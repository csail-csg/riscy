
// Copyright (c) 2016, 2017 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

`include "ProcConfig.bsv"

import ClientServer::*;
import FIFOF::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import Ehr::*;
import FIFOG::*;
import MemUtil::*;
import Port::*;

import Abstraction::*;
import RVAmo::*;
import RVExec::*; // for scatterStore and gatherLoad
import RVTypes::*;

interface RVDMMU#(numeric type xlen, numeric type addrSz);
    interface InputPort#(RVDMMUReq#(xlen)) request;
    interface OutputPort#(RVDMMUResp#(addrSz)) response;
    method Action updateVMInfo(VMInfo#(xlen) vm);
endinterface

interface RVIMMU#(numeric type xlen, numeric type addrSz);
    interface InputPort#(RVIMMUReq#(xlen)) request;
    interface OutputPort#(RVIMMUResp#(addrSz)) response;
    method Action updateVMInfo(VMInfo#(xlen) vm);
endinterface

// These are all RV64 MMUs, we have no support for RV32 MMUs yet

// This does not support any paged virtual memory modes
// TODO: add support for getPMA
// 64-Bit dummy MMU
module mkBasicDummyRVDMMU64#(Bool isInst, CoarseMemServerPort#(64,3) mainMemory)(RVDMMU#(64, 64));
    FIFOG#(RVDMMUReq#(64)) procMMUReq <- mkFIFOG;
    FIFOG#(RVDMMUResp#(64)) procMMUResp <- mkFIFOG;

    // TODO: This should be defaultValue
    Reg#(VMInfo#(64)) vmInfo <- mkReg(VMInfo{prv:2'b11, asid:0, vm:0, mxr: False, pum: False, base:0, bound:'1});

    rule doTranslate;
        // TODO: add misaligned address exceptions

        // let {addr: .vaddr, op: .op} = procMMUReq.first;
        let vaddr = procMMUReq.first.addr;
        let op = procMMUReq.first.op;
        procMMUReq.deq;

        Bool isStore = getsWritePermission(op); // XXX: was isStore(r.op) || isAmo(r.op) || (r.op == tagged Mem PrefetchForSt);
        Bool isSupervisor = vmInfo.prv == prvS;

        Bit#(64) paddr = 0;
        Maybe#(ExceptionCause) exception = tagged Invalid;
        Maybe#(ExceptionCause) accessFault = tagged Valid (isInst ? InstAccessFault :
                                                            (isStore ? StoreAccessFault :
                                                                LoadAccessFault));

        if (vmInfo.prv == prvM) begin
            paddr = vaddr;
        end else begin
            case (vmInfo.vm)
                vmMbare:        paddr = vaddr;
                vmMbb, vmMbbid: begin
                                    if (vaddr >= vmInfo.bound) begin
                                        exception = accessFault;
                                    end else begin
                                        paddr = vaddr + vmInfo.base;
                                    end
                                end
                default:
                    // unsupported virtual addressing mode
                    exception = accessFault;
            endcase
        end

        procMMUResp.enq(RVDMMUResp{addr: paddr, exception: exception});
    endrule

    interface InputPort request = toInputPort(procMMUReq);
    interface OutputPort response = toOutputPort(procMMUResp);
    method Action updateVMInfo(VMInfo#(64) vm);
        vmInfo <= vm;
    endmethod
endmodule

module mkRVIMMUWrapper#(RVDMMU#(xlen, addrSz) dMMU)(RVIMMU#(xlen, addrSz));
    interface InputPort request;
        method Action enq(RVIMMUReq#(xlen) req);
            dMMU.request.enq(RVDMMUReq{addr: req, size: W, op: Ld}); // XXX: Should this type include AMO instructions too?
        endmethod
        method Bool canEnq;
            return dMMU.request.canEnq;
        endmethod
    endinterface
    interface OutputPort response;
        method RVIMMUResp#(addrSz) first;
            return dMMU.response.first;
        endmethod
        method Action deq;
            dMMU.response.deq;
        endmethod
        method Bool canDeq;
            return dMMU.response.canDeq;
        endmethod
    endinterface
    method Action updateVMInfo(VMInfo#(xlen) vm);
        dMMU.updateVMInfo(vm);
    endmethod
endmodule

// This module assumes XLEN=64
module mkDummyRVIMMU64#(function PMA getPMA(Bit#(64) addr), CoarseMemServerPort#(64, 3) mainMemory)(RVIMMU#(64, 64));
    let _dMMU <- mkDummyRVDMMU64(True, getPMA, mainMemory);
    let _iMMU <- mkRVIMMUWrapper(_dMMU);
    return _iMMU;
endmodule

// This module assumes XLEN=64
module mkDummyRVDMMU64#(Bool isInst, function PMA getPMA(Bit#(64) addr), CoarseMemServerPort#(64, 3) mainMemory)(RVDMMU#(64, 64));
    FIFOG#(RVDMMUReq#(64)) procMMUReq <- mkFIFOG;
    FIFOG#(RVDMMUResp#(64)) procMMUResp <- mkFIFOG;

    Reg#(VMInfo#(64)) vmInfo <- mkReg(VMInfo{prv:2'b11, asid:0, vm:0, mxr: False, pum: False, base:0, bound:'1});

    // Registers for hardware pagetable walk
    Reg#(Bool) walking <- mkReg(False);
    Reg#(Bool) store <- mkReg(False);
    Reg#(Bool) supervisor <- mkReg(False);
    Reg#(Bit#(64)) a <- mkReg(0);
    Reg#(Bit#(2)) i <- mkReg(0);
    Reg#(Bit#(64)) pte <- mkReg(0);
    Reg#(Vector#(3,Bit#(9))) vpn <- mkReg(replicate(0));
    Reg#(Bit#(12)) pageoffset <- mkReg(0);

    // if the response from main memory is for a write, drop it
    rule ignoreWriteResps(mainMemory.response.first.write);
        mainMemory.response.deq();
    endrule

    rule doPageTableWalk(walking && !mainMemory.response.first.write);
        let memResp = mainMemory.response.first;
        mainMemory.response.deq;

        PTE_Sv39 pte = unpack(memResp.data);
        Maybe#(ExceptionCause) accessFault = tagged Valid (isInst ? InstAccessFault :
                                                            (store ? StoreAccessFault :
                                                                LoadAccessFault));
        Bool leafPTE = isLeafPTE(pte);
        Bool legalPTE = isLegalPTE(pte);
        if ((i == 0) && !leafPTE) begin
            // non-leaf PTEs at the lowest level of the page table are treated
            // as illegal PTEs
            legalPTE = False;
        end

        if (!legalPTE) begin
            // illegal pte, access fault
            procMMUResp.enq(RVDMMUResp{addr: 0, exception: accessFault});
            walking <= False;
        end else if (leafPTE) begin
            // valid leaf page

            // translated physical address
            Bit#(64) paddr = '1;
            if (i == 0) begin
                paddr = {0, pte.ppn2, pte.ppn1, pte.ppn0, pageoffset};
            end else if (i == 1) begin
                paddr = {0, pte.ppn2, pte.ppn1, vpn[0], pageoffset};
            end else begin // if (i == 2)
                paddr = {0, pte.ppn2, vpn[1], vpn[0], pageoffset};
            end

            // check page permissions
            Bool hasPermission = False;
            if (isInst) begin
                hasPermission = pte.x;
            end else if (store) begin
                hasPermission = pte.w;
            end else begin
                hasPermission = pte.r || (vmInfo.mxr && pte.x);
            end
            // supervisor can't access user pages if pum is set
            if (supervisor && vmInfo.pum && pte.u) begin
                hasPermission = False;
            end
            // user needs pte.u bit set
            if (!supervisor && !pte.u) begin
                hasPermission = False;
            end

            // check PMA permissions
            PMA pma = getPMA(paddr);
            if (pma == IORom) begin
                // no W permission
                if (store) begin
                    hasPermission = False;
                end
            end else if (pma == IODevice) begin
                // no AMO permission
                // TODO: change type of MMU request to include sufficient AMO
                // information (AMO Class) and check permission accordingly
                // no X permission
                if (isInst) begin
                    hasPermission = False;
                end
            end else if (pma == IOEmpty) begin
                // no R, W, or X permission
                hasPermission = False;
            end

            if (!hasPermission) begin
                // illegal, access fault
                procMMUResp.enq(RVDMMUResp{addr: 0, exception: accessFault});
                walking <= False;
            end else begin
                // legal, return translation
                procMMUResp.enq(RVDMMUResp{addr: paddr, exception: tagged Invalid});
                walking <= False;
                if (!pte.a || (store && !pte.d)) begin
                    // write back necessary
                    // update pte
                    pte.a = True;
                    if (store) begin
                        pte.d = True;
                    end
                    // send write request
                    mainMemory.request.enq(CoarseMemReq{write: True, addr: a, data: pack(pte)});
                end
            end
        end else begin
            // go to next level
            Bit#(64) newA = {0, pte.ppn2, pte.ppn1, pte.ppn0, 12'b0} | (zeroExtend(vpn[i-1]) << 3);
            mainMemory.request.enq(CoarseMemReq{write: False, addr: newA, data: ?});
            a <= newA;
            i <= i - 1;
        end
    endrule

    rule doTranslate(!walking);
        // let {addr: .vaddr, op: .op} = procMMUReq.first;
        let vaddr = procMMUReq.first.addr;
        let size = procMMUReq.first.size;
        let op = procMMUReq.first.op;
        procMMUReq.deq;

        Bool isStore = (op == St || op == Sc || op == PrefetchForSt);
        Bool isSupervisor = vmInfo.prv == prvS;
        Bool pageTableWalk = False;

        Bit#(64) paddr = 0;
        Maybe#(ExceptionCause) exception = tagged Invalid;
        Maybe#(ExceptionCause) accessFault = tagged Valid (isInst ? InstAccessFault :
                                                            (isStore ? StoreAccessFault :
                                                                LoadAccessFault));
        Maybe#(ExceptionCause) misalignedFault = tagged Valid (isInst ? InstAddrMisaligned :
                                                            (isStore ? StoreAddrMisaligned :
                                                                LoadAddrMisaligned));
        Bit#(3) alignmentBits = (case(size)
                D:       3'b111;
                W:       3'b011;
                H:       3'b001;
                B:       3'b000;
                default: 3'b111;
            endcase);
        if ((truncate(vaddr) & alignmentBits) != 0) begin
            exception = misalignedFault;
        end else if (vmInfo.prv == prvM) begin
            paddr = vaddr;
        end else begin
            case (vmInfo.vm)
                vmMbare:        paddr = vaddr;
                vmMbb, vmMbbid: begin
                                    if (vaddr >= vmInfo.bound) begin
                                        exception = accessFault;
                                    end else begin
                                        paddr = vaddr + vmInfo.base;
                                    end
                                end
                vmSv39: begin
                            // start page table walk
                            // PAddr newA = vmInfo.base + (zeroExtend(vpn[2]) << 3);
                            Vector#(3, Bit#(9)) newvpn = unpack(vaddr[38:12]);
                            Bit#(64) newA = vmInfo.base + (zeroExtend(newvpn[2]) << 3);
                            mainMemory.request.enq(CoarseMemReq{write: False, addr: newA, data: ?});
                            walking <= True;
                            pageTableWalk = True;
                            a <= newA;
                            i <= 2;
                            vpn <= newvpn;
                            pageoffset <= truncate(vaddr);
                            store <= isStore;
                            supervisor <= isSupervisor;
                        end
                default:
                    // unsupported virtual addressing mode
                    exception = accessFault;
            endcase
        end

        if (!pageTableWalk) begin
            procMMUResp.enq(RVDMMUResp{addr: paddr, exception: exception});
        end
    endrule

    interface InputPort request = toInputPort(procMMUReq);
    interface OutputPort response = toOutputPort(procMMUResp);
    method Action updateVMInfo(VMInfo#(64) vm);
        vmInfo <= vm;
    endmethod
endmodule

