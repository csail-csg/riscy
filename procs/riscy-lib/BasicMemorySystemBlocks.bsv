
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
import Port::*;

import Abstraction::*;
import RVAmo::*;
import RVExec::*; // for scatterStore and gatherLoad
import RVTypes::*;

// Dummy DCache
// This module has no internal storage. It just takes care of converting
// between RISC-V memory requests and main memory requests.
module mkDummyRVDCache#(GenericMemServer#(DataSz) mainMemory)(Server#(RVDMemReq, RVDMemResp));
    FIFOF#(RVDMemReq) procMemReq <- mkFIFOF;
    FIFOF#(RVDMemResp) procMemResp <- mkFIFOF;

    // True if this dummy cache is currently handling the "modify-write" part
    // of a read-modify-write operation.
    // NOTE: normal stores with byte enables count as RMW operations.
    Reg#(Bool) rmw <- mkReg(False);

    // Forces this dummy cache to wait for writes to finish before handling new reads
    Reg#(Bool) writePending <- mkReg(False);
    Reg#(Bool) readPending <- mkReg(False);

    FIFOF#(Tuple3#(DataByteSel,RVMemSize,Bool)) outstanding <- mkFIFOF;

    function Bool requiresRMW(RVDMemReq r);
        // The AxiSharedMemoryBridge can't handle byte enables, so we are handling it here
        return ((isStore(r.op) && r.size != D) || isAmo(r.op));
    endfunction

    rule ignoreWriteResps;
        let _x <- mainMemory.response.get();
        when(_x.write == True, noAction);
        writePending <= False;
    endrule

    // hanle request
    rule handleRVDMemReq(!rmw && !writePending && !readPending);
        let r = procMemReq.first;
        // This dummy cache does not support LR/SR instructions
        if (isLoad(r.op) || requiresRMW(r)) begin
            // send read request
            // this handles all store request with size < D
            mainMemory.request.put(GenericMemReq{write: False, byteen: '1, addr: r.addr, data: ?});
            readPending <= True;
        end else if (isStore(r.op)) begin
            // send write request (only when size == D)
            mainMemory.request.put(GenericMemReq{write: True, byteen: '1, addr: r.addr, data: r.data});
            writePending <= True;
            if (r.op == tagged Mem Sc) begin
                // successful
                procMemResp.enq(0);
            end
        end
        if (requiresRMW(r)) begin
            rmw <= True;
        end else begin
            procMemReq.deq;
        end
    endrule

    rule finishRMW(rmw && !writePending);
        let r = procMemReq.first;
        // get read data
        let memResp <- mainMemory.response.get;
        when(memResp.write == False, noAction);
        readPending <= False;
        let currData = memResp.data;
        // amoExec also handles plain stores with byte enables
        // If r.op is not an AMO operation, use Swap to perform stores with byte enables
        let {permutedDataByteEn, permutedStData} = scatterStore(truncate(r.addr), r.size, r.data);
        let newData = amoExec(r.op matches tagged Amo .amoFunc ? amoFunc : Swap, permutedDataByteEn, currData, permutedStData);
        mainMemory.request.put(GenericMemReq{write: True, byteen: '1, addr: r.addr, data: newData});
        writePending <= True;
        if (r.op == tagged Mem Sc) begin
            // Successful
            procMemResp.enq(0);
        end else if (r.op matches tagged Amo .*) begin
            procMemResp.enq(currData);
        end
        // finish
        rmw <= False;
        procMemReq.deq;
    endrule

    rule handleRVDMemResp(!rmw);
        let memResp <- mainMemory.response.get;
        when(memResp.write == False, noAction);
        procMemResp.enq(memResp.data);
        readPending <= False;
    endrule

    interface Put request;
        method Action put(RVDMemReq r);
            if (isLoad(r.op) || isAmo(r.op)) begin
                DataByteSel addrByteSel = truncate(r.addr);
                outstanding.enq(tuple3(addrByteSel, r.size, r.isUnsigned));
            end else if (r.op == tagged Mem Sc) begin
                outstanding.enq(tuple3(0, B, False));
            end
            procMemReq.enq(r);
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVDMemResp) get;
            let {addrByteSel, size, isUnsigned} = outstanding.first;
            outstanding.deq;
            procMemResp.deq;
            return gatherLoad(addrByteSel, size, isUnsigned, procMemResp.first);
        endmethod
    endinterface
endmodule

module mkRVIMemWrapper#(Server#(RVDMemReq, RVDMemResp) dMem)(Server#(RVIMemReq, RVIMemResp));
    interface Put request;
        method Action put(RVIMemReq req);
            let dReq = RVDMemReq {
                    op: tagged Mem Ld,
                    size: W,
                    isUnsigned: False,
                    addr: req,
                    data: 0 };
            dMem.request.put(dReq);
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVIMemResp) get;
            let resp <- dMem.response.get;
            return truncate(resp);
        endmethod
    endinterface
endmodule

module mkDummyRVICache#(GenericMemServer#(DataSz) mainMemory)(Server#(RVIMemReq, RVIMemResp));
    let _dMem <- mkDummyRVDCache(mainMemory);
    let _iMem <- mkRVIMemWrapper(_dMem);
    return _iMem;
endmodule

interface RVDMMU;
    interface Put#(RVDMMUReq) request;
    interface Get#(RVDMMUResp) response;
    method Action updateVMInfo(VMInfo vm);
endinterface

interface RVIMMU;
    interface Put#(RVIMMUReq) request;
    interface Get#(RVIMMUResp) response;
    method Action updateVMInfo(VMInfo vm);
endinterface

`ifndef CONFIG_RV32
// XXX: No RV32 support for MMU's yet

// This does not support any paged virtual memory modes
// TODO: add support for getPMA
module mkBasicDummyRVDMMU#(Bool isInst, GenericMemServer#(DataSz) mainMemory)(RVDMMU);
    FIFOF#(RVDMMUReq) procMMUReq <- mkFIFOF;
    FIFOF#(RVDMMUResp) procMMUResp <- mkFIFOF;

    // TODO: This should be defaultValue
    Reg#(VMInfo) vmInfo <- mkReg(VMInfo{prv:2'b11, asid:0, vm:0, mxr: False, pum: False, base:0, bound:'1});

    rule doTranslate;
        // TODO: add misaligned address exceptions

        // let {addr: .vaddr, op: .op} = procMMUReq.first;
        let vaddr = procMMUReq.first.addr;
        let op = procMMUReq.first.op;
        procMMUReq.deq;

        Bool isStore = getsWritePermission(op); // XXX: was isStore(r.op) || isAmo(r.op) || (r.op == tagged Mem PrefetchForSt);
        Bool isSupervisor = vmInfo.prv == prvS;

        PAddr paddr = 0;
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

    interface Put request;
        method Action put(RVDMMUReq r);
            procMMUReq.enq(r);
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVDMMUResp) get;
            procMMUResp.deq;
            return procMMUResp.first;
        endmethod
    endinterface
    method Action updateVMInfo(VMInfo vm);
        vmInfo <= vm;
    endmethod
endmodule

module mkRVIMMUWrapper#(RVDMMU dMMU)(RVIMMU);
    interface Put request;
        method Action put(RVIMMUReq req);
            dMMU.request.put(RVDMMUReq{addr: req, size: W, op: Ld}); // XXX: Should this type include AMO instructions too?
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVIMMUResp) get;
            let resp <- dMMU.response.get;
            return resp;
        endmethod
    endinterface
    method Action updateVMInfo(VMInfo vm);
        dMMU.updateVMInfo(vm);
    endmethod
endmodule

module mkDummyRVIMMU#(function PMA getPMA(PAddr addr), GenericMemServer#(DataSz) mainMemory)(RVIMMU);
    let _dMMU <- mkDummyRVDMMU(True, getPMA, mainMemory);
    let _iMMU <- mkRVIMMUWrapper(_dMMU);
    return _iMMU;
endmodule

module mkDummyRVDMMU#(Bool isInst, function PMA getPMA(PAddr addr), GenericMemServer#(DataSz) mainMemory)(RVDMMU);
    FIFOF#(RVDMMUReq) procMMUReq <- mkFIFOF;
    FIFOF#(RVDMMUResp) procMMUResp <- mkFIFOF;

    // TODO: This should be defaultValue
    Reg#(VMInfo) vmInfo <- mkReg(VMInfo{prv:2'b11, asid:0, vm:0, mxr: False, pum: False, base:0, bound:'1});

    // Registers for hardware pagetable walk
    Reg#(Bool) walking <- mkReg(False);
    Reg#(Bool) store <- mkReg(False);
    Reg#(Bool) supervisor <- mkReg(False);
    Reg#(PAddr) a <- mkReg(0);
    Reg#(Bit#(2)) i <- mkReg(0);
    Reg#(Bit#(64)) pte <- mkReg(0);
    Reg#(Vector#(3,Bit#(9))) vpn <- mkReg(replicate(0));
    Reg#(Bit#(12)) pageoffset <- mkReg(0);

    // if the response from main memory is for a write, drop it
    // XXX: this does not work if mainMemory has a synthesize boundary
    rule ignoreWriteResps;
        let _x <- mainMemory.response.get();
        when(_x.write == True, noAction);
    endrule

    rule doPageTableWalk(walking);
        let memResp <- mainMemory.response.get();
        when(memResp.write == False, noAction);

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
            PAddr paddr = '1;
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
                    mainMemory.request.put(GenericMemReq{write: True, byteen: '1, addr: a, data: pack(pte)});
                end
            end
        end else begin
            // go to next level
            PAddr newA = {0, pte.ppn2, pte.ppn1, pte.ppn0, 12'b0} | (zeroExtend(vpn[i-1]) << 3);
            mainMemory.request.put(GenericMemReq{write: False, byteen: '1, addr: newA, data: ?});
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

        PAddr paddr = 0;
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
                            PAddr newA = vmInfo.base + (zeroExtend(newvpn[2]) << 3);
                            mainMemory.request.put(GenericMemReq{write: False, byteen: '1, addr: newA, data: ?});
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

    interface Put request;
        method Action put(RVDMMUReq r);
            procMMUReq.enq(r);
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVDMMUResp) get;
            procMMUResp.deq;
            return procMMUResp.first;
        endmethod
    endinterface
    method Action updateVMInfo(VMInfo vm);
        vmInfo <= vm;
    endmethod
endmodule

`endif

// type used in the module below
typedef struct {
    Bool isWrite;
    RVMemSize size;
    Bool isUnsigned;
} PendingUncachedReqInfo deriving (Bits, Eq, FShow);
// probably should be called mkUncachedBridge
module mkUncachedConverter#(UncachedMemServerPort uncachedMem)(ServerPort#(RVDMemReq, RVDMemResp));
    // this assumes there are no RMW operations to uncached memory
    FIFOG#(PendingUncachedReqInfo) bookkeepingFIFO <- mkFIFOG;

    Ehr#(2, Maybe#(RVDMemResp)) respEhr <- mkEhr(tagged Invalid);

    rule handleResp(!isValid(respEhr[0]));
        let resp = uncachedMem.response.first;
        uncachedMem.response.deq;
        if (bookkeepingFIFO.notEmpty) begin
            let reqInfo = bookkeepingFIFO.first;
            if (reqInfo.isWrite != resp.write) begin
                $fdisplay(stderr, "[ERROR] Uncached memory responses out of sync.");
                $fdisplay(stderr, "[INFO] top of bookkeeping FIFO: ", fshow(bookkeepingFIFO.first));
                $fdisplay(stderr, "[INFO] uncached mem response: ", fshow(resp));
            end
            if (!resp.write) begin
                let result = resp.data;
                let extend = reqInfo.isUnsigned ? zeroExtend : signExtend;
                result = (case (reqInfo.size)
                        B: extend(result[7:0]);
                        H: extend(result[15:0]);
                        W: extend(result[31:0]);
`ifdef CONFIG_RV64
                        D: result[63:0];
`endif
                    endcase);
                respEhr[0] <= tagged Valid result;
            end
            bookkeepingFIFO.deq;
        end else begin
            $fdisplay(stderr, "[ERROR] Unexpected uncached memory responses.");
            $fdisplay(stderr, "[INFO] uncached mem response: ", fshow(resp));
        end
    endrule

    interface InputPort request;
        method Action enq(RVDMemReq r);
            uncachedMem.request.enq( UncachedMemReq {
                    write: r.op == tagged Mem St,
                    size: r.size,
                    addr: r.addr,
                    data: r.data
                } );
            bookkeepingFIFO.enq(PendingUncachedReqInfo {isWrite: r.op == tagged Mem St, size: r.size, isUnsigned: r.isUnsigned});
        endmethod
        method Bool canEnq;
            return uncachedMem.request.canEnq && bookkeepingFIFO.canEnq;
        endmethod
    endinterface
    interface OutputPort response;
        method RVDMemResp first if (respEhr[1] matches tagged Valid .resp);
            return resp;
        endmethod
        method Action deq if (respEhr[1] matches tagged Valid .resp);
            respEhr[1] <= tagged Invalid;
        endmethod
        method Bool canDeq;
            return isValid(respEhr[1]);
        endmethod
    endinterface
endmodule

// Memory bus takes in a vector of Servers and produces two server interfaces,
// one for a processor to attach to and one for an external interface to use.
// The processor port has priority, but if the external interface is preempted
// it will have the higher priority in the next cycle.
interface MemoryBus#(type reqT, type respT);
    interface Server#(reqT, respT) procIfc;
    interface Server#(reqT, respT) extIfc;
endinterface

typedef struct {
    Bool isExt;
    Bit#(TLog#(n)) server;
    Bool getsResp;
} MemoryBusPendingReq#(numeric type n) deriving (Bits, Eq, FShow);

module mkMemoryBus#(function Bit#(TLog#(n)) whichServer(reqT x), function Bool getsResponse(reqT x), Vector#(n, Server#(reqT, respT)) servers)(MemoryBus#(reqT, respT)) provisos (Bits#(reqT, reqTsz), Bits#(respT, respTsz));
    // ordering:
    // response < forwardResponse < request < forwardRequest

    Ehr#(4, Maybe#(reqT)) procReqEhr <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(reqT)) extReqEhr <- mkEhr(tagged Invalid);

    Ehr#(4, Maybe#(MemoryBusPendingReq#(n))) pendingReq <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(respT)) readyResp <- mkEhr(tagged Invalid);

    Reg#(Bool) extReqWasPreempted <- mkReg(False);

    // request priority:
    // old procIfc.request
    // old extIfc.request
    // current procIfc.request
    // current extIfc.request

    rule forwardRequest if (!isValid(pendingReq[3])
                            && (isValid(procReqEhr[3])
                                || isValid(extReqEhr[3])));
        Bool isExt = False;
        Bit#(TLog#(n)) serverIndx = 0;

        if (procReqEhr[3] matches tagged Valid .req &&& !extReqWasPreempted) begin
            procReqEhr[3] <= tagged Invalid;
            serverIndx = whichServer(req);
            servers[serverIndx].request.put(req);
            pendingReq[3] <= tagged Valid MemoryBusPendingReq { isExt: False, server: serverIndx, getsResp: getsResponse(req) };

            if (!isValid(extReqEhr[3])) begin
                extReqWasPreempted <= False;
            end else begin
                extReqWasPreempted <= True;
            end
        end else if (extReqEhr[3] matches tagged Valid .req) begin
            extReqEhr[3] <= tagged Invalid;
            serverIndx = whichServer(req);
            servers[serverIndx].request.put(req);
            pendingReq[3] <= tagged Valid MemoryBusPendingReq { isExt: True, server: serverIndx, getsResp: getsResponse(req) };

            extReqWasPreempted <= False;
        end else begin
            // Due to the guard of this rule, the only way this can happen is
            // if extWasPreempted is true but extReqEhr was invalid.
            $fdisplay(stderr, "[ERROR] mkMemoryBus: extReqWasPreempted == True, but there is no valid extReq");
            extReqWasPreempted <= False;
        end
    endrule

    rule forwardResponse if (pendingReq[0] matches tagged Valid .req
                                &&& !isValid(readyResp[0]));
        // get response
        let resp <- servers[req.server].response.get();
        if (req.getsResp) begin
            readyResp[0] <= tagged Valid resp;
        end else begin
            pendingReq[0] <= tagged Invalid;
        end
    endrule


    // Internal interface
    interface Server procIfc;
        interface Put request;
            method Action put(reqT r) if (!isValid(procReqEhr[2]));
                procReqEhr[2] <= tagged Valid r;
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(respT) get if (pendingReq[1] matches tagged Valid .req
                                                    &&& readyResp[1] matches tagged Valid .resp
                                                    &&& req.isExt == False);
                pendingReq[1] <= tagged Invalid;
                readyResp[1] <= tagged Invalid;
                return resp;
            endmethod
        endinterface
    endinterface

    // External interface
    interface Server extIfc;
        interface Put request;
            method Action put(reqT r) if (!isValid(extReqEhr[2]));
                extReqEhr[2] <= tagged Valid r;
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(respT) get if (pendingReq[1] matches tagged Valid .req
                                                    &&& readyResp[1] matches tagged Valid .resp
                                                    &&& req.isExt == True);
                pendingReq[1] <= tagged Invalid;
                readyResp[1] <= tagged Invalid;
                return resp;
            endmethod
        endinterface
    endinterface
endmodule

typedef struct {
    Addr addr_mask;
    Addr addr_match;
    UncachedMemServerPort ifc;
} MemoryBusItem;

typedef struct {
    Bool isExt;
    Bit#(TLog#(n)) serverIndex;
} MemoryBusV2PendingReq#(numeric type n) deriving (Bits, Eq, FShow);

interface MemoryBusV2;
    interface UncachedMemServerPort procIfc;
    interface UncachedMemServerPort extIfc;
endinterface

function MemoryBusItem busItemFromAddrRange( Addr low, Addr high, UncachedMemServerPort ifc );
    let addr_mask = ~(low ^ high);
    let addr_match = low & addr_mask;
    // mask should be a contiguous region of upper bits,
    // low should be the lowest valid address for mask/match combination,
    // and high should be the highest valid address for mask/match combination,
    Bool valid = ((addr_mask & ((~addr_mask) >> 1)) == 0)
                    && ((low & ~addr_mask) == 0)
                    && ((high & ~addr_mask) == ~addr_mask);
    if (valid) begin
        return MemoryBusItem {
            addr_mask: addr_mask,
            addr_match: addr_match,
            ifc: ifc
        };
    end else begin
        return error("busItemFromAddrRange compilation error: Address range (%x-%x) cannot be expressed as match/mask", ?);
    end
endfunction

module mkMemoryBusV2#(Vector#(n, MemoryBusItem ) bus_items)(MemoryBusV2);
    // check for consistency of addr_mask and addr_match in bus_items
    for (Integer i = 0 ; i < valueOf(n) ; i = i+1) begin
        if ((bus_items[i].addr_mask & bus_items[i].addr_match) != bus_items[i].addr_match) begin
            errorM("mkMemoryBusV2 compilation error: Illegal addr_mask addr_match combination");
        end
        for (Integer j = 0 ; j < valueOf(n) ; j = j+1) begin
            if (i != j) begin
                Addr shared_mask = bus_items[i].addr_mask & bus_items[j].addr_mask;
                Addr different_match = bus_items[i].addr_match ^ bus_items[j].addr_match;
                if ((shared_mask & different_match) == 0) begin
                    errorM("mkMemoryBusV2 compilation error: Overlapping address regions in bus_items");
                end
            end
        end
    end

    Ehr#(4, Maybe#(UncachedMemReq)) procReqEhr <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(UncachedMemReq)) extReqEhr <- mkEhr(tagged Invalid);

    // pendingReq says which client gets the next response and which server is sending it
    Ehr#(4, Maybe#(MemoryBusV2PendingReq#(n))) pendingReq <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(Bool)) currReqIsExt <- mkEhr(tagged Invalid);
    Ehr#(4, Maybe#(UncachedMemResp)) readyResp <- mkEhr(tagged Invalid);

    Reg#(Bool) extReqWasPreempted <- mkReg(False);

    // request priority:
    // old procIfc.request
    // old extIfc.request
    // current procIfc.request
    // current extIfc.request

    rule forwardRequest if (!isValid(pendingReq[3])
                            && (isValid(procReqEhr[3])
                                || isValid(extReqEhr[3])));
        Bool isExt = False;
        Bit#(TLog#(n)) serverIndx = 0;

        if (procReqEhr[3] matches tagged Valid .req &&& !extReqWasPreempted) begin
            // get serverIndex from the request address
            Integer serverIndex = valueOf(n);
            for (Integer i = 0 ; i < valueOf(n) ; i = i+1) begin
                if ((truncate(req.addr) & bus_items[i].addr_mask) == bus_items[i].addr_match) begin
                    serverIndex = i;
                end
            end

            procReqEhr[3] <= tagged Invalid;
            if (serverIndex == valueOf(n)) begin
                // illegal address
                readyResp[3] <= tagged Valid UncachedMemResp{ write: req.write, data: 0 };
                pendingReq[3] <= tagged Valid MemoryBusV2PendingReq{ isExt: False, serverIndex: 0 };
            end else begin
                // legal address
                bus_items[serverIndex].ifc.request.enq(req);
                pendingReq[3] <= tagged Valid MemoryBusV2PendingReq{ isExt: False, serverIndex: fromInteger(serverIndex) };
            end

            // record if an external request was preempted
            if (!isValid(extReqEhr[3])) begin
                extReqWasPreempted <= False;
            end else begin
                extReqWasPreempted <= True;
            end
        end else if (extReqEhr[3] matches tagged Valid .req) begin
            // get serverIndex from the request address
            Integer serverIndex = valueOf(n);
            for (Integer i = 0 ; i < valueOf(n) ; i = i+1) begin
                if ((truncate(req.addr) & bus_items[i].addr_mask) == bus_items[i].addr_match) begin
                    serverIndex = i;
                end
            end

            extReqEhr[3] <= tagged Invalid;
            if (serverIndex == valueOf(n)) begin
                // illegal address
                readyResp[3] <= tagged Valid UncachedMemResp{ write: req.write, data: 0 };
                pendingReq[3] <= tagged Valid MemoryBusV2PendingReq{ isExt: True, serverIndex: 0 };
            end else begin
                // legal address
                bus_items[serverIndex].ifc.request.enq(req);
                pendingReq[3] <= tagged Valid MemoryBusV2PendingReq{ isExt: True, serverIndex: fromInteger(serverIndex) };
            end

            extReqWasPreempted <= False;
        end else begin
            // Due to the guard of this rule, the only way this can happen is
            // if extWasPreempted is true but extReqEhr was invalid.
            $fdisplay(stderr, "[ERROR] mkMemoryBus: extReqWasPreempted == True, but there is no valid extReq");
            extReqWasPreempted <= False;
        end
    endrule

    rule forwardResponse if (pendingReq[0] matches tagged Valid .req
                                &&& !isValid(readyResp[0]));
        // get response
        let resp = bus_items[req.serverIndex].ifc.response.first;
        bus_items[req.serverIndex].ifc.response.deq;
        readyResp[0] <= tagged Valid resp;
    endrule

    interface UncachedMemServerPort procIfc;
        interface InputPort request;
            method Action enq(UncachedMemReq req) if (!isValid(procReqEhr[2]));
                procReqEhr[2] <= tagged Valid req;
            endmethod
            method Bool canEnq;
                return !isValid(procReqEhr[2]);
            endmethod
        endinterface
        interface OutputPort response;
            method UncachedMemResp first if (pendingReq[1] matches tagged Valid.req
                                                &&& readyResp[1] matches tagged Valid .resp
                                                &&& (req.isExt == False));
                return resp;
            endmethod
            method Action deq if (pendingReq[1] matches tagged Valid.req
                                    &&& readyResp[1] matches tagged Valid .resp
                                    &&& (req.isExt == False));
                pendingReq[1] <= tagged Invalid;
                readyResp[1] <= tagged Invalid;
            endmethod
            method Bool canDeq;
                // This interface method is not currently supported
                if (pendingReq[1] matches tagged Valid.req
                        &&& readyResp[1] matches tagged Valid .resp) begin
                    return req.isExt == False;
                end else begin
                    return False;
                end
            endmethod
        endinterface
    endinterface
    interface UncachedMemServerPort extIfc;
        interface InputPort request;
            method Action enq(UncachedMemReq req) if (!isValid(extReqEhr[2]));
                extReqEhr[2] <= tagged Valid req;
            endmethod
            method Bool canEnq;
                return !isValid(extReqEhr[2]);
            endmethod
        endinterface
        interface OutputPort response;
            method UncachedMemResp first if (pendingReq[1] matches tagged Valid.req
                                                &&& readyResp[1] matches tagged Valid .resp
                                                &&& (req.isExt == True));
                return resp;
            endmethod
            method Action deq if (pendingReq[1] matches tagged Valid.req
                                    &&& readyResp[1] matches tagged Valid .resp
                                    &&& (req.isExt == True));
                pendingReq[1] <= tagged Invalid;
                readyResp[1] <= tagged Invalid;
            endmethod
            method Bool canDeq;
                // This interface method is not currently supported
                if (pendingReq[1] matches tagged Valid.req
                        &&& readyResp[1] matches tagged Valid .resp) begin
                    return req.isExt == True;
                end else begin
                    return False;
                end
            endmethod
        endinterface
    endinterface
endmodule
