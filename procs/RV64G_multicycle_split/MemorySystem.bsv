
// Copyright (c) 2016 Massachusetts Institute of Technology

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

import BuildVector::*;
import ClientServer::*;
import DefaultValue::*;
import FIFOF::*;
import FIFO::*;
import GetPut::*;
import Vector::*;

import PrintTrace::*;
import Abstraction::*;
import RVAmo::*;
import MainMemoryArbiter::*;
import RVExec::*;
import RVTypes::*;
import ServerUtil::*;

module mkBasicMemorySystem#(function PMA getPMA(Addr addr))(SingleCoreMemorySystem#(DataSz));
    Bool verbose = False;
    File tracefile = verbose ? stdout : tagged InvalidFile;

    // cached memory port -- works on cache lines
    FIFO#(MainMemReq) mainMemReqFIFO <- mkFIFO;
    FIFO#(MainMemResp) mainMemRespFIFO <- mkFIFO;
    let mainMemoryServer = toGPServer(mainMemReqFIFO, mainMemRespFIFO);
    let mainMemoryClient = toGPClient(mainMemReqFIFO, mainMemRespFIFO);

    // uncached port -- works on 64-bit words
    FIFO#(UncachedMemReq) uncachedReqFIFO <- mkFIFO;
    FIFO#(UncachedMemResp) uncachedRespFIFO <- mkFIFO;
    let uncachedMemServer = toGPServer(uncachedReqFIFO, uncachedRespFIFO);
    let uncachedMemClient = toGPClient(uncachedReqFIFO, uncachedRespFIFO);

    // splits cached memory port for itlb, imem, dtlb, and dmem
    Vector#(4, Server#(MainMemReq, MainMemResp)) mainMemorySplitServer <- mkFixedPriorityServerSplitter(constFn(True), 4, mainMemoryServer);

    let itlb <- mkDummyRVIMMU(getPMA, fprintTrace(tracefile, "IMMU-Arbiter", mainMemorySplitServer[3]));
    let icache <- mkDummyRVICache(fprintTrace(tracefile, "ICache-Arbiter", mainMemorySplitServer[2]));
    let dtlb <- mkDummyRVDMMU(False, getPMA, fprintTrace(tracefile, "DMMU-Arbiter", mainMemorySplitServer[1]));
    // two different paths for dmem request to take: cached and uncached
    let dcache <- mkDummyRVDCache(fprintTrace(tracefile, "DCache-Arbiter", mainMemorySplitServer[0]));
    let duncached <- mkUncachedConverter(fprintTrace(tracefile, "DUncached-Bridge", uncachedMemServer));
    // join cached and uncached paths to make a unified dmem interface
    function Bit#(1) whichServer(RVDMemReq r);
        return (case (getPMA(r.addr))
                    MainMemory, IORom: 0; // cached
                    default: 1; // uncached
                endcase);
    endfunction
    function Bool getsResponse(RVDMemReq r);
        return (case (r.op) matches
                tagged Mem St: False;
                default: True;
            endcase);
    endfunction
    let dmem <- mkServerJoiner(whichServer, getsResponse, 4, vec(dcache, duncached));

    Vector#(numCores, MemorySystem) onecore;
    onecore[0] = (interface MemorySystem;
            interface Server ivat = fprintTrace(tracefile, "Proc-IMMU", (interface Server;
                                        interface Put request = itlb.request;
                                        interface Get response = itlb.response;
                                    endinterface));
            interface Server ifetch = fprintTrace(tracefile, "Proc-ICache", icache);
            interface Server dvat = fprintTrace(tracefile, "Proc-DMMU", (interface Server;
                                        interface Put request = dtlb.request;
                                        interface Get response = dtlb.response;
                                    endinterface));
            interface Server dmem = fprintTrace(tracefile, "Proc-DMem", dmem);
            interface Server fence;
                interface Put request;
                    method Action put(FenceReq f);
                        noAction;
                    endmethod
                endinterface
                interface Get response;
                    method ActionValue#(FenceResp) get;
                        return ?;
                    endmethod
                endinterface
            endinterface
            method Action updateVMInfoI(VMInfo vmI);
                itlb.updateVMInfo(vmI);
            endmethod
            method Action updateVMInfoD(VMInfo vmD);
                dtlb.updateVMInfo(vmD);
            endmethod
        endinterface);
    interface Vector core = onecore;
    interface Client cachedMemory = mainMemoryClient;
    interface Client uncachedMemory = uncachedMemClient;
endmodule

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

        Addr paddr = 0;
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

module mkDummyRVIMMU#(function PMA getPMA(Addr addr), GenericMemServer#(DataSz) mainMemory)(RVIMMU);
    let _dMMU <- mkDummyRVDMMU(True, getPMA, mainMemory);
    let _iMMU <- mkRVIMMUWrapper(_dMMU);
    return _iMMU;
endmodule

module mkDummyRVDMMU#(Bool isInst, function PMA getPMA(Addr addr), GenericMemServer#(DataSz) mainMemory)(RVDMMU);
    FIFOF#(RVDMMUReq) procMMUReq <- mkFIFOF;
    FIFOF#(RVDMMUResp) procMMUResp <- mkFIFOF;

    // TODO: This should be defaultValue
    Reg#(VMInfo) vmInfo <- mkReg(VMInfo{prv:2'b11, asid:0, vm:0, mxr: False, pum: False, base:0, bound:'1});

    // Registers for hardware pagetable walk
    Reg#(Bool) walking <- mkReg(False);
    Reg#(Bool) store <- mkReg(False);
    Reg#(Bool) supervisor <- mkReg(False);
    Reg#(Addr) a <- mkReg(0);
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
            Addr paddr = '1;
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
            Addr newA = {0, pte.ppn2, pte.ppn1, pte.ppn0, 12'b0} | (zeroExtend(vpn[i-1]) << 3);
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

        Addr paddr = 0;
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
                            // Addr newA = vmInfo.base + (zeroExtend(vpn[2]) << 3);
                            Vector#(3, Bit#(9)) newvpn = unpack(vaddr[38:12]);
                            Addr newA = vmInfo.base + (zeroExtend(newvpn[2]) << 3);
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

// type used in the module below
typedef struct {
    Bool isWrite;
    RVMemSize size;
    Bool isUnsigned;
} PendingUncachedReqInfo deriving (Bits, Eq, FShow);
// probably should be called mkUncachedBridge
module mkUncachedConverter#(UncachedMemServer uncachedMem)(Server#(RVDMemReq, RVDMemResp));
    // this assumes there are no RMW operations to uncached memory
    FIFO#(PendingUncachedReqInfo) bookkeepingFIFO <- mkFIFO;

    rule ignoreWriteResponses(bookkeepingFIFO.first.isWrite);
        let resp <- uncachedMem.response.get;
        if (!resp.write) begin
            $fdisplay(stderr, "[ERROR] Uncached memory responses out of sync. Expected a write response but got a read response.");
        end
        bookkeepingFIFO.deq;
    endrule

    interface Put request;
        method Action put(RVDMemReq r);
            uncachedMem.request.put( UncachedMemReq {
                    write: r.op == tagged Mem St,
                    size: r.size,
                    addr: r.addr,
                    data: r.data
                } );
            bookkeepingFIFO.enq(PendingUncachedReqInfo {isWrite: r.op == tagged Mem St, size: r.size, isUnsigned: r.isUnsigned});
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVDMemResp) get if (!bookkeepingFIFO.first.isWrite);
            let reqInfo = bookkeepingFIFO.first;
            bookkeepingFIFO.deq;
            let uncachedResp <- uncachedMem.response.get;
            if (uncachedResp.write) begin
                $fdisplay(stderr, "[ERROR] Uncached memory responses out of sync. Expected a read response but got a write response.");
            end
            let result = uncachedResp.data;
            let extend = reqInfo.isUnsigned ? zeroExtend : signExtend;
            result = (case (reqInfo.size)
                    B: extend(result[7:0]);
                    H: extend(result[15:0]);
                    W: extend(result[31:0]);
                    D: result[63:0];
                endcase);
            return result;
        endmethod
    endinterface
endmodule
