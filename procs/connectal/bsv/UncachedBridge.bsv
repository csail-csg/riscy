
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

import Abstraction::*;
import RVTypes::*;
import CompareProvisos::*;
import ClientServer::*;
import ConnectalConfig::*;
import GetPut::*;
import RegFile::*;
import Vector::*;
import FIFO::*;
import FIFOF::*;
import HostInterface::*;
import MemTypes::*;
import PrintTrace::*;

interface UncachedBridge;
    // Processor Interface
    interface UncachedMemServer toProc;

    // Shared Memory Interfaces
    interface UncachedMemClient externalMMIO;
    interface MemReadClient#(DataBusWidth) rom;

    // Initialize the shared memory with the ref pointer and size.
    // If an address is out of range, it will handled (somehow)
    method Action initUncachedMem(Bit#(32) refPointer, Addr romBaseAddr, Addr mmioBaseAddr);

    // Methods for clearing pending requests before reset
    // TODO: actually implement this
    method Action flushPendingReq;
    method Bool flushDone;
endinterface

typedef union tagged {
    struct {
        Bool        write;
        DataByteSel byteSel;
        RVMemSize   size;
    } ROM;
    void ExternalMMIO;
} UncachedReqType deriving (Bits, Eq, FShow);

(* synthesize *)
module mkUncachedBridge(UncachedBridge) provisos (EQ#(DataSz, DataBusWidth));
    Bool verbose = False;
    File tracefile = verbose ? stdout : tagged InvalidFile;

    FIFOF#(UncachedReqType) pendingReq <- fprintTraceM(tracefile, "pendingReq", mkSizedFIFOF(4));
    Reg#(Bool) flushing <- mkReg(False);

    // This assumes the ROM segment is before the MMIO segment in the address space

    // ROM segment
    FIFO#(MemRequest) romReadReqFifo <- fprintTraceM(tracefile, "romReadReqFifo", mkFIFO);
    FIFO#(MemData#(DataBusWidth)) romReadDataFifo <- fprintTraceM(tracefile, "romReadDataFifo", mkFIFO);
    Reg#(SGLId) refPointerReg <- mkReg(0);
    Reg#(Addr) romBaseAddrReg <- mkReg(64 << 20); // 64 MB shared memory default

    // MMIO segment
    FIFO#(UncachedMemReq) externalMMIOReq <- fprintTraceM(tracefile, "externalMMIOReq", mkFIFO);
    FIFO#(UncachedMemResp) externalMMIOResp <- fprintTraceM(tracefile, "externalMMIOResp", mkFIFO);
    Reg#(Addr) mmioBaseAddrReg <- mkReg(70 << 20); // 4 MB ROM by default

    interface UncachedMemServer toProc;
        interface Put request;
            method Action put(UncachedMemReq r) if (!flushing);
                // address check
                if (r.addr >= romBaseAddrReg && r.addr < mmioBaseAddrReg) begin
                    if (r.write) begin
                        // writing is not supported
                        // TODO: make this an exception in the TLB instead
                        $fdisplay(stderr, "[ERROR] write request sent to ROM");
                        pendingReq.enq(tagged ROM {write: True, byteSel: truncate(r.addr), size: r.size});
                    end else begin
                        let romAddr = r.addr - romBaseAddrReg;
                        DataByteSel byteSel = truncate(romAddr);
                        // allign romAddr to 8-byte boundary
                        romAddr[2:0] = 0;
                        romReadReqFifo.enq(MemRequest{sglId: refPointerReg, offset: truncate(romAddr), burstLen: 8, tag: 1}); // XXX: What should the tag be?
                        pendingReq.enq(tagged ROM {write: False, byteSel: byteSel, size: r.size});
                    end
                end else begin
                    externalMMIOReq.enq(r);
                    pendingReq.enq(tagged ExternalMMIO);
                end
            endmethod
        endinterface
        interface Get response;
            method ActionValue#(UncachedMemResp) get;
                let reqType = pendingReq.first;
                pendingReq.deq;
                case (reqType) matches
                    tagged ROM .romReq:
                        begin
                            if (romReq.write) begin
                                return UncachedMemResp{write: True, data: 0};
                            end else begin
                                let result = romReadDataFifo.first.data;
                                romReadDataFifo.deq;
                                // Shift according to the byteSel
                                result = result >> {romReq.byteSel, 3'b0}; // byteSel * 8
                                // Don't need to do anything with size since the cached/uncached splitter takes care of it.
                                return UncachedMemResp{write: False, data: result};
                            end
                        end
                    tagged ExternalMMIO:
                        begin
                            externalMMIOResp.deq;
                            return externalMMIOResp.first;
                        end
                endcase
            endmethod
        endinterface
    endinterface

    interface MemReadClient rom;
        interface Get readReq = toGet(romReadReqFifo);
        interface Put readData = toPut(romReadDataFifo);
    endinterface

    interface UncachedMemClient externalMMIO = toGPClient(externalMMIOReq, externalMMIOResp);

    method Action initUncachedMem(Bit#(32) refPointer, Addr romBaseAddr, Addr mmioBaseAddr);
        refPointerReg <= refPointer;
        romBaseAddrReg <= romBaseAddr;
        mmioBaseAddrReg <= mmioBaseAddr;
    endmethod

    method Action flushPendingReq;
        flushing <= True;
    endmethod
    method Bool flushDone;
        return !pendingReq.notEmpty;
    endmethod
endmodule
