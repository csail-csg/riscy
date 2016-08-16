
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
import FIFO::*;
import GetPut::*;
import Vector::*;

import PrintTrace::*;
import ServerUtil::*;

import BasicMemorySystemBlocks::*;
import Abstraction::*;
import RVTypes::*;

module mkBasicMemorySystem#(function PMA getPMA(PAddr addr))(SingleCoreMemorySystem#(DataSz));
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
