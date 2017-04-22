
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

import BuildVector::*;
import ClientServer::*;
import GetPut::*;
import Vector::*;

import FIFOG::*;
import Port::*;
import PortUtil::*;
import PrintTrace::*;

import BasicMemorySystemBlocks::*;
import Abstraction::*;
import RVTypes::*;

module mkBasicMemorySystem#(function PMA getPMA(PAddr addr))(SingleCoreMemorySystem#(DataSz));
    // cached memory port -- works on cache lines
    FIFOG#(MainMemReq) mainMemReqFIFO <- mkFIFOG;
    FIFOG#(MainMemResp) mainMemRespFIFO <- mkFIFOG;
    let mainMemoryServer = toServerPort(mainMemReqFIFO, mainMemRespFIFO);
    let mainMemoryClient = toClientPort(mainMemReqFIFO, mainMemRespFIFO);

    // uncached port -- works on 64-bit words
    FIFOG#(UncachedMemReq) uncachedReqFIFO <- mkFIFOG;
    FIFOG#(UncachedMemResp) uncachedRespFIFO <- mkFIFOG;
    let uncachedMemServer = toServerPort(uncachedReqFIFO, uncachedRespFIFO);
    let uncachedMemClient = toClientPort(uncachedReqFIFO, uncachedRespFIFO);

    // splits cached memory port for itlb, imem, dtlb, and dmem
    Vector#(5, ServerPort#(MainMemReq, MainMemResp)) mainMemorySplitServer <- mkFixedPriorityServerPortSplitter(constFn(True), 2, mainMemoryServer);

    Vector#(2, UncachedMemServerPort) uncachedMemSplitServer <- mkFixedPriorityServerPortSplitter(constFn(True), 2, uncachedMemServer);

    // extMemServer -- works on 64-bit words
    let extMemServer = mainMemorySplitServer[4];

    let itlb <- mkDummyRVIMMU(getPMA, mainMemorySplitServer[3]);
    // two different paths for imem request to take: cached and uncached
    let icache <- mkDummyRVICache(mainMemorySplitServer[2]);
    let iuncached <- mkUncachedIMemConverter(uncachedMemSplitServer[1]);
    let dtlb <- mkDummyRVDMMU(False, getPMA, mainMemorySplitServer[1]);
    // two different paths for dmem request to take: cached and uncached
    let dcache <- mkDummyRVDCache(mainMemorySplitServer[0]);
    let duncached <- mkUncachedConverter(uncachedMemSplitServer[0]);
    // join cached and uncached paths to make a unified dmem interface
    function Bit#(1) whichServerData(RVDMemReq r);
        return (case (getPMA(r.addr))
                    MainMemory: 0; // cached
                    default: 1; // uncached
                endcase);
    endfunction
    function Bit#(1) whichServerInst(RVIMemReq r);
        return (case (getPMA(r))
                    MainMemory: 0; // cached
                    default: 1; // uncached
                endcase);
    endfunction
    function Bool getsResponse(RVDMemReq r);
        return (case (r.op) matches
                tagged Mem St: False;
                default: True;
            endcase);
    endfunction
    let dmem <- mkServerPortJoiner(whichServerData, getsResponse, 2, vec(dcache, duncached));
    let imem <- mkServerPortJoiner(whichServerInst, constFn(True), 2, vec(icache, iuncached));

    Vector#(numCores, MemorySystem) onecore;
    onecore[0] = (interface MemorySystem;
            interface ServerPort ivat = (interface ServerPort;
                                        interface InputPort request = itlb.request;
                                        interface OutputPort response = itlb.response;
                                    endinterface);
            interface ServerPort ifetch = imem;
            interface ServerPort dvat = (interface ServerPort;
                                        interface InputPort request = dtlb.request;
                                        interface OutputPort response = dtlb.response;
                                    endinterface);
            interface ServerPort dmem = dmem;
            interface ServerPort fence;
                interface InputPort request;
                    method Action enq(FenceReq f);
                        noAction;
                    endmethod
                    method Bool canEnq;
                        return True;
                    endmethod
                endinterface
                interface OutputPort response;
                    method FenceResp first;
                        return ?;
                    endmethod
                    method Action deq;
                        noAction;
                    endmethod
                    method Bool canDeq;
                        return True;
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
    interface ClientPort cachedMemory = mainMemoryClient;
    interface ClientPort uncachedMemory = uncachedMemClient;
    interface GenericMemServer extMemory = extMemServer;
endmodule
