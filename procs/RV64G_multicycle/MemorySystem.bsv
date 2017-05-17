
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
import MemUtil::*;
import Port::*;
import PortUtil::*;
import PrintTrace::*;

import BasicMemorySystemBlocks::*;
import Abstraction::*;
import RVTypes::*;

interface MemorySystem#(numeric type xlen);
    // To Front-End
    interface ServerPort#(RVIMMUReq#(xlen), RVIMMUResp#(xlen)) ivat;
    interface ReadOnlyMemServerPort#(xlen, 2) ifetch; // ifetch is a 32-bit interface
    // To Back-End
    interface ServerPort#(RVDMMUReq#(xlen), RVDMMUResp#(xlen)) dvat;
    interface AtomicMemServerPort#(xlen, TLog#(TDiv#(xlen,8))) dmem;
    interface ServerPort#(FenceReq, FenceResp) fence;
    method Action updateVMInfoI(VMInfo#(xlen) vmI);
    method Action updateVMInfoD(VMInfo#(xlen) vmD);
endinterface

interface MulticoreMemorySystem#(numeric type xlen, numeric type numCores, numeric type mainMemWidth);
    interface Vector#(numCores, MemorySystem#(xlen)) core;
    // To main memory and devices
    interface CoarseMemClientPort#(xlen, TLog#(TDiv#(xlen,8))) cachedMemory;
    interface AtomicMemClientPort#(xlen, TLog#(TDiv#(xlen,8))) uncachedMemory;
    // Memory requests from external devices
    interface CoarseMemServerPort#(xlen, TLog#(TDiv#(xlen,8))) extMemory;
endinterface

typedef MulticoreMemorySystem#(xlen, 1, mainMemWidth) SingleCoreMemorySystem#(numeric type xlen, numeric type mainMemWidth);


module mkBasicMemorySystem#(function PMA getPMA(PAddr addr))(SingleCoreMemorySystem#(xlen, DataSz))
        provisos (NumAlias#(xlen, XLEN)); // TODO: make this a parameter
    // Main Memory CoarseMem Interface
    FIFOG#(CoarseMemReq#(xlen, TLog#(TDiv#(xlen,8)))) mainMemReqFIFO <- mkFIFOG;
    FIFOG#(CoarseMemResp#(TLog#(TDiv#(xlen,8)))) mainMemRespFIFO <- mkFIFOG;
    let mainMemoryServer = toServerPort(mainMemReqFIFO, mainMemRespFIFO);
    let mainMemoryClient = toClientPort(mainMemReqFIFO, mainMemRespFIFO);

    // MMIO AtomicMem Interface
    FIFOG#(AtomicMemReq#(xlen, TLog#(TDiv#(xlen,8)))) uncachedReqFIFO <- mkFIFOG;
    FIFOG#(AtomicMemResp#(TLog#(TDiv#(xlen,8)))) uncachedRespFIFO <- mkFIFOG;
    let uncachedMemServer = toServerPort(uncachedReqFIFO, uncachedRespFIFO);
    let uncachedMemClient = toClientPort(uncachedReqFIFO, uncachedRespFIFO);

    // splits cached memory port for itlb, imem, dtlb, and dmem
    Vector#(5, CoarseMemServerPort#(xlen, TLog#(TDiv#(xlen,8)))) mainMemorySplitServer <- mkFixedPriorityServerPortSplitter(constFn(True), 2, mainMemoryServer);

    Vector#(2, AtomicMemServerPort#(xlen, TLog#(TDiv#(xlen,8)))) uncachedMemSplitServer <- mkFixedPriorityServerPortSplitter(constFn(True), 2, uncachedMemServer);

    // extMemServer -- works on 64-bit words
    let extMemServer = mainMemorySplitServer[4];

    let itlb <- mkDummyRVIMMU64(getPMA, mainMemorySplitServer[3]);
    // two different paths for imem request to take: cached and uncached
    let icache = simplifyMemServerPort(mainMemorySplitServer[2]);
    // let icache <- mkDummyRVICache(mainMemorySplitServer[2]);
    // was mkUncachedIMemConverter:
    let iuncached = simplifyMemServerPort(uncachedMemSplitServer[1]);

    let dtlb <- mkDummyRVDMMU64(False, getPMA, mainMemorySplitServer[1]);
    // two different paths for dmem request to take: cached and uncached
    // let dcache <- mkDummyRVDCache(mainMemorySplitServer[0]);
    let dcache <- mkEmulateMemServerPort(mainMemorySplitServer[0]);
    // let duncached <- mkUncachedConverter(uncachedMemSplitServer[0]); // TODO: reimplement me
    let duncached = uncachedMemSplitServer[0];

    // join cached and uncached paths to make a unified dmem interface
    function Bit#(1) whichServerData(AtomicMemReq#(xlen, TLog#(TDiv#(xlen,8))) r);
        return (case (getPMA(r.addr))
                    MainMemory: 0; // cached
                    default: 1; // uncached
                endcase);
    endfunction
    function Bit#(1) whichServerInst(ReadOnlyMemReq#(xlen, TLog#(TDiv#(xlen,8))) r);
        return (case (getPMA(r.addr))
                    MainMemory: 0; // cached
                    default: 1; // uncached
                endcase);
    endfunction
    let dmem <- mkServerPortJoiner(whichServerData, constFn(True), 2, vec(dcache, duncached));
    ReadOnlyMemServerPort#(xlen, TLog#(TDiv#(xlen,8))) imem <- mkServerPortJoiner(whichServerInst, constFn(True), 2, vec(icache, iuncached));
    let imem_32bit <- mkNarrowerMemServerPort(imem);

    Vector#(numCores, MemorySystem#(xlen)) onecore;
    onecore[0] = (interface MemorySystem;
            interface ServerPort ivat = (interface ServerPort;
                                        interface InputPort request = itlb.request;
                                        interface OutputPort response = itlb.response;
                                    endinterface);
            interface ServerPort ifetch = imem_32bit;
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
            method Action updateVMInfoI(VMInfo#(xlen) vmI);
                itlb.updateVMInfo(vmI);
            endmethod
            method Action updateVMInfoD(VMInfo#(xlen) vmD);
                dtlb.updateVMInfo(vmD);
            endmethod
        endinterface);
    interface Vector core = onecore;
    interface ClientPort cachedMemory = mainMemoryClient;
    interface ClientPort uncachedMemory = uncachedMemClient;
    interface GenericMemServer extMemory = extMemServer;
endmodule
