
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

import Abstraction::*;
import BasicMemorySystemBlocks::*;
import BRAMTightlyCoupledMemory::*;
import RVTypes::*;

interface TightlyCoupledMemorySystem;
    interface Server#(RVIMemReq, RVIMemResp) ifetch;
    interface Server#(RVDMemReq, RVDMemResp) dmem;
    interface UncachedMemClient mmio;
    interface Server#(GenericMemReq#(XLEN), GenericMemResp#(XLEN)) ext;
endinterface

module mkTightlyCoupledMemorySystem(TightlyCoupledMemorySystem);
    Bool verbose = False;
    File tracefile = verbose ? stdout : tagged InvalidFile;

    // uncached port -- works on XLEN-bit words
    FIFO#(UncachedMemReq) uncachedReqFIFO <- mkFIFO;
    FIFO#(UncachedMemResp) uncachedRespFIFO <- mkFIFO;
    let uncachedMemClient = toGPClient(uncachedReqFIFO, uncachedRespFIFO);
    let mmio_server <- mkUncachedConverter(toGPServer(uncachedReqFIFO, uncachedRespFIFO));

    // Shared I/D Memory
    let sram <- mkBramIDExtMem;

    // address decoding the dmem port of the sram for uncachedMemClient
    function Bit#(1) whichServer(RVDMemReq r);
        return (r.addr >= 'h4000_0000) ? 1 : 0;
    endfunction
    function Bool getsResponse(RVDMemReq r);
        return r.op != tagged Mem St;
    endfunction
    let proc_dmem <- mkServerJoiner(whichServer, getsResponse, 2, vec(sram.dmem, mmio_server));

    interface Server ifetch = fprintTrace(tracefile, "Proc-IMem", sram.imem);
    interface Server dmem = fprintTrace(tracefile, "Proc-DMem", proc_dmem);

    interface Client mmio = uncachedMemClient;

    // External memory requests and responses
    interface Server ext = fprintTrace(tracefile, "ExtMem", sram.ext);
endmodule
