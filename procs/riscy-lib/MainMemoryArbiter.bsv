
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
import ClientServer::*;
import Connectable::*;
import GetPut::*;
import FIFO::*;
import PrintTrace::*;
import RVTypes::*;
import Vector::*;

interface GenericMemoryArbiter#(numeric type ports, numeric type dataWidth);
    interface Vector#(ports, GenericMemServer#(dataWidth)) servers;
    interface GenericMemClient#(dataWidth) client;
endinterface

module mkGenericMemoryArbiter(GenericMemoryArbiter#(ports, dataWidth));
    // XXX: These expect provisos that aren't assumed
    // Bool verbose = False;
    // File tracefile = verbose ? stdout : tagged InvalidFile;
    // FIFO#(GenericMemReq#(dataWidth, Tuple2#(Bit#(TLog#(ports)), inputTag))) memReqFifo <- fprintTraceM(tracefile, "GenericMemoryArbiter::memReqFifo", mkFIFO);
    // FIFO#(GenericMemResp#(dataWidth, Tuple2#(Bit#(TLog#(ports)), inputTag))) memRespFifo <- fprintTraceM(tracefile, "GenericMemoryArbiter::memRespFifo", mkFIFO);

    FIFO#(GenericMemReq#(dataWidth)) memReqFifo <- mkFIFO;
    FIFO#(GenericMemResp#(dataWidth)) memRespFifo <- mkFIFO;
    FIFO#(Bit#(TLog#(ports))) pendingReqs <- mkSizedFIFO(8);

    function Server#(GenericMemReq#(dataWidth), GenericMemResp#(dataWidth)) makeServerIFC(Integer portNum);
        return (interface Server;
                    interface Put request;
                        method Action put(GenericMemReq#(dataWidth) r);
                            memReqFifo.enq(r);
                            pendingReqs.enq(fromInteger(portNum));
                        endmethod
                    endinterface
                    interface Get response;
                        method ActionValue#(GenericMemResp#(dataWidth)) get if (pendingReqs.first == fromInteger(portNum));
                            pendingReqs.deq;
                            memRespFifo.deq;
                            return memRespFifo.first;
                        endmethod
                    endinterface
                endinterface);
    endfunction

    interface Vector servers = genWith(makeServerIFC);

    interface Client client;
        interface Get request = toGet(memReqFifo);
        interface Put response = toPut(memRespFifo);
    endinterface
endmodule

module mkGenericMemoryArbiterExtraFIFOs(GenericMemoryArbiter#(ports, dataWidth));
    // XXX: These expect provisos that aren't assumed
    // Bool verbose = False;
    // File tracefile = verbose ? stdout : tagged InvalidFile;
    // FIFO#(GenericMemReq#(dataWidth, Tuple2#(Bit#(TLog#(ports)), inputTag))) memReqFifo <- fprintTraceM(tracefile, "GenericMemoryArbiter::memReqFifo", mkFIFO);
    // FIFO#(GenericMemResp#(dataWidth, Tuple2#(Bit#(TLog#(ports)), inputTag))) memRespFifo <- fprintTraceM(tracefile, "GenericMemoryArbiter::memRespFifo", mkFIFO);

    FIFO#(GenericMemReq#(dataWidth)) memReqFifo <- mkFIFO;
    FIFO#(GenericMemResp#(dataWidth)) memRespFifo <- mkFIFO;
    FIFO#(Bit#(TLog#(ports))) pendingReqs <- mkSizedFIFO(8);

    // These are extra FIFOs that may be necessary to avoid deadlock
    Vector#(ports, FIFO#(GenericMemReq#(dataWidth))) serverReqFifos <- replicateM(mkFIFO);
    Vector#(ports, FIFO#(GenericMemResp#(dataWidth))) serverRespFifos <- replicateM(mkFIFO);

    function Server#(GenericMemReq#(dataWidth), GenericMemResp#(dataWidth)) makeServerIFC(Integer portNum);
        return (interface Server;
                    interface Put request;
                        method Action put(GenericMemReq#(dataWidth) r);
                            memReqFifo.enq(r);
                            pendingReqs.enq(fromInteger(portNum));
                        endmethod
                    endinterface
                    interface Get response;
                        method ActionValue#(GenericMemResp#(dataWidth)) get if (pendingReqs.first == fromInteger(portNum));
                            pendingReqs.deq;
                            memRespFifo.deq;
                            return memRespFifo.first;
                        endmethod
                    endinterface
                endinterface);
    endfunction

    for (Integer i = 0 ; i < valueOf(ports) ; i = i+1) begin
        mkConnection(makeServerIFC(i).request, toGet(serverReqFifos[i]));
        mkConnection(makeServerIFC(i).response, toPut(serverRespFifos[i]));
    end

    interface Vector servers = zipWith(toGPServer, serverReqFifos, serverRespFifos);

    interface Client client;
        interface Get request = toGet(memReqFifo);
        interface Put response = toPut(memRespFifo);
    endinterface
endmodule

interface MainMemoryArbiter#(numeric type dataWidth);
    interface GenericMemServer#(dataWidth) iMMU;
    interface GenericMemServer#(dataWidth) iCache;
    interface GenericMemServer#(dataWidth) dMMU;
    interface GenericMemServer#(dataWidth) dCache;
    interface GenericMemClient#(dataWidth) mainMemory;
endinterface

module mkMainMemoryArbiter(MainMemoryArbiter#(dataWidth));
    (* hide *)
    GenericMemoryArbiter#(4, dataWidth) _arbiter <- mkGenericMemoryArbiter;

    interface Server iMMU = _arbiter.servers[0];
    interface Server iCache = _arbiter.servers[1];
    interface Server dMMU = _arbiter.servers[2];
    interface Server dCache = _arbiter.servers[3];

    interface Client mainMemory = _arbiter.client;
endmodule

module mkMainMemoryArbiterExtraFIFOs(MainMemoryArbiter#(dataWidth));
    (* hide *)
    GenericMemoryArbiter#(4, dataWidth) _arbiter <- mkGenericMemoryArbiterExtraFIFOs;

    interface Server iMMU = _arbiter.servers[0];
    interface Server iCache = _arbiter.servers[1];
    interface Server dMMU = _arbiter.servers[2];
    interface Server dCache = _arbiter.servers[3];

    interface Client mainMemory = _arbiter.client;
endmodule

typedef union tagged {
    void Cached;
    struct {
        RVMemSize size;
        Bool isUnsigned;
    } Uncached;
} MemRegion deriving (Bits, Eq, FShow);
module mkUncachedSplitter#(Addr mmiobase, Server#(RVDMemReq, RVDMemResp) cache, UncachedMemServer uncachedMem)(Server#(RVDMemReq, RVDMemResp));
    // True if cached, False if uncached
    FIFO#(MemRegion) bookkeepingFIFO <- mkSizedFIFO(4);

    rule dropWriteResp(bookkeepingFIFO.first matches tagged Uncached .*);
        let x <- uncachedMem.response.get;
        when( x.write == True, noAction );
        bookkeepingFIFO.deq;
    endrule

    interface Put request;
        method Action put(RVDMemReq r);
            if (r.addr >= mmiobase) begin
                uncachedMem.request.put( UncachedMemReq {
                        write: r.op == tagged Mem St,
                        size: r.size,
                        addr: r.addr,
                        data: r.data
                    } );
                bookkeepingFIFO.enq(tagged Uncached {size: r.size, isUnsigned: r.isUnsigned});
            end else begin
                cache.request.put(r);
                // The cache doesn't respond to stores, so don't always enqueue
                // into the bookkeeping FIFO
                if (getsResponse(r.op)) begin
                    bookkeepingFIFO.enq(tagged Cached);
                end
            end
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(RVDMemResp) get;
            Data result = 0;
            case (bookkeepingFIFO.first) matches
                tagged Cached:
                    begin
                        result <- cache.response.get;
                    end
                tagged Uncached .x:
                    begin
                        let uncachedResp <- uncachedMem.response.get;
                        when(uncachedResp.write == False, noAction);
                        result = uncachedResp.data;
                        let extend = x.isUnsigned ? zeroExtend : signExtend;
                        result = (case (x.size)
                                B: extend(result[7:0]);
                                H: extend(result[15:0]);
                                W: extend(result[31:0]);
                                D: result[63:0];
                            endcase);
                    end
            endcase
            bookkeepingFIFO.deq;
            return result;
        endmethod
    endinterface
endmodule
