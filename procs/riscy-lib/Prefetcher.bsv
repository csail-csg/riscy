
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
import Ehr::*;
import FIFO::*;
import GetPut::*;
import RVTypes::*;
import SpecialFIFOs::*;

typedef enum { Invalid, ValidReq, WaitingResp, ValidResp } PrefetcherState deriving (Bits, Eq, FShow);
typedef enum { Real, Prefetch } RealOrPrefetch deriving (Bits, Eq, FShow);

interface Prefetcher#(numeric type mainMemoryWidth);
    interface GenericMemServer#(mainMemoryWidth) toCache;
    method Action flush;
    method Bool flushDone;
endinterface

module mkBlockingPrefetcher#(GenericMemServer#(mainMemoryWidth) mainMem)(Prefetcher#(mainMemoryWidth));
    Reg#(Bool) flushing <- mkReg(False);

    FIFO#(GenericMemResp#(mainMemoryWidth)) respFIFO <- mkBypassFIFO;
    FIFO#(RealOrPrefetch) pendingReqFIFO <- mkFIFO;
    Ehr#(4, Maybe#(GenericMemReq#(mainMemoryWidth))) realReq <- mkEhr(tagged Invalid);
    Ehr#(4, GenericMemReq#(mainMemoryWidth)) prefetcherReq <- mkEhr(?); // stores data also
    Ehr#(4, PrefetcherState) prefetcherState <- mkEhr(tagged Invalid);
    Ehr#(4, Bool) prefetcherHit <- mkEhr(False);

    rule sendRequest(isValid(realReq[1]) || (prefetcherState[1] == ValidReq));
        // $fdisplay(stdout, "[PREFETCHER] send request");
        RealOrPrefetch reqType = ?;
        GenericMemReq#(mainMemoryWidth) req = ?;
        if (realReq[1] matches tagged Valid .validReq) begin
            reqType = Real;
            req = validReq;
            realReq[1] <= tagged Invalid;
        end else begin
            reqType = Prefetch;
            req = prefetcherReq[1];
            prefetcherState[1] <= WaitingResp;
        end
        mainMem.request.put(req);
        pendingReqFIFO.enq(reqType);
    endrule

    rule getResponse;
        // $fdisplay(stdout, "[PREFETCHER] get response");
        let resp <- mainMem.response.get;
        let respType = pendingReqFIFO.first;
        pendingReqFIFO.deq;

        if (respType == Real) begin
            // real request response
            respFIFO.enq(resp);
        end else begin
            // prefetcher response
            prefetcherReq[2].data <= resp.data;
            prefetcherState[2] <= ValidResp;
        end
    endrule

    rule handleHit(prefetcherHit[3] && prefetcherState[3] == ValidResp);
        // $fdisplay(stdout, "[PREFETCHER] sending response for hit");
        respFIFO.enq(GenericMemResp{write: False, data: prefetcherReq[3].data});
        // send another request
        let prefetchAddr = prefetcherReq[3].addr + fromInteger(valueOf(mainMemoryWidth) / 8);
        prefetcherReq[3] <= GenericMemReq{write: False, byteen: '1, addr: prefetchAddr, data: ?};
        prefetcherState[3] <= ValidReq;
        prefetcherHit[3] <= False;
    endrule

    rule doneFlushing(flushing && !prefetcherHit[0] && ((prefetcherState[0] == ValidResp) || (prefetcherState[0] == Invalid)));
        flushing <= False;
        prefetcherState[0] <= Invalid;
    endrule

    interface GenericMemServer toCache;
        interface Put request;
            method Action put(GenericMemReq#(mainMemoryWidth) req) if (!isValid(realReq[0]) && !prefetcherHit[0]);
                if (!req.write && (req.addr == prefetcherReq[0].addr) && (prefetcherState[0] == WaitingResp || prefetcherState[0] == ValidResp)) begin
                    // signal to the prefetcher to forward the response in the proper order
                    // $fdisplay(stdout, "[PREFETCHER] hit for address ", fshow(req.addr));
                    prefetcherHit[0] <= True;
                end else begin
                    // store the real (non-speculative) request
                    // $fdisplay(stdout, "[PREFETCHER] miss for address ", fshow(req.addr));
                    realReq[0] <= tagged Valid req;
                    // prefetch a new line
                    if ((prefetcherState[0] != WaitingResp) && !flushing) begin
                        let prefetchAddr = req.addr + fromInteger(valueOf(mainMemoryWidth) / 8);
                        // $fdisplay(stdout, "[PREFETCHER] prefetching for address ", fshow(prefetchAddr));
                        prefetcherReq[0] <= GenericMemReq{write: False, byteen: '1, addr: prefetchAddr, data: ?};
                        prefetcherState[0] <= ValidReq;
                    end
                end
            endmethod
        endinterface

        interface Get response;
            method ActionValue#(GenericMemResp#(mainMemoryWidth)) get;
                respFIFO.deq;
                return respFIFO.first;
            endmethod
        endinterface
    endinterface

    method Action flush;
        flushing <= True;
    endmethod

    method Bool flushDone;
        return !flushing;
    endmethod
endmodule
