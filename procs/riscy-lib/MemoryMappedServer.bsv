
// Copyright (c) 2017 Massachusetts Institute of Technology

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

/**
 * This package contains modules to create a memory mapped server from a
 * collection of `Reg#(Bit#(32))` interfaces.
 */
package MemoryMappedServer;

import ClientServer::*;
import GetPut::*;
import Vector::*;

import Ehr::*;
import Port::*;

import Abstraction::*;
import RVTypes::*;

/**
 * This module takes a vector of `Reg#(Bit#(32))` interfaces and creates a
 * memory mapped IO interface to these registers.
 *
 * Currently this only supports 32-bit reads and writes.
 */
module mkMemoryMappedServer#(Vector#(n, Reg#(Bit#(32))) regs)(Server#(UncachedMemReq, UncachedMemResp)) provisos (Add#(a__, TLog#(n), 64));
    Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(TLog#(n))))) pendingReq <- mkEhr(tagged Invalid);

    interface Put request;
        method Action put(UncachedMemReq req) if (!isValid(pendingReq[1]));
            Bit#(TLog#(n)) index = truncate(req.addr >> 2);
            // do write here
            if (req.write && (index <= fromInteger(valueOf(n)-1))) begin
                regs[index] <= truncate(req.data);
            end
            pendingReq[1] <= tagged Valid tuple2(req.write, index);
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(UncachedMemResp) get if (pendingReq[0] matches tagged Valid {.write, .index});
            // do read here
            Bit#(XLEN) read_data = 0;
            if (!write && (index <= fromInteger(valueOf(n)-1))) begin
                read_data = zeroExtend(regs[index]);
            end
            pendingReq[0] <= tagged Invalid;
            return UncachedMemResp{ write: write, data: read_data };
        endmethod
    endinterface
endmodule

/**
 * This module takes a vector of `Reg#(Bit#(32))` interfaces and creates a
 * memory mapped IO interface to these registers using a `ServerPort` instead
 * of a `Server`.
 *
 * Currently this only supports 32-bit reads and writes.
 */
module mkMemoryMappedServerPort#(Vector#(n, Reg#(Bit#(32))) regs)(ServerPort#(UncachedMemReq, UncachedMemResp)) provisos (Add#(a__, TLog#(n), 64));
    Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(TLog#(n))))) pendingReq <- mkEhr(tagged Invalid);

    interface InputPort request;
        method Action enq(UncachedMemReq req) if (!isValid(pendingReq[1]));
            Bit#(TLog#(n)) index = truncate(req.addr >> 2);
            // do write here
            if (req.write && (index <= fromInteger(valueOf(n)-1))) begin
                regs[index] <= truncate(req.data);
            end
            pendingReq[1] <= tagged Valid tuple2(req.write, index);
        endmethod
        method Bool canEnq;
            return !isValid(pendingReq[1]);
        endmethod
    endinterface
    interface OutputPort response;
        method UncachedMemResp first if (pendingReq[0] matches tagged Valid {.write, .index});
            // do read here
            Bit#(XLEN) read_data = 0;
            if (!write && (index <= fromInteger(valueOf(n)-1))) begin
                read_data = zeroExtend(regs[index]);
            end
            return UncachedMemResp{ write: write, data: read_data };
        endmethod
        method Action deq if (pendingReq[0] matches tagged Valid {.write, .index});
            pendingReq[0] <= tagged Invalid;
        endmethod
        method Bool canDeq;
            return isValid(pendingReq[0]);
        endmethod
    endinterface
endmodule

/**
 * This module takes a vector of `Reg#(Bit#(XLEN))` interfaces and creates a
 * memory mapped IO interface to these registers.
 *
 * Currently this only supports reading and writing XLEN bits at a time.
 */
module mkMemoryMappedServerFromRegXLEN#(Vector#(n, Reg#(Bit#(XLEN))) regs)(Server#(UncachedMemReq, UncachedMemResp)) provisos (Add#(a__, TLog#(n), 64));
    Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(TLog#(n))))) pendingReq <- mkEhr(tagged Invalid);

    interface Put request;
        method Action put(UncachedMemReq req) if (!isValid(pendingReq[1]));
            Bit#(TLog#(n)) index = truncate(req.addr >> valueOf(TLog#(TDiv#(XLEN,8))));
            // do write here
            if (req.write && (index <= fromInteger(valueOf(n)-1))) begin
                regs[index] <= req.data;
            end
            pendingReq[1] <= tagged Valid tuple2(req.write, index);
        endmethod
    endinterface
    interface Get response;
        method ActionValue#(UncachedMemResp) get if (pendingReq[0] matches tagged Valid {.write, .index});
            // do read here
            Bit#(XLEN) read_data = 0;
            if (!write && (index <= fromInteger(valueOf(n)-1))) begin
                read_data = regs[index];
            end
            pendingReq[0] <= tagged Invalid;
            return UncachedMemResp{ write: write, data: read_data };
        endmethod
    endinterface
endmodule

/**
 * This module takes a vector of `Reg#(Bit#(XLEN))` interfaces and creates a
 * memory mapped IO interface to these registers using a `ServerPort` instead
 * of a `Server`.
 */
module mkMemoryMappedServerPortFromRegXLEN#(Vector#(n, Reg#(Bit#(XLEN))) regs)(ServerPort#(UncachedMemReq, UncachedMemResp)) provisos (Add#(a__, TLog#(n), 64));
    Ehr#(2, Maybe#(Tuple2#(Bool, Bit#(TLog#(n))))) pendingReq <- mkEhr(tagged Invalid);

    interface InputPort request;
        method Action enq(UncachedMemReq req) if (!isValid(pendingReq[1]));
            Bit#(TLog#(n)) index = truncate(req.addr >> valueOf(TLog#(TDiv#(XLEN,8))));
            // do write here
            if (req.write && (index <= fromInteger(valueOf(n)-1))) begin
                regs[index] <= req.data;
            end
            pendingReq[1] <= tagged Valid tuple2(req.write, index);
        endmethod
        method Bool canEnq;
            return !isValid(pendingReq[1]);
        endmethod
    endinterface
    interface OutputPort response;
        method UncachedMemResp first if (pendingReq[0] matches tagged Valid {.write, .index});
            // do read here
            Bit#(XLEN) read_data = 0;
            if (!write && (index <= fromInteger(valueOf(n)-1))) begin
                read_data = regs[index];
            end
            return UncachedMemResp{ write: write, data: read_data };
        endmethod
        method Action deq if (pendingReq[0] matches tagged Valid {.write, .index});
            pendingReq[0] <= tagged Invalid;
        endmethod
        method Bool canDeq;
            return isValid(pendingReq[0]);
        endmethod
    endinterface
endmodule

endpackage
