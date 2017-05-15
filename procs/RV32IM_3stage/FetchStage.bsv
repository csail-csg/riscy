
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

import GetPut::*;

import Port::*;
import MemUtil::*;

import RVTypes::*;
import CoreStates::*;

interface FetchStage;
endinterface

typedef struct {
    Reg#(Maybe#(FetchState#(xlen))) fs;
    Reg#(Maybe#(ExecuteState#(xlen))) es;
    InputPort#(ReadOnlyMemReq#(xlen, 2)) ifetchreq;
} FetchRegs#(numeric type xlen);

module mkFetchStage#(FetchRegs#(xlen) fr)(FetchStage);
    let ifetchreq = fr.ifetchreq;

    rule doFetch(fr.fs matches tagged Valid .fetchState
                    &&& fr.es == tagged Invalid);
        // get and clear the fetch state
        let pc = fetchState.pc;
        fr.fs <= tagged Invalid;

        // request instruction
        ifetchreq.enq(ReadOnlyMemReq{ addr: pc });

        // pass to execute state
        fr.es <= tagged Valid ExecuteState{ poisoned: False, pc: pc };
    endrule
endmodule
