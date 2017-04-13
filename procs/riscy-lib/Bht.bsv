
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

import RVTypes::*;
import RegFile::*;
import Vector::*;

interface DirPred;
    method Bool dirPred(Addr pc);
    method Action update(Addr pc, Bool taken);
endinterface

// Local BHT Typedefs
typedef 64 BhtEntries;
typedef Bit#(TLog#(BhtEntries)) BhtIndex;

(* synthesize, gate_all_clocks *)
module mkBht(DirPred);
    // Read and Write ordering doesn't matter since this is a predictor
    // mkRegFileWCF is the RegFile version of mkConfigReg
    RegFile#(BhtIndex, Bit#(2)) hist <- mkRegFileWCF(0,fromInteger(valueOf(BhtEntries)-1));

    function BhtIndex getIndex(Addr pc);
        return truncate(pc >> 2);
    endfunction

    method Bool dirPred(Addr pc);
        let index = getIndex(pc);
        return unpack(hist.sub(index)[1]);
    endmethod

    method Action update(Addr pc, Bool taken);
        let index = getIndex(pc);
        let current_hist = hist.sub(index);
        Bit#(2) next_hist;
        if(taken) begin
            next_hist = (current_hist == 2'b11) ? 2'b11 : current_hist + 1;
        end else begin
            next_hist = (current_hist == 2'b00) ? 2'b00 : current_hist - 1;
        end
        hist.upd(index, next_hist);
    endmethod
endmodule

