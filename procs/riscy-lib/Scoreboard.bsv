
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

import SearchFIFO::*;
import RVTypes::*;

interface Scoreboard#(numeric type size);
    method Action insert(Maybe#(FullRegIndex) fullRegIndex);
    method Action remove;
    method Bool search1(Maybe#(FullRegIndex) fullRegIndex);
    method Bool search2(Maybe#(FullRegIndex) fullRegIndex);
    method Bool search3(Maybe#(FullRegIndex) fullRegIndex);
    method Bool notEmpty;
    method Action clear;
endinterface

module mkScoreboard(Scoreboard#(size));
    function Bool isFound(Maybe#(FullRegIndex) x, Maybe#(FullRegIndex) y);
        return isValid(x) && isValid(y) && x == y;
    endfunction

    SearchFIFO#(size, Maybe#(FullRegIndex), Maybe#(FullRegIndex)) f <- mkSearchFIFO(isFound);

    method insert = f.enq;
    method remove = f.deq;
    method search1 = f.search;
    method search2 = f.search;
    method search3 = f.search;
    method notEmpty = f.notEmpty;
    method clear = f.clear;
endmodule

// scoreboard for bypassing
module mkBypassingScoreboard(Scoreboard#(size));
    function Bool isFound(Maybe#(FullRegIndex) x, Maybe#(FullRegIndex) y);
        return isValid(x) && isValid(y) && x == y;
    endfunction

    SearchFIFO#(size, Maybe#(FullRegIndex), Maybe#(FullRegIndex)) f <- mkPipelineSearchFIFO(isFound);

    method insert = f.enq;
    method remove = f.deq;
    method search1 = f.search;
    method search2 = f.search;
    method search3 = f.search;
    method notEmpty = f.notEmpty;
    method clear = f.clear;
endmodule

