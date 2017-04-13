
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

import RegFile::*;
import RVTypes::*;
import Vector::*;

interface ReturnAddrStack;
    method Action pushAddress(Addr a);
    method ActionValue#(Addr) popAddress();
endinterface

// Local RAS Typedefs
typedef 8 RasEntries;
typedef Bit#(TLog#(RasEntries)) RasIndex;

(* synthesize, gate_all_clocks *)
module mkRas( ReturnAddrStack );
    Vector#(RasEntries, Reg#(Addr)) stack <- replicateM(mkReg(0));

    // head points past valid data
    // to gracefully overflow, head is allowed to overflow to 0 and overwrite the oldest data
    Reg#(RasIndex) head <- mkReg(0);

    RasIndex max_head = fromInteger(valueOf(RasEntries)-1);

    method Action pushAddress(Addr a);
        stack[head] <= a;
        head <= (head == max_head) ? 0 : head + 1;
    endmethod

    method ActionValue#(Addr) popAddress();
        let new_head = (head == 0) ? max_head : head - 1;
        head <= new_head;
        return stack[new_head];
    endmethod
endmodule
