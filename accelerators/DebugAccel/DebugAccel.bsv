
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

import FIFO::*;
import Vector::*;

interface DebugAccelRequest;
    method Action printChar(Bit#(8) x);
endinterface

interface DebugAccelPins;
    method ActionValue#(Bit#(8)) charOut;
endinterface

interface DebugAccel;
    interface DebugAccelRequest debugAccelRequest;
    // interface DebugAccelPins debugAccelPins;
endinterface

module mkDebugAccel(DebugAccel);
    Reg#(Maybe#(Bit#(8))) lastChar <- mkReg(tagged Invalid);

    interface DebugAccelRequest debugAccelRequest;
        method Action printChar(Bit#(8) x);
            $fwrite(stderr, "%c", x);
            $fflush(stderr);
            lastChar <= tagged Valid x;
        endmethod
    endinterface

    // interface DebugAccelPins debugAccelPins;
    //     method ActionValue#(Bit#(8)) charOut if (lastChar matches tagged Valid .c);
    //         lastChar <= tagged Invalid;
    //         return c;
    //     endmethod
    // endinterface
endmodule
