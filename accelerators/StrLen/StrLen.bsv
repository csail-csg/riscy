
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

interface StrLenRequest;
    // x is the address of the c string
    method Action request(Bit#(64) x);
endinterface

interface StrLenIndication;
    // returns the length of the c string
    method Action response(Bit#(32) x);
endinterface

interface StrLenPins;
    method ActionValue#(Bit#(64)) readReq;
    method Action readData(Bit#(64) x);
endinterface

interface StrLenAccelerator;
    interface StrLenRequest strLenRequest;
    interface StrLenPins strLenPins;
endinterface

module mkStrLen#(StrLenIndication strLenIndication)(StrLenAccelerator);
    FIFO#(Bit#(64)) requestFIFO <- mkFIFO;
    FIFO#(Bit#(64)) responseFIFO <- mkFIFO;

    Reg#(Bool) running <- mkReg(False);
    Reg#(Bit#(64)) reqAddr <- mkReg(0);
    Reg#(Bit#(64)) respAddr <- mkReg(0);
    Reg#(Bit#(32)) count <- mkReg(0);

    rule strLenReqStep(running);
        // send a request
        let alignedReqAddr = reqAddr & ~'h07;
        requestFIFO.enq(alignedReqAddr);
        // and increment
        reqAddr <= alignedReqAddr + 8;
    endrule
    rule strLenRespStep(running);
        // get a response
        let data = responseFIFO.first;
        responseFIFO.deq;

        Vector#(8, Bit#(8)) bytes = unpack(data);
        let alignment = respAddr & 'h07;
        function Bool eqZero(Bit#(8) x);
            return x == 0;
        endfunction
        Vector#(8, Bool) zeroBytes = map( eqZero, bytes );
        // Vector#(8, Bool) zeroBytes = map( \== (0), bytes );
        Vector#(8, Bool) bytesInRange = unpack('1 << alignment[2:0]);
        function Bool boolAnd(Bool x, Bool y);
            return x && y;
        endfunction
        Bit#(8) zeroBytesToCount = pack(zipWith( boolAnd, zeroBytes, bytesInRange));
        // Bit#(8) zeroBytesToCount = pack(zipWith( \&& , zeroBytes, bytesInRange));
        Integer newBytes = (case (zeroBytesToCount) matches
                                8'b00000000: 8;
                                8'b10000000: 7;
                                8'b?1000000: 6;
                                8'b??100000: 5;
                                8'b???10000: 4;
                                8'b????1000: 3;
                                8'b?????100: 2;
                                8'b??????10: 1;
                                8'b???????1: 0;
                            endcase);
        let newCount = count + fromInteger(newBytes) - truncate(alignment);
        count <= newCount;
        respAddr <= (respAddr & ~'h07) + 8;
        if (newBytes != 8) begin
            running <= False;
            strLenIndication.response(newCount);
        end
    endrule
    rule strLenRespDrain(!running);
        respAddr <= (respAddr & ~'h07) + 8;
        responseFIFO.deq;
    endrule

    interface StrLenRequest strLenRequest;
        method Action request(Bit#(64) x) if (!running && (reqAddr == respAddr));
            respAddr <= x;
            reqAddr <= x;
            running <= True;
            count <= 0;
        endmethod
    endinterface

    interface StrLenPins strLenPins;
        method ActionValue#(Bit#(64)) readReq;
            requestFIFO.deq;
            return requestFIFO.first;
        endmethod
        method Action readData(Bit#(64) x);
            responseFIFO.enq(x);
        endmethod
    endinterface
endmodule
