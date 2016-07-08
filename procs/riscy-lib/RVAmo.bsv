
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

import RVTypes::*;
import Vector::*;

(* noinline *)
function Data amoExec(RVAmoOp amoFunc, DataByteEn permutedDataByteEn, Data currentData, Data inData);
    Data newData = 0;
    Data oldData = currentData;

    // This is a leftover from the old byteEn type
    Vector#(TDiv#(DataSz,8), Bool) byteEn = unpack(permutedDataByteEn);
    function Bit#(8) byteEnToBitMask(Bool en);
        return en ? 8'hFF : 8'h00;
    endfunction
    Data bitMask = pack(map(byteEnToBitMask, byteEn));

    Data currentDataMasked = currentData & bitMask;
    Data inDataMasked = inData & bitMask;

    // special case for sign extension
    if (amoFunc == Min || amoFunc == Max) begin
        if (byteEn == unpack(8'b00001111)) begin
            // sign extend if necessary
            currentDataMasked[63:32] = currentDataMasked[31] == 1 ? '1 : 0;
            inDataMasked[63:32] = inDataMasked[31] == 1 ? '1 : 0;
        end
    end

    function Bit#(t) sMax( Bit#(t) a, Bit#(t) b );
        Int#(t) x = max(unpack(a), unpack(b));
        return pack(x);
    endfunction
    function Bit#(t) sMin( Bit#(t) a, Bit#(t) b );
        Int#(t) x = min(unpack(a), unpack(b));
        return pack(x);
    endfunction
    function Bit#(t) uMax( Bit#(t) a, Bit#(t) b );
        UInt#(t) x = max(unpack(a), unpack(b));
        return pack(x);
    endfunction
    function Bit#(t) uMin( Bit#(t) a, Bit#(t) b );
        UInt#(t) x = min(unpack(a), unpack(b));
        return pack(x);
    endfunction

    newData = (case (amoFunc)
            Swap: inDataMasked;
            Add:  (currentDataMasked + inDataMasked);
            Xor:  (currentDataMasked ^ inDataMasked);
            And:  (currentDataMasked & inDataMasked);
            Or:   (currentDataMasked | inDataMasked);
            Min:  sMin(currentDataMasked, inDataMasked);
            Max:  sMax(currentDataMasked, inDataMasked);
            Minu: uMin(currentDataMasked, inDataMasked);
            Maxu: uMax(currentDataMasked, inDataMasked);
        endcase);
    newData = (oldData & ~bitMask) | (newData & bitMask);

    return newData;
endfunction
