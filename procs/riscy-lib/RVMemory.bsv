
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

function Bit#(xlen) addrCalc(Bit#(xlen) rVal1, Maybe#(Bit#(xlen)) imm);
    return rVal1 + fromMaybe(0, imm);
endfunction

//function Data gatherLoad(Addr addr, ByteEn byteEn, Bool unsignedLd, Data data);
//    function extend = unsignedLd ? zeroExtend : signExtend;
//    Bit#(IndxShamt) offset = truncate(addr);
//
//    if(byteEn[7]) begin
//        return extend(data);
//    end else if(byteEn[3]) begin
//        Vector#(2, Bit#(32)) dataVec = unpack(data);
//        return extend(dataVec[offset[2]]);
//    end else if(byteEn[1]) begin
//        Vector#(4, Bit#(16)) dataVec = unpack(data);
//        return extend(dataVec[offset[2:1]]);
//    end else begin
//        Vector#(8, Bit#(8)) dataVec = unpack(data);
//        return extend(dataVec[offset]);
//    end
//endfunction
//
//function Tuple2#(ByteEn, Data) scatterStore(Addr addr, ByteEn byteEn, Data data);
//    Bit#(IndxShamt) offset = truncate(addr);
//    if(byteEn[7]) begin
//        return tuple2(byteEn, data);
//    end else if(byteEn[3]) begin
//        return tuple2(unpack(pack(byteEn) << (offset)), data << {(offset), 3'b0});
//    end else if(byteEn[1]) begin
//        return tuple2(unpack(pack(byteEn) << (offset)), data << {(offset), 3'b0});
//    end else begin
//        return tuple2(unpack(pack(byteEn) << (offset)), data << {(offset), 3'b0});
//    end
//endfunction

