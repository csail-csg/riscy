
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

function Bit#(xlen) execControl(BrFunc brFunc, Bit#(xlen) rVal1, Bit#(xlen) rVal2, Maybe#(Bit#(xlen)) imm, Bit#(xlen) pc);
    // XXX: This should only be used with a valid imm
    Bool taken = aluBr(brFunc, rVal1, rVal2);
    Bit#(xlen) targetPc = brAddrCalc(brFunc, pc, rVal1, fromMaybe(?, imm));
    return taken ? targetPc : (pc + 4);
endfunction

function Bool aluBr(BrFunc brFunc, Bit#(xlen) a, Bit#(xlen) b);
    Bool eq = (a == b);
    Bool lt = signedLT(a,b);
    Bool ltu = (a < b);
    Bool brTaken = (case(brFunc)
            Eq:         eq;
            Neq:        (!eq);
            Lt:         lt;
            Ltu:        ltu;
            Ge:         (!lt);
            Geu:        (!ltu);
            Jal:        True;
            Jalr:       True;
            default:    True;
        endcase);
    return brTaken;
endfunction

function Bit#(xlen) brAddrCalc(BrFunc brFunc, Bit#(xlen) pc, Bit#(xlen) val, Bit#(xlen) imm);
    Bit#(xlen) in1 = (brFunc == Jalr) ? val : pc;
    Bit#(xlen) addOut = in1 + imm;
    // if JALR, zero LSB
    Bit#(xlen) targetAddr = (brFunc == Jalr) ? (addOut & (~1)) : addOut;
    return targetAddr;

    // XXX: Old implementation
    // Addr targetAddr = (case (brFunc)
    //         Jal:        (pc + imm);
    //         Jalr:       {(val + imm)[valueOf(AddrSz)-1:1], 1'b0};
    //         default:    (pc + imm);
    //     endcase);
    // return targetAddr;
endfunction

