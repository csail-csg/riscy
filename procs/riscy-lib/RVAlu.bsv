
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

`include "ProcConfig.bsv"

import RVTypes::*;

(* noinline *)
function Data execAluInst(AluInst aluInst, Data rVal1, Data rVal2, Maybe#(Data) imm, Data pc);
    Data aluVal1 = (case (aluInst.op)
                        Auipc:   pc;
                        Lui:     0;
                        default: rVal1;
                    endcase);
    Data aluVal2 = (case (imm) matches
                        tagged Valid .validImm: validImm;
                        default:                rVal2;
                    endcase);

`ifdef rv64
    Data data = alu64(aluInst.op, aluInst.w, aluVal1, aluVal2);
`else
    Data data = alu32(aluInst.op, aluVal1, aluVal2);
`endif

    return data;
endfunction

// RV64 ALU -- no need to use Data or other similar types because this has the
// "w" field only seen in 64-bit RISC-V, but it doesn't have the necessary
// inputs for 128-bit RISC-V
(* noinline *)
function Bit#(64) alu64(AluFunc func, Bool w, Bit#(64) a, Bit#(64) b);
    // setup inputs
    if (w) begin
        a = (func == Sra) ? signExtend(a[31:0]) : zeroExtend(a[31:0]);
        b = zeroExtend(b[31:0]);
    end
    Bit#(6) shamt = truncate(b);
    if (w) begin
        shamt = {1'b0, shamt[4:0]};
    end

    Bit#(64) res = (case(func)
            Add:        (a + b);
            Sub:        (a - b);
            And:        (a & b);
            Or:         (a | b);
            Xor:        (a ^ b);
            Slt:        zeroExtend( pack( signedLT(a, b) ) );
            Sltu:       zeroExtend( pack( a < b ) );
            Sll:        (a << shamt);
            Srl:        (a >> shamt);
            Sra:        signedShiftRight(a, shamt);
            Auipc:      (a + b);
            Lui:        (a + b);
            default:    0;
        endcase);

    if (w) begin
        res = signExtend(res[31:0]);
    end

    return res;
endfunction

// RV32 ALU -- no need to use Data or other similar types because this doesn't
// have the support necessary for larger ISAs
(* noinline *)
function Bit#(32) alu32(AluFunc func, Bit#(32) a, Bit#(32) b);
    // setup inputs
    Bit#(5) shamt = truncate(b);

    Bit#(32) res = (case(func)
            Add:        (a + b);
            Sub:        (a - b);
            And:        (a & b);
            Or:         (a | b);
            Xor:        (a ^ b);
            Slt:        zeroExtend( pack( signedLT(a, b) ) );
            Sltu:       zeroExtend( pack( a < b ) );
            Sll:        (a << shamt);
            Srl:        (a >> shamt);
            Sra:        signedShiftRight(a, shamt);
            Auipc:      (a + b);
            Lui:        (a + b);
            default:    0;
        endcase);

    return res;
endfunction

