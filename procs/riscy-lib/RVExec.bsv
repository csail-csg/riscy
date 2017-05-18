
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

import RVDecode::*;
import RVTypes::*;
import Vector::*;

import RVAlu::*;
import RVControl::*;
import RVMemory::*;

typedef struct {
    Bit#(xlen) data;
    Bit#(xlen) addr;
    Bool taken;
    Bit#(xlen) nextPc;
} ExecResult#(numeric type xlen) deriving (Bits, Eq, FShow);

// Reference implementation of the exec function
// This is an inefficient implementation because many of the functions used
// in the case statement can reuse hardware
(* noinline *)
function ExecResult#(xlen) execRef(RVDecodedInst dInst, Bit#(xlen) rVal1, Bit#(xlen) rVal2, Bit#(xlen) pc)
        provisos (NumAlias#(XLEN, xlen));
    Bit#(xlen) data = 0;
    Bit#(xlen) addr = 0;
    Bit#(xlen) pcPlus4 = pc + 4;
    Bool taken = False;
    Bit#(xlen) nextPc = pcPlus4;

    Maybe#(Bit#(xlen)) imm = getImmediate(dInst.imm, dInst.inst);
    case (dInst.execFunc) matches
        tagged Alu    .aluInst:
            begin
                data = execAluInst(aluInst, rVal1, rVal2, imm, pc);
            end
        tagged Br     .brFunc:
            begin
                // data for jal
                data = pcPlus4;
                addr = brAddrCalc(brFunc, pc, rVal1, fromMaybe(?,imm));
                taken = aluBr(brFunc, rVal1, rVal2);
                nextPc = taken ? addr : pcPlus4;
            end
        tagged Mem    .memInst:
            begin
                // data for store and AMO
                data = rVal2;
                addr = addrCalc(rVal1, imm);
            end
        tagged System .systemInst:
            begin
                // data for CSR instructions
                data = fromMaybe(rVal1, imm);
            end
    endcase
    return ExecResult {
            data: data,
            addr: addr,
            taken: taken,
            nextPc: nextPc
        };
endfunction

// functions for execBasic
(* noinline *)
function Bit#(xlen) alu(AluFunc func, Bool w, Bit#(xlen) a, Bit#(xlen) b)
        provisos (NumAlias#(XLEN, xlen));
    if (valueOf(xlen) == 32) begin
        w = True;
    end
    // setup inputs
    if (w) begin
        a = (func == Sra) ? signExtend(a[31:0]) : zeroExtend(a[31:0]);
        b = zeroExtend(b[31:0]);
    end
    Bit#(6) shamt = truncate(b);
    if (w) begin
        shamt = {1'b0, shamt[4:0]};
    end

    Bit#(xlen) res = (case(func)
            Add, Auipc, Lui: (a + b);
            Sub:        (a - b);
            And:        (a & b);
            Or:         (a | b);
            Xor:        (a ^ b);
            Slt:        zeroExtend( pack( signedLT(a, b) ) );
            Sltu:       zeroExtend( pack( a < b ) );
            Sll:        (a << shamt);
            Srl:        (a >> shamt);
            Sra:        signedShiftRight(a, shamt);
            default:    0;
        endcase);

    if (w) begin
        res = signExtend(res[31:0]);
    end

    return res;
endfunction

function Bool aluBr(BrFunc brFunc, Bit#(xlen) a, Bit#(xlen) b);
    Bool brTaken = (case(brFunc)
            Eq:         (a == b);
            Neq:        (a != b);
            Lt:         signedLT(a, b);
            Ltu:        (a < b);
            Ge:         signedGE(a, b);
            Geu:        (a >= b);
            Jal:        True;
            Jalr:       True;
            default:    True;
        endcase);
    return brTaken;
endfunction

function Bit#(xlen) brAddrCalc(BrFunc brFunc, Bit#(xlen) pc, Bit#(xlen) val, Bit#(xlen) imm) provisos (Add#(a__, 1, xlen));
    Bit#(xlen) targetAddr = (case (brFunc)
            Jal:        (pc + imm);
            Jalr:       {(val + imm)[valueOf(xlen)-1:1], 1'b0};
            default:    (pc + imm);
        endcase);
    return targetAddr;
endfunction

function ExecResult#(xlen) basicExec(RVDecodedInst dInst, Bit#(xlen) rVal1, Bit#(xlen) rVal2, Bit#(xlen) pc) provisos (NumAlias#(XLEN, xlen));
    // PC+4 is used in a few places
    Bit#(xlen) pcPlus4 = pc + 4;

    // just data, addr, and control flow
    Bit#(xlen) data = 0;
    Bit#(xlen) addr = 0;
    Bool taken = False;
    Bit#(xlen) nextPc = pcPlus4;

    // Immediate Field
    Maybe#(Bit#(xlen)) imm = getImmediate(dInst.imm, dInst.inst);
    if (dInst.execFunc matches tagged Mem .*) begin
        if (!isValid(imm)) begin
            // Lr, Sc, and AMO instructions don't have immediate fields, so ovveride the immediate field here for address calculation
            imm = tagged Valid 0;
        end
    end

    // ALU
    Bit#(xlen) aluVal1 = rVal1;
    Bit#(xlen) aluVal2 = imm matches tagged Valid .validImm ? validImm : rVal2;
    if (dInst.execFunc matches tagged Alu .aluInst) begin
        // Special functions use special inputs
        case (aluInst.op) matches
            Auipc: aluVal1 = pc;
            Lui:   aluVal1 = 0;
        endcase
    end
    // Use Add as default for memory instructions so alu result is the address
    AluFunc aluF = dInst.execFunc matches tagged Alu .aluInst ? aluInst.op : Add;
    Bool w = dInst.execFunc matches tagged Alu .aluInst ? aluInst.w : False;
    Bit#(xlen) aluResult = alu(aluF, w, aluVal1, aluVal2);

    // Branch
    if (dInst.execFunc matches tagged Br .brFunc) begin
        taken = aluBr(brFunc, rVal1, rVal2);
        if (taken) begin
            // otherwise, nextPc is already pcPlus4
            nextPc = brAddrCalc(brFunc, pc, rVal1, fromMaybe(?, imm));
        end
    end

    data = (case (dInst.execFunc) matches
            tagged Alu .*:  aluResult;
            tagged Br .*:   pcPlus4; // for jal and jalr
            tagged Mem .*:  rVal2;
            tagged System .*: (imm matches tagged Valid .validImm ? validImm : rVal1);
            default:        ?;
        endcase);

    addr = (case (dInst.execFunc) matches
            tagged Alu .*:  nextPc;
            tagged Br .*:   nextPc;
            tagged Mem .*:  aluResult;
            default:        ?;
        endcase);

    return ExecResult{data: data, addr: addr, taken: taken, nextPc: nextPc};
endfunction

function Bit#(xlen) gatherLoad(Bit#(TLog#(TDiv#(xlen,8))) byteSel, RVMemSize size, Bool isUnsigned, Bit#(xlen) data)
        provisos (Add#(a__, 32, xlen),
                  Add#(b__, 16, xlen),
                  Add#(c__, 8, xlen));
    function extend = isUnsigned ? zeroExtend : signExtend;

    let bitsToShiftBy = {byteSel, 3'b0}; // byteSel * 8
    data = data >> bitsToShiftBy;
    data = (case (size)
            B: extend(data[7:0]);
            H: extend(data[15:0]);
            W: extend(data[31:0]);
            D: data;
        endcase);

    return data;
endfunction

function Tuple2#(DataByteEn, Bit#(xlen)) scatterStore(DataByteSel byteSel, RVMemSize size, Bit#(xlen) data)
        provisos (NumAlias#(XLEN, xlen));
    let bitsToShiftBy = {byteSel, 3'b0}; // byteSel * 8
    data = data << bitsToShiftBy;
    DataByteEn permutedByteEn = toPermutedDataByteEn(size, byteSel);
    return tuple2(permutedByteEn, data);
endfunction

