
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
    Data data;
    Addr addr;
    Bool taken;
    Addr nextPc;
} ExecResult deriving (Bits, Eq, FShow);

// Reference implementation of the exec function
// This is an inefficient implementation because many of the functions used
// in the case statement can reuse hardware
(* noinline *)
function ExecResult execRef(RVDecodedInst dInst, Data rVal1, Data rVal2, Addr pc);
    Data data = 0;
    Addr addr = 0;
    Addr pcPlus4 = pc + 4;
    Bool taken = False;
    Addr nextPc = pcPlus4;

    Maybe#(Data) imm = getImmediate(dInst.imm, dInst.inst);
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
function Data alu(AluFunc func, Bool w, Data a, Data b);
    // setup inputs
    if (w) begin
        a = (func == Sra) ? signExtend(a[31:0]) : zeroExtend(a[31:0]);
        b = zeroExtend(b[31:0]);
    end
    Bit#(6) shamt = truncate(b);
    if (w) begin
        shamt = {1'b0, shamt[4:0]};
    end

    Data res = (case(func)
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

(* noinline *)
function Bool aluBr(BrFunc brFunc, Data a, Data b);
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

(* noinline *)
function Addr brAddrCalc(BrFunc brFunc, Addr pc, Data val, Data imm);
    Addr targetAddr = (case (brFunc)
            Jal:        (pc + imm);
            Jalr:       {(val + imm)[valueOf(AddrSz)-1:1], 1'b0};
            default:    (pc + imm);
        endcase);
    return targetAddr;
endfunction

(* noinline *)
function ExecResult basicExec(RVDecodedInst dInst, Data rVal1, Data rVal2, Addr pc /*, Addr ppc */);
    // PC+4 is used in a few places
    Addr pcPlus4 = pc + 4;

    // just data, addr, and control flow
    Data data = 0;
    Addr addr = 0;
    Bool taken = False;
    Addr nextPc = pcPlus4;

    // Immediate Field
    Maybe#(Data) imm = getImmediate(dInst.imm, dInst.inst);
    if (dInst.execFunc matches tagged Mem .*) begin
        if (!isValid(imm)) begin
            // Lr, Sc, and AMO instructions don't have immediate fields, so ovveride the immediate field here for address calculation
            imm = tagged Valid 0;
        end
    end

    // ALU
    Data aluVal1 = rVal1;
    Data aluVal2 = imm matches tagged Valid .validImm ? validImm : rVal2;
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
    Data aluResult = alu(aluF, w, aluVal1, aluVal2);

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

// function Data gatherLoad(Addr addr, ByteEn byteEn, Bool unsignedLd, Data data);
function Data gatherLoad(DataByteSel byteSel, RVMemSize size, Bool isUnsigned, Data data);
    function extend = isUnsigned ? zeroExtend : signExtend;

    let bitsToShiftBy = {byteSel, 3'b0}; // byteSel * 8
    data = data >> bitsToShiftBy;
    data = (case (size)
            B: extend(data[7:0]);
            H: extend(data[15:0]);
            W: extend(data[31:0]);
            D: data[63:0];
        endcase);

    return data;
endfunction

function Tuple2#(DataByteEn, Data) scatterStore(DataByteSel byteSel, RVMemSize size, Data data);
    let bitsToShiftBy = {byteSel, 3'b0}; // byteSel * 8
    data = data << bitsToShiftBy;
    DataByteEn permutedByteEn = toPermutedDataByteEn(size, byteSel);
    return tuple2(permutedByteEn, data);
endfunction

