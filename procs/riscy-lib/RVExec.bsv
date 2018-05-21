
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
    Bit#(XLEN) data;
    Bit#(XLEN) addr;
    Bool taken;
    Bit#(XLEN) nextPc;
} ExecResult#(numeric type xlen) deriving (Bits, Eq, FShow);

interface RVExec;
   method ExecResult#(XLEN) execRef(RVDecodedInst dInst, Bit#(XLEN) rVal1, Bit#(XLEN) rVal2, Bit#(XLEN) pc);
endinterface
  

module mkRVExec(RVExec);
// Reference implementation of the exec function
// This is an inefficient implementation because many of the functions used
// in the case statement can reuse hardware

   RVDecode rvDecoder <- mkRVDecode();

method ExecResult#(XLEN) execRef(RVDecodedInst dInst, Bit#(XLEN) rVal1, Bit#(XLEN) rVal2, Bit#(XLEN) pc)
        provisos (NumAlias#(XLEN, XLEN));
    Bit#(XLEN) data = 0;
    Bit#(XLEN) addr = 0;
    Bit#(XLEN) pcPlus4 = pc + 4;
    Bool taken = False;
    Bit#(XLEN) nextPc = pcPlus4;

    Maybe#(Bit#(XLEN)) imm = rvDecoder.getImmediate(dInst.imm, dInst.inst);
    case (dInst.execFunc) matches
        tagged EF_Alu    .aluInst:
            begin
                data = execAluInst(aluInst, rVal1, rVal2, imm, pc);
            end
        tagged EF_Br     .brFunc:
            begin
                // data for jal
                data = pcPlus4;
                addr = brAddrCalc(brFunc, pc, rVal1, fromMaybe(?,imm));
                taken = aluBr(brFunc, rVal1, rVal2);
                nextPc = taken ? addr : pcPlus4;
            end
        tagged EF_Mem    .memInst:
            begin
                // data for store and AMO
                data = rVal2;
                addr = addrCalc(rVal1, imm);
            end
        tagged EF_System .systemInst:
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
endmethod
endmodule

interface BasicExecInternal;
   method Bit#(XLEN) brAddrCalc(BrFunc brFunc, Bit#(XLEN) pc, Bit#(XLEN) val, Bit#(XLEN) imm) provisos (Add#(a__, 1, XLEN));
   method Bit#(XLEN) alu(AluFunc func, Bool w, Bit#(XLEN) a, Bit#(XLEN) b);
   method Bool aluBr(BrFunc brFunc, Bit#(XLEN) a, Bit#(XLEN) b);
endinterface



module mkBasicExecInternal(BasicExecInternal);
method Bit#(XLEN) brAddrCalc(BrFunc brFunc, Bit#(XLEN) pc, Bit#(XLEN) val, Bit#(XLEN) imm) provisos (Add#(a__, 1, XLEN));
    Bit#(XLEN) targetAddr = (case (brFunc)
            BrJal:        (pc + imm);
            BrJalr:       {(val + imm)[valueOf(XLEN)-1:1], 1'b0};
            default:      (pc + imm);
        endcase);
    return targetAddr;
endmethod

// functions for execBasic
method Bit#(XLEN) alu(AluFunc func, Bool w, Bit#(XLEN) a, Bit#(XLEN) b)
        provisos (NumAlias#(XLEN, XLEN));
    if (valueOf(XLEN) == 32) begin
        w = True;
    end
    // setup inputs
    if (w) begin
        a = (func == AluSra) ? signExtend(a[31:0]) : zeroExtend(a[31:0]);
        b = zeroExtend(b[31:0]);
    end
    Bit#(6) shamt = truncate(b);
    if (w) begin
        shamt = {1'b0, shamt[4:0]};
    end

    Bit#(XLEN) res = (case(func)
            AluAdd, AluAuipc, AluLui: (a + b);
            AluSub:        (a - b);
            AluAnd:        (a & b);
            AluOr:         (a | b);
            AluXor:        (a ^ b);
            AluSlt:        zeroExtend( pack( signedLT(a, b) ) );
            AluSltu:       zeroExtend( pack( a < b ) );
            AluSll:        (a << shamt);
            AluSrl:        (a >> shamt);
            AluSra:        signedShiftRight(a, shamt);
            default:    0;
        endcase);

    if (w) begin
        res = signExtend(res[31:0]);
    end

    return res;
endmethod

method Bool aluBr(BrFunc brFunc, Bit#(XLEN) a, Bit#(XLEN) b);
    Bool brTaken = (case(brFunc)
            BrEq:         (a == b);
            BrNeq:        (a != b);
            BrLt:         signedLT(a, b);
            BrLtu:        (a < b);
            BrGe:         signedGE(a, b);
            BrGeu:        (a >= b);
            BrJal:        True;
            BrJalr:       True;
            default:    True;
        endcase);
    return brTaken;
endmethod

endmodule

interface BasicExec;
method ExecResult#(XLEN) basicExec(RVDecodedInst dInst, Bit#(XLEN) rVal1, Bit#(XLEN) rVal2, Bit#(XLEN) pc) provisos (NumAlias#(XLEN, XLEN));
endinterface

module mkBasicExec(BasicExec);
   BasicExecInternal basicExecInternal <- mkBasicExecInternal();
   RVDecode rvDecoder <- mkRVDecode();

   method ExecResult#(XLEN) basicExec(RVDecodedInst dInst, Bit#(XLEN) rVal1, Bit#(XLEN) rVal2, Bit#(XLEN) pc) provisos (NumAlias#(XLEN, XLEN));
    // PC+4 is used in a few places
    Bit#(XLEN) pcPlus4 = pc + 4;

    // just data, addr, and control flow
    Bit#(XLEN) data = 0;
    Bit#(XLEN) addr = 0;
    Bool taken = False;
    Bit#(XLEN) nextPc = pcPlus4;

    // Immediate Field
    Maybe#(Bit#(XLEN)) imm = rvDecoder.getImmediate(dInst.imm, dInst.inst);
    if (dInst.execFunc matches tagged EF_Mem .*) begin
        if (!isValid(imm)) begin
            // Lr, Sc, and AMO instructions don't have immediate fields, so ovveride the immediate field here for address calculation
            imm = tagged Valid 0;
        end
    end

    // ALU
    Bit#(XLEN) aluVal1 = rVal1;
    Bit#(XLEN) aluVal2 = imm matches tagged Valid .validImm ? validImm : rVal2;
    if (dInst.execFunc matches tagged EF_Alu .aluInst) begin
        // Special functions use special inputs
        case (aluInst.op) matches
            AluAuipc: aluVal1 = pc;
            AluLui:   aluVal1 = 0;
        endcase
    end
    // Use Add as default for memory instructions so alu result is the address
    AluFunc aluF = dInst.execFunc matches tagged EF_Alu .aluInst ? aluInst.op : AluAdd;
    Bool w = dInst.execFunc matches tagged EF_Alu .aluInst ? aluInst.w : False;
    Bit#(XLEN) aluResult = basicExecInternal.alu(aluF, w, aluVal1, aluVal2);

    // Branch
    if (dInst.execFunc matches tagged EF_Br .brFunc) begin
        taken = basicExecInternal.aluBr(brFunc, rVal1, rVal2);
        if (taken) begin
            // otherwise, nextPc is already pcPlus4
            nextPc = basicExecInternal.brAddrCalc(brFunc, pc, rVal1, fromMaybe(?, imm));
        end
    end

    data = (case (dInst.execFunc) matches
            tagged EF_Alu .*:  aluResult;
            tagged EF_Br .*:   pcPlus4; // for jal and jalr
            tagged EF_Mem .*:  rVal2;
            tagged EF_System .*: (imm matches tagged Valid .validImm ? validImm : rVal1);
            default:        ?;
        endcase);

    addr = (case (dInst.execFunc) matches
            tagged EF_Alu .*:  nextPc;
            tagged EF_Br .*:   nextPc;
            tagged EF_Mem .*:  aluResult;
            default:        ?;
        endcase);

    return ExecResult{data: data, addr: addr, taken: taken, nextPc: nextPc};
endmethod
endmodule

interface ScatterGatherLoadStore;
   method Bit#(XLEN) gatherLoad(Bit#(TLog#(TDiv#(XLEN,8))) byteSel, RVMemSize size, Bool isUnsigned, Bit#(XLEN) data);
   method Tuple2#(DataByteEn, Bit#(XLEN)) scatterStore(DataByteSel byteSel, RVMemSize size, Bit#(XLEN) data);
endinterface
   
module mkScatterGatherLoadStore(ScatterGatherLoadStore);

   ToPermutedDataByteEn toPermutedDataByteEn <- mkToPermutedDataByteEn();

   method Bit#(XLEN) gatherLoad(Bit#(TLog#(TDiv#(XLEN,8))) byteSel, RVMemSize size, Bool isUnsigned, Bit#(XLEN) data)
      provisos (Add#(a__, 32, XLEN),
		Add#(b__, 16, XLEN),
		Add#(c__, 8, XLEN));
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
   endmethod
   method Tuple2#(DataByteEn, Bit#(XLEN)) scatterStore(DataByteSel byteSel, RVMemSize size, Bit#(XLEN) data)
      provisos (NumAlias#(XLEN, XLEN));
      let bitsToShiftBy = {byteSel, 3'b0}; // byteSel * 8
      data = data << bitsToShiftBy;
      DataByteEn permutedByteEn = toPermutedDataByteEn.toPermutedDataByteEn(size, byteSel);
      return tuple2(permutedByteEn, data);
   endmethod
endmodule

