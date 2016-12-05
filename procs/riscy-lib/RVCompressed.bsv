
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
`include "Opcodes.defines"

import BuildVector::*;
import Opcodes::*;
import RVTypes::*;
import Vector::*;
import DefaultValue::*;

typedef enum {
    ConstX0,       // x0 = zero
    ConstX1,       // x1 = ra
    ConstX2,       // x2 = sp
    FullGPR,       // inst[11:7]
    FullFPU,
    CompressedGPR, // {2'b0, inst[9:7]}
    CompressedFPU
} CompressedRegType;
// XXX ERROR FIXME: CompressedGPR for rd' is not unique. There are two locations where rd' can be present.

typedef enum {
    // cimmsh5    6:2[4:0]                     uimm    nzimm     green   none
    CImmSH5,
    // cimmsh6    12[5],6:2[4:0]               uimm    nzimm     green   none
    CImmSH6,
    // cimmi      12[5],6:2[4:0]               simm    imm       green   none
    CImmI,
    // cnzimmi    12[5],6:2[4:0]               simm    nzimm     green   none
    CImmI_NZ,
    // cimmui     12[17],6:2[16:12]            simm    nzimm     green   none
    CImmUI,
    // cimmlwsp   12[5],6:2[4:2|7:6]           simm    imm       green   none
    CImmLWSP,
    // cimmldsp   12[5],6:2[4:3|8:6]           simm    imm       green   none
    CImmLDSP,
    // cimm16sp   12[9],6:2[4|6|8:7|5]         simm    nzimm     green   none
    CImm16SP,
    // cimmj      12:2[11|4|9:8|10|6|7|3:1|5]  simm    imm       green   none
    CImmJ,
    // cimmb      12:10[8|4:3],6:2[7:6|2:1|5]  simm    imm       green   none
    CImmB,
    // cimmswsp   12:7[5:2|7:6]                simm    imm       green   none
    CImmSWSP,
    // cimmsdsp   12:7[5:3|8:6]                simm    imm       green   none
    CImmSDSP,
    // cimmsqsp   12:7[5:4|9:6]                simm    imm       green   none
    CImmSQSP,
    // cimm4spn   12:5[5:4|9:6|2|3]            simm    nzimm     green   none
    CImm4SPN,
    // cimmw      12:10[5:3],6:5[2|6]          simm    imm       green   none
    CImmW,
    // cimmd      12:10[5:3],6:5[7:6]          simm    imm       green   none
    CImmD,
    // cimmq      12:10[5:4|8],6:5[7:6]        simm    imm       green   none
    CImmq
} CompressedImmType deriving (Bits, Eq, FShow);
typedef struct {
    Maybe#(CompressedRegType) rs1;
    Maybe#(CompressedRegType) rs2;
    Maybe#(CompressedRegType) rd;
} CompressedInstType deriving (Bits, Eq, FShow);

function Maybe#(ExecFunc) toExecFuncRV32C(Instruction inst);
    // split by quadrants
    return (case ({inst[15:13], inst[1:0]}) matches
            // Quadrant 0
            5'b00000: // C.ADDI4SPN
                if (inst[15:0] == 0) begin inst = tagged Invalid; // illegal
                end else if (inst[12:5] == 0) begin inst = tagged Invalid; // reserved
                end else begin
                    inst = tagged Valid (tagged Alu AluInst{op: Add, w: False});
                    rs1 = tagged Valid ConstantX2;
                    rs2 = tagged Invalid;
                    rd = tagged Valid CompressedGPR;
                    imm = tagged Valid CImm4SPN;
                end
            5'b00100: // C.FLD (RV32/64), C.LQ (RV128)
                inst = tagged Invalid;
            5'b01000: // C.LW
                inst = tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: W, isUnsigned: False});
                rs1 = tagged Valid CompressedGPR;
                rs2 = tagged Invalid;
                rd = tagged Valid CompressedGPR;
                imm = tagged Valid CImmW;
            5'b01100: // C.FLW (RV32), C.LD (RV64/128)
                inst = tagged Invalid;
            5'b10000: // Reserved
                inst = tagged Invalid;
            5'b10100: // C.FSD (RV32/64), C.SQ (RV128)
                inst = tagged Invalid;
            5'b11000: // C.SW
                inst = tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: W, isUnsigned: False});
                rs1 = tagged Valid CompressedGPR;
                rs2 = tagged Valid CompressedGPR;
                rd = tagged Invalid;
                imm = tagged Valid CImmW;
            5'b11100: // C.FSW (RV32), C.SD (RV64/128)
                inst = tagged Invalid;

            // Quadrant 1
            5'b00001: // C.ADDI
                // TODO
                inst = tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: W, isUnsigned: False});
                rs1 = tagged Valid CompressedGPR;
                rs2 = tagged Invalid;
                rd = tagged Valid CompressedGPR;
                imm = tagged Valid CImmI; // NZ?
            5'b00101: // C.JAL (RV32), C.ADDIW (RV64/128)
                // TODO
            5'b01001: // C.LI
                // TODO
            5'b01101: // C.ADDI16SP, C.LUI
                // TODO
            5'b10001: // C.aluop
                // TODO
            5'b10101: // C.J
                // TODO
            5'b11001: // C.BEQZ
                // TODO
            5'b11101: // C.BNEZ
                // TODO
            // Quadrant 2
            5'b00001: // C.SLLI, C.SLLI64 (RV128)
                // TODO
            5'b00101: // C.FLDSP (RV32/64), C.LQSP (RV128)
                inst = tagged Invalid;
            5'b01001: // C.LWSP
                // TODO
            5'b01101: // C.FLWSP (RV32), C.LDSP (RV64/128)
                inst = tagged Invalid;
            5'b10001: // C.JR, C.MV, C.EBREAK, C.JALR, C.ADD
                // TODO
            5'b10101: // C.FSDSP (RV32/64), C.SQSP (RV128)
                inst = tagged Invalid;
            5'b11001: // C.SWSP
                // TODO
            5'b11101: // C.FSWSP (RV32), C.SDSP (RV64/128)
                inst = tagged Invalid;
            // Quadrant 3
            5'b???11: // entire quadrant is 32-bit instructions or longer
                tagged Invalid;
    endcase
    // TODO
endfunction

// This function is used to get the immediate value from a decoded instruction
function Maybe#(Data) getImmediateCompressed(CompressedImmType imm, Instruction inst);
    // cimmsh5    6:2[4:0]                     uimm    nzimm     green   none
    Data cimmsh5    = zeroExtend(inst[6:2]);
    // cimmsh6    12[5],6:2[4:0]               uimm    nzimm     green   none
    Data cimmsh6    = zeroExtend({inst[12], inst[6:2]});
    // cimmi      12[5],6:2[4:0]               simm    imm       green   none
    Data cimmi      = signExtend({inst[12], inst[6:2]});
    // cnzimmi    12[5],6:2[4:0]               simm    nzimm     green   none
    Data cnzimmi    = signExtend({inst[12], inst[6:2]});
    // cimmui     12[17],6:2[16:12]            simm    nzimm     green   none
    Data cimmui     = signExtend({inst[12], inst[6:2], 12'b0});
    // cimmlwsp   12[5],6:2[4:2|7:6]           simm    imm       green   none
    Data cimmlwsp   = signExtend({inst[3:2], inst[12], inst[6:4], 2'b0});
    // cimmldsp   12[5],6:2[4:3|8:6]           simm    imm       green   none
    Data cimmldsp   = signExtend({inst[4:2], inst[12], inst[6:5], 3'b0});
    // cimm16sp   12[9],6:2[4|6|8:7|5]         simm    nzimm     green   none
    Data cimm16sp   = signExtend({inst[12], inst[4], inst[3], inst[5], inst[2], inst[6]});
    // cimmj      12:2[11|4|9:8|10|6|7|3:1|5]  simm    imm       green   none
    Data cimmj      = signExtend({inst[12], inst[8], inst[10:9], isnt[6], inst[7], inst[2], inst[11], inst[5:3], 1'b0});
    // cimmb      12:10[8|4:3],6:2[7:6|2:1|5]  simm    imm       green   none
    Data cimmb      = signExtend({inst[12], inst[6:5], inst[2], inst[11:10], inst[4:3], 1'b0});
    // cimmswsp   12:7[5:2|7:6]                simm    imm       green   none
    Data cimmswsp   = signExtend({inst[8:7], inst[12:9], 2'b0});
    // cimmsdsp   12:7[5:3|8:6]                simm    imm       green   none
    Data cimmsdsp   = signExtend({inst[9:7], inst[12:10], 3'b0});
    // cimmsqsp   12:7[5:4|9:6]                simm    imm       green   none
    Data cimmsqsp   = signExtend({inst[10:7], inst[12:11], 4'b0});
    // cimm4spn   12:5[5:4|9:6|2|3]            simm    nzimm     green   none
    Data cimm4spn   = signExtend({inst[10:7], inst[12:11], inst[5], inst[6], 2'b0});
    // cimmw      12:10[5:3],6:5[2|6]          simm    imm       green   none
    Data cimmw      = signExtend({inst[5], inst[12:10], inst[6], 2'b0});
    // cimmd      12:10[5:3],6:5[7:6]          simm    imm       green   none
    Data cimmd      = signExtend({inst[6:5], inst[12:10], 3'b0});
    // cimmq      12:10[5:4|8],6:5[7:6]        simm    imm       green   none
    Data cimmq      = signExtend({inst[10], inst[6:5], inst[12:11], 4'b0});

    // TODO
    return (case (imm)
            default: tagged Invalid;
        endcase);
endfunction

// This returns a valid result if the instruction is legal, otherwise it
// returns a tagged invalid.
(* noinline *)
function Maybe#(RVDecodedInst) decodeInst(Instruction inst);
    // Construct a vector of all the results
    // We will apply a fold function on this vector to find the valid result
    let decoderResults = vec(
            toExecFuncRV32I(inst),
`ifdef CONFIG_RV64
            toExecFuncRV64I(inst),
`endif
`ifdef CONFIG_M
            toExecFuncRV32M(inst),
`ifdef CONFIG_RV64
            toExecFuncRV64M(inst),
`endif
`endif
`ifdef CONFIG_A
            toExecFuncRV32A(inst),
`ifdef CONFIG_RV64
            toExecFuncRV64A(inst),
`endif
`endif
`ifdef CONFIG_F
            toExecFuncRV32F(inst),
`ifdef CONFIG_RV64
            toExecFuncRV64F(inst),
`endif
`endif
`ifdef CONFIG_D
            toExecFuncRV32D(inst),
`ifdef CONFIG_RV64
            toExecFuncRV64D(inst),
`endif
`endif
            toExecFuncPriv(inst)
        );

    // This fold is equivalent to going down the list of decoder results and
    // returning the first valid result
    function Maybe#(t) fold_op(Maybe#(t) x, Maybe#(t) y) provisos (Bits#(t, tSz));
        return isValid(x) ? x : y;
    endfunction
    let execFunc = fold(fold_op, decoderResults);

    if (execFunc matches tagged Valid .validExecFunc) begin
        InstType instType = toInstType(inst);
        return tagged Valid (RVDecodedInst {
                execFunc: validExecFunc,
                imm: instType.imm,
                rs1: instType.rs1,
                rs2: instType.rs2,
                rs3: instType.rs3,
                dst: instType.dst,
                inst: inst });
    end else begin
        return tagged Invalid;
    end
endfunction

// This function is used to get the immediate value from a decoded instruction
function Maybe#(Data) getImmediate(ImmType imm, Instruction inst);
    Data immI  = signExtend(inst[31:20]);
    Data immS  = signExtend({inst[31:25], inst[11:7]});
    Data immSB = signExtend({inst[31], inst[7], inst[30:25], inst[11:8], 1'b0});
    Data immU  = signExtend({inst[31:12], 12'b0});
    Data immUJ = signExtend({inst[31], inst[19:12], inst[20], inst[30:21], 1'b0});
    Data immZ  = zeroExtend(inst[19:15]);
    return (case (imm)
            S:  tagged Valid immS;
            SB: tagged Valid immSB;
            U:  tagged Valid immU;
            UJ: tagged Valid immUJ;
            I:  tagged Valid immI;
            Z:  tagged Valid immZ;
            default: tagged Invalid;
        endcase);
endfunction

function Bit#(2) getMinPriv(Instruction inst);
    return (getInstFields(inst).opcode == System) ? inst[29:28] : prvU;
endfunction
