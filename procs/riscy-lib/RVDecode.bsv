
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

function Maybe#(ExecFunc) toExecFuncRV32I(Instruction inst);
    return (case (inst) matches
            // BRANCH
            `BEQ:   tagged Valid (tagged Br Eq);
            `BNE:   tagged Valid (tagged Br Neq);
            `BLT:   tagged Valid (tagged Br Lt);
            `BGE:   tagged Valid (tagged Br Ge);
            `BLTU:  tagged Valid (tagged Br Ltu);
            `BGEU:  tagged Valid (tagged Br Geu);
            // JALR
            `JALR:  tagged Valid (tagged Br Jalr);
            // JAL
            `JAL:   tagged Valid (tagged Br Jal);
            // LUI
            `LUI:   tagged Valid (tagged Alu AluInst{op: Lui,   w: False});
            // AUIPC
            `AUIPC: tagged Valid (tagged Alu AluInst{op: Auipc, w: False});
            // OP-IMM
            `ADDI:  tagged Valid (tagged Alu AluInst{op: Add,   w: False});
            `SLLI:  tagged Valid (tagged Alu AluInst{op: Sll,   w: False});
            `SLTI:  tagged Valid (tagged Alu AluInst{op: Slt,   w: False});
            `SLTIU: tagged Valid (tagged Alu AluInst{op: Sltu,  w: False});
            `XORI:  tagged Valid (tagged Alu AluInst{op: Xor,   w: False});
            `SRLI:  tagged Valid (tagged Alu AluInst{op: Srl,   w: False});
            `SRAI:  tagged Valid (tagged Alu AluInst{op: Sra,   w: False});
            `ORI:   tagged Valid (tagged Alu AluInst{op: Or,    w: False});
            `ANDI:  tagged Valid (tagged Alu AluInst{op: And,   w: False});
            // OP
            `ADD:   tagged Valid (tagged Alu AluInst{op: Add,   w: False});
            `SUB:   tagged Valid (tagged Alu AluInst{op: Sub,   w: False});
            `SLL:   tagged Valid (tagged Alu AluInst{op: Sll,   w: False});
            `SLT:   tagged Valid (tagged Alu AluInst{op: Slt,   w: False});
            `SLTU:  tagged Valid (tagged Alu AluInst{op: Sltu,  w: False});
            `XOR:   tagged Valid (tagged Alu AluInst{op: Xor,   w: False});
            `SRL:   tagged Valid (tagged Alu AluInst{op: Srl,   w: False});
            `SRA:   tagged Valid (tagged Alu AluInst{op: Sra,   w: False});
            `OR:    tagged Valid (tagged Alu AluInst{op: Or,    w: False});
            `AND:   tagged Valid (tagged Alu AluInst{op: And,   w: False});
            // LOAD
            `LB:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: B, isUnsigned: False});
            `LH:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: H, isUnsigned: False});
            `LW:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: W, isUnsigned: False});
            `LBU:   tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: B, isUnsigned: True});
            `LHU:   tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: H, isUnsigned: True});
            // STORE
            `SB:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: B, isUnsigned: False});
            `SH:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: H, isUnsigned: False});
            `SW:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: W, isUnsigned: False});
            // MISC-MEM
            `FENCE:     tagged Valid (tagged Fence (tagged InterCore unpack(truncate(inst[27:20]))));
            `FENCE_I:   tagged Valid (tagged Fence (tagged IntraCore FenceI));

            default: tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV64I(Instruction inst);
    return (case (inst) matches
            // OP-IMM-32
            `ADDIW: tagged Valid (tagged Alu AluInst{op: Add,   w: True});
            `SLLIW: tagged Valid (tagged Alu AluInst{op: Sll,   w: True});
            `SRLIW: tagged Valid (tagged Alu AluInst{op: Srl,   w: True});
            `SRAIW: tagged Valid (tagged Alu AluInst{op: Sra,   w: True});
            // OP-32
            `ADDW:  tagged Valid (tagged Alu AluInst{op: Add,   w: True});
            `SUBW:  tagged Valid (tagged Alu AluInst{op: Sub,   w: True});
            `SLLW:  tagged Valid (tagged Alu AluInst{op: Sll,   w: True});
            `SRLW:  tagged Valid (tagged Alu AluInst{op: Srl,   w: True});
            `SRAW:  tagged Valid (tagged Alu AluInst{op: Sra,   w: True});
            // LOAD
            `LD:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: D, isUnsigned: False});
            `LWU:   tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: W, isUnsigned: True});
            // STORE
            `SD:    tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: D, isUnsigned: False});
            // MISC-MEM
            `FENCE:     tagged Valid (tagged Fence (tagged InterCore unpack(truncate(inst[27:20]))));
            `FENCE_I:   tagged Valid (tagged Fence (tagged IntraCore FenceI));

            default: tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncPriv(Instruction inst);
    InstructionFields instFields = unpack(inst);
    return (case (inst) matches
            `ECALL:     tagged Valid (tagged System ECall);
            `EBREAK:    tagged Valid (tagged System EBreak);
            // `URET:      tagged Valid (tagged System URet);
            `SRET:      tagged Valid (tagged System SRet);
            // `HRET:      tagged Valid (tagged System HRet);
            `MRET:      tagged Valid (tagged System MRet);
            `SFENCE_VM: tagged Valid (tagged Fence (tagged IntraCore SFenceVM));
            `WFI:       tagged Valid (tagged System WFI);
            `CSRRW:     tagged Valid (tagged System ((instFields.rd == 0) ? CSRW : CSRRW));
            `CSRRS:     tagged Valid (tagged System ((instFields.rs1 == 0) ? CSRR : CSRRS));
            `CSRRC:     tagged Valid (tagged System ((instFields.rs1 == 0) ? CSRR : CSRRC));
            `CSRRWI:    tagged Valid (tagged System ((instFields.rd == 0) ? CSRW : CSRRW));
            `CSRRSI:    tagged Valid (tagged System ((instFields.rs1 == 0) ? CSRR : CSRRS));
            `CSRRCI:    tagged Valid (tagged System ((instFields.rs1 == 0) ? CSRR : CSRRC));

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV32M(Instruction inst);
    return (case(inst) matches
            `MUL:       tagged Valid (tagged MulDiv MulDivInst{func: Mul,  w: False, sign: Signed});
            `MULH:      tagged Valid (tagged MulDiv MulDivInst{func: Mulh, w: False, sign: Signed});
            `MULHSU:    tagged Valid (tagged MulDiv MulDivInst{func: Mulh, w: False, sign: SignedUnsigned});
            `MULHU:     tagged Valid (tagged MulDiv MulDivInst{func: Mulh, w: False, sign: Unsigned});
            `DIV:       tagged Valid (tagged MulDiv MulDivInst{func: Div,  w: False, sign: Signed});
            `DIVU:      tagged Valid (tagged MulDiv MulDivInst{func: Div,  w: False, sign: Unsigned});
            `REM:       tagged Valid (tagged MulDiv MulDivInst{func: Rem,  w: False, sign: Signed});
            `REMU:      tagged Valid (tagged MulDiv MulDivInst{func: Rem,  w: False, sign: Unsigned});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV64M(Instruction inst);
    return (case(inst) matches
            `MULW:      tagged Valid (tagged MulDiv MulDivInst{func: Mul,  w: True,  sign: Signed});
            `DIVW:      tagged Valid (tagged MulDiv MulDivInst{func: Div,  w: True,  sign: Signed});
            `DIVUW:     tagged Valid (tagged MulDiv MulDivInst{func: Div,  w: True,  sign: Unsigned});
            `REMW:      tagged Valid (tagged MulDiv MulDivInst{func: Rem,  w: True,  sign: Signed});
            `REMUW:     tagged Valid (tagged MulDiv MulDivInst{func: Rem,  w: True,  sign: Unsigned});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV32A(Instruction inst);
    return (case (inst) matches
            `AMOADD_W:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Add,  size: W, isUnsigned: False});
            `AMOXOR_W:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Xor,  size: W, isUnsigned: False});
            `AMOOR_W:   tagged Valid (tagged Mem RVMemInst{op: tagged Amo Or,   size: W, isUnsigned: False});
            `AMOAND_W:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo And,  size: W, isUnsigned: False});
            `AMOMIN_W:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Min,  size: W, isUnsigned: False});
            `AMOMAX_W:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Max,  size: W, isUnsigned: False});
            `AMOMINU_W: tagged Valid (tagged Mem RVMemInst{op: tagged Amo Minu, size: W, isUnsigned: False});
            `AMOMAXU_W: tagged Valid (tagged Mem RVMemInst{op: tagged Amo Maxu, size: W, isUnsigned: False});
            `AMOSWAP_W: tagged Valid (tagged Mem RVMemInst{op: tagged Amo Swap, size: W, isUnsigned: False});
            `LR_W:      tagged Valid (tagged Mem RVMemInst{op: tagged Mem Lr,   size: W, isUnsigned: False});
            `SC_W:      tagged Valid (tagged Mem RVMemInst{op: tagged Mem Sc,   size: W, isUnsigned: False});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV64A(Instruction inst);
    return (case (inst) matches
            `AMOADD_D:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Add,  size: D, isUnsigned: False});
            `AMOXOR_D:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Xor,  size: D, isUnsigned: False});
            `AMOOR_D:   tagged Valid (tagged Mem RVMemInst{op: tagged Amo Or,   size: D, isUnsigned: False});
            `AMOAND_D:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo And,  size: D, isUnsigned: False});
            `AMOMIN_D:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Min,  size: D, isUnsigned: False});
            `AMOMAX_D:  tagged Valid (tagged Mem RVMemInst{op: tagged Amo Max,  size: D, isUnsigned: False});
            `AMOMINU_D: tagged Valid (tagged Mem RVMemInst{op: tagged Amo Minu, size: D, isUnsigned: False});
            `AMOMAXU_D: tagged Valid (tagged Mem RVMemInst{op: tagged Amo Maxu, size: D, isUnsigned: False});
            `AMOSWAP_D: tagged Valid (tagged Mem RVMemInst{op: tagged Amo Swap, size: D, isUnsigned: False});
            `LR_D:      tagged Valid (tagged Mem RVMemInst{op: tagged Mem Lr,   size: D, isUnsigned: False});
            `SC_D:      tagged Valid (tagged Mem RVMemInst{op: tagged Mem Sc,   size: D, isUnsigned: False});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV32F(Instruction inst);
    return (case (inst) matches
            `FADD_S:    tagged Valid (tagged Fpu FpuInst{func: FAdd,     precision: Single});
            `FSUB_S:    tagged Valid (tagged Fpu FpuInst{func: FSub,     precision: Single});
            `FMUL_S:    tagged Valid (tagged Fpu FpuInst{func: FMul,     precision: Single});
`ifndef NO_FDIV
            `FDIV_S:    tagged Valid (tagged Fpu FpuInst{func: FDiv,     precision: Single});
`endif
            `FSGNJ_S:   tagged Valid (tagged Fpu FpuInst{func: FSgnj,    precision: Single});
            `FSGNJN_S:  tagged Valid (tagged Fpu FpuInst{func: FSgnjn,   precision: Single});
            `FSGNJX_S:  tagged Valid (tagged Fpu FpuInst{func: FSgnjx,   precision: Single});
            `FMIN_S:    tagged Valid (tagged Fpu FpuInst{func: FMin,     precision: Single});
            `FMAX_S:    tagged Valid (tagged Fpu FpuInst{func: FMax,     precision: Single});
`ifndef NO_FSQRT
            `FSQRT_S:   tagged Valid (tagged Fpu FpuInst{func: FSqrt,    precision: Single});
`endif

            `FLE_S:     tagged Valid (tagged Fpu FpuInst{func: FLe,      precision: Single});
            `FLT_S:     tagged Valid (tagged Fpu FpuInst{func: FLt,      precision: Single});
            `FEQ_S:     tagged Valid (tagged Fpu FpuInst{func: FEq,      precision: Single});

            `FCVT_W_S:  tagged Valid (tagged Fpu FpuInst{func: FCvt_WF,  precision: Single});
            `FCVT_WU_S: tagged Valid (tagged Fpu FpuInst{func: FCvt_WUF, precision: Single});

            `FMV_X_S:   tagged Valid (tagged Fpu FpuInst{func: FMv_XF,   precision: Single});

            `FCLASS_S:  tagged Valid (tagged Fpu FpuInst{func: FClass,   precision: Single});

            `FCVT_S_W:  tagged Valid (tagged Fpu FpuInst{func: FCvt_FW,  precision: Single});
            `FCVT_S_WU: tagged Valid (tagged Fpu FpuInst{func: FCvt_FWU, precision: Single});
            `FMV_S_X:   tagged Valid (tagged Fpu FpuInst{func: FMv_FX,   precision: Single});

            // Floating-Point Memory instructions
            `FLW:       tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: W, isUnsigned: True});
            `FSW:       tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: W, isUnsigned: True});

            // FMA instructions
            `FMADD_S:   tagged Valid (tagged Fpu FpuInst{func: FMAdd,  precision: Single});
            `FMSUB_S:   tagged Valid (tagged Fpu FpuInst{func: FMSub,  precision: Single});
            `FNMSUB_S:  tagged Valid (tagged Fpu FpuInst{func: FNMSub, precision: Single});
            `FNMADD_S:  tagged Valid (tagged Fpu FpuInst{func: FNMAdd, precision: Single});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV64F(Instruction inst);
    return (case (inst) matches
            `FCVT_L_S:  tagged Valid (tagged Fpu FpuInst{func: FCvt_LF,  precision: Single});
            `FCVT_LU_S: tagged Valid (tagged Fpu FpuInst{func: FCvt_LUF, precision: Single});
            `FCVT_S_L:  tagged Valid (tagged Fpu FpuInst{func: FCvt_FL,  precision: Single});
            `FCVT_S_LU: tagged Valid (tagged Fpu FpuInst{func: FCvt_FLU, precision: Single});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV32D(Instruction inst);
    return (case (inst) matches
            `FADD_D:    tagged Valid (tagged Fpu FpuInst{func: FAdd,     precision: Double});
            `FSUB_D:    tagged Valid (tagged Fpu FpuInst{func: FSub,     precision: Double});
            `FMUL_D:    tagged Valid (tagged Fpu FpuInst{func: FMul,     precision: Double});
`ifndef NO_FDIV
            `FDIV_D:    tagged Valid (tagged Fpu FpuInst{func: FDiv,     precision: Double});
`endif
            `FSGNJ_D:   tagged Valid (tagged Fpu FpuInst{func: FSgnj,    precision: Double});
            `FSGNJN_D:  tagged Valid (tagged Fpu FpuInst{func: FSgnjn,   precision: Double});
            `FSGNJX_D:  tagged Valid (tagged Fpu FpuInst{func: FSgnjx,   precision: Double});
            `FMIN_D:    tagged Valid (tagged Fpu FpuInst{func: FMin,     precision: Double});
            `FMAX_D:    tagged Valid (tagged Fpu FpuInst{func: FMax,     precision: Double});
            `FCVT_S_D:  tagged Valid (tagged Fpu FpuInst{func: FCvt_FF,  precision: Single});
            `FCVT_D_S:  tagged Valid (tagged Fpu FpuInst{func: FCvt_FF,  precision: Double});
`ifndef NO_FSQRT
            `FSQRT_D:   tagged Valid (tagged Fpu FpuInst{func: FSqrt,    precision: Double});
`endif

            `FLE_D:     tagged Valid (tagged Fpu FpuInst{func: FLe,      precision: Double});
            `FLT_D:     tagged Valid (tagged Fpu FpuInst{func: FLt,      precision: Double});
            `FEQ_D:     tagged Valid (tagged Fpu FpuInst{func: FEq,      precision: Double});

            `FCVT_W_D:  tagged Valid (tagged Fpu FpuInst{func: FCvt_WF,  precision: Double});
            `FCVT_WU_D: tagged Valid (tagged Fpu FpuInst{func: FCvt_WUF, precision: Double});

            `FCLASS_D:  tagged Valid (tagged Fpu FpuInst{func: FClass,   precision: Double});

            `FCVT_D_W:  tagged Valid (tagged Fpu FpuInst{func: FCvt_FW,  precision: Double});
            `FCVT_D_WU: tagged Valid (tagged Fpu FpuInst{func: FCvt_FWU, precision: Double});

            // Floating-Point Memory instructions
            `FLD:       tagged Valid (tagged Mem RVMemInst{op: tagged Mem Ld, size: D, isUnsigned: False});
            `FSD:       tagged Valid (tagged Mem RVMemInst{op: tagged Mem St, size: D, isUnsigned: False});

            // FMA instructions
            `FMADD_D:   tagged Valid (tagged Fpu FpuInst{func: FMAdd,  precision: Double});
            `FMSUB_D:   tagged Valid (tagged Fpu FpuInst{func: FMSub,  precision: Double});
            `FNMSUB_D:  tagged Valid (tagged Fpu FpuInst{func: FNMSub, precision: Double});
            `FNMADD_D:  tagged Valid (tagged Fpu FpuInst{func: FNMAdd, precision: Double});

            default:    tagged Invalid;
        endcase);
endfunction

function Maybe#(ExecFunc) toExecFuncRV64D(Instruction inst);
    return (case (inst) matches
            `FCVT_L_D:  tagged Valid (tagged Fpu FpuInst{func: FCvt_LF,  precision: Double});
            `FCVT_LU_D: tagged Valid (tagged Fpu FpuInst{func: FCvt_LUF, precision: Double});
            `FMV_X_D:   tagged Valid (tagged Fpu FpuInst{func: FMv_XF,   precision: Double});
            `FCVT_D_L:  tagged Valid (tagged Fpu FpuInst{func: FCvt_FL,  precision: Double});
            `FCVT_D_LU: tagged Valid (tagged Fpu FpuInst{func: FCvt_FLU, precision: Double});
            `FMV_D_X:   tagged Valid (tagged Fpu FpuInst{func: FMv_FX,   precision: Double});

            default:    tagged Invalid;
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
            toExecFuncRV64I(inst),
`ifdef m
            `m ? toExecFuncRV32M(inst) : tagged Invalid,
            `m ? toExecFuncRV64M(inst) : tagged Invalid,
`endif
`ifdef a
            `a ? toExecFuncRV32A(inst) : tagged Invalid,
            `a ? toExecFuncRV64A(inst) : tagged Invalid,
`endif
`ifdef f
            `f ? toExecFuncRV32F(inst) : tagged Invalid,
            `f ? toExecFuncRV64F(inst) : tagged Invalid,
`endif
`ifdef d
            `d ? toExecFuncRV32D(inst) : tagged Invalid,
            `d ? toExecFuncRV64D(inst) : tagged Invalid,
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
