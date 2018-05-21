
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

`include "ProcConfig.bsv"
`include "Opcodes.defines"

//import BuildVector::*;
import VecN::*;
import Opcodes::*;
import RVTypes::*;
import Vector::*;
import DefaultValue::*;

interface RVDecodeInternal;
   method  Maybe#(ExecFunc) toExecFuncRV32I(Instruction inst);
   method Maybe#(ExecFunc) toExecFuncPriv(Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV32M(Bool hasDiv, Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV32A(Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV32F(Bool hasDiv, Bool hasSqrt, Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV32D(Bool hasDiv, Bool hasSqrt, Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV64I(Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV64M(Bool hasDiv, Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV64A(Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV64F(Bool hasDiv, Bool hasSqrt, Instruction inst);
   method Maybe#(ExecFunc) toExecFuncRV64D(Bool hasDiv, Bool hasSqrt, Instruction inst);
endinterface

module mkRVDecodeInternal(RVDecodeInternal);
   GetInstFields getInstFields <- mkGetInstFields();

// RV32 Decoding functions
   method Maybe#(ExecFunc) toExecFuncRV32I(Instruction inst);
    return (case (inst) matches
            // BRANCH
            `BEQ:     tagged Valid (tagged EF_Br BrEq);
            `BNE:     tagged Valid (tagged EF_Br BrNeq);
            `BLT:     tagged Valid (tagged EF_Br BrLt);
            `BGE:     tagged Valid (tagged EF_Br BrGe);
            `BLTU:    tagged Valid (tagged EF_Br BrLtu);
            `BGEU:    tagged Valid (tagged EF_Br BrGeu);
            // JALR
            `JALR:    tagged Valid (tagged EF_Br BrJalr);
            // JAL
            `JAL:     tagged Valid (tagged EF_Br BrJal);
            // LUI
            `LUI:     tagged Valid (tagged EF_Alu AluInst{op: AluLui,   w: False});
            // AUIPC
            `AUIPC:   tagged Valid (tagged EF_Alu AluInst{op: AluAuipc, w: False});
            // OP-IMM
            `ADDI:    tagged Valid (tagged EF_Alu AluInst{op: AluAdd,   w: False});
            `SLLI_32: tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: False});
            `SLTI:    tagged Valid (tagged EF_Alu AluInst{op: AluSlt,   w: False});
            `SLTIU:   tagged Valid (tagged EF_Alu AluInst{op: AluSltu,  w: False});
            `XORI:    tagged Valid (tagged EF_Alu AluInst{op: AluXor,   w: False});
            `SRLI_32: tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: False});
            `SRAI_32: tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: False});
            `ORI:     tagged Valid (tagged EF_Alu AluInst{op: AluOr,    w: False});
            `ANDI:    tagged Valid (tagged EF_Alu AluInst{op: AluAnd,   w: False});
            // OP
            `ADD:     tagged Valid (tagged EF_Alu AluInst{op: AluAdd,   w: False});
            `SUB:     tagged Valid (tagged EF_Alu AluInst{op: AluSub,   w: False});
            `SLL:     tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: False});
            `SLT:     tagged Valid (tagged EF_Alu AluInst{op: AluSlt,   w: False});
            `SLTU:    tagged Valid (tagged EF_Alu AluInst{op: AluSltu,  w: False});
            `XOR:     tagged Valid (tagged EF_Alu AluInst{op: AluXor,   w: False});
            `SRL:     tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: False});
            `SRA:     tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: False});
            `OR:      tagged Valid (tagged EF_Alu AluInst{op: AluOr,    w: False});
            `AND:     tagged Valid (tagged EF_Alu AluInst{op: AluAnd,   w: False});
            // LOAD
            `LB:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: B, isUnsigned: False});
            `LH:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: H, isUnsigned: False});
            `LW:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: W, isUnsigned: False});
            `LBU:     tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: B, isUnsigned: True});
            `LHU:     tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: H, isUnsigned: True});
            // STORE
            `SB:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: B, isUnsigned: False});
            `SH:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: H, isUnsigned: False});
            `SW:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: W, isUnsigned: False});
            // MISC-MEM
            `FENCE:   tagged Valid (tagged EF_Fence (tagged InterCore unpack(truncate(inst[27:20]))));
            `FENCE_I: tagged Valid (tagged EF_Fence (tagged IntraCore FenceI));

            default:  tagged Invalid;
        endcase);
endmethod

// Same for RV32 and RV64
method Maybe#(ExecFunc) toExecFuncPriv(Instruction inst);
    InstructionFields instFields = getInstFields.getInstFields(inst);
    return (case (inst) matches
            `ECALL:     tagged Valid (tagged EF_System ECall);
            `EBREAK:    tagged Valid (tagged EF_System EBreak);
            // `URET:      tagged Valid (tagged EF_System URet);
            `SRET:      tagged Valid (tagged EF_System SRet);
            // `HRET:      tagged Valid (tagged EF_System HRet);
            `MRET:      tagged Valid (tagged EF_System MRet);
            `SFENCE_VM: tagged Valid (tagged EF_Fence (tagged IntraCore SFenceVM));
            `WFI:       tagged Valid (tagged EF_System WFI);
            `CSRRW:     tagged Valid (tagged EF_System ((instFields.rd == 0) ? CSRW : CSRRW));
            `CSRRS:     tagged Valid (tagged EF_System ((instFields.rs1 == 0) ? CSRR : CSRRS));
            `CSRRC:     tagged Valid (tagged EF_System ((instFields.rs1 == 0) ? CSRR : CSRRC));
            `CSRRWI:    tagged Valid (tagged EF_System ((instFields.rd == 0) ? CSRW : CSRRW));
            `CSRRSI:    tagged Valid (tagged EF_System ((instFields.rs1 == 0) ? CSRR : CSRRS));
            `CSRRCI:    tagged Valid (tagged EF_System ((instFields.rs1 == 0) ? CSRR : CSRRC));

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV32M(Bool hasDiv, Instruction inst);
    return (case(inst) matches
            `MUL:       tagged Valid (tagged EF_MulDiv MulDivInst{func: Mul,  w: False, sign: Signed});
            `MULH:      tagged Valid (tagged EF_MulDiv MulDivInst{func: Mulh, w: False, sign: Signed});
            `MULHSU:    tagged Valid (tagged EF_MulDiv MulDivInst{func: Mulh, w: False, sign: SignedUnsigned});
            `MULHU:     tagged Valid (tagged EF_MulDiv MulDivInst{func: Mulh, w: False, sign: Unsigned});
            `DIV:       (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Div,  w: False, sign: Signed}) : tagged Invalid);
            `DIVU:      (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Div,  w: False, sign: Unsigned}) : tagged Invalid);
            `REM:       (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Rem,  w: False, sign: Signed}) : tagged Invalid);
            `REMU:      (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Rem,  w: False, sign: Unsigned}) : tagged Invalid);

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV32A(Instruction inst);
    return (case (inst) matches
            `AMOADD_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Add,  size: W, isUnsigned: False});
            `AMOXOR_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Xor,  size: W, isUnsigned: False});
            `AMOOR_W:   tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Or,   size: W, isUnsigned: False});
            `AMOAND_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp And,  size: W, isUnsigned: False});
            `AMOMIN_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Min,  size: W, isUnsigned: False});
            `AMOMAX_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Max,  size: W, isUnsigned: False});
            `AMOMINU_W: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Minu, size: W, isUnsigned: False});
            `AMOMAXU_W: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Maxu, size: W, isUnsigned: False});
            `AMOSWAP_W: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Swap, size: W, isUnsigned: False});
            `LR_W:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Lr,   size: W, isUnsigned: False});
            `SC_W:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Sc,   size: W, isUnsigned: False});

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV32F(Bool hasDiv, Bool hasSqrt, Instruction inst);
    return (case (inst) matches
            `FADD_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FAdd,     precision: Single});
            `FSUB_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FSub,     precision: Single});
            `FMUL_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FMul,     precision: Single});
            `FDIV_S:    (hasDiv ? tagged Valid (tagged EF_Fpu FpuInst{func: FDiv,     precision: Single}) : tagged Invalid);
            `FSGNJ_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FSgnj,    precision: Single});
            `FSGNJN_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjn,   precision: Single});
            `FSGNJX_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjx,   precision: Single});
            `FMIN_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FMin,     precision: Single});
            `FMAX_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FMax,     precision: Single});
            `FSQRT_S:   (hasSqrt ? tagged Valid (tagged EF_Fpu FpuInst{func: FSqrt,    precision: Single}) : tagged Invalid);

            `FLE_S:     tagged Valid (tagged EF_Fpu FpuInst{func: FLe,      precision: Single});
            `FLT_S:     tagged Valid (tagged EF_Fpu FpuInst{func: FLt,      precision: Single});
            `FEQ_S:     tagged Valid (tagged EF_Fpu FpuInst{func: FEq,      precision: Single});

            `FCVT_W_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WF,  precision: Single});
            `FCVT_WU_S: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WUF, precision: Single});

            `FMV_X_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FMv_XF,   precision: Single});

            `FCLASS_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FClass,   precision: Single});

            `FCVT_S_W:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FW,  precision: Single});
            `FCVT_S_WU: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FWU, precision: Single});
            `FMV_S_X:   tagged Valid (tagged EF_Fpu FpuInst{func: FMv_FX,   precision: Single});

            // Floating-Point Memory instructions
            `FLW:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: W, isUnsigned: True});
            `FSW:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: W, isUnsigned: True});

            // FMA instructions
            `FMADD_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FMAdd,  precision: Single});
            `FMSUB_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FMSub,  precision: Single});
            `FNMSUB_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMSub, precision: Single});
            `FNMADD_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMAdd, precision: Single});

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV32D(Bool hasDiv, Bool hasSqrt, Instruction inst);
    return (case (inst) matches
            `FADD_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FAdd,     precision: Double});
            `FSUB_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FSub,     precision: Double});
            `FMUL_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FMul,     precision: Double});
            `FDIV_D:    (hasDiv ? tagged Valid (tagged EF_Fpu FpuInst{func: FDiv,     precision: Double}) : tagged Invalid);
            `FSGNJ_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FSgnj,    precision: Double});
            `FSGNJN_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjn,   precision: Double});
            `FSGNJX_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjx,   precision: Double});
            `FMIN_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FMin,     precision: Double});
            `FMAX_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FMax,     precision: Double});
            `FCVT_S_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FF,  precision: Single});
            `FCVT_D_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FF,  precision: Double});
            `FSQRT_D:   (hasSqrt ? tagged Valid (tagged EF_Fpu FpuInst{func: FSqrt,    precision: Double}) : tagged Invalid);

            `FLE_D:     tagged Valid (tagged EF_Fpu FpuInst{func: FLe,      precision: Double});
            `FLT_D:     tagged Valid (tagged EF_Fpu FpuInst{func: FLt,      precision: Double});
            `FEQ_D:     tagged Valid (tagged EF_Fpu FpuInst{func: FEq,      precision: Double});

            `FCVT_W_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WF,  precision: Double});
            `FCVT_WU_D: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WUF, precision: Double});

            `FCLASS_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FClass,   precision: Double});

            `FCVT_D_W:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FW,  precision: Double});
            `FCVT_D_WU: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FWU, precision: Double});

            // Floating-Point Memory instructions
            `FLD:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: D, isUnsigned: False});
            `FSD:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: D, isUnsigned: False});

            // FMA instructions
            `FMADD_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FMAdd,  precision: Double});
            `FMSUB_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FMSub,  precision: Double});
            `FNMSUB_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMSub, precision: Double});
            `FNMADD_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMAdd, precision: Double});

            default:    tagged Invalid;
        endcase);
endmethod

// RV64 Decoding functions
method Maybe#(ExecFunc) toExecFuncRV64I(Instruction inst);
    return (case (inst) matches
            // RV32/64 instructions
            // BRANCH
            `BEQ:     tagged Valid (tagged EF_Br BrEq);
            `BNE:     tagged Valid (tagged EF_Br BrNeq);
            `BLT:     tagged Valid (tagged EF_Br BrLt);
            `BGE:     tagged Valid (tagged EF_Br BrGe);
            `BLTU:    tagged Valid (tagged EF_Br BrLtu);
            `BGEU:    tagged Valid (tagged EF_Br BrGeu);
            // JALR
            `JALR:    tagged Valid (tagged EF_Br BrJalr);
            // JAL
            `JAL:     tagged Valid (tagged EF_Br BrJal);
            // LUI
            `LUI:     tagged Valid (tagged EF_Alu AluInst{op: AluLui,   w: False});
            // AUIPC
            `AUIPC:   tagged Valid (tagged EF_Alu AluInst{op: AluAuipc, w: False});
            // OP-IMM
            `ADDI:    tagged Valid (tagged EF_Alu AluInst{op: AluAdd,   w: False});
            `SLLI_32: tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: False});
            `SLTI:    tagged Valid (tagged EF_Alu AluInst{op: AluSlt,   w: False});
            `SLTIU:   tagged Valid (tagged EF_Alu AluInst{op: AluSltu,  w: False});
            `XORI:    tagged Valid (tagged EF_Alu AluInst{op: AluXor,   w: False});
            `SRLI_32: tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: False});
            `SRAI_32: tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: False});
            `ORI:     tagged Valid (tagged EF_Alu AluInst{op: AluOr,    w: False});
            `ANDI:    tagged Valid (tagged EF_Alu AluInst{op: AluAnd,   w: False});
            // OP
            `ADD:     tagged Valid (tagged EF_Alu AluInst{op: AluAdd,   w: False});
            `SUB:     tagged Valid (tagged EF_Alu AluInst{op: AluSub,   w: False});
            `SLL:     tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: False});
            `SLT:     tagged Valid (tagged EF_Alu AluInst{op: AluSlt,   w: False});
            `SLTU:    tagged Valid (tagged EF_Alu AluInst{op: AluSltu,  w: False});
            `XOR:     tagged Valid (tagged EF_Alu AluInst{op: AluXor,   w: False});
            `SRL:     tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: False});
            `SRA:     tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: False});
            `OR:      tagged Valid (tagged EF_Alu AluInst{op: AluOr,    w: False});
            `AND:     tagged Valid (tagged EF_Alu AluInst{op: AluAnd,   w: False});
            // LOAD
            `LB:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: B, isUnsigned: False});
            `LH:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: H, isUnsigned: False});
            `LW:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: W, isUnsigned: False});
            `LBU:     tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: B, isUnsigned: True});
            `LHU:     tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: H, isUnsigned: True});
            // STORE
            `SB:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: B, isUnsigned: False});
            `SH:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: H, isUnsigned: False});
            `SW:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: W, isUnsigned: False});
            // MISC-MEM
            `FENCE:   tagged Valid (tagged EF_Fence (tagged InterCore unpack(truncate(inst[27:20]))));
            `FENCE_I: tagged Valid (tagged EF_Fence (tagged IntraCore FenceI));

            // RV64-specific instructions
            // OP-IMM
            `SLLI_64: tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: False});
            `SRLI_64: tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: False});
            `SRAI_64: tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: False});
            // OP-IMM-32
            `ADDIW:   tagged Valid (tagged EF_Alu AluInst{op: AluAdd,   w: True});
            `SLLIW:   tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: True});
            `SRLIW:   tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: True});
            `SRAIW:   tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: True});
            // OP-32
            `ADDW:    tagged Valid (tagged EF_Alu AluInst{op: AluAdd,   w: True});
            `SUBW:    tagged Valid (tagged EF_Alu AluInst{op: AluSub,   w: True});
            `SLLW:    tagged Valid (tagged EF_Alu AluInst{op: AluSll,   w: True});
            `SRLW:    tagged Valid (tagged EF_Alu AluInst{op: AluSrl,   w: True});
            `SRAW:    tagged Valid (tagged EF_Alu AluInst{op: AluSra,   w: True});
            // LOAD
            `LD:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: D, isUnsigned: False});
            `LWU:     tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: W, isUnsigned: True});
            // STORE
            `SD:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: D, isUnsigned: False});

            default:  tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV64M(Bool hasDiv, Instruction inst);
    return (case(inst) matches
            // RV32/64 instructions
            `MUL:       tagged Valid (tagged EF_MulDiv MulDivInst{func: Mul,  w: False, sign: Signed});
            `MULH:      tagged Valid (tagged EF_MulDiv MulDivInst{func: Mulh, w: False, sign: Signed});
            `MULHSU:    tagged Valid (tagged EF_MulDiv MulDivInst{func: Mulh, w: False, sign: SignedUnsigned});
            `MULHU:     tagged Valid (tagged EF_MulDiv MulDivInst{func: Mulh, w: False, sign: Unsigned});
            `DIV:       (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Div,  w: False, sign: Signed}) : tagged Invalid);
            `DIVU:      (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Div,  w: False, sign: Unsigned}) : tagged Invalid);
            `REM:       (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Rem,  w: False, sign: Signed}) : tagged Invalid);
            `REMU:      (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Rem,  w: False, sign: Unsigned}) : tagged Invalid);

            // RV64-specific instructions
            `MULW:      tagged Valid (tagged EF_MulDiv MulDivInst{func: Mul,  w: True,  sign: Signed});
            `DIVW:      (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Div,  w: True,  sign: Signed}) : tagged Invalid);
            `DIVUW:     (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Div,  w: True,  sign: Unsigned}) : tagged Invalid);
            `REMW:      (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Rem,  w: True,  sign: Signed}) : tagged Invalid);
            `REMUW:     (hasDiv ? tagged Valid (tagged EF_MulDiv MulDivInst{func: Rem,  w: True,  sign: Unsigned}) : tagged Invalid);

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV64A(Instruction inst);
    return (case (inst) matches
            // RV32/64 instructions
            `AMOADD_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Add,  size: W, isUnsigned: False});
            `AMOXOR_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Xor,  size: W, isUnsigned: False});
            `AMOOR_W:   tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Or,   size: W, isUnsigned: False});
            `AMOAND_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp And,  size: W, isUnsigned: False});
            `AMOMIN_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Min,  size: W, isUnsigned: False});
            `AMOMAX_W:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Max,  size: W, isUnsigned: False});
            `AMOMINU_W: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Minu, size: W, isUnsigned: False});
            `AMOMAXU_W: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Maxu, size: W, isUnsigned: False});
            `AMOSWAP_W: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Swap, size: W, isUnsigned: False});
            `LR_W:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Lr,   size: W, isUnsigned: False});
            `SC_W:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Sc,   size: W, isUnsigned: False});

            // RV64-specific instructions
            `AMOADD_D:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Add,  size: D, isUnsigned: False});
            `AMOXOR_D:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Xor,  size: D, isUnsigned: False});
            `AMOOR_D:   tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Or,   size: D, isUnsigned: False});
            `AMOAND_D:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp And,  size: D, isUnsigned: False});
            `AMOMIN_D:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Min,  size: D, isUnsigned: False});
            `AMOMAX_D:  tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Max,  size: D, isUnsigned: False});
            `AMOMINU_D: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Minu, size: D, isUnsigned: False});
            `AMOMAXU_D: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Maxu, size: D, isUnsigned: False});
            `AMOSWAP_D: tagged Valid (tagged EF_Mem RVMemInst{op: tagged AmoOp Swap, size: D, isUnsigned: False});
            `LR_D:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Lr,   size: D, isUnsigned: False});
            `SC_D:      tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Sc,   size: D, isUnsigned: False});

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV64F(Bool hasDiv, Bool hasSqrt, Instruction inst);
    return (case (inst) matches
            // RV32/64 instructions
            `FADD_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FAdd,     precision: Single});
            `FSUB_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FSub,     precision: Single});
            `FMUL_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FMul,     precision: Single});
            `FDIV_S:    (hasDiv ? tagged Valid (tagged EF_Fpu FpuInst{func: FDiv,     precision: Single}) : tagged Invalid);
            `FSGNJ_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FSgnj,    precision: Single});
            `FSGNJN_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjn,   precision: Single});
            `FSGNJX_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjx,   precision: Single});
            `FMIN_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FMin,     precision: Single});
            `FMAX_S:    tagged Valid (tagged EF_Fpu FpuInst{func: FMax,     precision: Single});
            `FSQRT_S:   (hasSqrt ? tagged Valid (tagged EF_Fpu FpuInst{func: FSqrt,    precision: Single}) : tagged Invalid);

            `FLE_S:     tagged Valid (tagged EF_Fpu FpuInst{func: FLe,      precision: Single});
            `FLT_S:     tagged Valid (tagged EF_Fpu FpuInst{func: FLt,      precision: Single});
            `FEQ_S:     tagged Valid (tagged EF_Fpu FpuInst{func: FEq,      precision: Single});

            `FCVT_W_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WF,  precision: Single});
            `FCVT_WU_S: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WUF, precision: Single});

            `FMV_X_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FMv_XF,   precision: Single});

            `FCLASS_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FClass,   precision: Single});

            `FCVT_S_W:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FW,  precision: Single});
            `FCVT_S_WU: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FWU, precision: Single});
            `FMV_S_X:   tagged Valid (tagged EF_Fpu FpuInst{func: FMv_FX,   precision: Single});

            // Floating-Point Memory instructions
            `FLW:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: W, isUnsigned: True});
            `FSW:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: W, isUnsigned: True});

            // FMA instructions
            `FMADD_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FMAdd,  precision: Single});
            `FMSUB_S:   tagged Valid (tagged EF_Fpu FpuInst{func: FMSub,  precision: Single});
            `FNMSUB_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMSub, precision: Single});
            `FNMADD_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMAdd, precision: Single});

            // RV64-specific instructions
            `FCVT_L_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_LF,  precision: Single});
            `FCVT_LU_S: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_LUF, precision: Single});
            `FCVT_S_L:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FL,  precision: Single});
            `FCVT_S_LU: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FLU, precision: Single});

            default:    tagged Invalid;
        endcase);
endmethod

method Maybe#(ExecFunc) toExecFuncRV64D(Bool hasDiv, Bool hasSqrt, Instruction inst);
    return (case (inst) matches
            // RV32/64 instructions
            `FADD_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FAdd,     precision: Double});
            `FSUB_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FSub,     precision: Double});
            `FMUL_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FMul,     precision: Double});
            `FDIV_D:    (hasDiv ? tagged Valid (tagged EF_Fpu FpuInst{func: FDiv,     precision: Double}) : tagged Invalid);
            `FSGNJ_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FSgnj,    precision: Double});
            `FSGNJN_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjn,   precision: Double});
            `FSGNJX_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FSgnjx,   precision: Double});
            `FMIN_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FMin,     precision: Double});
            `FMAX_D:    tagged Valid (tagged EF_Fpu FpuInst{func: FMax,     precision: Double});
            `FCVT_S_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FF,  precision: Single});
            `FCVT_D_S:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FF,  precision: Double});
            `FSQRT_D:   (hasSqrt ? tagged Valid (tagged EF_Fpu FpuInst{func: FSqrt,    precision: Double}) : tagged Invalid);

            `FLE_D:     tagged Valid (tagged EF_Fpu FpuInst{func: FLe,      precision: Double});
            `FLT_D:     tagged Valid (tagged EF_Fpu FpuInst{func: FLt,      precision: Double});
            `FEQ_D:     tagged Valid (tagged EF_Fpu FpuInst{func: FEq,      precision: Double});

            `FCVT_W_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WF,  precision: Double});
            `FCVT_WU_D: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_WUF, precision: Double});

            `FCLASS_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FClass,   precision: Double});

            `FCVT_D_W:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FW,  precision: Double});
            `FCVT_D_WU: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FWU, precision: Double});

            // Floating-Point Memory instructions
            `FLD:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp Ld, size: D, isUnsigned: False});
            `FSD:       tagged Valid (tagged EF_Mem RVMemInst{op: tagged MemOp St, size: D, isUnsigned: False});

            // FMA instructions
            `FMADD_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FMAdd,  precision: Double});
            `FMSUB_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FMSub,  precision: Double});
            `FNMSUB_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMSub, precision: Double});
            `FNMADD_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FNMAdd, precision: Double});

            // RV64-specific instructions
            `FCVT_L_D:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_LF,  precision: Double});
            `FCVT_LU_D: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_LUF, precision: Double});
            `FMV_X_D:   tagged Valid (tagged EF_Fpu FpuInst{func: FMv_XF,   precision: Double});
            `FCVT_D_L:  tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FL,  precision: Double});
            `FCVT_D_LU: tagged Valid (tagged EF_Fpu FpuInst{func: FCvt_FLU, precision: Double});
            `FMV_D_X:   tagged Valid (tagged EF_Fpu FpuInst{func: FMv_FX,   precision: Double});

            default:    tagged Invalid;
        endcase);
endmethod
endmodule

interface RVDecode;
   method Maybe#(RVDecodedInst) decodeInst(Bool isRV64, Bool hasM, Bool hasA, Bool hasF, Bool hasD, Instruction inst);
   method Maybe#(Bit#(XLEN)) getImmediate(ImmType imm, Instruction inst);
   method Bit#(2) getMinPriv(Instruction inst);
endinterface

module mkRVDecode(RVDecode);
   GetInstFields getInstFields <- mkGetInstFields();
   ToInstType toInstType <- mkToInstType();   
   RVDecodeInternal decodeInternal <- mkRVDecodeInternal();   

// This returns a valid result if the instruction is legal, otherwise it
// returns a tagged invalid.
method Maybe#(RVDecodedInst) decodeInst(Bool isRV64, Bool hasM, Bool hasA, Bool hasF, Bool hasD, Instruction inst);
    // Construct a vector of all the results
    // We will apply a fold function on this vector to find the valid result
    let decoderResults = vec6(
            isRV64 ? decodeInternal.toExecFuncRV64I(inst) : decodeInternal.toExecFuncRV32I(inst),
            hasM ? (isRV64 ? decodeInternal.toExecFuncRV64M(True, inst) : decodeInternal.toExecFuncRV32M(True, inst)) : tagged Invalid,
            hasA ? (isRV64 ? decodeInternal.toExecFuncRV64A(inst) : decodeInternal.toExecFuncRV32A(inst)) : tagged Invalid,
            hasF ? (isRV64 ? decodeInternal.toExecFuncRV64F(True, True, inst) : decodeInternal.toExecFuncRV32F(True, True, inst)) : tagged Invalid,
            hasD ? (isRV64 ? decodeInternal.toExecFuncRV64D(True, True, inst) : decodeInternal.toExecFuncRV32D(True, True, inst)) : tagged Invalid,
            decodeInternal.toExecFuncPriv(inst)
        );

    // This fold is equivalent to going down the list of decoder results and
    // returning the first valid result
    function Maybe#(t) fold_op(Maybe#(t) x, Maybe#(t) y) provisos (Bits#(t, tSz));
        return isValid(x) ? x : y;
    endfunction
    let execFunc = fold(fold_op, decoderResults);

    if (execFunc matches tagged Valid .validExecFunc) begin
        InstType instType = toInstType.toInstType(inst);
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
endmethod

// This function is used to get the immediate value from a decoded instruction
method Maybe#(Bit#(XLEN)) getImmediate(ImmType imm, Instruction inst)
        provisos (Add#(a__, 5, XLEN),
                  Add#(b__, 12, XLEN),
                  Add#(c__, 13, XLEN),
                  Add#(d__, 21, XLEN),
                  Add#(e__, 32, XLEN));
    Bit#(XLEN) immI  = signExtend(inst[31:20]);
    Bit#(XLEN) immS  = signExtend({inst[31:25], inst[11:7]});
    Bit#(XLEN) immSB = signExtend({inst[31], inst[7], inst[30:25], inst[11:8], 1'b0});
    Bit#(XLEN) immU  = signExtend({inst[31:12], 12'b0});
    Bit#(XLEN) immUJ = signExtend({inst[31], inst[19:12], inst[20], inst[30:21], 1'b0});
    Bit#(XLEN) immZ  = zeroExtend(inst[19:15]);
    return (case (imm)
            ItS:  tagged Valid immS;
            ItSB: tagged Valid immSB;
            ItU:  tagged Valid immU;
            ItUJ: tagged Valid immUJ;
            ItI:  tagged Valid immI;
            ItZ:  tagged Valid immZ;
            default: tagged Invalid;
        endcase);
endmethod

method Bit#(2) getMinPriv(Instruction inst);
    return (getInstFields.getInstFields(inst).opcode == System) ? inst[29:28] : prvU;
endmethod
endmodule
