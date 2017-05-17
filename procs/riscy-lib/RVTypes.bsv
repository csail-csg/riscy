
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
import DefaultValue::*;
import FShow::*;
import Vector::*;

`ifdef CONFIG_RV64
typedef 64 XLEN;
`endif
`ifdef CONFIG_RV32
typedef 32 XLEN;
`endif

typedef XLEN DataSz;
typedef Bit#(DataSz) Data;
typedef Bit#(TDiv#(DataSz,8)) DataByteEn;
typedef Bit#(TLog#(TDiv#(DataSz,8))) DataByteSel; // Type of byte select value for Data

typedef 512 CacheLineSz; // Used in DCache.bsv

typedef 32 InstSz;
typedef Bit#(InstSz) Instruction;

// Virtual address
typedef XLEN AddrSz;
typedef Bit#(AddrSz) Addr;

// Physical address
typedef 64 PAddrSz;
typedef Bit#(PAddrSz) PAddr;

`ifdef CONFIG_RV64
typedef 26 AsidSz;
`endif
`ifdef CONFIG_RV32
typedef 10 AsidSz;
`endif
typedef Bit#(AsidSz) Asid;

// WARNING: Don't try updating fields when using this type.
typedef struct {
    // full instruction
    Instruction inst;
    // fields (XXX: Should these be Bits or enums?)
    Bit#(5)     rd;
    Bit#(5)     rs1;
    Bit#(5)     rs2;
    Bit#(5)     rs3;
    Bit#(2)     funct2;
    Bit#(3)     funct3;
    Bit#(5)     funct5;
    Bit#(7)     funct7;
    Bit#(2)     fmt;
    RVRoundMode rm;
    Opcode      opcode; // Bit#(7)
    Bit#(12)    csrAddr;
    CSR         csr;
} InstructionFields;
// XXX: probably don't want a Bits instance for this type
instance Bits#(InstructionFields, 32);
    function Bit#(32) pack(InstructionFields x);
        return x.inst;
    endfunction
    function InstructionFields unpack(Bit#(32) x);
        return getInstFields(x);
    endfunction
endinstance
// XXX: ... or an Eq instance
instance Eq#(InstructionFields);
    function Bool \== (InstructionFields a, InstructionFields b);
        return a.inst == b.inst;
    endfunction
endinstance
// XXX: ... or an FShow instance
instance FShow#(InstructionFields);
    function Fmt fshow(InstructionFields x);
        return $format("{InstructionFields: 0x%08x}",x);
    endfunction
endinstance
// XXX: we probably just want this function
function InstructionFields getInstFields(Instruction x);
    return InstructionFields {
            inst:       x,
            rd:         x[11:7],
            rs1:        x[19:15],
            rs2:        x[24:20],
            rs3:        x[31:27],
            funct2:     x[26:25],
            funct3:     x[14:12],
            funct5:     x[31:27],
            funct7:     x[31:25],
            fmt:        x[26:25],
            rm:         unpack(x[14:12]),
            opcode:     unpack(x[6:0]),
            csrAddr:    x[31:20],
            csr:        unpack(x[31:20])
        };
endfunction

// This encoding partially matches rocket, one day we may be able to use the same caches
// These are requests that a processor may send to the 
typedef enum {
    Ld              = 3'b000,
    St              = 3'b001,
    PrefetchForLd   = 3'b010,
    PrefetchForSt   = 3'b011,
    Lr              = 3'b110,
    Sc              = 3'b111
} RVMemOp deriving (Bits, Eq, FShow);

// This encoding matches inst[31,30,29,27] since inst[28] is always 0
typedef enum {
    Swap    = 4'b0001,
    Add     = 4'b0000,
    Xor     = 4'b0010,
    And     = 4'b0110,
    Or      = 4'b0100,
    Min     = 4'b1000,
    Max     = 4'b1010,
    Minu    = 4'b1100,
    Maxu    = 4'b1110
} RVAmoOp deriving (Bits, Eq, FShow);

//// This encoding matches rocket
//typedef enum {
//    Ld              = 5'b00000,
//    St              = 5'b00001,
//    PrefetchForLd   = 5'b00010,
//    PrefetchForSt   = 5'b00011,
//    AmoSwap         = 5'b00100,
//    Nop             = 5'b00101,
//    Lr              = 5'b00110,
//    Sc              = 5'b00111,
//    AmoAdd          = 5'b01000,
//    AmoXor          = 5'b01001,
//    AmoOr           = 5'b01010,
//    AmoAnd          = 5'b01011,
//    AmoMin          = 5'b01100,
//    AmoMax          = 5'b01101,
//    AmoMinu         = 5'b01110,
//    AmoMaxu         = 5'b01111,
//    Flush           = 5'b10000,
//    Produce         = 5'b10001,
//    Clean           = 5'b10011
//} RVRocketMemOp deriving (Bits, Eq, FShow);
//
//// Functions from rocket
//function Bool isAMO(RVRocketMemOp op);
//    return (case (op)
//            AmoSwap, AmoAdd, AmoXor, AmoOr, AmoAnd, AmoMin, AmoMax, AmoMinu, AmoMaxu: True;
//            default: False;
//        endcase);
//endfunction
//function Bool isPrefetch(RVRocketMemOp op);
//    return (op == PrefetchForLd) || (op == PrefetchForSt);
//endfunction
//function Bool isRead(RVRocketMemOp op);
//    return (op == Ld) || (op == Lr) || (op == Sc) || isAMO(op);
//endfunction
//function Bool isWrite(RVRocketMemOp op);
//    return (op == St) || (op == Sc) || isAMO(op);
//endfunction
//function Bool isWriteIntent(RVRocketMemOp op);
//    return isWrite(op) || (op == PrefetchForSt) || (op == Lr);
//endfunction

// This encoding matches the bottom two bits of func3
typedef enum {
    B   = 2'b00,
    H   = 2'b01,
    W   = 2'b10,
    D   = 2'b11
} RVMemSize deriving (Bits, Eq, FShow);

typeclass ToDataByteEn#(numeric type n);
    function Bit#(n) toDataByteEn(RVMemSize size);
endtypeclass

// RV32 Instance
instance ToDataByteEn#(4);
    function Bit#(4) toDataByteEn(RVMemSize size);
        return (case (size)
                B:       4'b0001;
                H:       4'b0011;
                W:       4'b1111;
                // D is illegal
                default: 4'b0000;
            endcase);
    endfunction
endinstance

// RV64 Instance
instance ToDataByteEn#(8);
    function Bit#(8) toDataByteEn(RVMemSize size);
        return (case (size)
                B:       8'b00000001;
                H:       8'b00000011;
                W:       8'b00001111;
                D:       8'b11111111;
                default: 8'b00000000;
            endcase);
    endfunction
endinstance

function DataByteEn toPermutedDataByteEn(RVMemSize size, DataByteSel addrLSB);
    return toDataByteEn(size) << addrLSB;
endfunction

typedef union tagged {
    RVMemOp Mem;
    RVAmoOp Amo;
} RVMemAmoOp deriving (Bits, Eq, FShow);

typedef struct {
    RVMemAmoOp  op;
    RVMemSize   size;
    Bool        isUnsigned;
} RVMemInst deriving (Bits, Eq, FShow);

typeclass IsMemOp#(type t);
    function Bool isLoad(t x);
    function Bool isStore(t x);
    function Bool isAmo(t x);
    function Bool getsReadPermission(t x);
    function Bool getsWritePermission(t x);
    function Bool getsResponse(t x);
endtypeclass
instance IsMemOp#(RVMemOp);
    function Bool isLoad(RVMemOp x);
        return ((x == Ld) || (x == Lr));
    endfunction
    function Bool isStore(RVMemOp x);
        return ((x == St) || (x == Sc));
    endfunction
    function Bool isAmo(RVMemOp x);
        return False;
    endfunction
    function Bool getsReadPermission(RVMemOp x);
        return ((x == Ld) || (x == PrefetchForLd));
    endfunction
    function Bool getsWritePermission(RVMemOp x);
        return (isStore(x) || (x == Lr) || (x == PrefetchForSt));
    endfunction
    function Bool getsResponse(RVMemOp x);
        return (isLoad(x) || isAmo(x) || (x == Sc));
    endfunction
endinstance
instance IsMemOp#(RVAmoOp);
    function Bool isLoad(RVAmoOp x);
        return False;
    endfunction
    function Bool isStore(RVAmoOp x);
        return False;
    endfunction
    function Bool isAmo(RVAmoOp x);
        return True;
    endfunction
    function Bool getsReadPermission(RVAmoOp x);
        return False;
    endfunction
    function Bool getsWritePermission(RVAmoOp x);
        return True;
    endfunction
    function Bool getsResponse(RVAmoOp x);
        return True;
    endfunction
endinstance
instance IsMemOp#(RVMemAmoOp);
    function Bool isLoad(RVMemAmoOp x);
        return (case (x) matches
                tagged Mem .mem: isLoad(mem);
                tagged Amo .amo: isLoad(amo);
            endcase);
    endfunction
    function Bool isStore(RVMemAmoOp x);
        return (case (x) matches
                tagged Mem .mem: isStore(mem);
                tagged Amo .amo: isStore(amo);
            endcase);
    endfunction
    function Bool isAmo(RVMemAmoOp x);
        return (case (x) matches
                tagged Mem .mem: isAmo(mem);
                tagged Amo .amo: isAmo(amo);
            endcase);
    endfunction
    function Bool getsReadPermission(RVMemAmoOp x);
        return (case (x) matches
                tagged Mem .mem: getsReadPermission(mem);
                tagged Amo .amo: getsReadPermission(amo);
            endcase);
    endfunction
    function Bool getsWritePermission(RVMemAmoOp x);
        return (case (x) matches
                tagged Mem .mem: getsWritePermission(mem);
                tagged Amo .amo: getsWritePermission(amo);
            endcase);
    endfunction
    function Bool getsResponse(RVMemAmoOp x);
        return (case (x) matches
                tagged Mem .mem: getsResponse(mem);
                tagged Amo .amo: getsResponse(amo);
            endcase);
    endfunction
endinstance

typedef struct {
    Bool rv64;
    // ISA modes
    Bool h;
    Bool s;
    Bool u;
    // standard ISA extensions
    Bool m;
    Bool a;
    Bool f;
    Bool d;
    // non-standard extensions
    Bool x;
} RiscVISASubset deriving (Bits, Eq, FShow);

instance DefaultValue#(RiscVISASubset);
    function RiscVISASubset defaultValue = RiscVISASubset{
`ifdef CONFIG_RV64
            rv64:   True,
`else
            rv64:   False,
`endif
            h:      False,
`ifdef CONFIG_S
            s:      True,
`else
            s:      False,
`endif
`ifdef CONFIG_U
            u:      True,
`else
            u:      False,
`endif
`ifdef CONFIG_M
            m:      True,
`else
            m:      False,
`endif
`ifdef CONFIG_A
            a:      True,
`else
            a:      False,
`endif
`ifdef CONFIG_F
            f:      True,
`else
            f:      False,
`endif
`ifdef CONFIG_D
            d:      True,
`else
            d:      False,
`endif
            x:      False
    };
endinstance

function Data getMISA(RiscVISASubset isa);
    // include I by default
    Data misa = {2'b00, 0, 26'b00000000000000000100000000};
    if (isa.rv64) begin
        // rv64
        misa = misa | {2'b10, 0, 26'b00000000000000000000000000};
    end else begin
        // rv32
        misa = misa | {2'b01, 0, 26'b00000000000000000000000000};
    end
    if (isa.s) misa = misa | {2'b00, 0, 26'b00000001000000000000000000};
    if (isa.u) misa = misa | {2'b00, 0, 26'b00000100000000000000000000};
    if (isa.m) misa = misa | {2'b00, 0, 26'b00000000000001000000000000};
    if (isa.a) misa = misa | {2'b00, 0, 26'b00000000000000000000000001};
    if (isa.f) misa = misa | {2'b00, 0, 26'b00000000000000000000100000};
    if (isa.d) misa = misa | {2'b00, 0, 26'b00000000000000000000001000};
    return misa;
endfunction

typedef Bit#(5) RegIndex;
typedef union tagged {
    RegIndex Gpr;
    RegIndex Fpu;
} FullRegIndex deriving (Bits, Eq, FShow, Bounded);
function Maybe#(FullRegIndex) toFullRegIndex(Maybe#(RegType) rType, RegIndex index);
    return (case (rType)
            tagged Valid Gpr: tagged Valid tagged Gpr index;
            tagged Valid Fpu: tagged Valid tagged Fpu index;
            default: tagged Invalid;
        endcase);
endfunction
typedef 64 NumArchReg;

`ifdef PHYS_REG_COUNT
typedef `PHYS_REG_COUNT NumPhyReg;
`else
typedef NumArchReg NumPhyReg;
`endif

typedef enum {
    Load    = 7'b0000011,
    LoadFp  = 7'b0000111,
    MiscMem = 7'b0001111,
    OpImm   = 7'b0010011,
    Auipc   = 7'b0010111,
    OpImm32 = 7'b0011011,
    Store   = 7'b0100011,
    StoreFp = 7'b0100111,
    Amo     = 7'b0101111,
    Op      = 7'b0110011,
    Lui     = 7'b0110111,
    Op32    = 7'b0111011,
    Fmadd   = 7'b1000011,
    Fmsub   = 7'b1000111,
    Fnmsub  = 7'b1001011,
    Fnmadd  = 7'b1001111,
    OpFp    = 7'b1010011,
    Branch  = 7'b1100011,
    Jalr    = 7'b1100111,
    Jal     = 7'b1101111,
    System  = 7'b1110011
} Opcode deriving (Bits, Eq, FShow);

typedef enum {
    CSRustatus          = 12'h000,
    CSRuie              = 12'h004,
    CSRutvec            = 12'h005,
    CSRuscratch         = 12'h040,
    CSRuepc             = 12'h041,
    CSRucause           = 12'h042,
    CSRubadaddr         = 12'h043,
    CSRuip              = 12'h044,
    CSRfflags           = 12'h001,
    CSRfrm              = 12'h002,
    CSRfcsr             = 12'h003,
    CSRcycle            = 12'hc00,
    CSRtime             = 12'hc01,
    CSRinstret          = 12'hc02,
    CSRcycleh           = 12'hc80,
    CSRtimeh            = 12'hc81,
    CSRinstreth         = 12'hc82,
    CSRsstatus          = 12'h100,
    CSRsedeleg          = 12'h102,
    CSRsideleg          = 12'h103,
    CSRsie              = 12'h104,
    CSRstvec            = 12'h105,
    CSRsscratch         = 12'h140,
    CSRsepc             = 12'h141,
    CSRscause           = 12'h142,
    CSRsbadaddr         = 12'h143,
    CSRsip              = 12'h144,
    CSRsptbr            = 12'h180,
    CSRscycle           = 12'hd00,
    CSRstime            = 12'hd01,
    CSRsinstret         = 12'hd02,
    CSRscycleh          = 12'hd80,
    CSRstimeh           = 12'hd81,
    CSRsinstreth        = 12'hd82,
    CSRhstatus          = 12'h200,
    CSRhedeleg          = 12'h202,
    CSRhideleg          = 12'h203,
    CSRhie              = 12'h204,
    CSRhtvec            = 12'h205,
    CSRhscratch         = 12'h240,
    CSRhepc             = 12'h241,
    CSRhcause           = 12'h242,
    CSRhbadaddr         = 12'h243,
    CSRhcycle           = 12'he00,
    CSRhtime            = 12'he01,
    CSRhinstret         = 12'he02,
    CSRhcycleh          = 12'he80,
    CSRhtimeh           = 12'he81,
    CSRhinstreth        = 12'he82,
    CSRmisa             = 12'hf10,
    CSRmvendorid        = 12'hf11,
    CSRmarchid          = 12'hf12,
    CSRmimpid           = 12'hf13,
    CSRmhartid          = 12'hf14,
    CSRmstatus          = 12'h300,
    CSRmedeleg          = 12'h302,
    CSRmideleg          = 12'h303,
    CSRmie              = 12'h304,
    CSRmtvec            = 12'h305,
    CSRmscratch         = 12'h340,
    CSRmepc             = 12'h341,
    CSRmcause           = 12'h342,
    CSRmbadaddr         = 12'h343,
    CSRmip              = 12'h344,
    CSRmbase            = 12'h380,
    CSRmbound           = 12'h381,
    CSRmibase           = 12'h382,
    CSRmibound          = 12'h383,
    CSRmdbase           = 12'h384,
    CSRmdbound          = 12'h385,
    CSRmcycle           = 12'hf00,
    CSRmtime            = 12'hf01,
    CSRminstret         = 12'hf02,
    CSRmcycleh          = 12'hf80,
    CSRmtimeh           = 12'hf81,
    CSRminstreth        = 12'hf82,
    CSRmucounteren      = 12'h310,
    CSRmscounteren      = 12'h311,
    CSRmhcounteren      = 12'h312,
    CSRmucycle_delta    = 12'h700,
    CSRmutime_delta     = 12'h701,
    CSRmuinstret_delta  = 12'h702,
    CSRmscycle_delta    = 12'h704,
    CSRmstime_delta     = 12'h705,
    CSRmsinstret_delta  = 12'h706,
    CSRmhcycle_delta    = 12'h708,
    CSRmhtime_delta     = 12'h709,
    CSRmhinstret_delta  = 12'h70a,
    CSRmucycle_deltah   = 12'h780,
    CSRmutime_deltah    = 12'h781,
    CSRmuinstret_deltah = 12'h782,
    CSRmscycle_deltah   = 12'h784,
    CSRmstime_deltah    = 12'h785,
    CSRmsinstret_deltah = 12'h786,
    CSRmhcycle_deltah   = 12'h788,
    CSRmhtime_deltah    = 12'h789,
    CSRmhinstret_deltah = 12'h78a
} CSR deriving (Bits, Eq, FShow);

function Bool hasCSRPermission(CSR csr, Bit#(2) prv, Bool write);
    Bit#(12) csr_index = pack(csr);
    return ((prv >= csr_index[9:8]) && (!write || (csr_index[11:10] != 2'b11)));
endfunction

// These enumeration values match the bit values for funct3
typedef enum {
    Eq   = 3'b000,
    Neq  = 3'b001,
    Jal  = 3'b010,
    Jalr = 3'b011,
    Lt   = 3'b100,
    Ge   = 3'b101,
    Ltu  = 3'b110,
    Geu  = 3'b111
} BrFunc deriving (Bits, Eq, FShow);

// This encoding tries to match {inst[30], funct3}
typedef enum {
    Add  = 4'b0000,
    Sll  = 4'b0001,
    Slt  = 4'b0010,
    Sltu = 4'b0011,
    Xor  = 4'b0100,
    Srl  = 4'b0101,
    Or   = 4'b0110,
    And  = 4'b0111,
    Sub  = 4'b1000,
    Sra  = 4'b1101,
    // These don't follow the {inst[30], funct3} encoding since they use
    // different opcodes
    // TODO: check the values of these instructions
    // XXX: Should these not specify a value?
    Auipc = 5'b10000,
    Lui   = 5'b11000
} AluFunc deriving (Bits, Eq, FShow);
typedef struct {
    AluFunc op;
    Bool    w;
} AluInst deriving (Bits, Eq, FShow);

typedef enum {
    Mul     = 2'b00,
    Mulh    = 2'b01,
    Div     = 2'b10,
    Rem     = 2'b11
} MulDivFunc deriving (Bits, Eq, FShow);
typedef enum {Signed, Unsigned, SignedUnsigned} MulDivSign deriving (Bits, Eq, FShow);
typedef struct {
    MulDivFunc  func;
    Bool        w;
    MulDivSign  sign;
} MulDivInst deriving (Bits, Eq, FShow);


typedef enum {
    FAdd, FSub, FMul, FDiv, FSqrt,
    FSgnj, FSgnjn, FSgnjx,
    FMin, FMax,
    FCvt_FF,
    FCvt_WF, FCvt_WUF, FCvt_LF, FCvt_LUF,
    FCvt_FW, FCvt_FWU, FCvt_FL, FCvt_FLU,
    FEq, FLt, FLe,
    FClass, FMv_XF, FMv_FX,
    FMAdd, FMSub, FNMSub, FNMAdd
} FpuFunc deriving (Bits, Eq, FShow);
typedef enum {
    Single,
    Double
} FpuPrecision deriving (Bits, Eq, FShow);
typedef struct {
    FpuFunc         func;
    FpuPrecision    precision;
} FpuInst deriving (Bits, Eq, FShow);


typedef enum {
    FenceI,
    SFenceVM
} IntraCoreFence deriving (Bits, Eq, FShow);

typedef struct {
    Bool sw; // successor wrtie
    Bool sr; // successor read
    Bool so; // successor output
    Bool si; // successor input
    Bool pw; // predecessor write
    Bool pr; // predecessor read
    Bool po; // predecessor output
    Bool pi; // predecessor input
} InterCoreFence deriving (Bits, Eq, FShow);

typedef union tagged {
    IntraCoreFence IntraCore;
    InterCoreFence InterCore;
} Fence deriving (Bits, Eq, FShow);


typedef enum {
    ECall,
    EBreak,
    URet,
    SRet,
    HRet,
    MRet,
    WFI,
    CSRRW,
    CSRRS,
    CSRRC,
    CSRR, // read-only CSR operation
    CSRW // write-only CSR operation
} SystemInst deriving (Bits, Eq, FShow);

// LdStInst and AmoInst are defined in Types.bsv
typedef union tagged {
    AluInst     Alu;
    BrFunc      Br;
    RVMemInst   Mem;
    MulDivInst  MulDiv;
    FpuInst     Fpu;
    Fence       Fence;
    SystemInst  System;
    // void        Other; // Should be none
} ExecFunc deriving (Bits, Eq, FShow);

typedef enum {
    Gpr = 1'b0,
    Fpu = 1'b1
} RegType deriving (Bits, Eq, FShow);

typedef enum {
    None, I, S, SB, U, UJ, Z
} ImmType deriving (Bits, Eq, FShow);

typedef struct {
    ExecFunc        execFunc;
    ImmType         imm;
    Maybe#(RegType) rs1;
    Maybe#(RegType) rs2;
    Maybe#(RegType) rs3;
    Maybe#(RegType) dst;
    Instruction     inst;
} RVDecodedInst deriving (Bits, Eq, FShow);

// Rounding Modes
typedef enum {
    RNE  = 3'b000,
    RTZ  = 3'b001,
    RDN  = 3'b010,
    RUP  = 3'b011,
    RMM  = 3'b100,
    RDyn = 3'b111
} RVRoundMode deriving (Bits, Eq, FShow);

typedef enum {
    InstAddrMisaligned  = 4'd0,
    InstAccessFault     = 4'd1,
    IllegalInst         = 4'd2,
    Breakpoint          = 4'd3,
    LoadAddrMisaligned  = 4'd4,
    LoadAccessFault     = 4'd5,
    StoreAddrMisaligned = 4'd6,
    StoreAccessFault    = 4'd7,
    EnvCallU            = 4'd8,
    EnvCallS            = 4'd9,
    EnvCallH            = 4'd10,
    EnvCallM            = 4'd11,
    IllegalException    = 4'd15 // to get a 4-bit implementation
} ExceptionCause deriving (Bits, Eq, FShow);

typedef enum {
    USoftwareInterrupt  = 4'd0,
    SSoftwareInterrupt  = 4'd1,
    HSoftwareInterrupt  = 4'd2,
    MSoftwareInterrupt  = 4'd3,
    UTimerInterrupt     = 4'd4,
    STimerInterrupt     = 4'd5,
    HTimerInterrupt     = 4'd6,
    MTimerInterrupt     = 4'd7,
    UExternalInterrupt  = 4'd8,
    SExternalInterrupt  = 4'd9,
    HExternalInterrupt  = 4'd10,
    MExternalInterrupt  = 4'd11,
    IllegalInterrupt    = 4'd15 // to get 4-bit implementation
} InterruptCause deriving (Bits, Eq, FShow);

// Traps are either an exception or an interrupt
typedef union tagged {
    ExceptionCause Exception;
    InterruptCause Interrupt;
} TrapCause deriving (Bits, Eq, FShow);

function Data toCauseCSR(TrapCause x);
    case (x) matches
        tagged Exception .cause:
            return {0, pack(cause)};
        tagged Interrupt .cause:
            return {1'b1, 0, pack(cause)};
        default:
            return 0;
    endcase
endfunction

typedef struct {
    Bit#(2) prv;
    Bit#(3) frm;
    Bool f_enabled;
    Bool x_enabled;
} CsrState deriving (Bits, Eq, FShow);

typedef struct {
    Addr  pc;
    Addr  nextPc;
    Bool  taken;
    Bool  mispredict;
} Redirect deriving (Bits, Eq, FShow);

typedef struct {
    Addr pc;
    Addr nextPc;
    Bool taken;
    Bool mispredict;
} ControlFlow deriving (Bits, Eq, FShow);

// typedef struct {
//   IType         iType;
//   ExecFunc      execFunc;
//   Maybe#(CSR)   csr;
//   Maybe#(Data)  imm;
// } DecodedInst deriving (Bits, Eq, FShow);

typedef struct {
    Bit#(xlen)              data;
    Bit#(5)                 fflags;
    Bit#(xlen)              vaddr;
    Bit#(xlen)              paddr;
    ControlFlow             controlFlow;
    Maybe#(ExceptionCause)  cause;
} FullResult#(numeric type xlen) deriving (Bits, Eq, FShow);

typeclass FullResultSubset#(type t, numeric type xlen);
    function FullResult#(xlen) updateFullResult(t x, FullResult#(xlen) full_result);
endtypeclass
instance DefaultValue#(ControlFlow);
    function ControlFlow defaultValue = ControlFlow{pc: 0,
                                                    nextPc: 0,
                                                    taken: False,
                                                    mispredict: False};
endinstance
instance DefaultValue#(FullResult#(xlen));
    function FullResult#(xlen) defaultValue = FullResult{  data: 0,
                                                    fflags: 0,
                                                    vaddr: 0,
                                                    paddr: 0,
                                                    controlFlow: defaultValue,
                                                    cause: tagged Invalid};
endinstance
function FullResult#(xlen) toFullResult(t x) provisos (FullResultSubset#(t, xlen));
    return updateFullResult(x, defaultValue);
endfunction

typedef struct {
    Bit#(2)    prv;
    Asid       asid;
    Bit#(5)    vm;
    Bool       mxr;
    Bool       pum;
    Bit#(xlen) base;
    Bit#(xlen) bound;
} VMInfo#(numeric type xlen) deriving (Bits, Eq, FShow);
instance DefaultValue#(VMInfo#(xlen));
    function VMInfo#(xlen) defaultValue = VMInfo {prv: prvM, asid: 0, vm: 0, mxr: False, pum: False, base: 0, bound: 0};
endinstance

// Instead of making PMAs generic (like a massive struct), we are adding named
// PMAs as needed. Currently these PMAs are defined by device
typedef enum {
    MainMemory, // Cacheable, R, W, and X, all AMO supported
    IORom,      // Cacheable, R and X only, no AMO
    IODevice,   // R and W, but no AMO
    IOEmpty     // no R, W, or X
} PMA deriving (Bits, Eq, FShow);

function Bool isCacheable(PMA pma);
    return (case (pma)
                MainMemory, IORom: True;
                default: False;
            endcase);
endfunction

Bit#(2) prvU = 0;
Bit#(2) prvS = 1;
Bit#(2) prvH = 2;
Bit#(2) prvM = 3;

typedef struct{
    RVMemOp op;
    Addr    addr;
} TlbReq deriving (Eq, Bits, FShow);
typedef Tuple2#(Addr, Maybe#(ExceptionCause)) TlbResp;

// Virtual Memory Types
Bit#(5) vmMbare = 0;
Bit#(5) vmMbb   = 1;
Bit#(5) vmMbbid = 2;
Bit#(5) vmSv32  = 8;
Bit#(5) vmSv39  = 9;
Bit#(5) vmSv48  = 10;
Bit#(5) vmSv57  = 11;
Bit#(5) vmSv64  = 12;

typedef struct {
    Bit#(16) reserved;
    Bit#(20) ppn2;
    Bit#(9) ppn1;
    Bit#(9) ppn0;
    Bit#(2) reserved_sw;
    Bool d;
    Bool a;
    Bool g;
    Bool u;
    Bool x;
    Bool w;
    Bool r;
    Bool valid;
} PTE_Sv39 deriving (Eq, FShow); // Has custom Bits implementation
instance Bits#(PTE_Sv39, 64);
    function Bit#(64) pack(PTE_Sv39 x);
        return {x.reserved, x.ppn2, x.ppn1, x.ppn0, x.reserved_sw, pack(x.d), pack(x.a), pack(x.g), pack(x.u), pack(x.x), pack(x.w), pack(x.r), pack(x.valid)};
    endfunction
    function PTE_Sv39 unpack(Bit#(64) x);
        return (PTE_Sv39 {
                reserved:     x[63:48],
                ppn2:         x[47:28],
                ppn1:         x[27:19],
                ppn0:         x[18:10],
                reserved_sw:  x[9:8],
                d:            unpack(x[7]),
                a:            unpack(x[6]),
                g:            unpack(x[5]),
                u:            unpack(x[4]),
                x:            unpack(x[3]),
                w:            unpack(x[2]),
                r:            unpack(x[1]),
                valid:        unpack(x[0])
            });
    endfunction
endinstance
function Bool isLegalPTE(PTE_Sv39 pte);
    return pte.valid && !(pte.w && !(pte.r));
endfunction
function Bool isLeafPTE(PTE_Sv39 pte);
    return pte.valid && (pte.r || pte.w || pte.x);
endfunction
