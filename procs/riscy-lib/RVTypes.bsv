
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
//typedef Bit#(DataSz) Data;
//typedef Bit#(TDiv#(DataSz,8)) DataByteEn;
//typedef Bit#(TLog#(TDiv#(DataSz,8))) DataByteSel; // Type of byte select value for Data
typedef Bit#(32) Data;
`ifdef BSVTOKAMI
(* nogen *)
`endif
typedef Bit#(4) DataByteEn;
`ifdef BSVTOKAMI
(* nogen *)
`endif
typedef Bit#(2) DataByteSel; // Type of byte select value for Data

typedef 512 CacheLineSz; // Used in DCache.bsv

typedef 32 InstSz;
typedef Bit#(InstSz) Instruction;

// Virtual address
typedef XLEN AddrSz;
`ifdef BSVTOKAMI
(* nogen *)
`endif
typedef Bit#(AddrSz) Addr;

// Physical address
typedef 64 PAddrSz;
`ifdef BSVTOKAMI
(* nogen *)
`endif
typedef Bit#(PAddrSz) PAddr;

`ifdef CONFIG_RV64
typedef 26 AsidSz;
`endif
`ifdef CONFIG_RV32
typedef 10 AsidSz;
`endif
typedef Bit#(AsidSz) Asid;

// Rounding Modes
typedef enum {
    RNE  = 3'b000,
    RTZ  = 3'b001,
    RDN  = 3'b010,
    RUP  = 3'b011,
    RMM  = 3'b100,
    RDyn = 3'b111
} RVRoundMode deriving (Eq, FShow);

interface Pack#(type t, numeric type sz);
   method t unpack(Bit#(sz) v);
   method Bit#(sz) pack(t v);
endinterface

module mkPackRVRoundMode(Pack#(RVRoundMode,3));
   method RVRoundMode unpack(Bit#(3) v);
      case (v) matches
	 3'b000: return RNE;
	 3'b001: return RTZ;
	 3'b010: return RDN;
	 3'b011: return RUP;
	 3'b100: return RMM;
	 3'b111: return RDyn;
	 default: return RDyn;
      endcase
   endmethod
   method Bit#(3) pack(RVRoundMode v);
      case (v) matches
	 tagged RNE: return 3'b000;
	 tagged RTZ: return 3'b001;
	 tagged RDN: return 3'b010;
	 tagged RUP: return 3'b011;
	 tagged RMM: return 3'b100;
	 tagged RDyn: return 3'b111;
	 default: return 3'b111;
	 endcase
   endmethod
endmodule

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
} Opcode deriving (Eq, FShow);

module mkPackOpcode(Pack#(Opcode,7));
   method Opcode unpack(Bit#(7) v);
      case (v) matches
	 7'b0000011: return Load;
	 7'b0000111: return LoadFp;
	 7'b0001111: return MiscMem;
	 7'b0010011: return OpImm;
	 7'b0010111: return Auipc;
	 7'b0011011: return OpImm32;
	 7'b0100011: return Store;
	 7'b0100111: return StoreFp;
	 7'b0101111: return Amo;
	 7'b0110011: return Op;
	 7'b0110111: return Lui;
	 7'b0111011: return Op32;
	 7'b1000011: return Fmadd;
	 7'b1000111: return Fmsub;
	 7'b1001011: return Fnmsub;
	 7'b1001111: return Fnmadd;
	 7'b1010011: return OpFp;
	 7'b1100011: return Branch;
	 7'b1100111: return Jalr;
	 7'b1101111: return Jal;
	 7'b1110011: return System;
	 default: return System;
      endcase
   endmethod
   method Bit#(7) pack(Opcode v);
      case (v) matches
	 tagged Load: return 7'b0000011;
	 tagged LoadFp: return 7'b0000111;
	 tagged MiscMem: return 7'b0001111;
	 tagged OpImm: return 7'b0010011;
	 tagged Auipc: return 7'b0010111;
	 tagged OpImm32: return 7'b0011011;
	 tagged Store: return 7'b0100011;
	 tagged StoreFp: return 7'b0100111;
	 tagged Amo: return 7'b0101111;
	 tagged Op: return 7'b0110011;
	 tagged Lui: return 7'b0110111;
	 tagged Op32: return 7'b0111011;
	 tagged Fmadd: return 7'b1000011;
	 tagged Fmsub: return 7'b1000111;
	 tagged Fnmsub: return 7'b1001011;
	 tagged Fnmadd: return 7'b1001111;
	 tagged OpFp: return 7'b1010011;
	 tagged Branch: return 7'b1100011;
	 tagged Jalr: return 7'b1100111;
	 tagged Jal: return 7'b1101111;
	 tagged System: return 7'b1110011;
	 default: return 7'b0000000;
      endcase
   endmethod
endmodule

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
} CSR deriving (Eq, FShow);

module mkPackCSR(Pack#(CSR,12));
   method CSR unpack(Bit#(12) v);
      case (v) matches
	 12'h000: return CSRustatus;
	 12'h004: return CSRuie;
	 12'h005: return CSRutvec;
	 12'h040: return CSRuscratch;
	 12'h041: return CSRuepc;
	 12'h042: return CSRucause;
	 12'h043: return CSRubadaddr;
	 12'h044: return CSRuip;
	 12'h001: return CSRfflags;
	 12'h002: return CSRfrm;
	 12'h003: return CSRfcsr;
	 12'hc00: return CSRcycle;
	 12'hc01: return CSRtime;
	 12'hc02: return CSRinstret;
	 12'hc80: return CSRcycleh;
	 12'hc81: return CSRtimeh;
	 12'hc82: return CSRinstreth;
	 12'h100: return CSRsstatus;
	 12'h102: return CSRsedeleg;
	 12'h103: return CSRsideleg;
	 12'h104: return CSRsie;
	 12'h105: return CSRstvec;
	 12'h140: return CSRsscratch;
	 12'h141: return CSRsepc;
	 12'h142: return CSRscause;
	 12'h143: return CSRsbadaddr;
	 12'h144: return CSRsip;
	 12'h180: return CSRsptbr;
	 12'hd00: return CSRscycle;
	 12'hd01: return CSRstime;
	 12'hd02: return CSRsinstret;
	 12'hd80: return CSRscycleh;
	 12'hd81: return CSRstimeh;
	 12'hd82: return CSRsinstreth;
	 12'h200: return CSRhstatus;
	 12'h202: return CSRhedeleg;
	 12'h203: return CSRhideleg;
	 12'h204: return CSRhie;
	 12'h205: return CSRhtvec;
	 12'h240: return CSRhscratch;
	 12'h241: return CSRhepc;
	 12'h242: return CSRhcause;
	 12'h243: return CSRhbadaddr;
	 12'he00: return CSRhcycle;
	 12'he01: return CSRhtime;
	 12'he02: return CSRhinstret;
	 12'he80: return CSRhcycleh;
	 12'he81: return CSRhtimeh;
	 12'he82: return CSRhinstreth;
	 12'hf10: return CSRmisa;
	 12'hf11: return CSRmvendorid;
	 12'hf12: return CSRmarchid;
	 12'hf13: return CSRmimpid;
	 12'hf14: return CSRmhartid;
	 12'h300: return CSRmstatus;
	 12'h302: return CSRmedeleg;
	 12'h303: return CSRmideleg;
	 12'h304: return CSRmie;
	 12'h305: return CSRmtvec;
	 12'h340: return CSRmscratch;
	 12'h341: return CSRmepc;
	 12'h342: return CSRmcause;
	 12'h343: return CSRmbadaddr;
	 12'h344: return CSRmip;
	 12'h380: return CSRmbase;
	 12'h381: return CSRmbound;
	 12'h382: return CSRmibase;
	 12'h383: return CSRmibound;
	 12'h384: return CSRmdbase;
	 12'h385: return CSRmdbound;
	 12'hf00: return CSRmcycle;
	 12'hf01: return CSRmtime;
	 12'hf02: return CSRminstret;
	 12'hf80: return CSRmcycleh;
	 12'hf81: return CSRmtimeh;
	 12'hf82: return CSRminstreth;
	 12'h310: return CSRmucounteren;
	 12'h311: return CSRmscounteren;
	 12'h312: return CSRmhcounteren;
	 12'h700: return CSRmucycle_delta;
	 12'h701: return CSRmutime_delta;
	 12'h702: return CSRmuinstret_delta;
	 12'h704: return CSRmscycle_delta;
	 12'h705: return CSRmstime_delta;
	 12'h706: return CSRmsinstret_delta;
	 12'h708: return CSRmhcycle_delta;
	 12'h709: return CSRmhtime_delta;
	 12'h70a: return CSRmhinstret_delta;
	 12'h780: return CSRmucycle_deltah;
	 12'h781: return CSRmutime_deltah;
	 12'h782: return CSRmuinstret_deltah;
	 12'h784: return CSRmscycle_deltah;
	 12'h785: return CSRmstime_deltah;
	 12'h786: return CSRmsinstret_deltah;
	 12'h788: return CSRmhcycle_deltah;
	 12'h789: return CSRmhtime_deltah;
	 12'h78a: return CSRmhinstret_deltah;
	 default: return CSRmhinstret_deltah;
      endcase
   endmethod
   method Bit#(12) pack(CSR v);
   case (v) matches
      tagged CSRustatus: return 12'h000;
      tagged CSRuie: return 12'h004;
      tagged CSRutvec: return 12'h005;
      tagged CSRuscratch: return 12'h040;
      tagged CSRuepc: return 12'h041;
      tagged CSRucause: return 12'h042;
      tagged CSRubadaddr: return 12'h043;
      tagged CSRuip: return 12'h044;
      tagged CSRfflags: return 12'h001;
      tagged CSRfrm: return 12'h002;
      tagged CSRfcsr: return 12'h003;
      tagged CSRcycle: return 12'hc00;
      tagged CSRtime: return 12'hc01;
      tagged CSRinstret: return 12'hc02;
      tagged CSRcycleh: return 12'hc80;
      tagged CSRtimeh: return 12'hc81;
      tagged CSRinstreth: return 12'hc82;
      tagged CSRsstatus: return 12'h100;
      tagged CSRsedeleg: return 12'h102;
      tagged CSRsideleg: return 12'h103;
      tagged CSRsie: return 12'h104;
      tagged CSRstvec: return 12'h105;
      tagged CSRsscratch: return 12'h140;
      tagged CSRsepc: return 12'h141;
      tagged CSRscause: return 12'h142;
      tagged CSRsbadaddr: return 12'h143;
      tagged CSRsip: return 12'h144;
      tagged CSRsptbr: return 12'h180;
      tagged CSRscycle: return 12'hd00;
      tagged CSRstime: return 12'hd01;
      tagged CSRsinstret: return 12'hd02;
      tagged CSRscycleh: return 12'hd80;
      tagged CSRstimeh: return 12'hd81;
      tagged CSRsinstreth: return 12'hd82;
      tagged CSRhstatus: return 12'h200;
      tagged CSRhedeleg: return 12'h202;
      tagged CSRhideleg: return 12'h203;
      tagged CSRhie: return 12'h204;
      tagged CSRhtvec: return 12'h205;
      tagged CSRhscratch: return 12'h240;
      tagged CSRhepc: return 12'h241;
      tagged CSRhcause: return 12'h242;
      tagged CSRhbadaddr: return 12'h243;
      tagged CSRhcycle: return 12'he00;
      tagged CSRhtime: return 12'he01;
      tagged CSRhinstret: return 12'he02;
      tagged CSRhcycleh: return 12'he80;
      tagged CSRhtimeh: return 12'he81;
      tagged CSRhinstreth: return 12'he82;
      tagged CSRmisa: return 12'hf10;
      tagged CSRmvendorid: return 12'hf11;
      tagged CSRmarchid: return 12'hf12;
      tagged CSRmimpid: return 12'hf13;
      tagged CSRmhartid: return 12'hf14;
      tagged CSRmstatus: return 12'h300;
      tagged CSRmedeleg: return 12'h302;
      tagged CSRmideleg: return 12'h303;
      tagged CSRmie: return 12'h304;
      tagged CSRmtvec: return 12'h305;
      tagged CSRmscratch: return 12'h340;
      tagged CSRmepc: return 12'h341;
      tagged CSRmcause: return 12'h342;
      tagged CSRmbadaddr: return 12'h343;
      tagged CSRmip: return 12'h344;
      tagged CSRmbase: return 12'h380;
      tagged CSRmbound: return 12'h381;
      tagged CSRmibase: return 12'h382;
      tagged CSRmibound: return 12'h383;
      tagged CSRmdbase: return 12'h384;
      tagged CSRmdbound: return 12'h385;
      tagged CSRmcycle: return 12'hf00;
      tagged CSRmtime: return 12'hf01;
      tagged CSRminstret: return 12'hf02;
      tagged CSRmcycleh: return 12'hf80;
      tagged CSRmtimeh: return 12'hf81;
      tagged CSRminstreth: return 12'hf82;
      tagged CSRmucounteren: return 12'h310;
      tagged CSRmscounteren: return 12'h311;
      tagged CSRmhcounteren: return 12'h312;
      tagged CSRmucycle_delta: return 12'h700;
      tagged CSRmutime_delta: return 12'h701;
      tagged CSRmuinstret_delta: return 12'h702;
      tagged CSRmscycle_delta: return 12'h704;
      tagged CSRmstime_delta: return 12'h705;
      tagged CSRmsinstret_delta: return 12'h706;
      tagged CSRmhcycle_delta: return 12'h708;
      tagged CSRmhtime_delta: return 12'h709;
      tagged CSRmhinstret_delta: return 12'h70a;
      tagged CSRmucycle_deltah: return 12'h780;
      tagged CSRmutime_deltah: return 12'h781;
      tagged CSRmuinstret_deltah: return 12'h782;
      tagged CSRmscycle_deltah: return 12'h784;
      tagged CSRmstime_deltah: return 12'h785;
      tagged CSRmsinstret_deltah: return 12'h786;
      tagged CSRmhcycle_deltah: return 12'h788;
      tagged CSRmhtime_deltah: return 12'h789;
      tagged CSRmhinstret_deltah: return 12'h78a;
      default: return 12'h0;
      endcase
   endmethod
endmodule

// WARNING: Don't try updating fields when using this type.
typedef struct {
    // full instruction
    Bit#(32) inst;
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
//    Opcode      opcode; // Bit#(7)
    Bit#(12)    csrAddr;
//    CSR         csr;
} InstructionFields;
// XXX: probably don't want a Bits instance for this type
`ifdef UNUSED
instance Bits#(InstructionFields, 32);
    function Bit#(32) pack(InstructionFields x);
        return x.inst;
    endfunction
   //function InstructionFields unpack(Bit#(32) x);
   //     return getInstFields(x);
   // endfunction
endinstance
`endif

// XXX: ... or an Eq instance
`ifdef UNUSED
instance Eq#(InstructionFields);
    function Bool \== (InstructionFields a, InstructionFields b);
        return a.inst == b.inst;
    endfunction
endinstance
`endif
// XXX: ... or an FShow instance
`ifdef UNUSED
instance FShow#(InstructionFields);
    function Fmt fshow(InstructionFields x);
        return $format("{InstructionFields: 0x%08x}",x);
    endfunction
endinstance
`endif

typedef struct {
Bit#(32) inst;
Bit#(5) rd;
CSR csr;
} TestStruct;

interface GetTestStruct;
   method TestStruct getTestStruct(Bit#(32) x);
endinterface

module mkTestStruct(GetTestStruct);
   Pack#(CSR,12) packCSR <- mkPackCSR();
   method TestStruct getTestStruct(Bit#(32) x);
      CSR xcsr = packCSR.unpack(x[31:20]);   
      TestStruct ts = TestStruct { inst: x, rd: x[4:0], csr: xcsr };
      return ts;
   endmethod
endmodule

// XXX: we probably just want this function
interface GetInstFields;
   method InstructionFields getInstFields(Instruction x);
endinterface

module mkGetInstFields(GetInstFields);
   Pack#(RVRoundMode,3) packRVRoundMode <- mkPackRVRoundMode();
   Pack#(Opcode,7) packOpcode <- mkPackOpcode();
   Pack#(CSR,12) packCSR <- mkPackCSR();
   method InstructionFields getInstFields(Instruction x);
      RVRoundMode xroundMode = packRVRoundMode.unpack(x[14:12]);
      Opcode xopcode = packOpcode.unpack(x[6:0]);   
      CSR xcsr = packCSR.unpack(x[31:20]);
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
            rm:         xroundMode,
//            opcode:     xopcode,
            csrAddr:    x[31:20] //,
//            csr:        xcsr
        };
   endmethod
endmodule

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

interface ToDataByteEn#(numeric type n);
    method Bit#(n) toDataByteEn(RVMemSize size);
endinterface

// RV32 Instance
module mkToDataByteEn4(ToDataByteEn#(4));
    method Bit#(4) toDataByteEn(RVMemSize size);
        return (case (size)
                B:       4'b0001;
                H:       4'b0011;
                W:       4'b1111;
                // D is illegal
                default: 4'b0000;
            endcase);
    endmethod
endmodule

// RV64 Instance
module mkToDataByteEn8(ToDataByteEn#(8));
    method Bit#(8) toDataByteEn(RVMemSize size);
        return (case (size)
                B:       8'b00000001;
                H:       8'b00000011;
                W:       8'b00001111;
                D:       8'b11111111;
                default: 8'b00000000;
            endcase);
    endmethod
endmodule

interface ToPermutedDataByteEn;
   method DataByteEn toPermutedDataByteEn(RVMemSize size, DataByteSel addrLSB);
endinterface

module mkToPermutedDataByteEn(ToPermutedDataByteEn);
   //FIXME hardcoded
   ToDataByteEn#(4) tdbe <- mkToDataByteEn4();
   method DataByteEn toPermutedDataByteEn(RVMemSize size, DataByteSel addrLSB);
      return tdbe.toDataByteEn(size) << addrLSB;
   endmethod
endmodule

typedef union tagged {
    RVMemOp MemOp;
    RVAmoOp AmoOp;
} RVMemAmoOp deriving (Bits, Eq, FShow);

typedef struct {
    RVMemAmoOp  op;
    RVMemSize   size;
    Bool        isUnsigned;
} RVMemInst deriving (Bits, Eq, FShow);

interface IsMemOp#(type t);
    method Bool isLoad(t x);
    method Bool isStore(t x);
    method Bool isAmo(t x);
    method Bool getsReadPermission(t x);
    method Bool getsWritePermission(t x);
    method Bool getsResponse(t x);
endinterface

module mkIsMemOpRVMemOp(IsMemOp#(RVMemOp));
    method Bool isLoad(RVMemOp x);
        return ((x == Ld) || (x == Lr));
    endmethod
    method Bool isStore(RVMemOp x);
        return ((x == St) || (x == Sc));
    endmethod
    method Bool isAmo(RVMemOp x);
        return False;
    endmethod
    method Bool getsReadPermission(RVMemOp x);
        return ((x == Ld) || (x == PrefetchForLd));
    endmethod
    method Bool getsWritePermission(RVMemOp x);
        return ((x == St) || (x == Sc) || (x == Lr) || (x == PrefetchForSt));
    endmethod
    method Bool getsResponse(RVMemOp x);
        return ((x == Ld) || (x == Lr) || (x == Sc));
    endmethod
endmodule

module mkIsMemOpRVAmoOp(IsMemOp#(RVAmoOp));
    method Bool isLoad(RVAmoOp x);
        return False;
    endmethod
    method Bool isStore(RVAmoOp x);
        return False;
    endmethod
    method Bool isAmo(RVAmoOp x);
        return True;
    endmethod
    method Bool getsReadPermission(RVAmoOp x);
        return False;
    endmethod
    method Bool getsWritePermission(RVAmoOp x);
        return True;
    endmethod
    method Bool getsResponse(RVAmoOp x);
        return True;
    endmethod
endmodule

module mkIsMemOpRVMemAmoOp(IsMemOp#(RVMemAmoOp));
   IsMemOp#(RVMemOp) isMemOpMem <- mkIsMemOpRVMemOp();
   IsMemOp#(RVAmoOp) isMemOpAmo <- mkIsMemOpRVAmoOp();
    method Bool isLoad(RVMemAmoOp x);
        return (case (x) matches
                tagged MemOp .mem: isMemOpMem.isLoad(mem);
                tagged AmoOp .amo: isMemOpAmo.isLoad(amo);
            endcase);
    endmethod
    method Bool isStore(RVMemAmoOp x);
        return (case (x) matches
                tagged MemOp .mem: isMemOpMem.isStore(mem);
                tagged AmoOp .amo: isMemOpAmo.isStore(amo);
            endcase);
    endmethod
    method Bool isAmo(RVMemAmoOp x);
        return (case (x) matches
                tagged MemOp .mem: isMemOpMem.isAmo(mem);
                tagged AmoOp .amo: isMemOpAmo.isAmo(amo);
            endcase);
    endmethod
    method Bool getsReadPermission(RVMemAmoOp x);
        return (case (x) matches
                tagged MemOp .mem: isMemOpMem.getsReadPermission(mem);
                tagged AmoOp .amo: isMemOpAmo.getsReadPermission(amo);
            endcase);
    endmethod
    method Bool getsWritePermission(RVMemAmoOp x);
        return (case (x) matches
                tagged MemOp .mem: isMemOpMem.getsWritePermission(mem);
                tagged AmoOp .amo: isMemOpAmo.getsWritePermission(amo);
            endcase);
    endmethod
    method Bool getsResponse(RVMemAmoOp x);
        return (case (x) matches
                tagged MemOp .mem: isMemOpMem.getsResponse(mem);
                tagged AmoOp .amo: isMemOpAmo.getsResponse(amo);
            endcase);
    endmethod
endmodule

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

`ifdef BSVTOKAMI
(* nogen *)
`endif
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

interface GetMISA;
   method Data getMISA(RiscVISASubset isa);
endinterface

module mkGetMISA(GetMISA);
method Data getMISA(RiscVISASubset isa);
    // include I by default
    Data misa = {2'b00, 4'd0, 26'b00000000000000000100000000};
    if (isa.rv64) begin
        // rv64
        misa = misa | {2'b10, 4'd0, 26'b00000000000000000000000000};
    end else begin
        // rv32
        misa = misa | {2'b01, 4'd0, 26'b00000000000000000000000000};
    end
    if (isa.s) misa = misa | {2'b00, 4'd0,  26'b00000001000000000000000000};
    if (isa.u) misa = misa | {2'b00, 4'd0,  26'b00000100000000000000000000};
    if (isa.m) misa = misa | {2'b00, 4'd0,  26'b00000000000001000000000000};
    if (isa.a) misa = misa | {2'b00, 4'd0,  26'b00000000000000000000000001};
    if (isa.f) misa = misa | {2'b00, 4'd0,  26'b00000000000000000000100000};
    if (isa.d) misa = misa | {2'b00, 4'd0,  26'b00000000000000000000001000};
    return misa;
endmethod
endmodule

typedef Bit#(5) RegIndex;
typedef union tagged {
    RegIndex Gpr;
    RegIndex Fpu;
} FullRegIndex deriving (Bits, Eq, FShow, Bounded);

interface ToFullRegIndex;
   method Maybe#(FullRegIndex) toFullRegIndex(Maybe#(RegType) rType, RegIndex index);
endinterface

module mkToFullRegIndex(ToFullRegIndex);
method Maybe#(FullRegIndex) toFullRegIndex(Maybe#(RegType) rType, RegIndex index);
    return (case (rType)
            tagged Valid RtGpr: tagged Valid tagged Gpr index;
            tagged Valid RtFpu: tagged Valid tagged Fpu index;
            default: tagged Invalid;
        endcase);
endmethod
endmodule

typedef 64 NumArchReg;

`ifdef PHYS_REG_COUNT
typedef `PHYS_REG_COUNT NumPhyReg;
`else
typedef NumArchReg NumPhyReg;
`endif

interface HasCSRPermission;
   method Bool hasCSRPermission(CSR csr, Bit#(2) prv, Bool write);
endinterface

module mkHasCSRPermission(HasCSRPermission);
   Pack#(CSR,12) packCSR <- mkPackCSR();
   method Bool hasCSRPermission(CSR csr, Bit#(2) prv, Bool write);
    Bit#(12) csr_index = packCSR.pack(csr);
    return ((prv >= csr_index[9:8]) && (!write || (csr_index[11:10] != 2'b11)));
   endmethod
endmodule

// These enumeration values match the bit values for funct3
typedef enum {
    BrEq   = 3'b000,
    BrNeq  = 3'b001,
    BrJal  = 3'b010,
    BrJalr = 3'b011,
    BrLt   = 3'b100,
    BrGe   = 3'b101,
    BrLtu  = 3'b110,
    BrGeu  = 3'b111
} BrFunc deriving (Bits, Eq, FShow);

// This encoding tries to match {inst[30], funct3}
typedef enum {
    AluAdd  = 4'b0000,
    AluSll  = 4'b0001,
    AluSlt  = 4'b0010,
    AluSltu = 4'b0011,
    AluXor  = 4'b0100,
    AluSrl  = 4'b0101,
    AluOr   = 4'b0110,
    AluAnd  = 4'b0111,
    AluSub  = 4'b1000,
    AluSra  = 4'b1101,
    // These don't follow the {inst[30], funct3} encoding since they use
    // different opcodes
    // TODO: check the values of these instructions
    // XXX: Should these not specify a value?
    AluAuipc = 5'b10000,
    AluLui   = 5'b11000
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
    AluInst     EF_Alu;
    BrFunc      EF_Br;
    RVMemInst   EF_Mem;
    MulDivInst  EF_MulDiv;
    FpuInst     EF_Fpu;
    Fence       EF_Fence;
    SystemInst  EF_System;
    // void        EF_Other; // Should be none
} ExecFunc deriving (Bits, Eq, FShow);

typedef enum {
    RtGpr = 1'b0,
    RtFpu = 1'b1
} RegType deriving (Bits, Eq, FShow);

typedef enum {
    ItNone, ItI, ItS, ItSB, ItU, ItUJ, ItZ
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
    ExceptionCause TcException;
    InterruptCause TcInterrupt;
} TrapCause deriving (Bits, Eq, FShow);

interface ToCauseCSR;
   method Data toCauseCSR(TrapCause x);
endinterface

module mkToCauseCSR(ToCauseCSR);
method Data toCauseCSR(TrapCause x);
    case (x) matches
        tagged TcException .cause: begin
	   Bit#(4) pcause = pack(cause);
            return {28'd0, pcause};
	end
        tagged TcInterrupt .cause: begin
	   Bit#(4) pcause = pack(cause);
            return {1'b1, 27'd0, pcause};
	   end
        default:
            return 0;
    endcase
endmethod
endmodule

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

interface FullResultSubset#(type t, numeric type xlen);
    method FullResult#(xlen) updateFullResult(t x, FullResult#(xlen) full_result);
endinterface

`ifdef BSVTOKAMI
(* nogen *)
`endif
instance DefaultValue#(ControlFlow);
    function ControlFlow defaultValue = ControlFlow{pc: 0,
                                                    nextPc: 0,
                                                    taken: False,
                                                    mispredict: False};
endinstance
`ifdef BSVTOKAMI
(* nogen *)
`endif
instance DefaultValue#(FullResult#(xlen));
    function FullResult#(xlen) defaultValue = FullResult{  data: 0,
                                                    fflags: 0,
                                                    vaddr: 0,
                                                    paddr: 0,
                                                    controlFlow: defaultValue,
                                                    cause: tagged Invalid};
endinstance

`ifdef UNUSED
module mkToFullResult(ToFullResult);
   method FullResult#(xlen) toFullResult(t x) provisos (FullResultSubset#(t, xlen));
    return updateFullResult(x, defaultValue);
   endmethod
endmodule
`endif

typedef struct {
    Bit#(2)    prv;
    Asid       asid;
    Bit#(5)    vm;
    Bool       mxr;
    Bool       pum;
    Bit#(xlen) base;
    Bit#(xlen) bound;
} VMInfo#(numeric type xlen) deriving (Bits, Eq, FShow);
`ifdef BSVTOKAMI
(* nogen *)
`endif
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

interface IsCacheable;
method Bool isCacheable(PMA pma);
endinterface

module mkIsCacheable(IsCacheable);
method Bool isCacheable(PMA pma);
    return (case (pma)
                MainMemory, IORom: True;
                default: False;
            endcase);
endmethod
endmodule

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

`ifdef BSVTOKAMI
(* nogen *)
`endif
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
`ifdef BSVTOKAMI
(* nogen *)
`endif
function Bool isLegalPTE(PTE_Sv39 pte);
    return pte.valid && !(pte.w && !(pte.r));
endfunction
`ifdef BSVTOKAMI
(* nogen *)
`endif

function Bool isLeafPTE(PTE_Sv39 pte);
    return pte.valid && (pte.r || pte.w || pte.x);
endfunction
