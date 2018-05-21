Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import FShow.
Require Import Vector.
Definition XLEN := 32.

Definition DataSz := XLEN.

Definition Data := (word 32).

Definition DataByteEn := (word 4).

Definition DataByteSel := (word 2).

Definition CacheLineSz := 512.

Definition InstSz := 32.

Definition Instruction := (Bit InstSz).

Definition AddrSz := XLEN.

Definition Addr := (word AddrSz).

Definition PAddrSz := 64.

Definition PAddr := (word PAddrSz).

Definition AsidSz := 10.

Definition Asid := (word AsidSz).

Notation RVRoundModeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVRoundMode : Kind := (Struct RVRoundModeFields).
Notation RNE := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation RTZ := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation RDN := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation RUP := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation RMM := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation RDyn := (STRUCT { "$tag" ::= $7 })%kami_expr.
Definition OpcodeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition Opcode : Kind := (Struct OpcodeFields).
Notation Load := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation LoadFp := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation MiscMem := (STRUCT { "$tag" ::= $15 })%kami_expr.
Notation OpImm := (STRUCT { "$tag" ::= $19 })%kami_expr.
Notation Auipc := (STRUCT { "$tag" ::= $23 })%kami_expr.
Notation OpImm32 := (STRUCT { "$tag" ::= $27 })%kami_expr.
Notation Store := (STRUCT { "$tag" ::= $35 })%kami_expr.
Notation StoreFp := (STRUCT { "$tag" ::= $39 })%kami_expr.
Notation Amo := (STRUCT { "$tag" ::= $47 })%kami_expr.
Notation Op := (STRUCT { "$tag" ::= $51 })%kami_expr.
Notation Lui := (STRUCT { "$tag" ::= $55 })%kami_expr.
Notation Op32 := (STRUCT { "$tag" ::= $59 })%kami_expr.
Notation Fmadd := (STRUCT { "$tag" ::= $67 })%kami_expr.
Notation Fmsub := (STRUCT { "$tag" ::= $71 })%kami_expr.
Notation Fnmsub := (STRUCT { "$tag" ::= $75 })%kami_expr.
Notation Fnmadd := (STRUCT { "$tag" ::= $79 })%kami_expr.
Notation OpFp := (STRUCT { "$tag" ::= $83 })%kami_expr.
Notation Branch := (STRUCT { "$tag" ::= $99 })%kami_expr.
Notation Jalr := (STRUCT { "$tag" ::= $103 })%kami_expr.
Notation Jal := (STRUCT { "$tag" ::= $111 })%kami_expr.
Notation System := (STRUCT { "$tag" ::= $115 })%kami_expr.
Definition CSRFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition CSR : Kind := (Struct CSRFields).
Notation CSRustatus := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRuie := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation CSRutvec := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation CSRuscratch := (STRUCT { "$tag" ::= $64 })%kami_expr.
Notation CSRuepc := (STRUCT { "$tag" ::= $65 })%kami_expr.
Notation CSRucause := (STRUCT { "$tag" ::= $66 })%kami_expr.
Notation CSRubadaddr := (STRUCT { "$tag" ::= $67 })%kami_expr.
Notation CSRuip := (STRUCT { "$tag" ::= $68 })%kami_expr.
Notation CSRfflags := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation CSRfrm := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation CSRfcsr := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation CSRcycle := (STRUCT { "$tag" ::= $3072 })%kami_expr.
Notation CSRtime := (STRUCT { "$tag" ::= $3073 })%kami_expr.
Notation CSRinstret := (STRUCT { "$tag" ::= $3074 })%kami_expr.
Notation CSRcycleh := (STRUCT { "$tag" ::= $3200 })%kami_expr.
Notation CSRtimeh := (STRUCT { "$tag" ::= $3201 })%kami_expr.
Notation CSRinstreth := (STRUCT { "$tag" ::= $3202 })%kami_expr.
Notation CSRsstatus := (STRUCT { "$tag" ::= $256 })%kami_expr.
Notation CSRsedeleg := (STRUCT { "$tag" ::= $258 })%kami_expr.
Notation CSRsideleg := (STRUCT { "$tag" ::= $259 })%kami_expr.
Notation CSRsie := (STRUCT { "$tag" ::= $260 })%kami_expr.
Notation CSRstvec := (STRUCT { "$tag" ::= $261 })%kami_expr.
Notation CSRsscratch := (STRUCT { "$tag" ::= $320 })%kami_expr.
Notation CSRsepc := (STRUCT { "$tag" ::= $321 })%kami_expr.
Notation CSRscause := (STRUCT { "$tag" ::= $322 })%kami_expr.
Notation CSRsbadaddr := (STRUCT { "$tag" ::= $323 })%kami_expr.
Notation CSRsip := (STRUCT { "$tag" ::= $324 })%kami_expr.
Notation CSRsptbr := (STRUCT { "$tag" ::= $384 })%kami_expr.
Notation CSRscycle := (STRUCT { "$tag" ::= $3328 })%kami_expr.
Notation CSRstime := (STRUCT { "$tag" ::= $3329 })%kami_expr.
Notation CSRsinstret := (STRUCT { "$tag" ::= $3330 })%kami_expr.
Notation CSRscycleh := (STRUCT { "$tag" ::= $3456 })%kami_expr.
Notation CSRstimeh := (STRUCT { "$tag" ::= $3457 })%kami_expr.
Notation CSRsinstreth := (STRUCT { "$tag" ::= $3458 })%kami_expr.
Notation CSRhstatus := (STRUCT { "$tag" ::= $512 })%kami_expr.
Notation CSRhedeleg := (STRUCT { "$tag" ::= $514 })%kami_expr.
Notation CSRhideleg := (STRUCT { "$tag" ::= $515 })%kami_expr.
Notation CSRhie := (STRUCT { "$tag" ::= $516 })%kami_expr.
Notation CSRhtvec := (STRUCT { "$tag" ::= $517 })%kami_expr.
Notation CSRhscratch := (STRUCT { "$tag" ::= $576 })%kami_expr.
Notation CSRhepc := (STRUCT { "$tag" ::= $577 })%kami_expr.
Notation CSRhcause := (STRUCT { "$tag" ::= $578 })%kami_expr.
Notation CSRhbadaddr := (STRUCT { "$tag" ::= $579 })%kami_expr.
Notation CSRhcycle := (STRUCT { "$tag" ::= $3584 })%kami_expr.
Notation CSRhtime := (STRUCT { "$tag" ::= $3585 })%kami_expr.
Notation CSRhinstret := (STRUCT { "$tag" ::= $3586 })%kami_expr.
Notation CSRhcycleh := (STRUCT { "$tag" ::= $3712 })%kami_expr.
Notation CSRhtimeh := (STRUCT { "$tag" ::= $3713 })%kami_expr.
Notation CSRhinstreth := (STRUCT { "$tag" ::= $3714 })%kami_expr.
Notation CSRmisa := (STRUCT { "$tag" ::= $3856 })%kami_expr.
Notation CSRmvendorid := (STRUCT { "$tag" ::= $3857 })%kami_expr.
Notation CSRmarchid := (STRUCT { "$tag" ::= $3858 })%kami_expr.
Notation CSRmimpid := (STRUCT { "$tag" ::= $3859 })%kami_expr.
Notation CSRmhartid := (STRUCT { "$tag" ::= $3860 })%kami_expr.
Notation CSRmstatus := (STRUCT { "$tag" ::= $768 })%kami_expr.
Notation CSRmedeleg := (STRUCT { "$tag" ::= $770 })%kami_expr.
Notation CSRmideleg := (STRUCT { "$tag" ::= $771 })%kami_expr.
Notation CSRmie := (STRUCT { "$tag" ::= $772 })%kami_expr.
Notation CSRmtvec := (STRUCT { "$tag" ::= $773 })%kami_expr.
Notation CSRmscratch := (STRUCT { "$tag" ::= $832 })%kami_expr.
Notation CSRmepc := (STRUCT { "$tag" ::= $833 })%kami_expr.
Notation CSRmcause := (STRUCT { "$tag" ::= $834 })%kami_expr.
Notation CSRmbadaddr := (STRUCT { "$tag" ::= $835 })%kami_expr.
Notation CSRmip := (STRUCT { "$tag" ::= $836 })%kami_expr.
Notation CSRmbase := (STRUCT { "$tag" ::= $896 })%kami_expr.
Notation CSRmbound := (STRUCT { "$tag" ::= $897 })%kami_expr.
Notation CSRmibase := (STRUCT { "$tag" ::= $898 })%kami_expr.
Notation CSRmibound := (STRUCT { "$tag" ::= $899 })%kami_expr.
Notation CSRmdbase := (STRUCT { "$tag" ::= $900 })%kami_expr.
Notation CSRmdbound := (STRUCT { "$tag" ::= $901 })%kami_expr.
Notation CSRmcycle := (STRUCT { "$tag" ::= $3840 })%kami_expr.
Notation CSRmtime := (STRUCT { "$tag" ::= $3841 })%kami_expr.
Notation CSRminstret := (STRUCT { "$tag" ::= $3842 })%kami_expr.
Notation CSRmcycleh := (STRUCT { "$tag" ::= $3968 })%kami_expr.
Notation CSRmtimeh := (STRUCT { "$tag" ::= $3969 })%kami_expr.
Notation CSRminstreth := (STRUCT { "$tag" ::= $3970 })%kami_expr.
Notation CSRmucounteren := (STRUCT { "$tag" ::= $784 })%kami_expr.
Notation CSRmscounteren := (STRUCT { "$tag" ::= $785 })%kami_expr.
Notation CSRmhcounteren := (STRUCT { "$tag" ::= $786 })%kami_expr.
Notation CSRmucycle_delta := (STRUCT { "$tag" ::= $1792 })%kami_expr.
Notation CSRmutime_delta := (STRUCT { "$tag" ::= $1793 })%kami_expr.
Notation CSRmuinstret_delta := (STRUCT { "$tag" ::= $1794 })%kami_expr.
Notation CSRmscycle_delta := (STRUCT { "$tag" ::= $1796 })%kami_expr.
Notation CSRmstime_delta := (STRUCT { "$tag" ::= $1797 })%kami_expr.
Notation CSRmsinstret_delta := (STRUCT { "$tag" ::= $1798 })%kami_expr.
Notation CSRmhcycle_delta := (STRUCT { "$tag" ::= $1800 })%kami_expr.
Notation CSRmhtime_delta := (STRUCT { "$tag" ::= $1801 })%kami_expr.
Notation CSRmhinstret_delta := (STRUCT { "$tag" ::= $1802 })%kami_expr.
Notation CSRmucycle_deltah := (STRUCT { "$tag" ::= $1920 })%kami_expr.
Notation CSRmutime_deltah := (STRUCT { "$tag" ::= $1921 })%kami_expr.
Notation CSRmuinstret_deltah := (STRUCT { "$tag" ::= $1922 })%kami_expr.
Notation CSRmscycle_deltah := (STRUCT { "$tag" ::= $1924 })%kami_expr.
Notation CSRmstime_deltah := (STRUCT { "$tag" ::= $1925 })%kami_expr.
Notation CSRmsinstret_deltah := (STRUCT { "$tag" ::= $1926 })%kami_expr.
Notation CSRmhcycle_deltah := (STRUCT { "$tag" ::= $1928 })%kami_expr.
Notation CSRmhtime_deltah := (STRUCT { "$tag" ::= $1929 })%kami_expr.
Notation CSRmhinstret_deltah := (STRUCT { "$tag" ::= $1930 })%kami_expr.
Definition InstructionFields'Fields := (STRUCT {
    "inst" :: (Bit InstSz);
    "rd" :: (Bit 5);
    "rs1" :: (Bit 5);
    "rs2" :: (Bit 5);
    "rs3" :: (Bit 5);
    "funct2" :: (Bit 2);
    "funct3" :: (Bit 3);
    "funct5" :: (Bit 5);
    "funct7" :: (Bit 7);
    "fmt" :: (Bit 2);
    "rm" :: RVRoundMode;
    "opcode" :: Opcode;
    "csrAddr" :: (Bit 12);
    "csr" :: CSR}).
Definition InstructionFields  := Struct (InstructionFields'Fields).

Definition getInstFields (x: (Bit 32)): InstructionFields := 
                Ret STRUCT { "inst" ::= #x; "rd" ::= #x[$11 : $7]; "rs1" ::= #x[$19 : $15]; "rs2" ::= #x[$24 : $20]; "rs3" ::= #x[$31 : $27]; "funct2" ::= #x[$26 : $25]; "funct3" ::= #x[$14 : $12]; "funct5" ::= #x[$31 : $27]; "funct7" ::= #x[$31 : $25]; "fmt" ::= #x[$26 : $25]; "rm" ::=  unpack(#x[$14 : $12]); "opcode" ::=  unpack(#x[$6 : $0]); "csrAddr" ::= #x[$31 : $20]; "csr" ::=  unpack(#x[$31 : $20])  }

.

Definition RVMemOpFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVMemOp := (Struct RVMemOpFields).
Notation Ld := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation St := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation PrefetchForLd := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation PrefetchForSt := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation Lr := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation Sc := (STRUCT { "$tag" ::= $7 })%kami_expr.
Definition RVAmoOpFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVAmoOp := (Struct RVAmoOpFields).
Notation Swap := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation Add := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Xor := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation And := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation Or := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation Min := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation Max := (STRUCT { "$tag" ::= $10 })%kami_expr.
Notation Minu := (STRUCT { "$tag" ::= $12 })%kami_expr.
Notation Maxu := (STRUCT { "$tag" ::= $14 })%kami_expr.
Definition RVMemSizeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVMemSize := (Struct RVMemSizeFields).
Notation B := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation H := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation W := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation D := (STRUCT { "$tag" ::= $3 })%kami_expr.
Definition toPermutedDataByteEn (size: RVMemSize) (addrLSB: DataByteSel): DataByteEn := 
                Ret (<<  toDataByteEn(#size) #addrLSB)

.

Definition RVMemAmoOpFields := (STRUCT {
    "$tag" :: (Bit 8);
    "MemOp" :: RVMemOp;
    "AmoOp" :: RVAmoOp}).
Definition RVMemAmoOp := Struct (RVMemAmoOpFields).
Definition RVMemInstFields := (STRUCT {
    "op" :: RVMemAmoOp;
    "size" :: RVMemSize;
    "isUnsigned" :: Bool}).
Definition RVMemInst  := Struct (RVMemInstFields).

Definition RiscVISASubsetFields := (STRUCT {
    "rv64" :: Bool;
    "h" :: Bool;
    "s" :: Bool;
    "u" :: Bool;
    "m" :: Bool;
    "a" :: Bool;
    "f" :: Bool;
    "d" :: Bool;
    "x" :: Bool}).
Definition RiscVISASubset  := Struct (RiscVISASubsetFields).

Definition getMISA (isa: RiscVISASubset): Data := 
                LET misa : Data <- (BinBit (Concat 2 4) $2'b00 $4'd0)

                If #isa
        then                 BKSTMTS {
                Assign misa = (| #misa (BinBit (Concat 2 4) $2'b10 $4'd0))
;
        Retv
        else                 BKSTMTS {
                Assign misa = (| #misa (BinBit (Concat 2 4) $2'b01 $4'd0))
;
        Retv;

                If #isa
        then                 Assign misa = (| #misa (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv

                If #isa
        then                 Assign misa = (| #misa (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv

                If #isa
        then                 Assign misa = (| #misa (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv

                If #isa
        then                 Assign misa = (| #misa (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv

                If #isa
        then                 Assign misa = (| #misa (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv

                If #isa
        then                 Assign misa = (| #misa (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv

                Ret #misa

.

Definition RegIndex := (word 5).

Definition FullRegIndexFields := (STRUCT {
    "$tag" :: (Bit 8);
    "Gpr" :: RegIndex;
    "Fpu" :: RegIndex}).
Definition FullRegIndex := Struct (FullRegIndexFields).
Definition toFullRegIndex (rType: Maybe RegType) (index: RegIndex): (Maybe FullRegIndex) := 
                Ret null

.

Definition NumArchReg := 64.

Definition NumPhyReg := NumArchReg.

Definition hasCSRPermission (csr: CSR) (prv: word 2) (write: bool): bool := 
        LET csr_index <- 

                Ret (&& (>= #prv #csr_index[$9 : $8]) (|| !#write (!= #csr_index[$11 : $10] $2'b11)))

.

Definition BrFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition BrFunc := (Struct BrFuncFields).
Notation BrEq := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation BrNeq := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation BrJal := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation BrJalr := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation BrLt := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation BrGe := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation BrLtu := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation BrGeu := (STRUCT { "$tag" ::= $7 })%kami_expr.
Definition AluFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition AluFunc := (Struct AluFuncFields).
Notation AluAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AluSll := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation AluSlt := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation AluSltu := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation AluXor := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation AluSrl := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation AluOr := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation AluAnd := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation AluSub := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation AluSra := (STRUCT { "$tag" ::= $13 })%kami_expr.
Notation AluAuipc := (STRUCT { "$tag" ::= $16 })%kami_expr.
Notation AluLui := (STRUCT { "$tag" ::= $24 })%kami_expr.
Definition AluInstFields := (STRUCT {
    "op" :: AluFunc;
    "w" :: Bool}).
Definition AluInst  := Struct (AluInstFields).

Definition MulDivFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition MulDivFunc := (Struct MulDivFuncFields).
Notation Mul := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Mulh := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation Div := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation Rem := (STRUCT { "$tag" ::= $3 })%kami_expr.
Definition MulDivSignFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition MulDivSign := (Struct MulDivSignFields).
Notation Signed := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Unsigned := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SignedUnsigned := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition MulDivInstFields := (STRUCT {
    "func" :: MulDivFunc;
    "w" :: Bool;
    "sign" :: MulDivSign}).
Definition MulDivInst  := Struct (MulDivInstFields).

Definition FpuFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition FpuFunc := (Struct FpuFuncFields).
Notation FAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSub := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMul := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FDiv := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSqrt := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSgnj := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSgnjn := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSgnjx := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMin := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMax := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_WF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_WUF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_LF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_LUF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FW := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FWU := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FL := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FLU := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FEq := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FLt := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FLe := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FClass := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMv_XF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMv_FX := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMSub := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FNMSub := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FNMAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition FpuPrecisionFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition FpuPrecision := (Struct FpuPrecisionFields).
Notation Single := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Double := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition FpuInstFields := (STRUCT {
    "func" :: FpuFunc;
    "precision" :: FpuPrecision}).
Definition FpuInst  := Struct (FpuInstFields).

Definition IntraCoreFenceFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition IntraCoreFence := (Struct IntraCoreFenceFields).
Notation FenceI := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SFenceVM := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition InterCoreFenceFields := (STRUCT {
    "sw" :: Bool;
    "sr" :: Bool;
    "so" :: Bool;
    "si" :: Bool;
    "pw" :: Bool;
    "pr" :: Bool;
    "po" :: Bool;
    "pi" :: Bool}).
Definition InterCoreFence  := Struct (InterCoreFenceFields).

Definition FenceFields := (STRUCT {
    "$tag" :: (Bit 8);
    "IntraCore" :: IntraCoreFence;
    "InterCore" :: InterCoreFence}).
Definition Fence := Struct (FenceFields).
Definition SystemInstFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition SystemInst := (Struct SystemInstFields).
Notation ECall := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation EBreak := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation URet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SRet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation HRet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation MRet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation WFI := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRRW := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRRS := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRRC := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRR := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRW := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition ExecFuncFields := (STRUCT {
    "$tag" :: (Bit 8);
    "EF_Alu" :: AluInst;
    "EF_Br" :: BrFunc;
    "EF_Mem" :: RVMemInst;
    "EF_MulDiv" :: MulDivInst;
    "EF_Fpu" :: FpuInst;
    "EF_Fence" :: Fence;
    "EF_System" :: SystemInst}).
Definition ExecFunc := Struct (ExecFuncFields).
Definition RegTypeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RegType := (Struct RegTypeFields).
Notation RtGpr := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation RtFpu := (STRUCT { "$tag" ::= $1 })%kami_expr.
Definition ImmTypeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition ImmType := (Struct ImmTypeFields).
Notation ItNone := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItI := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItS := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItSB := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItU := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItUJ := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItZ := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition RVDecodedInstFields := (STRUCT {
    "execFunc" :: ExecFunc;
    "imm" :: ImmType;
    "rs1" :: (Maybe RegType);
    "rs2" :: (Maybe RegType);
    "rs3" :: (Maybe RegType);
    "dst" :: (Maybe RegType);
    "inst" :: Instruction}).
Definition RVDecodedInst  := Struct (RVDecodedInstFields).

Definition ExceptionCauseFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition ExceptionCause := (Struct ExceptionCauseFields).
Notation InstAddrMisaligned := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation InstAccessFault := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation IllegalInst := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation Breakpoint := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation LoadAddrMisaligned := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation LoadAccessFault := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation StoreAddrMisaligned := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation StoreAccessFault := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation EnvCallU := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation EnvCallS := (STRUCT { "$tag" ::= $9 })%kami_expr.
Notation EnvCallH := (STRUCT { "$tag" ::= $10 })%kami_expr.
Notation EnvCallM := (STRUCT { "$tag" ::= $11 })%kami_expr.
Notation IllegalException := (STRUCT { "$tag" ::= $15 })%kami_expr.
Definition InterruptCauseFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition InterruptCause := (Struct InterruptCauseFields).
Notation USoftwareInterrupt := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SSoftwareInterrupt := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation HSoftwareInterrupt := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation MSoftwareInterrupt := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation UTimerInterrupt := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation STimerInterrupt := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation HTimerInterrupt := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation MTimerInterrupt := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation UExternalInterrupt := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation SExternalInterrupt := (STRUCT { "$tag" ::= $9 })%kami_expr.
Notation HExternalInterrupt := (STRUCT { "$tag" ::= $10 })%kami_expr.
Notation MExternalInterrupt := (STRUCT { "$tag" ::= $11 })%kami_expr.
Notation IllegalInterrupt := (STRUCT { "$tag" ::= $15 })%kami_expr.
Definition TrapCauseFields := (STRUCT {
    "$tag" :: (Bit 8);
    "TcException" :: ExceptionCause;
    "TcInterrupt" :: InterruptCause}).
Definition TrapCause := Struct (TrapCauseFields).
Definition toCauseCSR (x: TrapCause): Data := 
            If (#x!TrapCauseFields@."$tag" == $0) then
              LET cause <- x;
        BKSTMTS {
        LET pcause <- 
        with         Ret (BinBit (Concat 28 4) $28'd0 #pcause)
;
        Retv
    else
    If (#x!TrapCauseFields@."$tag" == $1) then
              LET cause <- x;
        BKSTMTS {
        LET pcause <- 
        with         Ret (BinBit (Concat 1 27) $1'b1 $27'd0)
;
        Retv
    else
        Retv

.

Definition CsrStateFields := (STRUCT {
    "prv" :: (Bit 2);
    "frm" :: (Bit 3);
    "f_enabled" :: Bool;
    "x_enabled" :: Bool}).
Definition CsrState  := Struct (CsrStateFields).

Definition RedirectFields := (STRUCT {
    "pc" :: Addr;
    "nextPc" :: Addr;
    "taken" :: Bool;
    "mispredict" :: Bool}).
Definition Redirect  := Struct (RedirectFields).

Definition ControlFlowFields := (STRUCT {
    "pc" :: Addr;
    "nextPc" :: Addr;
    "taken" :: Bool;
    "mispredict" :: Bool}).
Definition ControlFlow  := Struct (ControlFlowFields).

Definition FullResultFields (xlen : nat) := (STRUCT {
    "data" :: (Bit xlen);
    "fflags" :: (Bit 5);
    "vaddr" :: (Bit xlen);
    "paddr" :: (Bit xlen);
    "controlFlow" :: ControlFlow;
    "cause" :: (Maybe ExceptionCause)}).
Definition FullResult  (xlen : nat) := Struct (FullResultFields xlen).

Definition toFullResult (x: t): (FullResult xlen) := 
                Ret  updateFullResult(#x, #defaultValue)

.

Definition VMInfoFields (xlen : nat) := (STRUCT {
    "prv" :: (Bit 2);
    "asid" :: Asid;
    "vm" :: (Bit 5);
    "mxr" :: Bool;
    "pum" :: Bool;
    "base" :: (Bit xlen);
    "bound" :: (Bit xlen)}).
Definition VMInfo  (xlen : nat) := Struct (VMInfoFields xlen).

Definition PMAFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition PMA := (Struct PMAFields).
Notation MainMemory := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation IORom := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation IODevice := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation IOEmpty := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition isCacheable (pma: PMA): bool := 
                Ret null

.

Definition TlbReqFields := (STRUCT {
    "op" :: RVMemOp;
    "addr" :: Addr}).
Definition TlbReq  := Struct (TlbReqFields).

Definition TlbResp := (Tuple2 Addr (Maybe ExceptionCause)).

Definition PTE_Sv39Fields := (STRUCT {
    "reserved" :: (Bit 16);
    "ppn2" :: (Bit 20);
    "ppn1" :: (Bit 9);
    "ppn0" :: (Bit 9);
    "reserved_sw" :: (Bit 2);
    "d" :: Bool;
    "a" :: Bool;
    "g" :: Bool;
    "u" :: Bool;
    "x" :: Bool;
    "w" :: Bool;
    "r" :: Bool;
    "valid" :: Bool}).
Definition PTE_Sv39  := Struct (PTE_Sv39Fields).

Definition isLegalPTE (pte: PTE_Sv39): bool := 
                Ret (&& #pte !(&& #pte !#pte))

.

Definition isLeafPTE (pte: PTE_Sv39): bool := 
                Ret (&& #pte (|| (|| #pte #pte) #pte))

.

