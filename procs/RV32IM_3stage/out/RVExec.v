Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVDecode.
Require Import RVTypes.
Require Import Vector.
Require Import RVAlu.
Require Import RVControl.
Require Import RVMemory.
Definition ExecResultFields (xlen : nat) := (STRUCT {
    "data" :: (Bit XLEN);
    "addr" :: (Bit XLEN);
    "taken" :: Bool;
    "nextPc" :: (Bit XLEN)}).
Definition ExecResult  (xlen : nat) := Struct (ExecResultFields xlen).

(* * interface RVExec *)
Record RVExec := {
    RVExec'modules: Modules;
    RVExec'execRef : string;
}.

Module module'mkRVExec.
    Section Section'mkRVExec.
    Variable instancePrefix: string.
               Let rvDecoder := mkRVDecode (instancePrefix--"rvDecoder").
    Let rvDecodergetImmediate : string := (RVDecode'getImmediate rvDecoder).
    Definition mkRVExecModule: Modules :=
         (BKMODULE {
           (BKMod (RVDecode'modules rvDecoder :: nil))
       with Method4 instancePrefix--"execRef" (dInst : RVDecodedInst) (rVal1 : (Bit XLEN)) (rVal2 : (Bit XLEN)) (pc : (Bit XLEN)) : (ExecResult XLEN) :=
        LET data : (Bit XLEN) <- $0;
        LET addr : (Bit XLEN) <- $0;
        LET pcPlus4 : (Bit XLEN) <- (#pc + $4);
        LET taken : Bool <- False;
        LET nextPc : (Bit XLEN) <- #pcPlus4;
CallM imm : (Maybe (Bit XLEN)) <-  rvDecodergetImmediate(#dInst, #dInst);
    If (#dInst!ExecFuncFields@."$tag" == $0) then (
              LET aluInst <- dInst.execFunc;
        BKSTMTS {
                Assign data =  execAluInst(#aluInst, #rVal1, #rVal2, #imm, #pc);


   ) else (
    If (#dInst!ExecFuncFields@."$tag" == $1) then (
              LET brFunc <- dInst.execFunc;
        BKSTMTS {
                Assign data = #pcPlus4;
                Assign addr =  brAddrCalc(#brFunc, #pc, #rVal1,  fromMaybe(null, #imm));
                Assign taken =  aluBr(#brFunc, #rVal1, #rVal2);
                Assign nextPc = #taken#addr#pcPlus4;


   ) else (
    If (#dInst!ExecFuncFields@."$tag" == $2) then (
              LET memInst <- dInst.execFunc;
        BKSTMTS {
                Assign data = #rVal2;
                Assign addr =  addrCalc(#rVal1, #imm);


   ) else (
    If (#dInst!ExecFuncFields@."$tag" == $6) then (
              LET systemInst <- dInst.execFunc;
        BKSTMTS {
                Assign data =  fromMaybe(#rVal1, #imm);


   ) else (
        Assign data = $0
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
;
        Ret STRUCT { "data" ::= (#data); "addr" ::= (#addr); "taken" ::= (#taken); "nextPc" ::= (#nextPc)  }

    }). (* mkRVExec *)

(* Module mkRVExec type Module#(RVExec) return type RVExec *)
    Definition mkRVExec := Build_RVExec mkRVExecModule%kami (instancePrefix--"execRef").
    End Section'mkRVExec.
End module'mkRVExec.

Definition mkRVExec := module'mkRVExec.mkRVExec.

(* * interface BasicExecInternal *)
Record BasicExecInternal := {
    BasicExecInternal'modules: Modules;
    BasicExecInternal'brAddrCalc : string;
    BasicExecInternal'alu : string;
    BasicExecInternal'aluBr : string;
}.

Module module'mkBasicExecInternal.
    Section Section'mkBasicExecInternal.
    Variable instancePrefix: string.
                Definition mkBasicExecInternalModule: Modules :=
         (BKMODULE {
           Method4 instancePrefix--"brAddrCalc" (brFunc : BrFunc) (pc : (Bit XLEN)) (val : (Bit XLEN)) (imm : (Bit XLEN)) : (Bit XLEN) :=
        LET targetAddr : (Bit XLEN) <- null;
        Ret #targetAddr

       with Method4 instancePrefix--"alu" (func : AluFunc) (w : Bool) (a : (Bit XLEN)) (b : (Bit XLEN)) : (Bit XLEN) :=
        If (null == $32)
        then                 BKSTMTS {
                Assign w = True;
;
        Retv;
        If #w
        then                 BKSTMTS {
                Assign a = (#func == AluSra) signExtend(#a$[31:0]@32) zeroExtend(#a$[31:0]@32);
                Assign b =  zeroExtend(#b$[31:0]@32);
;
        Retv;
LET shamt : (Bit 6) <- UniBit (Trunc 6 (32 - 6)) (castBits _ _ _ _ #b);
        If #w
        then                 BKSTMTS {
                Assign shamt = castBits _ _ _ _ (BinBit (Concat 1 tvar1653) $0 #shamt$[4:0]@6);
;
        Retv;
        LET res : (Bit XLEN) <- null;
        If #w
        then                 BKSTMTS {
                Assign res =  signExtend(#res$[31:0]@32);
;
        Retv;
        Ret #res

       with Method3 instancePrefix--"aluBr" (brFunc : BrFunc) (a : (Bit XLEN)) (b : (Bit XLEN)) : Bool :=
        LET brTaken : Bool <- null;
        Ret #brTaken

    }). (* mkBasicExecInternal *)

(* Module mkBasicExecInternal type Module#(BasicExecInternal) return type BasicExecInternal *)
    Definition mkBasicExecInternal := Build_BasicExecInternal mkBasicExecInternalModule%kami (instancePrefix--"alu") (instancePrefix--"aluBr") (instancePrefix--"brAddrCalc").
    End Section'mkBasicExecInternal.
End module'mkBasicExecInternal.

Definition mkBasicExecInternal := module'mkBasicExecInternal.mkBasicExecInternal.

(* * interface BasicExec *)
Record BasicExec := {
    BasicExec'modules: Modules;
    BasicExec'basicExec : string;
}.

Module module'mkBasicExec.
    Section Section'mkBasicExec.
    Variable instancePrefix: string.
                   Let basicExecInternal := mkBasicExecInternal (instancePrefix--"basicExecInternal").
       Let rvDecoder := mkRVDecode (instancePrefix--"rvDecoder").
    Let basicExecInternalalu : string := (BasicExecInternal'alu basicExecInternal).
    Let basicExecInternalaluBr : string := (BasicExecInternal'aluBr basicExecInternal).
    Let basicExecInternalbrAddrCalc : string := (BasicExecInternal'brAddrCalc basicExecInternal).
    Let rvDecodergetImmediate : string := (RVDecode'getImmediate rvDecoder).
    Definition mkBasicExecModule: Modules :=
         (BKMODULE {
           (BKMod (BasicExecInternal'modules basicExecInternal :: nil))
       with (BKMod (RVDecode'modules rvDecoder :: nil))
       with Method4 instancePrefix--"basicExec" (dInst : RVDecodedInst) (rVal1 : (Bit XLEN)) (rVal2 : (Bit XLEN)) (pc : (Bit XLEN)) : (ExecResult XLEN) :=
        LET pcPlus4 : (Bit XLEN) <- (#pc + $4);
        LET data : (Bit XLEN) <- $0;
        LET addr : (Bit XLEN) <- $0;
        LET taken : Bool <- False;
        LET nextPc : (Bit XLEN) <- #pcPlus4;
CallM imm : (Maybe (Bit XLEN)) <-  rvDecodergetImmediate(#dInst, #dInst);
        If #dInst$taggedEF_Mem.*
        then                 BKSTMTS {
                If ! isValid(#imm)
        then                 BKSTMTS {
                Assign imm = STRUCT {  "$tag" ::= $0; "Valid" ::= $0; "Invalid" ::= $0 };
;
        Retv;
;
        Retv;
        LET aluVal1 : (Bit XLEN) <- #rVal1;
        LET aluVal2 : (Bit XLEN) <- #imm$taggedValid.validImm#validImm#rVal2;
        If #dInst$taggedEF_Alu.aluInst
        then                 BKSTMTS {
            If (#aluInst!AluFuncFields@."$tag" == $16) then (
        Assign aluVal1 = #pc

   ) else (
    If (#aluInst!AluFuncFields@."$tag" == $24) then (
        Assign aluVal1 = $0

   ) else (
        Assign aluVal1 = $0
) as retval; Ret #retval
) as retval; Ret #retval
;
;
        Retv;
        LET aluF : AluFunc <- #dInst$taggedEF_Alu.aluInst#aluInstAluAdd;
        LET w : Bool <- #dInst$taggedEF_Alu.aluInst#aluInstFalse;
CallM aluResult : (Bit XLEN) <-  basicExecInternalalu(#aluF, #w, #aluVal1, #aluVal2);
        If #dInst$taggedEF_Br.brFunc
        then                 BKSTMTS {
                Assign taken =  basicExecInternalaluBr(#brFunc, #rVal1, #rVal2);
                If #taken
        then                 BKSTMTS {
                Assign nextPc =  basicExecInternalbrAddrCalc(#brFunc, #pc, #rVal1,  fromMaybe(null, #imm));
;
        Retv;
;
        Retv;
        Assign data = null;
        Assign addr = null;
        Ret STRUCT { "data" ::= (#data); "addr" ::= (#addr); "taken" ::= (#taken); "nextPc" ::= (#nextPc)  }

    }). (* mkBasicExec *)

(* Module mkBasicExec type Module#(BasicExec) return type BasicExec *)
    Definition mkBasicExec := Build_BasicExec mkBasicExecModule%kami (instancePrefix--"basicExec").
    End Section'mkBasicExec.
End module'mkBasicExec.

Definition mkBasicExec := module'mkBasicExec.mkBasicExec.

(* * interface ScatterGatherLoadStore *)
Record ScatterGatherLoadStore := {
    ScatterGatherLoadStore'modules: Modules;
    ScatterGatherLoadStore'gatherLoad : string;
    ScatterGatherLoadStore'scatterStore : string;
}.

Module module'mkScatterGatherLoadStore.
    Section Section'mkScatterGatherLoadStore.
    Variable instancePrefix: string.
        Definition extend:  := 
    #isUnsigned#zeroExtend#signExtend
.

           Let toPermutedDataByteEn := mkToPermutedDataByteEn (instancePrefix--"toPermutedDataByteEn").
    Let toPermutedDataByteEntoPermutedDataByteEn : string := (ToPermutedDataByteEn'toPermutedDataByteEn toPermutedDataByteEn).
    Definition mkScatterGatherLoadStoreModule: Modules :=
         (BKMODULE {
           (BKMod (ToPermutedDataByteEn'modules toPermutedDataByteEn :: nil))
       with Method4 instancePrefix--"gatherLoad" (byteSel : (Bit (TLog (TDiv XLEN 8)))) (size : RVMemSize) (isUnsigned : Bool) (data : (Bit XLEN)) : (Bit XLEN) :=
        LET bitsToShiftBy : Bit tvar1649 = castBits _ _ _ _ (BinBit (Concat TLog#(TDiv#(XLEN, 8)) 3) #byteSel $0);
        Assign data = (#data >> #bitsToShiftBy);
        Assign data = null;
        Ret #data

       with Method3 instancePrefix--"scatterStore" (byteSel : DataByteSel) (size : RVMemSize) (data : (Bit XLEN)) : (Tuple2 DataByteEn (Bit XLEN)) :=
        LET bitsToShiftBy : (Bit 5) <- ( extend(#byteSel) * $8);
        Assign data = (#data << #bitsToShiftBy);
CallM permutedByteEn : DataByteEn <-  toPermutedDataByteEntoPermutedDataByteEn(#size, #byteSel);
        Ret  tuple2(#permutedByteEn, #data)

    }). (* mkScatterGatherLoadStore *)

(* Module mkScatterGatherLoadStore type Module#(ScatterGatherLoadStore) return type ScatterGatherLoadStore *)
    Definition mkScatterGatherLoadStore := Build_ScatterGatherLoadStore mkScatterGatherLoadStoreModule%kami (instancePrefix--"gatherLoad") (instancePrefix--"scatterStore").
    End Section'mkScatterGatherLoadStore.
End module'mkScatterGatherLoadStore.

Definition mkScatterGatherLoadStore := module'mkScatterGatherLoadStore.mkScatterGatherLoadStore.

