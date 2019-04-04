Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import GetPut.
Require Import MemUtil.
Require Import Port.
Require Import Abstraction.
Require Import RVRegFile.
Require Import RVCsrFile.
Require Import RVExec.
Require Import RVTypes.
Require Import RVAlu.
Require Import RVControl.
Require Import RVDecode.
Require Import RVMemory.
Require Import RVMulDiv.
Require Import CoreStates.
(* * interface ExecStage *)
Record ExecStage := {
    ExecStage'modules: Modules;
}.

Definition ExecRegsFields (xlen : nat) := (STRUCT {
    "fs" :: (Reg (Maybe (FetchState xlen)));
    "es" :: (Reg (Maybe (ExecuteState xlen)));
    "ws" :: (Reg (Maybe (WriteBackState xlen)));
    "ifetchres" :: (OutputPort (ReadOnlyMemResp 2));
    "dmemreq" :: (InputPort (AtomicMemReq 32 2));
    "mulDiv" :: (MulDivExec xlen);
    "csrf" :: (RVCsrFile xlen);
    "rf" :: (RVRegFile xlen)}).
Definition ExecRegs  (xlen : nat) := Struct (ExecRegsFields xlen).

Module module'mkExecStage.
    Section Section'mkExecStage.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable fs: string.
    Variable es: string.
    Variable ws: string.
    Variable ifetchres: (OutputPort (ReadOnlyMemResp 2)).
    Variable dmemreq: (InputPort (AtomicMemReq 32 2)).
    Variable mulDiv: (MulDivExec xlen).
    Variable csrf: (RVCsrFile xlen).
    Variable rf: (RVRegFile xlen).
    Variable 32: nat.
                           Let getInstFields := mkGetInstFields (instancePrefix--"getInstFields").
       Let rvDecode := mkRVDecode (instancePrefix--"rvDecode").
       Let basicExec := mkBasicExec (instancePrefix--"basicExec").
       Let tfri := mkToFullRegIndex (instancePrefix--"tfri").
    Let basicExecbasicExec : string := (BasicExec'basicExec basicExec).
(* FIXME: interface RVCsrFile subinterface readyInterrupt *)
    Let dmemreqenq : string := (InputPort'enq dmemreq).
(* FIXME: interface OutputPort subinterface deq *)
(* FIXME: interface OutputPort subinterface first *)
    Let mulDivexec : string := (MulDivExec'exec mulDiv).
    Let rfrd1 : string := (RVRegFile'rd1 rf).
    Let rfrd2 : string := (RVRegFile'rd2 rf).
    Let rvDecodedecodeInst : string := (RVDecode'decodeInst rvDecode).
    Definition mkExecStageModule: Modules.
        refine  (BKMODULE {
           (BKMod (GetInstFields'modules getInstFields :: nil))
       with (BKMod (RVDecode'modules rvDecode :: nil))
       with (BKMod (BasicExec'modules basicExec :: nil))
       with (BKMod (ToFullRegIndex'modules tfri :: nil))
       with Rule instancePrefix--"doExecute" :=
        Read es_v : Maybe ExecuteState xlen <- es;
        Read ws_v : Maybe WriteBackState xlen <- ws;
        Assert(#es_v$taggedValid.executeState(#ws_v == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }));
               LET poisoned : tvar1787 = #executeState;
               LET pc : tvar1788 = #executeState;
               Write es : Maybe ExecuteState xlen <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
               LET ifetchdata : (ReadOnlyMemResp 2) <- #ifetchres;
               LET inst : Bit TMul 8 TExp logNumBytes = #ifetchdata;
       #ifetchres;
               If !#poisoned
        then                 BKSTMTS {
                LET trap : (Maybe TrapCause) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
                If #csrf$taggedValid.validInterrupt
        then                 BKSTMTS {
                Assign trap = STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT {  "$tag" ::= $1; "TcInterrupt" ::= #validInterrupt; "TcException" ::= $0 }; "Invalid" ::= $0 };
;
        Retv;
                LET misa : RiscVISASubset <- #defaultValue;
                Call maybeDInst : tvar1800 <-  rvDecodedecodeInst(#misa, #misa, #misa, #misa, #misa, #inst);
                If ((#maybeDInst == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }) && (#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }))
        then                 BKSTMTS {
                Assign trap = STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT {  "$tag" ::= $0; "TcException" ::= IllegalInst; "TcInterrupt" ::= $0 }; "Invalid" ::= $0 };
;
        Retv;
                Call dInst : tvar1803 <-  fromMaybe(null, #maybeDInst);
                Call rVal1 : tvar1804 <-  rfrd1( tfritoFullRegIndex(#dInst,  getInstFieldsgetInstFields(#inst)));
                Call rVal2 : tvar1810 <-  rfrd2( tfritoFullRegIndex(#dInst,  getInstFieldsgetInstFields(#inst)));
                Call execResult : tvar1819 <-  basicExecbasicExec(#dInst, #rVal1, #rVal2, #pc);
                LET data : (Bit XLEN) <- #execResult;
                LET addr : (Bit XLEN) <- #execResult;
                LET nextPc : (Bit XLEN) <- #execResult;
                If ((#nextPc$[1:0]@32 != $0) && (#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }))
        then                 BKSTMTS {
                Assign trap = STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT {  "$tag" ::= $0; "TcException" ::= InstAddrMisaligned; "TcInterrupt" ::= $0 }; "Invalid" ::= $0 };
;
        Retv;
                If #dInst$taggedEF_MulDiv.mulDivInst(#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
        then                 BKSTMTS {
         mulDivexec(#mulDivInst, #rVal1, #rVal2);
;
        Retv;
                If #dInst$taggedEF_Mem.memInst(#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
        then                 BKSTMTS {
                LET aligned : Bool <- null;
                If #aligned
        then                 BKSTMTS {
                LET addrlsb : (Bit 2) <- #addr$[1:0]@32;
                LET aligned_data : (Bit 32) <- (#data << castBits _ _ _ _ (BinBit (Concat 2 3) #addrlsb $0));
                LET write_en : (Bit 4) <- (#dInst == STRUCT {  "$tag" ::= $0; "MemOp" ::= Ld; "AmoOp" ::= $0 })$0null;
         dmemreqenq(STRUCT { "write_en" ::= (#write_en); "atomic_op" ::= (None); "addr" ::= (#addr); "data" ::= (#aligned_data)  });
;
        Retv
        else                 BKSTMTS {
                If ((#memInst == STRUCT {  "$tag" ::= $0; "MemOp" ::= Ld; "AmoOp" ::= $0 }) || (#memInst == STRUCT {  "$tag" ::= $0; "MemOp" ::= Lr; "AmoOp" ::= $0 }))
        then                 BKSTMTS {
                Assign trap = STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT {  "$tag" ::= $0; "TcException" ::= LoadAddrMisaligned; "TcInterrupt" ::= $0 }; "Invalid" ::= $0 };
;
        Retv
        else                 BKSTMTS {
                Assign trap = STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT {  "$tag" ::= $0; "TcException" ::= StoreAddrMisaligned; "TcInterrupt" ::= $0 }; "Invalid" ::= $0 };
;
        Retv;;
;
        Retv;;
;
        Retv;
                If (#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
        then                 BKSTMTS {
                Write fs : Maybe FetchState xlen <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "pc" ::= (#nextPc)  }; "Invalid" ::= $0 };
;
        Retv;
                Write ws : Maybe WriteBackState xlen <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "pc" ::= (#pc); "trap" ::= (#trap); "dInst" ::= (#dInst); "addr" ::= (#addr); "data" ::= (#data)  }; "Invalid" ::= $0 };
;
        Retv;
        Retv (* rule doExecute *)
    }); abstract omega. Qed. (* mkExecStage *)

(* Module mkExecStage type Reg#(Maybe#(FetchState#(xlen))) -> Reg#(Maybe#(ExecuteState#(xlen))) -> Reg#(Maybe#(WriteBackState#(xlen))) -> OutputPort#(ReadOnlyMemResp#(2)) -> InputPort#(AtomicMemReq#(32, 2)) -> MulDivExec#(xlen) -> RVCsrFile#(xlen) -> RVRegFile#(xlen) -> Module#(ExecStage) return type Reg#(Maybe#(ExecuteState#(xlen))) *)
    Definition mkExecStage := Build_ExecStage (Maybe ExecuteState xlen) mkExecStageModule%kami.
    End Section'mkExecStage.
End module'mkExecStage.

Definition mkExecStage := module'mkExecStage.mkExecStage.

