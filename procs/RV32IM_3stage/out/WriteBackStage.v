Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import GetPut.
Require Import MemUtil.
Require Import Port.
Require Import Abstraction.
Require Import RVRegFile.
Require Import RVCsrFile.
Require Import RVTypes.
Require Import VerificationPacket.
Require Import RVMemory.
Require Import RVMulDiv.
Require Import CoreStates.
(* * interface WriteBackStage *)
Record WriteBackStage := {
    WriteBackStage'modules: Modules;
}.

Definition WriteBackRegsFields (xlen : nat) := (STRUCT {
    "fs" :: (Reg (Maybe (FetchState xlen)));
    "es" :: (Reg (Maybe (ExecuteState xlen)));
    "ws" :: (Reg (Maybe (WriteBackState xlen)));
    "dmemres" :: (OutputPort (AtomicMemResp 2));
    "mulDiv" :: (MulDivExec xlen);
    "csrf" :: (RVCsrFile xlen);
    "rf" :: (RVRegFile xlen);
    "verificationPackets" :: (Reg (Maybe VerificationPacket))}).
Definition WriteBackRegs  (xlen : nat) := Struct (WriteBackRegsFields xlen).

Module module'mkWriteBackStage.
    Section Section'mkWriteBackStage.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable fs: string.
    Variable es: string.
    Variable ws: string.
    Variable dmemres: (OutputPort (AtomicMemResp 2)).
    Variable mulDiv: (MulDivExec xlen).
    Variable csrf: (RVCsrFile xlen).
    Variable rf: (RVRegFile xlen).
    Variable verificationPackets: string.
    Variable stall: Bool.
    Variable 32: nat.
                       Let getInstFields := mkGetInstFields (instancePrefix--"getInstFields").
       Let isMemOp := mkIsMemOpRVMemAmoOp (instancePrefix--"isMemOp").
       Let tfri := mkToFullRegIndex (instancePrefix--"tfri").
    Let csrfwr : string := (RVCsrFile'wr csrf).
(* FIXME: interface OutputPort subinterface deq *)
    Let getInstFieldsgetInstFields : string := (GetInstFields'getInstFields getInstFields).
    Let isMemOpgetsResponse : string := (IsMemOp'getsResponse isMemOp).
(* FIXME: interface MulDivExec subinterface result_data *)
(* FIXME: interface MulDivExec subinterface result_deq *)
    Let rfwr : string := (RVRegFile'wr rf).
    Definition mkWriteBackStageModule: Modules.
        refine  (BKMODULE {
           (BKMod (GetInstFields'modules getInstFields :: nil))
       with (BKMod (IsMemOp'modules isMemOp :: nil))
       with (BKMod (ToFullRegIndex'modules tfri :: nil))
       with Rule instancePrefix--"doWriteBack" :=
        Read es_v : Maybe ExecuteState xlen <- es;
        Read ws_v : Maybe WriteBackState xlen <- ws;
        Assert(#ws_v$taggedValid.writeBackState((#writeBackState != STRUCT {  "$tag" ::= $6; "EF_System" ::= WFI; "EF_Alu" ::= $0; "EF_Br" ::= $0; "EF_Fence" ::= $0; "EF_Fpu" ::= $0; "EF_Mem" ::= $0; "EF_MulDiv" ::= $0 }) ||  csrfwakeFromWFI())!#stall);
               LET pc : tvar1834 = #writeBackState;
               LET trap : tvar1835 = #writeBackState;
               LET dInst : RVDecodedInst <- #writeBackState;
               LET inst : Instruction <- #dInst;
               LET addr : (Bit XLEN) <- #writeBackState;
               LET data : (Bit XLEN) <- #writeBackState;
               Write ws : Maybe WriteBackState xlen <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
               If #dInst$taggedEF_MulDiv.*(#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
        then                 BKSTMTS {
                Assign data = #mulDiv;
        #mulDiv;
;
        Retv;
               If #dInst$taggedEF_Mem.memInst(#trap == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
        then                 BKSTMTS {
                If  isMemOpgetsResponse(#memInst)
        then                 BKSTMTS {
                LET addrlsb : (Bit 2) <- #addr$[1:0]@32;
                Assign data = (#dmemres >> castBits _ _ _ _ (BinBit (Concat 2 3) #addrlsb $0));
                LET extendFunc : tvar1844 = #memInst#zeroExtend#signExtend;
                Assign data = null;
;
        Retv;
        #dmemres;
;
        Retv;
               Call csrfResult : tvar1859 <-  csrfwr(#pc, #dInst$taggedEF_System.sysInstSTRUCT {  "$tag" ::= $0; "Valid" ::= #sysInst; "Invalid" ::= $0 }STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 },  getInstFieldsgetInstFields(#inst), #data, #addr, #trap, $0, False, False);
               LET maybeNextPc : (Maybe Addr) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
               LET maybeData : (Maybe Data) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
               LET maybeTrap : (Maybe TrapCause) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
           If (#csrfResult!CsrReturnFields@."$tag" == $0) then (
              LET exc <- csrfResult;
        BKSTMTS {
                Assign maybeNextPc = STRUCT {  "$tag" ::= $0; "Valid" ::= #exc; "Invalid" ::= $0 };
                Assign maybeTrap = STRUCT {  "$tag" ::= $0; "Valid" ::= #exc; "Invalid" ::= $0 };


   ) else (
    If (#csrfResult!CsrReturnFields@."$tag" == $1) then (
              LET newPc <- csrfResult;
        Assign maybeNextPc = STRUCT {  "$tag" ::= $0; "Valid" ::= #newPc; "Invalid" ::= $0 }

   ) else (
    If (#csrfResult!CsrReturnFields@."$tag" == $2) then (
              LET data <- csrfResult;
        Assign maybeData = STRUCT {  "$tag" ::= $0; "Valid" ::= #data; "Invalid" ::= $0 }

   ) else (
    If (#csrfResult!CsrReturnFields@."$tag" == $3) then (
#noAction

   ) else (
#noAction
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
;
               LET isInterrupt : Bool <- False;
               LET isException : Bool <- False;
               LET trapCause : (Bit 4) <- $0;
           If (#maybeTrap!MaybeFields@."$tag" == $0) then (
        BKSTMTS {
                Assign isInterrupt = True;
                Assign trapCause =  pack(#x);


   ) else (
    If (#maybeTrap!MaybeFields@."$tag" == $0) then (
        BKSTMTS {
                Assign isException = True;
                Assign trapCause =  pack(#x);


   ) else (
#noAction
) as retval; Ret #retval
) as retval; Ret #retval
;
       CallM instFields : InstructionFields <-  getInstFieldsgetInstFields(#inst);
               LET dst : (Maybe RegType) <- #dInst;
       CallM dstbits : (Bit 2) <-  pack(#dst);
               Write verificationPackets : Maybe VerificationPacket <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "skippedPackets" ::= ($0); "pc" ::= ( signExtend(#pc)); "data" ::= ( signExtend( fromMaybe(#data, #maybeData))); "addr" ::= ( signExtend(#addr)); "instruction" ::= (#inst); "dst" ::= (castBits _ _ _ _ (BinBit (Concat 2 5) #dstbits #instFields)); "exception" ::= (#isException); "interrupt" ::= (#isInterrupt); "cause" ::= (#trapCause)  }; "Invalid" ::= $0 };
               If #maybeNextPc$taggedValid.replayPc
        then                 BKSTMTS {
                Write fs : Maybe FetchState xlen <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "pc" ::= (#replayPc)  }; "Invalid" ::= $0 };
                If #es_v$taggedValid.validExecuteState
        then                 BKSTMTS {
                Write es : Maybe ExecuteState xlen <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "poisoned" ::= (True); "pc" ::= (#validExecuteState)  }; "Invalid" ::= $0 };
;
        Retv;
;
        Retv
        else                 BKSTMTS {
         rfwr( tfritoFullRegIndex(#dInst,  getInstFieldsgetInstFields(#inst)),  fromMaybe(#data, #maybeData));
;
        Retv;;
        Retv (* rule doWriteBack *)
    }); abstract omega. Qed. (* mkWriteBackStage *)

(* Module mkWriteBackStage type Reg#(Maybe#(FetchState#(xlen))) -> Reg#(Maybe#(ExecuteState#(xlen))) -> Reg#(Maybe#(WriteBackState#(xlen))) -> OutputPort#(AtomicMemResp#(2)) -> MulDivExec#(xlen) -> RVCsrFile#(xlen) -> RVRegFile#(xlen) -> Reg#(Maybe#(VerificationPacket)) -> Bool -> Module#(WriteBackStage) return type Reg#(Maybe#(ExecuteState#(xlen))) *)
    Definition mkWriteBackStage := Build_WriteBackStage (Maybe ExecuteState xlen) mkWriteBackStageModule%kami.
    End Section'mkWriteBackStage.
End module'mkWriteBackStage.

Definition mkWriteBackStage := module'mkWriteBackStage.mkWriteBackStage.

