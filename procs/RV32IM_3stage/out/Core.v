Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import CoreStates.
Require Import FetchStage.
Require Import ExecStage.
Require Import WriteBackStage.
Require Import ClientServer.
Require Import GetPut.
Require Import Connectable.
Require Import DefaultValue.
Require Import FIFO.
Require Import GetPut.
Require Import Ehr.
Require Import MemUtil.
Require Import Port.
Require Import Abstraction.
Require Import RegUtil.
Require Import RVRegFile.
Require Import RVCsrFile.
Require Import RVTypes.
Require Import VerificationPacket.
Require Import RVMemory.
Require Import RVMulDiv.
(* * interface Core#(xlen) *)
Record Core (xlen : nat) := {
    Core'modules: Modules;
    Core'start : string;
    Core'stop : string;
    Core'stallPipeline : string;
    Core'currVerificationPacket : string;
}.

Module module'mkThreeStageCore.
    Section Section'mkThreeStageCore.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable ifetch: (ReadOnlyMemServerPort xlen 2).
    Variable dmem: (AtomicMemServerPort xlen (TLog (TDiv xlen 8))).
    Variable ipi: Bool.
    Variable timerInterrupt: Bool.
    Variable timer: string.
    Variable externalInterrupt: Bool.
    Variable hartID: (Bit xlen).
    Variable 32: nat.
                                                                       Let stallReg : string := instancePrefix--"stallReg".
       Let rf := mkRVRegFileBypass (instancePrefix--"rf").
       Let csrf := mkRVCsrFile (instancePrefix--"csrf").
       Let mulDiv := mkBoothRoughMulDivExec (instancePrefix--"mulDiv").
       Let fetchStateEhr := mkEhr (instancePrefix--"fetchStateEhr").
       Let executeStateEhr := mkEhr (instancePrefix--"executeStateEhr").
       Let writeBackStateEhr := mkEhr (instancePrefix--"writeBackStateEhr").
       Let verificationPacketEhr := mkEhr (instancePrefix--"verificationPacketEhr").
       Let f := mkFetchStage (instancePrefix--"f").
       Let e := mkExecStage (instancePrefix--"e").
       Let w := mkWriteBackStage (instancePrefix--"w").
    Definition mkThreeStageCoreModule: Modules.
        refine  (BKMODULE {
           Register stallReg : Bool <- $False
       with (BKMod (Bool'modules rf :: nil))
       with (BKMod (Data'modules csrf :: nil))
       with (BKMod (MulDivExec'modules mulDiv :: nil))
       with (BKMod (t'modules fetchStateEhr :: nil))
       with (BKMod (t'modules executeStateEhr :: nil))
       with (BKMod (t'modules writeBackStateEhr :: nil))
       with (BKMod (t'modules verificationPacketEhr :: nil))
       with (BKMod (Reg'modules f :: nil))
       with (BKMod (Reg'modules e :: nil))
       with (BKMod (Reg'modules w :: nil))
       with Rule instancePrefix--"clearVerificationPacketEhr" :=
               Write verificationPacketEhr[$0] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv (* rule clearVerificationPacketEhr *)
       with Method instancePrefix--"start" (startPc : (Bit xlen)) : Void :=
        Write fetchStateEhr[$3] <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "pc" ::= (#startPc)  }; "Invalid" ::= $0 };
        Write executeStateEhr[$3] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Write writeBackStateEhr[$3] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Write stallReg : Bool <- False;
        Retv

       with Method instancePrefix--"stop" () : Void :=
        Write fetchStateEhr[$3] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Write executeStateEhr[$3] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Write writeBackStateEhr[$3] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv

       with Method instancePrefix--"stallPipeline" (stall : Bool) : Void :=
        Write stallReg : Bool <- #stall;
        Retv

       with Method instancePrefix--"currVerificationPacket" () : (Maybe VerificationPacket) :=
        Read stallReg_v : Bool <- "stallReg";        Ret #stallReg_vSTRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }#verificationPacketEhr@[$0]

    }); abstract omega. Qed. (* mkThreeStageCore *)

(* Module mkThreeStageCore type ReadOnlyMemServerPort#(xlen, 2) -> AtomicMemServerPort#(xlen, TLog#(TDiv#(xlen, 8))) -> Bool -> Bool -> Reg#(Bit#(64)) -> Bool -> Bit#(xlen) -> Module#(Core#(xlen)) return type AtomicMemServerPort#(xlen, TLog#(TDiv#(xlen, 8))) *)
    Definition mkThreeStageCore := Build_Core (xlen) (TLog TDiv xlen 8) mkThreeStageCoreModule%kami (instancePrefix--"currVerificationPacket") (instancePrefix--"stallPipeline") (instancePrefix--"start") (instancePrefix--"stop").
    End Section'mkThreeStageCore.
End module'mkThreeStageCore.

Definition mkThreeStageCore := module'mkThreeStageCore.mkThreeStageCore.

