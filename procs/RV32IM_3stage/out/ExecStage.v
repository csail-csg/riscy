Require Import Bool String List Arith.
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
    ExecStage'interface: Modules;
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

Module mkExecStage.
    Section Section'mkExecStage.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable fs: (Reg (Maybe (FetchState xlen))).
    Variable es: (Reg (Maybe (ExecuteState xlen))).
    Variable ws: (Reg (Maybe (WriteBackState xlen))).
    Variable ifetchres: (OutputPort (ReadOnlyMemResp 2)).
    Variable dmemreq: (InputPort (AtomicMemReq 32 2)).
    Variable mulDiv: (MulDivExec xlen).
    Variable csrf: (RVCsrFile xlen).
    Variable rf: (RVRegFile xlen).
(* FIXME: interface RVCsrFile subinterface readyInterrupt *)
    Let dmemreqenq := MethodSig (InputPort'enq dmemreq) (t) : Void.
(* FIXME: interface OutputPort subinterface deq *)
(* FIXME: interface OutputPort subinterface first *)
    Let mulDivexec := MethodSig (MulDivExec'exec mulDiv) (MulDivInst) : Function Bit xlen Function Bit xlen Void.
    Let rfrd1 := MethodSig (RVRegFile'rd1 rf) (Maybe FullRegIndex) : Bit xlen.
    Let rfrd2 := MethodSig (RVRegFile'rd2 rf) (Maybe FullRegIndex) : Bit xlen.
    