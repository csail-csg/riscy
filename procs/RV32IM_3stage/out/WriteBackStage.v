Require Import Bool String List Arith.
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
    WriteBackStage'interface: Modules;
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

Module mkWriteBackStage.
    Section Section'mkWriteBackStage.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable fs: (Reg (Maybe (FetchState xlen))).
    Variable es: (Reg (Maybe (ExecuteState xlen))).
    Variable ws: (Reg (Maybe (WriteBackState xlen))).
    Variable dmemres: (OutputPort (AtomicMemResp 2)).
    Variable mulDiv: (MulDivExec xlen).
    Variable csrf: (RVCsrFile xlen).
    Variable rf: (RVRegFile xlen).
    Variable verificationPackets: (Reg (Maybe VerificationPacket)).
    Variable stall: bool.
    Let csrfwr := MethodSig (RVCsrFile'wr csrf) (Bit xlen) : Function Maybe SystemInst Function CSR Function Bit xlen Function Bit xlen Function Maybe TrapCause Function Bit 5 Function Bool Function Bool ActionValue CsrReturn xlen.
(* FIXME: interface OutputPort subinterface deq *)
(* FIXME: interface MulDivExec subinterface result_data *)
(* FIXME: interface MulDivExec subinterface result_deq *)
    Let rfwr := MethodSig (RVRegFile'wr rf) (Maybe FullRegIndex) : Function Bit xlen Void.
    