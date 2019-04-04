Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import ClientServer.
Require Import Connectable.
Require Import DefaultValue.
Require Import GetPut.
Require Import Vector.
Require Import MemUtil.
Require Import Port.
Require Import ProcPins.
Require Import RVTypes.
Require Import VerificationPacket.
Definition FrontEndCsrsFields (xlen : nat) := (STRUCT {
    "vmI" :: (VMInfo xlen);
    "state" :: CsrState}).
Definition FrontEndCsrs  (xlen : nat) := Struct (FrontEndCsrsFields xlen).

Definition (RVIMMUReq addrSz) := (Bit addrSz).

Definition RVIMMURespFields (xlen : nat) := (STRUCT {
    "addr" :: (Bit xlen);
    "exception" :: (Maybe ExceptionCause)}).
Definition RVIMMUResp  (xlen : nat) := Struct (RVIMMURespFields xlen).

Definition RVDMMUReqFields (xlen : nat) := (STRUCT {
    "addr" :: (Bit xlen);
    "size" :: RVMemSize;
    "op" :: RVMemOp}).
Definition RVDMMUReq  (xlen : nat) := Struct (RVDMMUReqFields xlen).

Definition (RVDMMUResp addrSz) := (RVIMMUResp addrSz).

Definition FenceReq := Fence.

Definition FenceResp := Void.

(* * interface Proc#(mainMemoryWidth) *)
Record Proc (mainMemoryWidth : nat) := {
    Proc'modules: Modules;
    Proc'start : string;
    Proc'stop : string;
    Proc'currVerificationPacket : string;
    Proc'mmio : (CoarseMemClientPort XLEN (TLog (TDiv XLEN 8)));
    Proc'extmem : (CoarseMemServerPort XLEN (TLog (TDiv XLEN 8)));
    Proc'triggerExternalInterrupt : string;
    Proc'stallPipeline : string;
    Proc'pins : ProcPins;
}.

