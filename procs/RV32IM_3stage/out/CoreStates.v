Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition FetchStateFields (xlen : nat) := (STRUCT {
    "pc" :: (Bit xlen)}).
Definition FetchState  (xlen : nat) := Struct (FetchStateFields xlen).

Definition ExecuteStateFields (xlen : nat) := (STRUCT {
    "poisoned" :: Bool;
    "pc" :: (Bit xlen)}).
Definition ExecuteState  (xlen : nat) := Struct (ExecuteStateFields xlen).

Definition WriteBackStateFields (xlen : nat) := (STRUCT {
    "pc" :: (Bit xlen);
    "trap" :: (Maybe TrapCause);
    "dInst" :: RVDecodedInst;
    "addr" :: (Bit xlen);
    "data" :: (Bit xlen)}).
Definition WriteBackState  (xlen : nat) := Struct (WriteBackStateFields xlen).

