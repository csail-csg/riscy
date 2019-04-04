Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Vector#(len, element_type) *)
Record Vector (len : nat) (element_type : Kind) := {
    Vector'modules: Modules;
}.

