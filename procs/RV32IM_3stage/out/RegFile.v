Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface RegFile#(index_t, data_t) *)
Record RegFile (index_t : Kind) (data_t : Kind) := {
    RegFile'modules: Modules;
    RegFile'upd : string;
    RegFile'sub : string;
}.

