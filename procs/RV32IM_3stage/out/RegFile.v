Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface RegFile#(index_t, data_t) *)
Record RegFile (data_t : Kind) (index_t : Kind) := {
    RegFile'interface: Modules;
    RegFile'upd : string;
    RegFile'sub : string;
}.

