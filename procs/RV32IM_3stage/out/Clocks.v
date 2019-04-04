Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Clock *)
Record Clock := {
    Clock'modules: Modules;
}.

(* * interface Reset *)
Record Reset := {
    Reset'modules: Modules;
}.

(* * interface SyncFIFOIfc#(a_type) *)
Record SyncFIFOIfc (a_type : Kind) := {
    SyncFIFOIfc'modules: Modules;
    SyncFIFOIfc'enq : string;
    SyncFIFOIfc'deq : string;
    SyncFIFOIfc'first : string;
    SyncFIFOIfc'notFull : string;
    SyncFIFOIfc'notEmpty : string;
}.

