Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import FIFOF.
(* * interface Get#(a) *)
Record Get (a : Kind) := {
    Get'modules: Modules;
    Get'get : string;
}.

(* * interface Put#(a) *)
Record Put (a : Kind) := {
    Put'modules: Modules;
    Put'put : string;
}.

