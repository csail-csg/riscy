Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import FIFOF.
(* * interface Get#(a) *)
Record Get (a : Kind) := {
    Get'interface: Modules;
    Get'get : string;
}.

(* * interface Put#(a) *)
Record Put (a : Kind) := {
    Put'interface: Modules;
    Put'put : string;
}.

