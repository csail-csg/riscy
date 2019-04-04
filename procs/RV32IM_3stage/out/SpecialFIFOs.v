Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import FIFOF.
Require Import FIFOLevel.
Require Import RevertingVirtualReg.
(* * interface SCounter *)
Record SCounter := {
    SCounter'modules: Modules;
    SCounter'incr : string;
    SCounter'decr : string;
    SCounter'isEq : string;
    SCounter'setNext : string;
    SCounter'set : string;
    SCounter'clear : string;
}.

