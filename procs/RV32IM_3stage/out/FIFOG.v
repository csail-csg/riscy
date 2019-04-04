Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFOF.
Require Import GetPut.
Require Import SpecialFIFOs.
Require Import RevertingVirtualReg.
(* * interface FIFOG#(t) *)
Record FIFOG (t : Kind) := {
    FIFOG'modules: Modules;
    FIFOG'enq : string;
    FIFOG'deq : string;
    FIFOG'first : string;
    FIFOG'clear : string;
    FIFOG'notFull : string;
    FIFOG'notEmpty : string;
    FIFOG'canEnq : string;
    FIFOG'canDeq : string;
}.

