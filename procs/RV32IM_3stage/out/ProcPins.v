Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RS232.
Require Import SPI.
(* * interface ProcPins *)
Record ProcPins := {
    ProcPins'interface: Modules;
    ProcPins'spi : SPIMasterPins;
    ProcPins'deleteme_unused_clock : Clock;
}.

