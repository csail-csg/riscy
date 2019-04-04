Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Clocks.
(* * interface SPIMasterPins *)
Record SPIMasterPins := {
    SPIMasterPins'modules: Modules;
    SPIMasterPins'sclk : string;
    SPIMasterPins'mosi : string;
    SPIMasterPins'miso : string;
    SPIMasterPins'ncs : string;
}.

(* * interface SPIMaster *)
Record SPIMaster := {
    SPIMaster'modules: Modules;
    SPIMaster'setSclkDiv : string;
    SPIMaster'setNcs : string;
    SPIMaster'setCpol : string;
    SPIMaster'setCpha : string;
    SPIMaster'isChipSelectEnabled : string;
    SPIMaster'put : string;
    SPIMaster'get : string;
    SPIMaster'pins : SPIMasterPins;
}.

