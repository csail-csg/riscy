Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface FIFOLevelIfc#(element_type, fifoDepth) *)
Record FIFOLevelIfc (element_type : Kind) (fifoDepth : nat) := {
    FIFOLevelIfc'modules: Modules;
    FIFOLevelIfc'enq : string;
    FIFOLevelIfc'deq : string;
    FIFOLevelIfc'first : string;
    FIFOLevelIfc'clear : string;
    FIFOLevelIfc'notFull : string;
    FIFOLevelIfc'notEmpty : string;
    FIFOLevelIfc'isLessThan : string;
    FIFOLevelIfc'isGreaterThan : string;
}.

