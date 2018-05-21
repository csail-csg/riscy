Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition addrCalc (rVal1: word xlen) (imm: Maybe word xlen): (word xlen) := 
                Ret (+ #rVal1  fromMaybe($0, #imm))

.

