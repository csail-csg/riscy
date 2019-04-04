Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition addrCalc (rVal1: Bit xlen) (imm: Maybe Bit xlen): (Bit xlen) := 
                Ret (+ #rVal1  fromMaybe($0, #imm))

.

