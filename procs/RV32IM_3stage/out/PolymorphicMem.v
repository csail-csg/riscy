Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RegFile.
Require Import Vector.
Require Import FIFOG.
Require Import GenericAtomicMem.
Require Import Port.
Module mkPolymorphicBRAM.
    Section Section'mkPolymorphicBRAM.
    Variable reqT : Kind.
    Variable respT : Kind.
    Variable instancePrefix: string.
    Variable numWords: nat.
            Definition mkPolymorphicBRAMModule :=
        (BKMODULE {
                   Call _m : tvar601 <-  mkPolymorphicBRAMLoad($numWords, STRUCT {  "$tag" ::= $0; "LfBinary" ::= $0; "LfHex" ::= $0; "LfNone" ::= $0 })
       with         Ret #_m
    }). (* mkPolymorphicBRAM *)

    Definition mkPolymorphicBRAM := Build_ServerPort reqT respT mkPolymorphicBRAMModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkPolymorphicBRAM.
End mkPolymorphicBRAM.

