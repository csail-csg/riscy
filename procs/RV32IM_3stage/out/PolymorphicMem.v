Require Import Bool String List Arith.
Require Import Omega.
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
Module module'mkPolymorphicBRAM.
    Section Section'mkPolymorphicBRAM.
    Variable reqT : Kind.
    Variable respT : Kind.
    Variable instancePrefix: string.
    Variable numWords: nat.
            Definition mkPolymorphicBRAMModule: Modules.
        refine  (BKMODULE {
                   Call _m : tvar607 <-  mkPolymorphicBRAMLoad($numWords, STRUCT {  "$tag" ::= $0; "LfBinary" ::= $0; "LfHex" ::= $0; "LfNone" ::= $0 })
       with         Ret #_m
    }); abstract omega. Qed. (* mkPolymorphicBRAM *)

(* Module mkPolymorphicBRAM type Integer -> Module#(ServerPort#(reqT, respT)) return type ServerPort#(reqT, respT) *)
    Definition mkPolymorphicBRAM := Build_ServerPort (reqT) (respT) mkPolymorphicBRAMModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkPolymorphicBRAM.
End module'mkPolymorphicBRAM.

Definition mkPolymorphicBRAM := module'mkPolymorphicBRAM.mkPolymorphicBRAM.

