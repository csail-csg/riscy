Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

(* * interface CSRReg#(a) *)
Record CSRReg (a : Kind) := {
    CSRReg'interface: Modules;
    CSRReg'read : string;
    CSRReg'write : string;
}.

Module truncateReg.
    Section Section'truncateReg.
    Variable n : nat.
    Variable m : nat.
    Variable instancePrefix: string.
    Variable r: string.
            Definition truncateRegModule :=
        (BKMODULE {
           Method instancePrefix--"read" () : (Bit n) :=
             (Read r_v : Bit (n + m) <- r;
              LET v : Bit n <-  (UniBit (Trunc n m) #r_v);
              Ret #v)

       with Method instancePrefix--"write" (x : (Bit n)) : Void :=
               Read r_v : Bit (n + m) <- r;
           LET msb : (Bit m) <- (UniBit (TruncLsb n m) #r_v); 
           LET v : Bit (n + m) <-  (BinBit (Concat m n) #msb #x);
           Write r : Bit (n + m) <- #v;
           Retv

    }). (* truncateReg *)

    Definition truncateReg := Build_CSRReg (Bit n) truncateRegModule%kami (instancePrefix--"read") (instancePrefix--"write").
    End Section'truncateReg.
End truncateReg.
