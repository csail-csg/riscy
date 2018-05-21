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

Module mkCSRReg.
    Section Section'mkCSRReg.
    Variable asz : nat.
    Variable instancePrefix: string.
                   Let r : string := instancePrefix--"r".
    Definition mkCSRRegModule :=
        (BKMODULE {
           Register r : Bit asz <- $0
       with Method instancePrefix--"read" () : (Bit asz) :=
        Read r_v : Bit asz <- "r";        Ret #r_v

       with Method instancePrefix--"write" (v : (Bit asz)) : Void :=
        Write r : Bit asz <- #v;
        Retv

    }). (* mkCSRReg *)

    Definition mkCSRReg := Build_CSRReg asz mkCSRRegModule%kami (instancePrefix--"read") (instancePrefix--"write").
    End Section'mkCSRReg.
End mkCSRReg.

Module truncateReg.
    Section Section'truncateReg.
    Variable m : Kind.
    Variable n : Kind.
    Variable instancePrefix: string.
    Variable r: (Reg (word (TAdd n m))).
            Definition truncateRegModule :=
        (BKMODULE {
           Method instancePrefix--"read" () : (Bit n) :=
        Read r_v : Bit TAdd n m <- "r";LET v : (Bit n) <- (UniBit (Trunc TAdd#(n, m) (n - TAdd#(n, m))) #r_v);
        Ret #v

       with Method instancePrefix--"write" (x : (Bit n)) : Void :=
        Read r_v : Bit TAdd n m <- "r";LET vmsb : (Bit m) <- (UniBit (TruncLsb TAdd#(n, m) (m - TAdd#(n, m))) #r_v);
        LET v : (Bit (TAdd n m)) <- (BinBit (Concat m n) #vmsb #x);
        Write r : Bit TAdd n m <- #v;
        Retv

    }). (* truncateReg *)

    Definition truncateReg := Build_CSRReg m n truncateRegModule%kami (instancePrefix--"read") (instancePrefix--"write").
    End Section'truncateReg.
End truncateReg.

Module truncateRegLSB.
    Section Section'truncateRegLSB.
    Variable m : Kind.
    Variable n : Kind.
    Variable instancePrefix: string.
    Variable r: (Reg (word m)).
        