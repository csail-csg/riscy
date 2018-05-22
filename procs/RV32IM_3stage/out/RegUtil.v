Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Module mkCSRReg.
    Section Section'mkCSRReg.
    Variable asz : nat.
    Variable instancePrefix: string.
                   Let r : string := instancePrefix--"r".
    Definition mkCSRRegModule :=
        (BKMODULE {
           Register r : Bit asz <- $0
       with Method instancePrefix--"_read" () : (Bit asz) :=
        Read r_v : Bit asz <- "r";        Ret #r_v

       with Method instancePrefix--"_write" (v : (Bit asz)) : Void :=
        Write r : Bit asz <- #v;
        Retv

    }). (* mkCSRReg *)

    Definition mkCSRReg := Build_Reg asz mkCSRRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkCSRReg.
End mkCSRReg.

Module truncateReg.
    Section Section'truncateReg.
    Variable k : Kind.
    Variable n : Kind.
    Variable instancePrefix: string.
    Variable r: (Reg (word k)).
            Definition truncateRegModule :=
        (BKMODULE {
           Method instancePrefix--"_read" () : (Bit n) :=
        Read r_v : Bit k <- "r";LET v : (Bit n) <- (UniBit (Trunc k (n - k)) #r_v);
        Ret #v

       with Method instancePrefix--"_write" (x : (Bit n)) : Void :=
        Read r_v : Bit k <- "r";LET vmsb : (Bit m) <- (UniBit (TruncLsb k (m - k)) #r_v);
        LET v : (Bit (TAdd n m)) <- (BinBit (Concat m n) #vmsb #x);
        Write r : Bit k <- #v;
        Retv

    }). (* truncateReg *)

    Definition truncateReg := Build_Reg k n truncateRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'truncateReg.
End truncateReg.

Module truncateRegLSB.
    Section Section'truncateRegLSB.
    Variable m : Kind.
    Variable n : Kind.
    Variable instancePrefix: string.
    Variable r: (Reg (word m)).
        