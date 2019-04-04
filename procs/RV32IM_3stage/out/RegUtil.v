Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Module module'mkCSRReg.
    Section Section'mkCSRReg.
    Variable asz : nat.
    Variable instancePrefix: string.
                   Let r : string := instancePrefix--"r".
    Definition mkCSRRegModule: Modules :=
         (BKMODULE {
           Register r : Bit asz <- $0
       with Method instancePrefix--"_read" () : (Bit asz) :=
        Read r_v : Bit asz <- "r";        Ret #r_v

       with Method instancePrefix--"_write" (v : (Bit asz)) : Void :=
        Write r : Bit asz <- #v;
        Retv

    }). (* mkCSRReg *)

(* Module mkCSRReg type Module#(Reg#(Bit#(asz))) return type Reg#(Bit#(asz)) *)
    Definition mkCSRReg := Build_Reg (Bit asz) mkCSRRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkCSRReg.
End module'mkCSRReg.

Definition mkCSRReg := module'mkCSRReg.mkCSRReg.

Module module'truncateReg.
    Section Section'truncateReg.
    Variable ksz : nat.
    Variable nsz : nat.
    Variable instancePrefix: string.
    Variable r: string.
    Variable msz: nat.
    Hypothesis HAdd: (ksz = nsz + msz)%nat.
    Hypothesis HMul: (ksz = nsz * msz)%nat.
    Hypothesis HDiv: (ksz = nsz / msz)%nat.
            Definition truncateRegModule: Modules.
        refine  (BKMODULE {
           Method instancePrefix--"_read" () : (Bit nsz) :=
        Read r_v : Bit ksz <- "r";LET v : (Bit nsz) <- UniBit (Trunc nsz (ksz - nsz)) (castBits _ _ _ _ #r_v);
        Ret #v

       with Method instancePrefix--"_write" (x : (Bit nsz)) : Void :=
        Read r_v : Bit ksz <- "r";LET vmsb : (Bit msz) <-  UniBit (TruncLsb (ksz - msz) msz) (castBits _ _ _ _ #r_v);
        LET v : (Bit ksz) <- castBits _ _ _ _ (BinBit (Concat msz nsz) #vmsb #x);
        Write r : Bit ksz <- #v;
        Retv

    }); abstract omega. Qed. (* truncateReg *)

(* Module truncateReg type Reg#(Bit#(ksz)) -> Module#(Reg#(Bit#(nsz))) return type Reg#(Bit#(nsz)) *)
    Definition truncateReg := Build_Reg (Bit nsz) truncateRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'truncateReg.
End module'truncateReg.

Definition truncateReg := module'truncateReg.truncateReg.

Module module'truncateRegLSB.
    Section Section'truncateRegLSB.
    Variable ksz : nat.
    Variable msz : nat.
    Variable instancePrefix: string.
    Variable r: string.
    Variable nsz: nat.
    Hypothesis HAdd: (ksz = nsz + msz)%nat.
            Definition truncateRegLSBModule: Modules.
        refine  (BKMODULE {
           Method instancePrefix--"_read" () : (Bit msz) :=
        Read r_v : Bit ksz <- "r";LET v : (Bit msz) <-  UniBit (TruncLsb (ksz - msz) msz) (castBits _ _ _ _ #r_v);
        Ret #v

       with Method instancePrefix--"_write" (x : (Bit msz)) : Void :=
        Read r_v : Bit ksz <- "r";LET lsb : (Bit nsz) <- UniBit (Trunc nsz (ksz - nsz)) (castBits _ _ _ _ #r_v);
        LET v : (Bit ksz) <- castBits _ _ _ _ (BinBit (Concat msz nsz) #x #lsb);
        Write r : Bit ksz <- #v;
        Retv

    }); abstract omega. Qed. (* truncateRegLSB *)

(* Module truncateRegLSB type Reg#(Bit#(ksz)) -> Module#(Reg#(Bit#(msz))) return type Reg#(Bit#(msz)) *)
    Definition truncateRegLSB := Build_Reg (Bit msz) truncateRegLSBModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'truncateRegLSB.
End module'truncateRegLSB.

Definition truncateRegLSB := module'truncateRegLSB.truncateRegLSB.

Module module'zeroExtendReg.
    Section Section'zeroExtendReg.
    Variable msz : nat.
    Variable nsz : nat.
    Variable instancePrefix: string.
    Variable r: string.
    Variable asz: nat.
    Hypothesis HAdd: (nsz = asz + msz)%nat.
            Definition zeroExtendRegModule: Modules.
        refine  (BKMODULE {
           Method instancePrefix--"_read" () : (Bit nsz) :=
        Read r_v : Bit msz <- "r";        LET z : (Bit asz) <- $0;
        LET v : (Bit nsz) <- castBits _ _ _ _ (BinBit (Concat asz msz) #z #r_v);
        Ret #v

       with Method instancePrefix--"_write" (x : (Bit nsz)) : Void :=
LET v : (Bit msz) <- UniBit (Trunc msz (nsz - msz)) (castBits _ _ _ _ #x);
        Write r : Bit msz <- #v;
        Retv

    }); abstract omega. Qed. (* zeroExtendReg *)

(* Module zeroExtendReg type Reg#(Bit#(msz)) -> Module#(Reg#(Bit#(nsz))) return type Reg#(Bit#(nsz)) *)
    Definition zeroExtendReg := Build_Reg (Bit nsz) zeroExtendRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'zeroExtendReg.
End module'zeroExtendReg.

Definition zeroExtendReg := module'zeroExtendReg.zeroExtendReg.

Module module'addReg.
    Section Section'addReg.
    Variable sz : nat.
    Variable instancePrefix: string.
    Variable areg: string.
    Variable breg: string.
            Definition addRegModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"_read" () : (Bit sz) :=
        Read areg_v : Bit sz <- "areg";        Read breg_v : Bit sz <- "breg";        Ret (#areg_v + #breg_v)

       with Method instancePrefix--"_write" (v : (Bit sz)) : Void :=
        Retv

    }). (* addReg *)

(* Module addReg type Reg#(Bit#(sz)) -> Reg#(Bit#(sz)) -> Module#(Reg#(Bit#(sz))) return type Reg#(Bit#(sz)) *)
    Definition addReg := Build_Reg (Bit sz) addRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'addReg.
End module'addReg.

Definition addReg := module'addReg.addReg.

Module module'mkReadOnlyReg.
    Section Section'mkReadOnlyReg.
    Variable t : Kind.
    Variable instancePrefix: string.
    Variable r: ConstT t.
            Definition mkReadOnlyRegModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"_read" () : t :=
        Ret $$r

       with Method instancePrefix--"_write" (x : t) : Void :=
        Retv

    }). (* mkReadOnlyReg *)

(* Module mkReadOnlyReg type t -> Module#(Reg#(t)) return type Reg#(t) *)
    Definition mkReadOnlyReg := Build_Reg (t) mkReadOnlyRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkReadOnlyReg.
End module'mkReadOnlyReg.

Definition mkReadOnlyReg := module'mkReadOnlyReg.mkReadOnlyReg.

