Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition execControl (brFunc: BrFunc) (rVal1: word xlen) (rVal2: word xlen) (imm: Maybe word xlen) (pc: word xlen): (word xlen) := 
        LET taken <- 

        LET targetPc <- 

                Ret #taken#targetPc(+ #pc $4)

.

Definition aluBr (brFunc: BrFunc) (a: word xlen) (b: word xlen): bool := 
                LET eq : bool <- (== #a #b)

        LET lt <- 

                LET ltu : bool <- (bitlt #a #b)

                LET brTaken : bool <- null

                Ret #brTaken

.

Definition brAddrCalc (brFunc: BrFunc) (pc: word xlen) (val: word xlen) (imm: word xlen): (word xlen) := 
                LET in1 : (word xlen) <- (== #brFunc #BrJalr)#val#pc

                LET addOut : (word xlen) <- (+ #in1 #imm)

                LET targetAddr : (word xlen) <- (== #brFunc #BrJalr)(& #addOut ~$1)#addOut

                Ret #targetAddr

.

