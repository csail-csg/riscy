Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition execControl (brFunc: BrFunc) (rVal1: Bit xlen) (rVal2: Bit xlen) (imm: Maybe Bit xlen) (pc: Bit xlen): (Bit xlen) := 
        CallM taken : bool <-  aluBr(#brFunc, #rVal1, #rVal2)

        CallM targetPc : (Bit xlen) <-  brAddrCalc(#brFunc, #pc, #rVal1,  fromMaybe(null, #imm))

                Ret #taken#targetPc(+ #pc $4)

.

Definition aluBr (brFunc: BrFunc) (a: Bit xlen) (b: Bit xlen): bool := 
                LET eq : bool <- (== #a #b)

        CallM lt : bool <-  signedLT(#a, #b)

                LET ltu : bool <- (bitlt #a #b)

                LET brTaken : bool <- null

                Ret #brTaken

.

Definition brAddrCalc (brFunc: BrFunc) (pc: Bit xlen) (val: Bit xlen) (imm: Bit xlen): (Bit xlen) := 
                LET in1 : (Bit xlen) <- (== #brFunc BrJalr)#val#pc

                LET addOut : (Bit xlen) <- (+ #in1 #imm)

                LET targetAddr : (Bit xlen) <- (== #brFunc BrJalr)(& #addOut ~$1)#addOut

                Ret #targetAddr

.

