Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition alu64 (func: AluFunc) (w: bool) (a: Bit 64) (b: Bit 64): (Bit 64) := 
                If #w
        then                 BKSTMTS {
                Assign a = (== #func AluSra) signExtend(#a$[31:0]@64) zeroExtend(#a$[31:0]@64)
        with         Assign b =  zeroExtend(#b$[31:0]@64)
;
        Retv

        LET shamt : (Bit 6) <- UniBit (Trunc 6 (64 - 6)) (castBits _ _ _ _ #b)

                If #w
        then                 BKSTMTS {
                Assign shamt = castBits _ _ _ _ (BinBit (Concat 1 tvar1603) $0 #shamt$[4:0]@6)
;
        Retv

                LET res : (Bit 64) <- null

                If #w
        then                 BKSTMTS {
                Assign res =  signExtend(#res$[31:0]@64)
;
        Retv

                Ret #res

.

Definition alu32 (func: AluFunc) (a: Bit 32) (b: Bit 32): (Bit 32) := 
        LET shamt : (Bit 5) <- UniBit (Trunc 5 (32 - 5)) (castBits _ _ _ _ #b)

                LET res : (Bit 32) <- null

                Ret #res

.

