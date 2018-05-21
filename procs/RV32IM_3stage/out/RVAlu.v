Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition alu64 (func: AluFunc) (w: bool) (a: word 64) (b: word 64): (word 64) := 
                If #w
        then                 BKSTMTS {
                Assign a = (== #func #AluSra) signExtend(#a[$31 : $0]) zeroExtend(#a[$31 : $0])
        with         Assign b =  zeroExtend(#b[$31 : $0])
;
        Retv

        LET shamt : (word 6) <- (UniBit (Trunc 64 (6 - 64)) #b)

                If #w
        then                 BKSTMTS {
                Assign shamt = (BinBit (Concat 1 tvar1563) $1'b0 #shamt[$4 : $0])
;
        Retv

                LET res : (word 64) <- null

                If #w
        then                 BKSTMTS {
                Assign res =  signExtend(#res[$31 : $0])
;
        Retv

                Ret #res

.

Definition alu32 (func: AluFunc) (a: word 32) (b: word 32): (word 32) := 
        LET shamt : (word 5) <- (UniBit (Trunc 32 (5 - 32)) #b)

                LET res : (word 32) <- null

                Ret #res

.

