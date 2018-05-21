Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Require Import FIFOF.
Definition isMul (func: MulDivFunc): bool := 
                Ret null

.

Definition isDiv (func: MulDivFunc): bool := 
                Ret null

.

(* * interface Multiplier#(xlen) *)
Record Multiplier (xlen : nat) := {
    Multiplier'interface: Modules;
    Multiplier'multiply : string;
    Multiplier'result_rdy : string;
    Multiplier'result_data : string;
    Multiplier'result_deq : string;
}.

(* * interface Divider#(xlen) *)
Record Divider (xlen : nat) := {
    Divider'interface: Modules;
    Divider'divide : string;
    Divider'result_rdy : string;
    Divider'result_data : string;
    Divider'result_deq : string;
}.

(* * interface MulDivExec#(xlen) *)
Record MulDivExec (xlen : nat) := {
    MulDivExec'interface: Modules;
    MulDivExec'exec : string;
    MulDivExec'notEmpty : string;
    MulDivExec'result_rdy : string;
    MulDivExec'result_data : string;
    MulDivExec'result_deq : string;
}.

Module mkBluesimMultiplier.
    Section Section'mkBluesimMultiplier.
    Variable xlen : Kind.
    Variable instancePrefix: string.
(* FIXME: interface FIFOF subinterface deq *)
    Let result_fifoenq := MethodSig (FIFOF'enq result_fifo) (element_type) : Void.
(* FIXME: interface FIFOF subinterface first *)
(* FIXME: interface FIFOF subinterface notEmpty *)
                           Let result_fifo := mkSizedFIFOF (instancePrefix--"result_fifo").
    Definition mkBluesimMultiplierModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance result_fifo :: nil))
       with Method2 instancePrefix--"multiply" (multiplicand : (Bit (TAdd xlen 1))) (multiplier : (Bit (TAdd xlen 1))) : Void :=
LET a <- ;
LET b <- ;
LET r <- ;
LET answer <- ;
 result_fifoenq(#answer);
        Retv

       with Method instancePrefix--"result_rdy" () : Bool :=
#result_fifo

       with Method instancePrefix--"result_data" () : (Tuple2 (Bit xlen) (Bit xlen)) :=
#result_fifo

       with Method instancePrefix--"result_deq" () : Void :=
#result_fifo;
        Retv

    }). (* mkBluesimMultiplier *)

    Definition mkBluesimMultiplier := Build_Multiplier xlen mkBluesimMultiplierModule%kami (instancePrefix--"multiply") (instancePrefix--"result_data") (instancePrefix--"result_deq") (instancePrefix--"result_rdy").
    End Section'mkBluesimMultiplier.
End mkBluesimMultiplier.

Module mkBoothMultiplier.
    Section Section'mkBoothMultiplier.
    Variable xlen : Kind.
    Variable instancePrefix: string.
                        