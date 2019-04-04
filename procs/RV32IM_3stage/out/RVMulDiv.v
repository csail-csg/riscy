Require Import Bool String List Arith.
Require Import Omega.
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
    Multiplier'modules: Modules;
    Multiplier'multiply : string;
    Multiplier'result_rdy : string;
    Multiplier'result_data : string;
    Multiplier'result_deq : string;
}.

(* * interface Divider#(xlen) *)
Record Divider (xlen : nat) := {
    Divider'modules: Modules;
    Divider'divide : string;
    Divider'result_rdy : string;
    Divider'result_data : string;
    Divider'result_deq : string;
}.

(* * interface MulDivExec#(xlen) *)
Record MulDivExec (xlen : nat) := {
    MulDivExec'modules: Modules;
    MulDivExec'exec : string;
    MulDivExec'notEmpty : string;
    MulDivExec'result_rdy : string;
    MulDivExec'result_data : string;
    MulDivExec'result_deq : string;
}.

Module module'mkBluesimMultiplier.
    Section Section'mkBluesimMultiplier.
    Variable xlen : Kind.
    Variable instancePrefix: string.
        