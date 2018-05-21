Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface BRAM_PORT#(addr, data) *)
Record BRAM_PORT (addr : Kind) (data : Kind) := {
    BRAM_PORT'interface: Modules;
    BRAM_PORT'put : string;
    BRAM_PORT'read : string;
}.

(* * interface BRAM_DUAL_PORT#(addr, data) *)
Record BRAM_DUAL_PORT (addr : Kind) (data : Kind) := {
    BRAM_DUAL_PORT'interface: Modules;
    BRAM_DUAL_PORT'a : (BRAM_PORT addr data);
    BRAM_DUAL_PORT'b : (BRAM_PORT addr data);
}.

(* * interface BRAM_PORT_BE#(addr, data, n) *)
Record BRAM_PORT_BE (addr : Kind) (data : Kind) (n : nat) := {
    BRAM_PORT_BE'interface: Modules;
    BRAM_PORT_BE'put : string;
    BRAM_PORT_BE'read : string;
}.

(* * interface BRAM_DUAL_PORT_BE#(addr, data, n) *)
Record BRAM_DUAL_PORT_BE (addr : Kind) (data : Kind) (n : nat) := {
    BRAM_DUAL_PORT_BE'interface: Modules;
    BRAM_DUAL_PORT_BE'a : (BRAM_PORT_BE addr data n);
    BRAM_DUAL_PORT_BE'b : (BRAM_PORT_BE addr data n);
}.

Module mkBRAMCore1.
    Section Section'mkBRAMCore1.
    Variable addr : Kind.
    Variable data : Kind.
    Variable instancePrefix: string.
    Variable memSize: nat.
    Variable hasOutputRegister: bool.
                   Let d : string := instancePrefix--"d".
    Definition mkBRAMCore1Module :=
        (BKMODULE {
           Register d : data <- Default
       with Method3 instancePrefix--"put" (write : Bool) (address : addr) (datain : data) : Void :=
        If #write
        then                 Write d : data <- #datain;
        Retv;
        Retv

       with Method instancePrefix--"read" () : data :=
        Read d_v : data <- "d";        Ret #d_v

    }). (* mkBRAMCore1 *)

    Definition mkBRAMCore1 := Build_BRAM_PORT addr data mkBRAMCore1Module%kami (instancePrefix--"put") (instancePrefix--"read").
    End Section'mkBRAMCore1.
End mkBRAMCore1.

