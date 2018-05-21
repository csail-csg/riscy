Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Counter#(sz) *)
Record Counter (sz : nat) := {
    Counter'interface: Modules;
    Counter'up : string;
    Counter'down : string;
    Counter'dec : string;
    Counter'inc : string;
    Counter'setF : string;
    Counter'clear : string;
    Counter'value : string;
}.

Module mkCounter.
    Section Section'mkCounter.
    Variable sz : nat.
    Variable instancePrefix: string.
    Variable init: nat.
                                       Let counter : string := instancePrefix--"counter".
    Definition mkCounterModule :=
        (BKMODULE {
           Register counter : Bit sz <- $init
       with Method instancePrefix--"dec" (v : (Bit sz)) : Void :=
        Read counter_v : Bit sz <- "counter";        Write counter : Bit sz <- (#counter_v - #v);
        Retv

       with Method instancePrefix--"up" () : Void :=
        Read counter_v : Bit sz <- "counter";        Write counter : Bit sz <- (#counter_v + $1);
        Retv

       with Method instancePrefix--"down" () : Void :=
        Read counter_v : Bit sz <- "counter";        Write counter : Bit sz <- (#counter_v - $1);
        Retv

       with Method instancePrefix--"inc" (v : (Bit sz)) : Void :=
        Read counter_v : Bit sz <- "counter";        Write counter : Bit sz <- (#counter_v + #v);
        Retv

       with Method instancePrefix--"setF" (v : (Bit sz)) : Void :=
        Write counter : Bit sz <- #v;
        Retv

       with Method instancePrefix--"clear" () : Void :=
        Write counter : Bit sz <- $init;
        Retv

       with Method instancePrefix--"value" () : (Bit sz) :=
        Read counter_v : Bit sz <- "counter";        Ret #counter_v

    }). (* mkCounter *)

    Definition mkCounter := Build_Counter sz mkCounterModule%kami (instancePrefix--"clear") (instancePrefix--"dec") (instancePrefix--"down") (instancePrefix--"inc") (instancePrefix--"setF") (instancePrefix--"up") (instancePrefix--"value").
    End Section'mkCounter.
End mkCounter.

