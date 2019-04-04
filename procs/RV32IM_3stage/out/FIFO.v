Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface FIFO#(element_type) *)
Record FIFO (element_type : Kind) := {
    FIFO'modules: Modules;
    FIFO'first : string;
    FIFO'enq : string;
    FIFO'deq : string;
    FIFO'clear : string;
}.

Module module'mkFIFO.
    Section Section'mkFIFO.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable esz: nat.
                               Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkFIFOModule: Modules.
        refine  (BKMODULE {
           Register v : element_type <- Default
       with Register valid : Bit 0 <- $0
       with Method instancePrefix--"first" () : element_type :=
        Read v_v : element_type <- "v";        Ret #v_v

       with Method instancePrefix--"enq" (new_v : element_type) : Void :=
        Write v : element_type <- #new_v;
        Write valid : Bit 0 <- $1;
        Retv

       with Method instancePrefix--"deq" () : Void :=
        Write valid : Bit 0 <- $0;
        Retv

       with Method instancePrefix--"clear" () : Void :=
        Write valid : Bit 0 <- $0;
        Retv

    }); abstract omega. Qed. (* mkFIFO *)

(* Module mkFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO := Build_FIFO (element_type) mkFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkFIFO.
End module'mkFIFO.

Definition mkFIFO := module'mkFIFO.mkFIFO.

Module module'mkFIFO1.
    Section Section'mkFIFO1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                               Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkFIFO1Module: Modules :=
         (BKMODULE {
           Register v : element_type <- Default
       with Register valid : Bit 0 <- $0
       with Method instancePrefix--"first" () : element_type :=
        Read v_v : element_type <- "v";        Ret #v_v

       with Method instancePrefix--"enq" (new_v : element_type) : Void :=
        Write v : element_type <- #new_v;
        Write valid : Bit 0 <- $1;
        Retv

       with Method instancePrefix--"deq" () : Void :=
        Write valid : Bit 0 <- $0;
        Retv

       with Method instancePrefix--"clear" () : Void :=
        Write valid : Bit 0 <- $0;
        Retv

    }). (* mkFIFO1 *)

(* Module mkFIFO1 type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO1 := Build_FIFO (element_type) mkFIFO1Module%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkFIFO1.
End module'mkFIFO1.

Definition mkFIFO1 := module'mkFIFO1.mkFIFO1.

Module module'mkSizedFIFO.
    Section Section'mkSizedFIFO.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
                               Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkSizedFIFOModule: Modules :=
         (BKMODULE {
           Register v : element_type <- Default
       with Register valid : Bit 0 <- $0
       with Method instancePrefix--"first" () : element_type :=
        Read v_v : element_type <- "v";        Ret #v_v

       with Method instancePrefix--"enq" (new_v : element_type) : Void :=
        Write v : element_type <- #new_v;
        Write valid : Bit 0 <- $1;
        Retv

       with Method instancePrefix--"deq" () : Void :=
        Write valid : Bit 0 <- $0;
        Retv

       with Method instancePrefix--"clear" () : Void :=
        Write valid : Bit 0 <- $0;
        Retv

    }). (* mkSizedFIFO *)

(* Module mkSizedFIFO type Integer -> Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkSizedFIFO := Build_FIFO (element_type) mkSizedFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkSizedFIFO.
End module'mkSizedFIFO.

Definition mkSizedFIFO := module'mkSizedFIFO.mkSizedFIFO.

