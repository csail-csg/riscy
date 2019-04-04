Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface FIFOF#(element_type) *)
Record FIFOF (element_type : Kind) := {
    FIFOF'modules: Modules;
    FIFOF'first : string;
    FIFOF'enq : string;
    FIFOF'deq : string;
    FIFOF'notEmpty : string;
    FIFOF'notFull : string;
    FIFOF'clear : string;
}.

Module module'mkLFIFOF.
    Section Section'mkLFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkLFIFOFModule: Modules :=
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

       with Method instancePrefix--"notEmpty" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $0)

       with Method instancePrefix--"notFull" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $1)

    }). (* mkLFIFOF *)

(* Module mkLFIFOF type Module#(FIFOF#(element_type)) return type FIFOF#(element_type) *)
    Definition mkLFIFOF := Build_FIFOF (element_type) mkLFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkLFIFOF.
End module'mkLFIFOF.

Definition mkLFIFOF := module'mkLFIFOF.mkLFIFOF.

Module module'mkFIFOF1.
    Section Section'mkFIFOF1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkFIFOF1Module: Modules :=
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

       with Method instancePrefix--"notEmpty" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $0)

       with Method instancePrefix--"notFull" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $1)

    }). (* mkFIFOF1 *)

(* Module mkFIFOF1 type Module#(FIFOF#(element_type)) return type FIFOF#(element_type) *)
    Definition mkFIFOF1 := Build_FIFOF (element_type) mkFIFOF1Module%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkFIFOF1.
End module'mkFIFOF1.

Definition mkFIFOF1 := module'mkFIFOF1.mkFIFOF1.

Module module'mkUGFIFOF.
    Section Section'mkUGFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable width_any: nat.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkUGFIFOFModule: Modules.
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

       with Method instancePrefix--"notEmpty" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $0)

       with Method instancePrefix--"notFull" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $1)

    }); abstract omega. Qed. (* mkUGFIFOF *)

(* Module mkUGFIFOF type Module#(FIFOF#(element_type)) return type FIFOF#(element_type) *)
    Definition mkUGFIFOF := Build_FIFOF (element_type) mkUGFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkUGFIFOF.
End module'mkUGFIFOF.

Definition mkUGFIFOF := module'mkUGFIFOF.mkUGFIFOF.

Module module'mkUGFIFO1.
    Section Section'mkUGFIFO1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable width_any: nat.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkUGFIFO1Module: Modules.
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

       with Method instancePrefix--"notEmpty" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $0)

       with Method instancePrefix--"notFull" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $1)

    }); abstract omega. Qed. (* mkUGFIFO1 *)

(* Module mkUGFIFO1 type Module#(FIFOF#(element_type)) return type FIFOF#(element_type) *)
    Definition mkUGFIFO1 := Build_FIFOF (element_type) mkUGFIFO1Module%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkUGFIFO1.
End module'mkUGFIFO1.

Definition mkUGFIFO1 := module'mkUGFIFO1.mkUGFIFO1.

Module module'mkUGSizedFIFOF.
    Section Section'mkUGSizedFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
    Variable width_any: nat.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkUGSizedFIFOFModule: Modules.
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

       with Method instancePrefix--"notEmpty" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $0)

       with Method instancePrefix--"notFull" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $1)

    }); abstract omega. Qed. (* mkUGSizedFIFOF *)

(* Module mkUGSizedFIFOF type Integer -> Module#(FIFOF#(element_type)) return type FIFOF#(element_type) *)
    Definition mkUGSizedFIFOF := Build_FIFOF (element_type) mkUGSizedFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkUGSizedFIFOF.
End module'mkUGSizedFIFOF.

Definition mkUGSizedFIFOF := module'mkUGSizedFIFOF.mkUGSizedFIFOF.

Module module'mkSizedFIFOF.
    Section Section'mkSizedFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
    Variable width_any: nat.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkSizedFIFOFModule: Modules.
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

       with Method instancePrefix--"notEmpty" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $0)

       with Method instancePrefix--"notFull" () : Bool :=
        Read valid_v : Bit 0 <- "valid";        Ret (#valid_v != $1)

    }); abstract omega. Qed. (* mkSizedFIFOF *)

(* Module mkSizedFIFOF type Integer -> Module#(FIFOF#(element_type)) return type FIFOF#(element_type) *)
    Definition mkSizedFIFOF := Build_FIFOF (element_type) mkSizedFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkSizedFIFOF.
End module'mkSizedFIFOF.

Definition mkSizedFIFOF := module'mkSizedFIFOF.mkSizedFIFOF.

