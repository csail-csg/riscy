Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface FIFOF#(element_type) *)
Record FIFOF (element_type : Kind) := {
    FIFOF'interface: Modules;
    FIFOF'first : string;
    FIFOF'enq : string;
    FIFOF'deq : string;
    FIFOF'notEmpty : string;
    FIFOF'notFull : string;
    FIFOF'clear : string;
}.

Module mkLFIFOF.
    Section Section'mkLFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkLFIFOFModule :=
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

    Definition mkLFIFOF := Build_FIFOF element_type mkLFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkLFIFOF.
End mkLFIFOF.

Module mkFIFOF1.
    Section Section'mkFIFOF1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkFIFOF1Module :=
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

    Definition mkFIFOF1 := Build_FIFOF element_type mkFIFOF1Module%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkFIFOF1.
End mkFIFOF1.

Module mkUGFIFOF.
    Section Section'mkUGFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkUGFIFOFModule :=
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

    }). (* mkUGFIFOF *)

    Definition mkUGFIFOF := Build_FIFOF element_type mkUGFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkUGFIFOF.
End mkUGFIFOF.

Module mkUGFIFO1.
    Section Section'mkUGFIFO1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkUGFIFO1Module :=
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

    }). (* mkUGFIFO1 *)

    Definition mkUGFIFO1 := Build_FIFOF element_type mkUGFIFO1Module%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkUGFIFO1.
End mkUGFIFO1.

Module mkUGSizedFIFOF.
    Section Section'mkUGSizedFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkUGSizedFIFOFModule :=
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

    }). (* mkUGSizedFIFOF *)

    Definition mkUGSizedFIFOF := Build_FIFOF element_type mkUGSizedFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkUGSizedFIFOF.
End mkUGSizedFIFOF.

Module mkSizedFIFOF.
    Section Section'mkSizedFIFOF.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
                                       Let v : string := instancePrefix--"v".
       Let valid : string := instancePrefix--"valid".
    Definition mkSizedFIFOFModule :=
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

    }). (* mkSizedFIFOF *)

    Definition mkSizedFIFOF := Build_FIFOF element_type mkSizedFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkSizedFIFOF.
End mkSizedFIFOF.

