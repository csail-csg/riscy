Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFOF.
Require Import GetPut.
Require Import SpecialFIFOs.
Require Import RevertingVirtualReg.
(* * interface FIFOG#(t) *)
Record FIFOG (t : Kind) := {
    FIFOG'interface: Modules;
    FIFOG'enq : string;
    FIFOG'deq : string;
    FIFOG'first : string;
    FIFOG'clear : string;
    FIFOG'notFull : string;
    FIFOG'notEmpty : string;
    FIFOG'canEnq : string;
    FIFOG'canDeq : string;
}.

Module mkFIFOG.
    Section Section'mkFIFOG.
    Variable t : Kind.
    Variable instancePrefix: string.
            Definition mkFIFOGModule :=
        (BKMODULE {
                   Call _m : tvar369 <-  mkFIFOGfromFIFOF(#mkFIFOF)
       with         Ret #_m
    }). (* mkFIFOG *)

    Definition mkFIFOG := Build_FIFOG t mkFIFOGModule%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkFIFOG.
End mkFIFOG.

Module mkSizedFIFOG.
    Section Section'mkSizedFIFOG.
    Variable t : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
            Definition mkSizedFIFOGModule :=
        (BKMODULE {
                   Call _m : tvar372 <-  mkFIFOGfromFIFOF( mkSizedFIFOF($n))
       with         Ret #_m
    }). (* mkSizedFIFOG *)

    Definition mkSizedFIFOG := Build_FIFOG t mkSizedFIFOGModule%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkSizedFIFOG.
End mkSizedFIFOG.

Module mkFIFOG1.
    Section Section'mkFIFOG1.
    Variable t : Kind.
    Variable instancePrefix: string.
            Definition mkFIFOG1Module :=
        (BKMODULE {
                   Call _m : tvar374 <-  mkFIFOGfromFIFOF(#mkFIFOF1)
       with         Ret #_m
    }). (* mkFIFOG1 *)

    Definition mkFIFOG1 := Build_FIFOG t mkFIFOG1Module%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkFIFOG1.
End mkFIFOG1.

Module mkLFIFOG.
    Section Section'mkLFIFOG.
    Variable t : Kind.
    Variable instancePrefix: string.
            Definition mkLFIFOGModule :=
        (BKMODULE {
                   Call _m : tvar376 <-  mkFIFOGfromFIFOF(#mkLFIFOF)
       with         Ret #_m
    }). (* mkLFIFOG *)

    Definition mkLFIFOG := Build_FIFOG t mkLFIFOGModule%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkLFIFOG.
End mkLFIFOG.

Module mkBypassFIFOG.
    Section Section'mkBypassFIFOG.
    Variable t : Kind.
    Variable instancePrefix: string.
            Definition mkBypassFIFOGModule :=
        (BKMODULE {
                   Call _m : tvar378 <-  mkFIFOGfromFIFOF(#mkBypassFIFOF)
       with         Ret #_m
    }). (* mkBypassFIFOG *)

    Definition mkBypassFIFOG := Build_FIFOG t mkBypassFIFOGModule%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkBypassFIFOG.
End mkBypassFIFOG.

Module mkPipelineFIFOG.
    Section Section'mkPipelineFIFOG.
    Variable t : Kind.
    Variable instancePrefix: string.
            Definition mkPipelineFIFOGModule :=
        (BKMODULE {
                   Call _m : tvar380 <-  mkFIFOGfromFIFOF(#mkPipelineFIFOF)
       with         Ret #_m
    }). (* mkPipelineFIFOG *)

    Definition mkPipelineFIFOG := Build_FIFOG t mkPipelineFIFOGModule%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkPipelineFIFOG.
End mkPipelineFIFOG.

Module mkFIFOGfromFIFOF.
    Section Section'mkFIFOGfromFIFOF.
    Variable m : Kind.
    Variable t : Kind.
    Variable instancePrefix: string.
    Variable mkM: (m (FIFOF t)).
(* FIXME: interface FIFOF subinterface clear *)
(* FIXME: interface FIFOF subinterface deq *)
    Let _menq := MethodSig (FIFOF'enq _m) (element_type) : Void.
(* FIXME: interface FIFOF subinterface first *)
(* FIXME: interface FIFOF subinterface notEmpty *)
(* FIXME: interface FIFOF subinterface notFull *)
                                                                   Let _m := mkM (instancePrefix--"_m").
       Let canEnq_wire := mkBypassWire (instancePrefix--"canEnq_wire").
       Let canDeq_wire := mkBypassWire (instancePrefix--"canDeq_wire").
       Let virtualEnqReg : string := instancePrefix--"virtualEnqReg".
       Let virtualDeqReg : string := instancePrefix--"virtualDeqReg".
    Definition mkFIFOGfromFIFOFModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance _m :: nil))
       with (BKMod (FIXME'InterfaceName'instance canEnq_wire :: nil))
       with (BKMod (FIXME'InterfaceName'instance canDeq_wire :: nil))
       with Register virtualEnqReg : Bool <-  mkRevertingVirtualReg(#True)
       with Register virtualDeqReg : Bool <-  mkRevertingVirtualReg(#True)
       with Rule instancePrefix--"setCanEnqWire" :=
               Write canEnq_wire : Bool <- #_m;
        Retv (* rule setCanEnqWire *)
       with Rule instancePrefix--"setCanDeqWire" :=
               Write canDeq_wire : Bool <- #_m;
        Retv (* rule setCanDeqWire *)
       with Method instancePrefix--"enq" (x : t) : Void :=
 _menq(#x);
        Write virtualEnqReg : Bool <- #False;
        Retv

       with Method instancePrefix--"deq" () : Void :=
#_m;
        Write virtualDeqReg : Bool <- #False;
        Retv

       with Method instancePrefix--"first" () : t :=
#_m

       with Method instancePrefix--"clear" () : Void :=
#_m;
        Retv

       with Method instancePrefix--"notFull" () : Bool :=
#_m

       with Method instancePrefix--"notEmpty" () : Bool :=
#_m

       with Method instancePrefix--"canEnq" () : Bool :=
#canEnq_wire

       with Method instancePrefix--"canDeq" () : Bool :=
#canDeq_wire

    }). (* mkFIFOGfromFIFOF *)

    Definition mkFIFOGfromFIFOF := Build_FIFOG m t mkFIFOGfromFIFOFModule%kami (instancePrefix--"canDeq") (instancePrefix--"canEnq") (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkFIFOGfromFIFOF.
End mkFIFOGfromFIFOF.

