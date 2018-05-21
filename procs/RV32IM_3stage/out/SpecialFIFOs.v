Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import FIFOF.
Require Import FIFOLevel.
Require Import RevertingVirtualReg.
Module mkPipelineFIFO.
    Section Section'mkPipelineFIFO.
    Variable a : Kind.
    Variable instancePrefix: string.
(* FIXME: interface FIFOF subinterface clear *)
(* FIXME: interface FIFOF subinterface deq *)
    Let _ifcenq := MethodSig (FIFOF'enq _ifc) (element_type) : Void.
(* FIXME: interface FIFOF subinterface first *)
                           Let _ifc := mkPipelineFIFOF (instancePrefix--"_ifc").
    Definition mkPipelineFIFOModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance _ifc :: nil))
       with Method instancePrefix--"enq" () :  :=
#_ifc

       with Method instancePrefix--"deq" () :  :=
#_ifc

       with Method instancePrefix--"first" () :  :=
#_ifc

       with Method instancePrefix--"clear" () :  :=
#_ifc

    }). (* mkPipelineFIFO *)

    Definition mkPipelineFIFO := Build_FIFO a mkPipelineFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkPipelineFIFO.
End mkPipelineFIFO.

Module mkPipelineFIFOF.
    Section Section'mkPipelineFIFOF.
    Variable a : Kind.
    Variable instancePrefix: string.
                                           Let rv : string := instancePrefix--"rv".
    Definition mkPipelineFIFOFModule :=
        (BKMODULE {
           Register rv : Maybe a <-  mkCReg($3, STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
       with LET enq_ok <- 
       with LET deq_ok <- 
       with Method instancePrefix--"notFull" () :  :=
#enq_ok

       with Method instancePrefix--"enq" (v : <nulltype>) : Void :=
        Write rv[$1] <- STRUCT {  "$tag" ::= $0; "Valid" ::= #v; "Invalid" ::= $0 };
        Retv

       with Method instancePrefix--"notEmpty" () :  :=
#deq_ok

       with Method instancePrefix--"deq" () : Void :=
        Write rv[$0] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv

       with Method instancePrefix--"first" () :  :=
        Ret #v

       with Method instancePrefix--"clear" () : Void :=
        Write rv[$2] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv

    }). (* mkPipelineFIFOF *)

    Definition mkPipelineFIFOF := Build_FIFOF a mkPipelineFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkPipelineFIFOF.
End mkPipelineFIFOF.

Module mkBypassFIFO.
    Section Section'mkBypassFIFO.
    Variable a : Kind.
    Variable instancePrefix: string.
(* FIXME: interface FIFOF subinterface clear *)
(* FIXME: interface FIFOF subinterface deq *)
    Let _ifcenq := MethodSig (FIFOF'enq _ifc) (element_type) : Void.
(* FIXME: interface FIFOF subinterface first *)
                           Let _ifc := mkBypassFIFOF (instancePrefix--"_ifc").
    Definition mkBypassFIFOModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance _ifc :: nil))
       with Method instancePrefix--"enq" () :  :=
#_ifc

       with Method instancePrefix--"deq" () :  :=
#_ifc

       with Method instancePrefix--"first" () :  :=
#_ifc

       with Method instancePrefix--"clear" () :  :=
#_ifc

    }). (* mkBypassFIFO *)

    Definition mkBypassFIFO := Build_FIFO a mkBypassFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkBypassFIFO.
End mkBypassFIFO.

Module mkBypassFIFOF.
    Section Section'mkBypassFIFOF.
    Variable a : Kind.
    Variable instancePrefix: string.
                                           Let rv : string := instancePrefix--"rv".
    Definition mkBypassFIFOFModule :=
        (BKMODULE {
           Register rv : Maybe a <-  mkCReg($3, STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 })
       with LET enq_ok <- 
       with LET deq_ok <- 
       with Method instancePrefix--"notFull" () :  :=
#enq_ok

       with Method instancePrefix--"enq" (v : <nulltype>) : Void :=
        Write rv[$0] <- STRUCT {  "$tag" ::= $0; "Valid" ::= #v; "Invalid" ::= $0 };
        Retv

       with Method instancePrefix--"notEmpty" () :  :=
#deq_ok

       with Method instancePrefix--"deq" () : Void :=
        Write rv[$1] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv

       with Method instancePrefix--"first" () :  :=
        Ret #v

       with Method instancePrefix--"clear" () : Void :=
        Write rv[$2] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv

    }). (* mkBypassFIFOF *)

    Definition mkBypassFIFOF := Build_FIFOF a mkBypassFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkBypassFIFOF.
End mkBypassFIFOF.

Module mkDFIFOF.
    Section Section'mkDFIFOF.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable dflt: a.
            Definition mkDFIFOFModule :=
        (BKMODULE {
                   Call _ifc : tvar278 <-  mkSizedDFIFOF($2, #dflt)
       with         Ret #_ifc
    }). (* mkDFIFOF *)

    Definition mkDFIFOF := Build_FIFOF a mkDFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkDFIFOF.
End mkDFIFOF.

Module mkSizedDFIFOF.
    Section Section'mkSizedDFIFOF.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
    Variable dflt: a.
(* FIXME: interface SCounter subinterface clear *)
(* FIXME: interface SCounter subinterface decr *)
(* FIXME: interface SCounter subinterface incr *)
    Let cntrisEq := MethodSig (SCounter'isEq cntr) (nat) : Bool.
    Let cntrset := MethodSig (SCounter'set cntr) (b) : Function Vector n Reg b Void.
    Let cntrsetNext := MethodSig (SCounter'setNext cntr) (b) : Function Vector n Reg b Void.
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
                                                                           Let cntr := mkSCounter (instancePrefix--"cntr").
       Let enqueueing := mkPulseWire (instancePrefix--"enqueueing").
       Let x_wire := mkWire (instancePrefix--"x_wire").
       Let dequeueing := mkPulseWire (instancePrefix--"dequeueing").
    Definition mkSizedDFIFOFModule :=
        (BKMODULE {
                   LET q : (Reg a)
       with     (BKBlock
      (let limit : nat := n
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        Assign q[i] <-  mkReg(#dflt)
        (loopM' m')
        end)
        n)))
       with (BKMod (FIXME'InterfaceName'instance cntr :: nil))
       with (BKMod (FIXME'InterfaceName'instance enqueueing :: nil))
       with (BKMod (FIXME'InterfaceName'instance x_wire :: nil))
       with (BKMod (FIXME'InterfaceName'instance dequeueing :: nil))
       with         Call empty : tvar280 <-  cntrisEq($0)
       with         Call full : tvar281 <-  cntrisEq($n)
       with Rule instancePrefix--"incCtr" :=
        Read q_v : a <- q;
        Assert((#enqueueing && !#dequeueing));
       #cntr;
        cntrsetNext(#x_wire, #q_v);
        Retv (* rule incCtr *)
       with Rule instancePrefix--"decCtr" :=
        Read q_v : a <- q;
        Assert((#dequeueing && !#enqueueing));
           (BKBlock
      (let limit : nat := n
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        Write q[$i] <- ($i == ($n - $1))#dflt#q_v[($i + $1)]
        (loopM' m')
        end)
        n)));
       #cntr;
        Retv (* rule decCtr *)
       with Rule instancePrefix--"both" :=
        Read q_v : a <- q;
        Assert((#dequeueing && #enqueueing));
           (BKBlock
      (let limit : nat := n
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        If ! cntrisEq(($i + $1))
        then                 Write q[$i] <- ($i == ($n - $1))#dflt#q_v[($i + $1)];
        Retv
        (loopM' m')
        end)
        n)));
        cntrset(#x_wire, #q_v);
        Retv (* rule both *)
       with Method instancePrefix--"deq" () : Void :=
        If !#empty
        then         #dequeueing;
        Retv;
        Retv

       with Method instancePrefix--"first" () :  :=
        Read q_v : a <- "q";        Ret #q_v[$0]

       with Method instancePrefix--"enq" (x : <nulltype>) : Void :=
#enqueueing;
        Write x_wire : a <- #x;
        Retv

       with Method instancePrefix--"notEmpty" () :  :=
!#empty

       with Method instancePrefix--"notFull" () :  :=
!#full

       with Method instancePrefix--"clear" () : Void :=
#cntr;
        Retv

    }). (* mkSizedDFIFOF *)

    Definition mkSizedDFIFOF := Build_FIFOF a mkSizedDFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkSizedDFIFOF.
End mkSizedDFIFOF.

(* * interface SCounter *)
Record SCounter := {
    SCounter'interface: Modules;
    SCounter'incr : string;
    SCounter'decr : string;
    SCounter'isEq : string;
    SCounter'setNext : string;
    SCounter'set : string;
    SCounter'clear : string;
}.

Module mkSCtr.
    Section Section'mkSCtr.
    Variable s : Kind.
    Variable instancePrefix: string.
    Variable c: (Reg (UInt s)).
                            Definition mkSCtrModule :=
        (BKMODULE {
           Method instancePrefix--"incr" () : Void :=
        Read c_v : UInt s <- "c";        Write c : UInt s <- (#c_v + $1);
        Retv

       with Method instancePrefix--"decr" () : Void :=
        Read c_v : UInt s <- "c";        Write c : UInt s <- (#c_v - $1);
        Retv

       with Method instancePrefix--"isEq" (n : <nulltype>) :  :=
        Read c_v : UInt s <- "c";(#c_v ==  fromInteger(#n))

       with Method2 instancePrefix--"setNext" (value : b) (as : (Vector n (Reg b))) : Void :=
        Read c_v : UInt s <- "c";        Write as[#c_v] <- #value;
        Retv

       with Method2 instancePrefix--"set" (value : b) (as : (Vector n (Reg b))) : Void :=
        Read c_v : UInt s <- "c";        Write as[(#c_v - $1)] <- #value;
        Retv

       with Method instancePrefix--"clear" () : Void :=
        Write c : UInt s <- $0;
        Retv

    }). (* mkSCtr *)

    Definition mkSCtr := Build_SCounter s mkSCtrModule%kami (instancePrefix--"clear") (instancePrefix--"decr") (instancePrefix--"incr") (instancePrefix--"isEq") (instancePrefix--"set") (instancePrefix--"setNext").
    End Section'mkSCtr.
End mkSCtr.

Module mkSCounter.
    Section Section'mkSCounter.
    Variable instancePrefix: string.
    Variable m: nat.
                Definition mkSCounterModule :=
        (BKMODULE {
                   LET _i : tvar312 = null
       with         If ($m < $2)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 1 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $4)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 2 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $8)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 3 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $16)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 4 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $32)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 5 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $64)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 6 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $128)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 7 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $256)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 8 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $512)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 9 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $1024)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 10 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $2048)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 11 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $4096)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 12 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $8192)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 13 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $16384)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 14 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $32768)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 15 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv
        else                 If ($m < $65536)
        then                 (BKBlock (
        let r : string := instancePrefix--"r" in
        BKSTMTS {
        Register r : UInt 16 <- $0
        with         Assign _i <-  mkSCtr(#r_v)
        }));
        Retv;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;;
        Retv;
       with         Ret #_i
    }). (* mkSCounter *)

    Definition mkSCounter := Build_SCounter mkSCounterModule%kami (instancePrefix--"clear") (instancePrefix--"decr") (instancePrefix--"incr") (instancePrefix--"isEq") (instancePrefix--"set") (instancePrefix--"setNext").
    End Section'mkSCounter.
End mkSCounter.

Module mkSizedBypassFIFOF.
    Section Section'mkSizedBypassFIFOF.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable n: nat.
(* FIXME: interface PulseWire subinterface send *)
    Let enqwwset := MethodSig (RWire'wset enqw) (element_type) : Void.
(* FIXME: interface FIFOF subinterface clear *)
(* FIXME: interface FIFOF subinterface deq *)
    Let ffenq := MethodSig (FIFOF'enq ff) (element_type) : Void.
(* FIXME: interface FIFOF subinterface first *)
(* FIXME: interface FIFOF subinterface notEmpty *)
(* FIXME: interface FIFOF subinterface notFull *)
                                                                       Let ff := mkUGSizedFIFOF (instancePrefix--"ff").
       Let enqw := mkRWire (instancePrefix--"enqw").
       Let firstValid : string := instancePrefix--"firstValid".
       Let dequeueing := mkPulseWire (instancePrefix--"dequeueing").
    Definition mkSizedBypassFIFOFModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance ff :: nil))
       with (BKMod (FIXME'InterfaceName'instance enqw :: nil))
       with Register firstValid : Bool <-  mkRevertingVirtualReg(#True)
       with (BKMod (FIXME'InterfaceName'instance dequeueing :: nil))
       with         LET empty : Bool = !#ff
       with         LET full : Bool = !#ff
       with         Call enqueueing : tvar331 <-  isValid(#enqw)
       with         LET bypassing : tvar331 = ((#enqueueing && #dequeueing) && #empty)
       with Rule instancePrefix--"enqueue" :=
        Assert((#enqueueing && !#bypassing));
        ffenq( validValue(#enqw));
        Retv (* rule enqueue *)
       with Rule instancePrefix--"dequeue" :=
        Assert((#dequeueing && !#empty));
       #ff;
        Retv (* rule dequeue *)
       with Method instancePrefix--"deq" () : Void :=
#dequeueing;
        Write firstValid : Bool <- #False;
        Retv

       with Method instancePrefix--"first" () :  :=
        Ret #empty validValue(#enqw)#ff

       with Method instancePrefix--"enq" (x : <nulltype>) : Void :=
 enqwwset(#x);
        Retv

       with Method instancePrefix--"clear" () : Void :=
#ff;
        Retv

       with Method instancePrefix--"notEmpty" () :  :=
#ff

       with Method instancePrefix--"notFull" () :  :=
#ff

    }). (* mkSizedBypassFIFOF *)

    Definition mkSizedBypassFIFOF := Build_FIFOF a mkSizedBypassFIFOFModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkSizedBypassFIFOF.
End mkSizedBypassFIFOF.

Module mkBypassFIFOLevel.
    Section Section'mkBypassFIFOLevel.
    Variable a : Kind.
    Variable fifoDepth : Kind.
    Variable instancePrefix: string.
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface FIFOF subinterface clear *)
(* FIXME: interface FIFOF subinterface deq *)
    Let fifofenq := MethodSig (FIFOF'enq fifof) (element_type) : Void.
(* FIXME: interface FIFOF subinterface first *)
(* FIXME: interface FIFOF subinterface notEmpty *)
(* FIXME: interface FIFOF subinterface notFull *)
                                                                                           Let fifof := mkSizedBypassFIFOF (instancePrefix--"fifof").
       Let count : string := instancePrefix--"count".
       Let levelsValidEnq : string := instancePrefix--"levelsValidEnq".
       Let levelsValidDeq : string := instancePrefix--"levelsValidDeq".
       Let levelsValidClr : string := instancePrefix--"levelsValidClr".
       Let do_enq := mkPulseWire (instancePrefix--"do_enq").
       Let do_deq := mkPulseWire (instancePrefix--"do_deq").
       Let do_clr := mkPulseWire (instancePrefix--"do_clr").
    Definition mkBypassFIFOLevelModule :=
        (BKMODULE {
                   LET ififoDepth : nat <- (null < $3) error((((null + null) +  integerToString(null)) + null))null
       with (BKMod (FIXME'InterfaceName'instance fifof :: nil))
       with Register count : UInt cntSize <- $0
       with Register levelsValidEnq : Bool <-  mkRevertingVirtualReg(#True)
       with Register levelsValidDeq : Bool <-  mkRevertingVirtualReg(#True)
       with Register levelsValidClr : Bool <-  mkRevertingVirtualReg(#True)
       with (BKMod (FIXME'InterfaceName'instance do_enq :: nil))
       with (BKMod (FIXME'InterfaceName'instance do_deq :: nil))
       with (BKMod (FIXME'InterfaceName'instance do_clr :: nil))
       with         LET levelsValid : Bool <- ((#levelsValidEnq_v && #levelsValidDeq_v) && #levelsValidClr_v)
       with Rule instancePrefix--"do_incr" :=
        Read count_v : UInt cntSize <- count;
        Assert(((#do_enq && !#do_deq) && !#do_clr));
               Write count : UInt cntSize <- (#count_v + $1);
        Retv (* rule do_incr *)
       with Rule instancePrefix--"do_decr" :=
        Read count_v : UInt cntSize <- count;
        Assert(((!#do_enq && #do_deq) && !#do_clr));
               Write count : UInt cntSize <- (#count_v - $1);
        Retv (* rule do_decr *)
       with Rule instancePrefix--"do_clear" :=
        Assert(#do_clr);
               Write count : UInt cntSize <- $0;
        Retv (* rule do_clear *)
       with Method instancePrefix--"enq" (value : a) : Void :=
 fifofenq(#value);
        Write levelsValidEnq : Bool <- #False;
#do_enq;
        Retv

       with Method instancePrefix--"deq" () : Void :=
#fifof;
        Write levelsValidDeq : Bool <- #False;
#do_deq;
        Retv

       with Method instancePrefix--"first" () :  :=
#fifof

       with Method instancePrefix--"clear" () : Void :=
#fifof;
        Write levelsValidClr : Bool <- #False;
#do_clr;
        Retv

       with Method instancePrefix--"notFull" () :  :=
#fifof

       with Method instancePrefix--"notEmpty" () :  :=
#fifof

       with Method instancePrefix--"isLessThan" (c : nat) : Bool :=
        Read count_v : UInt cntSize <- "count";        Ret  rangeTest(#count_v, $c, #\<, $1, $ififoDepth, null)

       with Method instancePrefix--"isGreaterThan" (c : nat) : Bool :=
        Read count_v : UInt cntSize <- "count";        Ret  rangeTest(#count_v, $c, #\>, $0, ($ififoDepth - $1), null)

    }). (* mkBypassFIFOLevel *)

    Definition mkBypassFIFOLevel := Build_FIFOLevelIfc a fifoDepth mkBypassFIFOLevelModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first") (instancePrefix--"isGreaterThan") (instancePrefix--"isLessThan") (instancePrefix--"notEmpty") (instancePrefix--"notFull").
    End Section'mkBypassFIFOLevel.
End mkBypassFIFOLevel.

Definition rangeTest (value: UInt cntSz) (comp: nat) (foperation: Function UInt cntSz Function UInt cntSz bool) (minValue: nat) (maxValue: nat) (methodName: String): bool := 
                Ret (&& (>= $comp $minValue) (<= $comp $maxValue)) foperation(#value,  fromInteger($comp)) error((+ (+ (+ (+ (+ (+ (+ (+ null #methodName) null)  integerToString($minValue)) null)  integerToString($maxValue)) null)  integerToString($comp)) null))

.

