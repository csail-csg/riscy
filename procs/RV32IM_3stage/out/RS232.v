Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Clocks.
Require Import GetPut.
Require Import Connectable.
Require Import FIFOLevel.
Require Import Vector.
Require Import BUtils.
Require Import Counter.
Definition RecvStateFields := (STRUCT {
    "$tag" :: (Bit 8);
    "Start" :: void;
    "Center" :: void;
    "Wait" :: void;
    "Sample" :: void;
    "RS_Parity" :: void;
    "StopFirst" :: void;
    "StopLast" :: void}).
Definition RecvState := Struct (RecvStateFields).
Definition XmitStateFields := (STRUCT {
    "$tag" :: (Bit 8);
    "XS_Idle" :: void;
    "XS_Start" :: void;
    "XS_Wait" :: void;
    "XS_Shift" :: void;
    "XS_Stop" :: void;
    "XS_Stop5" :: void;
    "XS_Stop2" :: void;
    "XS_Parity" :: void}).
Definition XmitState := Struct (XmitStateFields).
Definition ParityFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition Parity := (Struct ParityFields).
Notation NONE := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ODD := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation EVEN := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition StopBitsFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition StopBits := (Struct StopBitsFields).
Notation STOP_1 := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation STOP_1_5 := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation STOP_2 := (STRUCT { "$tag" ::= $0 })%kami_expr.
(* * interface RS232 *)
Record RS232 := {
    RS232'interface: Modules;
    RS232'sin : string;
    RS232'sout : string;
}.

(* * interface BaudGenerator *)
Record BaudGenerator := {
    BaudGenerator'interface: Modules;
    BaudGenerator'clock_enable : string;
    BaudGenerator'clear : string;
    BaudGenerator'baud_tick_16x : string;
    BaudGenerator'baud_tick_2x : string;
}.

(* * interface InputFilter#(size, a) *)
Record InputFilter (a : Kind) (size : nat) := {
    InputFilter'interface: Modules;
    InputFilter'clock_enable : string;
    InputFilter'_read : string;
}.

(* * interface EdgeDetector#(a) *)
Record EdgeDetector (a : Kind) := {
    EdgeDetector'interface: Modules;
    EdgeDetector'rising : string;
    EdgeDetector'falling : string;
}.

(* * interface Synchronizer#(a) *)
Record Synchronizer (a : Kind) := {
    Synchronizer'interface: Modules;
    Synchronizer'_write : string;
    Synchronizer'_read : string;
}.

(* * interface InputMovingFilter#(width, threshold, a) *)
Record InputMovingFilter (a : Kind) (threshold : nat) (width : nat) := {
    InputMovingFilter'interface: Modules;
    InputMovingFilter'sample : string;
    InputMovingFilter'clear : string;
    InputMovingFilter'_read : string;
}.

(* * interface UART#(depth) *)
Record UART (depth : nat) := {
    UART'interface: Modules;
    UART'rs232 : RS232;
    UART'tx : (Get (word 8));
    UART'rx : (Put (word 8));
}.

Module mkBaudGenerator.
    Section Section'mkBaudGenerator.
    Variable instancePrefix: string.
    Variable divider: (word 16).
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface Counter subinterface clear *)
(* FIXME: interface Counter subinterface up *)
(* FIXME: interface Counter subinterface value *)
(* FIXME: interface Counter subinterface value *)
                                                               Let rBaudCounter := mkCounter (instancePrefix--"rBaudCounter").
       Let pwBaudTick16x := mkPulseWire (instancePrefix--"pwBaudTick16x").
       Let rBaudTickCounter := mkCounter (instancePrefix--"rBaudTickCounter").
       Let pwBaudTick2x := mkPulseWire (instancePrefix--"pwBaudTick2x").
       Let wBaudCount := mkWire (instancePrefix--"wBaudCount").
       Let wBaudTickCount := mkWire (instancePrefix--"wBaudTickCount").
    Definition mkBaudGeneratorModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance rBaudCounter :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwBaudTick16x :: nil))
       with (BKMod (FIXME'InterfaceName'instance rBaudTickCounter :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwBaudTick2x :: nil))
       with (BKMod (FIXME'InterfaceName'instance wBaudCount :: nil))
       with Rule instancePrefix--"baud_count_wire" :=
               Write wBaudCount : Bit 16 <- #rBaudCounter;
        Retv (* rule baud_count_wire *)
       with (BKMod (FIXME'InterfaceName'instance wBaudTickCount :: nil))
       with Rule instancePrefix--"baud_tick_count_wire" :=
               Write wBaudTickCount : Bit 3 <- #rBaudTickCounter;
        Retv (* rule baud_tick_count_wire *)
       with Rule instancePrefix--"count_baudtick_16x" :=
        Assert(#pwBaudTick16x);
               LET btc : (Counter 3) <- #rBaudTickCounter;
        btcup();
        Retv (* rule count_baudtick_16x *)
       with Rule instancePrefix--"assert_2x_baud_tick" :=
        Assert((( rBaudTickCountervalue() == $0) && #pwBaudTick16x));
       #pwBaudTick2x;
        Retv (* rule assert_2x_baud_tick *)
       with Method instancePrefix--"clock_enable" () : Void :=
        If (( rBaudCountervalue() + $1) >= #divider)
        then                 BKSTMTS {
        #pwBaudTick16x;
         rBaudCounterclear();
;
        Retv
        else                 BKSTMTS {
         rBaudCounterup();
;
        Retv;;
        Retv

       with Method instancePrefix--"clear" () : Void :=
 rBaudCounterclear();
        Retv

       with Method instancePrefix--"baud_tick_16x" () : Bool :=
        Ret #pwBaudTick16x

       with Method instancePrefix--"baud_tick_2x" () : Bool :=
        Ret #pwBaudTick2x

    }). (* mkBaudGenerator *)

    Definition mkBaudGenerator := Build_BaudGenerator mkBaudGeneratorModule%kami (instancePrefix--"baud_tick_16x") (instancePrefix--"baud_tick_2x") (instancePrefix--"clear") (instancePrefix--"clock_enable").
    End Section'mkBaudGenerator.
End mkBaudGenerator.

Module mkInputFilter.
    Section Section'mkInputFilter.
    Variable a : Kind.
    Variable size : Kind.
    Variable instancePrefix: string.
    Variable initval: a.
    Variable din: a.
(* FIXME: interface Counter subinterface down *)
(* FIXME: interface Counter subinterface up *)
                       Let counter := mkCounter (instancePrefix--"counter").
       Let rOut : string := instancePrefix--"rOut".
    Definition mkInputFilterModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance counter :: nil))
       with Register rOut : a <- $initval
       with Method instancePrefix--"clock_enable" () : Void :=
        If ((#din ==  unpack($1)) && ( countervalue() !=  fromInteger(null)))
        then         #counter;
        Retv
        else                 If ((#din ==  unpack($0)) && ( countervalue() != $0))
        then         #counter;
        Retv;
        Retv;;
        If ( countervalue() ==  fromInteger(null))
        then                 Write rOut : a <-  unpack($1);
        Retv
        else                 If ( countervalue() == $0)
        then                 Write rOut : a <-  unpack($0);
        Retv;
        Retv;;
        Retv

       with Method instancePrefix--"_read" () : a :=
        Read rOut_v : a <- "rOut";        Ret #rOut_v

    }). (* mkInputFilter *)

    Definition mkInputFilter := Build_InputFilter a size mkInputFilterModule%kami (instancePrefix--"_read") (instancePrefix--"clock_enable").
    End Section'mkInputFilter.
End mkInputFilter.

Module mkEdgeDetector.
    Section Section'mkEdgeDetector.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable initval: a.
    Variable din: a.
                       Let rDinD1 : string := instancePrefix--"rDinD1".
    Definition mkEdgeDetectorModule :=
        (BKMODULE {
           Register rDinD1 : a <- $initval
       with Rule instancePrefix--"pipeline" :=
               Write rDinD1 : a <- #din;
        Retv (* rule pipeline *)
       with Method instancePrefix--"rising" () : Bool :=
        Read rDinD1_v : a <- "rDinD1";        Ret ((#din ==  unpack($1)) && (#rDinD1_v ==  unpack($0)))

       with Method instancePrefix--"falling" () : Bool :=
        Read rDinD1_v : a <- "rDinD1";        Ret ((#din ==  unpack($0)) && (#rDinD1_v ==  unpack($1)))

    }). (* mkEdgeDetector *)

    Definition mkEdgeDetector := Build_EdgeDetector a mkEdgeDetectorModule%kami (instancePrefix--"falling") (instancePrefix--"rising").
    End Section'mkEdgeDetector.
End mkEdgeDetector.

Definition getRising (ifc: EdgeDetector a): bool := 
                Ret #ifc

.

Definition getFalling (ifc: EdgeDetector a): bool := 
                Ret #ifc

.

Module mkSynchronizer.
    Section Section'mkSynchronizer.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable initval: a.
                       Let d1 : string := instancePrefix--"d1".
       Let d2 : string := instancePrefix--"d2".
    Definition mkSynchronizerModule :=
        (BKMODULE {
           Register d1 : a <- $initval
       with Register d2 : a <- $initval
       with Method instancePrefix--"_write" (x : <nulltype>) : Void :=
        Read d1_v : a <- "d1";        Write d1 : a <- #x;
        Write d2 : a <- #d1_v;
        Retv

       with Method instancePrefix--"_read" () : a :=
        Read d2_v : a <- "d2";        Ret #d2_v

    }). (* mkSynchronizer *)

    Definition mkSynchronizer := Build_Synchronizer a mkSynchronizerModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkSynchronizer.
End mkSynchronizer.

Module mkInputMovingFilter.
    Section Section'mkInputMovingFilter.
    Variable a : Kind.
    Variable threshold : Kind.
    Variable width : Kind.
    Variable instancePrefix: string.
    Variable din: a.
(* FIXME: interface Counter subinterface clear *)
(* FIXME: interface Counter subinterface up *)
(* FIXME: interface PulseWire subinterface send *)
                                       Let counter := mkCounter (instancePrefix--"counter").
       Let rOut : string := instancePrefix--"rOut".
       Let pwSample := mkPulseWire (instancePrefix--"pwSample").
    Definition mkInputMovingFilterModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance counter :: nil))
       with Register rOut : a <- $unpack(0)
       with (BKMod (FIXME'InterfaceName'instance pwSample :: nil))
       with Rule instancePrefix--"threshold_compare" :=
        Assert(( countervalue() >=  fromInteger(null)));
               Write rOut : a <-  unpack($1);
        Retv (* rule threshold_compare *)
       with Rule instancePrefix--"take_sample" :=
        Assert((#pwSample && (#din ==  unpack($1))));
       #counter;
        Retv (* rule take_sample *)
       with Method instancePrefix--"sample" () : Void :=
#pwSample;
        Retv

       with Method instancePrefix--"clear" () : Void :=
 counterclear();
        Write rOut : a <-  unpack($0);
        Retv

       with Method instancePrefix--"_read" () : a :=
        Read rOut_v : a <- "rOut";        Ret #rOut_v

    }). (* mkInputMovingFilter *)

    Definition mkInputMovingFilter := Build_InputMovingFilter a threshold width mkInputMovingFilterModule%kami (instancePrefix--"_read") (instancePrefix--"clear") (instancePrefix--"sample").
    End Section'mkInputMovingFilter.
End mkInputMovingFilter.

Module mkUART.
    Section Section'mkUART.
    Variable d : Kind.
    Variable instancePrefix: string.
    Variable charsize: (word 4).
    Variable paritysel: Parity.
    Variable stopbits: StopBits.
    Variable divider: (word 16).
    Variable ifc: (UART d).
(* FIXME: interface BaudGenerator subinterface baud_tick_16x *)
(* FIXME: interface BaudGenerator subinterface clock_enable *)
(* FIXME: interface FIFOLevelIfc subinterface deq *)
    Let fifoRecvenq := MethodSig (FIFOLevelIfc'enq fifoRecv) (element_type) : Void.
(* FIXME: interface FIFOLevelIfc subinterface deq *)
    Let fifoXmitenq := MethodSig (FIFOLevelIfc'enq fifoXmit) (element_type) : Void.
(* FIXME: interface FIFOLevelIfc subinterface notEmpty *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
(* FIXME: interface PulseWire subinterface send *)
    Let rRecvData_write := MethodSig (Reg'_write rRecvData) (a) : Void.
                                                                                                                                                                                        