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
                                                                                                                                                                                                                       Let baudGen := mkBaudGenerator (instancePrefix--"baudGen").
       Let fifoRecv := mkGFIFOLevel (instancePrefix--"fifoRecv").
       Let vrRecvBuffer := replicateM (instancePrefix--"vrRecvBuffer").
       Let rRecvData : string := instancePrefix--"rRecvData".
       Let rRecvState : string := instancePrefix--"rRecvState".
       Let rRecvCellCount : string := instancePrefix--"rRecvCellCount".
       Let rRecvBitCount : string := instancePrefix--"rRecvBitCount".
       Let rRecvParity : string := instancePrefix--"rRecvParity".
       Let pwRecvShiftBuffer := mkPulseWire (instancePrefix--"pwRecvShiftBuffer").
       Let pwRecvCellCountReset := mkPulseWire (instancePrefix--"pwRecvCellCountReset").
       Let pwRecvResetBitCount := mkPulseWire (instancePrefix--"pwRecvResetBitCount").
       Let pwRecvEnableBitCount := mkPulseWire (instancePrefix--"pwRecvEnableBitCount").
       Let fifoXmit := mkGFIFOLevel (instancePrefix--"fifoXmit").
       Let vrXmitBuffer := replicateM (instancePrefix--"vrXmitBuffer").
       Let rXmitState : string := instancePrefix--"rXmitState".
       Let rXmitCellCount : string := instancePrefix--"rXmitCellCount".
       Let rXmitBitCount : string := instancePrefix--"rXmitBitCount".
       Let rXmitDataOut : string := instancePrefix--"rXmitDataOut".
       Let rXmitParity : string := instancePrefix--"rXmitParity".
       Let pwXmitCellCountReset := mkPulseWire (instancePrefix--"pwXmitCellCountReset").
       Let pwXmitResetBitCount := mkPulseWire (instancePrefix--"pwXmitResetBitCount").
       Let pwXmitEnableBitCount := mkPulseWire (instancePrefix--"pwXmitEnableBitCount").
       Let pwXmitLoadBuffer := mkPulseWire (instancePrefix--"pwXmitLoadBuffer").
       Let pwXmitShiftBuffer := mkPulseWire (instancePrefix--"pwXmitShiftBuffer").
    Definition mkUARTModule :=
        (BKMODULE {
                   LET fifodepth : nat <- null
       with (BKMod (FIXME'InterfaceName'instance baudGen :: nil))
       with (BKMod (FIXME'InterfaceName'instance fifoRecv :: nil))
       with (BKMod (FIXME'InterfaceName'instance vrRecvBuffer :: nil))
       with Register rRecvData : Bit 1 <- $1
       with Register rRecvState : RecvState <-  mkRegA(#Start)
       with Register rRecvCellCount : Bit 4 <-  mkRegA($0)
       with Register rRecvBitCount : Bit 4 <-  mkRegA($0)
       with Register rRecvParity : Bit 1 <-  mkRegA($0)
       with (BKMod (FIXME'InterfaceName'instance pwRecvShiftBuffer :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwRecvCellCountReset :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwRecvResetBitCount :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwRecvEnableBitCount :: nil))
       with (BKMod (FIXME'InterfaceName'instance fifoXmit :: nil))
       with (BKMod (FIXME'InterfaceName'instance vrXmitBuffer :: nil))
       with Register rXmitState : XmitState <-  mkRegA(#XS_Idle)
       with Register rXmitCellCount : Bit 4 <-  mkRegA($0)
       with Register rXmitBitCount : Bit 4 <-  mkRegA($0)
       with Register rXmitDataOut : Bit 1 <-  mkRegA($1)
       with Register rXmitParity : Bit 1 <-  mkRegA($0)
       with (BKMod (FIXME'InterfaceName'instance pwXmitCellCountReset :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwXmitResetBitCount :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwXmitEnableBitCount :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwXmitLoadBuffer :: nil))
       with (BKMod (FIXME'InterfaceName'instance pwXmitShiftBuffer :: nil))
       with         LET tick : Bool = #baudGen
       with Rule instancePrefix--"baud_generator_clock_enable" :=
       #baudGen;
        Retv (* rule baud_generator_clock_enable *)
       with Rule instancePrefix--"receive_bit_cell_time_counter" :=
        Read rRecvCellCount_v : Bit 4 <- rRecvCellCount;
        Assert(#tick);
               If #pwRecvCellCountReset
        then                 Write rRecvCellCount : Bit 4 <- $0;
        Retv
        else                 Write rRecvCellCount : Bit 4 <- (#rRecvCellCount_v + $1);
        Retv;;
        Retv (* rule receive_bit_cell_time_counter *)
       with Rule instancePrefix--"receive_buffer_shift" :=
        Read rRecvData_v : Bit 1 <- rRecvData;
        Assert(#pwRecvShiftBuffer);
               Call v : tvar886 <-  shiftInAtN( readVReg(#vrRecvBuffer), #rRecvData_v);
        writeVReg(#vrRecvBuffer, #v);
        Retv (* rule receive_buffer_shift *)
       with Rule instancePrefix--"receive_bit_counter" :=
        Read rRecvBitCount_v : Bit 4 <- rRecvBitCount;
               If #pwRecvResetBitCount
        then                 Write rRecvBitCount : Bit 4 <- $0;
        Retv
        else                 If #pwRecvEnableBitCount
        then                 Write rRecvBitCount : Bit 4 <- (#rRecvBitCount_v + $1);
        Retv;
        Retv;;
        Retv (* rule receive_bit_counter *)
       with Rule instancePrefix--"receive_wait_for_start_bit" :=
        Read rRecvData_v : Bit 1 <- rRecvData;
        Read rRecvState_v : RecvState <- rRecvState;
        Assert(((#rRecvState_v == #Start) && #tick));
        pwRecvCellCountResetsend();
               If (#rRecvData_v == $1'b0)
        then                 BKSTMTS {
                Write rRecvState : RecvState <- #Center;
;
        Retv
        else                 BKSTMTS {
                Write rRecvState : RecvState <- #Start;
         pwRecvResetBitCountsend();
;
        Retv;;
        Retv (* rule receive_wait_for_start_bit *)
       with Rule instancePrefix--"receive_find_center_of_bit_cell" :=
        Read rRecvCellCount_v : Bit 4 <- rRecvCellCount;
        Read rRecvData_v : Bit 1 <- rRecvData;
        Read rRecvState_v : RecvState <- rRecvState;
        Assert(((#rRecvState_v == #Center) && #tick));
               If (#rRecvCellCount_v == $4'h4)
        then                 BKSTMTS {
         pwRecvCellCountResetsend();
                If (#rRecvData_v == $1'b0)
        then                 Write rRecvState : RecvState <- #Wait;
        Retv
        else                 Write rRecvState : RecvState <- #Start;
        Retv;;
;
        Retv
        else                 BKSTMTS {
                Write rRecvState : RecvState <- #Center;
;
        Retv;;
        Retv (* rule receive_find_center_of_bit_cell *)
       with Rule instancePrefix--"receive_wait_bit_cell_time_for_sample" :=
        Read rRecvBitCount_v : Bit 4 <- rRecvBitCount;
        Read rRecvCellCount_v : Bit 4 <- rRecvCellCount;
        Read rRecvState_v : RecvState <- rRecvState;
        Assert((((#rRecvState_v == #Wait) && (#rRecvCellCount_v == $4'hF)) && #tick));
       #pwRecvCellCountReset;
               If (#rRecvBitCount_v == #charsize)
        then                 BKSTMTS {
                If (#paritysel != #NONE)
        then                 Write rRecvState : RecvState <- #RS_Parity;
        Retv
        else                 If (#stopbits != #STOP_1)
        then                 Write rRecvState : RecvState <- #StopFirst;
        Retv
        else                 Write rRecvState : RecvState <- #StopLast;
        Retv;;
        Retv;;
;
        Retv
        else                 If (#rRecvBitCount_v == (#charsize + $1))
        then                 BKSTMTS {
                If ((#paritysel == #NONE) || (#stopbits == #STOP_1))
        then                 Write rRecvState : RecvState <- #StopLast;
        Retv
        else                 Write rRecvState : RecvState <- #StopFirst;
        Retv;;
;
        Retv
        else                 If (#rRecvBitCount_v == (#charsize + $2))
        then                 BKSTMTS {
                Write rRecvState : RecvState <- #StopLast;
;
        Retv
        else                 BKSTMTS {
                Write rRecvState : RecvState <- #Sample;
;
        Retv;;
        Retv;;
        Retv;;
        Retv (* rule receive_wait_bit_cell_time_for_sample *)
       with Rule instancePrefix--"receive_sample_pin" :=
        Read rRecvState_v : RecvState <- rRecvState;
        Assert(((#rRecvState_v == #Sample) && #tick));
       #pwRecvShiftBuffer;
       #pwRecvEnableBitCount;
       #pwRecvCellCountReset;
               Write rRecvState : RecvState <- #Wait;
        Retv (* rule receive_sample_pin *)
       with Rule instancePrefix--"receive_parity_bit" :=
        Read rRecvData_v : Bit 1 <- rRecvData;
        Read rRecvState_v : RecvState <- rRecvState;
        Assert(((#rRecvState_v == #RS_Parity) && #tick));
               Write rRecvParity : Bit 1 <- #rRecvData_v;
       #pwRecvEnableBitCount;
       #pwRecvCellCountReset;
               Write rRecvState : RecvState <- #Wait;
        Retv (* rule receive_parity_bit *)
       with Rule instancePrefix--"receive_stop_first_bit" :=
        Read rRecvData_v : Bit 1 <- rRecvData;
        Read rRecvState_v : RecvState <- rRecvState;
        Assert(((#rRecvState_v == #StopFirst) && #tick));
       #pwRecvEnableBitCount;
       #pwRecvCellCountReset;
               If (#rRecvData_v == $1)
        then                 Write rRecvState : RecvState <- #Wait;
        Retv
        else                 Write rRecvState : RecvState <- #Start;
        Retv;;
        Retv (* rule receive_stop_first_bit *)
       with Rule instancePrefix--"receive_stop_last_bit" :=
        Read rRecvState_v : RecvState <- rRecvState;
        Assert(((#rRecvState_v == #StopLast) && #tick));
       LET data <- ;
               LET bitdata : (Bit 8) <- ( pack(#data) >> ($8 - #charsize));
        fifoRecvenq(#bitdata);
               Write rRecvState : RecvState <- #Start;
       #pwRecvCellCountReset;
        Retv (* rule receive_stop_last_bit *)
       with Rule instancePrefix--"transmit_bit_cell_time_counter" :=
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Assert(#tick);
               If #pwXmitCellCountReset
        then                 Write rXmitCellCount : Bit 4 <- $0;
        Retv
        else                 Write rXmitCellCount : Bit 4 <- (#rXmitCellCount_v + $1);
        Retv;;
        Retv (* rule transmit_bit_cell_time_counter *)
       with Rule instancePrefix--"transmit_bit_counter" :=
        Read rXmitBitCount_v : Bit 4 <- rXmitBitCount;
               If #pwXmitResetBitCount
        then                 Write rXmitBitCount : Bit 4 <- $0;
        Retv
        else                 If #pwXmitEnableBitCount
        then                 Write rXmitBitCount : Bit 4 <- (#rXmitBitCount_v + $1);
        Retv;
        Retv;;
        Retv (* rule transmit_bit_counter *)
       with Rule instancePrefix--"transmit_buffer_load" :=
        Assert(#pwXmitLoadBuffer);
       LET data <- ;
       #fifoXmit;
        writeVReg(#vrXmitBuffer,  unpack(#data));
               Write rXmitParity : Bit 1 <-  parity(#data);
        Retv (* rule transmit_buffer_load *)
       with Rule instancePrefix--"transmit_buffer_shift" :=
        Assert((!#pwXmitLoadBuffer && #pwXmitShiftBuffer));
               Call v : tvar942 <-  shiftInAtN( readVReg(#vrXmitBuffer), $1);
        writeVReg(#vrXmitBuffer, #v);
        Retv (* rule transmit_buffer_shift *)
       with Rule instancePrefix--"transmit_wait_for_start_command" :=
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Idle) && #tick));
               Write rXmitDataOut : Bit 1 <- $1'b1;
       #pwXmitResetBitCount;
               If #fifoXmit
        then                 BKSTMTS {
        #pwXmitCellCountReset;
        #pwXmitLoadBuffer;
                Write rXmitState : XmitState <- #XS_Start;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Idle;
;
        Retv;;
        Retv (* rule transmit_wait_for_start_command *)
       with Rule instancePrefix--"transmit_send_start_bit" :=
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Start) && #tick));
               Write rXmitDataOut : Bit 1 <- $1'b0;
               If (#rXmitCellCount_v == $4'hF)
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Wait;
        #pwXmitCellCountReset;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Start;
;
        Retv;;
        Retv (* rule transmit_send_start_bit *)
       with Rule instancePrefix--"transmit_wait_1_bit_cell_time" :=
        Read rXmitBitCount_v : Bit 4 <- rXmitBitCount;
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Wait) && #tick));
               Write rXmitDataOut : Bit 1 <-  head( readVReg(#vrXmitBuffer));
               If (#rXmitCellCount_v == $4'hF)
        then                 BKSTMTS {
        #pwXmitCellCountReset;
                If ((#rXmitBitCount_v == (#charsize - $1)) && (#paritysel == #NONE))
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop;
;
        Retv
        else                 If ((#rXmitBitCount_v == (#charsize - $1)) && (#paritysel != #NONE))
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Parity;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Shift;
        #pwXmitEnableBitCount;
;
        Retv;;
        Retv;;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Wait;
;
        Retv;;
        Retv (* rule transmit_wait_1_bit_cell_time *)
       with Rule instancePrefix--"transmit_shift_next_bit" :=
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Shift) && #tick));
               Write rXmitDataOut : Bit 1 <-  head( readVReg(#vrXmitBuffer));
               Write rXmitState : XmitState <- #XS_Wait;
       #pwXmitShiftBuffer;
        Retv (* rule transmit_shift_next_bit *)
       with Rule instancePrefix--"transmit_send_parity_bit" :=
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Read rXmitParity_v : Bit 1 <- rXmitParity;
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Parity) && #tick));
           If (#paritysel!ParityFields@."$tag" == $0) then
        Write rXmitDataOut : Bit 1 <- #rXmitParity_v;
        Retv
    else
    If (#paritysel!ParityFields@."$tag" == $0) then
        Write rXmitDataOut : Bit 1 <- ~#rXmitParity_v;
        Retv
    else
        Retv;
               If (#rXmitCellCount_v == $4'hF)
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop;
        #pwXmitCellCountReset;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Parity;
;
        Retv;;
        Retv (* rule transmit_send_parity_bit *)
       with Rule instancePrefix--"transmit_send_stop_bit" :=
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Stop) && #tick));
               Write rXmitDataOut : Bit 1 <- $1'b1;
               If ((#rXmitCellCount_v == $4'hF) && (#stopbits == #STOP_1))
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Idle;
        #pwXmitCellCountReset;
;
        Retv
        else                 If ((#rXmitCellCount_v == $4'hF) && (#stopbits == #STOP_2))
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop2;
        #pwXmitCellCountReset;
;
        Retv
        else                 If ((#rXmitCellCount_v == $4'hF) && (#stopbits == #STOP_1_5))
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop5;
        #pwXmitCellCountReset;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop;
;
        Retv;;
        Retv;;
        Retv;;
        Retv (* rule transmit_send_stop_bit *)
       with Rule instancePrefix--"transmit_send_stop_bit1_5" :=
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Stop5) && #tick));
               Write rXmitDataOut : Bit 1 <- $1'b1;
               If (#rXmitCellCount_v == $4'h7)
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Idle;
        #pwXmitCellCountReset;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop5;
;
        Retv;;
        Retv (* rule transmit_send_stop_bit1_5 *)
       with Rule instancePrefix--"transmit_send_stop_bit2" :=
        Read rXmitCellCount_v : Bit 4 <- rXmitCellCount;
        Read rXmitState_v : XmitState <- rXmitState;
        Assert(((#rXmitState_v == #XS_Stop2) && #tick));
               Write rXmitDataOut : Bit 1 <- $1'b1;
               If (#rXmitCellCount_v == $4'hF)
        then                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Idle;
        #pwXmitCellCountReset;
;
        Retv
        else                 BKSTMTS {
                Write rXmitState : XmitState <- #XS_Stop2;
;
        Retv;;
        Retv (* rule transmit_send_stop_bit2 *)
       with Method instancePrefix--"sout" () :  :=
        Read rXmitDataOut_v : Bit 1 <- "rXmitDataOut";#rXmitDataOut_v

       with Method instancePrefix--"sin" () :  :=
        Read rRecvData_v : Bit 1 <- "rRecvData";#rRecvData_v

       with Method instancePrefix--"get" () : (ActionValue (Bit 8)) :=
LET data <- ;
#fifoRecv;
        Ret #data

       with Method instancePrefix--"put" (x : <nulltype>) : Void :=
 fifoXmitenq(#x);
        Retv

    }). (* mkUART *)

    Definition mkUART := Build_Bit d mkUARTModule%kami.
    End Section'mkUART.
End mkUART.

