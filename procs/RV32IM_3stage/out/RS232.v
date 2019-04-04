Require Import Bool String List Arith.
Require Import Omega.
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
    "Start" :: Void;
    "Center" :: Void;
    "Wait" :: Void;
    "Sample" :: Void;
    "RS_Parity" :: Void;
    "StopFirst" :: Void;
    "StopLast" :: Void}).
Definition RecvState := Struct (RecvStateFields).
Definition XmitStateFields := (STRUCT {
    "$tag" :: (Bit 8);
    "XS_Idle" :: Void;
    "XS_Start" :: Void;
    "XS_Wait" :: Void;
    "XS_Shift" :: Void;
    "XS_Stop" :: Void;
    "XS_Stop5" :: Void;
    "XS_Stop2" :: Void;
    "XS_Parity" :: Void}).
Definition XmitState := Struct (XmitStateFields).
Definition ParityFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition Parity := (Struct ParityFields).
Notation NONE := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation ODD := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation EVEN := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
Definition StopBitsFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition StopBits := (Struct StopBitsFields).
Notation STOP_1 := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation STOP_1_5 := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation STOP_2 := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
(* * interface RS232 *)
Record RS232 := {
    RS232'modules: Modules;
    RS232'sin : string;
    RS232'sout : string;
}.

(* * interface BaudGenerator *)
Record BaudGenerator := {
    BaudGenerator'modules: Modules;
    BaudGenerator'clock_enable : string;
    BaudGenerator'clear : string;
    BaudGenerator'baud_tick_16x : string;
    BaudGenerator'baud_tick_2x : string;
}.

(* * interface InputFilter#(size, a) *)
Record InputFilter (size : nat) (a : Kind) := {
    InputFilter'modules: Modules;
    InputFilter'clock_enable : string;
    InputFilter'_read : string;
}.

(* * interface EdgeDetector#(a) *)
Record EdgeDetector (a : Kind) := {
    EdgeDetector'modules: Modules;
    EdgeDetector'rising : string;
    EdgeDetector'falling : string;
}.

(* * interface Synchronizer#(a) *)
Record Synchronizer (a : Kind) := {
    Synchronizer'modules: Modules;
    Synchronizer'_write : string;
    Synchronizer'_read : string;
}.

(* * interface InputMovingFilter#(width, threshold, a) *)
Record InputMovingFilter (width : nat) (threshold : nat) (a : Kind) := {
    InputMovingFilter'modules: Modules;
    InputMovingFilter'sample : string;
    InputMovingFilter'clear : string;
    InputMovingFilter'_read : string;
}.

(* * interface UART#(depth) *)
Record UART (depth : nat) := {
    UART'modules: Modules;
    UART'rs232 : RS232;
    UART'tx : (Get (Bit 8));
    UART'rx : (Put (Bit 8));
}.

Definition getRising (ifc: EdgeDetector a): bool := 
                Ret #ifc

.

Definition getFalling (ifc: EdgeDetector a): bool := 
                Ret #ifc

.

