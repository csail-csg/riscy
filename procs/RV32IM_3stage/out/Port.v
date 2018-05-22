Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import ClientServer.
Require Import Connectable.
Require Import Ehr.
Require Import FIFOG.
Require Import GetPut.
(* * interface InputPort#(t) *)
Record InputPort (t : Kind) := {
    InputPort'interface: Modules;
    InputPort'enq : string;
    InputPort'canEnq : string;
}.

(* * interface OutputPort#(t) *)
Record OutputPort (t : Kind) := {
    OutputPort'interface: Modules;
    OutputPort'canDeq : string;
    OutputPort'first : string;
    OutputPort'deq : string;
}.

Module nullInputPort.
    Section Section'nullInputPort.
    Variable t : Kind.
    Variable instancePrefix: string.
            Definition nullInputPortModule :=
        (BKMODULE {
           Method instancePrefix--"enq" (val : t) : Void :=
#noAction;
        Retv

       with Method instancePrefix--"canEnq" () :  :=
        Ret #False

    }). (* nullInputPort *)

    Definition nullInputPort := Build_InputPort t nullInputPortModule%kami (instancePrefix--"canEnq") (instancePrefix--"enq").
    End Section'nullInputPort.
End nullInputPort.

Module nullOutputPort.
    Section Section'nullOutputPort.
    Variable t : Kind.
    Variable instancePrefix: string.
                Definition nullOutputPortModule :=
        (BKMODULE {
           Method instancePrefix--"first" () : t :=
        Ret null

       with Method instancePrefix--"deq" () : Void :=
#noAction;
        Retv

       with Method instancePrefix--"canDeq" () : Bool :=
        Ret #False

    }). (* nullOutputPort *)

    Definition nullOutputPort := Build_OutputPort t nullOutputPortModule%kami (instancePrefix--"canDeq") (instancePrefix--"deq") (instancePrefix--"first").
    End Section'nullOutputPort.
End nullOutputPort.

(* * interface ServerPort#(req_t, resp_t) *)
Record ServerPort (req_t : Kind) (resp_t : Kind) := {
    ServerPort'interface: Modules;
    ServerPort'request : (InputPort req_t);
    ServerPort'response : (OutputPort resp_t);
}.

(* * interface ClientPort#(req_t, resp_t) *)
Record ClientPort (req_t : Kind) (resp_t : Kind) := {
    ClientPort'interface: Modules;
    ClientPort'request : (OutputPort req_t);
    ClientPort'response : (InputPort resp_t);
}.

Module nullServerPort.
    Section Section'nullServerPort.
    Variable req_t : Kind.
    Variable resp_t : Kind.
    Variable instancePrefix: string.
                       Let nip := nullInputPort (instancePrefix--"nip").
       Let nop := nullOutputPort (instancePrefix--"nop").
    Definition nullServerPortModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance nip :: nil))
       with (BKMod (FIXME'InterfaceName'instance nop :: nil))
    }). (* nullServerPort *)

    Definition nullServerPort := Build_ServerPort req_t resp_t nullServerPortModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'nullServerPort.
End nullServerPort.

Module nullClientPort.
    Section Section'nullClientPort.
    Variable req_t : Kind.
    Variable resp_t : Kind.
    Variable instancePrefix: string.
                       Let nop := nullOutputPort (instancePrefix--"nop").
       Let nip := nullInputPort (instancePrefix--"nip").
    Definition nullClientPortModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance nop :: nil))
       with (BKMod (FIXME'InterfaceName'instance nip :: nil))
    }). (* nullClientPort *)

    Definition nullClientPort := Build_ClientPort req_t resp_t nullClientPortModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'nullClientPort.
End nullClientPort.

