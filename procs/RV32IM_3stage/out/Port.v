Require Import Bool String List Arith.
Require Import Omega.
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
    InputPort'modules: Modules;
    InputPort'enq : string;
    InputPort'canEnq : string;
}.

(* * interface OutputPort#(t) *)
Record OutputPort (t : Kind) := {
    OutputPort'modules: Modules;
    OutputPort'canDeq : string;
    OutputPort'first : string;
    OutputPort'deq : string;
}.

(* * interface ServerPort#(req_t, resp_t) *)
Record ServerPort (req_t : Kind) (resp_t : Kind) := {
    ServerPort'modules: Modules;
    ServerPort'request : (InputPort req_t);
    ServerPort'response : (OutputPort resp_t);
}.

(* * interface ClientPort#(req_t, resp_t) *)
Record ClientPort (req_t : Kind) (resp_t : Kind) := {
    ClientPort'modules: Modules;
    ClientPort'request : (OutputPort req_t);
    ClientPort'response : (InputPort resp_t);
}.

