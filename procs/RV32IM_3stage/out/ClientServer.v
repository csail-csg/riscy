Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import GetPut.
Require Import Connectable.
(* * interface Client#(req_type, resp_type) *)
Record Client (req_type : Kind) (resp_type : Kind) := {
    Client'interface: Modules;
    Client'request : (Get req_type);
    Client'response : (Put resp_type);
}.

(* * interface Server#(req_type, resp_type) *)
Record Server (req_type : Kind) (resp_type : Kind) := {
    Server'interface: Modules;
    Server'request : (Put req_type);
    Server'response : (Get resp_type);
}.

