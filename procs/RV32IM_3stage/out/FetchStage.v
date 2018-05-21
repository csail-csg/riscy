Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import GetPut.
Require Import Port.
Require Import MemUtil.
Require Import RVTypes.
Require Import CoreStates.
(* * interface FetchStage *)
Record FetchStage := {
    FetchStage'interface: Modules;
}.

Module mkFetchStage.
    Section Section'mkFetchStage.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable fs: (Reg (Maybe (FetchState xlen))).
    Variable es: (Reg (Maybe (ExecuteState xlen))).
    Variable ifetchreq: (InputPort (ReadOnlyMemReq xlen 2)).
    Let ifetchreqenq := MethodSig (InputPort'enq ifetchreq) (t) : Void.
        Definition mkFetchStageModule :=
        (BKMODULE {
           Rule instancePrefix--"doFetch" :=
        Read es_v : Maybe ExecuteState xlen <- es;
        Read fs_v : Maybe FetchState xlen <- fs;
        Assert(#fs_v$taggedValid.fetchState(#es_v == STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }));
               LET pc : tvar772 = #fetchState;
               Write fs : Maybe FetchState xlen <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        ifetchreqenq(STRUCT { "addr" ::= #pc  });
               Write es : Maybe ExecuteState xlen <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "poisoned" ::= #False; "pc" ::= #pc  }; "Invalid" ::= $0 };
        Retv (* rule doFetch *)
    }). (* mkFetchStage *)

    Definition mkFetchStage := Build_FetchStage xlen mkFetchStageModule%kami.
    End Section'mkFetchStage.
End mkFetchStage.

