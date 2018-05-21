Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Definition InstTypeFields := (STRUCT {
    "rs1" :: (Maybe RegType);
    "rs2" :: (Maybe RegType);
    "rs3" :: (Maybe RegType);
    "dst" :: (Maybe RegType);
    "imm" :: ImmType}).
Definition InstType  := Struct (InstTypeFields).

Definition toInstType (inst: Instruction): InstType := 
                LET i : (Maybe RegType) <- STRUCT {  "$tag" ::= $0; "Valid" ::= #RtGpr_v; "Invalid" ::= $0 }

                LET f : (Maybe RegType) <- STRUCT {  "$tag" ::= $0; "Valid" ::= #RtFpu_v; "Invalid" ::= $0 }

                LET n : (Maybe RegType) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }

                LET ret : InstType <- null

                If (&& (== #ret STRUCT {  "$tag" ::= $0; "Valid" ::= #RtGpr_v; "Invalid" ::= $0 }) (==  getInstFields(#inst) $0))
        then                 BKSTMTS {
                Assign ret.dst = STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }
;
        Retv

                Ret #ret

.

