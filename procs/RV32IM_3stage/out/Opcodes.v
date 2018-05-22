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

(* * interface ToInstType *)
Record ToInstType := {
    ToInstType'interface: Modules;
    ToInstType'toInstType : string;
}.

Module mkToInstType.
    Section Section'mkToInstType.
    Variable instancePrefix: string.
               Let getInstFields := mkGetInstFields (instancePrefix--"getInstFields").
    Definition mkToInstTypeModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance getInstFields :: nil))
       with Method instancePrefix--"toInstType" (inst : Instruction) : InstType :=
        LET i : (Maybe RegType) <- STRUCT {  "$tag" ::= $0; "Valid" ::= #RtGpr_v; "Invalid" ::= $0 };
        LET f : (Maybe RegType) <- STRUCT {  "$tag" ::= $0; "Valid" ::= #RtFpu_v; "Invalid" ::= $0 };
        LET n : (Maybe RegType) <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        LET ret : InstType <- null;
        If ((#ret == STRUCT {  "$tag" ::= $0; "Valid" ::= #RtGpr_v; "Invalid" ::= $0 }) && ( getInstFieldsgetInstFields(#inst) == $0))
        then                 BKSTMTS {
                Assign ret.dst = STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
;
        Retv;
        Ret #ret

    }). (* mkToInstType *)

    Definition mkToInstType := Build_ToInstType mkToInstTypeModule%kami (instancePrefix--"toInstType").
    End Section'mkToInstType.
End mkToInstType.

