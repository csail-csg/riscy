Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import BRAMCore.
Require Import Connectable.
Require Import RegFile.
Require Import Vector.
Require Import Ehr.
Require Import FIFOG.
Require Import GenericAtomicMem.
Require Import PolymorphicMem.
Require Import Port.
Definition ReadOnlyMemReqFields (addrSz : nat) (logNumBytes : nat) := (STRUCT {
    "addr" :: (Bit addrSz)}).
Definition ReadOnlyMemReq  (addrSz : nat) (logNumBytes : nat) := Struct (ReadOnlyMemReqFields addrSz logNumBytes).

Definition ReadOnlyMemRespFields (logNumBytes : nat) := (STRUCT {
    "data" :: (Bit (TMul 8 (TExp logNumBytes)))}).
Definition ReadOnlyMemResp  (logNumBytes : nat) := Struct (ReadOnlyMemRespFields logNumBytes).

Definition CoarseMemReqFields (addrSz : nat) (logNumBytes : nat) := (STRUCT {
    "write" :: Bool;
    "addr" :: (Bit addrSz);
    "data" :: (Bit (TMul 8 (TExp logNumBytes)))}).
Definition CoarseMemReq  (addrSz : nat) (logNumBytes : nat) := Struct (CoarseMemReqFields addrSz logNumBytes).

Definition CoarseMemRespFields (logNumBytes : nat) := (STRUCT {
    "write" :: Bool;
    "data" :: (Bit (TMul 8 (TExp logNumBytes)))}).
Definition CoarseMemResp  (logNumBytes : nat) := Struct (CoarseMemRespFields logNumBytes).

Definition ByteEnMemReqFields (addrSz : nat) (logNumBytes : nat) := (STRUCT {
    "write_en" :: (Bit (TExp logNumBytes));
    "addr" :: (Bit addrSz);
    "data" :: (Bit (TMul 8 (TExp logNumBytes)))}).
Definition ByteEnMemReq  (addrSz : nat) (logNumBytes : nat) := Struct (ByteEnMemReqFields addrSz logNumBytes).

Definition (ByteEnMemResp logNumBytes) := (CoarseMemResp logNumBytes).

Definition AtomicMemOpFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition AtomicMemOp := (Struct AtomicMemOpFields).
Notation None := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation Swap := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation Add := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation Xor := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation And := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation Or := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation Min := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation Max := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation Minu := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Notation Maxu := (STRUCT { "$tag" ::= $$(natToWord 4 9) })%kami_expr.
Definition AtomicMemReqFields (addrSz : nat) (logNumBytes : nat) := (STRUCT {
    "write_en" :: (Bit (TExp logNumBytes));
    "atomic_op" :: AtomicMemOp;
    "addr" :: (Bit addrSz);
    "data" :: (Bit (TMul 8 (TExp logNumBytes)))}).
Definition AtomicMemReq  (addrSz : nat) (logNumBytes : nat) := Struct (AtomicMemReqFields addrSz logNumBytes).

Definition (AtomicMemResp logNumBytes) := (CoarseMemResp logNumBytes).

Definition (ReadOnlyMemServerPort addrSz logNumBytes) := (ServerPort (ReadOnlyMemReq addrSz logNumBytes) (ReadOnlyMemResp logNumBytes)).

Definition (ReadOnlyMemClientPort addrSz logNumBytes) := (ClientPort (ReadOnlyMemReq addrSz logNumBytes) (ReadOnlyMemResp logNumBytes)).

Definition (CoarseMemServerPort addrSz logNumBytes) := (ServerPort (CoarseMemReq addrSz logNumBytes) (CoarseMemResp logNumBytes)).

Definition (CoarseMemClientPort addrSz logNumBytes) := (ClientPort (CoarseMemReq addrSz logNumBytes) (CoarseMemResp logNumBytes)).

Definition (ByteEnMemServerPort addrSz logNumBytes) := (ServerPort (ByteEnMemReq addrSz logNumBytes) (ByteEnMemResp logNumBytes)).

Definition (ByteEnMemClientPort addrSz logNumBytes) := (ClientPort (ByteEnMemReq addrSz logNumBytes) (ByteEnMemResp logNumBytes)).

Definition (AtomicMemServerPort addrSz logNumBytes) := (ServerPort (AtomicMemReq addrSz logNumBytes) (AtomicMemResp logNumBytes)).

Definition (AtomicMemClientPort addrSz logNumBytes) := (ClientPort (AtomicMemReq addrSz logNumBytes) (AtomicMemResp logNumBytes)).

Definition (ReadOnlyMem32Req addrSz) := (ReadOnlyMemReq addrSz 2).

Definition ReadOnlyMem32Resp := (ReadOnlyMemResp 2).

Definition (ReadOnlyMem32ServerPort addrSz) := (ReadOnlyMemServerPort addrSz 2).

Definition (ReadOnlyMem32ClientPort addrSz) := (ReadOnlyMemClientPort addrSz 2).

Definition (CoarseMem32Req addrSz) := (CoarseMemReq addrSz 2).

Definition CoarseMem32Resp := (CoarseMemResp 2).

Definition (CoarseMem32ServerPort addrSz) := (CoarseMemServerPort addrSz 2).

Definition (CoarseMem32ClientPort addrSz) := (CoarseMemClientPort addrSz 2).

Definition (ByteEnMem32Req addrSz) := (ByteEnMemReq addrSz 2).

Definition ByteEnMem32Resp := (ByteEnMemResp 2).

Definition (ByteEnMem32ServerPort addrSz) := (ByteEnMemServerPort addrSz 2).

Definition (ByteEnMem32ClientPort addrSz) := (ByteEnMemClientPort addrSz 2).

Definition (AtomicMem32Req addrSz) := (AtomicMemReq addrSz 2).

Definition AtomicMem32Resp := (AtomicMemResp 2).

Definition (AtomicMem32ServerPort addrSz) := (AtomicMemServerPort addrSz 2).

Definition (AtomicMem32ClientPort addrSz) := (AtomicMemClientPort addrSz 2).

Definition (ReadOnlyMem64Req addrSz) := (ReadOnlyMemReq addrSz 3).

Definition ReadOnlyMem64Resp := (ReadOnlyMemResp 3).

Definition (ReadOnlyMem64ServerPort addrSz) := (ReadOnlyMemServerPort addrSz 3).

Definition (ReadOnlyMem64ClientPort addrSz) := (ReadOnlyMemClientPort addrSz 3).

Definition (CoarseMem64Req addrSz) := (CoarseMemReq addrSz 3).

Definition CoarseMem64Resp := (CoarseMemResp 3).

Definition (CoarseMem64ServerPort addrSz) := (CoarseMemServerPort addrSz 3).

Definition (CoarseMem64ClientPort addrSz) := (CoarseMemClientPort addrSz 3).

Definition (ByteEnMem64Req addrSz) := (ByteEnMemReq addrSz 3).

Definition ByteEnMem64Resp := (ByteEnMemResp 3).

Definition (ByteEnMem64ServerPort addrSz) := (ByteEnMemServerPort addrSz 3).

Definition (ByteEnMem64ClientPort addrSz) := (ByteEnMemClientPort addrSz 3).

Definition (AtomicMem64Req addrSz) := (AtomicMemReq addrSz 3).

Definition AtomicMem64Resp := (AtomicMemResp 3).

Definition (AtomicMem64ServerPort addrSz) := (AtomicMemServerPort addrSz 3).

Definition (AtomicMem64ClientPort addrSz) := (AtomicMemClientPort addrSz 3).

Definition MemTypeFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition MemType := (Struct MemTypeFields).
Notation ReadOnly := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation Coarse := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation ByteEn := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
Notation Atomic := (STRUCT { "$tag" ::= $$(natToWord 2 3) })%kami_expr.
Definition TaggedMemServerPortFields (addrSz : nat) (logNumBytes : nat) := (STRUCT {
    "$tag" :: (Bit 8);
    "ReadOnly" :: (ReadOnlyMemServerPort addrSz logNumBytes);
    "Coarse" :: (CoarseMemServerPort addrSz logNumBytes);
    "ByteEn" :: (ByteEnMemServerPort addrSz logNumBytes);
    "Atomic" :: (AtomicMemServerPort addrSz logNumBytes)}).
Definition TaggedMemServerPort (addrSz : nat) (logNumBytes : nat) := Struct (TaggedMemServerPortFields addrSz logNumBytes).
(* * interface CoarseBRAM#(addrSz, logNumBytes, numBytes) *)
Record CoarseBRAM (addrSz : nat) (logNumBytes : nat) (numBytes : nat) := {
    CoarseBRAM'modules: Modules;
    CoarseBRAM'portA : (CoarseMemServerPort addrSz logNumBytes);
}.

(* * interface ByteEnBRAM#(addrSz, logNumBytes, numBytes) *)
Record ByteEnBRAM (addrSz : nat) (logNumBytes : nat) (numBytes : nat) := {
    ByteEnBRAM'modules: Modules;
    ByteEnBRAM'portA : (ByteEnMemServerPort addrSz logNumBytes);
}.

(* * interface AtomicBRAM#(addrSz, logNumBytes, numBytes) *)
Record AtomicBRAM (addrSz : nat) (logNumBytes : nat) (numBytes : nat) := {
    AtomicBRAM'modules: Modules;
    AtomicBRAM'portA : (AtomicMemServerPort addrSz logNumBytes);
}.

Definition AtomicBRAMPendingReqFields (logNumBytes : nat) := (STRUCT {
    "write_en" :: (Bit (TExp logNumBytes));
    "atomic_op" :: AtomicMemOp;
    "rmw_write" :: Bool}).
Definition AtomicBRAMPendingReq  (logNumBytes : nat) := Struct (AtomicBRAMPendingReqFields logNumBytes).

Definition MemBusItemFields (memReqT : Type) (memRespT : Type) (addrSz : nat) := (STRUCT {
    "addr_mask" :: (Bit addrSz);
    "addr_match" :: (Bit addrSz);
    "ifc" :: (ServerPort memReqT memRespT)}).
Definition MemBusItem  (memReqT : Type) (memRespT : Type) (addrSz : nat) := Struct (MemBusItemFields memReqT memRespT addrSz).

Definition MixedMemBusItemFields (addrSz : nat) (logNumBytes : nat) := (STRUCT {
    "addr_mask" :: (Bit addrSz);
    "addr_match" :: (Bit addrSz);
    "ifc" :: (TaggedMemServerPort addrSz logNumBytes)}).
Definition MixedMemBusItem  (addrSz : nat) (logNumBytes : nat) := Struct (MixedMemBusItemFields addrSz logNumBytes).

(* * interface MixedAtomicMemBus#(nClients, addrSz, logNumBytes) *)
Record MixedAtomicMemBus (nClients : nat) (addrSz : nat) (logNumBytes : nat) := {
    MixedAtomicMemBus'modules: Modules;
    MixedAtomicMemBus'clients : (Vector nClients (AtomicMemServerPort addrSz logNumBytes));
    MixedAtomicMemBus'getMemType : string;
}.

