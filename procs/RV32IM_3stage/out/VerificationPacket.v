Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Definition VerificationPacketFields := (STRUCT {
    "skippedPackets" :: (Bit 64);
    "pc" :: (Bit 64);
    "instruction" :: (Bit 32);
    "data" :: (Bit 64);
    "addr" :: (Bit 64);
    "dst" :: (Bit 7);
    "exception" :: Bool;
    "interrupt" :: Bool;
    "cause" :: (Bit 4)}).
Definition VerificationPacket  := Struct (VerificationPacketFields).

