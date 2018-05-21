Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVTypes.
Require Import ConcatReg.
Require Import ConfigReg.
Require Import DefaultValue.
Require Import RegUtil.
Require Import Vector.
Definition CsrReturnFields (xlen : nat) := (STRUCT {
    "$tag" :: (Bit 8);
    "Exception$exception" :: TrapCause;
    "Exception$trapHandlerPC" :: (Bit xlen);
    "RedirectPC" :: (Bit xlen);
    "CsrData" :: (Bit xlen);
    "None" :: void}).
Definition CsrReturn (xlen : nat) := Struct (CsrReturnFields xlen).
(* * interface RVCsrFile#(xlen) *)
Record RVCsrFile (xlen : nat) := {
    RVCsrFile'interface: Modules;
    RVCsrFile'wr : string;
    RVCsrFile'vmI : string;
    RVCsrFile'vmD : string;
    RVCsrFile'csrState : string;
    RVCsrFile'readyInterrupt : string;
    RVCsrFile'wakeFromWFI : string;
}.

Module mkRVCsrFile.
    Section Section'mkRVCsrFile.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable hartid: Data.
    Variable time_counter: (word 64).
    Variable mtip: bool.
    Variable msip: bool.
    Variable meip: bool.
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Definition getCSR (csr: CSR): (CSRReg Data) := 
                Ret null

.

    Definition isLegalCSR (csr: CSR): Bool := 
                Ret null

.

    Definition readyInterruptFunc: (Maybe InterruptCause) := 
