Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import FShow.
Require Import Vector.
Definition XLEN := 32.

Definition DataSz := XLEN.

Definition Data := (Bit 32).

Definition CacheLineSz := 512.

Definition InstSz := 32.

Definition Instruction := (Bit InstSz).

Definition AddrSz := XLEN.

Definition PAddrSz := 64.

Definition AsidSz := 10.

Definition Asid := (Bit AsidSz).

Definition RVRoundModeFields := (STRUCT { "$tag" :: (Bit 3) }).
Definition RVRoundMode := (Struct RVRoundModeFields).
Notation RNE := (STRUCT { "$tag" ::= $$(natToWord 3 0) })%kami_expr.
Notation RTZ := (STRUCT { "$tag" ::= $$(natToWord 3 1) })%kami_expr.
Notation RDN := (STRUCT { "$tag" ::= $$(natToWord 3 2) })%kami_expr.
Notation RUP := (STRUCT { "$tag" ::= $$(natToWord 3 3) })%kami_expr.
Notation RMM := (STRUCT { "$tag" ::= $$(natToWord 3 4) })%kami_expr.
Notation RDyn := (STRUCT { "$tag" ::= $$(natToWord 3 5) })%kami_expr.
(* * interface Pack#(t, sz) *)
Record Pack (t : Kind) (sz : nat) := {
    Pack'modules: Modules;
    Pack'unpack : string;
    Pack'pack : string;
}.

Module module'mkPackRVRoundMode.
    Section Section'mkPackRVRoundMode.
    Variable instancePrefix: string.
            Definition mkPackRVRoundModeModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 3)) : RVRoundMode :=
    If (#v == $0) then (
        Ret RNE

   ) else (
    If (#v == $1) then (
        Ret RTZ

   ) else (
    If (#v == $2) then (
        Ret RDN

   ) else (
    If (#v == $3) then (
        Ret RUP

   ) else (
    If (#v == $4) then (
        Ret RMM

   ) else (
    If (#v == $7) then (
        Ret RDyn

   ) else (
        Ret RDyn
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


       with Method instancePrefix--"pack" (v : RVRoundMode) : (Bit 3) :=
    If (#v!RVRoundModeFields@."$tag" == $0) then (
        Ret $0

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $1) then (
        Ret $1

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $2) then (
        Ret $2

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $3) then (
        Ret $3

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $4) then (
        Ret $4

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $7) then (
        Ret $7

   ) else (
        Ret $7
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


    }). (* mkPackRVRoundMode *)

(* Module mkPackRVRoundMode type Module#(Pack#(RVRoundMode, 3)) return type Pack#(RVRoundMode, 3) *)
    Definition mkPackRVRoundMode := Build_Pack (RVRoundMode) (3) mkPackRVRoundModeModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackRVRoundMode.
End module'mkPackRVRoundMode.

Definition mkPackRVRoundMode := module'mkPackRVRoundMode.mkPackRVRoundMode.

Definition OpcodeFields := (STRUCT { "$tag" :: (Bit 5) }).
Definition Opcode := (Struct OpcodeFields).
Notation Load := (STRUCT { "$tag" ::= $$(natToWord 5 0) })%kami_expr.
Notation LoadFp := (STRUCT { "$tag" ::= $$(natToWord 5 1) })%kami_expr.
Notation MiscMem := (STRUCT { "$tag" ::= $$(natToWord 5 2) })%kami_expr.
Notation OpImm := (STRUCT { "$tag" ::= $$(natToWord 5 3) })%kami_expr.
Notation Auipc := (STRUCT { "$tag" ::= $$(natToWord 5 4) })%kami_expr.
Notation OpImm32 := (STRUCT { "$tag" ::= $$(natToWord 5 5) })%kami_expr.
Notation Store := (STRUCT { "$tag" ::= $$(natToWord 5 6) })%kami_expr.
Notation StoreFp := (STRUCT { "$tag" ::= $$(natToWord 5 7) })%kami_expr.
Notation Amo := (STRUCT { "$tag" ::= $$(natToWord 5 8) })%kami_expr.
Notation Op := (STRUCT { "$tag" ::= $$(natToWord 5 9) })%kami_expr.
Notation Lui := (STRUCT { "$tag" ::= $$(natToWord 5 10) })%kami_expr.
Notation Op32 := (STRUCT { "$tag" ::= $$(natToWord 5 11) })%kami_expr.
Notation Fmadd := (STRUCT { "$tag" ::= $$(natToWord 5 12) })%kami_expr.
Notation Fmsub := (STRUCT { "$tag" ::= $$(natToWord 5 13) })%kami_expr.
Notation Fnmsub := (STRUCT { "$tag" ::= $$(natToWord 5 14) })%kami_expr.
Notation Fnmadd := (STRUCT { "$tag" ::= $$(natToWord 5 15) })%kami_expr.
Notation OpFp := (STRUCT { "$tag" ::= $$(natToWord 5 16) })%kami_expr.
Notation Branch := (STRUCT { "$tag" ::= $$(natToWord 5 17) })%kami_expr.
Notation Jalr := (STRUCT { "$tag" ::= $$(natToWord 5 18) })%kami_expr.
Notation Jal := (STRUCT { "$tag" ::= $$(natToWord 5 19) })%kami_expr.
Notation System := (STRUCT { "$tag" ::= $$(natToWord 5 20) })%kami_expr.
Module module'mkPackOpcode.
    Section Section'mkPackOpcode.
    Variable instancePrefix: string.
            Definition mkPackOpcodeModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 7)) : Opcode :=
    If (#v == $3) then (
        Ret Load

   ) else (
    If (#v == $7) then (
        Ret LoadFp

   ) else (
    If (#v == $15) then (
        Ret MiscMem

   ) else (
    If (#v == $19) then (
        Ret OpImm

   ) else (
    If (#v == $23) then (
        Ret Auipc

   ) else (
    If (#v == $27) then (
        Ret OpImm32

   ) else (
    If (#v == $35) then (
        Ret Store

   ) else (
    If (#v == $39) then (
        Ret StoreFp

   ) else (
    If (#v == $47) then (
        Ret Amo

   ) else (
    If (#v == $51) then (
        Ret Op

   ) else (
    If (#v == $55) then (
        Ret Lui

   ) else (
    If (#v == $59) then (
        Ret Op32

   ) else (
    If (#v == $67) then (
        Ret Fmadd

   ) else (
    If (#v == $71) then (
        Ret Fmsub

   ) else (
    If (#v == $75) then (
        Ret Fnmsub

   ) else (
    If (#v == $79) then (
        Ret Fnmadd

   ) else (
    If (#v == $83) then (
        Ret OpFp

   ) else (
    If (#v == $99) then (
        Ret Branch

   ) else (
    If (#v == $103) then (
        Ret Jalr

   ) else (
    If (#v == $111) then (
        Ret Jal

   ) else (
    If (#v == $115) then (
        Ret System

   ) else (
        Ret System
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


       with Method instancePrefix--"pack" (v : Opcode) : (Bit 7) :=
    If (#v!OpcodeFields@."$tag" == $3) then (
        Ret $3

   ) else (
    If (#v!OpcodeFields@."$tag" == $7) then (
        Ret $7

   ) else (
    If (#v!OpcodeFields@."$tag" == $15) then (
        Ret $15

   ) else (
    If (#v!OpcodeFields@."$tag" == $19) then (
        Ret $19

   ) else (
    If (#v!OpcodeFields@."$tag" == $23) then (
        Ret $23

   ) else (
    If (#v!OpcodeFields@."$tag" == $27) then (
        Ret $27

   ) else (
    If (#v!OpcodeFields@."$tag" == $35) then (
        Ret $35

   ) else (
    If (#v!OpcodeFields@."$tag" == $39) then (
        Ret $39

   ) else (
    If (#v!OpcodeFields@."$tag" == $47) then (
        Ret $47

   ) else (
    If (#v!OpcodeFields@."$tag" == $51) then (
        Ret $51

   ) else (
    If (#v!OpcodeFields@."$tag" == $55) then (
        Ret $55

   ) else (
    If (#v!OpcodeFields@."$tag" == $59) then (
        Ret $59

   ) else (
    If (#v!OpcodeFields@."$tag" == $67) then (
        Ret $67

   ) else (
    If (#v!OpcodeFields@."$tag" == $71) then (
        Ret $71

   ) else (
    If (#v!OpcodeFields@."$tag" == $75) then (
        Ret $75

   ) else (
    If (#v!OpcodeFields@."$tag" == $79) then (
        Ret $79

   ) else (
    If (#v!OpcodeFields@."$tag" == $83) then (
        Ret $83

   ) else (
    If (#v!OpcodeFields@."$tag" == $99) then (
        Ret $99

   ) else (
    If (#v!OpcodeFields@."$tag" == $103) then (
        Ret $103

   ) else (
    If (#v!OpcodeFields@."$tag" == $111) then (
        Ret $111

   ) else (
    If (#v!OpcodeFields@."$tag" == $115) then (
        Ret $115

   ) else (
        Ret $0
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


    }). (* mkPackOpcode *)

(* Module mkPackOpcode type Module#(Pack#(Opcode, 7)) return type Pack#(Opcode, 7) *)
    Definition mkPackOpcode := Build_Pack (Opcode) (7) mkPackOpcodeModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackOpcode.
End module'mkPackOpcode.

Definition mkPackOpcode := module'mkPackOpcode.mkPackOpcode.

Definition CSRFields := (STRUCT { "$tag" :: (Bit 7) }).
Definition CSR := (Struct CSRFields).
Notation CSRustatus := (STRUCT { "$tag" ::= $$(natToWord 7 0) })%kami_expr.
Notation CSRuie := (STRUCT { "$tag" ::= $$(natToWord 7 1) })%kami_expr.
Notation CSRutvec := (STRUCT { "$tag" ::= $$(natToWord 7 2) })%kami_expr.
Notation CSRuscratch := (STRUCT { "$tag" ::= $$(natToWord 7 3) })%kami_expr.
Notation CSRuepc := (STRUCT { "$tag" ::= $$(natToWord 7 4) })%kami_expr.
Notation CSRucause := (STRUCT { "$tag" ::= $$(natToWord 7 5) })%kami_expr.
Notation CSRubadaddr := (STRUCT { "$tag" ::= $$(natToWord 7 6) })%kami_expr.
Notation CSRuip := (STRUCT { "$tag" ::= $$(natToWord 7 7) })%kami_expr.
Notation CSRfflags := (STRUCT { "$tag" ::= $$(natToWord 7 8) })%kami_expr.
Notation CSRfrm := (STRUCT { "$tag" ::= $$(natToWord 7 9) })%kami_expr.
Notation CSRfcsr := (STRUCT { "$tag" ::= $$(natToWord 7 10) })%kami_expr.
Notation CSRcycle := (STRUCT { "$tag" ::= $$(natToWord 7 11) })%kami_expr.
Notation CSRtime := (STRUCT { "$tag" ::= $$(natToWord 7 12) })%kami_expr.
Notation CSRinstret := (STRUCT { "$tag" ::= $$(natToWord 7 13) })%kami_expr.
Notation CSRcycleh := (STRUCT { "$tag" ::= $$(natToWord 7 14) })%kami_expr.
Notation CSRtimeh := (STRUCT { "$tag" ::= $$(natToWord 7 15) })%kami_expr.
Notation CSRinstreth := (STRUCT { "$tag" ::= $$(natToWord 7 16) })%kami_expr.
Notation CSRsstatus := (STRUCT { "$tag" ::= $$(natToWord 7 17) })%kami_expr.
Notation CSRsedeleg := (STRUCT { "$tag" ::= $$(natToWord 7 18) })%kami_expr.
Notation CSRsideleg := (STRUCT { "$tag" ::= $$(natToWord 7 19) })%kami_expr.
Notation CSRsie := (STRUCT { "$tag" ::= $$(natToWord 7 20) })%kami_expr.
Notation CSRstvec := (STRUCT { "$tag" ::= $$(natToWord 7 21) })%kami_expr.
Notation CSRsscratch := (STRUCT { "$tag" ::= $$(natToWord 7 22) })%kami_expr.
Notation CSRsepc := (STRUCT { "$tag" ::= $$(natToWord 7 23) })%kami_expr.
Notation CSRscause := (STRUCT { "$tag" ::= $$(natToWord 7 24) })%kami_expr.
Notation CSRsbadaddr := (STRUCT { "$tag" ::= $$(natToWord 7 25) })%kami_expr.
Notation CSRsip := (STRUCT { "$tag" ::= $$(natToWord 7 26) })%kami_expr.
Notation CSRsptbr := (STRUCT { "$tag" ::= $$(natToWord 7 27) })%kami_expr.
Notation CSRscycle := (STRUCT { "$tag" ::= $$(natToWord 7 28) })%kami_expr.
Notation CSRstime := (STRUCT { "$tag" ::= $$(natToWord 7 29) })%kami_expr.
Notation CSRsinstret := (STRUCT { "$tag" ::= $$(natToWord 7 30) })%kami_expr.
Notation CSRscycleh := (STRUCT { "$tag" ::= $$(natToWord 7 31) })%kami_expr.
Notation CSRstimeh := (STRUCT { "$tag" ::= $$(natToWord 7 32) })%kami_expr.
Notation CSRsinstreth := (STRUCT { "$tag" ::= $$(natToWord 7 33) })%kami_expr.
Notation CSRhstatus := (STRUCT { "$tag" ::= $$(natToWord 7 34) })%kami_expr.
Notation CSRhedeleg := (STRUCT { "$tag" ::= $$(natToWord 7 35) })%kami_expr.
Notation CSRhideleg := (STRUCT { "$tag" ::= $$(natToWord 7 36) })%kami_expr.
Notation CSRhie := (STRUCT { "$tag" ::= $$(natToWord 7 37) })%kami_expr.
Notation CSRhtvec := (STRUCT { "$tag" ::= $$(natToWord 7 38) })%kami_expr.
Notation CSRhscratch := (STRUCT { "$tag" ::= $$(natToWord 7 39) })%kami_expr.
Notation CSRhepc := (STRUCT { "$tag" ::= $$(natToWord 7 40) })%kami_expr.
Notation CSRhcause := (STRUCT { "$tag" ::= $$(natToWord 7 41) })%kami_expr.
Notation CSRhbadaddr := (STRUCT { "$tag" ::= $$(natToWord 7 42) })%kami_expr.
Notation CSRhcycle := (STRUCT { "$tag" ::= $$(natToWord 7 43) })%kami_expr.
Notation CSRhtime := (STRUCT { "$tag" ::= $$(natToWord 7 44) })%kami_expr.
Notation CSRhinstret := (STRUCT { "$tag" ::= $$(natToWord 7 45) })%kami_expr.
Notation CSRhcycleh := (STRUCT { "$tag" ::= $$(natToWord 7 46) })%kami_expr.
Notation CSRhtimeh := (STRUCT { "$tag" ::= $$(natToWord 7 47) })%kami_expr.
Notation CSRhinstreth := (STRUCT { "$tag" ::= $$(natToWord 7 48) })%kami_expr.
Notation CSRmisa := (STRUCT { "$tag" ::= $$(natToWord 7 49) })%kami_expr.
Notation CSRmvendorid := (STRUCT { "$tag" ::= $$(natToWord 7 50) })%kami_expr.
Notation CSRmarchid := (STRUCT { "$tag" ::= $$(natToWord 7 51) })%kami_expr.
Notation CSRmimpid := (STRUCT { "$tag" ::= $$(natToWord 7 52) })%kami_expr.
Notation CSRmhartid := (STRUCT { "$tag" ::= $$(natToWord 7 53) })%kami_expr.
Notation CSRmstatus := (STRUCT { "$tag" ::= $$(natToWord 7 54) })%kami_expr.
Notation CSRmedeleg := (STRUCT { "$tag" ::= $$(natToWord 7 55) })%kami_expr.
Notation CSRmideleg := (STRUCT { "$tag" ::= $$(natToWord 7 56) })%kami_expr.
Notation CSRmie := (STRUCT { "$tag" ::= $$(natToWord 7 57) })%kami_expr.
Notation CSRmtvec := (STRUCT { "$tag" ::= $$(natToWord 7 58) })%kami_expr.
Notation CSRmscratch := (STRUCT { "$tag" ::= $$(natToWord 7 59) })%kami_expr.
Notation CSRmepc := (STRUCT { "$tag" ::= $$(natToWord 7 60) })%kami_expr.
Notation CSRmcause := (STRUCT { "$tag" ::= $$(natToWord 7 61) })%kami_expr.
Notation CSRmbadaddr := (STRUCT { "$tag" ::= $$(natToWord 7 62) })%kami_expr.
Notation CSRmip := (STRUCT { "$tag" ::= $$(natToWord 7 63) })%kami_expr.
Notation CSRmbase := (STRUCT { "$tag" ::= $$(natToWord 7 64) })%kami_expr.
Notation CSRmbound := (STRUCT { "$tag" ::= $$(natToWord 7 65) })%kami_expr.
Notation CSRmibase := (STRUCT { "$tag" ::= $$(natToWord 7 66) })%kami_expr.
Notation CSRmibound := (STRUCT { "$tag" ::= $$(natToWord 7 67) })%kami_expr.
Notation CSRmdbase := (STRUCT { "$tag" ::= $$(natToWord 7 68) })%kami_expr.
Notation CSRmdbound := (STRUCT { "$tag" ::= $$(natToWord 7 69) })%kami_expr.
Notation CSRmcycle := (STRUCT { "$tag" ::= $$(natToWord 7 70) })%kami_expr.
Notation CSRmtime := (STRUCT { "$tag" ::= $$(natToWord 7 71) })%kami_expr.
Notation CSRminstret := (STRUCT { "$tag" ::= $$(natToWord 7 72) })%kami_expr.
Notation CSRmcycleh := (STRUCT { "$tag" ::= $$(natToWord 7 73) })%kami_expr.
Notation CSRmtimeh := (STRUCT { "$tag" ::= $$(natToWord 7 74) })%kami_expr.
Notation CSRminstreth := (STRUCT { "$tag" ::= $$(natToWord 7 75) })%kami_expr.
Notation CSRmucounteren := (STRUCT { "$tag" ::= $$(natToWord 7 76) })%kami_expr.
Notation CSRmscounteren := (STRUCT { "$tag" ::= $$(natToWord 7 77) })%kami_expr.
Notation CSRmhcounteren := (STRUCT { "$tag" ::= $$(natToWord 7 78) })%kami_expr.
Notation CSRmucycle_delta := (STRUCT { "$tag" ::= $$(natToWord 7 79) })%kami_expr.
Notation CSRmutime_delta := (STRUCT { "$tag" ::= $$(natToWord 7 80) })%kami_expr.
Notation CSRmuinstret_delta := (STRUCT { "$tag" ::= $$(natToWord 7 81) })%kami_expr.
Notation CSRmscycle_delta := (STRUCT { "$tag" ::= $$(natToWord 7 82) })%kami_expr.
Notation CSRmstime_delta := (STRUCT { "$tag" ::= $$(natToWord 7 83) })%kami_expr.
Notation CSRmsinstret_delta := (STRUCT { "$tag" ::= $$(natToWord 7 84) })%kami_expr.
Notation CSRmhcycle_delta := (STRUCT { "$tag" ::= $$(natToWord 7 85) })%kami_expr.
Notation CSRmhtime_delta := (STRUCT { "$tag" ::= $$(natToWord 7 86) })%kami_expr.
Notation CSRmhinstret_delta := (STRUCT { "$tag" ::= $$(natToWord 7 87) })%kami_expr.
Notation CSRmucycle_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 88) })%kami_expr.
Notation CSRmutime_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 89) })%kami_expr.
Notation CSRmuinstret_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 90) })%kami_expr.
Notation CSRmscycle_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 91) })%kami_expr.
Notation CSRmstime_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 92) })%kami_expr.
Notation CSRmsinstret_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 93) })%kami_expr.
Notation CSRmhcycle_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 94) })%kami_expr.
Notation CSRmhtime_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 95) })%kami_expr.
Notation CSRmhinstret_deltah := (STRUCT { "$tag" ::= $$(natToWord 7 96) })%kami_expr.
Module module'mkPackCSR.
    Section Section'mkPackCSR.
    Variable instancePrefix: string.
            Definition mkPackCSRModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 12)) : CSR :=
    If (#v == $0) then (
        Ret CSRustatus

   ) else (
    If (#v == $4) then (
        Ret CSRuie

   ) else (
    If (#v == $5) then (
        Ret CSRutvec

   ) else (
    If (#v == $64) then (
        Ret CSRuscratch

   ) else (
    If (#v == $65) then (
        Ret CSRuepc

   ) else (
    If (#v == $66) then (
        Ret CSRucause

   ) else (
    If (#v == $67) then (
        Ret CSRubadaddr

   ) else (
    If (#v == $68) then (
        Ret CSRuip

   ) else (
    If (#v == $1) then (
        Ret CSRfflags

   ) else (
    If (#v == $2) then (
        Ret CSRfrm

   ) else (
    If (#v == $3) then (
        Ret CSRfcsr

   ) else (
    If (#v == $3072) then (
        Ret CSRcycle

   ) else (
    If (#v == $3073) then (
        Ret CSRtime

   ) else (
    If (#v == $3074) then (
        Ret CSRinstret

   ) else (
    If (#v == $3200) then (
        Ret CSRcycleh

   ) else (
    If (#v == $3201) then (
        Ret CSRtimeh

   ) else (
    If (#v == $3202) then (
        Ret CSRinstreth

   ) else (
    If (#v == $256) then (
        Ret CSRsstatus

   ) else (
    If (#v == $258) then (
        Ret CSRsedeleg

   ) else (
    If (#v == $259) then (
        Ret CSRsideleg

   ) else (
    If (#v == $260) then (
        Ret CSRsie

   ) else (
    If (#v == $261) then (
        Ret CSRstvec

   ) else (
    If (#v == $320) then (
        Ret CSRsscratch

   ) else (
    If (#v == $321) then (
        Ret CSRsepc

   ) else (
    If (#v == $322) then (
        Ret CSRscause

   ) else (
    If (#v == $323) then (
        Ret CSRsbadaddr

   ) else (
    If (#v == $324) then (
        Ret CSRsip

   ) else (
    If (#v == $384) then (
        Ret CSRsptbr

   ) else (
    If (#v == $3328) then (
        Ret CSRscycle

   ) else (
    If (#v == $3329) then (
        Ret CSRstime

   ) else (
    If (#v == $3330) then (
        Ret CSRsinstret

   ) else (
    If (#v == $3456) then (
        Ret CSRscycleh

   ) else (
    If (#v == $3457) then (
        Ret CSRstimeh

   ) else (
    If (#v == $3458) then (
        Ret CSRsinstreth

   ) else (
    If (#v == $512) then (
        Ret CSRhstatus

   ) else (
    If (#v == $514) then (
        Ret CSRhedeleg

   ) else (
    If (#v == $515) then (
        Ret CSRhideleg

   ) else (
    If (#v == $516) then (
        Ret CSRhie

   ) else (
    If (#v == $517) then (
        Ret CSRhtvec

   ) else (
    If (#v == $576) then (
        Ret CSRhscratch

   ) else (
    If (#v == $577) then (
        Ret CSRhepc

   ) else (
    If (#v == $578) then (
        Ret CSRhcause

   ) else (
    If (#v == $579) then (
        Ret CSRhbadaddr

   ) else (
    If (#v == $3584) then (
        Ret CSRhcycle

   ) else (
    If (#v == $3585) then (
        Ret CSRhtime

   ) else (
    If (#v == $3586) then (
        Ret CSRhinstret

   ) else (
    If (#v == $3712) then (
        Ret CSRhcycleh

   ) else (
    If (#v == $3713) then (
        Ret CSRhtimeh

   ) else (
    If (#v == $3714) then (
        Ret CSRhinstreth

   ) else (
    If (#v == $3856) then (
        Ret CSRmisa

   ) else (
    If (#v == $3857) then (
        Ret CSRmvendorid

   ) else (
    If (#v == $3858) then (
        Ret CSRmarchid

   ) else (
    If (#v == $3859) then (
        Ret CSRmimpid

   ) else (
    If (#v == $3860) then (
        Ret CSRmhartid

   ) else (
    If (#v == $768) then (
        Ret CSRmstatus

   ) else (
    If (#v == $770) then (
        Ret CSRmedeleg

   ) else (
    If (#v == $771) then (
        Ret CSRmideleg

   ) else (
    If (#v == $772) then (
        Ret CSRmie

   ) else (
    If (#v == $773) then (
        Ret CSRmtvec

   ) else (
    If (#v == $832) then (
        Ret CSRmscratch

   ) else (
    If (#v == $833) then (
        Ret CSRmepc

   ) else (
    If (#v == $834) then (
        Ret CSRmcause

   ) else (
    If (#v == $835) then (
        Ret CSRmbadaddr

   ) else (
    If (#v == $836) then (
        Ret CSRmip

   ) else (
    If (#v == $896) then (
        Ret CSRmbase

   ) else (
    If (#v == $897) then (
        Ret CSRmbound

   ) else (
    If (#v == $898) then (
        Ret CSRmibase

   ) else (
    If (#v == $899) then (
        Ret CSRmibound

   ) else (
    If (#v == $900) then (
        Ret CSRmdbase

   ) else (
    If (#v == $901) then (
        Ret CSRmdbound

   ) else (
    If (#v == $3840) then (
        Ret CSRmcycle

   ) else (
    If (#v == $3841) then (
        Ret CSRmtime

   ) else (
    If (#v == $3842) then (
        Ret CSRminstret

   ) else (
    If (#v == $3968) then (
        Ret CSRmcycleh

   ) else (
    If (#v == $3969) then (
        Ret CSRmtimeh

   ) else (
    If (#v == $3970) then (
        Ret CSRminstreth

   ) else (
    If (#v == $784) then (
        Ret CSRmucounteren

   ) else (
    If (#v == $785) then (
        Ret CSRmscounteren

   ) else (
    If (#v == $786) then (
        Ret CSRmhcounteren

   ) else (
    If (#v == $1792) then (
        Ret CSRmucycle_delta

   ) else (
    If (#v == $1793) then (
        Ret CSRmutime_delta

   ) else (
    If (#v == $1794) then (
        Ret CSRmuinstret_delta

   ) else (
    If (#v == $1796) then (
        Ret CSRmscycle_delta

   ) else (
    If (#v == $1797) then (
        Ret CSRmstime_delta

   ) else (
    If (#v == $1798) then (
        Ret CSRmsinstret_delta

   ) else (
    If (#v == $1800) then (
        Ret CSRmhcycle_delta

   ) else (
    If (#v == $1801) then (
        Ret CSRmhtime_delta

   ) else (
    If (#v == $1802) then (
        Ret CSRmhinstret_delta

   ) else (
    If (#v == $1920) then (
        Ret CSRmucycle_deltah

   ) else (
    If (#v == $1921) then (
        Ret CSRmutime_deltah

   ) else (
    If (#v == $1922) then (
        Ret CSRmuinstret_deltah

   ) else (
    If (#v == $1924) then (
        Ret CSRmscycle_deltah

   ) else (
    If (#v == $1925) then (
        Ret CSRmstime_deltah

   ) else (
    If (#v == $1926) then (
        Ret CSRmsinstret_deltah

   ) else (
    If (#v == $1928) then (
        Ret CSRmhcycle_deltah

   ) else (
    If (#v == $1929) then (
        Ret CSRmhtime_deltah

   ) else (
    If (#v == $1930) then (
        Ret CSRmhinstret_deltah

   ) else (
        Ret CSRmhinstret_deltah
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


       with Method instancePrefix--"pack" (v : CSR) : (Bit 12) :=
    If (#v!CSRFields@."$tag" == $0) then (
        Ret $0

   ) else (
    If (#v!CSRFields@."$tag" == $4) then (
        Ret $4

   ) else (
    If (#v!CSRFields@."$tag" == $5) then (
        Ret $5

   ) else (
    If (#v!CSRFields@."$tag" == $64) then (
        Ret $64

   ) else (
    If (#v!CSRFields@."$tag" == $65) then (
        Ret $65

   ) else (
    If (#v!CSRFields@."$tag" == $66) then (
        Ret $66

   ) else (
    If (#v!CSRFields@."$tag" == $67) then (
        Ret $67

   ) else (
    If (#v!CSRFields@."$tag" == $68) then (
        Ret $68

   ) else (
    If (#v!CSRFields@."$tag" == $1) then (
        Ret $1

   ) else (
    If (#v!CSRFields@."$tag" == $2) then (
        Ret $2

   ) else (
    If (#v!CSRFields@."$tag" == $3) then (
        Ret $3

   ) else (
    If (#v!CSRFields@."$tag" == $3072) then (
        Ret $3072

   ) else (
    If (#v!CSRFields@."$tag" == $3073) then (
        Ret $3073

   ) else (
    If (#v!CSRFields@."$tag" == $3074) then (
        Ret $3074

   ) else (
    If (#v!CSRFields@."$tag" == $3200) then (
        Ret $3200

   ) else (
    If (#v!CSRFields@."$tag" == $3201) then (
        Ret $3201

   ) else (
    If (#v!CSRFields@."$tag" == $3202) then (
        Ret $3202

   ) else (
    If (#v!CSRFields@."$tag" == $256) then (
        Ret $256

   ) else (
    If (#v!CSRFields@."$tag" == $258) then (
        Ret $258

   ) else (
    If (#v!CSRFields@."$tag" == $259) then (
        Ret $259

   ) else (
    If (#v!CSRFields@."$tag" == $260) then (
        Ret $260

   ) else (
    If (#v!CSRFields@."$tag" == $261) then (
        Ret $261

   ) else (
    If (#v!CSRFields@."$tag" == $320) then (
        Ret $320

   ) else (
    If (#v!CSRFields@."$tag" == $321) then (
        Ret $321

   ) else (
    If (#v!CSRFields@."$tag" == $322) then (
        Ret $322

   ) else (
    If (#v!CSRFields@."$tag" == $323) then (
        Ret $323

   ) else (
    If (#v!CSRFields@."$tag" == $324) then (
        Ret $324

   ) else (
    If (#v!CSRFields@."$tag" == $384) then (
        Ret $384

   ) else (
    If (#v!CSRFields@."$tag" == $3328) then (
        Ret $3328

   ) else (
    If (#v!CSRFields@."$tag" == $3329) then (
        Ret $3329

   ) else (
    If (#v!CSRFields@."$tag" == $3330) then (
        Ret $3330

   ) else (
    If (#v!CSRFields@."$tag" == $3456) then (
        Ret $3456

   ) else (
    If (#v!CSRFields@."$tag" == $3457) then (
        Ret $3457

   ) else (
    If (#v!CSRFields@."$tag" == $3458) then (
        Ret $3458

   ) else (
    If (#v!CSRFields@."$tag" == $512) then (
        Ret $512

   ) else (
    If (#v!CSRFields@."$tag" == $514) then (
        Ret $514

   ) else (
    If (#v!CSRFields@."$tag" == $515) then (
        Ret $515

   ) else (
    If (#v!CSRFields@."$tag" == $516) then (
        Ret $516

   ) else (
    If (#v!CSRFields@."$tag" == $517) then (
        Ret $517

   ) else (
    If (#v!CSRFields@."$tag" == $576) then (
        Ret $576

   ) else (
    If (#v!CSRFields@."$tag" == $577) then (
        Ret $577

   ) else (
    If (#v!CSRFields@."$tag" == $578) then (
        Ret $578

   ) else (
    If (#v!CSRFields@."$tag" == $579) then (
        Ret $579

   ) else (
    If (#v!CSRFields@."$tag" == $3584) then (
        Ret $3584

   ) else (
    If (#v!CSRFields@."$tag" == $3585) then (
        Ret $3585

   ) else (
    If (#v!CSRFields@."$tag" == $3586) then (
        Ret $3586

   ) else (
    If (#v!CSRFields@."$tag" == $3712) then (
        Ret $3712

   ) else (
    If (#v!CSRFields@."$tag" == $3713) then (
        Ret $3713

   ) else (
    If (#v!CSRFields@."$tag" == $3714) then (
        Ret $3714

   ) else (
    If (#v!CSRFields@."$tag" == $3856) then (
        Ret $3856

   ) else (
    If (#v!CSRFields@."$tag" == $3857) then (
        Ret $3857

   ) else (
    If (#v!CSRFields@."$tag" == $3858) then (
        Ret $3858

   ) else (
    If (#v!CSRFields@."$tag" == $3859) then (
        Ret $3859

   ) else (
    If (#v!CSRFields@."$tag" == $3860) then (
        Ret $3860

   ) else (
    If (#v!CSRFields@."$tag" == $768) then (
        Ret $768

   ) else (
    If (#v!CSRFields@."$tag" == $770) then (
        Ret $770

   ) else (
    If (#v!CSRFields@."$tag" == $771) then (
        Ret $771

   ) else (
    If (#v!CSRFields@."$tag" == $772) then (
        Ret $772

   ) else (
    If (#v!CSRFields@."$tag" == $773) then (
        Ret $773

   ) else (
    If (#v!CSRFields@."$tag" == $832) then (
        Ret $832

   ) else (
    If (#v!CSRFields@."$tag" == $833) then (
        Ret $833

   ) else (
    If (#v!CSRFields@."$tag" == $834) then (
        Ret $834

   ) else (
    If (#v!CSRFields@."$tag" == $835) then (
        Ret $835

   ) else (
    If (#v!CSRFields@."$tag" == $836) then (
        Ret $836

   ) else (
    If (#v!CSRFields@."$tag" == $896) then (
        Ret $896

   ) else (
    If (#v!CSRFields@."$tag" == $897) then (
        Ret $897

   ) else (
    If (#v!CSRFields@."$tag" == $898) then (
        Ret $898

   ) else (
    If (#v!CSRFields@."$tag" == $899) then (
        Ret $899

   ) else (
    If (#v!CSRFields@."$tag" == $900) then (
        Ret $900

   ) else (
    If (#v!CSRFields@."$tag" == $901) then (
        Ret $901

   ) else (
    If (#v!CSRFields@."$tag" == $3840) then (
        Ret $3840

   ) else (
    If (#v!CSRFields@."$tag" == $3841) then (
        Ret $3841

   ) else (
    If (#v!CSRFields@."$tag" == $3842) then (
        Ret $3842

   ) else (
    If (#v!CSRFields@."$tag" == $3968) then (
        Ret $3968

   ) else (
    If (#v!CSRFields@."$tag" == $3969) then (
        Ret $3969

   ) else (
    If (#v!CSRFields@."$tag" == $3970) then (
        Ret $3970

   ) else (
    If (#v!CSRFields@."$tag" == $784) then (
        Ret $784

   ) else (
    If (#v!CSRFields@."$tag" == $785) then (
        Ret $785

   ) else (
    If (#v!CSRFields@."$tag" == $786) then (
        Ret $786

   ) else (
    If (#v!CSRFields@."$tag" == $1792) then (
        Ret $1792

   ) else (
    If (#v!CSRFields@."$tag" == $1793) then (
        Ret $1793

   ) else (
    If (#v!CSRFields@."$tag" == $1794) then (
        Ret $1794

   ) else (
    If (#v!CSRFields@."$tag" == $1796) then (
        Ret $1796

   ) else (
    If (#v!CSRFields@."$tag" == $1797) then (
        Ret $1797

   ) else (
    If (#v!CSRFields@."$tag" == $1798) then (
        Ret $1798

   ) else (
    If (#v!CSRFields@."$tag" == $1800) then (
        Ret $1800

   ) else (
    If (#v!CSRFields@."$tag" == $1801) then (
        Ret $1801

   ) else (
    If (#v!CSRFields@."$tag" == $1802) then (
        Ret $1802

   ) else (
    If (#v!CSRFields@."$tag" == $1920) then (
        Ret $1920

   ) else (
    If (#v!CSRFields@."$tag" == $1921) then (
        Ret $1921

   ) else (
    If (#v!CSRFields@."$tag" == $1922) then (
        Ret $1922

   ) else (
    If (#v!CSRFields@."$tag" == $1924) then (
        Ret $1924

   ) else (
    If (#v!CSRFields@."$tag" == $1925) then (
        Ret $1925

   ) else (
    If (#v!CSRFields@."$tag" == $1926) then (
        Ret $1926

   ) else (
    If (#v!CSRFields@."$tag" == $1928) then (
        Ret $1928

   ) else (
    If (#v!CSRFields@."$tag" == $1929) then (
        Ret $1929

   ) else (
    If (#v!CSRFields@."$tag" == $1930) then (
        Ret $1930

   ) else (
        Ret $0
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


    }). (* mkPackCSR *)

(* Module mkPackCSR type Module#(Pack#(CSR, 12)) return type Pack#(CSR, 12) *)
    Definition mkPackCSR := Build_Pack (CSR) (12) mkPackCSRModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackCSR.
End module'mkPackCSR.

Definition mkPackCSR := module'mkPackCSR.mkPackCSR.

Definition InstructionFieldsFields := (STRUCT {
    "inst" :: (Bit 32);
    "rd" :: (Bit 5);
    "rs1" :: (Bit 5);
    "rs2" :: (Bit 5);
    "rs3" :: (Bit 5);
    "funct2" :: (Bit 2);
    "funct3" :: (Bit 3);
    "funct5" :: (Bit 5);
    "funct7" :: (Bit 7);
    "fmt" :: (Bit 2);
    "rm" :: RVRoundMode;
    "csrAddr" :: (Bit 12)}).
Definition InstructionFields  := Struct (InstructionFieldsFields).

Definition TestStructFields := (STRUCT {
    "inst" :: (Bit 32);
    "rd" :: (Bit 5);
    "csr" :: CSR}).
Definition TestStruct  := Struct (TestStructFields).

(* * interface GetTestStruct *)
Record GetTestStruct := {
    GetTestStruct'modules: Modules;
    GetTestStruct'getTestStruct : string;
}.

Module module'mkTestStruct.
    Section Section'mkTestStruct.
    Variable instancePrefix: string.
               Let packCSR := mkPackCSR (instancePrefix--"packCSR").
    Let packCSRunpack : string := (Pack'unpack packCSR).
    Definition mkTestStructModule: Modules :=
         (BKMODULE {
           (BKMod (Pack'modules packCSR :: nil))
       with Method instancePrefix--"getTestStruct" (x : (Bit 32)) : TestStruct :=
CallM xcsr : CSR <-  packCSRunpack(#x$[31:20]@32);
        LET ts : TestStruct <- STRUCT { "inst" ::= (#x); "rd" ::= (#x$[4:0]@32); "csr" ::= (#xcsr)  };
        Ret #ts

    }). (* mkTestStruct *)

(* Module mkTestStruct type Module#(GetTestStruct) return type GetTestStruct *)
    Definition mkTestStruct := Build_GetTestStruct mkTestStructModule%kami (instancePrefix--"getTestStruct").
    End Section'mkTestStruct.
End module'mkTestStruct.

Definition mkTestStruct := module'mkTestStruct.mkTestStruct.

(* * interface GetInstFields *)
Record GetInstFields := {
    GetInstFields'modules: Modules;
    GetInstFields'getInstFields : string;
}.

Module module'mkGetInstFields.
    Section Section'mkGetInstFields.
    Variable instancePrefix: string.
                       Let packRVRoundMode := mkPackRVRoundMode (instancePrefix--"packRVRoundMode").
       Let packOpcode := mkPackOpcode (instancePrefix--"packOpcode").
       Let packCSR := mkPackCSR (instancePrefix--"packCSR").
    Let packCSRunpack : string := (Pack'unpack packCSR).
    Let packOpcodeunpack : string := (Pack'unpack packOpcode).
    Let packRVRoundModeunpack : string := (Pack'unpack packRVRoundMode).
    Definition mkGetInstFieldsModule: Modules :=
         (BKMODULE {
           (BKMod (Pack'modules packRVRoundMode :: nil))
       with (BKMod (Pack'modules packOpcode :: nil))
       with (BKMod (Pack'modules packCSR :: nil))
       with Method instancePrefix--"getInstFields" (x : Instruction) : InstructionFields :=
CallM xroundMode : RVRoundMode <-  packRVRoundModeunpack(#x$[14:12]@32);
CallM xopcode : Opcode <-  packOpcodeunpack(#x$[6:0]@32);
CallM xcsr : CSR <-  packCSRunpack(#x$[31:20]@32);
        Ret STRUCT { "inst" ::= (#x); "rd" ::= (#x$[11:7]@32); "rs1" ::= (#x$[19:15]@32); "rs2" ::= (#x$[24:20]@32); "rs3" ::= (#x$[31:27]@32); "funct2" ::= (#x$[26:25]@32); "funct3" ::= (#x$[14:12]@32); "funct5" ::= (#x$[31:27]@32); "funct7" ::= (#x$[31:25]@32); "fmt" ::= (#x$[26:25]@32); "rm" ::= (#xroundMode); "csrAddr" ::= (#x$[31:20]@32)  }

    }). (* mkGetInstFields *)

(* Module mkGetInstFields type Module#(GetInstFields) return type GetInstFields *)
    Definition mkGetInstFields := Build_GetInstFields mkGetInstFieldsModule%kami (instancePrefix--"getInstFields").
    End Section'mkGetInstFields.
End module'mkGetInstFields.

Definition mkGetInstFields := module'mkGetInstFields.mkGetInstFields.

Definition RVMemOpFields := (STRUCT { "$tag" :: (Bit 3) }).
Definition RVMemOp := (Struct RVMemOpFields).
Notation Ld := (STRUCT { "$tag" ::= $$(natToWord 3 0) })%kami_expr.
Notation St := (STRUCT { "$tag" ::= $$(natToWord 3 1) })%kami_expr.
Notation PrefetchForLd := (STRUCT { "$tag" ::= $$(natToWord 3 2) })%kami_expr.
Notation PrefetchForSt := (STRUCT { "$tag" ::= $$(natToWord 3 3) })%kami_expr.
Notation Lr := (STRUCT { "$tag" ::= $$(natToWord 3 4) })%kami_expr.
Notation Sc := (STRUCT { "$tag" ::= $$(natToWord 3 5) })%kami_expr.
Definition RVAmoOpFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition RVAmoOp := (Struct RVAmoOpFields).
Notation Swap := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation Add := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation Xor := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation And := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation Or := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation Min := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation Max := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation Minu := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation Maxu := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Definition RVMemSizeFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition RVMemSize := (Struct RVMemSizeFields).
Notation B := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation H := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation W := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
Notation D := (STRUCT { "$tag" ::= $$(natToWord 2 3) })%kami_expr.
(* * interface ToDataByteEn#(n) *)
Record ToDataByteEn (n : nat) := {
    ToDataByteEn'modules: Modules;
    ToDataByteEn'toDataByteEn : string;
}.

Module module'mkToDataByteEn4.
    Section Section'mkToDataByteEn4.
    Variable instancePrefix: string.
        Definition mkToDataByteEn4Module: Modules :=
         (BKMODULE {
           Method instancePrefix--"toDataByteEn" (size : RVMemSize) : (Bit 4) :=
        Ret null

    }). (* mkToDataByteEn4 *)

(* Module mkToDataByteEn4 type Module#(ToDataByteEn#(4)) return type ToDataByteEn#(4) *)
    Definition mkToDataByteEn4 := Build_ToDataByteEn (4) mkToDataByteEn4Module%kami (instancePrefix--"toDataByteEn").
    End Section'mkToDataByteEn4.
End module'mkToDataByteEn4.

Definition mkToDataByteEn4 := module'mkToDataByteEn4.mkToDataByteEn4.

Module module'mkToDataByteEn8.
    Section Section'mkToDataByteEn8.
    Variable instancePrefix: string.
        Definition mkToDataByteEn8Module: Modules :=
         (BKMODULE {
           Method instancePrefix--"toDataByteEn" (size : RVMemSize) : (Bit 8) :=
        Ret null

    }). (* mkToDataByteEn8 *)

(* Module mkToDataByteEn8 type Module#(ToDataByteEn#(8)) return type ToDataByteEn#(8) *)
    Definition mkToDataByteEn8 := Build_ToDataByteEn (8) mkToDataByteEn8Module%kami (instancePrefix--"toDataByteEn").
    End Section'mkToDataByteEn8.
End module'mkToDataByteEn8.

Definition mkToDataByteEn8 := module'mkToDataByteEn8.mkToDataByteEn8.

(* * interface ToPermutedDataByteEn *)
Record ToPermutedDataByteEn := {
    ToPermutedDataByteEn'modules: Modules;
    ToPermutedDataByteEn'toPermutedDataByteEn : string;
}.

Module module'mkToPermutedDataByteEn.
    Section Section'mkToPermutedDataByteEn.
    Variable instancePrefix: string.
               Let tdbe := mkToDataByteEn4 (instancePrefix--"tdbe").
    Definition mkToPermutedDataByteEnModule: Modules :=
         (BKMODULE {
           (BKMod (ToDataByteEn'modules tdbe :: nil))
       with Method2 instancePrefix--"toPermutedDataByteEn" (size : RVMemSize) (addrLSB : DataByteSel) : DataByteEn :=
        Ret ( tdbetoDataByteEn(#size) << #addrLSB)

    }). (* mkToPermutedDataByteEn *)

(* Module mkToPermutedDataByteEn type Module#(ToPermutedDataByteEn) return type ToPermutedDataByteEn *)
    Definition mkToPermutedDataByteEn := Build_ToPermutedDataByteEn mkToPermutedDataByteEnModule%kami (instancePrefix--"toPermutedDataByteEn").
    End Section'mkToPermutedDataByteEn.
End module'mkToPermutedDataByteEn.

Definition mkToPermutedDataByteEn := module'mkToPermutedDataByteEn.mkToPermutedDataByteEn.

Definition RVMemAmoOpFields := (STRUCT {
    "$tag" :: (Bit 8);
    "MemOp" :: RVMemOp;
    "AmoOp" :: RVAmoOp}).
Definition RVMemAmoOp := Struct (RVMemAmoOpFields).
Definition RVMemInstFields := (STRUCT {
    "op" :: RVMemAmoOp;
    "size" :: RVMemSize;
    "isUnsigned" :: Bool}).
Definition RVMemInst  := Struct (RVMemInstFields).

(* * interface IsMemOp#(t) *)
Record IsMemOp (t : Kind) := {
    IsMemOp'modules: Modules;
    IsMemOp'isLoad : string;
    IsMemOp'isStore : string;
    IsMemOp'isAmo : string;
    IsMemOp'getsReadPermission : string;
    IsMemOp'getsWritePermission : string;
    IsMemOp'getsResponse : string;
}.

Module module'mkIsMemOpRVMemOp.
    Section Section'mkIsMemOpRVMemOp.
    Variable instancePrefix: string.
                            Definition mkIsMemOpRVMemOpModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"isLoad" (x : RVMemOp) : Bool :=
        Ret ((#x == Ld) || (#x == Lr))

       with Method instancePrefix--"isStore" (x : RVMemOp) : Bool :=
        Ret ((#x == St) || (#x == Sc))

       with Method instancePrefix--"isAmo" (x : RVMemOp) : Bool :=
        Ret False

       with Method instancePrefix--"getsReadPermission" (x : RVMemOp) : Bool :=
        Ret ((#x == Ld) || (#x == PrefetchForLd))

       with Method instancePrefix--"getsWritePermission" (x : RVMemOp) : Bool :=
        Ret ((((#x == St) || (#x == Sc)) || (#x == Lr)) || (#x == PrefetchForSt))

       with Method instancePrefix--"getsResponse" (x : RVMemOp) : Bool :=
        Ret (((#x == Ld) || (#x == Lr)) || (#x == Sc))

    }). (* mkIsMemOpRVMemOp *)

(* Module mkIsMemOpRVMemOp type Module#(IsMemOp#(RVMemOp)) return type IsMemOp#(RVMemOp) *)
    Definition mkIsMemOpRVMemOp := Build_IsMemOp (RVMemOp) mkIsMemOpRVMemOpModule%kami (instancePrefix--"getsReadPermission") (instancePrefix--"getsResponse") (instancePrefix--"getsWritePermission") (instancePrefix--"isAmo") (instancePrefix--"isLoad") (instancePrefix--"isStore").
    End Section'mkIsMemOpRVMemOp.
End module'mkIsMemOpRVMemOp.

Definition mkIsMemOpRVMemOp := module'mkIsMemOpRVMemOp.mkIsMemOpRVMemOp.

Module module'mkIsMemOpRVAmoOp.
    Section Section'mkIsMemOpRVAmoOp.
    Variable instancePrefix: string.
                            Definition mkIsMemOpRVAmoOpModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"isLoad" (x : RVAmoOp) : Bool :=
        Ret False

       with Method instancePrefix--"isStore" (x : RVAmoOp) : Bool :=
        Ret False

       with Method instancePrefix--"isAmo" (x : RVAmoOp) : Bool :=
        Ret True

       with Method instancePrefix--"getsReadPermission" (x : RVAmoOp) : Bool :=
        Ret False

       with Method instancePrefix--"getsWritePermission" (x : RVAmoOp) : Bool :=
        Ret True

       with Method instancePrefix--"getsResponse" (x : RVAmoOp) : Bool :=
        Ret True

    }). (* mkIsMemOpRVAmoOp *)

(* Module mkIsMemOpRVAmoOp type Module#(IsMemOp#(RVAmoOp)) return type IsMemOp#(RVAmoOp) *)
    Definition mkIsMemOpRVAmoOp := Build_IsMemOp (RVAmoOp) mkIsMemOpRVAmoOpModule%kami (instancePrefix--"getsReadPermission") (instancePrefix--"getsResponse") (instancePrefix--"getsWritePermission") (instancePrefix--"isAmo") (instancePrefix--"isLoad") (instancePrefix--"isStore").
    End Section'mkIsMemOpRVAmoOp.
End module'mkIsMemOpRVAmoOp.

Definition mkIsMemOpRVAmoOp := module'mkIsMemOpRVAmoOp.mkIsMemOpRVAmoOp.

Module module'mkIsMemOpRVMemAmoOp.
    Section Section'mkIsMemOpRVMemAmoOp.
    Variable instancePrefix: string.
                                       Let isMemOpMem := mkIsMemOpRVMemOp (instancePrefix--"isMemOpMem").
       Let isMemOpAmo := mkIsMemOpRVAmoOp (instancePrefix--"isMemOpAmo").
    Let isMemOpAmogetsReadPermission : string := (IsMemOp'getsReadPermission isMemOpAmo).
    Let isMemOpAmogetsResponse : string := (IsMemOp'getsResponse isMemOpAmo).
    Let isMemOpAmogetsWritePermission : string := (IsMemOp'getsWritePermission isMemOpAmo).
    Let isMemOpAmoisAmo : string := (IsMemOp'isAmo isMemOpAmo).
    Let isMemOpAmoisLoad : string := (IsMemOp'isLoad isMemOpAmo).
    Let isMemOpAmoisStore : string := (IsMemOp'isStore isMemOpAmo).
    Let isMemOpMemgetsReadPermission : string := (IsMemOp'getsReadPermission isMemOpMem).
    Let isMemOpMemgetsResponse : string := (IsMemOp'getsResponse isMemOpMem).
    Let isMemOpMemgetsWritePermission : string := (IsMemOp'getsWritePermission isMemOpMem).
    Let isMemOpMemisAmo : string := (IsMemOp'isAmo isMemOpMem).
    Let isMemOpMemisLoad : string := (IsMemOp'isLoad isMemOpMem).
    Let isMemOpMemisStore : string := (IsMemOp'isStore isMemOpMem).
    Definition mkIsMemOpRVMemAmoOpModule: Modules :=
         (BKMODULE {
           (BKMod (IsMemOp'modules isMemOpMem :: nil))
       with (BKMod (IsMemOp'modules isMemOpAmo :: nil))
       with Method instancePrefix--"isLoad" (x : RVMemAmoOp) : Bool :=
        Ret null

       with Method instancePrefix--"isStore" (x : RVMemAmoOp) : Bool :=
        Ret null

       with Method instancePrefix--"isAmo" (x : RVMemAmoOp) : Bool :=
        Ret null

       with Method instancePrefix--"getsReadPermission" (x : RVMemAmoOp) : Bool :=
        Ret null

       with Method instancePrefix--"getsWritePermission" (x : RVMemAmoOp) : Bool :=
        Ret null

       with Method instancePrefix--"getsResponse" (x : RVMemAmoOp) : Bool :=
        Ret null

    }). (* mkIsMemOpRVMemAmoOp *)

(* Module mkIsMemOpRVMemAmoOp type Module#(IsMemOp#(RVMemAmoOp)) return type IsMemOp#(RVMemAmoOp) *)
    Definition mkIsMemOpRVMemAmoOp := Build_IsMemOp (RVMemAmoOp) mkIsMemOpRVMemAmoOpModule%kami (instancePrefix--"getsReadPermission") (instancePrefix--"getsResponse") (instancePrefix--"getsWritePermission") (instancePrefix--"isAmo") (instancePrefix--"isLoad") (instancePrefix--"isStore").
    End Section'mkIsMemOpRVMemAmoOp.
End module'mkIsMemOpRVMemAmoOp.

Definition mkIsMemOpRVMemAmoOp := module'mkIsMemOpRVMemAmoOp.mkIsMemOpRVMemAmoOp.

Definition RiscVISASubsetFields := (STRUCT {
    "rv64" :: Bool;
    "h" :: Bool;
    "s" :: Bool;
    "u" :: Bool;
    "m" :: Bool;
    "a" :: Bool;
    "f" :: Bool;
    "d" :: Bool;
    "x" :: Bool}).
Definition RiscVISASubset  := Struct (RiscVISASubsetFields).

(* * interface GetMISA *)
Record GetMISA := {
    GetMISA'modules: Modules;
    GetMISA'getMISA : string;
}.

Module module'mkGetMISA.
    Section Section'mkGetMISA.
    Variable instancePrefix: string.
        Definition mkGetMISAModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"getMISA" (isa : RiscVISASubset) : Data :=
        LET misa : Data <- castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0);
        If #isa
        then                 BKSTMTS {
                Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $2 $0));
;
        Retv
        else                 BKSTMTS {
                Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $1 $0));
;
        Retv;;
        If #isa
        then                 Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | castBits _ _ _ _ (BinBit (Concat 2 4) $0 $0));
        Retv;
        Ret #misa

    }). (* mkGetMISA *)

(* Module mkGetMISA type Module#(GetMISA) return type GetMISA *)
    Definition mkGetMISA := Build_GetMISA mkGetMISAModule%kami (instancePrefix--"getMISA").
    End Section'mkGetMISA.
End module'mkGetMISA.

Definition mkGetMISA := module'mkGetMISA.mkGetMISA.

Definition RegIndex := (Bit 5).

Definition FullRegIndexFields := (STRUCT {
    "$tag" :: (Bit 8);
    "Gpr" :: RegIndex;
    "Fpu" :: RegIndex}).
Definition FullRegIndex := Struct (FullRegIndexFields).
(* * interface ToFullRegIndex *)
Record ToFullRegIndex := {
    ToFullRegIndex'modules: Modules;
    ToFullRegIndex'toFullRegIndex : string;
}.

Module module'mkToFullRegIndex.
    Section Section'mkToFullRegIndex.
    Variable instancePrefix: string.
        Definition mkToFullRegIndexModule: Modules :=
         (BKMODULE {
           Method2 instancePrefix--"toFullRegIndex" (rType : (Maybe RegType)) (index : RegIndex) : (Maybe FullRegIndex) :=
        Ret null

    }). (* mkToFullRegIndex *)

(* Module mkToFullRegIndex type Module#(ToFullRegIndex) return type ToFullRegIndex *)
    Definition mkToFullRegIndex := Build_ToFullRegIndex mkToFullRegIndexModule%kami (instancePrefix--"toFullRegIndex").
    End Section'mkToFullRegIndex.
End module'mkToFullRegIndex.

Definition mkToFullRegIndex := module'mkToFullRegIndex.mkToFullRegIndex.

Definition NumArchReg := 64.

Definition NumPhyReg := NumArchReg.

(* * interface HasCSRPermission *)
Record HasCSRPermission := {
    HasCSRPermission'modules: Modules;
    HasCSRPermission'hasCSRPermission : string;
}.

Module module'mkHasCSRPermission.
    Section Section'mkHasCSRPermission.
    Variable instancePrefix: string.
               Let packCSR := mkPackCSR (instancePrefix--"packCSR").
    Let packCSRpack : string := (Pack'pack packCSR).
    Definition mkHasCSRPermissionModule: Modules :=
         (BKMODULE {
           (BKMod (Pack'modules packCSR :: nil))
       with Method3 instancePrefix--"hasCSRPermission" (csr : CSR) (prv : (Bit 2)) (write : Bool) : Bool :=
CallM csr_index : (Bit 12) <-  packCSRpack(#csr);
        Ret ((#prv >= #csr_index$[9:8]@12) && (!#write || (#csr_index$[11:10]@12 != $3)))

    }). (* mkHasCSRPermission *)

(* Module mkHasCSRPermission type Module#(HasCSRPermission) return type HasCSRPermission *)
    Definition mkHasCSRPermission := Build_HasCSRPermission mkHasCSRPermissionModule%kami (instancePrefix--"hasCSRPermission").
    End Section'mkHasCSRPermission.
End module'mkHasCSRPermission.

Definition mkHasCSRPermission := module'mkHasCSRPermission.mkHasCSRPermission.

Definition BrFuncFields := (STRUCT { "$tag" :: (Bit 3) }).
Definition BrFunc := (Struct BrFuncFields).
Notation BrEq := (STRUCT { "$tag" ::= $$(natToWord 3 0) })%kami_expr.
Notation BrNeq := (STRUCT { "$tag" ::= $$(natToWord 3 1) })%kami_expr.
Notation BrJal := (STRUCT { "$tag" ::= $$(natToWord 3 2) })%kami_expr.
Notation BrJalr := (STRUCT { "$tag" ::= $$(natToWord 3 3) })%kami_expr.
Notation BrLt := (STRUCT { "$tag" ::= $$(natToWord 3 4) })%kami_expr.
Notation BrGe := (STRUCT { "$tag" ::= $$(natToWord 3 5) })%kami_expr.
Notation BrLtu := (STRUCT { "$tag" ::= $$(natToWord 3 6) })%kami_expr.
Notation BrGeu := (STRUCT { "$tag" ::= $$(natToWord 3 7) })%kami_expr.
Definition AluFuncFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition AluFunc := (Struct AluFuncFields).
Notation AluAdd := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation AluSll := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation AluSlt := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation AluSltu := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation AluXor := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation AluSrl := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation AluOr := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation AluAnd := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation AluSub := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Notation AluSra := (STRUCT { "$tag" ::= $$(natToWord 4 9) })%kami_expr.
Notation AluAuipc := (STRUCT { "$tag" ::= $$(natToWord 4 10) })%kami_expr.
Notation AluLui := (STRUCT { "$tag" ::= $$(natToWord 4 11) })%kami_expr.
Definition AluInstFields := (STRUCT {
    "op" :: AluFunc;
    "w" :: Bool}).
Definition AluInst  := Struct (AluInstFields).

Definition MulDivFuncFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition MulDivFunc := (Struct MulDivFuncFields).
Notation Mul := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation Mulh := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation Div := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
Notation Rem := (STRUCT { "$tag" ::= $$(natToWord 2 3) })%kami_expr.
Definition MulDivSignFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition MulDivSign := (Struct MulDivSignFields).
Notation Signed := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation Unsigned := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation SignedUnsigned := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
Definition MulDivInstFields := (STRUCT {
    "func" :: MulDivFunc;
    "w" :: Bool;
    "sign" :: MulDivSign}).
Definition MulDivInst  := Struct (MulDivInstFields).

Definition FpuFuncFields := (STRUCT { "$tag" :: (Bit 5) }).
Definition FpuFunc := (Struct FpuFuncFields).
Notation FAdd := (STRUCT { "$tag" ::= $$(natToWord 5 0) })%kami_expr.
Notation FSub := (STRUCT { "$tag" ::= $$(natToWord 5 1) })%kami_expr.
Notation FMul := (STRUCT { "$tag" ::= $$(natToWord 5 2) })%kami_expr.
Notation FDiv := (STRUCT { "$tag" ::= $$(natToWord 5 3) })%kami_expr.
Notation FSqrt := (STRUCT { "$tag" ::= $$(natToWord 5 4) })%kami_expr.
Notation FSgnj := (STRUCT { "$tag" ::= $$(natToWord 5 5) })%kami_expr.
Notation FSgnjn := (STRUCT { "$tag" ::= $$(natToWord 5 6) })%kami_expr.
Notation FSgnjx := (STRUCT { "$tag" ::= $$(natToWord 5 7) })%kami_expr.
Notation FMin := (STRUCT { "$tag" ::= $$(natToWord 5 8) })%kami_expr.
Notation FMax := (STRUCT { "$tag" ::= $$(natToWord 5 9) })%kami_expr.
Notation FCvt_FF := (STRUCT { "$tag" ::= $$(natToWord 5 10) })%kami_expr.
Notation FCvt_WF := (STRUCT { "$tag" ::= $$(natToWord 5 11) })%kami_expr.
Notation FCvt_WUF := (STRUCT { "$tag" ::= $$(natToWord 5 12) })%kami_expr.
Notation FCvt_LF := (STRUCT { "$tag" ::= $$(natToWord 5 13) })%kami_expr.
Notation FCvt_LUF := (STRUCT { "$tag" ::= $$(natToWord 5 14) })%kami_expr.
Notation FCvt_FW := (STRUCT { "$tag" ::= $$(natToWord 5 15) })%kami_expr.
Notation FCvt_FWU := (STRUCT { "$tag" ::= $$(natToWord 5 16) })%kami_expr.
Notation FCvt_FL := (STRUCT { "$tag" ::= $$(natToWord 5 17) })%kami_expr.
Notation FCvt_FLU := (STRUCT { "$tag" ::= $$(natToWord 5 18) })%kami_expr.
Notation FEq := (STRUCT { "$tag" ::= $$(natToWord 5 19) })%kami_expr.
Notation FLt := (STRUCT { "$tag" ::= $$(natToWord 5 20) })%kami_expr.
Notation FLe := (STRUCT { "$tag" ::= $$(natToWord 5 21) })%kami_expr.
Notation FClass := (STRUCT { "$tag" ::= $$(natToWord 5 22) })%kami_expr.
Notation FMv_XF := (STRUCT { "$tag" ::= $$(natToWord 5 23) })%kami_expr.
Notation FMv_FX := (STRUCT { "$tag" ::= $$(natToWord 5 24) })%kami_expr.
Notation FMAdd := (STRUCT { "$tag" ::= $$(natToWord 5 25) })%kami_expr.
Notation FMSub := (STRUCT { "$tag" ::= $$(natToWord 5 26) })%kami_expr.
Notation FNMSub := (STRUCT { "$tag" ::= $$(natToWord 5 27) })%kami_expr.
Notation FNMAdd := (STRUCT { "$tag" ::= $$(natToWord 5 28) })%kami_expr.
Definition FpuPrecisionFields := (STRUCT { "$tag" :: (Bit 1) }).
Definition FpuPrecision := (Struct FpuPrecisionFields).
Notation Single := (STRUCT { "$tag" ::= $$(natToWord 1 0) })%kami_expr.
Notation Double := (STRUCT { "$tag" ::= $$(natToWord 1 1) })%kami_expr.
Definition FpuInstFields := (STRUCT {
    "func" :: FpuFunc;
    "precision" :: FpuPrecision}).
Definition FpuInst  := Struct (FpuInstFields).

Definition IntraCoreFenceFields := (STRUCT { "$tag" :: (Bit 1) }).
Definition IntraCoreFence := (Struct IntraCoreFenceFields).
Notation FenceI := (STRUCT { "$tag" ::= $$(natToWord 1 0) })%kami_expr.
Notation SFenceVM := (STRUCT { "$tag" ::= $$(natToWord 1 1) })%kami_expr.
Definition InterCoreFenceFields := (STRUCT {
    "sw" :: Bool;
    "sr" :: Bool;
    "so" :: Bool;
    "si" :: Bool;
    "pw" :: Bool;
    "pr" :: Bool;
    "po" :: Bool;
    "pi" :: Bool}).
Definition InterCoreFence  := Struct (InterCoreFenceFields).

Definition FenceFields := (STRUCT {
    "$tag" :: (Bit 8);
    "IntraCore" :: IntraCoreFence;
    "InterCore" :: InterCoreFence}).
Definition Fence := Struct (FenceFields).
Definition SystemInstFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition SystemInst := (Struct SystemInstFields).
Notation ECall := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation EBreak := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation URet := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation SRet := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation HRet := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation MRet := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation WFI := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation CSRRW := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation CSRRS := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Notation CSRRC := (STRUCT { "$tag" ::= $$(natToWord 4 9) })%kami_expr.
Notation CSRR := (STRUCT { "$tag" ::= $$(natToWord 4 10) })%kami_expr.
Notation CSRW := (STRUCT { "$tag" ::= $$(natToWord 4 11) })%kami_expr.
Definition ExecFuncFields := (STRUCT {
    "$tag" :: (Bit 8);
    "EF_Alu" :: AluInst;
    "EF_Br" :: BrFunc;
    "EF_Mem" :: RVMemInst;
    "EF_MulDiv" :: MulDivInst;
    "EF_Fpu" :: FpuInst;
    "EF_Fence" :: Fence;
    "EF_System" :: SystemInst}).
Definition ExecFunc := Struct (ExecFuncFields).
Definition RegTypeFields := (STRUCT { "$tag" :: (Bit 1) }).
Definition RegType := (Struct RegTypeFields).
Notation RtGpr := (STRUCT { "$tag" ::= $$(natToWord 1 0) })%kami_expr.
Notation RtFpu := (STRUCT { "$tag" ::= $$(natToWord 1 1) })%kami_expr.
Definition ImmTypeFields := (STRUCT { "$tag" :: (Bit 3) }).
Definition ImmType := (Struct ImmTypeFields).
Notation ItNone := (STRUCT { "$tag" ::= $$(natToWord 3 0) })%kami_expr.
Notation ItI := (STRUCT { "$tag" ::= $$(natToWord 3 1) })%kami_expr.
Notation ItS := (STRUCT { "$tag" ::= $$(natToWord 3 2) })%kami_expr.
Notation ItSB := (STRUCT { "$tag" ::= $$(natToWord 3 3) })%kami_expr.
Notation ItU := (STRUCT { "$tag" ::= $$(natToWord 3 4) })%kami_expr.
Notation ItUJ := (STRUCT { "$tag" ::= $$(natToWord 3 5) })%kami_expr.
Notation ItZ := (STRUCT { "$tag" ::= $$(natToWord 3 6) })%kami_expr.
Definition RVDecodedInstFields := (STRUCT {
    "execFunc" :: ExecFunc;
    "imm" :: ImmType;
    "rs1" :: (Maybe RegType);
    "rs2" :: (Maybe RegType);
    "rs3" :: (Maybe RegType);
    "dst" :: (Maybe RegType);
    "inst" :: Instruction}).
Definition RVDecodedInst  := Struct (RVDecodedInstFields).

Definition ExceptionCauseFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition ExceptionCause := (Struct ExceptionCauseFields).
Notation InstAddrMisaligned := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation InstAccessFault := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation IllegalInst := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation Breakpoint := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation LoadAddrMisaligned := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation LoadAccessFault := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation StoreAddrMisaligned := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation StoreAccessFault := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation EnvCallU := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Notation EnvCallS := (STRUCT { "$tag" ::= $$(natToWord 4 9) })%kami_expr.
Notation EnvCallH := (STRUCT { "$tag" ::= $$(natToWord 4 10) })%kami_expr.
Notation EnvCallM := (STRUCT { "$tag" ::= $$(natToWord 4 11) })%kami_expr.
Notation IllegalException := (STRUCT { "$tag" ::= $$(natToWord 4 12) })%kami_expr.
Definition InterruptCauseFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition InterruptCause := (Struct InterruptCauseFields).
Notation USoftwareInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation SSoftwareInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation HSoftwareInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation MSoftwareInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation UTimerInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation STimerInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation HTimerInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation MTimerInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation UExternalInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Notation SExternalInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 9) })%kami_expr.
Notation HExternalInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 10) })%kami_expr.
Notation MExternalInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 11) })%kami_expr.
Notation IllegalInterrupt := (STRUCT { "$tag" ::= $$(natToWord 4 12) })%kami_expr.
Definition TrapCauseFields := (STRUCT {
    "$tag" :: (Bit 8);
    "TcException" :: ExceptionCause;
    "TcInterrupt" :: InterruptCause}).
Definition TrapCause := Struct (TrapCauseFields).
(* * interface ToCauseCSR *)
Record ToCauseCSR := {
    ToCauseCSR'modules: Modules;
    ToCauseCSR'toCauseCSR : string;
}.

Module module'mkToCauseCSR.
    Section Section'mkToCauseCSR.
    Variable instancePrefix: string.
        Definition mkToCauseCSRModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"toCauseCSR" (x : TrapCause) : Data :=
    If (#x!TrapCauseFields@."$tag" == $0) then (
              LET cause <- x;
        BKSTMTS {
        CallM pcause : (Bit 4) <-  pack(#cause);
                Ret castBits _ _ _ _ (BinBit (Concat 28 4) $0 #pcause);


   ) else (
    If (#x!TrapCauseFields@."$tag" == $1) then (
              LET cause <- x;
        BKSTMTS {
        CallM pcause : (Bit 4) <-  pack(#cause);
                Ret castBits _ _ _ _ (BinBit (Concat 1 27) $1 $0);


   ) else (
        Ret $0
) as retval; Ret #retval
) as retval; Ret #retval


    }). (* mkToCauseCSR *)

(* Module mkToCauseCSR type Module#(ToCauseCSR) return type ToCauseCSR *)
    Definition mkToCauseCSR := Build_ToCauseCSR mkToCauseCSRModule%kami (instancePrefix--"toCauseCSR").
    End Section'mkToCauseCSR.
End module'mkToCauseCSR.

Definition mkToCauseCSR := module'mkToCauseCSR.mkToCauseCSR.

Definition CsrStateFields := (STRUCT {
    "prv" :: (Bit 2);
    "frm" :: (Bit 3);
    "f_enabled" :: Bool;
    "x_enabled" :: Bool}).
Definition CsrState  := Struct (CsrStateFields).

Definition RedirectFields := (STRUCT {
    "pc" :: Addr;
    "nextPc" :: Addr;
    "taken" :: Bool;
    "mispredict" :: Bool}).
Definition Redirect  := Struct (RedirectFields).

Definition ControlFlowFields := (STRUCT {
    "pc" :: Addr;
    "nextPc" :: Addr;
    "taken" :: Bool;
    "mispredict" :: Bool}).
Definition ControlFlow  := Struct (ControlFlowFields).

Definition FullResultFields (xlen : nat) := (STRUCT {
    "data" :: (Bit xlen);
    "fflags" :: (Bit 5);
    "vaddr" :: (Bit xlen);
    "paddr" :: (Bit xlen);
    "controlFlow" :: ControlFlow;
    "cause" :: (Maybe ExceptionCause)}).
Definition FullResult  (xlen : nat) := Struct (FullResultFields xlen).

(* * interface FullResultSubset#(t, xlen) *)
Record FullResultSubset (t : Kind) (xlen : nat) := {
    FullResultSubset'modules: Modules;
    FullResultSubset'updateFullResult : string;
}.

Definition VMInfoFields (xlen : nat) := (STRUCT {
    "prv" :: (Bit 2);
    "asid" :: Asid;
    "vm" :: (Bit 5);
    "mxr" :: Bool;
    "pum" :: Bool;
    "base" :: (Bit xlen);
    "bound" :: (Bit xlen)}).
Definition VMInfo  (xlen : nat) := Struct (VMInfoFields xlen).

Definition PMAFields := (STRUCT { "$tag" :: (Bit 2) }).
Definition PMA := (Struct PMAFields).
Notation MainMemory := (STRUCT { "$tag" ::= $$(natToWord 2 0) })%kami_expr.
Notation IORom := (STRUCT { "$tag" ::= $$(natToWord 2 1) })%kami_expr.
Notation IODevice := (STRUCT { "$tag" ::= $$(natToWord 2 2) })%kami_expr.
Notation IOEmpty := (STRUCT { "$tag" ::= $$(natToWord 2 3) })%kami_expr.
(* * interface IsCacheable *)
Record IsCacheable := {
    IsCacheable'modules: Modules;
    IsCacheable'isCacheable : string;
}.

Module module'mkIsCacheable.
    Section Section'mkIsCacheable.
    Variable instancePrefix: string.
        Definition mkIsCacheableModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"isCacheable" (pma : PMA) : Bool :=
        Ret null

    }). (* mkIsCacheable *)

(* Module mkIsCacheable type Module#(IsCacheable) return type IsCacheable *)
    Definition mkIsCacheable := Build_IsCacheable mkIsCacheableModule%kami (instancePrefix--"isCacheable").
    End Section'mkIsCacheable.
End module'mkIsCacheable.

Definition mkIsCacheable := module'mkIsCacheable.mkIsCacheable.

Definition TlbReqFields := (STRUCT {
    "op" :: RVMemOp;
    "addr" :: Addr}).
Definition TlbReq  := Struct (TlbReqFields).

Definition TlbResp := (Tuple2 Addr (Maybe ExceptionCause)).

Definition PTE_Sv39Fields := (STRUCT {
    "reserved" :: (Bit 16);
    "ppn2" :: (Bit 20);
    "ppn1" :: (Bit 9);
    "ppn0" :: (Bit 9);
    "reserved_sw" :: (Bit 2);
    "d" :: Bool;
    "a" :: Bool;
    "g" :: Bool;
    "u" :: Bool;
    "x" :: Bool;
    "w" :: Bool;
    "r" :: Bool;
    "valid" :: Bool}).
Definition PTE_Sv39  := Struct (PTE_Sv39Fields).

