Require Import Bool String List Arith.
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

Definition Data := (word 32).

Definition DataByteEn := (word 4).

Definition DataByteSel := (word 2).

Definition CacheLineSz := 512.

Definition InstSz := 32.

Definition Instruction := (word InstSz).

Definition AddrSz := XLEN.

Definition Addr := (word AddrSz).

Definition PAddrSz := 64.

Definition PAddr := (word PAddrSz).

Definition AsidSz := 10.

Definition Asid := (word AsidSz).

Definition RVRoundModeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVRoundMode := (Struct RVRoundModeFields).
Print RVRoundMode.

Notation RNE := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation RTZ := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation RDN := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation RUP := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation RMM := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation RDyn := (STRUCT { "$tag" ::= $7 })%kami_expr.
(* * interface Pack#(t, sz) *)
Record Pack (sz : nat) (t : Kind) := {
    Pack'interface: Modules;
    Pack'unpack : string;
    Pack'pack : string;
}.

Module mkPackRVRoundMode.
    Section Section'mkPackRVRoundMode.
    Variable instancePrefix: string.
            Definition mkPackRVRoundModeModule :=
        (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 3)) : RVRoundMode :=
             If (#v == $0) then
                Ret RNE
             else
               Ret RDyn as retval;
              Ret #retval

       with Method instancePrefix--"pack" (v : RVRoundMode) : (Bit 3) :=
    If (#v!RVRoundModeFields@."$tag" == $0) then
        Ret $0
    else (If (#v!RVRoundModeFields@."$tag" == $1) then
        Ret $1
    else (If (#v!RVRoundModeFields@."$tag" == $2) then
        Ret $2
    else (If (#v!RVRoundModeFields@."$tag" == $3) then
        Ret $3
    else (If (#v!RVRoundModeFields@."$tag" == $4) then
        Ret $4
    else (If (#v!RVRoundModeFields@."$tag" == $7) then
            Ret $7
          else Ret $7 as retval; Ret #retval)
      as retval;
          Ret #retval) as retval;
          Ret #retval) as retval;
          Ret #retval) as retval;
          Ret #retval) as retval;
           Ret #retval
                            

    }). (* mkPackRVRoundMode *)

    Definition mkPackRVRoundMode := Build_Pack 32 RVRoundMode mkPackRVRoundModeModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackRVRoundMode.
End mkPackRVRoundMode.

Definition OpcodeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition Opcode := (Struct OpcodeFields).
Notation Load := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation LoadFp := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation MiscMem := (STRUCT { "$tag" ::= $15 })%kami_expr.
Notation OpImm := (STRUCT { "$tag" ::= $19 })%kami_expr.
Notation Auipc := (STRUCT { "$tag" ::= $23 })%kami_expr.
Notation OpImm32 := (STRUCT { "$tag" ::= $27 })%kami_expr.
Notation Store := (STRUCT { "$tag" ::= $35 })%kami_expr.
Notation StoreFp := (STRUCT { "$tag" ::= $39 })%kami_expr.
Notation Amo := (STRUCT { "$tag" ::= $47 })%kami_expr.
Notation Op := (STRUCT { "$tag" ::= $51 })%kami_expr.
Notation Lui := (STRUCT { "$tag" ::= $55 })%kami_expr.
Notation Op32 := (STRUCT { "$tag" ::= $59 })%kami_expr.
Notation Fmadd := (STRUCT { "$tag" ::= $67 })%kami_expr.
Notation Fmsub := (STRUCT { "$tag" ::= $71 })%kami_expr.
Notation Fnmsub := (STRUCT { "$tag" ::= $75 })%kami_expr.
Notation Fnmadd := (STRUCT { "$tag" ::= $79 })%kami_expr.
Notation OpFp := (STRUCT { "$tag" ::= $83 })%kami_expr.
Notation Branch := (STRUCT { "$tag" ::= $99 })%kami_expr.
Notation Jalr := (STRUCT { "$tag" ::= $103 })%kami_expr.
Notation Jal := (STRUCT { "$tag" ::= $111 })%kami_expr.
Notation System := (STRUCT { "$tag" ::= $115 })%kami_expr.
Module mkPackOpcode.
    Section Section'mkPackOpcode.
    Variable instancePrefix: string.
            Definition mkPackOpcodeModule :=
        (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 7)) : Opcode :=
             If (#v == $3) then
             Ret #Load
           else
             (If (#v == $7) then
                Ret #LoadFp
              else
                (If (#v == $15) then
                   Ret #MiscMem
                 else
                   (If (#v == $19) then
                      Ret #OpImm
                    else
                      (If (#v == $23) then
                         Ret #Auipc
                       else
                         (If (#v == $27) then
                            Ret #OpImm32
                          else
                            (If (#v == $35) then
                               Ret #Store
                             else
                               (If (#v == $39) then
                                  Ret #StoreFp
                                else
                                  (If (#v == $47) then
                                     Ret #Amo
                                   else
                                     (If (#v == $51) then
                                        Ret #Op
                                      else
                                        (If (#v == $55) then
                                           Ret #Lui
                                         else
                                           (If (#v == $59) then
                                              Ret #Op32
                                            else
                                              (If (#v == $67) then
                                                 Ret #Fmadd
                                               else
                                                 (If (#v == $71) then
                                                    Ret #Fmsub
                                                  else
                                                    (If (#v == $75) then
                                                       Ret #Fnmsub
                                                     else
                                                       (If (#v == $79) then
                                                          Ret #Fnmadd
                                                        else
                                                          (If (#v == $83) then
                                                             Ret #OpFp
                                                           else
                                                             (If (#v == $99) then
                                                                Ret #Branch
                                                              else
                                                                (If (#v == $103) then
                                                                   Ret #Jalr
                                                                 else
                                                                   (If (#v == $111) then
                                                                      Ret #Jal
                                                                    else
                                                                      (If (#v == $115) then
                                                                         Ret #System
                                                                       else
                                                                         Retv as retval;
                                                                       Ret #retval) as retval;
                                                                    Ret #retval) as retval;
                                                                 Ret #retval) as retval;
                                                              Ret #retval) as retval;
                                                           Ret #retval) as retval;
                                                        Ret #retval) as retval;
                                                     Ret #retval) as retval;
                                                  Ret #retval) as retval;
                                               Ret #retval) as retval;
                                            Ret #retval) as retval;
                                         Ret #retval) as retval;
                                      Ret #retval) as retval;
                                   Ret #retval) as retval;
                                Ret #retval) as retval;
                             Ret #retval) as retval;
                          Ret #retval) as retval;
                       Ret #retval) as retval;
                    Ret #retval) as retval;
                 Ret #retval) as retval;
              Ret #retval) as retval;
           Ret #retval
        

       with Method instancePrefix--"pack" (v : Opcode) : (Bit 7) :=
    If (#v!OpcodeFields@."$tag" == $3) then
        Ret $7'b0000011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $7) then
        Ret $7'b0000111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $15) then
        Ret $7'b0001111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $19) then
        Ret $7'b0010011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $23) then
        Ret $7'b0010111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $27) then
        Ret $7'b0011011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $35) then
        Ret $7'b0100011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $39) then
        Ret $7'b0100111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $47) then
        Ret $7'b0101111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $51) then
        Ret $7'b0110011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $55) then
        Ret $7'b0110111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $59) then
        Ret $7'b0111011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $67) then
        Ret $7'b1000011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $71) then
        Ret $7'b1000111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $75) then
        Ret $7'b1001011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $79) then
        Ret $7'b1001111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $83) then
        Ret $7'b1010011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $99) then
        Ret $7'b1100011;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $103) then
        Ret $7'b1100111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $111) then
        Ret $7'b1101111;
        Retv
    else
    If (#v!OpcodeFields@."$tag" == $115) then
        Ret $7'b1110011;
        Retv
    else
        Retv

    }). (* mkPackOpcode *)

    Definition mkPackOpcode := Build_Pack mkPackOpcodeModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackOpcode.
End mkPackOpcode.

Definition CSRFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition CSR := (Struct CSRFields).
Notation CSRustatus := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRuie := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation CSRutvec := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation CSRuscratch := (STRUCT { "$tag" ::= $64 })%kami_expr.
Notation CSRuepc := (STRUCT { "$tag" ::= $65 })%kami_expr.
Notation CSRucause := (STRUCT { "$tag" ::= $66 })%kami_expr.
Notation CSRubadaddr := (STRUCT { "$tag" ::= $67 })%kami_expr.
Notation CSRuip := (STRUCT { "$tag" ::= $68 })%kami_expr.
Notation CSRfflags := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation CSRfrm := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation CSRfcsr := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation CSRcycle := (STRUCT { "$tag" ::= $3072 })%kami_expr.
Notation CSRtime := (STRUCT { "$tag" ::= $3073 })%kami_expr.
Notation CSRinstret := (STRUCT { "$tag" ::= $3074 })%kami_expr.
Notation CSRcycleh := (STRUCT { "$tag" ::= $3200 })%kami_expr.
Notation CSRtimeh := (STRUCT { "$tag" ::= $3201 })%kami_expr.
Notation CSRinstreth := (STRUCT { "$tag" ::= $3202 })%kami_expr.
Notation CSRsstatus := (STRUCT { "$tag" ::= $256 })%kami_expr.
Notation CSRsedeleg := (STRUCT { "$tag" ::= $258 })%kami_expr.
Notation CSRsideleg := (STRUCT { "$tag" ::= $259 })%kami_expr.
Notation CSRsie := (STRUCT { "$tag" ::= $260 })%kami_expr.
Notation CSRstvec := (STRUCT { "$tag" ::= $261 })%kami_expr.
Notation CSRsscratch := (STRUCT { "$tag" ::= $320 })%kami_expr.
Notation CSRsepc := (STRUCT { "$tag" ::= $321 })%kami_expr.
Notation CSRscause := (STRUCT { "$tag" ::= $322 })%kami_expr.
Notation CSRsbadaddr := (STRUCT { "$tag" ::= $323 })%kami_expr.
Notation CSRsip := (STRUCT { "$tag" ::= $324 })%kami_expr.
Notation CSRsptbr := (STRUCT { "$tag" ::= $384 })%kami_expr.
Notation CSRscycle := (STRUCT { "$tag" ::= $3328 })%kami_expr.
Notation CSRstime := (STRUCT { "$tag" ::= $3329 })%kami_expr.
Notation CSRsinstret := (STRUCT { "$tag" ::= $3330 })%kami_expr.
Notation CSRscycleh := (STRUCT { "$tag" ::= $3456 })%kami_expr.
Notation CSRstimeh := (STRUCT { "$tag" ::= $3457 })%kami_expr.
Notation CSRsinstreth := (STRUCT { "$tag" ::= $3458 })%kami_expr.
Notation CSRhstatus := (STRUCT { "$tag" ::= $512 })%kami_expr.
Notation CSRhedeleg := (STRUCT { "$tag" ::= $514 })%kami_expr.
Notation CSRhideleg := (STRUCT { "$tag" ::= $515 })%kami_expr.
Notation CSRhie := (STRUCT { "$tag" ::= $516 })%kami_expr.
Notation CSRhtvec := (STRUCT { "$tag" ::= $517 })%kami_expr.
Notation CSRhscratch := (STRUCT { "$tag" ::= $576 })%kami_expr.
Notation CSRhepc := (STRUCT { "$tag" ::= $577 })%kami_expr.
Notation CSRhcause := (STRUCT { "$tag" ::= $578 })%kami_expr.
Notation CSRhbadaddr := (STRUCT { "$tag" ::= $579 })%kami_expr.
Notation CSRhcycle := (STRUCT { "$tag" ::= $3584 })%kami_expr.
Notation CSRhtime := (STRUCT { "$tag" ::= $3585 })%kami_expr.
Notation CSRhinstret := (STRUCT { "$tag" ::= $3586 })%kami_expr.
Notation CSRhcycleh := (STRUCT { "$tag" ::= $3712 })%kami_expr.
Notation CSRhtimeh := (STRUCT { "$tag" ::= $3713 })%kami_expr.
Notation CSRhinstreth := (STRUCT { "$tag" ::= $3714 })%kami_expr.
Notation CSRmisa := (STRUCT { "$tag" ::= $3856 })%kami_expr.
Notation CSRmvendorid := (STRUCT { "$tag" ::= $3857 })%kami_expr.
Notation CSRmarchid := (STRUCT { "$tag" ::= $3858 })%kami_expr.
Notation CSRmimpid := (STRUCT { "$tag" ::= $3859 })%kami_expr.
Notation CSRmhartid := (STRUCT { "$tag" ::= $3860 })%kami_expr.
Notation CSRmstatus := (STRUCT { "$tag" ::= $768 })%kami_expr.
Notation CSRmedeleg := (STRUCT { "$tag" ::= $770 })%kami_expr.
Notation CSRmideleg := (STRUCT { "$tag" ::= $771 })%kami_expr.
Notation CSRmie := (STRUCT { "$tag" ::= $772 })%kami_expr.
Notation CSRmtvec := (STRUCT { "$tag" ::= $773 })%kami_expr.
Notation CSRmscratch := (STRUCT { "$tag" ::= $832 })%kami_expr.
Notation CSRmepc := (STRUCT { "$tag" ::= $833 })%kami_expr.
Notation CSRmcause := (STRUCT { "$tag" ::= $834 })%kami_expr.
Notation CSRmbadaddr := (STRUCT { "$tag" ::= $835 })%kami_expr.
Notation CSRmip := (STRUCT { "$tag" ::= $836 })%kami_expr.
Notation CSRmbase := (STRUCT { "$tag" ::= $896 })%kami_expr.
Notation CSRmbound := (STRUCT { "$tag" ::= $897 })%kami_expr.
Notation CSRmibase := (STRUCT { "$tag" ::= $898 })%kami_expr.
Notation CSRmibound := (STRUCT { "$tag" ::= $899 })%kami_expr.
Notation CSRmdbase := (STRUCT { "$tag" ::= $900 })%kami_expr.
Notation CSRmdbound := (STRUCT { "$tag" ::= $901 })%kami_expr.
Notation CSRmcycle := (STRUCT { "$tag" ::= $3840 })%kami_expr.
Notation CSRmtime := (STRUCT { "$tag" ::= $3841 })%kami_expr.
Notation CSRminstret := (STRUCT { "$tag" ::= $3842 })%kami_expr.
Notation CSRmcycleh := (STRUCT { "$tag" ::= $3968 })%kami_expr.
Notation CSRmtimeh := (STRUCT { "$tag" ::= $3969 })%kami_expr.
Notation CSRminstreth := (STRUCT { "$tag" ::= $3970 })%kami_expr.
Notation CSRmucounteren := (STRUCT { "$tag" ::= $784 })%kami_expr.
Notation CSRmscounteren := (STRUCT { "$tag" ::= $785 })%kami_expr.
Notation CSRmhcounteren := (STRUCT { "$tag" ::= $786 })%kami_expr.
Notation CSRmucycle_delta := (STRUCT { "$tag" ::= $1792 })%kami_expr.
Notation CSRmutime_delta := (STRUCT { "$tag" ::= $1793 })%kami_expr.
Notation CSRmuinstret_delta := (STRUCT { "$tag" ::= $1794 })%kami_expr.
Notation CSRmscycle_delta := (STRUCT { "$tag" ::= $1796 })%kami_expr.
Notation CSRmstime_delta := (STRUCT { "$tag" ::= $1797 })%kami_expr.
Notation CSRmsinstret_delta := (STRUCT { "$tag" ::= $1798 })%kami_expr.
Notation CSRmhcycle_delta := (STRUCT { "$tag" ::= $1800 })%kami_expr.
Notation CSRmhtime_delta := (STRUCT { "$tag" ::= $1801 })%kami_expr.
Notation CSRmhinstret_delta := (STRUCT { "$tag" ::= $1802 })%kami_expr.
Notation CSRmucycle_deltah := (STRUCT { "$tag" ::= $1920 })%kami_expr.
Notation CSRmutime_deltah := (STRUCT { "$tag" ::= $1921 })%kami_expr.
Notation CSRmuinstret_deltah := (STRUCT { "$tag" ::= $1922 })%kami_expr.
Notation CSRmscycle_deltah := (STRUCT { "$tag" ::= $1924 })%kami_expr.
Notation CSRmstime_deltah := (STRUCT { "$tag" ::= $1925 })%kami_expr.
Notation CSRmsinstret_deltah := (STRUCT { "$tag" ::= $1926 })%kami_expr.
Notation CSRmhcycle_deltah := (STRUCT { "$tag" ::= $1928 })%kami_expr.
Notation CSRmhtime_deltah := (STRUCT { "$tag" ::= $1929 })%kami_expr.
Notation CSRmhinstret_deltah := (STRUCT { "$tag" ::= $1930 })%kami_expr.
Module mkPackCSR.
    Section Section'mkPackCSR.
    Variable instancePrefix: string.
            Definition mkPackCSRModule :=
        (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 12)) : CSR :=
    If (#v == $0) then
        Ret #CSRustatus;
        Retv
    else
    If (#v == $4) then
        Ret #CSRuie;
        Retv
    else
    If (#v == $5) then
        Ret #CSRutvec;
        Retv
    else
    If (#v == $64) then
        Ret #CSRuscratch;
        Retv
    else
    If (#v == $65) then
        Ret #CSRuepc;
        Retv
    else
    If (#v == $66) then
        Ret #CSRucause;
        Retv
    else
    If (#v == $67) then
        Ret #CSRubadaddr;
        Retv
    else
    If (#v == $68) then
        Ret #CSRuip;
        Retv
    else
    If (#v == $1) then
        Ret #CSRfflags;
        Retv
    else
    If (#v == $2) then
        Ret #CSRfrm;
        Retv
    else
    If (#v == $3) then
        Ret #CSRfcsr;
        Retv
    else
    If (#v == $3072) then
        Ret #CSRcycle;
        Retv
    else
    If (#v == $3073) then
        Ret #CSRtime;
        Retv
    else
    If (#v == $3074) then
        Ret #CSRinstret;
        Retv
    else
    If (#v == $3200) then
        Ret #CSRcycleh;
        Retv
    else
    If (#v == $3201) then
        Ret #CSRtimeh;
        Retv
    else
    If (#v == $3202) then
        Ret #CSRinstreth;
        Retv
    else
    If (#v == $256) then
        Ret #CSRsstatus;
        Retv
    else
    If (#v == $258) then
        Ret #CSRsedeleg;
        Retv
    else
    If (#v == $259) then
        Ret #CSRsideleg;
        Retv
    else
    If (#v == $260) then
        Ret #CSRsie;
        Retv
    else
    If (#v == $261) then
        Ret #CSRstvec;
        Retv
    else
    If (#v == $320) then
        Ret #CSRsscratch;
        Retv
    else
    If (#v == $321) then
        Ret #CSRsepc;
        Retv
    else
    If (#v == $322) then
        Ret #CSRscause;
        Retv
    else
    If (#v == $323) then
        Ret #CSRsbadaddr;
        Retv
    else
    If (#v == $324) then
        Ret #CSRsip;
        Retv
    else
    If (#v == $384) then
        Ret #CSRsptbr;
        Retv
    else
    If (#v == $3328) then
        Ret #CSRscycle;
        Retv
    else
    If (#v == $3329) then
        Ret #CSRstime;
        Retv
    else
    If (#v == $3330) then
        Ret #CSRsinstret;
        Retv
    else
    If (#v == $3456) then
        Ret #CSRscycleh;
        Retv
    else
    If (#v == $3457) then
        Ret #CSRstimeh;
        Retv
    else
    If (#v == $3458) then
        Ret #CSRsinstreth;
        Retv
    else
    If (#v == $512) then
        Ret #CSRhstatus;
        Retv
    else
    If (#v == $514) then
        Ret #CSRhedeleg;
        Retv
    else
    If (#v == $515) then
        Ret #CSRhideleg;
        Retv
    else
    If (#v == $516) then
        Ret #CSRhie;
        Retv
    else
    If (#v == $517) then
        Ret #CSRhtvec;
        Retv
    else
    If (#v == $576) then
        Ret #CSRhscratch;
        Retv
    else
    If (#v == $577) then
        Ret #CSRhepc;
        Retv
    else
    If (#v == $578) then
        Ret #CSRhcause;
        Retv
    else
    If (#v == $579) then
        Ret #CSRhbadaddr;
        Retv
    else
    If (#v == $3584) then
        Ret #CSRhcycle;
        Retv
    else
    If (#v == $3585) then
        Ret #CSRhtime;
        Retv
    else
    If (#v == $3586) then
        Ret #CSRhinstret;
        Retv
    else
    If (#v == $3712) then
        Ret #CSRhcycleh;
        Retv
    else
    If (#v == $3713) then
        Ret #CSRhtimeh;
        Retv
    else
    If (#v == $3714) then
        Ret #CSRhinstreth;
        Retv
    else
    If (#v == $3856) then
        Ret #CSRmisa;
        Retv
    else
    If (#v == $3857) then
        Ret #CSRmvendorid;
        Retv
    else
    If (#v == $3858) then
        Ret #CSRmarchid;
        Retv
    else
    If (#v == $3859) then
        Ret #CSRmimpid;
        Retv
    else
    If (#v == $3860) then
        Ret #CSRmhartid;
        Retv
    else
    If (#v == $768) then
        Ret #CSRmstatus;
        Retv
    else
    If (#v == $770) then
        Ret #CSRmedeleg;
        Retv
    else
    If (#v == $771) then
        Ret #CSRmideleg;
        Retv
    else
    If (#v == $772) then
        Ret #CSRmie;
        Retv
    else
    If (#v == $773) then
        Ret #CSRmtvec;
        Retv
    else
    If (#v == $832) then
        Ret #CSRmscratch;
        Retv
    else
    If (#v == $833) then
        Ret #CSRmepc;
        Retv
    else
    If (#v == $834) then
        Ret #CSRmcause;
        Retv
    else
    If (#v == $835) then
        Ret #CSRmbadaddr;
        Retv
    else
    If (#v == $836) then
        Ret #CSRmip;
        Retv
    else
    If (#v == $896) then
        Ret #CSRmbase;
        Retv
    else
    If (#v == $897) then
        Ret #CSRmbound;
        Retv
    else
    If (#v == $898) then
        Ret #CSRmibase;
        Retv
    else
    If (#v == $899) then
        Ret #CSRmibound;
        Retv
    else
    If (#v == $900) then
        Ret #CSRmdbase;
        Retv
    else
    If (#v == $901) then
        Ret #CSRmdbound;
        Retv
    else
    If (#v == $3840) then
        Ret #CSRmcycle;
        Retv
    else
    If (#v == $3841) then
        Ret #CSRmtime;
        Retv
    else
    If (#v == $3842) then
        Ret #CSRminstret;
        Retv
    else
    If (#v == $3968) then
        Ret #CSRmcycleh;
        Retv
    else
    If (#v == $3969) then
        Ret #CSRmtimeh;
        Retv
    else
    If (#v == $3970) then
        Ret #CSRminstreth;
        Retv
    else
    If (#v == $784) then
        Ret #CSRmucounteren;
        Retv
    else
    If (#v == $785) then
        Ret #CSRmscounteren;
        Retv
    else
    If (#v == $786) then
        Ret #CSRmhcounteren;
        Retv
    else
    If (#v == $1792) then
        Ret #CSRmucycle_delta;
        Retv
    else
    If (#v == $1793) then
        Ret #CSRmutime_delta;
        Retv
    else
    If (#v == $1794) then
        Ret #CSRmuinstret_delta;
        Retv
    else
    If (#v == $1796) then
        Ret #CSRmscycle_delta;
        Retv
    else
    If (#v == $1797) then
        Ret #CSRmstime_delta;
        Retv
    else
    If (#v == $1798) then
        Ret #CSRmsinstret_delta;
        Retv
    else
    If (#v == $1800) then
        Ret #CSRmhcycle_delta;
        Retv
    else
    If (#v == $1801) then
        Ret #CSRmhtime_delta;
        Retv
    else
    If (#v == $1802) then
        Ret #CSRmhinstret_delta;
        Retv
    else
    If (#v == $1920) then
        Ret #CSRmucycle_deltah;
        Retv
    else
    If (#v == $1921) then
        Ret #CSRmutime_deltah;
        Retv
    else
    If (#v == $1922) then
        Ret #CSRmuinstret_deltah;
        Retv
    else
    If (#v == $1924) then
        Ret #CSRmscycle_deltah;
        Retv
    else
    If (#v == $1925) then
        Ret #CSRmstime_deltah;
        Retv
    else
    If (#v == $1926) then
        Ret #CSRmsinstret_deltah;
        Retv
    else
    If (#v == $1928) then
        Ret #CSRmhcycle_deltah;
        Retv
    else
    If (#v == $1929) then
        Ret #CSRmhtime_deltah;
        Retv
    else
    If (#v == $1930) then
        Ret #CSRmhinstret_deltah;
        Retv
    else
        Retv

       with Method instancePrefix--"pack" (v : CSR) : (Bit 12) :=
    If (#v!CSRFields@."$tag" == $0) then
        Ret $12'h000;
        Retv
    else
    If (#v!CSRFields@."$tag" == $4) then
        Ret $12'h004;
        Retv
    else
    If (#v!CSRFields@."$tag" == $5) then
        Ret $12'h005;
        Retv
    else
    If (#v!CSRFields@."$tag" == $64) then
        Ret $12'h040;
        Retv
    else
    If (#v!CSRFields@."$tag" == $65) then
        Ret $12'h041;
        Retv
    else
    If (#v!CSRFields@."$tag" == $66) then
        Ret $12'h042;
        Retv
    else
    If (#v!CSRFields@."$tag" == $67) then
        Ret $12'h043;
        Retv
    else
    If (#v!CSRFields@."$tag" == $68) then
        Ret $12'h044;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1) then
        Ret $12'h001;
        Retv
    else
    If (#v!CSRFields@."$tag" == $2) then
        Ret $12'h002;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3) then
        Ret $12'h003;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3072) then
        Ret $12'hc00;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3073) then
        Ret $12'hc01;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3074) then
        Ret $12'hc02;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3200) then
        Ret $12'hc80;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3201) then
        Ret $12'hc81;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3202) then
        Ret $12'hc82;
        Retv
    else
    If (#v!CSRFields@."$tag" == $256) then
        Ret $12'h100;
        Retv
    else
    If (#v!CSRFields@."$tag" == $258) then
        Ret $12'h102;
        Retv
    else
    If (#v!CSRFields@."$tag" == $259) then
        Ret $12'h103;
        Retv
    else
    If (#v!CSRFields@."$tag" == $260) then
        Ret $12'h104;
        Retv
    else
    If (#v!CSRFields@."$tag" == $261) then
        Ret $12'h105;
        Retv
    else
    If (#v!CSRFields@."$tag" == $320) then
        Ret $12'h140;
        Retv
    else
    If (#v!CSRFields@."$tag" == $321) then
        Ret $12'h141;
        Retv
    else
    If (#v!CSRFields@."$tag" == $322) then
        Ret $12'h142;
        Retv
    else
    If (#v!CSRFields@."$tag" == $323) then
        Ret $12'h143;
        Retv
    else
    If (#v!CSRFields@."$tag" == $324) then
        Ret $12'h144;
        Retv
    else
    If (#v!CSRFields@."$tag" == $384) then
        Ret $12'h180;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3328) then
        Ret $12'hd00;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3329) then
        Ret $12'hd01;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3330) then
        Ret $12'hd02;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3456) then
        Ret $12'hd80;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3457) then
        Ret $12'hd81;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3458) then
        Ret $12'hd82;
        Retv
    else
    If (#v!CSRFields@."$tag" == $512) then
        Ret $12'h200;
        Retv
    else
    If (#v!CSRFields@."$tag" == $514) then
        Ret $12'h202;
        Retv
    else
    If (#v!CSRFields@."$tag" == $515) then
        Ret $12'h203;
        Retv
    else
    If (#v!CSRFields@."$tag" == $516) then
        Ret $12'h204;
        Retv
    else
    If (#v!CSRFields@."$tag" == $517) then
        Ret $12'h205;
        Retv
    else
    If (#v!CSRFields@."$tag" == $576) then
        Ret $12'h240;
        Retv
    else
    If (#v!CSRFields@."$tag" == $577) then
        Ret $12'h241;
        Retv
    else
    If (#v!CSRFields@."$tag" == $578) then
        Ret $12'h242;
        Retv
    else
    If (#v!CSRFields@."$tag" == $579) then
        Ret $12'h243;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3584) then
        Ret $12'he00;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3585) then
        Ret $12'he01;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3586) then
        Ret $12'he02;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3712) then
        Ret $12'he80;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3713) then
        Ret $12'he81;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3714) then
        Ret $12'he82;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3856) then
        Ret $12'hf10;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3857) then
        Ret $12'hf11;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3858) then
        Ret $12'hf12;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3859) then
        Ret $12'hf13;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3860) then
        Ret $12'hf14;
        Retv
    else
    If (#v!CSRFields@."$tag" == $768) then
        Ret $12'h300;
        Retv
    else
    If (#v!CSRFields@."$tag" == $770) then
        Ret $12'h302;
        Retv
    else
    If (#v!CSRFields@."$tag" == $771) then
        Ret $12'h303;
        Retv
    else
    If (#v!CSRFields@."$tag" == $772) then
        Ret $12'h304;
        Retv
    else
    If (#v!CSRFields@."$tag" == $773) then
        Ret $12'h305;
        Retv
    else
    If (#v!CSRFields@."$tag" == $832) then
        Ret $12'h340;
        Retv
    else
    If (#v!CSRFields@."$tag" == $833) then
        Ret $12'h341;
        Retv
    else
    If (#v!CSRFields@."$tag" == $834) then
        Ret $12'h342;
        Retv
    else
    If (#v!CSRFields@."$tag" == $835) then
        Ret $12'h343;
        Retv
    else
    If (#v!CSRFields@."$tag" == $836) then
        Ret $12'h344;
        Retv
    else
    If (#v!CSRFields@."$tag" == $896) then
        Ret $12'h380;
        Retv
    else
    If (#v!CSRFields@."$tag" == $897) then
        Ret $12'h381;
        Retv
    else
    If (#v!CSRFields@."$tag" == $898) then
        Ret $12'h382;
        Retv
    else
    If (#v!CSRFields@."$tag" == $899) then
        Ret $12'h383;
        Retv
    else
    If (#v!CSRFields@."$tag" == $900) then
        Ret $12'h384;
        Retv
    else
    If (#v!CSRFields@."$tag" == $901) then
        Ret $12'h385;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3840) then
        Ret $12'hf00;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3841) then
        Ret $12'hf01;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3842) then
        Ret $12'hf02;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3968) then
        Ret $12'hf80;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3969) then
        Ret $12'hf81;
        Retv
    else
    If (#v!CSRFields@."$tag" == $3970) then
        Ret $12'hf82;
        Retv
    else
    If (#v!CSRFields@."$tag" == $784) then
        Ret $12'h310;
        Retv
    else
    If (#v!CSRFields@."$tag" == $785) then
        Ret $12'h311;
        Retv
    else
    If (#v!CSRFields@."$tag" == $786) then
        Ret $12'h312;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1792) then
        Ret $12'h700;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1793) then
        Ret $12'h701;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1794) then
        Ret $12'h702;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1796) then
        Ret $12'h704;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1797) then
        Ret $12'h705;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1798) then
        Ret $12'h706;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1800) then
        Ret $12'h708;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1801) then
        Ret $12'h709;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1802) then
        Ret $12'h70a;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1920) then
        Ret $12'h780;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1921) then
        Ret $12'h781;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1922) then
        Ret $12'h782;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1924) then
        Ret $12'h784;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1925) then
        Ret $12'h785;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1926) then
        Ret $12'h786;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1928) then
        Ret $12'h788;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1929) then
        Ret $12'h789;
        Retv
    else
    If (#v!CSRFields@."$tag" == $1930) then
        Ret $12'h78a;
        Retv
    else
        Retv

    }). (* mkPackCSR *)

    Definition mkPackCSR := Build_Pack mkPackCSRModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackCSR.
End mkPackCSR.

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
    "opcode" :: Opcode;
    "csrAddr" :: (Bit 12);
    "csr" :: CSR}).
Definition InstructionFields  := Struct (InstructionFieldsFields).

(* * interface GetInstFields *)
Record GetInstFields := {
    GetInstFields'interface: Modules;
    GetInstFields'getInstFields : string;
}.

Module mkGetInstFields.
    Section Section'mkGetInstFields.
    Variable instancePrefix: string.
    Let packCSRunpack := MethodSig (Pack'unpack packCSR) (Bit sz) : t.
    Let packOpcodeunpack := MethodSig (Pack'unpack packOpcode) (Bit sz) : t.
    Let packRVRoundModeunpack := MethodSig (Pack'unpack packRVRoundMode) (Bit sz) : t.
                       Let packRVRoundMode := mkPackRVRoundMode (instancePrefix--"packRVRoundMode").
       Let packOpcode := mkPackOpcode (instancePrefix--"packOpcode").
       Let packCSR := mkPackCSR (instancePrefix--"packCSR").
    Definition mkGetInstFieldsModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance packRVRoundMode :: nil))
       with (BKMod (FIXME'InterfaceName'instance packOpcode :: nil))
       with (BKMod (FIXME'InterfaceName'instance packCSR :: nil))
       with Method instancePrefix--"getInstFields" (x : Instruction) : InstructionFields :=
        Ret STRUCT { "inst" ::= #x; "rd" ::= #x[$11 : $7]; "rs1" ::= #x[$19 : $15]; "rs2" ::= #x[$24 : $20]; "rs3" ::= #x[$31 : $27]; "funct2" ::= #x[$26 : $25]; "funct3" ::= #x[$14 : $12]; "funct5" ::= #x[$31 : $27]; "funct7" ::= #x[$31 : $25]; "fmt" ::= #x[$26 : $25]; "rm" ::=  packRVRoundModeunpack(#x[$14 : $12]); "opcode" ::=  packOpcodeunpack(#x[$6 : $0]); "csrAddr" ::= #x[$31 : $20]; "csr" ::=  packCSRunpack(#x[$31 : $20])  }

    }). (* mkGetInstFields *)

    Definition mkGetInstFields := Build_GetInstFields mkGetInstFieldsModule%kami (instancePrefix--"getInstFields").
    End Section'mkGetInstFields.
End mkGetInstFields.

Definition RVMemOpFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVMemOp := (Struct RVMemOpFields).
Notation Ld := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation St := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation PrefetchForLd := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation PrefetchForSt := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation Lr := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation Sc := (STRUCT { "$tag" ::= $7 })%kami_expr.
Definition RVAmoOpFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVAmoOp := (Struct RVAmoOpFields).
Notation Swap := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation Add := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Xor := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation And := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation Or := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation Min := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation Max := (STRUCT { "$tag" ::= $10 })%kami_expr.
Notation Minu := (STRUCT { "$tag" ::= $12 })%kami_expr.
Notation Maxu := (STRUCT { "$tag" ::= $14 })%kami_expr.
Definition RVMemSizeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RVMemSize := (Struct RVMemSizeFields).
Notation B := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation H := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation W := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation D := (STRUCT { "$tag" ::= $3 })%kami_expr.
(* * interface ToDataByteEn#(n) *)
Record ToDataByteEn (n : nat) := {
    ToDataByteEn'interface: Modules;
    ToDataByteEn'toDataByteEn : string;
}.

Module mkToDataByteEn4.
    Section Section'mkToDataByteEn4.
    Variable instancePrefix: string.
        Definition mkToDataByteEn4Module :=
        (BKMODULE {
           Method instancePrefix--"toDataByteEn" (size : RVMemSize) : (Bit 4) :=
        Ret null

    }). (* mkToDataByteEn4 *)

    Definition mkToDataByteEn4 := Build_ToDataByteEn mkToDataByteEn4Module%kami (instancePrefix--"toDataByteEn").
    End Section'mkToDataByteEn4.
End mkToDataByteEn4.

Module mkToDataByteEn8.
    Section Section'mkToDataByteEn8.
    Variable instancePrefix: string.
        Definition mkToDataByteEn8Module :=
        (BKMODULE {
           Method instancePrefix--"toDataByteEn" (size : RVMemSize) : (Bit 8) :=
        Ret null

    }). (* mkToDataByteEn8 *)

    Definition mkToDataByteEn8 := Build_ToDataByteEn mkToDataByteEn8Module%kami (instancePrefix--"toDataByteEn").
    End Section'mkToDataByteEn8.
End mkToDataByteEn8.

(* * interface ToPermutedDataByteEn *)
Record ToPermutedDataByteEn := {
    ToPermutedDataByteEn'interface: Modules;
    ToPermutedDataByteEn'toPermutedDataByteEn : string;
}.

Module mkToPermutedDataByteEn.
    Section Section'mkToPermutedDataByteEn.
    Variable instancePrefix: string.
               Let tdbe := mkToDataByteEn4 (instancePrefix--"tdbe").
    Definition mkToPermutedDataByteEnModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance tdbe :: nil))
       with Method2 instancePrefix--"toPermutedDataByteEn" (size : RVMemSize) (addrLSB : DataByteSel) : DataByteEn :=
        Ret ( tdbetoDataByteEn(#size) << #addrLSB)

    }). (* mkToPermutedDataByteEn *)

    Definition mkToPermutedDataByteEn := Build_ToPermutedDataByteEn mkToPermutedDataByteEnModule%kami (instancePrefix--"toPermutedDataByteEn").
    End Section'mkToPermutedDataByteEn.
End mkToPermutedDataByteEn.

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
    IsMemOp'interface: Modules;
    IsMemOp'isLoad : string;
    IsMemOp'isStore : string;
    IsMemOp'isAmo : string;
    IsMemOp'getsReadPermission : string;
    IsMemOp'getsWritePermission : string;
    IsMemOp'getsResponse : string;
}.

Module mkIsMemOpRVMemOp.
    Section Section'mkIsMemOpRVMemOp.
    Variable instancePrefix: string.
                            Definition mkIsMemOpRVMemOpModule :=
        (BKMODULE {
           Method instancePrefix--"isLoad" (x : RVMemOp) : Bool :=
        Ret ((#x == #Ld) || (#x == #Lr))

       with Method instancePrefix--"isStore" (x : RVMemOp) : Bool :=
        Ret ((#x == #St) || (#x == #Sc))

       with Method instancePrefix--"isAmo" (x : RVMemOp) : Bool :=
        Ret #False

       with Method instancePrefix--"getsReadPermission" (x : RVMemOp) : Bool :=
        Ret ((#x == #Ld) || (#x == #PrefetchForLd))

       with Method instancePrefix--"getsWritePermission" (x : RVMemOp) : Bool :=
        Ret ((((#x == #St) || (#x == #Sc)) || (#x == #Lr)) || (#x == #PrefetchForSt))

       with Method instancePrefix--"getsResponse" (x : RVMemOp) : Bool :=
        Ret (((#x == #Ld) || (#x == #Lr)) || (#x == #Sc))

    }). (* mkIsMemOpRVMemOp *)

    Definition mkIsMemOpRVMemOp := Build_IsMemOp mkIsMemOpRVMemOpModule%kami (instancePrefix--"getsReadPermission") (instancePrefix--"getsResponse") (instancePrefix--"getsWritePermission") (instancePrefix--"isAmo") (instancePrefix--"isLoad") (instancePrefix--"isStore").
    End Section'mkIsMemOpRVMemOp.
End mkIsMemOpRVMemOp.

Module mkIsMemOpRVAmoOp.
    Section Section'mkIsMemOpRVAmoOp.
    Variable instancePrefix: string.
                            Definition mkIsMemOpRVAmoOpModule :=
        (BKMODULE {
           Method instancePrefix--"isLoad" (x : RVAmoOp) : Bool :=
        Ret #False

       with Method instancePrefix--"isStore" (x : RVAmoOp) : Bool :=
        Ret #False

       with Method instancePrefix--"isAmo" (x : RVAmoOp) : Bool :=
        Ret #True

       with Method instancePrefix--"getsReadPermission" (x : RVAmoOp) : Bool :=
        Ret #False

       with Method instancePrefix--"getsWritePermission" (x : RVAmoOp) : Bool :=
        Ret #True

       with Method instancePrefix--"getsResponse" (x : RVAmoOp) : Bool :=
        Ret #True

    }). (* mkIsMemOpRVAmoOp *)

    Definition mkIsMemOpRVAmoOp := Build_IsMemOp mkIsMemOpRVAmoOpModule%kami (instancePrefix--"getsReadPermission") (instancePrefix--"getsResponse") (instancePrefix--"getsWritePermission") (instancePrefix--"isAmo") (instancePrefix--"isLoad") (instancePrefix--"isStore").
    End Section'mkIsMemOpRVAmoOp.
End mkIsMemOpRVAmoOp.

Module mkIsMemOpRVMemAmoOp.
    Section Section'mkIsMemOpRVMemAmoOp.
    Variable instancePrefix: string.
    Let isMemOpAmogetsReadPermission := MethodSig (IsMemOp'getsReadPermission isMemOpAmo) (t) : Bool.
    Let isMemOpAmogetsResponse := MethodSig (IsMemOp'getsResponse isMemOpAmo) (t) : Bool.
    Let isMemOpAmogetsWritePermission := MethodSig (IsMemOp'getsWritePermission isMemOpAmo) (t) : Bool.
    Let isMemOpAmoisAmo := MethodSig (IsMemOp'isAmo isMemOpAmo) (t) : Bool.
    Let isMemOpAmoisLoad := MethodSig (IsMemOp'isLoad isMemOpAmo) (t) : Bool.
    Let isMemOpAmoisStore := MethodSig (IsMemOp'isStore isMemOpAmo) (t) : Bool.
    Let isMemOpMemgetsReadPermission := MethodSig (IsMemOp'getsReadPermission isMemOpMem) (t) : Bool.
    Let isMemOpMemgetsResponse := MethodSig (IsMemOp'getsResponse isMemOpMem) (t) : Bool.
    Let isMemOpMemgetsWritePermission := MethodSig (IsMemOp'getsWritePermission isMemOpMem) (t) : Bool.
    Let isMemOpMemisAmo := MethodSig (IsMemOp'isAmo isMemOpMem) (t) : Bool.
    Let isMemOpMemisLoad := MethodSig (IsMemOp'isLoad isMemOpMem) (t) : Bool.
    Let isMemOpMemisStore := MethodSig (IsMemOp'isStore isMemOpMem) (t) : Bool.
                                       Let isMemOpMem := mkIsMemOpRVMemOp (instancePrefix--"isMemOpMem").
       Let isMemOpAmo := mkIsMemOpRVAmoOp (instancePrefix--"isMemOpAmo").
    Definition mkIsMemOpRVMemAmoOpModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance isMemOpMem :: nil))
       with (BKMod (FIXME'InterfaceName'instance isMemOpAmo :: nil))
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

    Definition mkIsMemOpRVMemAmoOp := Build_IsMemOp mkIsMemOpRVMemAmoOpModule%kami (instancePrefix--"getsReadPermission") (instancePrefix--"getsResponse") (instancePrefix--"getsWritePermission") (instancePrefix--"isAmo") (instancePrefix--"isLoad") (instancePrefix--"isStore").
    End Section'mkIsMemOpRVMemAmoOp.
End mkIsMemOpRVMemAmoOp.

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
    GetMISA'interface: Modules;
    GetMISA'getMISA : string;
}.

Module mkGetMISA.
    Section Section'mkGetMISA.
    Variable instancePrefix: string.
        Definition mkGetMISAModule :=
        (BKMODULE {
           Method instancePrefix--"getMISA" (isa : RiscVISASubset) : Data :=
        LET misa : Data <- (BinBit (Concat 2 4) $2'b00 $4'd0);
        If #isa
        then                 BKSTMTS {
                Assign misa = (#misa | (BinBit (Concat 2 4) $2'b10 $4'd0));
;
        Retv
        else                 BKSTMTS {
                Assign misa = (#misa | (BinBit (Concat 2 4) $2'b01 $4'd0));
;
        Retv;;
        If #isa
        then                 Assign misa = (#misa | (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv;
        If #isa
        then                 Assign misa = (#misa | (BinBit (Concat 2 4) $2'b00 $4'd0));
        Retv;
        Ret #misa

    }). (* mkGetMISA *)

    Definition mkGetMISA := Build_GetMISA mkGetMISAModule%kami (instancePrefix--"getMISA").
    End Section'mkGetMISA.
End mkGetMISA.

Definition RegIndex := (word 5).

Definition FullRegIndexFields := (STRUCT {
    "$tag" :: (Bit 8);
    "Gpr" :: RegIndex;
    "Fpu" :: RegIndex}).
Definition FullRegIndex := Struct (FullRegIndexFields).
(* * interface ToFullRegIndex *)
Record ToFullRegIndex := {
    ToFullRegIndex'interface: Modules;
    ToFullRegIndex'toFullRegIndex : string;
}.

Module mkToFullRegIndex.
    Section Section'mkToFullRegIndex.
    Variable instancePrefix: string.
        Definition mkToFullRegIndexModule :=
        (BKMODULE {
           Method2 instancePrefix--"toFullRegIndex" (rType : (Maybe RegType)) (index : RegIndex) : (Maybe FullRegIndex) :=
        Ret null

    }). (* mkToFullRegIndex *)

    Definition mkToFullRegIndex := Build_ToFullRegIndex mkToFullRegIndexModule%kami (instancePrefix--"toFullRegIndex").
    End Section'mkToFullRegIndex.
End mkToFullRegIndex.

Definition NumArchReg := 64.

Definition NumPhyReg := NumArchReg.

(* * interface HasCSRPermission *)
Record HasCSRPermission := {
    HasCSRPermission'interface: Modules;
    HasCSRPermission'hasCSRPermission : string;
}.

Module mkHasCSRPermission.
    Section Section'mkHasCSRPermission.
    Variable instancePrefix: string.
    Let packCSRpack := MethodSig (Pack'pack packCSR) (t) : Bit sz.
               Let packCSR := mkPackCSR (instancePrefix--"packCSR").
    Definition mkHasCSRPermissionModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance packCSR :: nil))
       with Method3 instancePrefix--"hasCSRPermission" (csr : CSR) (prv : (Bit 2)) (write : Bool) : Bool :=
LET csr_index <- ;
        Ret ((#prv >= #csr_index[$9 : $8]) && (!#write || (#csr_index[$11 : $10] != $2'b11)))

    }). (* mkHasCSRPermission *)

    Definition mkHasCSRPermission := Build_HasCSRPermission mkHasCSRPermissionModule%kami (instancePrefix--"hasCSRPermission").
    End Section'mkHasCSRPermission.
End mkHasCSRPermission.

Definition BrFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition BrFunc := (Struct BrFuncFields).
Notation BrEq := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation BrNeq := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation BrJal := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation BrJalr := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation BrLt := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation BrGe := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation BrLtu := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation BrGeu := (STRUCT { "$tag" ::= $7 })%kami_expr.
Definition AluFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition AluFunc := (Struct AluFuncFields).
Notation AluAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AluSll := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation AluSlt := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation AluSltu := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation AluXor := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation AluSrl := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation AluOr := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation AluAnd := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation AluSub := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation AluSra := (STRUCT { "$tag" ::= $13 })%kami_expr.
Notation AluAuipc := (STRUCT { "$tag" ::= $16 })%kami_expr.
Notation AluLui := (STRUCT { "$tag" ::= $24 })%kami_expr.
Definition AluInstFields := (STRUCT {
    "op" :: AluFunc;
    "w" :: Bool}).
Definition AluInst  := Struct (AluInstFields).

Definition MulDivFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition MulDivFunc := (Struct MulDivFuncFields).
Notation Mul := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Mulh := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation Div := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation Rem := (STRUCT { "$tag" ::= $3 })%kami_expr.
Definition MulDivSignFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition MulDivSign := (Struct MulDivSignFields).
Notation Signed := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Unsigned := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SignedUnsigned := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition MulDivInstFields := (STRUCT {
    "func" :: MulDivFunc;
    "w" :: Bool;
    "sign" :: MulDivSign}).
Definition MulDivInst  := Struct (MulDivInstFields).

Definition FpuFuncFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition FpuFunc := (Struct FpuFuncFields).
Notation FAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSub := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMul := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FDiv := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSqrt := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSgnj := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSgnjn := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FSgnjx := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMin := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMax := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_WF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_WUF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_LF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_LUF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FW := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FWU := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FL := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FCvt_FLU := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FEq := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FLt := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FLe := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FClass := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMv_XF := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMv_FX := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FMSub := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FNMSub := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation FNMAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition FpuPrecisionFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition FpuPrecision := (Struct FpuPrecisionFields).
Notation Single := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation Double := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition FpuInstFields := (STRUCT {
    "func" :: FpuFunc;
    "precision" :: FpuPrecision}).
Definition FpuInst  := Struct (FpuInstFields).

Definition IntraCoreFenceFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition IntraCoreFence := (Struct IntraCoreFenceFields).
Notation FenceI := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SFenceVM := (STRUCT { "$tag" ::= $0 })%kami_expr.
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
Definition SystemInstFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition SystemInst := (Struct SystemInstFields).
Notation ECall := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation EBreak := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation URet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SRet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation HRet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation MRet := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation WFI := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRRW := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRRS := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRRC := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRR := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation CSRW := (STRUCT { "$tag" ::= $0 })%kami_expr.
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
Definition RegTypeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition RegType := (Struct RegTypeFields).
Notation RtGpr := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation RtFpu := (STRUCT { "$tag" ::= $1 })%kami_expr.
Definition ImmTypeFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition ImmType := (Struct ImmTypeFields).
Notation ItNone := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItI := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItS := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItSB := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItU := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItUJ := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation ItZ := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition RVDecodedInstFields := (STRUCT {
    "execFunc" :: ExecFunc;
    "imm" :: ImmType;
    "rs1" :: (Maybe RegType);
    "rs2" :: (Maybe RegType);
    "rs3" :: (Maybe RegType);
    "dst" :: (Maybe RegType);
    "inst" :: Instruction}).
Definition RVDecodedInst  := Struct (RVDecodedInstFields).

Definition ExceptionCauseFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition ExceptionCause := (Struct ExceptionCauseFields).
Notation InstAddrMisaligned := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation InstAccessFault := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation IllegalInst := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation Breakpoint := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation LoadAddrMisaligned := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation LoadAccessFault := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation StoreAddrMisaligned := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation StoreAccessFault := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation EnvCallU := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation EnvCallS := (STRUCT { "$tag" ::= $9 })%kami_expr.
Notation EnvCallH := (STRUCT { "$tag" ::= $10 })%kami_expr.
Notation EnvCallM := (STRUCT { "$tag" ::= $11 })%kami_expr.
Notation IllegalException := (STRUCT { "$tag" ::= $15 })%kami_expr.
Definition InterruptCauseFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition InterruptCause := (Struct InterruptCauseFields).
Notation USoftwareInterrupt := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation SSoftwareInterrupt := (STRUCT { "$tag" ::= $1 })%kami_expr.
Notation HSoftwareInterrupt := (STRUCT { "$tag" ::= $2 })%kami_expr.
Notation MSoftwareInterrupt := (STRUCT { "$tag" ::= $3 })%kami_expr.
Notation UTimerInterrupt := (STRUCT { "$tag" ::= $4 })%kami_expr.
Notation STimerInterrupt := (STRUCT { "$tag" ::= $5 })%kami_expr.
Notation HTimerInterrupt := (STRUCT { "$tag" ::= $6 })%kami_expr.
Notation MTimerInterrupt := (STRUCT { "$tag" ::= $7 })%kami_expr.
Notation UExternalInterrupt := (STRUCT { "$tag" ::= $8 })%kami_expr.
Notation SExternalInterrupt := (STRUCT { "$tag" ::= $9 })%kami_expr.
Notation HExternalInterrupt := (STRUCT { "$tag" ::= $10 })%kami_expr.
Notation MExternalInterrupt := (STRUCT { "$tag" ::= $11 })%kami_expr.
Notation IllegalInterrupt := (STRUCT { "$tag" ::= $15 })%kami_expr.
Definition TrapCauseFields := (STRUCT {
    "$tag" :: (Bit 8);
    "TcException" :: ExceptionCause;
    "TcInterrupt" :: InterruptCause}).
Definition TrapCause := Struct (TrapCauseFields).
(* * interface ToCauseCSR *)
Record ToCauseCSR := {
    ToCauseCSR'interface: Modules;
    ToCauseCSR'toCauseCSR : string;
}.

Module mkToCauseCSR.
    Section Section'mkToCauseCSR.
    Variable instancePrefix: string.
        Definition mkToCauseCSRModule :=
        (BKMODULE {
           Method instancePrefix--"toCauseCSR" (x : TrapCause) : Data :=
    If (#x!TrapCauseFields@."$tag" == $0) then
              LET cause <- x;
        BKSTMTS {
        LET pcause <- ;
                Ret (BinBit (Concat 28 4) $28'd0 #pcause);
;
        Retv
    else
    If (#x!TrapCauseFields@."$tag" == $1) then
              LET cause <- x;
        BKSTMTS {
        LET pcause <- ;
                Ret (BinBit (Concat 1 27) $1'b1 $27'd0);
;
        Retv
    else
        Retv

    }). (* mkToCauseCSR *)

    Definition mkToCauseCSR := Build_ToCauseCSR mkToCauseCSRModule%kami (instancePrefix--"toCauseCSR").
    End Section'mkToCauseCSR.
End mkToCauseCSR.

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
    FullResultSubset'interface: Modules;
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

Definition PMAFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition PMA := (Struct PMAFields).
Notation MainMemory := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation IORom := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation IODevice := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation IOEmpty := (STRUCT { "$tag" ::= $0 })%kami_expr.
(* * interface IsCacheable *)
Record IsCacheable := {
    IsCacheable'interface: Modules;
    IsCacheable'isCacheable : string;
}.

Module mkIsCacheable.
    Section Section'mkIsCacheable.
    Variable instancePrefix: string.
        Definition mkIsCacheableModule :=
        (BKMODULE {
           Method instancePrefix--"isCacheable" (pma : PMA) : Bool :=
        Ret null

    }). (* mkIsCacheable *)

    Definition mkIsCacheable := Build_IsCacheable mkIsCacheableModule%kami (instancePrefix--"isCacheable").
    End Section'mkIsCacheable.
End mkIsCacheable.

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

Definition isLegalPTE (pte: PTE_Sv39): bool := 
                Ret (&& #pte !(&& #pte !#pte))

.

Definition isLeafPTE (pte: PTE_Sv39): bool := 
                Ret (&& #pte (|| (|| #pte #pte) #pte))

.

