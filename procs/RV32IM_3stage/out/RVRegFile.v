Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Ehr.
Require Import Vector.
Require Import RegUtil.
Require Import RVTypes.
(* * interface RVRegFile#(xlen) *)
Record RVRegFile (xlen : nat) := {
    RVRegFile'interface: Modules;
    RVRegFile'wr : string;
    RVRegFile'rd1 : string;
    RVRegFile'rd2 : string;
    RVRegFile'rd3 : string;
}.

Module mkRVRegFile.
    Section Section'mkRVRegFile.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable hasFPU: bool.
                    Definition read (fullRegIndex: Maybe FullRegIndex): (Bit xlen) := 
                Ret null

.

                       Let gpr_rfile := replicateM (instancePrefix--"gpr_rfile").
       Let fpu_rfile := replicateM (instancePrefix--"fpu_rfile").
    Definition mkRVRegFileModule :=
        (BKMODULE {
                   LET verbose : Bool = #False
       with         LET fout : File <- #stdout
       with (BKMod (FIXME'InterfaceName'instance gpr_rfile :: nil))
       with (BKMod (FIXME'InterfaceName'instance fpu_rfile :: nil))
       with Method2 instancePrefix--"wr" (fullRegIndex : (Maybe FullRegIndex)) (data : (Bit xlen)) : Void :=
        If #verbose
        then          FIXME$$fdisplay(#fout,  fshow(#fullRegIndex), null, #data);
        Retv;
    If (#fullRegIndex!MaybeFields@."$tag" == $0) then
#noAction;
        Retv
    else
    If (#fullRegIndex!MaybeFields@."$tag" == $0) then
        Write gpr_rfile[#rIndex] <- #data;
        Retv
    else
    If (#fullRegIndex!MaybeFields@."$tag" == $0) then
        Write fpu_rfile[#rIndex] <- #data;
        Retv
    else
        Retv;
        Retv

       with Method instancePrefix--"rd1" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

       with Method instancePrefix--"rd2" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

       with Method instancePrefix--"rd3" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

    }). (* mkRVRegFile *)

    Definition mkRVRegFile := Build_RVRegFile xlen mkRVRegFileModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile.
End mkRVRegFile.

Module mkRVRegFileBypass.
    Section Section'mkRVRegFileBypass.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable hasFPU: bool.
                            Definition read (fullRegIndex: Maybe FullRegIndex): (Bit xlen) := 
                LET result : (Bit xlen) <- $0

                If #fullRegIndex$taggedValid.validIndex
        then                 BKSTMTS {
                If (#validIndex == STRUCT {  "$tag" ::= $0; "Gpr" ::= $0; "Fpu" ::= $0 })
        then                 BKSTMTS {
                Assign result = $0
;
        Retv
        else                 If (#validIndex ==  tpl_1(#writeReq[$1]))
        then                 BKSTMTS {
                Assign result =  tpl_2(#writeReq[$1])
;
        Retv
        else                 BKSTMTS {
                Assign result = null
;
        Retv;;
        Retv;
;
        Retv

                Ret #result

.

                       Let gpr_rfile := replicateM (instancePrefix--"gpr_rfile").
       Let fpu_rfile := replicateM (instancePrefix--"fpu_rfile").
       Let writeReq := mkEhr (instancePrefix--"writeReq").
    Definition mkRVRegFileBypassModule :=
        (BKMODULE {
                   LET verbose : Bool = #False
       with         LET fout : File <- #stdout
       with (BKMod (FIXME'InterfaceName'instance gpr_rfile :: nil))
       with (BKMod (FIXME'InterfaceName'instance fpu_rfile :: nil))
       with (BKMod (FIXME'InterfaceName'instance writeReq :: nil))
       with Rule instancePrefix--"performWrite" :=
           If ( tpl_1(#writeReq[$1])!FullRegIndexFields@."$tag" == $0) then
#noAction;
        Retv
    else
    If ( tpl_1(#writeReq[$1])!FullRegIndexFields@."$tag" == $0) then
              LET rIndex <- tpl_1(writeReq[1]);
        Write gpr_rfile[#rIndex] <-  tpl_2(#writeReq[$1]);
        Retv
    else
    If ( tpl_1(#writeReq[$1])!FullRegIndexFields@."$tag" == $1) then
              LET rIndex <- tpl_1(writeReq[1]);
        Write fpu_rfile[#rIndex] <-  tpl_2(#writeReq[$1]);
        Retv
    else
        Retv;
               Write writeReq[$1] <-  tuple2(STRUCT {  "$tag" ::= $0; "Gpr" ::= $0; "Fpu" ::= $0 }, $0);
        Retv (* rule performWrite *)
       with Method2 instancePrefix--"wr" (fullRegIndex : (Maybe FullRegIndex)) (data : (Bit xlen)) : Void :=
        If #verbose
        then          FIXME$$fdisplay(#fout,  fshow(#fullRegIndex), null, #data);
        Retv;
        Write writeReq[$0] <-  tuple2( fromMaybe(STRUCT {  "$tag" ::= $0; "Gpr" ::= $0; "Fpu" ::= $0 }, #fullRegIndex), #data);
        Retv

       with Method instancePrefix--"rd1" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

       with Method instancePrefix--"rd2" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

       with Method instancePrefix--"rd3" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

    }). (* mkRVRegFileBypass *)

    Definition mkRVRegFileBypass := Build_RVRegFile xlen mkRVRegFileBypassModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass.
End mkRVRegFileBypass.

Module mkRVRegFile32WithFPU.
    Section Section'mkRVRegFile32WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile32WithFPUModule :=
        (BKMODULE {
                   Call _m : tvar1221 <-  mkRVRegFile(#True)
       with         Ret #_m
    }). (* mkRVRegFile32WithFPU *)

    Definition mkRVRegFile32WithFPU := Build_RVRegFile mkRVRegFile32WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile32WithFPU.
End mkRVRegFile32WithFPU.

Module mkRVRegFile32WithoutFPU.
    Section Section'mkRVRegFile32WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile32WithoutFPUModule :=
        (BKMODULE {
                   Call _m : tvar1223 <-  mkRVRegFile(#False)
       with         Ret #_m
    }). (* mkRVRegFile32WithoutFPU *)

    Definition mkRVRegFile32WithoutFPU := Build_RVRegFile mkRVRegFile32WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile32WithoutFPU.
End mkRVRegFile32WithoutFPU.

Module mkRVRegFileBypass32WithFPU.
    Section Section'mkRVRegFileBypass32WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass32WithFPUModule :=
        (BKMODULE {
                   Call _m : tvar1225 <-  mkRVRegFileBypass(#True)
       with         Ret #_m
    }). (* mkRVRegFileBypass32WithFPU *)

    Definition mkRVRegFileBypass32WithFPU := Build_RVRegFile mkRVRegFileBypass32WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass32WithFPU.
End mkRVRegFileBypass32WithFPU.

Module mkRVRegFileBypass32WithoutFPU.
    Section Section'mkRVRegFileBypass32WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass32WithoutFPUModule :=
        (BKMODULE {
                   Call _m : tvar1227 <-  mkRVRegFileBypass(#False)
       with         Ret #_m
    }). (* mkRVRegFileBypass32WithoutFPU *)

    Definition mkRVRegFileBypass32WithoutFPU := Build_RVRegFile mkRVRegFileBypass32WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass32WithoutFPU.
End mkRVRegFileBypass32WithoutFPU.

Module mkRVRegFile64WithFPU.
    Section Section'mkRVRegFile64WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile64WithFPUModule :=
        (BKMODULE {
                   Call _m : tvar1229 <-  mkRVRegFile(#True)
       with         Ret #_m
    }). (* mkRVRegFile64WithFPU *)

    Definition mkRVRegFile64WithFPU := Build_RVRegFile mkRVRegFile64WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile64WithFPU.
End mkRVRegFile64WithFPU.

Module mkRVRegFile64WithoutFPU.
    Section Section'mkRVRegFile64WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile64WithoutFPUModule :=
        (BKMODULE {
                   Call _m : tvar1231 <-  mkRVRegFile(#False)
       with         Ret #_m
    }). (* mkRVRegFile64WithoutFPU *)

    Definition mkRVRegFile64WithoutFPU := Build_RVRegFile mkRVRegFile64WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile64WithoutFPU.
End mkRVRegFile64WithoutFPU.

Module mkRVRegFileBypass64WithFPU.
    Section Section'mkRVRegFileBypass64WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass64WithFPUModule :=
        (BKMODULE {
                   Call _m : tvar1233 <-  mkRVRegFileBypass(#True)
       with         Ret #_m
    }). (* mkRVRegFileBypass64WithFPU *)

    Definition mkRVRegFileBypass64WithFPU := Build_RVRegFile mkRVRegFileBypass64WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass64WithFPU.
End mkRVRegFileBypass64WithFPU.

Module mkRVRegFileBypass64WithoutFPU.
    Section Section'mkRVRegFileBypass64WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass64WithoutFPUModule :=
        (BKMODULE {
                   Call _m : tvar1235 <-  mkRVRegFileBypass(#False)
       with         Ret #_m
    }). (* mkRVRegFileBypass64WithoutFPU *)

    Definition mkRVRegFileBypass64WithoutFPU := Build_RVRegFile mkRVRegFileBypass64WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass64WithoutFPU.
End mkRVRegFileBypass64WithoutFPU.

