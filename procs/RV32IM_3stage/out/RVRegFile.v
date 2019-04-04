Require Import Bool String List Arith.
Require Import Omega.
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
    RVRegFile'modules: Modules;
    RVRegFile'wr : string;
    RVRegFile'rd1 : string;
    RVRegFile'rd2 : string;
    RVRegFile'rd3 : string;
}.

Module module'mkRVRegFile.
    Section Section'mkRVRegFile.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable hasFPU: Bool.
                    Definition read (fullRegIndex: Maybe FullRegIndex): (Bit xlen) := 
                Ret null

.

                       Let gpr_rfile := replicateM (instancePrefix--"gpr_rfile").
       Let fpu_rfile := replicateM (instancePrefix--"fpu_rfile").
    Definition mkRVRegFileModule: Modules :=
         (BKMODULE {
                   LET verbose : Bool = False
       with         LET fout : File <- #stdout
       with (BKMod (m'modules gpr_rfile :: nil))
       with (BKMod (m'modules fpu_rfile :: nil))
       with Method2 instancePrefix--"wr" (fullRegIndex : (Maybe FullRegIndex)) (data : (Bit xlen)) : Void :=
        If #verbose
        then          FIXME$$fdisplay(#fout,  fshow(#fullRegIndex), null, #data);
        Retv;
    If (#fullRegIndex!MaybeFields@."$tag" == $0) then (
#noAction

   ) else (
    If (#fullRegIndex!MaybeFields@."$tag" == $0) then (
        Write gpr_rfile[#rIndex] <- #data

   ) else (
    If (#fullRegIndex!MaybeFields@."$tag" == $0) then (
        Write fpu_rfile[#rIndex] <- #data

   ) else (
#noAction
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
;
        Retv

       with Method instancePrefix--"rd1" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

       with Method instancePrefix--"rd2" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

       with Method instancePrefix--"rd3" (fullRegIndex : (Maybe FullRegIndex)) : (Bit xlen) :=
 read(#fullRegIndex)

    }). (* mkRVRegFile *)

(* Module mkRVRegFile type Bool -> Module#(RVRegFile#(xlen)) return type RVRegFile#(xlen) *)
    Definition mkRVRegFile := Build_RVRegFile (xlen) mkRVRegFileModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile.
End module'mkRVRegFile.

Definition mkRVRegFile := module'mkRVRegFile.mkRVRegFile.

Module module'mkRVRegFileBypass.
    Section Section'mkRVRegFileBypass.
    Variable xlen : Kind.
    Variable instancePrefix: string.
    Variable hasFPU: Bool.
                            Definition read (fullRegIndex: Maybe FullRegIndex): (Bit xlen) := 
                LET result : (Bit xlen) <- $0

                If #fullRegIndex$taggedValid.validIndex
        then                 BKSTMTS {
                If (#validIndex == STRUCT {  "$tag" ::= $0; "Gpr" ::= $0; "Fpu" ::= $0 })
        then                 BKSTMTS {
                Assign result = $0
;
        Retv
        else                 If (#validIndex ==  tpl_1(#writeReq@[$1]))
        then                 BKSTMTS {
                Assign result =  tpl_2(#writeReq@[$1])
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
    Definition mkRVRegFileBypassModule: Modules :=
         (BKMODULE {
                   LET verbose : Bool = False
       with         LET fout : File <- #stdout
       with (BKMod (m'modules gpr_rfile :: nil))
       with (BKMod (m'modules fpu_rfile :: nil))
       with (BKMod (t'modules writeReq :: nil))
       with Rule instancePrefix--"performWrite" :=
           If ( tpl_1(#writeReq@[$1])!FullRegIndexFields@."$tag" == $0) then (
#noAction

   ) else (
    If ( tpl_1(#writeReq@[$1])!FullRegIndexFields@."$tag" == $0) then (
              LET rIndex <- tpl_1(writeReq[1]);
        Write gpr_rfile[#rIndex] <-  tpl_2(#writeReq@[$1])

   ) else (
    If ( tpl_1(#writeReq@[$1])!FullRegIndexFields@."$tag" == $1) then (
              LET rIndex <- tpl_1(writeReq[1]);
        Write fpu_rfile[#rIndex] <-  tpl_2(#writeReq@[$1])

   ) else (
#noAction
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
;
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

(* Module mkRVRegFileBypass type Bool -> Module#(RVRegFile#(xlen)) return type RVRegFile#(xlen) *)
    Definition mkRVRegFileBypass := Build_RVRegFile (xlen) mkRVRegFileBypassModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass.
End module'mkRVRegFileBypass.

Definition mkRVRegFileBypass := module'mkRVRegFileBypass.mkRVRegFileBypass.

Module module'mkRVRegFile32WithFPU.
    Section Section'mkRVRegFile32WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile32WithFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1227 <-  mkRVRegFile(True)
       with         Ret #_m
    }). (* mkRVRegFile32WithFPU *)

(* Module mkRVRegFile32WithFPU type Module#(RVRegFile#(32)) return type RVRegFile#(32) *)
    Definition mkRVRegFile32WithFPU := Build_RVRegFile (32) mkRVRegFile32WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile32WithFPU.
End module'mkRVRegFile32WithFPU.

Definition mkRVRegFile32WithFPU := module'mkRVRegFile32WithFPU.mkRVRegFile32WithFPU.

Module module'mkRVRegFile32WithoutFPU.
    Section Section'mkRVRegFile32WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile32WithoutFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1229 <-  mkRVRegFile(False)
       with         Ret #_m
    }). (* mkRVRegFile32WithoutFPU *)

(* Module mkRVRegFile32WithoutFPU type Module#(RVRegFile#(32)) return type RVRegFile#(32) *)
    Definition mkRVRegFile32WithoutFPU := Build_RVRegFile (32) mkRVRegFile32WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile32WithoutFPU.
End module'mkRVRegFile32WithoutFPU.

Definition mkRVRegFile32WithoutFPU := module'mkRVRegFile32WithoutFPU.mkRVRegFile32WithoutFPU.

Module module'mkRVRegFileBypass32WithFPU.
    Section Section'mkRVRegFileBypass32WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass32WithFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1231 <-  mkRVRegFileBypass(True)
       with         Ret #_m
    }). (* mkRVRegFileBypass32WithFPU *)

(* Module mkRVRegFileBypass32WithFPU type Module#(RVRegFile#(32)) return type RVRegFile#(32) *)
    Definition mkRVRegFileBypass32WithFPU := Build_RVRegFile (32) mkRVRegFileBypass32WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass32WithFPU.
End module'mkRVRegFileBypass32WithFPU.

Definition mkRVRegFileBypass32WithFPU := module'mkRVRegFileBypass32WithFPU.mkRVRegFileBypass32WithFPU.

Module module'mkRVRegFileBypass32WithoutFPU.
    Section Section'mkRVRegFileBypass32WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass32WithoutFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1233 <-  mkRVRegFileBypass(False)
       with         Ret #_m
    }). (* mkRVRegFileBypass32WithoutFPU *)

(* Module mkRVRegFileBypass32WithoutFPU type Module#(RVRegFile#(32)) return type RVRegFile#(32) *)
    Definition mkRVRegFileBypass32WithoutFPU := Build_RVRegFile (32) mkRVRegFileBypass32WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass32WithoutFPU.
End module'mkRVRegFileBypass32WithoutFPU.

Definition mkRVRegFileBypass32WithoutFPU := module'mkRVRegFileBypass32WithoutFPU.mkRVRegFileBypass32WithoutFPU.

Module module'mkRVRegFile64WithFPU.
    Section Section'mkRVRegFile64WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile64WithFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1235 <-  mkRVRegFile(True)
       with         Ret #_m
    }). (* mkRVRegFile64WithFPU *)

(* Module mkRVRegFile64WithFPU type Module#(RVRegFile#(64)) return type RVRegFile#(64) *)
    Definition mkRVRegFile64WithFPU := Build_RVRegFile (64) mkRVRegFile64WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile64WithFPU.
End module'mkRVRegFile64WithFPU.

Definition mkRVRegFile64WithFPU := module'mkRVRegFile64WithFPU.mkRVRegFile64WithFPU.

Module module'mkRVRegFile64WithoutFPU.
    Section Section'mkRVRegFile64WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFile64WithoutFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1237 <-  mkRVRegFile(False)
       with         Ret #_m
    }). (* mkRVRegFile64WithoutFPU *)

(* Module mkRVRegFile64WithoutFPU type Module#(RVRegFile#(64)) return type RVRegFile#(64) *)
    Definition mkRVRegFile64WithoutFPU := Build_RVRegFile (64) mkRVRegFile64WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFile64WithoutFPU.
End module'mkRVRegFile64WithoutFPU.

Definition mkRVRegFile64WithoutFPU := module'mkRVRegFile64WithoutFPU.mkRVRegFile64WithoutFPU.

Module module'mkRVRegFileBypass64WithFPU.
    Section Section'mkRVRegFileBypass64WithFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass64WithFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1239 <-  mkRVRegFileBypass(True)
       with         Ret #_m
    }). (* mkRVRegFileBypass64WithFPU *)

(* Module mkRVRegFileBypass64WithFPU type Module#(RVRegFile#(64)) return type RVRegFile#(64) *)
    Definition mkRVRegFileBypass64WithFPU := Build_RVRegFile (64) mkRVRegFileBypass64WithFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass64WithFPU.
End module'mkRVRegFileBypass64WithFPU.

Definition mkRVRegFileBypass64WithFPU := module'mkRVRegFileBypass64WithFPU.mkRVRegFileBypass64WithFPU.

Module module'mkRVRegFileBypass64WithoutFPU.
    Section Section'mkRVRegFileBypass64WithoutFPU.
    Variable instancePrefix: string.
            Definition mkRVRegFileBypass64WithoutFPUModule: Modules :=
         (BKMODULE {
                   Call _m : tvar1241 <-  mkRVRegFileBypass(False)
       with         Ret #_m
    }). (* mkRVRegFileBypass64WithoutFPU *)

(* Module mkRVRegFileBypass64WithoutFPU type Module#(RVRegFile#(64)) return type RVRegFile#(64) *)
    Definition mkRVRegFileBypass64WithoutFPU := Build_RVRegFile (64) mkRVRegFileBypass64WithoutFPUModule%kami (instancePrefix--"rd1") (instancePrefix--"rd2") (instancePrefix--"rd3") (instancePrefix--"wr").
    End Section'mkRVRegFileBypass64WithoutFPU.
End module'mkRVRegFileBypass64WithoutFPU.

Definition mkRVRegFileBypass64WithoutFPU := module'mkRVRegFileBypass64WithoutFPU.mkRVRegFileBypass64WithoutFPU.

