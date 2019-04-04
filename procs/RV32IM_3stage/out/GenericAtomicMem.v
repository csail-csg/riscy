Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import BRAMCore.
Require Import RegFile.
Require Import Vector.
Require Import Ehr.
Require Import FIFOG.
Require Import Port.
Definition GenericAtomicMemReqFields (writeEnSz : nat) (atomicMemOpT : Type) (wordAddrSz : nat) (dataSz : nat) := (STRUCT {
    "write_en" :: (Bit writeEnSz);
    "atomic_op" :: atomicMemOpT;
    "word_addr" :: (Bit wordAddrSz);
    "data" :: (Bit dataSz)}).
Definition GenericAtomicMemReq  (writeEnSz : nat) (atomicMemOpT : Type) (wordAddrSz : nat) (dataSz : nat) := Struct (GenericAtomicMemReqFields writeEnSz atomicMemOpT wordAddrSz dataSz).

Definition GenericAtomicMemRespFields (dataSz : nat) := (STRUCT {
    "write" :: Bool;
    "data" :: (Bit dataSz)}).
Definition GenericAtomicMemResp  (dataSz : nat) := Struct (GenericAtomicMemRespFields dataSz).

Definition (GenericAtomicMemServerPort writeEnSz atomicMemOpT wordAddrSz dataSz) := (ServerPort (GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz) (GenericAtomicMemResp dataSz)).

Definition (GenericAtomicMemClientPort writeEnSz atomicMemOpT wordAddrSz dataSz) := (ClientPort (GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz) (GenericAtomicMemResp dataSz)).

Definition AMONone := Void.

Definition AMOSwapFields := (STRUCT { "$tag" :: (Bit 1) }).
Definition AMOSwap := (Struct AMOSwapFields).
Notation AsNone := (STRUCT { "$tag" ::= $$(natToWord 1 0) })%kami_expr.
Notation AsSwap := (STRUCT { "$tag" ::= $$(natToWord 1 1) })%kami_expr.
Definition AMOLogicalFields := (STRUCT { "$tag" :: (Bit 3) }).
Definition AMOLogical := (Struct AMOLogicalFields).
Notation AlNone := (STRUCT { "$tag" ::= $$(natToWord 3 0) })%kami_expr.
Notation AlSwap := (STRUCT { "$tag" ::= $$(natToWord 3 1) })%kami_expr.
Notation AlAnd := (STRUCT { "$tag" ::= $$(natToWord 3 2) })%kami_expr.
Notation AlOr := (STRUCT { "$tag" ::= $$(natToWord 3 3) })%kami_expr.
Notation AlXor := (STRUCT { "$tag" ::= $$(natToWord 3 4) })%kami_expr.
Definition AMOArithmeticFields := (STRUCT { "$tag" :: (Bit 4) }).
Definition AMOArithmetic := (Struct AMOArithmeticFields).
Notation AaNone := (STRUCT { "$tag" ::= $$(natToWord 4 0) })%kami_expr.
Notation AaSwap := (STRUCT { "$tag" ::= $$(natToWord 4 1) })%kami_expr.
Notation AaAnd := (STRUCT { "$tag" ::= $$(natToWord 4 2) })%kami_expr.
Notation AaOr := (STRUCT { "$tag" ::= $$(natToWord 4 3) })%kami_expr.
Notation AaXor := (STRUCT { "$tag" ::= $$(natToWord 4 4) })%kami_expr.
Notation AaAdd := (STRUCT { "$tag" ::= $$(natToWord 4 5) })%kami_expr.
Notation AaMin := (STRUCT { "$tag" ::= $$(natToWord 4 6) })%kami_expr.
Notation AaMax := (STRUCT { "$tag" ::= $$(natToWord 4 7) })%kami_expr.
Notation AaMinu := (STRUCT { "$tag" ::= $$(natToWord 4 8) })%kami_expr.
Notation AaMaxu := (STRUCT { "$tag" ::= $$(natToWord 4 9) })%kami_expr.
Definition writeEnExtend (write_en: Bit writeEnSz): (Bit dataSz) := 
        CallM write_en_vec : (Vector writeEnSz (Bit 1)) <-  unpack(#write_en)

                Ret  pack( map(#signExtend, #write_en_vec))

.

Definition emulateWriteEn (memData: Bit dataSz) (writeData: Bit dataSz) (writeEn: Bit writeEnSz): (Bit dataSz) := 
        CallM bitEn : (Bit dataSz) <-  writeEnExtend(#writeEn)

                Ret (| (& #writeData #bitEn) (& #memData ~#bitEn))

.

Definition GenericAtomicBRAMPendingReqFields (writeEnSz : nat) (atomicMemOpT : Type) := (STRUCT {
    "write_en" :: (Bit writeEnSz);
    "atomic_op" :: atomicMemOpT;
    "rmw_write" :: Bool}).
Definition GenericAtomicBRAMPendingReq  (writeEnSz : nat) (atomicMemOpT : Type) := Struct (GenericAtomicBRAMPendingReqFields writeEnSz atomicMemOpT).

Definition to_BRAM_PORT_BE (bram: BRAM_PORT addrT dataT): (BRAM_PORT_BE addrT dataT writeEnSz) := 
        Method3 instancePrefix--"put" (writeen : (Bit writeEnSz)) (addr : addrT) (data : dataT) : Void :=
 bramput((!= #writeen $0), #addr, #data);
        Retv


        Method instancePrefix--"read" () : dataT :=
#bram


                Ret null

.

Definition LoadFormatFields := (STRUCT {
    "$tag" :: (Bit 8);
    "LfNone" :: Void;
    "LfHex" :: String;
    "LfBinary" :: String}).
Definition LoadFormat := Struct (LoadFormatFields).
Module module'mkGenericAtomicBRAM.
    Section Section'mkGenericAtomicBRAM.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable numWords: nat.
    Variable TDiv#(dataSz,writeEnSz): nat.
    Hypothesis HMul: (dataSz = TDiv#(dataSz,writeEnSz) * writeEnSz)%nat.
    Variable atomicMemOpSz: nat.
            Definition mkGenericAtomicBRAMModule: Modules.
        refine  (BKMODULE {
                   Call _m : tvar541 <-  mkGenericAtomicBRAMLoad($numWords, STRUCT {  "$tag" ::= $0; "LfBinary" ::= $0; "LfHex" ::= $0; "LfNone" ::= $0 })
       with         Ret #_m
    }); abstract omega. Qed. (* mkGenericAtomicBRAM *)

(* Module mkGenericAtomicBRAM type Integer -> Module#(GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz)) return type GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz) *)
    Definition mkGenericAtomicBRAM := Build_ServerPort (writeEnSz) (atomicMemOpT) (wordAddrSz) (dataSz) mkGenericAtomicBRAMModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicBRAM.
End module'mkGenericAtomicBRAM.

Definition mkGenericAtomicBRAM := module'mkGenericAtomicBRAM.mkGenericAtomicBRAM.

Module module'mkGenericAtomicBRAMLoad.
    Section Section'mkGenericAtomicBRAMLoad.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable numWords: nat.
    Variable loadFile: LoadFormat.
    Variable TDiv#(dataSz,writeEnSz): nat.
    Hypothesis HMul: (dataSz = TDiv#(dataSz,writeEnSz) * writeEnSz)%nat.
    Variable atomicMemOpSz: nat.
                                                   Let pendingReq := mkEhr (instancePrefix--"pendingReq").
       Let pendingResp := mkBypassFIFOG (instancePrefix--"pendingResp").
       Let atomicOpWordAddr : string := instancePrefix--"atomicOpWordAddr".
       Let atomicOpData : string := instancePrefix--"atomicOpData".
    Let bramput : string := (BRAM_PORT_BE'put bram).
(* FIXME: interface BRAM_PORT_BE subinterface read *)
    Let pendingRespenq : string := (FIFOG'enq pendingResp).
    Definition mkGenericAtomicBRAMLoadModule: Modules.
        refine  (BKMODULE {
                   LET actualNumWords : nat <- ($numWords == $0)null$numWords
       with         LET bram : (BRAM_PORT_BE (Bit wordAddrSz) (Bit dataSz) writeEnSz)
       with         If (null == $1)
        then                 BKSTMTS {
                LET bram_non_be : (BRAM_PORT (Bit wordAddrSz) (Bit dataSz))
        with     If (#loadFile!LoadFormatFields@."$tag" == $0) then (
        Assign bram_non_be <-  mkBRAMCore1($actualNumWords, False)

   ) else (
    If (#loadFile!LoadFormatFields@."$tag" == $1) then (
              LET hexfile <- loadFile;
        Assign bram_non_be <-  mkBRAMCore1Load($actualNumWords, False, #hexfile, False)

   ) else (
    If (#loadFile!LoadFormatFields@."$tag" == $2) then (
              LET binfile <- loadFile;
        Assign bram_non_be <-  mkBRAMCore1Load($actualNumWords, False, #binfile, True)

   ) else (
#noAction
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval

        with         Assign bram =  to_BRAM_PORT_BE(#bram_non_be)
;
        Retv
        else                 BKSTMTS {
            If (#loadFile!LoadFormatFields@."$tag" == $0) then (
        Assign bram <-  mkBRAMCore1BE($actualNumWords, False)

   ) else (
    If (#loadFile!LoadFormatFields@."$tag" == $1) then (
              LET hexfile <- loadFile;
        Assign bram <-  mkBRAMCore1BELoad($actualNumWords, False, #hexfile, False)

   ) else (
    If (#loadFile!LoadFormatFields@."$tag" == $2) then (
              LET binfile <- loadFile;
        Assign bram <-  mkBRAMCore1BELoad($actualNumWords, False, #binfile, True)

   ) else (
#noAction
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval

;
        Retv;
       with (BKMod (t'modules pendingReq :: nil))
       with (BKMod (FIFOG'modules pendingResp :: nil))
       with Register atomicOpWordAddr : Bit wordAddrSz <- $0
       with Register atomicOpData : Bit dataSz <- $0
       with Rule instancePrefix--"performAtomicMemoryOp" :=
        Read atomicOpData_v : Bit dataSz <- atomicOpData;
        Read atomicOpWordAddr_v : Bit wordAddrSz <- atomicOpWordAddr;
        Assert(#pendingReq@[$0]$taggedValid.req isAtomicMemOp(#req));
               Call writeData : tvar555 <-  atomicMemOpFunc(#req, #bram, #atomicOpData_v, #req);
        bramput(#req, #atomicOpWordAddr_v, #writeData);
               Write pendingReq[$0] <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "write_en" ::= (#req); "atomic_op" ::= (#nonAtomicMemOp); "rmw_write" ::= (True)  }; "Invalid" ::= $0 };
               Write atomicOpData : Bit dataSz <- #bram;
        Retv (* rule performAtomicMemoryOp *)
       with Rule instancePrefix--"getRespFromCore" :=
        Read atomicOpData_v : Bit dataSz <- atomicOpData;
        Assert(#pendingReq@[$0]$taggedValid.req! isAtomicMemOp(#req));
        pendingRespenq(STRUCT { "write" ::= ((#req != $0)); "data" ::= (#req#atomicOpData_v#bram)  });
               Write pendingReq[$0] <- STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
        Retv (* rule getRespFromCore *)
       with Method instancePrefix--"enq" (req : (GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz)) : Void :=
        LET atomic_op : atomicMemOpT <- (#req == $0)#nonAtomicMemOp#req;
        If  isAtomicMemOp(#atomic_op)
        then                 BKSTMTS {
         bramput($0, #req, #req);
                Write atomicOpWordAddr : Bit wordAddrSz <- #req;
                Write atomicOpData : Bit dataSz <- #req;
;
        Retv
        else                 BKSTMTS {
         bramput(#req, #req, #req);
;
        Retv;;
        Write pendingReq[$1] <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "write_en" ::= (#req); "atomic_op" ::= (#atomic_op); "rmw_write" ::= (False)  }; "Invalid" ::= $0 };
        Retv

       with Method instancePrefix--"canEnq" () : Bool :=
        Ret ! isValid(#pendingReq@[$1])

    }); abstract omega. Qed. (* mkGenericAtomicBRAMLoad *)

(* Module mkGenericAtomicBRAMLoad type Integer -> LoadFormat -> Module#(GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz)) return type LoadFormat *)
    Definition mkGenericAtomicBRAMLoad := Build_ServerPort mkGenericAtomicBRAMLoadModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicBRAMLoad.
End module'mkGenericAtomicBRAMLoad.

Definition mkGenericAtomicBRAMLoad := module'mkGenericAtomicBRAMLoad.mkGenericAtomicBRAMLoad.

Definition performGenericAtomicMemOpOnRegs (regs: Vector numRegs Reg Bit dataSz) (req: GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz): (ActionValue (GenericAtomicMemResp dataSz)) := 
        LET index : (Bit (TLog numRegs)) <- UniBit (Trunc TLog#(numRegs) (wordAddrSz - TLog#(numRegs))) (castBits _ _ _ _ #req)

                LET resp : (GenericAtomicMemResp dataSz) <- STRUCT { "write" ::= ((!= #req $0)); "data" ::= ($0)  }

                If (<= #index  fromInteger((- null $1)))
        then                 BKSTMTS {
                If (== #req $0)
        then                 BKSTMTS {
                Assign resp.data = #regs@[#index]
;
        Retv
        else                 If (&& (== #req $1) ! isAtomicMemOp(#req))
        then                 BKSTMTS {
                Write regs[#index] <- #req
;
        Retv
        else                 If ! isAtomicMemOp(#req)
        then                 BKSTMTS {
                Write regs[#index] <-  emulateWriteEn(#regs@[#index], #req, #req)
;
        Retv
        else                 BKSTMTS {
                Call write_data : tvar582 <-  atomicMemOpFunc(#req, #regs@[#index], #req, #req)
        with         Write regs[#index] <-  emulateWriteEn(#regs@[#index], #write_data, #req)
        with         Assign resp.data = #regs@[#index]
;
        Retv;;
        Retv;;
        Retv;
;
        Retv

                Ret #resp

                Ret null

.

Definition performGenericAtomicMemOpOnRegFile (rf: RegFile Bit rfWordAddrSz Bit dataSz) (req: GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz): (ActionValue (GenericAtomicMemResp dataSz)) := 
        LET index : (Bit rfWordAddrSz) <- UniBit (Trunc rfWordAddrSz (wordAddrSz - rfWordAddrSz)) (castBits _ _ _ _ #req)

                LET resp : (GenericAtomicMemResp dataSz) <- STRUCT { "write" ::= ((!= #req $0)); "data" ::= ($0)  }

                If (== #req $0)
        then                 BKSTMTS {
                Assign resp.data =  rfsub(#index)
;
        Retv
        else                 If (&& (== #req $1) ! isAtomicMemOp(#req))
        then                 BKSTMTS {
         rfupd(#index, #req)
;
        Retv
        else                 If ! isAtomicMemOp(#req)
        then                 BKSTMTS {
                Call new_data : tvar590 <-  emulateWriteEn( rfsub(#index), #req, #req)
        with  rfupd(#index, #new_data)
;
        Retv
        else                 BKSTMTS {
                Call old_data : tvar591 <-  rfsub(#index)
        with         Call write_data : tvar595 <-  atomicMemOpFunc(#req, #old_data, #req, #req)
        with         Call new_data : tvar598 <-  emulateWriteEn(#old_data, #write_data, #req)
        with  rfupd(#index, #new_data)
        with         Assign resp.data = #old_data
;
        Retv;;
        Retv;;
        Retv;

                Ret #resp

                Ret null

.

Module module'mkGenericAtomicMemFromRegs.
    Section Section'mkGenericAtomicMemFromRegs.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable numRegs : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable regs: (Vector numRegs (Reg (Bit dataSz))).
    Variable byteSz: nat.
    Hypothesis HMul: (dataSz = writeEnSz * byteSz)%nat.
    Variable a__: nat.
    Variable 1: nat.
    Hypothesis HAdd: (byteSz = a__ + 1)%nat.
    Variable b__: nat.
    Variable TLog#(numRegs): nat.
    Hypothesis HAdd: (wordAddrSz = b__ + TLog#(numRegs))%nat.
    Variable atomicMemOpSz: nat.
                           Let reqFIFO := mkLFIFOG (instancePrefix--"reqFIFO").
       Let respFIFO := mkBypassFIFOG (instancePrefix--"respFIFO").
(* FIXME: interface FIFOG subinterface deq *)
(* FIXME: interface FIFOG subinterface first *)
    Let respFIFOenq : string := (FIFOG'enq respFIFO).
    Definition mkGenericAtomicMemFromRegsModule: Modules.
        refine  (BKMODULE {
           (BKMod (FIFOG'modules reqFIFO :: nil))
       with (BKMod (FIFOG'modules respFIFO :: nil))
       with Rule instancePrefix--"performMemReq" :=
               LET req : t = #reqFIFO;
       #reqFIFO;
               Call resp : tvar601 <-  performGenericAtomicMemOpOnRegs(#regs, #req);
        respFIFOenq(#resp);
        Retv (* rule performMemReq *)
    }); abstract omega. Qed. (* mkGenericAtomicMemFromRegs *)

(* Module mkGenericAtomicMemFromRegs type Vector#(numRegs, Reg#(Bit#(dataSz))) -> Module#(GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz)) return type GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz) *)
    Definition mkGenericAtomicMemFromRegs := Build_ServerPort (writeEnSz) (atomicMemOpT) (wordAddrSz) (dataSz) mkGenericAtomicMemFromRegsModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicMemFromRegs.
End module'mkGenericAtomicMemFromRegs.

Definition mkGenericAtomicMemFromRegs := module'mkGenericAtomicMemFromRegs.mkGenericAtomicMemFromRegs.

Module module'mkGenericAtomicMemFromRegFile.
    Section Section'mkGenericAtomicMemFromRegFile.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable rfWordAddrSz : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable rf: (RegFile (Bit rfWordAddrSz) (Bit dataSz)).
    Variable byteSz: nat.
    Hypothesis HMul: (dataSz = writeEnSz * byteSz)%nat.
    Variable a__: nat.
    Variable 1: nat.
    Hypothesis HAdd: (byteSz = a__ + 1)%nat.
    Variable b__: nat.
    Hypothesis HAdd: (wordAddrSz = b__ + rfWordAddrSz)%nat.
    Variable atomicMemOpSz: nat.
                           Let reqFIFO := mkLFIFOG (instancePrefix--"reqFIFO").
       Let respFIFO := mkBypassFIFOG (instancePrefix--"respFIFO").
(* FIXME: interface FIFOG subinterface deq *)
(* FIXME: interface FIFOG subinterface first *)
    Let respFIFOenq : string := (FIFOG'enq respFIFO).
    Definition mkGenericAtomicMemFromRegFileModule: Modules.
        refine  (BKMODULE {
           (BKMod (FIFOG'modules reqFIFO :: nil))
       with (BKMod (FIFOG'modules respFIFO :: nil))
       with Rule instancePrefix--"performMemReq" :=
               LET req : t = #reqFIFO;
       #reqFIFO;
               Call resp : tvar604 <-  performGenericAtomicMemOpOnRegFile(#rf_v, #req);
        respFIFOenq(#resp);
        Retv (* rule performMemReq *)
    }); abstract omega. Qed. (* mkGenericAtomicMemFromRegFile *)

(* Module mkGenericAtomicMemFromRegFile type RegFile#(Bit#(rfWordAddrSz), Bit#(dataSz)) -> Module#(GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz)) return type GenericAtomicMemServerPort#(writeEnSz, atomicMemOpT, wordAddrSz, dataSz) *)
    Definition mkGenericAtomicMemFromRegFile := Build_ServerPort (writeEnSz) (atomicMemOpT) (wordAddrSz) (dataSz) mkGenericAtomicMemFromRegFileModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicMemFromRegFile.
End module'mkGenericAtomicMemFromRegFile.

Definition mkGenericAtomicMemFromRegFile := module'mkGenericAtomicMemFromRegFile.mkGenericAtomicMemFromRegFile.

