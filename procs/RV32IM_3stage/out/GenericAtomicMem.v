Require Import Bool String List Arith.
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

Definition AMONone := void.

Definition AMOSwapFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition AMOSwap := (Struct AMOSwapFields).
Notation AsNone := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AsSwap := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition AMOLogicalFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition AMOLogical := (Struct AMOLogicalFields).
Notation AlNone := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AlSwap := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AlAnd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AlOr := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AlXor := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition AMOArithmeticFields := (STRUCT { "$tag" :: (Bit 8) }).
Definition AMOArithmetic := (Struct AMOArithmeticFields).
Notation AaNone := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaSwap := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaAnd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaOr := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaXor := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaAdd := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaMin := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaMax := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaMinu := (STRUCT { "$tag" ::= $0 })%kami_expr.
Notation AaMaxu := (STRUCT { "$tag" ::= $0 })%kami_expr.
Definition writeEnExtend (write_en: word writeEnSz): (word dataSz) := 
        LET write_en_vec <- 

                Ret  pack( map(#signExtend, #write_en_vec))

.

Definition emulateWriteEn (memData: word dataSz) (writeData: word dataSz) (writeEn: word writeEnSz): (word dataSz) := 
        LET bitEn <- 

                Ret (| (& #writeData #bitEn) (& #memData ~#bitEn))

.

Definition GenericAtomicBRAMPendingReqFields (writeEnSz : nat) (atomicMemOpT : Type) := (STRUCT {
    "write_en" :: (Bit writeEnSz);
    "atomic_op" :: atomicMemOpT;
    "rmw_write" :: Bool}).
Definition GenericAtomicBRAMPendingReq  (writeEnSz : nat) (atomicMemOpT : Type) := Struct (GenericAtomicBRAMPendingReqFields writeEnSz atomicMemOpT).

Definition to_BRAM_PORT_BE (bram: BRAM_PORT addrT dataT): (BRAM_PORT_BE addrT dataT writeEnSz) := 
        Method3 instancePrefix--"put" (writeen : (word writeEnSz)) (addr : addrT) (data : dataT) : Void :=
 bramput((!= #writeen $0), #addr, #data);
        Retv


        Method instancePrefix--"read" () : dataT :=
#bram


                Ret null

.

Definition LoadFormatFields := (STRUCT {
    "$tag" :: (Bit 8);
    "LfNone" :: void;
    "LfHex" :: String;
    "LfBinary" :: String}).
Definition LoadFormat := Struct (LoadFormatFields).
Module mkGenericAtomicBRAM.
    Section Section'mkGenericAtomicBRAM.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable numWords: nat.
            Definition mkGenericAtomicBRAMModule :=
        (BKMODULE {
                   Call _m : tvar535 <-  mkGenericAtomicBRAMLoad($numWords, STRUCT {  "$tag" ::= $0; "LfBinary" ::= $0; "LfHex" ::= $0; "LfNone" ::= $0 })
       with         Ret #_m
    }). (* mkGenericAtomicBRAM *)

    Definition mkGenericAtomicBRAM := Build_ServerPort atomicMemOpT dataSz wordAddrSz writeEnSz mkGenericAtomicBRAMModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicBRAM.
End mkGenericAtomicBRAM.

Module mkGenericAtomicBRAMLoad.
    Section Section'mkGenericAtomicBRAMLoad.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable numWords: nat.
    Variable loadFile: LoadFormat.
    Let bramput := MethodSig (BRAM_PORT_BE'put bram) (Bit n) : Function addr Function data Void.
(* FIXME: interface BRAM_PORT_BE subinterface read *)
    Let pendingRespenq := MethodSig (FIFOG'enq pendingResp) (t) : Void.
                                                   Let pendingReq := mkEhr (instancePrefix--"pendingReq").
       Let pendingResp := mkBypassFIFOG (instancePrefix--"pendingResp").
       Let atomicOpWordAddr : string := instancePrefix--"atomicOpWordAddr".
       Let atomicOpData : string := instancePrefix--"atomicOpData".
    Definition mkGenericAtomicBRAMLoadModule :=
        (BKMODULE {
                   LET actualNumWords : nat <- ($numWords == $0)null$numWords
       with         LET bram : (BRAM_PORT_BE (Bit wordAddrSz) (Bit dataSz) writeEnSz)
       with         If (null == $1)
        then                 BKSTMTS {
                LET bram_non_be : (BRAM_PORT (Bit wordAddrSz) (Bit dataSz))
        with     If (#loadFile!LoadFormatFields@."$tag" == $0) then
        Assign bram_non_be <-  mkBRAMCore1($actualNumWords, #False);
        Retv
    else
    If (#loadFile!LoadFormatFields@."$tag" == $1) then
              LET hexfile <- loadFile;
        Assign bram_non_be <-  mkBRAMCore1Load($actualNumWords, #False, #hexfile, #False);
        Retv
    else
    If (#loadFile!LoadFormatFields@."$tag" == $2) then
              LET binfile <- loadFile;
        Assign bram_non_be <-  mkBRAMCore1Load($actualNumWords, #False, #binfile, #True);
        Retv
    else
        Retv
        with         Assign bram =  to_BRAM_PORT_BE(#bram_non_be)
;
        Retv
        else                 BKSTMTS {
            If (#loadFile!LoadFormatFields@."$tag" == $0) then
        Assign bram <-  mkBRAMCore1BE($actualNumWords, #False);
        Retv
    else
    If (#loadFile!LoadFormatFields@."$tag" == $1) then
              LET hexfile <- loadFile;
        Assign bram <-  mkBRAMCore1BELoad($actualNumWords, #False, #hexfile, #False);
        Retv
    else
    If (#loadFile!LoadFormatFields@."$tag" == $2) then
              LET binfile <- loadFile;
        Assign bram <-  mkBRAMCore1BELoad($actualNumWords, #False, #binfile, #True);
        Retv
    else
        Retv
;
        Retv;
       with (BKMod (FIXME'InterfaceName'instance pendingReq :: nil))
       with (BKMod (FIXME'InterfaceName'instance pendingResp :: nil))
       with Register atomicOpWordAddr : Bit wordAddrSz <- $0
       with Register atomicOpData : Bit dataSz <- $0
       with Rule instancePrefix--"performAtomicMemoryOp" :=
        Read atomicOpData_v : Bit dataSz <- atomicOpData;
        Read atomicOpWordAddr_v : Bit wordAddrSz <- atomicOpWordAddr;
        Assert(#pendingReq[$0]$taggedValid.req isAtomicMemOp(#req));
               Call writeData : tvar549 <-  atomicMemOpFunc(#req, #bram, #atomicOpData_v, #req);
        bramput(#req, #atomicOpWordAddr_v, #writeData);
               Write pendingReq[$0] <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "write_en" ::= #req; "atomic_op" ::= #nonAtomicMemOp; "rmw_write" ::= #True  }; "Invalid" ::= $0 };
               Write atomicOpData : Bit dataSz <- #bram;
        Retv (* rule performAtomicMemoryOp *)
       with Rule instancePrefix--"getRespFromCore" :=
        Read atomicOpData_v : Bit dataSz <- atomicOpData;
        Assert(#pendingReq[$0]$taggedValid.req! isAtomicMemOp(#req));
        pendingRespenq(STRUCT { "write" ::= (#req != $0); "data" ::= #req#atomicOpData_v#bram  });
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
        Write pendingReq[$1] <- STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "write_en" ::= #req; "atomic_op" ::= #atomic_op; "rmw_write" ::= #False  }; "Invalid" ::= $0 };
        Retv

       with Method instancePrefix--"canEnq" () : Bool :=
        Ret ! isValid(#pendingReq[$1])

    }). (* mkGenericAtomicBRAMLoad *)

    Definition mkGenericAtomicBRAMLoad := Build_ServerPort atomicMemOpT dataSz wordAddrSz writeEnSz mkGenericAtomicBRAMLoadModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicBRAMLoad.
End mkGenericAtomicBRAMLoad.

Definition performGenericAtomicMemOpOnRegs (regs: Vector numRegs Reg word dataSz) (req: GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz): (ActionValue (GenericAtomicMemResp dataSz)) := 
        LET index : (word (TLog numRegs)) <- (UniBit (Trunc wordAddrSz (TLog#(numRegs) - wordAddrSz)) #req)

                LET resp : (GenericAtomicMemResp dataSz) <- STRUCT { "write" ::= (!= #req $0); "data" ::= $0  }

                If (<= #index  fromInteger((- null $1)))
        then                 BKSTMTS {
                If (== #req $0)
        then                 BKSTMTS {
                Assign resp.data = #regs[#index]
;
        Retv
        else                 If (&& (== #req $'1) ! isAtomicMemOp(#req))
        then                 BKSTMTS {
                Write regs[#index] <- #req
;
        Retv
        else                 If ! isAtomicMemOp(#req)
        then                 BKSTMTS {
                Write regs[#index] <-  emulateWriteEn(#regs[#index], #req, #req)
;
        Retv
        else                 BKSTMTS {
                Call write_data : tvar576 <-  atomicMemOpFunc(#req, #regs[#index], #req, #req)
        with         Write regs[#index] <-  emulateWriteEn(#regs[#index], #write_data, #req)
        with         Assign resp.data = #regs[#index]
;
        Retv;;
        Retv;;
        Retv;
;
        Retv

                Ret #resp

                Ret null

.

Definition performGenericAtomicMemOpOnRegFile (rf: RegFile word rfWordAddrSz word dataSz) (req: GenericAtomicMemReq writeEnSz atomicMemOpT wordAddrSz dataSz): (ActionValue (GenericAtomicMemResp dataSz)) := 
        LET index : (word rfWordAddrSz) <- (UniBit (Trunc wordAddrSz (rfWordAddrSz - wordAddrSz)) #req)

                LET resp : (GenericAtomicMemResp dataSz) <- STRUCT { "write" ::= (!= #req $0); "data" ::= $0  }

                If (== #req $0)
        then                 BKSTMTS {
                Assign resp.data =  rfsub(#index)
;
        Retv
        else                 If (&& (== #req $'1) ! isAtomicMemOp(#req))
        then                 BKSTMTS {
         rfupd(#index, #req)
;
        Retv
        else                 If ! isAtomicMemOp(#req)
        then                 BKSTMTS {
                Call new_data : tvar584 <-  emulateWriteEn( rfsub(#index), #req, #req)
        with  rfupd(#index, #new_data)
;
        Retv
        else                 BKSTMTS {
                Call old_data : tvar585 <-  rfsub(#index)
        with         Call write_data : tvar589 <-  atomicMemOpFunc(#req, #old_data, #req, #req)
        with         Call new_data : tvar592 <-  emulateWriteEn(#old_data, #write_data, #req)
        with  rfupd(#index, #new_data)
        with         Assign resp.data = #old_data
;
        Retv;;
        Retv;;
        Retv;

                Ret #resp

                Ret null

.

Module mkGenericAtomicMemFromRegs.
    Section Section'mkGenericAtomicMemFromRegs.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable numRegs : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable regs: (Vector numRegs (Reg (word dataSz))).
(* FIXME: interface FIFOG subinterface deq *)
(* FIXME: interface FIFOG subinterface first *)
    Let respFIFOenq := MethodSig (FIFOG'enq respFIFO) (t) : Void.
                           Let reqFIFO := mkLFIFOG (instancePrefix--"reqFIFO").
       Let respFIFO := mkBypassFIFOG (instancePrefix--"respFIFO").
    Definition mkGenericAtomicMemFromRegsModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance reqFIFO :: nil))
       with (BKMod (FIXME'InterfaceName'instance respFIFO :: nil))
       with Rule instancePrefix--"performMemReq" :=
               LET req : t = #reqFIFO;
       #reqFIFO;
               Call resp : tvar595 <-  performGenericAtomicMemOpOnRegs(#regs, #req);
        respFIFOenq(#resp);
        Retv (* rule performMemReq *)
    }). (* mkGenericAtomicMemFromRegs *)

    Definition mkGenericAtomicMemFromRegs := Build_ServerPort atomicMemOpT dataSz numRegs wordAddrSz writeEnSz mkGenericAtomicMemFromRegsModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicMemFromRegs.
End mkGenericAtomicMemFromRegs.

Module mkGenericAtomicMemFromRegFile.
    Section Section'mkGenericAtomicMemFromRegFile.
    Variable atomicMemOpT : Kind.
    Variable dataSz : Kind.
    Variable rfWordAddrSz : Kind.
    Variable wordAddrSz : Kind.
    Variable writeEnSz : Kind.
    Variable instancePrefix: string.
    Variable rf: (RegFile (word rfWordAddrSz) (word dataSz)).
(* FIXME: interface FIFOG subinterface deq *)
(* FIXME: interface FIFOG subinterface first *)
    Let respFIFOenq := MethodSig (FIFOG'enq respFIFO) (t) : Void.
                           Let reqFIFO := mkLFIFOG (instancePrefix--"reqFIFO").
       Let respFIFO := mkBypassFIFOG (instancePrefix--"respFIFO").
    Definition mkGenericAtomicMemFromRegFileModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance reqFIFO :: nil))
       with (BKMod (FIXME'InterfaceName'instance respFIFO :: nil))
       with Rule instancePrefix--"performMemReq" :=
               LET req : t = #reqFIFO;
       #reqFIFO;
               Call resp : tvar598 <-  performGenericAtomicMemOpOnRegFile(#rf_v, #req);
        respFIFOenq(#resp);
        Retv (* rule performMemReq *)
    }). (* mkGenericAtomicMemFromRegFile *)

    Definition mkGenericAtomicMemFromRegFile := Build_ServerPort atomicMemOpT dataSz rfWordAddrSz wordAddrSz writeEnSz mkGenericAtomicMemFromRegFileModule%kami (instancePrefix--"request") (instancePrefix--"response").
    End Section'mkGenericAtomicMemFromRegFile.
End mkGenericAtomicMemFromRegFile.

