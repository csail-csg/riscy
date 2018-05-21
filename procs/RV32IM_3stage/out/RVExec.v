Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import RVDecode.
Require Import RVTypes.
Require Import Vector.
Require Import RVAlu.
Require Import RVControl.
Require Import RVMemory.
Definition ExecResultFields (xlen : nat) := (STRUCT {
    "data" :: (Bit xlen);
    "addr" :: (Bit xlen);
    "taken" :: Bool;
    "nextPc" :: (Bit xlen)}).
Definition ExecResult  (xlen : nat) := Struct (ExecResultFields xlen).

Definition execRef (dInst: RVDecodedInst) (rVal1: word xlen) (rVal2: word xlen) (pc: word xlen): (ExecResult xlen) := 
                LET data : (word xlen) <- $0

                LET addr : (word xlen) <- $0

                LET pcPlus4 : (word xlen) <- (+ #pc $4)

                LET taken : bool <- #False

                LET nextPc : (word xlen) <- #pcPlus4

        LET imm <- 

            If (#dInst!ExecFuncFields@."$tag" == $0) then
              LET aluInst <- dInst.execFunc;
        BKSTMTS {
                Assign data =  execAluInst(#aluInst, #rVal1, #rVal2, #imm, #pc)
;
        Retv
    else
    If (#dInst!ExecFuncFields@."$tag" == $1) then
              LET brFunc <- dInst.execFunc;
        BKSTMTS {
                Assign data = #pcPlus4
        with         Assign addr =  brAddrCalc(#brFunc, #pc, #rVal1,  fromMaybe(null, #imm))
        with         Assign taken =  aluBr(#brFunc, #rVal1, #rVal2)
        with         Assign nextPc = #taken#addr#pcPlus4
;
        Retv
    else
    If (#dInst!ExecFuncFields@."$tag" == $2) then
              LET memInst <- dInst.execFunc;
        BKSTMTS {
                Assign data = #rVal2
        with         Assign addr =  addrCalc(#rVal1, #imm)
;
        Retv
    else
    If (#dInst!ExecFuncFields@."$tag" == $6) then
              LET systemInst <- dInst.execFunc;
        BKSTMTS {
                Assign data =  fromMaybe(#rVal1, #imm)
;
        Retv
    else
        Retv

                Ret STRUCT { "data" ::= #data; "addr" ::= #addr; "taken" ::= #taken; "nextPc" ::= #nextPc  }

.

Definition alu (func: AluFunc) (w: bool) (a: word xlen) (b: word xlen): (word xlen) := 
                If (== null $32)
        then                 BKSTMTS {
                Assign w = #True
;
        Retv

                If #w
        then                 BKSTMTS {
                Assign a = (== #func #AluSra) signExtend(#a[$31 : $0]) zeroExtend(#a[$31 : $0])
        with         Assign b =  zeroExtend(#b[$31 : $0])
;
        Retv

        LET shamt : (word 6) <- (UniBit (Trunc xlen (6 - xlen)) #b)

                If #w
        then                 BKSTMTS {
                Assign shamt = (BinBit (Concat 1 tvar1606) $1'b0 #shamt[$4 : $0])
;
        Retv

                LET res : (word xlen) <- null

                If #w
        then                 BKSTMTS {
                Assign res =  signExtend(#res[$31 : $0])
;
        Retv

                Ret #res

.

Definition aluBr (brFunc: BrFunc) (a: word xlen) (b: word xlen): bool := 
                LET brTaken : bool <- null

                Ret #brTaken

.

Definition brAddrCalc (brFunc: BrFunc) (pc: word xlen) (val: word xlen) (imm: word xlen): (word xlen) := 
                LET targetAddr : (word xlen) <- null

                Ret #targetAddr

.

Definition basicExec (dInst: RVDecodedInst) (rVal1: word xlen) (rVal2: word xlen) (pc: word xlen): (ExecResult xlen) := 
                LET pcPlus4 : (word xlen) <- (+ #pc $4)

                LET data : (word xlen) <- $0

                LET addr : (word xlen) <- $0

                LET taken : bool <- #False

                LET nextPc : (word xlen) <- #pcPlus4

        LET imm <- 

                If #dInst$taggedEF_Mem.*
        then                 BKSTMTS {
                If ! isValid(#imm)
        then                 BKSTMTS {
                Assign imm = STRUCT {  "$tag" ::= $0; "Valid" ::= $0; "Invalid" ::= $0 }
;
        Retv
;
        Retv

                LET aluVal1 : (word xlen) <- #rVal1

                LET aluVal2 : (word xlen) <- #imm$taggedValid.validImm#validImm#rVal2

                If #dInst$taggedEF_Alu.aluInst
        then                 BKSTMTS {
            If (#aluInst!AluFuncFields@."$tag" == $16) then
        Assign aluVal1 = #pc;
        Retv
    else
    If (#aluInst!AluFuncFields@."$tag" == $24) then
        Assign aluVal1 = $0;
        Retv
    else
        Retv
;
        Retv

                LET aluF : AluFunc <- #dInst$taggedEF_Alu.aluInst#aluInst#AluAdd

                LET w : bool <- #dInst$taggedEF_Alu.aluInst#aluInst#False

        LET aluResult <- 

                If #dInst$taggedEF_Br.brFunc
        then                 BKSTMTS {
                Assign taken =  aluBr(#brFunc, #rVal1, #rVal2)
        with         If #taken
        then                 BKSTMTS {
                Assign nextPc =  brAddrCalc(#brFunc, #pc, #rVal1,  fromMaybe(null, #imm))
;
        Retv
;
        Retv

                Assign data = null

                Assign addr = null

                Ret STRUCT { "data" ::= #data; "addr" ::= #addr; "taken" ::= #taken; "nextPc" ::= #nextPc  }

.

Definition gatherLoad (byteSel: word TLog TDiv xlen 8) (size: RVMemSize) (isUnsigned: bool) (data: word xlen): (word xlen) := 
Definition extend:  := 
    #isUnsigned#zeroExtend#signExtend
.

                LET bitsToShiftBy : word tvar1603 = (BinBit (Concat TLog#(TDiv#(xlen, 8)) 3) #byteSel $3'b0)

                Assign data = (>> #data #bitsToShiftBy)

                Assign data = null

                Ret #data

.

Definition scatterStore (byteSel: DataByteSel) (size: RVMemSize) (data: word xlen): (Tuple2 DataByteEn (word xlen)) := 
