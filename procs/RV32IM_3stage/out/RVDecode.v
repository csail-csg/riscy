Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import VecN.
Require Import Opcodes.
Require Import RVTypes.
Require Import Vector.
Require Import DefaultValue.
Definition toExecFuncRV32I (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncPriv (inst: Instruction): (Maybe ExecFunc) := 
        LET instFields <- 

                Ret null

.

Definition toExecFuncRV32M (hasDiv: bool) (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV32A (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV32F (hasDiv: bool) (hasSqrt: bool) (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV32D (hasDiv: bool) (hasSqrt: bool) (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV64I (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV64M (hasDiv: bool) (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV64A (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV64F (hasDiv: bool) (hasSqrt: bool) (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition toExecFuncRV64D (hasDiv: bool) (hasSqrt: bool) (inst: Instruction): (Maybe ExecFunc) := 
                Ret null

.

Definition decodeInst (isRV64: bool) (hasM: bool) (hasA: bool) (hasF: bool) (hasD: bool) (inst: Instruction): (Maybe RVDecodedInst) := 
Definition fold_op (x: Maybe t) (y: Maybe t): (Maybe t) := 
                Ret  isValid(#x)#x#y

.

                Call decoderResults : tvar1543 <-  vec6(#isRV64 toExecFuncRV64I(#inst) toExecFuncRV32I(#inst), #hasM#isRV64 toExecFuncRV64M(#True, #inst) toExecFuncRV32M(#True, #inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }, #hasA#isRV64 toExecFuncRV64A(#inst) toExecFuncRV32A(#inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }, #hasF#isRV64 toExecFuncRV64F(#True, #True, #inst) toExecFuncRV32F(#True, #True, #inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }, #hasD#isRV64 toExecFuncRV64D(#True, #True, #inst) toExecFuncRV32D(#True, #True, #inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 },  toExecFuncPriv(#inst))

                Call execFunc : tvar1546 <-  fold(#fold_op, #decoderResults)

                If #execFunc$taggedValid.validExecFunc
        then                 BKSTMTS {
        LET instType <- 
        with         Ret STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "execFunc" ::= #validExecFunc; "imm" ::= #instType; "rs1" ::= #instType; "rs2" ::= #instType; "rs3" ::= #instType; "dst" ::= #instType; "inst" ::= #inst  }; "Invalid" ::= $0 }
;
        Retv
        else                 BKSTMTS {
                Ret STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }
;
        Retv;

.

Definition getImmediate (imm: ImmType) (inst: Instruction): (Maybe (word xlen)) := 
        LET immI <- 

        LET immS <- 

        LET immSB <- 

        LET immU <- 

        LET immUJ <- 

        LET immZ <- 

                Ret null

.

Definition getMinPriv (inst: Instruction): (word 2) := 
                Ret (==  getInstFields(#inst) #System)#inst[$29 : $28]#prvU

.

