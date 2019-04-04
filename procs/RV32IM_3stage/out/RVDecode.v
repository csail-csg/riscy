Require Import Bool String List Arith.
Require Import Omega.
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
(* * interface RVDecodeInternal *)
Record RVDecodeInternal := {
    RVDecodeInternal'modules: Modules;
    RVDecodeInternal'toExecFuncRV32I : string;
    RVDecodeInternal'toExecFuncPriv : string;
    RVDecodeInternal'toExecFuncRV32M : string;
    RVDecodeInternal'toExecFuncRV32A : string;
    RVDecodeInternal'toExecFuncRV32F : string;
    RVDecodeInternal'toExecFuncRV32D : string;
    RVDecodeInternal'toExecFuncRV64I : string;
    RVDecodeInternal'toExecFuncRV64M : string;
    RVDecodeInternal'toExecFuncRV64A : string;
    RVDecodeInternal'toExecFuncRV64F : string;
    RVDecodeInternal'toExecFuncRV64D : string;
}.

Module module'mkRVDecodeInternal.
    Section Section'mkRVDecodeInternal.
    Variable instancePrefix: string.
                                                       Let getInstFields := mkGetInstFields (instancePrefix--"getInstFields").
    Let getInstFieldsgetInstFields : string := (GetInstFields'getInstFields getInstFields).
    Definition mkRVDecodeInternalModule: Modules :=
         (BKMODULE {
           (BKMod (GetInstFields'modules getInstFields :: nil))
       with Method instancePrefix--"toExecFuncRV32I" (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method instancePrefix--"toExecFuncPriv" (inst : Instruction) : (Maybe ExecFunc) :=
CallM instFields : InstructionFields <-  getInstFieldsgetInstFields(#inst);
        Ret null

       with Method2 instancePrefix--"toExecFuncRV32M" (hasDiv : Bool) (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method instancePrefix--"toExecFuncRV32A" (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method3 instancePrefix--"toExecFuncRV32F" (hasDiv : Bool) (hasSqrt : Bool) (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method3 instancePrefix--"toExecFuncRV32D" (hasDiv : Bool) (hasSqrt : Bool) (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method instancePrefix--"toExecFuncRV64I" (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method2 instancePrefix--"toExecFuncRV64M" (hasDiv : Bool) (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method instancePrefix--"toExecFuncRV64A" (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method3 instancePrefix--"toExecFuncRV64F" (hasDiv : Bool) (hasSqrt : Bool) (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

       with Method3 instancePrefix--"toExecFuncRV64D" (hasDiv : Bool) (hasSqrt : Bool) (inst : Instruction) : (Maybe ExecFunc) :=
        Ret null

    }). (* mkRVDecodeInternal *)

(* Module mkRVDecodeInternal type Module#(RVDecodeInternal) return type RVDecodeInternal *)
    Definition mkRVDecodeInternal := Build_RVDecodeInternal mkRVDecodeInternalModule%kami (instancePrefix--"toExecFuncPriv") (instancePrefix--"toExecFuncRV32A") (instancePrefix--"toExecFuncRV32D") (instancePrefix--"toExecFuncRV32F") (instancePrefix--"toExecFuncRV32I") (instancePrefix--"toExecFuncRV32M") (instancePrefix--"toExecFuncRV64A") (instancePrefix--"toExecFuncRV64D") (instancePrefix--"toExecFuncRV64F") (instancePrefix--"toExecFuncRV64I") (instancePrefix--"toExecFuncRV64M").
    End Section'mkRVDecodeInternal.
End module'mkRVDecodeInternal.

Definition mkRVDecodeInternal := module'mkRVDecodeInternal.mkRVDecodeInternal.

(* * interface RVDecode *)
Record RVDecode := {
    RVDecode'modules: Modules;
    RVDecode'decodeInst : string;
    RVDecode'getImmediate : string;
    RVDecode'getMinPriv : string;
}.

Module module'mkRVDecode.
    Section Section'mkRVDecode.
    Variable instancePrefix: string.
                Definition fold_op (x: Maybe t) (y: Maybe t): (Maybe t) := 
                Ret  isValid(#x)#x#y

.

               Let getInstFields := mkGetInstFields (instancePrefix--"getInstFields").
       Let toInstType := mkToInstType (instancePrefix--"toInstType").
       Let decodeInternal := mkRVDecodeInternal (instancePrefix--"decodeInternal").
    Let toInstTypetoInstType : string := (ToInstType'toInstType toInstType).
    Definition mkRVDecodeModule: Modules :=
         (BKMODULE {
           (BKMod (GetInstFields'modules getInstFields :: nil))
       with (BKMod (ToInstType'modules toInstType :: nil))
       with (BKMod (RVDecodeInternal'modules decodeInternal :: nil))
       with Method6 instancePrefix--"decodeInst" (isRV64 : Bool) (hasM : Bool) (hasA : Bool) (hasF : Bool) (hasD : Bool) (inst : Instruction) : (Maybe RVDecodedInst) :=
        Call decoderResults : tvar1581 <-  vec6(#isRV64 decodeInternaltoExecFuncRV64I(#inst) decodeInternaltoExecFuncRV32I(#inst), #hasM#isRV64 decodeInternaltoExecFuncRV64M(True, #inst) decodeInternaltoExecFuncRV32M(True, #inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }, #hasA#isRV64 decodeInternaltoExecFuncRV64A(#inst) decodeInternaltoExecFuncRV32A(#inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }, #hasF#isRV64 decodeInternaltoExecFuncRV64F(True, True, #inst) decodeInternaltoExecFuncRV32F(True, True, #inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 }, #hasD#isRV64 decodeInternaltoExecFuncRV64D(True, True, #inst) decodeInternaltoExecFuncRV32D(True, True, #inst)STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 },  decodeInternaltoExecFuncPriv(#inst));
        Call execFunc : tvar1584 <-  fold(#fold_op, #decoderResults);
        If #execFunc$taggedValid.validExecFunc
        then                 BKSTMTS {
        CallM instType : InstType <-  toInstTypetoInstType(#inst);
                Ret STRUCT {  "$tag" ::= $0; "Valid" ::= STRUCT { "execFunc" ::= (#validExecFunc); "imm" ::= (#instType); "rs1" ::= (#instType); "rs2" ::= (#instType); "rs3" ::= (#instType); "dst" ::= (#instType); "inst" ::= (#inst)  }; "Invalid" ::= $0 };
;
        Retv
        else                 BKSTMTS {
                Ret STRUCT {  "$tag" ::= $1; "Invalid" ::= $0; "Valid" ::= $0 };
;
        Retv;

       with Method2 instancePrefix--"getImmediate" (imm : ImmType) (inst : Instruction) : (Maybe (Bit XLEN)) :=
CallM immI : (Bit XLEN) <-  signExtend(#inst$[31:20]@32);
CallM immS : (Bit XLEN) <-  signExtend(castBits _ _ _ _ (BinBit (Concat tvar1595 tvar1596) #inst$[31:25]@32 #inst$[11:7]@32));
CallM immSB : (Bit XLEN) <-  signExtend(castBits _ _ _ _ (BinBit (Concat 1 1) #inst@[$31] #inst@[$7]));
CallM immU : (Bit XLEN) <-  signExtend(castBits _ _ _ _ (BinBit (Concat tvar1597 12) #inst$[31:12]@32 $0));
CallM immUJ : (Bit XLEN) <-  signExtend(castBits _ _ _ _ (BinBit (Concat 1 tvar1598) #inst@[$31] #inst$[19:12]@32));
CallM immZ : (Bit XLEN) <-  zeroExtend(#inst$[19:15]@32);
        Ret null

       with Method instancePrefix--"getMinPriv" (inst : Instruction) : (Bit 2) :=
        Ret ( getInstFieldsgetInstFields(#inst) == System)#inst$[29:28]@32#prvU

    }). (* mkRVDecode *)

(* Module mkRVDecode type Module#(RVDecode) return type RVDecode *)
    Definition mkRVDecode := Build_RVDecode mkRVDecodeModule%kami (instancePrefix--"decodeInst") (instancePrefix--"getImmediate") (instancePrefix--"getMinPriv").
    End Section'mkRVDecode.
End module'mkRVDecode.

Definition mkRVDecode := module'mkRVDecode.mkRVDecode.

