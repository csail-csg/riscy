Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Vector.
Require Import RevertingVirtualReg.
Definition (Ehr n t) := (Vector n (Reg t)).

Definition readVEhr (ehr_index: i) (vec_ehr: Vector n Ehr n2 t): (Vector n t) := 
Definition get_ehr_index (e: Ehr n2 t): (Reg t) := 
    #e[#ehr_index]
.

                Ret  readVReg( map(#get_ehr_index, #vec_ehr))

.

Definition writeVEhr (ehr_index: i) (vec_ehr: Vector n Ehr n2 t) (data: Vector n t): Void := 
Definition get_ehr_index (e: Ehr n2 t): (Reg t) := 
    #e[#ehr_index]
.

                Ret  writeVReg( map(#get_ehr_index, #vec_ehr), #data)

        Retv
.

Module mkEhr.
    Section Section'mkEhr.
    Variable n : Kind.
    Variable t : Kind.
    Variable instancePrefix: string.
    Variable initVal: t.
                                   Let port := replicateM (instancePrefix--"port").
       Let register : string := instancePrefix--"register".
       Let readBeforeLaterWrites := replicateM (instancePrefix--"readBeforeLaterWrites").
    Definition mkEhrModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance port :: nil))
       with Register register : t <- $initVal
       with (BKMod (FIXME'InterfaceName'instance readBeforeLaterWrites :: nil))
       with Rule instancePrefix--"canonicalize" :=
        Read register_v : t <- register;
               LET nextVal : t <- #register_v;
           (BKBlock
      (let limit : nat := valueOf(n)
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        BKSTMTS {
                Assign nextVal =  fromMaybe(#nextVal, #port[$i]);

        (loopM' m')
        end)
        valueOf(n))));
               Write register : t <- #nextVal;
        Retv (* rule canonicalize *)
       with         LET _m : (Ehr n t) <- #newVector
       with     (BKBlock
      (let limit : nat := valueOf(n)
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        BKSTMTS {
        Method instancePrefix--"_write" (x : t) : Void :=
        Read register_v : t <- "register";        LET currentVal : t <- #register_v;
    (BKBlock
      (let limit : nat := i
       in let instancePrefix : string := instancePrefix--"j"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let j := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString j)
          in ConsInBKModule
        BKSTMTS {
                Assign currentVal =  fromMaybe(#currentVal, #port[$j]);

        (loopM' m')
        end)
        i)));
        Write readBeforeLaterWrites[$i] <- #False;
 FIXME$port[i]wset(#readBeforeLaterWrites[$i]#x#currentVal);
        Retv

        with Method instancePrefix--"_read" () : t :=
        Read register_v : t <- "register";        LET currentVal : t <- #register_v;
    (BKBlock
      (let limit : nat := i
       in let instancePrefix : string := instancePrefix--"j"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let j := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString j)
          in ConsInBKModule
        BKSTMTS {
                Assign currentVal =  fromMaybe(#currentVal, #port[$j]);

        (loopM' m')
        end)
        i)));
        LET genConstraints : Bool <- #True;
    (BKBlock
      (let limit : nat := valueOf(n)
       in let instancePrefix : string := instancePrefix--"j"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let j := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString j)
          in ConsInBKModule
        BKSTMTS {
                Assign genConstraints = (#genConstraints && #readBeforeLaterWrites[$j]);

        (loopM' m')
        end)
        valueOf(n))));
        Ret #genConstraints#currentValnull

        with         Assign _m[i] = null

        (loopM' m')
        end)
        valueOf(n))))
       with         Ret #_m
    }). (* mkEhr *)

    Definition mkEhr := Build_Vector n t mkEhrModule%kami.
    End Section'mkEhr.
End mkEhr.

Module mkEhrU.
    Section Section'mkEhrU.
    Variable n : Kind.
    Variable t : Kind.
    Variable instancePrefix: string.
               Let _m := mkEhr (instancePrefix--"_m").
    Definition mkEhrUModule :=
        (BKMODULE {
           (BKMod (FIXME'InterfaceName'instance _m :: nil))
       with         Ret #_m
    }). (* mkEhrU *)

    Definition mkEhrU := Build_Vector n t mkEhrUModule%kami.
    End Section'mkEhrU.
End mkEhrU.

