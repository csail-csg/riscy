Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Vector.
Definition grab_left (value: b): a := 
                Call result : tvar822 <-  truncate((>>  pack(#value)  fromInteger((- null null))))

                Ret  unpack(#result)

.

Definition reverse_bytes (value: a): a := 
                LET result_bits : (word sa) <- $0

        LET value_bits <- 

                LET one_byte : (word 8) <- $0

                LET z : (word sb) <- $0

            (BKBlock
      (let limit : nat := valueOf(sa)
       in let instancePrefix : string := instancePrefix--"xx"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let xx := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString xx)
          in ConsInBKModule
        BKSTMTS {
                LET x : nat <- (- $xx (- null $1))
        with LET y <- 
        with         Assign one_byte = #value_bits[#y : (- #y $7)]
        with         Assign z = (BinBit (Concat 8 sa) #one_byte #result_bits)
        with         Assign result_bits =  grab_left(#z)

        (loopM' m')
        end)
        valueOf(sa))))

                Ret  unpack(#result_bits)

.

Definition getSizeOf (value: a): nat := 
                Ret null

.

Definition zExtend (value: word n): (word m) := 
        LET out <- 

                If (== null $0)
        then                 Ret null;
        Retv
        else                 Ret #out[(- null $1) : $0];
        Retv;

.

Definition sExtend (value: word n): (word m) := 
        LET out <- 

                If (== null $0)
        then                 Ret null;
        Retv
        else                 Ret #out[(- null $1) : $0];
        Retv;

.

Definition cExtend (value: b): a := 
                Call out : tvar833 <-  unpack( zExtend( pack(#value)))

                Ret #out

.

Definition zExtendLSB (value: word n): (word m) := 
