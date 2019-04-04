Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Definition concatReg (r1: Reg Bit n1) (r2: Reg Bit n2): r := 
                Ret  _concatReg( asReg(#r1_v),  asReg(#r2_v))

.

Definition concatReg2 (r1: Reg Bit n1) (r2: Reg Bit n2): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v))

.

Definition concatReg3 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v))

.

Definition concatReg4 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v))

.

Definition concatReg5 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v))

.

Definition concatReg6 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v))

.

Definition concatReg7 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v))

.

Definition concatReg8 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v))

.

Definition concatReg9 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v))

.

Definition concatReg10 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v))

.

Definition concatReg11 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v))

.

Definition concatReg12 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v))

.

Definition concatReg13 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v))

.

Definition concatReg14 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v))

.

Definition concatReg15 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14) (r15: Reg Bit n15): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v))

.

Definition concatReg16 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14) (r15: Reg Bit n15) (r16: Reg Bit n16): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v))

.

Definition concatReg17 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14) (r15: Reg Bit n15) (r16: Reg Bit n16) (r17: Reg Bit n17): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v))

.

Definition concatReg18 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14) (r15: Reg Bit n15) (r16: Reg Bit n16) (r17: Reg Bit n17) (r18: Reg Bit n18): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v),  asReg(#r18_v))

.

Definition concatReg19 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14) (r15: Reg Bit n15) (r16: Reg Bit n16) (r17: Reg Bit n17) (r18: Reg Bit n18) (r19: Reg Bit n19): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v),  asReg(#r18_v),  asReg(#r19_v))

.

Definition concatReg20 (r1: Reg Bit n1) (r2: Reg Bit n2) (r3: Reg Bit n3) (r4: Reg Bit n4) (r5: Reg Bit n5) (r6: Reg Bit n6) (r7: Reg Bit n7) (r8: Reg Bit n8) (r9: Reg Bit n9) (r10: Reg Bit n10) (r11: Reg Bit n11) (r12: Reg Bit n12) (r13: Reg Bit n13) (r14: Reg Bit n14) (r15: Reg Bit n15) (r16: Reg Bit n16) (r17: Reg Bit n17) (r18: Reg Bit n18) (r19: Reg Bit n19) (r20: Reg Bit n20): (Reg (Bit n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v),  asReg(#r18_v),  asReg(#r19_v),  asReg(#r20_v))

.

