Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Definition concatReg (r1: Reg word n1) (r2: Reg word n2): r := 
                Ret  _concatReg( asReg(#r1_v),  asReg(#r2_v))

.

Definition concatReg2 (r1: Reg word n1) (r2: Reg word n2): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v))

.

Definition concatReg3 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v))

.

Definition concatReg4 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v))

.

Definition concatReg5 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v))

.

Definition concatReg6 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v))

.

Definition concatReg7 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v))

.

Definition concatReg8 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v))

.

Definition concatReg9 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v))

.

Definition concatReg10 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v))

.

Definition concatReg11 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v))

.

Definition concatReg12 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v))

.

Definition concatReg13 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v))

.

Definition concatReg14 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v))

.

Definition concatReg15 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14) (r15: Reg word n15): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v))

.

Definition concatReg16 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14) (r15: Reg word n15) (r16: Reg word n16): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v))

.

Definition concatReg17 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14) (r15: Reg word n15) (r16: Reg word n16) (r17: Reg word n17): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v))

.

Definition concatReg18 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14) (r15: Reg word n15) (r16: Reg word n16) (r17: Reg word n17) (r18: Reg word n18): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v),  asReg(#r18_v))

.

Definition concatReg19 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14) (r15: Reg word n15) (r16: Reg word n16) (r17: Reg word n17) (r18: Reg word n18) (r19: Reg word n19): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v),  asReg(#r18_v),  asReg(#r19_v))

.

Definition concatReg20 (r1: Reg word n1) (r2: Reg word n2) (r3: Reg word n3) (r4: Reg word n4) (r5: Reg word n5) (r6: Reg word n6) (r7: Reg word n7) (r8: Reg word n8) (r9: Reg word n9) (r10: Reg word n10) (r11: Reg word n11) (r12: Reg word n12) (r13: Reg word n13) (r14: Reg word n14) (r15: Reg word n15) (r16: Reg word n16) (r17: Reg word n17) (r18: Reg word n18) (r19: Reg word n19) (r20: Reg word n20): (Reg (word n)) := 
                Ret  concatReg( asReg(#r1_v),  asReg(#r2_v),  asReg(#r3_v),  asReg(#r4_v),  asReg(#r5_v),  asReg(#r6_v),  asReg(#r7_v),  asReg(#r8_v),  asReg(#r9_v),  asReg(#r10_v),  asReg(#r11_v),  asReg(#r12_v),  asReg(#r13_v),  asReg(#r14_v),  asReg(#r15_v),  asReg(#r16_v),  asReg(#r17_v),  asReg(#r18_v),  asReg(#r19_v),  asReg(#r20_v))

.

