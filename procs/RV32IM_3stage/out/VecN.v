Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Vector.
Definition vec1 (v0: element_t): (Vector 1 element_t) := 
                Ret  cons(#v0, #nil)

.

Definition vec2 (v0: element_t) (v1: element_t): (Vector 2 element_t) := 
                Ret  cons(#v1,  cons(#v0, #nil))

.

Definition vec3 (v0: element_t) (v1: element_t) (v2: element_t): (Vector 3 element_t) := 
                Ret  cons(#v2,  cons(#v1,  cons(#v0, #nil)))

.

Definition vec4 (v0: element_t) (v1: element_t) (v2: element_t) (v3: element_t): (Vector 4 element_t) := 
                Ret  cons(#v3,  cons(#v2,  cons(#v1,  cons(#v0, #nil))))

.

Definition vec5 (v0: element_t) (v1: element_t) (v2: element_t) (v3: element_t) (v4: element_t): (Vector 5 element_t) := 
                Ret  cons(#v4,  cons(#v3,  cons(#v2,  cons(#v1,  cons(#v0, #nil)))))

.

Definition vec6 (v0: element_t) (v1: element_t) (v2: element_t) (v3: element_t) (v4: element_t) (v5: element_t): (Vector 6 element_t) := 
                Ret  cons(#v5,  cons(#v4,  cons(#v3,  cons(#v2,  cons(#v1,  cons(#v0, #nil))))))

.

