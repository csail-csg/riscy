Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Vector#(len, element_type) *)
Record Vector (element_type : Kind) (len : nat) := {
    Vector'interface: Modules;
}.

Definition genWith (func: Function nat element_type): (Vector len element_type) := 
Definition genWithRec (vect: Vector len element_type) (i: nat): (Vector len element_type) := 
                If (bitlt $i null)
        then                 Ret  genWithRec( $vecupdate(#vect, $i,  func($i)), (+ $i $1));
        Retv
        else                 Ret #vect;
        Retv;

.

                Ret  genWithRec( $vecnew(null), $0)

.

Definition newVector: (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                Ret null

.

                Ret  genWith(#elt)

.

Definition genVector: (Vector len nat) := 
Definition elt (xi: nat): nat := 
                Ret $xi

.

                Ret  genWith(#elt)

.

Definition replicate (v: element_type): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #v

.

                Ret  genWith(#elt)

.

Definition cons (v: element_type) (vect: Vector len element_type): (Vector len_plus_1 element_type) := 
Definition elt (xi: nat): element_type := 
                If (== $xi $0)
        then                 Ret #v;
        Retv
        else                 Ret #vect[(- $xi $1)];
        Retv;

.

                Ret  genWith(#elt)

.

Definition nil: (Vector 0 element_type) := 
     newVector()
.

Definition append (vecta: Vector lena element_type) (vectb: Vector lenb element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                If (bitlt $xi null)
        then                 Ret #vecta[$xi];
        Retv
        else                 Ret #vectb[(- $xi null)];
        Retv;

.

                Ret  genWith(#elt)

.

Definition concat (vectofvects: Vector m Vector n element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                LET vectnum : nat <- (/ $xi null)

                LET eltnum : nat <- (% $xi null)

                Ret #vectofvects[$vectnum][$eltnum]

.

                Ret  genWith(#elt)

.

Definition head (v: Vector len element_type): element_type := 
                Ret #v[$0]

.

Definition tail (v: Vector len element_type): element_type := 
                Ret #v[(- null $1)]

.

Definition init (v: Vector vsize1 element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #v[$xi]

.

                Ret  genWith(#elt)

.

Definition take (v: Vector vsize1 element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #v[$xi]

.

                Ret  genWith(#elt)

.

Definition drop (v: Vector vsize1 element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #v[(- (+ $xi null) null)]

.

                Ret  genWith(#elt)

.

Definition takeTail (v: Vector vsize1 element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #v[(- (+ $xi null) null)]

.

                Ret  genWith(#elt)

.

Definition takeAt (startPos: nat) (vect: Vector vsize1 element_type): (Vector vsize element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #vect[(- $xi $startPos)]

.

                Ret  genWith(#elt)

.

Definition map (func: Function a_type b_type) (vect: Vector vsize a_type): (Vector vsize b_type) := 
Definition funci (i: nat): b_type := 
                Ret  func(#vect[$i])

.

                Ret  genWith(#funci)

.

Definition rotate (vect: Vector len element_type): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #vect[(% (+ $xi $1) null)]

.

                Ret  genWith(#elt)

.

Definition rotateR (vect: Vector len element_type): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #vect[(% (- $xi $1) null)]

.

                Ret  genWith(#elt)

.

Definition rotateBy (vect: Vector len element_type) (n: nat): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #vect[(% (+ $xi $n) null)]

.

                Ret  genWith(#elt)

.

Definition shiftInAt0 (vect: Vector len element_type) (new_elt: element_type): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                If (== $xi $0)
        then                 Ret #new_elt;
        Retv
        else                 Ret #vect[(- $xi $1)];
        Retv;

.

                Ret  genWith(#elt)

.

Definition shiftInAtN (vect: Vector len element_type) (new_elt: element_type): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                If (== $xi (- null $1))
        then                 Ret #new_elt;
        Retv
        else                 Ret #vect[(+ $xi $1)];
        Retv;

.

                Ret  genWith(#elt)

.

Definition shiftOutFrom0 (new_elt: element_type) (vect: Vector len element_type) (amount: nat): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                If (>= $xi (- null $amount))
        then                 Ret #new_elt;
        Retv
        else                 Ret #vect[(+ $xi $amount)];
        Retv;

.

                Ret  genWith(#elt)

.

Definition shiftOutFromN (new_elt: element_type) (vect: Vector len element_type) (amount: nat): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                If (bitlt $xi $amount)
        then                 Ret #new_elt;
        Retv
        else                 Ret #vect[(- $xi $amount)];
        Retv;

.

                Ret  genWith(#elt)

.

Definition reverse (vect: Vector len element_type): (Vector len element_type) := 
Definition elt (xi: nat): element_type := 
                Ret #vect[(- (- null $xi) $1)]

.

                Ret  genWith(#elt)

.

Definition transpose (vectofvects: Vector m Vector n element_type): (Vector m (Vector n element_type)) := 
Definition outer_elt (xi: nat): (Vector n element_type) := 
Definition inner_elt (yi: nat): element_type := 
                Ret #vectofvects[$yi][$xi]

.

                Ret  genWith(#inner_elt)

.

                Ret  genWith(#outer_elt)

.

Definition foldr (func: Function a_type Function b_type b_type) (seed: b_type) (vect: Vector vsize a_type): b_type := 
Definition foldrec (i: nat) (v: b_type): b_type := 
                If (bitlt $i null)
        then                 Ret  foldrec((+ $i $1),  func(#vect[(- (- null $i) $1)], #v));
        Retv
        else                 Ret #v;
        Retv;

.

                Ret  foldrec($0, #seed)

.

Definition foldl (func: Function b_type Function a_type b_type) (seed: b_type) (vect: Vector vsize a_type): b_type := 
Definition foldrec (i: nat) (v: b_type): b_type := 
                If (bitlt $i null)
        then                 Ret  foldrec((+ $i $1),  func(#v, #vect[$i]));
        Retv
        else                 Ret #v;
        Retv;

.

                LET result : b_type <- #seed

                Ret  foldrec($0, #seed)

.

Definition fold (func: Function a_type Function a_type b_type) (vect: Vector vsize a_type): a_type := 
Definition recursive (lb: nat) (rb: nat): b_type := 
                If (== $lb $rb)
        then                 Ret #vect[$lb];
        Retv
        else                 If (== $lb (- $rb $1))
        then                 Ret  func(#vect[$lb], #vect[$rb]);
        Retv
        else                 BKSTMTS {
                LET midpoint : nat <- (+ $lb (+ (- $rb $lb) (/ $1 $2)))
        with LET v0 <- 
        with LET v1 <- 
        with         Ret  func(#v0, #v2)
;
        Retv;;
        Retv;

.

                Ret  recursive($0, (- null $1), #seed)

.

Definition foldr1 (func: Function a_type Function a_type a_type) (vect: Vector vsize a_type): a_type := 
        LET subvec <- 

                Ret  foldr(#func,  tail(#vect), #subvec)

.

Definition foldl1 (func: Function a_type Function a_type a_type) (vect: Vector vsize a_type): a_type := 
        LET subvec <- 

                Ret  foldl(#func,  head(#vect), #subvec)

.

Definition elem (needle: element_type) (vect: Vector vsize element_type): bool := 
Definition found (f: bool) (elt: element_type): bool := 
                Ret (|| #f (== #elt #needle))

.

                Ret  foldl(#found, #False, #vect)

.

Definition any (pred: Function element_type bool) (vect: Vector vsize element_type): bool := 
Definition anypred (f: bool) (elt: element_type): bool := 
                Ret (|| #f  pred(#elt))

.

                Ret  foldl(#anypred, #False, #vect)

.

Definition all (pred: Function element_type bool) (vect: Vector vsize element_type): bool := 
Definition allelts (f: bool) (elt: element_type): bool := 
                Ret (&& #f  pred(#elt))

.

                Ret  foldl(#allelts, #True, #vect)

.

Definition vector (vect: Vector vsize bool): bool := 
Definition anyelt (f: bool) (g: bool): bool := 
                Ret (|| #f #g)

.

                Ret  foldl(#anyelt, #False, #vect)

.

Definition vectand (vect: Vector vsize bool): bool := 
Definition allelts (f: bool) (g: bool): bool := 
                Ret (&& #f #g)

.

                Ret  foldl(#allelts, #False, #vect)

.

Definition countElem (needle: element_type) (vect: Vector vsize element_type): (UInt logv1) := 
Definition countelt (sum: UInt logv1) (elt: element_type): (UInt logv1) := 
                Ret (+ #sum (== #needle #elt)$1$0)

.

                Ret  foldl(#countelt, $0, #vect)

.

Definition countIf (pred: Function element_type bool) (vect: Vector vsize element_type): (UInt logv1) := 
Definition countelt (sum: UInt logv1) (elt: element_type): (UInt logv1) := 
                Ret (+ #sum  pred(#elt)$1$0)

.

                Ret  foldl(#countelt, $0, #vect)

.

Definition find (pred: Function element_type bool) (vect: Vector vsize element_type): (Maybe element_type) := 
Definition findelt (found: Maybe element_type) (elt: element_type): (Maybe element_type) := 
            If (#found!MaybeFields@."$tag" == $1) then
        Ret  pred(#elt) Valid(#elt)#Invalid;
        Retv
    else
    If (#found!MaybeFields@."$tag" == $0) then
              LET x <- found;
        Ret #found;
        Retv
    else
        Retv

.

                Ret  foldl(#findelt, #Invalid, #vect)

.

Definition findElem (needle: element_type) (vect: Vector vsize element_type): (Maybe (UInt logv)) := 
Definition findelt (found: Maybe UInt logv) (i: nat): (Maybe (UInt logv)) := 
            If (#found!MaybeFields@."$tag" == $1) then
        Ret (== #vect[$i] #needle) Valid( fromInteger($i))#Invalid;
        Retv
    else
    If (#found!MaybeFields@."$tag" == $0) then
              LET x <- found;
        Ret #found;
        Retv
    else
        Retv

.

        LET indices <- 

                Ret  foldl(#findelt, #Invalid, #indices)

.

Definition findIndex (pred: Function element_type bool) (vect: Vector vsize element_type): (Maybe (UInt logv)) := 
Definition findelt (found: Maybe UInt logv) (i: nat): (Maybe (UInt logv)) := 
            If (#found!MaybeFields@."$tag" == $1) then
        Ret  pred(#vect[$i]) Valid( fromInteger($i))#Invalid;
        Retv
    else
    If (#found!MaybeFields@."$tag" == $0) then
              LET x <- found;
        Ret #found;
        Retv
    else
        Retv

.

        LET indices <- 

                Ret  foldl(#findelt, #Invalid, #indices)

.

Definition rotateBitsBy (bvect: word n) (rotatebits: UInt logn): (word n) := 
Definition elt (xi: nat): (word 1) := 
                Ret #bits[(% (+  fromInteger($xi) #rotatebits)  fromInteger(null))]

.

        LET bits <- 

        LET rotated <- 

                Ret  pack(#rotated)

.

Definition countOnesAlt (bvect: word n): (UInt logn1) := 
Definition countone (sum: UInt logn1) (b: word 1): (UInt logn1) := 
                Ret (+ #sum (== #b $1)$1$0)

.

        LET bits <- 

                Ret  foldl(#countone, $0, #bits)

.

Definition readVReg (vrin: Vector n Reg a): (Vector n a) := 
Definition readreg (r: Reg a): a := 
                Ret #r_v

.

                Ret  map(#readreg, #vrin)

.

Definition writeVReg (vr: Vector n Reg a) (vdin: Vector n a): Void := 
Definition loop (i: nat): Void := 
                If (bitlt $i null)
        then                 BKSTMTS {
                Write vr[$i] <- #vdin[$i]
        with  loop((+ $i $1))
;
        Retv

        Retv
.

         loop($0)

        Retv
.

Definition zip (vecta: Vector vsize a_type) (vectb: Vector vsize b_type): (Vector vsize (Tuple2 a_type b_type)) := 
Definition combine (i: nat): (Tuple2 a_type b_type) := 
                Ret  tuple2(#vecta[$i], #vectb[$i])

.

                Ret  genWith(#combine)

.

Definition zip3 (vecta: Vector vsize a_type) (vectb: Vector vsize b_type) (vectc: Vector vsize c_type): (Vector vsize (Tuple3 a_type b_type c_type)) := 
Definition combine (i: nat): (Tuple3 a_type b_type c_type) := 
                Ret  tuple3(#vecta[$i], #vectb[$i], #vectc[$i])

.

                Ret  genWith(#combine)

.

Definition zip4 (vecta: Vector vsize a_type) (vectb: Vector vsize b_type) (vectc: Vector vsize c_type) (vectd: Vector vsize d_type): (Vector vsize (Tuple4 a_type b_type c_type d_type)) := 
Definition combine (i: nat): (Tuple4 a_type b_type c_type d_type) := 
                Ret  tuple4(#vecta[$i], #vectb[$i], #vectc[$i], #vectd[$i])

.

                Ret  genWith(#combine)

.

Definition zipAny (vect1: Vector m a_type) (vect2: Vector n b_type): (Vector vsize (Tuple2 a_type b_type)) := 
        LET as <- 

        LET bs <- 

                Ret  zip(#as, #bs)

.

Definition unzip (vectab: Vector vsize Tuple2 a_type b_type): (Tuple2 (Vector vsize a_type) (Vector vsize b_type)) := 
                Ret  tuple2( map(#tpl_1, #vectab),  map(#tpl_2, #vectab))

.

Definition zipWith (func: Function a_type Function b_type c_type) (vecta: Vector vsize a_type) (vectb: Vector vsize b_type): (Vector vsize c_type) := 
Definition funci (i: nat): c_type := 
                Ret  func(#vecta[$i], #vectb[$i])

.

                Ret  genWith(#funci)

.

Definition zipWithAny (func: Function a_type Function b_type c_type) (vecta: Vector m a_type) (vectb: Vector n b_type): (Vector vsize c_type) := 
Definition funci (i: nat): c_type := 
                Ret  func(#vecta[$i], #vectb[$i])

.

                Ret  genWith(#funci)

.

Definition zipWith3 (func: Function a_type Function b_type Function c_type d_type) (vecta: Vector vsize a_type) (vectb: Vector vsize b_type) (vectc: Vector vsize c_type): (Vector vsize d_type) := 
Definition funci (i: nat): d_type := 
                Ret  func(#vecta[$i], #vectb[$i], #vectc[$i])

.

                Ret  genWith(#funci)

.

Definition zipWithAny3 (func: Function a_type Function b_type Function c_type d_type) (vecta: Vector m a_type) (vectb: Vector n b_type) (vectc: Vector o c_type): (Vector vsize d_type) := 
Definition funci (i: nat): d_type := 
                Ret  func(#vecta[$i], #vectb[$i], #vectc[$i])

.

                Ret  genWith(#funci)

.

Definition genWithM (func: Function nat m element_type): (m (Vector vsize element_type)) := 
Definition upd (elt: element_type): (m (Vector vsize element_type)) := 
                LET i : nat <- $0

.

                LET indices : (Vector vsize nat) <- #genVector

                LET result : (Vector vsize element_type) <- #newVector

.

Definition mapM (func: Function a_type m b_type) (vecta: Vector vsize a_type): (m (Vector vsize b_type)) := 
Definition gen_elt (i: nat): (m b_type) := 
        LET v <- 

                Ret #v

.

                Ret  genWithM(#gen_elt)

.

Definition mapM_ (func: Function a_type m b_type) (vecta: Vector vsize a_type): (m void) := 
Definition gen_elt (i: nat): (m b_type) := 
        LET v <- 

                Ret #v

.

                Call vect : tvar36 <-  genWithM(#gen_elt)

                Ret null

.

Definition zipWithM (func: Function a_type Function b_type m c_type) (vecta: Vector vsize a_type) (vectb: Vector vsize b_type): (m (Vector vsize c_type)) := 
Definition gen_elt (i: nat): (m c_type) := 
        LET v <- 

                Ret #v

.

                Ret  genWithM(#gen_elt)

.

Definition zipWithM_ (func: Function a_type Function b_type m c_type) (vecta: Vector vsize a_type) (vectb: Vector vsize b_type): (m void) := 
Definition gen_elt (i: nat): (m c_type) := 
        LET v <- 

                Ret #v

.

        LET vect <- 

                Ret null

.

Definition zipWith3M (func: Function a_type Function b_type Function c_type m d_type) (vecta: Vector vsize a_type) (vectb: Vector vsize b_type) (vectc: Vector vsize c_type): (m (Vector vsize d_type)) := 
Definition gen_elt_3m (i: nat): (m d_type) := 
        LET v <- 

                Ret #v

.

                Ret  genWithM(#gen_elt_3m)

.

Definition replicateM (c: m b_type): (m (Vector vsize b_type)) := 
Definition gen_elt (i: nat): (m b_type) := 
                Ret #c

.

                Ret  genWithM(#gen_elt)

.

