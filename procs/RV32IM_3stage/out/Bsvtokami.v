Require Import Kami.
Require Import Kami.Lib.Struct.
Require Import Bool Arith String Nat ZArith.

Record Empty := {
    Empty'modules: Modules;
}.

Record Reg (a : Kind) := {
    Reg'modules: Modules;
    Reg'_read : string;
    Reg'_write : string;
}.

Fixpoint toBinaryP (p: positive) : string :=
  match p with
  | xI p' => String "1" (toBinaryP p')
  | xO p' => String "0" (toBinaryP p')
  | xH => ""
  end.

Definition toBinaryN (n: N): string :=
  match n with
  | N0 => "0"
  | Npos p => toBinaryP p
  end.

Definition toBinaryString (n: nat) := (toBinaryN (N.of_nat n)).

Record ModuleInstance intT :=
    { module : Modules;
      interface : intT;
    }.

Definition bitlt (x : nat) (y: nat): bool := (Nat.ltb x y).

(** * Notation for BSV to Kami modules *)

Inductive BKElt :=
| BKRegister (_ : RegInitT)
| BKRule (_ : Attribute (Action Void))
| BKMeth (_ : DefMethT)
| BKMod (_ : list Modules)
| BKBlock (_ : InBKModule)

with InBKModule :=
| NilInBKModule
| ConsInBKModule (_ : BKElt) (_ : InBKModule).

Fixpoint makeBKModule' (im : InBKModule) :=
  match im with
  | NilInBKModule => (nil, nil, nil, nil)
  | ConsInBKModule e i =>
    let '(iregs, irules, imeths, imods) := makeBKModule' i in
    match e with
    | BKRegister mreg => (mreg :: iregs, irules, imeths, imods)
    | BKRule mrule => (iregs, mrule :: irules, imeths, imods)
    | BKMeth mmeth => (iregs, irules, mmeth :: imeths, imods)
    | BKMod mmods => (iregs, irules, imeths, mmods ++ imods)
    | BKBlock m =>
      let '(mregs, mrules, mmeths, mmods) := makeBKModule' m in
      (mregs ++ iregs, mrules ++ irules, mmeths ++ imeths, mmods ++ imods)
    end
  end.

Fixpoint concatModules (m: Modules) (lm: list Modules) :=
  match lm with
  | nil => m
  | m' :: lm' => concatModules (ConcatMod m m') lm'
  end.

Definition makeBKModule (im : InBKModule) :=
  let '(regs, rules, meths, mods) := makeBKModule' im in
  concatModules (Mod regs rules meths) mods.

(* * BSV to Kami Notation *)

Delimit Scope bk_scope with bk.

Notation "'BKSTMTS' { s1 'with' .. 'with' sN }" :=
  (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk NilInBKModule) ..)
    (at level 0, only parsing).

Notation "'LOOP' { s1 'with' .. 'with' sN } SL" :=
  (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk SL%bk) ..)
    (at level 0, only parsing).

Notation "'RegisterN' name : type <- 'Default'" :=
  (BKRegister (Build_Attribute name (RegInitDefault type)))
    (at level 0, name at level 0, type at level 0) : bk_scope.

Notation "'RegisterN' name : type <- init" :=
  (BKRegister (Build_Attribute name (RegInitCustom (existT ConstFullT type init))))
    (at level 0, name at level 0, type at level 0, init at level 0) : bk_scope.

Notation "'Register' name : type <- 'Default'" :=
  (BKRegister (Build_Attribute name (RegInitDefault (SyntaxKind type))))
    (at level 0, name at level 0, type at level 0) : bk_scope.

Notation "'Register' name : type <- init" :=
  (BKRegister (Build_Attribute name (RegInitCustom (existT ConstFullT (SyntaxKind type) (makeConst init)))))
    (at level 0, name at level 0, type at level 0, init at level 0) : bk_scope.

Notation "'Method' name () : retT := c" :=
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := Void; ret := retT |}
                                   (fun ty => fun _ : ty Void =>
                                                (c)%kami_action : ActionT ty retT))))
    (at level 0, name at level 0) : bk_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := dom; ret := retT |}
                                   (fun ty => fun param : ty dom =>
                                                (c)%kami_action : ActionT ty retT))))
    (at level 0, name at level 0, param at level 0, dom at level 0) : bk_scope.

Notation "'Rule' name := c" :=
  (BKRule (Build_Attribute name (fun ty => c%kami_action : ActionT ty Void)))
    (at level 0, name at level 0) : bk_scope.

Notation "'BKMODULE' { s1 'with' .. 'with' sN }" :=
  (makeBKModule (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk NilInBKModule) ..))
    (at level 0, only parsing).

Notation "'Method2' name ( p1 : d1 ) ( p2 : d2 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let fields := STRUCT { "_1" :: d1f ; "_2" :: d2f } in
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := (Struct fields); ret := retT |}
                                   (fun ty => fun param : ty (Struct fields)  =>
                                                 (LET p1 : d1g <-  #param!fields @."_1";
                                                  LET p2 : d2g <-  #param!fields @."_2";
                                                  c)%kami_action : ActionT ty retT)))))
    (at level 0, name at level 0, p1 at level 0, d1 at level 0, p2 at level 0, d2 at level 0).

Notation "'Method3' name ( p1 : d1 ) ( p2 : d2 )  ( p3 : d3 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let d3f := d3 in
   let d3g := d3 in
   let fields := STRUCT { "_1" :: d1f ; "_2" :: d2f; "_3" :: d3f } in
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := (Struct fields); ret := retT |}
                                   (fun ty => fun param : ty (Struct fields)  =>
                                                 (LET p1 : d1g <-  #param!fields @."_1";
                                                  LET p2 : d2g <-  #param!fields @."_2";
                                                  LET p3 : d3g <-  #param!fields @."_3";
                                                  c)%kami_action : ActionT ty retT)))))
    (at level 0, name at level 0, p1 at level 0, d1 at level 0, p2 at level 0, d2 at level 0, p3 at level 0, d3 at level 0).
