Require Import Arith.
Module Hierarchy.

  (*** First ***)
Module EQ.

  Record class (T : Type) := Class { cmp : T -> T -> Prop }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _ the_cmp) := e in the_cmp.
  Check op. (* forall e : type, obj e -> obj e -> Prop *)
  Arguments op {e} x y : simpl never.
  Arguments Class {T} cmp.

  Module theory.
  Notation "x == y" := (op x y) (at level 70).
  Check forall (e : type) (a b : obj e), a == b.
  End theory.

End EQ. Import EQ.theory.

Fail Check 3 == 3. (* !!! need canonical instance *)

(* Error: The term "3" has type "nat" while it is expected to have type
    "EQ.obj ?1". *)
Definition nat_eq (x y : nat) := nat_compare x y = Eq.  (* nat_compare is a default thing *)
Definition nat_EQcl : EQ.class nat := EQ.Class nat_eq.
Canonical Structure nat_EQty : EQ.type := EQ.Pack nat nat_EQcl.

Check 3 == 3.
Eval compute in 3 == 4.

(* Let's define a family of hints now rather than a single one *)
Fail Check forall (e : EQ.type) (a b : EQ.obj e), (a,b) == (a,b). 
(* The term "(a, b)" has type "(obj e * obj e)%type"
  while it is expected to have type "obj ?15". *)

Definition pair_eq (e1 e2 : EQ.type) (x y : EQ.obj e1 * EQ.obj e2) :=
  fst x == fst y /\ snd x == snd y.
Definition pair_EQcl e1 e2 := EQ.Class (pair_eq e1 e2).
Canonical Structure pair_EQty (e1 e2 : EQ.type) : EQ.type :=
  EQ.Pack (EQ.obj e1 * EQ.obj e2) (pair_EQcl e1 e2).




Check forall (e : EQ.type) (a b : EQ.obj e), (a,b) == (a,b).
Check (forall n m : nat, (3,4) == (n,m)).






(*** Done with EQ, going LE.
Second  ***)

Module LE.

  Record class T := Class { cmp : T -> T -> Prop }.
  Structure type := Pack { obj : Type; class_of : class obj }.
  Definition op (e : type) : obj e -> obj e -> Prop :=
    let 'Pack _ (Class _  f) := e in f.
  Arguments op {_} x y : simpl never.
  Arguments Class {T} cmp.

  Module theory.
  Notation "x <= y" := (op x y) (at level 70).
  End theory.

End LE.

Import LE.theory.

Definition nat_le x y := nat_compare x y <> Gt.
Definition nat_LEcl : LE.class nat := LE.Class nat_le.
Canonical Structure nat_LEty : LE.type := LE.Pack nat nat_LEcl.

Definition pair_le e1 e2 (x y : LE.obj e1 * LE.obj e2) :=
  fst x <= fst y /\ snd x <= snd y.
Definition pair_LEcl e1 e2 := LE.Class (pair_le e1 e2).
Canonical Structure pair_LEty (e1 e2 : LE.type) : LE.type :=
  LE.Pack (LE.obj e1 * LE.obj e2) (pair_LEcl e1 e2).

Check (3,4,5) <= (3,4,5).


(*** Why can't we be happy with it yet? 
Still can't type the mixtures well
*)

Check 2 <= 3 /\ 2 == 2.
Fail Check forall (e : EQ.type) (x y : EQ.obj e), x <= y -> y <= x -> x == y.
(* The term "x" has type "EQ.obj e" while it is expected to have type
    "LE.obj ?32". *)


Module LEQ.
  (*!!!  didn't have that before *)

  (*** All properties that appear as a result of chemistry between two classes *blush* *)

  Record mixin (e : EQ.type) (le : EQ.obj e -> EQ.obj e -> Prop) :=
    Mixin { compat : forall x y : EQ.obj e, le x y -> le y x -> x == y }.

  (** derivation through inclusion (fellow programmers taught me that in java)  *)
  (** Bref: properties of EQ, properties of LE, new properties *)
  
  Record class T := Class {
    EQ_class    : EQ.class T;
    LE_class    : LE.class T;
    extra : mixin (EQ.Pack T EQ_class) (LE.cmp T LE_class) }.
  
  Structure type := _Pack { obj : Type; class_of : class obj }.
  Arguments Mixin {e le} _.
  Arguments Class {T} _ _ _.

  Module theory.

  Fail Check (forall (le : type) (n m : obj le), n <= m -> n <= m -> n == m).
    (* The term "n" has type "obj le" while it is expected to have type
       "LE.obj ?44". *)

  Definition to_EQ (e : type) : EQ.type := EQ.Pack _ (EQ_class _ (class_of e)).
  Definition to_LE (e : type) : LE.type := LE.Pack _ (LE_class _ (class_of e)).


  Canonical Structure to_EQ.
  Canonical Structure to_LE.

  

  (** The faulty example from above: *)
  
  Lemma lele_eq (e : type) (x y : obj e) : x <= y -> y <= x -> x == y.
  Proof. exact (compat _ _ (extra _ (class_of e)) x y). Qed.
  Check lele_eq.
  (* forall (e : type) (x y : obj e), x <= y -> y <= x -> x == y*)
  Arguments lele_eq {e} x y _ _.

  End theory.

End LEQ.

Import LEQ.theory.

Example test_algebraic (n m : nat) :  n <= m -> m <= n -> n == m.
Proof. Fail apply (lele_eq n m). Abort.
  (* The term "n" has type "nat" while it is expected to have type 
   "obj ?48". *)

Example test_algebraic2 (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
  n <= m -> m <= n -> n == m.
Proof. Fail apply (lele_eq n m). Abort.
  (* The term "n" has type "(obj l1 * obj l2)%type"
    while it is expected to have type "obj ?70". *)

Lemma nat_LEQ_compat (n m : nat) : n <= m -> m <= n -> n == m.
Proof.
unfold EQ.op; unfold LE.op; simpl; unfold nat_le; unfold nat_eq.
case (nat_compare_spec n m); [ reflexivity | | now intros _ H; case H ].
now intro H; apply nat_compare_gt in H; rewrite -> H; intros _ H1; case H1.
Qed.
Definition nat_LEQmx := LEQ.Mixin nat_LEQ_compat.

Lemma pair_LEQ_compat (l1 l2 : LEQ.type) (n m : LEQ.obj l1 * LEQ.obj l2) :
n <= m -> m <= n -> n == m.
Proof.
case n; case m; unfold EQ.op; unfold LE.op; simpl.
now intros n1 n2 m1 m2 [Le1 Le2] [Ge1 Ge2]; split; apply lele_eq.
Qed.
Definition pair_LEQmx l1 l2 := LEQ.Mixin (pair_LEQ_compat l1 l2).

Module Add_instance_attempt.

  Canonical Structure nat_LEQty : LEQ.type :=
    LEQ._Pack nat (LEQ.Class nat_EQcl nat_LEcl nat_LEQmx).

  Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
  Proof. now apply (lele_eq n m). Qed.

  Canonical Structure pair_LEQty (l1 l2 : LEQ.type) : LEQ.type :=
    LEQ._Pack (LEQ.obj l1 * LEQ.obj l2)
      (LEQ.Class
        (EQ.class_of (pair_EQty (to_EQ l1) (to_EQ l2)))
        (LE.class_of (pair_LEty (to_LE l1) (to_LE l2)))
        (pair_LEQmx l1 l2)).

  Example test_algebraic2 (n m : nat * nat) : n <= m -> m <= n -> n == m.
  Proof. now apply (lele_eq n m). Qed.

End Add_instance_attempt.

Import infrastructure.

Definition packager T e0 le0 (m0 : LEQ.mixin e0 le0) :=
    [find e  | EQ.obj e ~ T       | "is not an EQ.type" ]
    [find o  | LE.obj o ~ T       | "is not an LE.type" ]
    [find ce | EQ.class_of e ~ ce ]
    [find co | LE.class_of o ~ co ]
    [find m  | m ~ m0             | "is not the right mixin" ]
  LEQ._Pack T (LEQ.Class ce co m).

Notation Pack T m := (packager T _ _ m _ id _ id _ id _ id _ id).

Canonical Structure nat_LEQty := Eval hnf in Pack nat nat_LEQmx.
Print nat_LEQty.

Example test_algebraic (n m : nat) : n <= m -> m <= n -> n == m.
Proof. now apply (lele_eq n m). Qed.

Canonical Structure pair_LEQty (l1 l2 : LEQ.type) :=
Eval hnf in Pack (LEQ.obj l1 * LEQ.obj l2) (pair_LEQmx l1 l2).

Example test_algebraic2 (n m : nat * nat) : n <= m -> m <= n -> n == m.
Proof. now apply (lele_eq n m). Qed.

Fail Canonical Structure err := Eval hnf in Pack bool nat_LEQmx.
(* Error : bool : "is not an EQ.type" *)
Fail Canonical Structure err := Eval hnf in Pack (nat * nat) nat_LEQmx.
(* Error : nat_LEQmx : "is not the right mixin" *)

End Hierarchy.

Module InteractiveFailure.
Import Hierarchy EQ.theory.
Canonical Structure failsafe t f : EQ.type := EQ.Pack t (EQ.Class f).
Set Printing All. Check (true == true). 
Fail Lemma test : true == true.
(* Cannot infer an internal placeholder of type "bool -> bool -> Prop *)
End InteractiveFailure.

Module LinkCStoTC.
Import Hierarchy EQ.theory.
(* Existing Class EQ.class.
   Anomaly: https://coq.inria.fr/bugs/show_bug.cgi?id=2951 *)
(* Begin workaround, Record -> Class *)
Module EQ.
Class class A : Type := Class { cmp : A -> A -> Prop }.
Structure type : Type := Pack { obj : Type; class_of : class obj }.
Canonical Structure nat_EQty := Pack nat (Class nat nat_eq).
Definition op (e : type) : obj e -> obj e -> Prop :=
  let 'Pack _ (Class _ f) := e in f.
End EQ.
Notation "x == y" := (EQ.op _ x y) (at level 70).
(* End workaround *)
Canonical Structure failsafe T {c : EQ.class T} : EQ.type := EQ.Pack T c.
Lemma test : True.
Fail cut (true == true). Abort.
Instance bool_EQclass : EQ.class bool := EQ.Class bool (@eq bool).
Set Printing All. Check (true == true).
(* op (@failsafe bool bool_EQclass) true true *)
Lemma test : true == true. Abort.
End LinkCStoTC.


Module LinkTCtoCS.

Class eq_class {A} : Type := Class { cmp : A -> A -> Prop }.
Definition bool_cmp b1 b2 := bool_eq b1 b2 = true.
Instance bool_eq : eq_class := Class bool bool_cmp.
Notation "x === y" := (cmp x y) (at level 70).
Import Hierarchy EQ.theory.
Instance find_CS (e : EQ.type) : eq_class := Class (EQ.obj e) (@EQ.op e).
Set Printing All. 
Check 0 === 0. (* @cmp nat (find_CS nat_EQty) O O : Prop *)

End LinkTCtoCS.
