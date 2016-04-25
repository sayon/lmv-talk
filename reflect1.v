(* How to define a property the usual way *)
Inductive evenp  : nat-> Prop :=
| evenz : evenp 0
| evenss n : evenp n -> evenp (S (S n)).

Theorem _200_is_even: evenp 200.
  repeat apply evenss.
  apply evenz.
Qed.

Print _200_is_even.

Fixpoint evenc (n:nat) :=
  match n with
    | 0 => true
    | S ( S n ) =>  evenc n
    | S n => false
  end.


Require Import Bool.

Fail Check forall n, evenc n || evenc (n + 1).


Coercion is_true (b:bool) := b = true.

Theorem _2000_is_even: evenc 2000.
  compute.
  apply eq_refl. 
Qed.

Print _2000_is_even.

(* Sometimes the proofs are carried around when step-by-step reasoning (esp. with dependent types) *)
(* Benefits are evident *)


Fixpoint In {T:Type} (a:T) (l:list T) : Prop :=
  match l with
    | nil  => False
    | cons b  m => b = a \/ In a m
  end.

Fixpoint genlist n := match n with
                        | 0 => nil
                        | S n => cons (S n) (genlist n)
                      end.

Definition mylst := genlist 3000. 

Time Eval compute in In 3 mylst.


From mathcomp.ssreflect Require Import all_ssreflect ssrbool.

Eval compute in  has (fun x => x == 4) mylst .
Eval compute in is_true ( has (fun x => x == 4) mylst ).

Check hasP.

(* *)

Parameters  A B C : bool.
Theorem _about_bools: A /\ B -> B /\ C -> A /\ B /\ C.
  move /andP; case A => //=.
Qed.

Time Eval compute in is_true ( has (fun x => x == 4) mylst ).

Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT: P -> reflect P true
| ReflectF: (not P) -> reflect  P false.

(* ensure that is_true P is equiv to P *)

Parameters A B: bool.
Lemma andP: reflect (A /\ B) (A && B).
 case A; case B; constructor.
 apply conj; unfold is_true; reflexivity.
 unfold not.
 intro H. inversion H. inversion H1.
 intro H. inversion H. inversion H0.
 intro H. inversion H. inversion H0.
Qed.

Lemma orP: reflect (A \/ B) (A || B).
  case A; case B; constructor.
  apply or_introl; unfold is_true; reflexivity.
  apply or_introl; unfold is_true; reflexivity.
  apply or_intror; unfold is_true; reflexivity.
  unfold not; intro H. inversion H; inversion H0.
Qed.
Parameter C: bool.

Theorem _about_bools: A /\ B -> B /\ C -> A /\ B /\ C.
   case A; case B; case C; try done; try by move /andP.
Qed.

