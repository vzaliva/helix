Require Import Coq.Relations.Relations.
Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadExc.

Require Import MathClasses.interfaces.canonical_names.

Require Export Vellvm.Error.

Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.StringSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Tactics.HelixTactics.

Inductive is_OK {A : Type} : err A -> Prop :=
| is_OK_intro : forall a, is_OK (inr a).

Inductive is_Err {A : Type} : err A -> Prop :=
| is_Err_intro : forall a, is_Err (inl a).

Fact eq_inr_is_OK {A:Type} (x:A) (y: err A):
  (y ≡ inr x) -> is_OK y.
Proof.
  intro; subst; constructor.
Qed.

Fact eq_inl_is_Err {A:Type} (msg:string) (y: err A):
  (y ≡ inl msg) -> is_Err y.
Proof.
  intro; subst; constructor.
Qed.

Inductive err_equiv_r {A:Type} `{Equiv A} : relation (err A) :=
| err_r_inr : forall a b, a=b -> err_equiv_r (inr a) (inr b)
| err_r_inl : forall a b, err_equiv_r (inl a) (inl b). (* Error messages could differ! *)

Global Instance err_equiv {T:Type} `{Equiv T}:
  Equiv (err T) := err_equiv_r.

Global Instance err_Equivalence
       {A:Type}
       `{Ae: Equiv A}
       `{Ar: Equivalence A Ae}:
  Equivalence (@err_equiv A Ae).
Proof.
  split.
  -
    intros x.
    destruct x; constructor; try reflexivity.
  -
    intros x y E.
    destruct x, y; inversion E; constructor; auto.
  -
    intros a b c Eab Ebc.
    destruct a,b,c; inversion Eab; inversion Ebc;  constructor; auto.
Qed.

Global Instance err_inr_proper {T:Type} `{Equiv T}:
  Proper ((=) ==> (=)) (@inr string T).
Proof.
  simpl_relation.
  constructor.
  assumption.
Qed.

Global Instance err_inl_proper {T:Type} `{Equiv T}:
  Proper ((=) ==> (=)) (@inl string T).
Proof.
  simpl_relation.
  constructor.
Qed.

Global Instance trywith_proper {T:Type} `{Te: Equiv T}:
  Proper((=) ==> (=) ==> (=)) (@trywith string T err Monad_err Exception_err).
Proof.
  simpl_relation.
  unfold trywith.
  destruct x0, y0; try some_none; try some_inv; try constructor; auto.
Qed.

Ltac destruct_err_equiv :=
  match goal with
  | [ |- @equiv (err _) (@err_equiv _ _) _ _] =>
    unfold equiv; destruct_err_equiv
  | [ |- err_equiv _ _] =>
    unfold err_equiv; destruct_err_equiv
  | [ |- err_equiv_r ?a ?b] =>
    let Ha := fresh "Ha" in
    let Hb := fresh "Hb" in
    destruct a eqn:Ha, b eqn:Hb;
    match goal with
    | [ |- err_equiv_r (inr _) (inl _)] => exfalso
    | [ |- err_equiv_r (inl _) (inr _)] => exfalso
    | [ |- err_equiv_r (inl _) (inl _)] => constructor
    | [ |- err_equiv_r (inr _) (inr _)] => constructor
    end
  end.

(* Not 'err'-specific but defined here for lack of better place *)
Ltac inl_inr :=
  match goal with
  | [H1: inl _ ≡ inr _ |- _] => inversion H1
  | [H1: inr _ ≡ inl _ |- _] => inversion H1

  | [H1: inl _ ≡ Monad.ret _ |- _] => inversion H1
  | [H1: Monad.ret _ ≡ inl _ |- _] => inversion H1

  | [H1: raise _ ≡ inr _ |- _] => inversion H1
  | [H1: inr _ ≡ raise _ |- _] => inversion H1

  | [H1: inl _ = inr _ |- _] => unfold equiv in H1; inversion H1
  | [H1: inr _ = inl _ |- _] => unfold equiv in H1; inversion H1

  | [ |- inl ?x ≡ inl ?x ] => reflexivity
  | [ |- inr ?x ≡ inr ?x ] => reflexivity

  | [H1: ?a = inr _,
         H2: ?a = inl _ |- _] => rewrite H1 in H2;
                               unfold equiv in H2;
                               inversion H2

  | [H1: is_OK (inl _) |- _] => inversion H1
  | [H1: is_Err (inr _) |- _] => inversion H1
  | [|- is_OK (inr _)] => constructor
  | [|- is_Err (inl _)] => constructor
  end.

Lemma inl_inj_equiv :
  forall s1 s2, inl s1 = inl s2.
Proof.
  constructor; assumption.
Qed.

Lemma inr_inj_equiv `{E: Equiv A}:
  forall (a b : A), a = b <-> inr a = inr b.
Proof.
  split; intros.
  - constructor; assumption.
  - inversion H; subst; assumption.
Qed.

Ltac inl_inr_inv :=
  match goal with
  | [H1: inl _ ≡ inl _ |- _] => inversion H1; clear H1
  | [H1: inr _ ≡ inr _ |- _] => inversion H1; clear H1
  | [H1: inl _ = inl _ |- _] => apply inl_inj_equiv in H1
  | [H1: inr _ = inr _ |- _] => apply inr_inj_equiv in H1

  | [H1: inr _ ≡ Monad.ret _ |- _] => inversion H1; clear H1
  | [H1: Monad.ret _ ≡ inr _ |- _] => inversion H1; clear H1
  | [H1: raise _ ≡ inl _ |- _] => inversion H1; clear H1
  | [H1: inl _ ≡ raise _ |- _] => inversion H1; clear H1
  end.

Lemma err_equiv_eq
      {A: Type}
      `{Ae: Equiv A}
      `{Ar: Equivalence A Ae}
      (a b: err A) :
  (a ≡ b) -> (a = b).
Proof.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma trywith_inr_any_exc {E A : Type} (e : E) (oa : option A) (a : A) :
  trywith e oa ≡ inr a ->
  forall e' : E, trywith e' oa ≡ inr a.
Proof.
  intros.
  unfold trywith in *.
  break_match; [assumption | inversion H].
Qed.

Ltac err_eq_to_equiv_hyp :=
  repeat
    match goal with
    | [H: @eq (err _) _ _ |- _] => apply err_equiv_eq in H
    end.

Fact inr_is_OK `{Equiv A} (x:A) (y: err A):
  (y = inr x) -> is_OK y.
Proof.
  intros.
  destruct y.
  inversion H0.
  constructor.
Qed.

Definition nat_eq_or_err (msg:string) (a b:nat) : err unit :=
  if PeanoNat.Nat.eq_dec a b
  then ret tt
  else raise (msg ++ " " ++ string_of_nat a ++ "!=" ++ string_of_nat b)%string.
