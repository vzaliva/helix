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

Lemma is_OK_neq_inl {A : Type} {E : Equiv A} (a : err A) :
  is_OK a -> forall s, a ≠ inl s.
Proof.
  intros.
  destruct a.
  inversion H.
  intros C; inversion C.
Qed.

Lemma inr_neq {A : Type} {a b : A} :
  inr (A:=string) a ≢ inr b <-> a ≢ b.
Proof.
  split; congruence.
Qed.

Section err_p.

  Variables (A : Type) (P : A -> Prop).

  (* lifting Predicate to option. None is not allowed *)
  Inductive err_p : (err A) -> Prop :=
  | err_p_intro : forall x, P x -> err_p (inr x).

  (* lifting Predicate to option. None is allowed *)
  Inductive err_p_n : (err A) -> Prop :=
  | err_p_inl_intro: forall x, err_p_n (inl x)
  | err_p_inr_intro : forall x, P x -> err_p_n (inr x).

  Global Instance err_p_proper
         `{Ae: Equiv A}
         {Pp: Proper ((=) ==> (iff)) P}
    :
      Proper ((=) ==> (iff)) err_p.
  Proof.
    intros a b E.
    split; intro.
    -
      destruct a,b; try inl_inr; inversion H.
      inl_inr_inv.
      subst.
      constructor.
      rewrite <-E.
      assumption.
    -
      destruct a,b; try inl_inr; inversion H.
      inl_inr_inv.
      subst.
      constructor.
      rewrite E.
      assumption.
  Qed.

End err_p.
Arguments err_p {A} P.
Arguments err_p_n {A} P.

Section herr.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Complete on [inl]. *)
  Inductive herr_c : (err A) -> (err B) -> Prop :=
  | herr_c_inl : forall e1 e2, herr_c (inl e1) (inl e2)
  | herr_c_inr : forall a b, R a b -> herr_c (inr a) (inr b).

  (** Empty on [inl]. *)
  Inductive herr : (err A) -> (err B) -> Prop :=
  | herr_inr : forall a b, R a b -> herr (inr a) (inr b).

  (** implication-like. *)
  Inductive herr_i : (err A) -> (err B) -> Prop :=
  | herr_i_inl_inl : forall e1 e2, herr_i (inl e1) (inl e2)
  | herr_i_inl_inr : forall e a, herr_i (inl e) (inr a)
  | herr_i_inr_inr : forall a b, R a b -> herr_i (inr a) (inr b).

  Inductive herr_f : (err A) -> (err B) -> Prop :=
  | herr_f_inl_l : forall e x, herr_f (inl e) x
  | herr_f_inl_r : forall e x, herr_f x (inl e)
  | herr_f_inr : forall a b, R a b -> herr_f (inr a) (inr b).

End herr.
Arguments herr {A B} R.
Arguments herr_c {A B} R.
Arguments herr_i {A B} R.

Section h_opt_err.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Complete on [inl]. *)
  Inductive h_opt_err_c : (option A) -> (err B) -> Prop :=
  | h_opt_err_c_None : forall e, h_opt_err_c None (inl e)
  | h_opt_err_c_Some : forall a b, R a b -> h_opt_err_c (Some a) (inr b).

  Inductive h_opt_opterr_c : (option A) -> option (err B) -> Prop :=
  | h_opt_opterr_c_None1 : h_opt_opterr_c None None
  | h_opt_opterr_c_None2 : forall e, h_opt_opterr_c None (Some (inl e))
  | h_opt_opterr_c_Some : forall a b, R a b -> h_opt_opterr_c (Some a) (Some (inr b)).

  (** Empty on [inl]. *)
  Inductive h_opt_err : (option A) -> (err B) -> Prop :=
  | h_opt_err_Some : forall a b, R a b -> h_opt_err (Some a) (inr b).

  (** implication-like. *)
  Inductive h_opt_err_i : (option A) -> (err B) -> Prop :=
  | herr_i_None_inl : forall e, h_opt_err_i None (inl e)
  | herr_i_None_inr : forall a, h_opt_err_i None (inr a)
  | herr_i_Some_inr : forall a b, R a b -> h_opt_err_i (Some a) (inr b).

  Global Instance h_opt_err_c_proper
         `{Ae : Equiv A}
         `{Be : Equiv B}
         {RP : Proper ((=) ==> (=) ==> (iff)) R}
    :
      Proper ((=) ==> (=) ==> (iff)) h_opt_err_c.
  Proof.
    split; intros.
    -
      destruct x, y, x0, y0.
      all: try some_none.
      all: try inl_inr.
      all: try inversion H1.
      all: constructor.
      some_inv; inl_inr_inv; subst.
      unfold Proper, respectful in RP.
      specialize (RP a a0 H b b0 H0).
      apply RP.
      apply H4.
    -
      destruct x, y, x0, y0.
      all: try some_none.
      all: try inl_inr.
      all: try inversion H1.
      all: constructor.
      some_inv; inl_inr_inv; subst.
      unfold Proper, respectful in RP.
      specialize (RP a a0 H b b0 H0).
      apply RP.
      apply H4.
  Qed.

End h_opt_err.
Arguments h_opt_err {A B} R.
Arguments h_opt_err_c {A B} R.
Arguments h_opt_opterr_c {A B} R.
Arguments h_opt_err_i {A B} R.

Require Import Helix.Util.ListSetoid.

Lemma monadic_fold_left_err_app
      {A B : Type}
      {f : A -> B -> err A}
      {a a':A}
      {l l': list B}
      {x: err A}
  :
    monadic_fold_left f a l ≡ inr a' ->
    monadic_fold_left f a' l' ≡ x ->
    monadic_fold_left f a (l++l') ≡ x.
Proof.
  revert a a'.
  induction l as [|l0 ls IH]; intros.
  -
    cbn in *.
    inv H.
    auto.
  -
    cbn in *.
    break_match_goal;[inl_inr|].
    eapply IH; eauto.
Qed.

(* raise [err] if boolean flag is false *)
Definition assert_true_to_err {A:Type} (msg:string) (b:bool) (v:A) : err A
  := if b then inr v else inl msg.

(* raise [err] if boolean flag is true *)
Definition assert_false_to_err {A:Type} (msg:string) (b:bool) (v:A) : err A
  := if b then inl msg else inr v.
