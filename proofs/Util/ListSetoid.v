Require Import Coq.Lists.List.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.

Import ListNotations.

Global Instance List_equiv {A: Type} `{Ea: Equiv A}: Equiv (list A) := List.Forall2 equiv.

Global Instance Forall2_Reflexive
       {A: Type} {R: relation A} `{RR: Reflexive A R}:
  Reflexive (Forall2 R).
Proof.
  intros x.
  induction x; constructor; auto.
Qed.

Global Instance nth_error_proper {A: Type} `{Ae: Equiv A} `{AEe: Equivalence A Ae}:
  Proper ((=) ==> (=) ==> (=)) (@nth_error A).
Proof.
  intros l1 l2 El n1 n2 En.
  unfold equiv, peano_naturals.nat_equiv in En.
  subst n2. rename n1 into n.
  revert l1 l2 El.
  induction n.
  -
    intros l1 l2 El.
    simpl.
    repeat break_match; auto; try inversion El.
    rewrite H2.
    reflexivity.
  -
    intros l1 l2 El.
    destruct l1, l2; try inversion El.
    auto.
    simpl.
    apply IHn.
    inversion El.
    auto.
Qed.

Definition isNth {A:Type} `{Equiv A} (l:list A) (n:nat) (v:A) : Prop :=
  match nth_error l n with
  | None => False
  | Some x => x = v
  end.

Lemma isNth_Sn {A:Type} `{Equiv A} (h:A) (l:list A) (n:nat) (v:A):
  isNth (h :: l) (S n) v ≡ isNth l n v.
Proof.
  crush.
Qed.

Definition listsDiffByOneElement {A:Type} `{Ae:Equiv A} (l0 l1:list A) (n:nat) : Prop :=
  forall i, i≢n -> nth_error l0 i = nth_error l1 i.

Lemma listsDiffByOneElement_Sn {A:Type} `{Ae:Equiv A} {Aeq: Equivalence Ae} (h0 h1:A) (l0 l1:list A) (n:nat):
  h0 = h1 ->
  listsDiffByOneElement l0 l1 n ->
  listsDiffByOneElement (h0::l0) (h1::l1) (S n).
Proof.
  intros E H.
  unfold listsDiffByOneElement in *.
  intros i ic.
  destruct i.
  -
    simpl.
    some_apply.
  -
    simpl.
    apply H.
    crush.
Qed.
