Require Import Coq.Bool.Bool.

Definition T:Type := prod bool bool.
Definition t0 := (true, false).

Definition op (a b: T) :=
  let (s0,c0) := a in
  let (s1,c1) := b in
  (andb s0 s1, orb c0 c1).
(*   (andb s0 s1, orb (orb c0 c1) (negb (orb s0 s1))). *)

Lemma Tident: forall a:T,
    (op a t0) = a /\ (op t0 a) = a.
Proof.
  intros a.
  split.
  - destruct a as [sa ca].
    unfold t0.
    destruct t0 as [s0 c0].
    destr_bool; reflexivity.

  - destruct a as [sa ca].
    unfold t0.
    destruct t0 as [s0 c0].
    destr_bool; reflexivity.
Qed.

Lemma Tassoc: forall a b c:T,
    op (op a b) c = op a (op b c).
Proof.
  intros a b c.
  destruct a,b,c.
  destr_bool.
Qed.
