Require Import Coq.Bool.Bool.

Definition T:Type := prod (prod (prod (prod bool bool) bool) bool) bool.
Definition t0:T := (true, false, false, false, false).

Definition op (a b: T) : T :=
  match a,b with
    (s0,c0_00,c0_01,c0_10,c0_11), (s1,c1_00,c1_01,c1_10,c1_11) =>
    (andb s0 s1,
     (orb (orb c0_00 c0_00) (andb s0 s1)) , (* struct col *)
     (orb (orb c0_01 c1_01) (negb (orb s0 s1))), (* value col *)
     (orb (orb c0_01 c0_01) (andb s0 (negb s1))), (* left value col *)
     (orb (orb c0_11 c0_11) (andb s1 (negb s0))) (* right value col *)
    )
  end.

(* Only works for value collision *)
Lemma Tident: forall a:T,
    (op a t0) = a /\ (op t0 a) = a.
Proof.
  intros a.
  split.
  -
    destruct a as [[[[s c1] c2] c3] c4].
    unfold t0, op.
    destr_bool; reflexivity.

  -
    destruct a as [[[[s c1] c2] c3] c4].
    unfold t0, op.
    destr_bool; reflexivity.
Qed.


Lemma Tassoc: forall a b c:T,
    op (op a b) c = op a (op b c).
Proof.
  intros a b c.
  destruct a as [[[[sa ca1] ca2] ca3] ca4].
  destruct b as [[[[sb cb1] cb2] cb3] cb4].
  destruct c as [[[[sc cc1] cc2] cc3] cc4].
  destr_bool.
Qed.

