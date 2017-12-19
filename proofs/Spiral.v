(* Base Spiral defintions: data types, utility functions, lemmas *)

Global Generalizable All Variables.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Lt.
Require Import Coq.Program.Program.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.
Require Export Coq.Init.Specif.

Require Import Spiral.SpiralTactics.

Require Import Psatz.
Require Import Omega.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.abs.
Require Import MathClasses.theory.setoids.

Require Import CoLoR.Util.Nat.NatUtil.

Notation FinNat n := {x:nat | (x<n)%nat}.
Definition mkFinNat {n} {j:nat} (jc:(j<n)%nat) : FinNat n := @exist _ (gt n) j jc.

Global Instance max_proper A `{Le A, TotalOrder A, !Setoid A} `{!∀ x y: A, Decision (x ≤ y)}:
  Proper ((=) ==> (=) ==> (=)) max.
Proof.
  solve_proper.
Qed.

Global Instance negate_proper A `{Ar: Ring A} `{!Setoid A}:
  Setoid_Morphism (negate).
Proof.
  split;try assumption.
  solve_proper.
Qed.

Lemma ne_sym {T:Type} `{E: Equiv T} `{S: @Setoid T E} {a b: T}:
  (a ≠ b) <-> (b ≠ a).
Proof.
  crush.
Qed.

Global Instance abs_Setoid_Morphism A
         `{Ar: Ring A}
         `{Asetoid: !Setoid A}
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Azero Anegate}
  : Setoid_Morphism abs | 0.
Proof.
  split; try assumption.
  intros x y E.
  unfold abs, abs_sig.
  destruct (Aabs x) as [z1 [Ez1 Fz1]]. destruct (Aabs y) as [z2 [Ez2 Fz2]].
  simpl.
  rewrite <-E in Ez2, Fz2.
  destruct (total (≤) 0 x).
  now rewrite Ez1, Ez2.
  now rewrite Fz1, Fz2.
Qed.

Lemma abs_nonneg_s `{Aabs: Abs A}: forall (x : A), 0 ≤ x → abs x = x.
Proof.
  intros AA AE. unfold abs, abs_sig.
  destruct (Aabs AA).  destruct a.
  auto.
Qed.

Lemma abs_nonpos_s `{Aabs: Abs A} (x : A): x ≤ 0 → abs x = -x.
Proof.
  intros E. unfold abs, abs_sig. destruct (Aabs x) as [z1 [Ez1 Fz1]]. auto.
Qed.

Lemma abs_0_s
      `{Ae: Equiv A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Azero Anegate}
  : abs 0 = 0.
Proof.
  apply abs_nonneg_s. auto.
Qed.

Lemma abs_always_nonneg
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A}
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
  : forall x, 0 ≤ abs x.
Proof.
  intros.
  destruct (total (≤) 0 x).
  rewrite abs_nonneg_s; assumption.
  rewrite abs_nonpos_s.
  rewrite <- flip_nonpos_negate; assumption.
  assumption.
Qed.

Lemma abs_negate_s A (x:A)
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A}
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
  : abs (-x) = abs x.
Proof with trivial.
  destruct (total (≤) 0 x).
  -
    rewrite (abs_nonneg x), abs_nonpos.
    apply rings.negate_involutive.
    apply flip_nonneg_negate.
    apply H.
    apply H.
  -
    rewrite (abs_nonneg (-x)), abs_nonpos.
    reflexivity.
    apply H.
    apply flip_nonpos_negate.
    apply H.
Qed.

Lemma abs_nz_nz
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A}
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{Aledec: ∀ x y: A, Decision (x ≤ y)}
  :
    forall v : A, v ≠ zero <-> abs v ≠ zero.
Proof.
  split.
  -
    intros V.
    destruct (Aledec zero v).
    +
      apply abs_nonneg_s in l.
      rewrite l.
      apply V.
    +
      apply orders.le_flip in n.
      rewrite abs_nonpos_s; auto.
      apply rings.flip_negate_ne_0, V.
  -
    intros V.
    destruct (Aledec zero v) as [E | N].
    +
      apply abs_nonneg_s in E.
      rewrite <- E.
      apply V.
    +
      apply orders.le_flip in N.
      apply abs_nonpos_s in N.
      apply rings.flip_negate_ne_0.
      rewrite <- N.
      apply V.
Qed.

Global Instance abs_idempotent
         `{Ae: Equiv A}
         `{Az: Zero A} `{A1: One A}
         `{Aplus: Plus A} `{Amult: Mult A}
         `{Aneg: Negate A}
         `{Ale: Le A}
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Az Aneg}
         `{Ar: !Ring A}
         `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
  :UnaryIdempotent abs.
Proof.
  intros a b E.
  unfold compose.
  destruct (total (≤) 0 a).
  rewrite abs_nonneg_s.
  auto.
  apply abs_always_nonneg.
  setoid_replace (abs a) with (-a) by apply abs_nonpos_s.
  rewrite abs_negate_s.
  auto.
  apply Ato.
  apply Ar.
  apply ASRO.
  apply H.
Qed.

Lemma abs_max_comm_2nd
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A}
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
      `{Aledec: !∀ x y: A, Decision (x ≤ y)}
  : forall (x y:A),  max (abs y) x = abs (max (abs y) x).
Proof.

  intros.
  unfold max, sort, decide_rel.
  destruct (Aledec (abs y) x).

  (* Case "abs y <= x". *)
  unfold abs, abs_sig.
  simpl.
  destruct (Aabs x) as [z1 [Ez1 Fz1]].
  simpl.
  symmetry.
  assert (XP: 0 ≤ x). revert l. assert (0 ≤ abs y). apply abs_always_nonneg. auto.
  revert Ez1.
  auto.

  (* Case "abs y > x". *)
  simpl.
  rewrite unary_idempotency.
  reflexivity.
Qed.


Local Open Scope nat_scope.

Lemma modulo_smaller_than_devisor:
  ∀ x y : nat, 0 ≢ y → x mod y < y.
Proof.
  intros.
  destruct y; try congruence.
  unfold PeanoNat.Nat.modulo.
  omega.
Qed.

Lemma ext_equiv_applied_equiv
      `{Equiv A} `{Equiv B}
      `(!Setoid_Morphism (f : A → B))
      `(!Setoid_Morphism (g : A → B)) :
  f = g ↔ ∀ x, f x = g x.
Proof.
  pose proof (setoidmor_a f).
  pose proof (setoidmor_b f).
  split; intros E1.
  now apply ext_equiv_applied.
  intros x y E2. now rewrite E2.
Qed.

Lemma zero_lt_Sn:
  forall n:nat, 0<S n.
Proof.
  intros.
  omega.
Qed.

Lemma S_j_lt_n {n j:nat}:
  S j ≡ n -> j < n.
Proof.
  intros H.
  rewrite <- H.
  auto.
Qed.

Lemma Decidable_decision
      (P:Prop):
  Decision P -> decidable P.
Proof.
  intros D.
  unfold decidable.
  destruct D; tauto.
Qed.

Lemma div_iff_0:
  forall m i : nat, m ≢ 0 → i/m≡0 -> m>i.
Proof.
  intros m i M H.
  destruct (Compare_dec.dec_lt i m) as [HL|HGE].
  -
    omega.
  -
    apply Nat.nlt_ge in HGE.
    destruct (eq_nat_dec i m).
    *
      subst i.
      rewrite Nat.div_same in H.
      congruence.
      apply M.
    *
      assert(G:i>m) by crush.
      apply NatUtil.gt_plus in G.
      destruct G.
      rename x into k.
      subst i.
      replace (k + 1 + m) with (1*m+(k+1)) in H by ring.
      rewrite Nat.div_add_l in H.
      simpl in H.
      congruence.
      apply M.
Qed.

Lemma div_ne_0:
  ∀ m i : nat, m <= i → m ≢ 0 → i / m ≢ 0.
Proof.
  intros m i H MZ.
  unfold not.
  intros M.
  apply div_iff_0 in M.
  destruct M; crush.
  apply MZ.
Qed.

Lemma add_lt_lt
     {n m t : nat}:
  (t < m) ->  (t + n < n + m).
Proof.
  omega.
Qed.

(* Similar to `Vnth_cast_aux` but arguments in equality hypotheis are swapped *)
Lemma eq_lt_lt {n m k: nat} : n ≡ m -> k < n -> k < m.
Proof. intros; omega. Qed.

Lemma S_pred_simpl:
  forall n : nat, n ≢ 0 -> S (Init.Nat.pred n) ≡ n.
Proof.
  intros n H.
  destruct n.
  - congruence.
  - auto.
Qed.


Global Instance Sig_Equiv {A:Type} {Ae : Equiv A} {P:A->Prop}:
  Equiv (@sig A P) := fun a b => (proj1_sig a) = (proj1_sig b).

Instance proj1_Proper {A:Type} {Ae : Equiv A} {P:A->Prop}:
  Proper ((=)==>(=)) (@proj1_sig A P).
Proof.
  intros x y E.
  unfold equiv, Sig_Equiv in E.
  auto.
Qed.

Definition FinNat_bloat
           {m n:nat}
           (mn: (m < n)%nat):
  FinNat m -> FinNat n.
Proof.
  intros H.
  destruct H.
  assert (xc:(x<n)%nat).
  apply Nat.lt_trans with (m:=m); auto.
  exact (mkFinNat xc).
Defined.

Require Import MathClasses.implementations.peano_naturals.

Global Instance FinNat_bloat_proper
       {m n:nat}
       (mn: (m<n)%nat):
  Proper ((=) ==> (=)) (FinNat_bloat mn).
Proof.
  intros x y H.
  destruct x, y.
  unfold FinNat_bloat.
  inversion H.
  simpl in H0.
  clear H.
  unfold mkFinNat.
  unfold equiv, Sig_Equiv.
  simpl.
  rewrite H0.
  reflexivity.
Qed.
