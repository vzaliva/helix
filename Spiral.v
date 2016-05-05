(* Base Spiral defintions: data types, utility functions, lemmas *)


Global Generalizable All Variables.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Program.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Strings.String.

Require Import VecUtil.
Require Import VecSetoid.

Require Import CaseNaming.
Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.
Require Import Psatz.
Require Import Omega.

Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.products.
Require Import MathClasses.theory.naturals.

Require Export Coq.Vectors.Vector.
Require Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Instance max_proper A `{Le A, TotalOrder A, !Setoid A} `{!∀ x y: A, Decision (x ≤ y)}:
  Proper ((=) ==> (=) ==> (=)) max.
Proof.
  solve_proper.
Qed.

Instance negate_proper A `{Ar: Ring A} `{!Setoid A}:
  Setoid_Morphism (negate).
Proof.
  split;try assumption.
  solve_proper.
Qed.

Instance abs_setoid_proper A
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
  rewrite (abs_nonneg x), abs_nonpos...
  apply rings.negate_involutive.
  apply flip_nonneg_negate...
  rewrite (abs_nonneg (-x)), abs_nonpos...
  reflexivity.
  apply flip_nonpos_negate...
Qed.

Instance abs_idempotent
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

  Case "abs y <= x".
  unfold abs, abs_sig.
  simpl.
  destruct (Aabs x) as [z1 [Ez1 Fz1]].
  simpl.
  symmetry.
  assert (XP: 0 ≤ x). revert l. assert (0 ≤ abs y). apply abs_always_nonneg. auto.
  revert Ez1.
  auto.

  Case "abs y > x".
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

