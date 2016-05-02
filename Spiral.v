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


(* 0 ... n-1*)
Program Fixpoint natrange (n:nat) : (vector nat n) :=
  match n return (vector nat n) with
    0 => Vnil
  | S p => snoc (natrange p) p
  end.

(* n-1 ... 0*)
Program Fixpoint rev_natrange (n:nat) : (vector nat n) :=
  match n return (vector nat n) with
    0 => Vnil
  | S p => Vcons p (rev_natrange p)
  end.

Local Open Scope nat_scope.
Lemma vin_rev_natrange x n:
  Vin x (rev_natrange n) <-> (x<n).
Proof.
  split.
  + intros.
    induction n; crush.
  + intros.
    induction n.
    crush.
    simpl.
    assert (XN: x ≡ n \/ x < n).
    crush.
    decompose sum XN.
  - left. auto.
  - right.
    apply IHn.
    assumption.
Qed.

Lemma vnth_natrange {n} (i:nat) (ip:i<n):
  Vnth (rev_natrange n) ip ≡ (pred n) - i.
Proof.
  revert i ip.
  dependent induction n.
  + intros. crush.
  + simpl (rev_natrange (S n)).
    intros.
    simpl (pred (S n)).
    destruct i.
    rewrite <- minus_n_O.
    apply Vnth_cons_head.
    reflexivity.
    remember (S i) as j.
    assert (JP: j>0) by omega.
    rewrite Vnth_cons_tail with (h2:=JP).
    rewrite IHn.
    omega.
Qed.

Lemma vnth_natrange_sn {n} (i:nat) (ip:i<(S n)):
  Vnth (rev_natrange (S n)) ip ≡ n - i.
Proof.
  revert i ip.
  dependent induction n.
  + unfold rev_natrange.
    intros.
    apply Vnth_cons_head.
    omega.
  + intros.
    replace (rev_natrange (S (S n))) with (S n :: rev_natrange (S n)) by auto.
    destruct i.
    crush.
    remember (S i) as j.
    assert (JP: j>0) by omega.
    rewrite Vnth_cons_tail with (h2:=JP).
    rewrite IHn.
    omega.
Qed.

(*
Lemma vmap_natrange `{Equiv B} {n:nat} (f: nat->B) (v: vector B n):
  (Vmap f (rev_natrange n) ≡ v)
  <->
  (forall (i:nat) (ip:i<n), Vnth v ip ≡ f ((pred n) - i)).
Proof.
  split.
  + intros M i ip.
    rewrite <- M.
    rewrite Vnth_map.
    rewrite vnth_natrange.
    reflexivity.
  + intros M.

Qed.
 *)

Local Close Scope nat_scope.

Lemma hd0: natrange 0 ≡ [].
Proof.
  reflexivity.
Qed.

Lemma hd_natrange1: forall n, hd (natrange (S n)) ≡ O.
Proof.
  intros.
  simpl.
  induction n.
  auto.
  rewrite snoc2cons.
  simpl.
  apply IHn.
Qed.


Lemma last_natrange: forall n, last (natrange (S n)) ≡ n.
Proof.
  intros.
  induction n.
  auto.
  simpl.
  rewrite last_snoc.
  reflexivity.
Qed.

Lemma shifhout_natrange: forall n, shiftout (natrange (S n)) ≡ natrange n.
Proof.
  intros.
  dependent destruction n.
  auto.
  simpl.
  rewrite shiftout_snoc.
  reflexivity.
Qed.

Lemma tl_natrange: forall n, tl (natrange (S n)) ≡ map (S) (natrange n).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  simpl in IHn.
  rewrite tl_snoc1.
  rewrite IHn. clear IHn.
  replace (snoc (natrange n) n) with (natrange (S n)) by reflexivity.

  rewrite map_snoc.
  rewrite last_natrange.
  rewrite shifhout_natrange.
  reflexivity.
Qed.


Local Open Scope nat_scope.

Lemma One_ne_Zero: 1 ≢ 0.
Proof.
  auto.
Qed.

Lemma  plus_lt_subst_r: forall a b b' c,  b' < b -> a + b < c -> a + b' < c.
Proof.
  intros. omega.
Qed.

Lemma  plus_le_subst_r: forall a b b' c,  b' <= b -> a + b < c -> a + b' < c.
Proof.
  intros. omega.
Qed.

Lemma le_mius_minus : forall a b c, a>=(b+c) -> a-b-c ≡ a - (b+c).
Proof.
  intros.
  omega.
Qed.

Lemma nez2gt: forall n, 0 ≢ n -> gt n 0.
Proof.
  intros.
  omega.
Defined.

Lemma neq_nat_to_neq {a b:nat} (e: ¬eq_nat a b): a ≢ b.
Proof.
  crush.
Defined.

Lemma modulo_smaller_than_devisor:
  ∀ x y : nat, 0 ≢ y → x mod y < y.
Proof.
  intros.
  destruct y; try congruence.
  unfold PeanoNat.Nat.modulo.
  omega.
Qed.

Lemma le_pred_l {n m} (H: S n <= m): n <= m.
Proof.
  auto with arith.
Defined.

Local Close Scope nat_scope.

Close Scope vector_scope.

Lemma Vnth_index_equiv `{Setoid A}: forall n (v : vector A n) i1 (h1 : i1<n) i2 (h2 : i2<n),
    i1 = i2 -> Vnth v h1 = Vnth v h2.
Proof.
  induction v; intro; case i1.
  - intro.
    nat_lt_0_contradiction; omega.
  - intros n h1.
    nat_lt_0_contradiction; omega.
  - intros.
    revert h2. rewrite <- H0. intros h2.
    reflexivity.
  - intros.
    revert h2. rewrite <- H0. intros h2.
    simpl.
    apply IHv.
    reflexivity.
Qed.

Lemma Vnth_arg_equiv:
  ∀ (A : Type) (Ae : Equiv A) (n : nat) (v1 v2 : vector A n)
    (i : nat) (ip : i < n), v1 = v2 → Vnth v1 ip = Vnth v2 ip.
Proof.
  intros A Ae n v1 v2 i ip E.
  unfold equiv, vec_Equiv in E.
  apply Vforall2_elim_nth with (i:=i) (ip:=ip) in E.
  assumption.
Qed.

Lemma Vnth_equiv `{Setoid A}: forall n (v1 v2 : vector A n) i1 (h1 : i1<n) i2 (h2 : i2<n),
    i1 = i2 -> v1 = v2 -> Vnth v1 h1 = Vnth v2 h2.
Proof.
  intros n v1 v2 i1 h1 i2 h2 Ei Ev.
  rewrite (@Vnth_index_equiv A Ae H n v1 i1 h1 i2 h2) by assumption.
  apply Vnth_arg_equiv.
  assumption.
Qed.


Section VMap2_Indexed.

  Local Open Scope nat_scope.

  Definition Vmap2Indexed {A B C : Type} {n}
             (f: nat->A->B->C) (a: vector A n) (b: vector B n)
    := Vbuild (fun i ip => f i (Vnth a ip) (Vnth b ip)).

  Global Instance Vmap2Indexed_proper
         `{Setoid A, Setoid B, Setoid C} {n:nat}
    :
      Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
             (@Vmap2Indexed A B C n).
  Proof.
    intros fa fb Ef a a' Ea b b' Eb.
    unfold Vmap2Indexed.

    unfold equiv, vec_Equiv.
    apply Vforall2_intro_nth.
    intros i ip.
    rewrite 2!Vbuild_nth.
    apply Ef.
    - reflexivity.
    - apply Vnth_equiv.
      reflexivity.
      assumption.
    - apply Vnth_equiv.
      reflexivity.
      assumption.
  Qed.

  Lemma Vnth_Vmap2Indexed:
    forall {A B C : Type} {n:nat} (i : nat) (ip : i < n) (f: nat->A->B->C)
           (a:vector A n) (b:vector B n),
      Vnth (Vmap2Indexed f a b) ip ≡ f i (Vnth a ip) (Vnth b ip).
  Proof.
    intros A B C n i ip f a b.
    unfold Vmap2Indexed.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

End VMap2_Indexed.

