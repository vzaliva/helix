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
Require Import Coq.Lists.List.

Require Import VecUtil.

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

Global Instance Nat_Spec_Equiv {n:nat}: Equiv {i | (i<n)%nat} := sig_equiv _.

(* Various definitions related to vector equality and setoid rewriting *)

Instance vec_equiv `{Equiv A} {n}: Equiv (vector A n) := Vforall2 (n:=n) equiv.

Instance vec_Equivalence `{Ae: Equiv A} {n:nat}
         `{!Equivalence (@equiv A _)}
  : Equivalence (@vec_equiv A Ae n).
Proof.
  unfold vec_equiv.
  apply Vforall2_equiv.
  assumption.
Qed.

Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
Proof.
  unfold Setoid.
  apply vec_Equivalence.
Qed.

Section Vfold_right_p.
  Context
    `{eqA: Equiv A}
    `{eqB: Equiv B}.

  Definition Vfold_right_reord {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B): B := @Vfold_right A B f n v initial.

  Lemma Vfold_right_to_Vfold_right_reord: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
      Vfold_right f v initial ≡ Vfold_right_reord f v initial.
  Proof.
    crush.
  Qed.

  Global Instance Vfold_right_reord_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> (@vec_equiv A _ n ==> (=) ==> (=)))
           (@Vfold_right_reord A B n).
  Proof.
    intros f f' Ef v v' vEq i i' iEq.
    unfold Vfold_right_reord.
    induction v.
    Case "N=0".
    VOtac. simpl. assumption.
    Case "S(N)".
    revert vEq. VSntac v'. unfold vec_equiv. rewrite Vforall2_cons_eq. intuition. simpl.
    apply Ef.
    SCase "Pf - 1".
    assumption.
    SCase "Pf - 2".
    apply IHv. unfold vec_equiv.  assumption.
  Qed.

End Vfold_right_p.

Section VCons_p.
  Definition Vcons_reord {A} {n} (t: vector A n) (h:A): vector A (S n) := Vcons h t.

  Lemma Vcons_to_Vcons_reord: forall A n (t: t A n) (h:A), Vcons h t  ≡ Vcons_reord t h.
  Proof.
    crush.
  Qed.

  Global Instance Vcons_reord_proper `{Equiv A} n:
    Proper ((=) ==> (=) ==> (=))
           (@Vcons_reord A n).
  Proof.
    split.
    assumption.
    unfold vec_equiv, Vforall2 in H0.  assumption.
  Qed.

End VCons_p.

Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
  Proper ((=) ==>  (=) ==> (=)) (@Vapp A n1 n2).
Proof.
  intros a0 a1 aEq b0 b1 bEq.
  induction n1.
  VOtac. auto.

  dep_destruct a0.
  dep_destruct a1.
  rewrite 2!Vapp_cons.

  assert (h=h0).
  apply aEq.

  rewrite 2!Vcons_to_Vcons_reord.
  rewrite H.
  rewrite <- 2!Vcons_to_Vcons_reord.

  unfold equiv, vec_equiv.
  apply Vforall2_cons_eq.
  split. reflexivity.

  unfold equiv, vec_equiv in IHn1.
  apply IHn1.
  apply aEq.
Qed.


Instance Vhead_proper A `{H:Equiv A} n:
  Proper (@equiv (vector A (S n)) (@vec_equiv A H (S n)) ==> @equiv A H) (@Vhead A n).
Proof.
  intros a b E.
  dep_destruct a.  dep_destruct b.
  unfold equiv, vec_equiv, vec_equiv, relation in E.
  rewrite Vforall2_cons_eq in E.
  intuition.
Defined.

Instance Vtail_proper `{Equiv A} n:
  Proper (@vec_equiv A _ (S n) ==> @vec_equiv A _ n)
         (@Vtail A n).
Proof.
  intros a b E.
  unfold equiv, vec_equiv, vec_equiv, relation in E.
  apply Vforall2_tail in E.
  unfold vec_equiv.
  assumption.
Defined.

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


Section Natrange_List.
  (* Probably will be removed later *)

  (* n-1 ... 0 *)
  Fixpoint rev_natrange_list (n:nat) : list nat :=
    match n with
    | 0 => List.nil
    | S p => List.cons p (rev_natrange_list p)
    end.

  (* 0 ...  n-1  *)
  Definition natrange_list (n:nat) : list nat :=
    List.rev (rev_natrange_list n).

  Lemma rev_natrange_len:
    ∀ i : nat, Datatypes.length (rev_natrange_list i) ≡ i.
  Proof.
    intros.
    induction i.
    crush.
    simpl.
    rewrite IHi.
    reflexivity.
  Qed.

  Lemma rev_natrange_list_bound:
    ∀ z x : nat, List.In x (rev_natrange_list z) → (x < z)%nat.
  Proof.
    intros.
    induction z.
    + compute in H.
      contradiction.
    + crush.
  Qed.

  Lemma natrange_list_bound:
    ∀ z x : nat, List.In x (natrange_list z) → (x < z)%nat.
  Proof.
    unfold natrange_list.
    intros.
    rewrite <- in_rev in H.
    apply rev_natrange_list_bound.
    assumption.
  Qed.
End Natrange_List.

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

Lemma Vmap_equiv_cons: forall A B `{Setoid B} (f:A->B) n (x:A) (xs: vector A n),
    Vmap f (Vcons x xs) = Vcons (f x) (Vmap f xs).
Proof.
  intros.
  constructor. reflexivity.
  fold (Vforall2 (n:=n) equiv (Vmap f xs) (Vmap f xs)).
  fold (vec_equiv (Vmap f xs) (Vmap f xs)).
  fold (equiv (Vmap f xs) (Vmap f xs)).
  reflexivity.
Qed.

Lemma Vmap2_cons_hd: forall A B C `{Setoid C} (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)),
    Vmap2 f a b = @cons _ (f (Vhead a) (Vhead b)) _ (Vmap2 f (Vtail a) (Vtail b)).
Proof.
  intros.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
Qed.

Lemma Vmap2_cons: forall A B C `{Setoid C} (f:A->B->C) n (a:A) (b:B) (a':vector A n) (b':vector B n),
    Vmap2 f (a::a') (b::b') = @cons _ (f a b) _ (Vmap2 f a' b').
Proof.
  intros.
  reflexivity.
Qed.

Lemma Vmap2_comm
      `{CO:Commutative B A f}
      `{SB: !Setoid B} {n:nat}:
  Commutative (Vmap2 f (n:=n)).
Proof.
  unfold Commutative.
  intros a b.
  induction n.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
  rewrite Vmap2_cons_hd by apply SB.

  (* reorder LHS head *)

  rewrite Vcons_to_Vcons_reord.
  rewrite commutativity.
  rewrite <- IHn. (* reoder LHS tail *)
  setoid_rewrite <- Vmap2_cons.
  reflexivity.
  assumption.
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


Lemma hd_equiv: forall `{Setoid A} {n} (u v: vector A (S n)), u=v -> (Vhead u) = (Vhead v).
Proof.
  intros.
  rewrite H0.
  f_equiv.
Qed.

Lemma Vcons_equiv_elim `{Equiv A}: forall a1 a2 n (v1 v2 : vector A n),
    Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.
Proof.
  intros. auto.
Qed.

Lemma Vcons_equiv_intro `{Setoid A} : forall a1 a2 n (v1 v2 : vector A n),
    a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.
Proof.
  intros.
  rewrite 2!Vcons_to_Vcons_reord.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Lemma Vcons_single_elim `{Equiv A} : forall a1 a2,
    Vcons a1 (@Vnil A) = Vcons a2 (@Vnil A) <-> a1 = a2.
Proof.
  intros a1 a2.
  unfold equiv, vec_equiv.
  rewrite Vforall2_cons_eq.
  assert(Vforall2 equiv (@Vnil A) (@Vnil A)).
  constructor.
  split; tauto.
Qed.

(* Utlity functions for vector products *)

Section VectorPairs.
  Definition Phead {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): A*B
    := match ab with
       | (va,vb) => ((Vhead va), (Vhead vb))
       end.

  Definition Ptail {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): (vector A n)*(vector B n)
    := match ab with
       | (va,vb) => ((Vtail va), (Vtail vb))
       end.

  Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
    Proper ((=) ==> (=)) (@Ptail A B n).
  Proof.
    intros x y E.
    destruct x as [xa xb].
    destruct y as [ya yb].
    destruct E as [E1 E2].
    simpl in E1. simpl in E2.
    unfold Ptail.
    rewrite E1, E2.
    reflexivity.
  Qed.
End VectorPairs.

Definition Vmap_reord (A B: Type) (n:nat) (f:A->B) (x: vector A n): vector B n := Vmap f x.

Lemma Vmap_to_Vmap_reord: forall (A B: Type) (n:nat) (f:A->B) (x: vector A n), @Vmap A B f n x ≡ @Vmap_reord A B n f x.
Proof.
  crush.
Qed.

Instance Vmap_reord_proper n (M N:Type) `{Ne:!Equiv N, Me:!Equiv M}:
  Proper (((=) ==> (=)) ==> (=) ==> (=))
         (@Vmap_reord M N n).
Proof.
  intros f g Eext a b Ev.
  induction n.
  Case "N=0".
  VOtac. auto.
  Case "S N".
  dep_destruct a. dep_destruct b.
  split.
  apply Eext, Ev.
  apply IHn, Ev.
Qed.

Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
         `{fP: !Proper (Me ==> Ne) f} (n:nat):
  Proper ((@vec_equiv M _ n) ==> (@vec_equiv N _ n)) (@Vmap M N f n).
Proof.
  intros a b Ea.
  unfold vec_equiv.
  induction n.
  Case "N=0".
  VOtac. auto.
  Case "S N".
  dep_destruct a. dep_destruct b.
  split.
  apply fP, Ea.
  apply IHn, Ea.
Qed.

Definition Lst {B:Type} (x:B) := [x].

Instance VBreak_proper (A:Type) `{Setoid A} (n1 n2:nat) `{Plus nat}:
  Proper ((=) ==> (=)) (@Vbreak A n1 n2).
Proof.
  intros v v1 vE.
  induction n1.
  simpl. setoid_rewrite vE. reflexivity.
  assert (V1: v ≡ Vapp (fst (Vbreak (n1:=1) v)) (snd (Vbreak (n1:=1) v))).
  simpl. dep_destruct v. reflexivity.
  assert (V2: v1 ≡ Vapp (fst (Vbreak (n1:=1) v1)) (snd (Vbreak (n1:=1) v1))).
  simpl. dep_destruct v1. reflexivity.
  rewrite V1. clear V1. rewrite V2. clear V2.
  dep_destruct v. dep_destruct v1.
  simpl.

  rewrite 2!Vcons_to_Vcons_reord.
  assert (E: Vbreak x = Vbreak x0).
  apply IHn1.  apply vE.
  rewrite E.
  setoid_replace h with h0 by apply vE.
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

Lemma Vin_cons:
  ∀ (T:Type) (h : T) (n : nat) (v : vector T n) (x : T),
    Vin x (Vcons h v) → x ≡ h ∨ Vin x v.
Proof.
  crush.
Qed.

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

Lemma  fold_left_once:
  forall (A B:Type) (x:B) (xs:list B) (b:A) (f:A->B->A),
    List.fold_left f (x::xs) b ≡ List.fold_left f xs (f b x).
Proof.
  auto.
Qed.

Lemma fold_left_map {A B M} (ff:A -> B -> A) (fm:M->B) (l:list M) (a0:A):
  List.fold_left ff (List.map fm l) a0 ≡ List.fold_left (fun a m => ff a (fm m)) l a0.
Proof.
  generalize a0.
  induction l.
  + auto.
  + simpl.
    intros.
    rewrite IHl.
    reflexivity.
Qed.


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
  unfold equiv, vec_equiv in E.
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

    unfold equiv, vec_equiv.
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

