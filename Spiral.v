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

Require Import CaseNaming.
Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.
Require Import Psatz.

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

(* equality of option types *)
Instance opt_Equiv `{Equiv A}: Equiv (option A) :=
  fun a b =>
    match a with
    | None => is_None b
    | Some x => (match b with
                | None => False
                | Some y => equiv x y
                end)
    end.

Instance opt_Setoid `{Setoid A}: Setoid (@option A).
Proof.
  unfold Setoid in H.
  constructor. destruct H.
  unfold Reflexive. destruct x; (unfold equiv; crush).
  unfold Symmetric. intros. destruct x,y; (unfold equiv; crush).
  unfold Transitive. intros. destruct x,y,z; unfold equiv, opt_Equiv in *; crush.
Qed.

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
    `{eqB: Equiv B}
    (f : A->B->B)
    `{pF: !Proper ((=) ==> (=) ==> (=)) f}.

  Definition Vfold_right_reord {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B): B := @Vfold_right A B f n v initial.

  Lemma Vfold_right_to_Vfold_right_reord: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
      Vfold_right f v initial ≡ Vfold_right_reord f v initial.
  Proof.
    crush.
  Qed.

  Global Instance Vfold_right_reord_proper n :
    Proper (@vec_equiv A _ n ==> (=) ==> (=)) (@Vfold_right_reord A B n f).
  Proof.
    intros v v' vEq i i' iEq.
    unfold Vfold_right_reord.
    induction v.
    Case "N=0".
    VOtac. simpl. assumption.
    Case "S(N)".
    revert vEq. VSntac v'. unfold vec_equiv. rewrite Vforall2_cons_eq. intuition. simpl.
    apply pF.
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
    Proper (@vec_equiv A _ n ==> (=) ==> @vec_equiv A _ (S n))
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
  Proper ((=) ==> (=) ==> (=)) (max).
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
  assumption. assumption. assumption. assumption.
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

Open Scope vector_scope.

Notation "h :: t" := (cons h t) (at level 60, right associativity)
                     : vector_scope.

Fixpoint take_plus {A} {m} (p:nat) : vector A (p+m) -> vector A p :=
  match p return vector A (p+m) -> vector A p with
    0%nat => fun _ => Vnil
  | S p' => fun a => Vcons (hd a) (take_plus p' (tl a))
  end.
Program Definition take A n p (a : vector A n) (H : p <= n) : vector A p :=
  take_plus (m := n - p) p a.
Solve Obligations using auto with arith.

Fixpoint drop_plus {A} {m} (p:nat) : vector A (p+m) -> vector A m :=
  match p return vector A (p+m) -> vector A m with
    0 => fun a => a
  | S p' => fun a => drop_plus p' (tl a)
  end.
Program Definition drop A n p (a : vector A n) (H : p <= n) : vector A (n-p) :=
  drop_plus (m := n - p) p a.
Solve Obligations using auto with arith.

(* Split vector into a pair: first  'p' elements and the rest. *)
Definition vector2pair {A:Type} (p:nat) {t:nat} (v:vector A (p+t)) : (vector A p)*(vector A t) :=
  @Vbreak A p t v.

(* Split vector into a pair: first  'p' elements and the rest. *)
Definition pair2vector {A:Type} {i j:nat} (p:(vector A i)*(vector A j)) : (vector A (i+j))  :=
  match p with
    (a,b) => Vapp a b
  end.

Lemma vp2pv: forall {T:Type} i1 i2 (p:((vector T i1)*(vector T i2))),
    vector2pair i1 (pair2vector p) ≡ p.
Proof.
  intros.
  unfold vector2pair.
  destruct p.
  unfold pair2vector.
  apply Vbreak_app.
Qed.

(* reverse CONS, append single element to the end of the list *)
Program Fixpoint snoc {A} {n} (l:vector A n) (v:A) : (vector A (S n)) :=
  match l with
  | nil => [v]
  | h' :: t' => Vcons h' (snoc t' v)
  end.

Notation "h ;; t" := (snoc h t) (at level 60, right associativity).

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

Lemma hd_cons {A} {n} (h:A) {t: vector A n}: Vhead (Vcons h t) ≡ h.
Proof.
  reflexivity.
Qed.

Lemma hd_snoc0: forall {A} (l:vector A 0) v, hd (snoc l v) ≡ v.
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.

Lemma hd_snoc1: forall {A} {n} (l:vector A (S n)) v, hd (snoc l v) ≡ hd l.
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.

Lemma tl_snoc1: forall {A} {n} (l:vector A (S n)) v, tl (snoc l v) ≡ snoc (tl l) v.
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.

Lemma snoc2cons: forall {A} (n:nat) (l:vector A (S n)) v,
    snoc l v ≡ @cons _ (hd l) _ (snoc (tl l) v).
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.


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


Lemma last_snoc: forall A n (l:vector A n) v, last (snoc l v) ≡ v.
Proof.
  intros.
  induction l.
  auto.
  rewrite snoc2cons.
  simpl.
  assumption.
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

Lemma map_nil: forall A B (f:A->B), map f [] ≡ [].
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma map2_nil: forall A B C (f:A->B->C), map2 f [] [] ≡ [].
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma map_hd: forall A B (f:A->B) n (v:vector A (S n)), hd (map f v) ≡ f (hd v).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma Vmap_cons: forall A B (f:A->B) n (x:A) (xs: vector A n),
    Vmap f (Vcons x xs) ≡ Vcons (f x) (Vmap f xs).
Proof.
  intros.
  constructor.
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

Lemma map_cons: forall A B n (f:A->B) (v:vector A (S n)),
    map f v ≡ @cons _ (f (hd v)) _ (map f (tl v)).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma map2_cons: forall A B C (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)),
    map2 f a b ≡ @cons _ (f (hd a) (hd b)) _ (map2 f (tl a) (tl b)).
Proof.
  intros.
  dep_destruct a.
  dep_destruct b.
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

Lemma VMapp2_app:
  ∀ {A B} {f: A->A->B} (n m : nat)
    {a b: vector A m} {a' b':vector A n},
    Vmap2 f (Vapp a a') (Vapp b b')
          ≡ Vapp (Vmap2 f a b) (Vmap2 f a' b').
Proof.
  intros A B f n m a b a' b'.
  induction m.
  - VOtac.
    reflexivity.
  - VSntac a. VSntac b.
    simpl.
    rewrite IHm.
    reflexivity.
Qed.

Lemma shifout_tl_swap: forall {A} n (l:vector A (S (S n))),
    tl (shiftout l) ≡ shiftout (tl l).
Proof.
  intros.
  dep_destruct l.
  simpl.
  reflexivity.
Qed.

Lemma last_tl: forall {A} n (l:vector A (S (S n))),
    last (tl l) ≡ last l.
Proof.
  intros.
  dep_destruct l.
  simpl.
  reflexivity.
Qed.

Lemma map_snoc: forall A B n (f:A->B) (l:vector A (S n)),
    map f l ≡ snoc (map f (shiftout l)) (f (last l)).
Proof.
  intros.
  induction n.
  Case "n=0".
  dep_destruct l.
  assert (L: last (h::x) ≡ h).
  SCase "L".
  dep_destruct x.
  reflexivity.
  rewrite L.
  assert (S: forall (z:vector A 1), shiftout z ≡ []).
  SCase "S".
  intros.
  dep_destruct z.
  dep_destruct x0.
  reflexivity.
  dep_destruct x.
  rewrite S.
  simpl.
  reflexivity.
  Case "S n".
  rewrite map_cons.
  rewrite IHn.  clear_all.
  symmetry.
  rewrite snoc2cons.
  rewrite map_cons.
  assert (HS: hd (shiftout l) ≡ hd l).
  dep_destruct l.
  reflexivity.
  rewrite HS. clear_all.
  simpl (hd (f (hd l) :: map f (tl (shiftout l)))).
  assert (L:(tl (f (hd l) :: map f (tl (shiftout l)))) ≡ (map f (shiftout (tl l)))).
  simpl. rewrite shifout_tl_swap. reflexivity.
  rewrite L. rewrite last_tl. reflexivity.
Qed.


Lemma map2_snoc: forall A B C (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)),
    map2 f a b ≡ snoc (map2 f (shiftout a) (shiftout b)) (f (last a) (last b)).
Proof.
  intros.
  induction n.
  Case "n=0".
  dep_destruct a.
  dep_destruct b.
  assert (L: forall T hl (xl:t T 0), last (hl::xl) ≡ hl).
  SCase "L".
  intros.
  dep_destruct xl.
  reflexivity.
  repeat rewrite L.
  assert (S: forall T (z:t T 1), shiftout z ≡ []).
  SCase "S".
  intros.
  dep_destruct z.
  dep_destruct x1.
  reflexivity.
  dep_destruct x.
  dep_destruct x0.
  repeat rewrite S.
  simpl.
  reflexivity.
  Case "S n".
  rewrite map2_cons.
  rewrite IHn.  clear_all.
  symmetry.
  repeat rewrite snoc2cons.
  repeat rewrite map2_cons.
  assert (HS: forall T m (l:t T (S (S m))), hd (shiftout l) ≡ hd l).
  intros. dep_destruct l. reflexivity.
  repeat rewrite HS. clear_all.
  simpl (hd (f (hd a) (hd b) :: map2 f (tl (shiftout a)) (tl (shiftout b)))).

  assert(L:(tl (f (hd a) (hd b) :: map2 f (tl (shiftout a)) (tl (shiftout b)))) ≡ (map2 f (shiftout (tl a)) (shiftout (tl b)))).
  simpl. repeat rewrite shifout_tl_swap. reflexivity.
  rewrite L. repeat rewrite last_tl. reflexivity.
Qed.


Lemma map2_comm: forall A B (f:A->A->B) n (a b:vector A n),
    (forall x y, (f x y) ≡ (f y x)) -> map2 f a b ≡ map2 f b a.
Proof.
  intros.
  induction n.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
  rewrite -> map2_cons.
  rewrite H. (* reorder LHS head *)
  rewrite <- IHn. (* reoder LHS tail *)
  rewrite <- map2_cons.
  reflexivity.
Qed.

Lemma Vmap2_comm : forall `{CO:Commutative B A f} `{SB: !Setoid B},
    forall n:nat, Commutative (Vmap2 f (n:=n)).
Proof.
  intros.
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


(* Shows that two map2 supplied with function which ignores 2nd argument
will be eqivalent for all values of second list *)
Lemma map2_ignore_2: forall A B C (f:A->B->C) n (a:vector A n) (b0 b1:vector B n),
    (forall a' b0' b1', f a' b0' ≡ f a' b1') ->
    map2 f a b0 ≡ map2 f a b1 .
Proof.
  intros.
  induction a.
  dep_destruct (map2 f [] b1).
  dep_destruct (map2 f [] b0).
  reflexivity.
  rewrite 2!map2_cons.
  simpl.
  rewrite -> H with (a':=h) (b0':=(hd b0)) (b1':=(hd b1)).
  assert(map2 f a (tl b0) ≡ map2 f a (tl b1)).
  apply(IHa).
  rewrite <- H0.
  reflexivity.
Qed.


(* Shows that two map2 supplied with function which ignores 1st argument
will be eqivalent for all values of first list *)
Lemma map2_ignore_1: forall A B C (f:A->B->C) n (a0 a1:vector A n) (b:vector B n),
    (forall a0' a1' b', f a0' b' ≡ f a1' b') ->
    map2 f a0 b ≡ map2 f a1 b .
Proof.
  intros.
  induction b.
  dep_destruct (map2 f a0 []).
  dep_destruct (map2 f a1 []).
  reflexivity.
  rewrite 2!map2_cons.
  simpl.
  rewrite -> H with (b':=h) (a0':=(hd a0)) (a1':=(hd a1)).
  assert(map2 f (tl a0) b ≡ map2 f (tl a1) b).
  apply(IHb).
  rewrite <- H0.
  reflexivity.
Qed.

Lemma shiftout_snoc: forall A n (l:vector A n) v, shiftout (snoc l v) ≡ l.
Proof.
  intros.
  induction l.
  auto.
  simpl.
  rewrite IHl.
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

Lemma fold_right_reduce: forall A B n (f:A->B->B) (id:B) (v:vector A (S n)),
    fold_right f v id ≡ f (hd v) (fold_right f (tl v) id).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma Vfold_left_1
      {B C : Type} (f: C → B → C) {z: C} {v:vector B 1}:
  Vfold_left f z v ≡ f z (Vhead v).
Proof.
  dep_destruct v.
  simpl.
  replace x with (@Vnil B).
  simpl.
  reflexivity.
  symmetry.
  dep_destruct x.
  reflexivity.
Qed.

Lemma Vfold_right_reduce: forall A B n (f:A->B->B) (id:B) (v:vector A (S n)),
    Vfold_right f v id ≡ f (hd v) (Vfold_right f (tl v) id).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma Vfold_right_fold_right: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
    Vfold_right f v initial ≡ @fold_right A B f n v initial.
Proof.
  intros.
  induction v.
  reflexivity.
  rewrite fold_right_reduce.
  simpl.
  rewrite <- IHv.
  reflexivity.
Qed.

Lemma Vfold_left_app : forall {A B:Type} {m n} (f:B → A → B) (l:vector A m) (l': vector A n) (i:B),
    Vfold_left f i (Vapp l l') ≡ Vfold_left f (Vfold_left f i l') l.
Proof.
  intros A B m n f l l' i.
  induction l; simpl.
  + reflexivity.
  + rewrite IHl.
    reflexivity.
Qed.

(* It directly follows from definition, but haiving it as sepearate lemma helps to do rewiring *)
Lemma Vfold_left_cons:
  forall A B {n} (f : B->A->B) (b:B) (x: A) (xs : vector A n),
    Vfold_left f b (Vcons x xs) ≡ f (Vfold_left f b xs) x.
Proof.
  crush.
Qed.

Lemma rev_nil: forall A, rev (@nil A) ≡ [].
Proof.
  intros A.
  unfold rev.
  assert (rev_append (@nil A) (@nil A) ≡ (@nil A)).
  unfold rev_append.
  assert (rev_append_tail (@nil A) (@nil A) ≡ (@nil A)).
  auto.
  rewrite H. clear_all.
  dep_destruct (plus_tail_plus 0 0).
  auto.
  rewrite H. clear_all.
  dep_destruct (plus_n_O 0).
  auto.
Qed.

Lemma hd_eq: forall A n (u v: vector A (S n)), u≡v -> (hd u) ≡ (hd v).
Proof.
  intros.
  rewrite H.
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

Definition Vmap_reord (A B: Type) (n:nat) (f:A->B) (x: vector A n): vector B n := Vmap f x.

Lemma Vmap_to_Vmap_reord: forall (A B: Type) (n:nat) (f:A->B) (x: vector A n), @Vmap A B f n x ≡ @Vmap_reord A B n f x.
Proof.
  crush.
Qed.

Instance Vmap_reord_proper_ext_equiv n  (M N:Type) `{Ne:!Equiv N, Me:!Equiv M}:
  Proper (@ext_equiv M Me N Ne
                     ==> @vec_equiv M Me n
                     ==> @vec_equiv N Ne n)
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

Lemma Vbreak_arg_app:
  ∀ {B} (m n : nat) (x : vector B (m + n)) (a: vector B m) (b: vector B n),
    Vbreak x ≡ (a, b) → x ≡ Vapp a b.
Proof.
  intros B m n x a b V.
  rewrite Vbreak_eq_app with (v:=x).
  rewrite V.
  reflexivity.
Qed.

Lemma Vbreak_preserves_values {A} {n1 n2} {x: vector A (n1+n2)} {x0 x1}:
  Vbreak x ≡ (x0, x1) ->
  forall a, Vin a x <-> ((Vin a x0) \/ (Vin a x1)).
Proof.
  intros B a.
  apply Vbreak_arg_app in B.
  subst.
  split.
  apply Vin_app.
  intros.
  destruct H.
  apply Vin_appl; assumption.
  apply Vin_appr; assumption.
Qed.

Lemma Vbreak_preserves_P {A} {n1 n2} {x: vector A (n1+n2)} {x0 x1} {P}:
  Vbreak x ≡ (x0, x1) ->
  (Vforall P x -> ((Vforall P x0) /\ (Vforall P x1))).
Proof.
  intros B D.
  assert(N: forall a, Vin a x → P a).
  {
    intros a.
    apply Vforall_in with (v:=x); assumption.
  }
  (split;
   apply Vforall_intro; intros x2 H;
   apply N;
   apply Vbreak_preserves_values with (a:=x2) in B;
   destruct B as [B0 B1];
   apply B1) ;
    [left | right]; assumption.
Qed.

Lemma Vforall_hd {A:Type} {P:A->Prop} {n:nat} {v:vector A (S n)}:
  Vforall P v -> P (Vhead v).
Proof.
  dep_destruct v.
  simpl.
  tauto.
Qed.

Lemma Vforall_tl {A:Type} {P:A->Prop} {n:nat} {v:vector A (S n)}:
  Vforall P v -> Vforall P (Vtail v).
Proof.
  dep_destruct v.
  simpl.
  tauto.
Qed.

Lemma Vforall_nil:
  ∀ B (P:B->Prop), Vforall P (@Vnil B).
Proof.
  crush.
Qed.

Lemma Vforall_cons {B:Type} {P:B->Prop} {n:nat} {x:B} {xs:vector B n}:
  (P x /\ Vforall P xs) ≡ Vforall P (cons x xs).
Proof.
  auto.
Qed.

Lemma Vforall_1 {B: Type} {P} (v: vector B 1):
  Vforall P v <-> P (Vhead v).
Proof.
  split.
  +
    dep_destruct v.
    simpl.
    replace (Vforall P x) with True; simpl.
    tauto.
    replace x with (@Vnil B).
    simpl; reflexivity.
    dep_destruct x; reflexivity.
  + dep_destruct v.
    simpl.
    replace (Vforall P x) with True; simpl.
    tauto.
    replace x with (@Vnil B).
    simpl; reflexivity.
    dep_destruct x; reflexivity.
Qed.

Lemma vec_eq_elementwise n B (v1 v2: vector B n):
  Vforall2 eq v1 v2 -> (v1 ≡ v2).
Proof.
  induction n.
  + dep_destruct v1. dep_destruct v2.
    auto.
  + dep_destruct v1. dep_destruct v2.
    intros H.
    rewrite Vforall2_cons_eq in H.
    destruct H as [Hh Ht].
    apply IHn in Ht.
    rewrite Ht, Hh.
    reflexivity.
Qed.

Lemma Vmap_Vbuild n B C (fm: B->C) (fb : ∀ i : nat, i < n → B):
  Vmap fm (Vbuild fb) ≡ Vbuild (fun z zi => fm (fb z zi)).
Proof.
  apply vec_eq_elementwise.
  apply Vforall2_intro_nth.
  intros i ip.
  rewrite Vnth_map.
  rewrite 2!Vbuild_nth.
  reflexivity.
Qed.

Local Open Scope nat_scope.

Lemma One_ne_Zero: 1 ≢ 0.
Proof.
  auto.
Qed.

Lemma Vbuild_0:
  forall B gen, @Vbuild B 0 gen ≡ @Vnil B.
Proof.
  intros B gen.
  auto.
Qed.

Lemma Vbuild_1 B gen:
  @Vbuild B 1 gen ≡ [gen 0 (lt_0_Sn 0)].
Proof.
  unfold Vbuild.
  simpl.
  replace (Vbuild_spec_obligation_4 gen eq_refl) with (lt_0_Sn 0) by apply proof_irrelevance.
  reflexivity.
Qed.

Fact lt_0_SSn:  forall n:nat, 0<S (S n). Proof. intros;omega. Qed.

Fact lt_1_SSn:  forall n:nat, 1<S (S n). Proof. intros; omega. Qed.

Lemma Vbuild_2 B gen:
  @Vbuild B 2 gen ≡ [gen 0 (lt_0_SSn 0) ; gen 1 (lt_1_SSn 0)].
Proof.
  unfold Vbuild.
  simpl.
  replace (Vbuild_spec_obligation_4 gen eq_refl) with (lt_0_SSn 0) by apply proof_irrelevance.
  replace (Vbuild_spec_obligation_3 gen eq_refl
                                    (Vbuild_spec_obligation_4
                                       (λ (i : nat) (ip : i < 1),
                                        gen (S i) (Vbuild_spec_obligation_3 gen eq_refl ip)) eq_refl)) with (lt_1_SSn 0) by apply proof_irrelevance.
  reflexivity.
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

Definition Vin_aux {A} {n} (v : vector A n) (x : A) : Prop := Vin x v.

Lemma Vnth_0 {B} {n} (v:vector B (S n)) (ip: 0<(S n)):
  Vnth (i:=0) v ip ≡ Vhead v.
Proof.
  dep_destruct v.
  simpl.
  reflexivity.
Qed.

Lemma Vnth_Sn {B} (n i:nat) (v:B) (vs:vector B n) (ip: S i< S n) (ip': i< n):
  Vnth (Vcons v vs) ip ≡ Vnth vs ip'.
Proof.
  simpl.
  replace (lt_S_n ip) with ip' by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma Vnth_cast_index:
  ∀ {B} {n : nat} i j (ic: i<n) (jc: j<n) (x : vector B n),
    i ≡ j -> Vnth x ic ≡ Vnth x jc.
Proof.
  intros B n i j ic jc x E.
  crush.
  replace ic with jc by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma Vbuild_cons:
  forall B n (gen : forall i, i < S n -> B),
    Vbuild gen ≡ Vcons (gen 0 (lt_O_Sn n)) (Vbuild (fun i ip => gen (S i) (lt_n_S ip))).
Proof.
  intros B n gen.
  rewrite <- Vbuild_head.
  rewrite <- Vbuild_tail.
  auto.
Qed.

Lemma modulo_smaller_than_devisor:
  ∀ x y : nat, 0 ≢ y → x mod y < y.
Proof.
  intros.
  destruct y; try congruence.
  unfold modulo.
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

Section VMap2_Indexed.

  Definition Vmap2Indexed {A B C : Type} {n}
             (f: nat->A->B->C) (a: vector A n) (b: vector B n)
    := Vbuild (fun i ip => f i (Vnth a ip) (Vnth b ip)).

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

  Global Instance Vmap2Indexed_proper
         `{Setoid A} `{Setoid B} `{Setoid C}
         n
         (f: nat->A->B->C)
         `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    :
      Proper ((=) ==> (=) ==> (=)) (@Vmap2Indexed A B C n f).
  Proof.
    intros a a' Ea b b' Eb.
    unfold Vmap2Indexed.

    unfold equiv, vec_equiv.
    apply Vforall2_intro_nth.
    intros i ip.
    rewrite 2!Vbuild_nth.
    apply f_mor.
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




