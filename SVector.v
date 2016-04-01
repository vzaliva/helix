
Require Import Spiral.
Require Import Rtheta.

Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import SpiralTactics.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Require Import WriterMonadNoT.

Open Scope vector_scope.
Open Scope nat_scope.

(* "sparse" vector for CarrierA type elements could be simulated using Rtheta *)
Notation svector n := (vector Rtheta n) (only parsing).

(* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
Definition sparsify {n} (v:vector CarrierA n): svector n :=
  Vmap mkValue v.

(* Project out carrier type values from vector of Rheta values *)
Definition densify {n} (v:svector n): vector CarrierA n :=
  Vmap (@evalWriter RthetaFlags CarrierA _) v.

(* Construct "Zero svector". All values are structural zeros. *)
Definition szero_svector n: svector n := Vconst mkSZero n.

(* "dense" vector means that it does not contain "structural" values *)
Definition svector_is_dense {n} (v:svector n) : Prop :=
  Vforall Is_Val v.


Local Open Scope bool_scope.

Set Implicit Arguments.

Lemma Vnth_sparsify:
  ∀ (n i : nat) (ip : i < n) (v : vector CarrierA n),
    Vnth (sparsify v) ip ≡ mkValue (Vnth v ip).
Proof.
  intros n i ip v.
  unfold sparsify.
  apply Vnth_map.
Qed.

Definition Union: Rtheta -> Rtheta -> Rtheta := liftM2 plus.

Lemma Union_comm:
  Commutative Union.
Proof.
  intros x y.
  unfold Union, equiv, Rtheta_equiv.
  rewrite 2!evalWriter_Rtheta_liftM2.
  ring.
Qed.

Global Instance Union_proper
  :
    Proper ((=) ==> (=) ==> (=)) Union.
Proof.
  intros a b H x y E.
  unfold Union, equiv, Rtheta_equiv in *.
  rewrite 2!evalWriter_Rtheta_liftM2.
  rewrite E, H.
  reflexivity.
Qed.

(* Unary union of vector's elements (left fold) *)
Definition VecUnion {n} (v: svector n): Rtheta :=
  Vfold_left Union mkSZero v.

(* Binary element-wise union of two vectors *)
Definition Vec2Union {n} (a b: svector n): svector n
  := Vmap2 Union a b.

Definition SumUnion
           {o n}
           (v: vector (svector o) n): svector o
  :=  Vfold_left Vec2Union (szero_svector o) v.

Lemma VecUnion_cons:
  ∀ m x (xs : svector m),
    VecUnion (Vcons x xs) ≡ Union (VecUnion xs) x.
Proof.
  intros m x xs.
  unfold VecUnion.
  rewrite Vfold_left_cons.
  reflexivity.
Qed.

Lemma Vec2Union_comm {n}:
  @Commutative (svector n) _ (svector n) Vec2Union.
Proof.
  intros a b.
  induction n.
  VOtac; reflexivity.
  VSntac a. VSntac b.
  simpl.
  rewrite 2!Vcons_to_Vcons_reord.
  apply Vcons_reord_proper.
  apply IHn.
  apply Union_comm; apply C.
Qed.

Lemma SumUnion_cons {m n}
      (x: svector m) (xs: vector (svector m) n):
  SumUnion (Vcons x xs) ≡ Vec2Union (SumUnion xs) x.
Proof.
  unfold SumUnion.
  apply Vfold_left_cons.
Qed.

Lemma AbsorbUnionIndexBinary
      (m k : nat)
      (kc : k < m)
      (a b : svector m):
  Vnth (Vec2Union a b) kc ≡ Union (Vnth a kc) (Vnth b kc).
Proof.
  unfold Vec2Union.
  apply Vnth_map2.
Qed.

Lemma AbsorbUnionIndex
      m n (x: vector (svector m) n) k (kc: k<m):
  Vnth (SumUnion x) kc = VecUnion (Vmap (fun v => Vnth v kc) x).
Proof.
  induction n.
  + dep_destruct x.
    unfold VecUnion, SumUnion, szero_svector; simpl.
    rewrite Vnth_const; reflexivity.
  + dep_destruct x.
    rewrite Vmap_cons, SumUnion_cons, AbsorbUnionIndexBinary, IHn, VecUnion_cons.
    reflexivity.
Qed.

(* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
Lemma AbsorbIUnionIndex
      {o n}
      (body: forall (i : nat) (ic : i < n), svector o)
      k (kc: k<o)
  :
    Vnth
      (SumUnion (Vbuild body)) kc ≡
      VecUnion
      (Vbuild
         (fun (i : nat) (ic : i < n) =>
            Vnth (body i ic) kc
      )).
Proof.
  induction n.
  - rewrite 2!Vbuild_0.
    unfold VecUnion, SumUnion, szero_svector, mkSZero.
    apply Vnth_const.
  -
    rewrite Vbuild_cons.
    rewrite SumUnion_cons.
    rewrite AbsorbUnionIndexBinary.
    rewrite IHn.
    rewrite <- VecUnion_cons.
    rewrite Vbuild_cons.
    reflexivity.
Qed.


Lemma Union_SZero_r x:
  (Union x mkSZero) = x.
Proof.
  unfold Union.
  unfold_Rtheta_equiv.
  rewrite evalWriter_Rtheta_liftM2.
  rewrite evalWriter_Rtheta_SZero.
  ring.
Qed.

Lemma Union_SZero_l x:
  (Union mkSZero x) = x.
Proof.
  unfold Union.
  unfold_Rtheta_equiv.
  rewrite evalWriter_Rtheta_liftM2.
  rewrite evalWriter_Rtheta_SZero.
  ring.
Qed.

Lemma Vbreak_dense_vector {n1 n2} {x: svector (n1+n2)} {x0 x1}:
  Vbreak x ≡ (x0, x1) ->
  svector_is_dense x ->  (svector_is_dense x0) /\ (svector_is_dense x1).
Proof.
  unfold svector_is_dense.
  apply Vbreak_preserves_P.
Qed.

Lemma Vec2Union_szero_svector_r {n} {a: svector n}:
  Vec2Union a (szero_svector n) = a.
Proof.
  unfold szero_svector.
  induction n.
  VOtac; reflexivity.
  simpl.
  rewrite Vcons_to_Vcons_reord.
  rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
  rewrite Union_SZero_r.
  rewrite <- Vcons_to_Vcons_reord.
  dep_destruct a.
  crush.
Qed.

Lemma Vec2Union_szero_svector_l {n} {a: svector n}:
  Vec2Union (szero_svector n) a = a.
Proof.
  unfold szero_svector.
  induction n.
  VOtac; reflexivity.
  simpl.
  rewrite Vcons_to_Vcons_reord.
  rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
  rewrite Union_SZero_l.
  rewrite <- Vcons_to_Vcons_reord.
  dep_destruct a.
  crush.
Qed.

Definition svector_is_collision {n} (v:svector n) :=
  Vexists Is_Collision v.

Definition svector_is_non_collision {n} (v:svector n) :=
  Vforall (not ∘ Is_Collision) v.

(* TODO: decidable for collision? *)

Lemma sparsify_non_coll: forall n (x:avector n),
    svector_is_non_collision (sparsify x).
Proof.
  intros n x.
  unfold sparsify.
  unfold svector_is_non_collision, compose.
  apply Vforall_map_intro.
  apply Vforall_intro.
  intros v N.
  auto.
Qed.

Lemma sparsify_is_dense:
  ∀ (i : nat) (x : vector CarrierA i), svector_is_dense (sparsify x).
Proof.
  intros i x.
  unfold sparsify, svector_is_dense.
  apply Vforall_map_intro.
  apply Vforall_intro.
  intros v N.
  apply IsVal_mkValue.
Qed.



Close Scope vector_scope.
Close Scope nat_scope.

