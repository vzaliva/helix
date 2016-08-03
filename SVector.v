
Require Import VecUtil.
Require Import VecSetoid.
Require Import Spiral.
Require Import Rtheta.

Require Import Coq.Bool.Bool.
Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import CpdtTactics.
Require Import JRWTactics.
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
Definition sparsify {n} (v:avector n): svector n :=
  Vmap mkValue v.

Global Instance sparsify_proper {n:nat}:
  Proper ((=) ==> (=)) (@sparsify n).
Proof.
  intros x y E.
  unfold sparsify.
  rewrite E.
  reflexivity.
Qed.

(* Project out carrier type values from vector of Rheta values *)
Definition densify {n} (v:svector n): avector n :=
  Vmap (A:=Rtheta) (@evalWriter _ _ _) v.

Global Instance densify_proper {n:nat}:
  Proper ((=) ==> (=)) (@densify n).
Proof.
  intros x y E.
  unfold densify.
  rewrite E.
  reflexivity.
Qed.

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

Lemma evalWriterUnion {a b: Rtheta}:
  evalWriter (Union a b) =
  plus (evalWriter a)
       (evalWriter b).
Proof.
  unfold Union.
  rewrite evalWriter_Rtheta_liftM2.
  reflexivity.
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
  Vfold_left_rev Union mkSZero v.

(* Binary element-wise union of two vectors *)
Definition Vec2Union {n} (a b: svector n): svector n
  := Vmap2 Union a b.

Global Instance Vec2Union_proper {n}
  :
    Proper ((=) ==> (=) ==> (=)) (Vec2Union (n:=n)).
Proof.
  intros a a' Ea b b' Eb.
  unfold Vec2Union.
  rewrite Ea, Eb.
  reflexivity.
Qed.

Definition SumUnion
           {o n}
           (v: vector (svector o) n): svector o
  :=  Vfold_left_rev Vec2Union (szero_svector o) v.

Global Instance SumUnion_proper {o n}
  : Proper ((=) ==> (=)) (@SumUnion o n).
Proof.
  intros x y E.
  unfold SumUnion.
  rewrite E.
  reflexivity.
Qed.

Lemma VecUnion_cons:
  ∀ m x (xs : svector m),
    VecUnion (Vcons x xs) ≡ Union (VecUnion xs) x.
Proof.
  intros m x xs.
  unfold VecUnion.
  rewrite Vfold_left_rev_cons.
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
  apply Vfold_left_rev_cons.
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

Lemma UnionCollisionFree (a b : Rtheta):
  ¬Is_Collision a →
  ¬Is_Collision b →
  ¬(Is_Val a ∧ Is_Val b)
  → ¬Is_Collision (Union a b).
Proof.
  intros CA CB C.
  unfold Union, Is_Collision, compose.
  rewrite execWriter_Rtheta_liftM2.
  unfold Is_Collision, Is_Val, compose in *.
  destruct (execWriter a) as [str_a col_a].
  destruct (execWriter b) as [str_b col_b].
  unfold RthetaFlagsAppend.
  unfold IsCollision, IsVal in *.
  destr_bool.
  auto.
Qed.

(* Conditions under which Union produces value *)
Lemma ValUnionIsVal (a b : Rtheta):
  Is_Val a \/ Is_Val b <-> Is_Val (Union a b).
Proof.
  split.
  - intros [VA | VB];
      (
        unfold Union, Is_Val, compose in *;
        rewrite execWriter_Rtheta_liftM2;
        destruct (execWriter a) as [str_a col_a];
        destruct (execWriter b) as [str_b col_b];
        unfold RthetaFlagsAppend;
        unfold IsVal in *;
        destr_bool; auto).
  -
    intros H.
    unfold Union, Is_Val, compose in *.
    rewrite execWriter_Rtheta_liftM2 in *.
    destruct (execWriter a) as [str_a col_a].
    destruct (execWriter b) as [str_b col_b].
    unfold IsVal in *.
    destr_bool; auto.
Qed.

Lemma Is_Val_VecUnion {n} {v: svector n}:
  Vexists Is_Val v <-> Is_Val (VecUnion v).
Proof.
  split.
  - intros H.
    apply Vexists_eq in H.
    unfold VecUnion.
    destruct H as [x [XI XV]].
    induction v.
    + unfold Vin in XI.
      congruence.
    + apply Vin_cons in XI.
      rewrite Vfold_left_rev_cons.
      destruct XI.
      * subst h.
        apply ValUnionIsVal.
        right.
        assumption.
      *
        clear XV.
        apply IHv in H.
        apply ValUnionIsVal.
        left.
        assumption.
  -
    intros H.
    induction v.
    + crush.
    + simpl in *.
      rewrite VecUnion_cons in H.
      apply ValUnionIsVal in H.
      destruct H.
      apply IHv in H.
      right.
      apply H.
      left.
      apply H.
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
  Vforall Not_Collision v.

Lemma sparsify_non_coll: forall n (x:avector n),
    svector_is_non_collision (sparsify x).
Proof.
  intros n x.
  unfold sparsify.
  unfold svector_is_non_collision, Not_Collision, compose.
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

Lemma sparsify_densify {n} (x:svector n):
  svector_is_dense x ->
  svector_is_non_collision x ->
  (sparsify (densify x)) ≡ x.
Proof.
  intros D N.
  unfold densify, sparsify.
  rewrite Vmap_map.
  apply Vmap_eq_nth.
  intros i ip.
  unfold svector_is_dense in D.
  apply Vforall_nth with (ip:=ip) in D.
  unfold svector_is_non_collision in N.
  apply Vforall_nth with (ip:=ip) in N.
  generalize dependent (Vnth x ip). clear ip i.
  apply mkValue_evalWriter_VNC.
Qed.

Lemma sparsify_densify_equiv {n} (x:svector n):
  (sparsify (densify x)) = x.
Proof.
  unfold densify, sparsify.
  rewrite Vmap_map.
  vec_index_equiv i ip.
  rewrite Vnth_map.
  generalize dependent (Vnth x ip). clear ip i.
  intros r.
  apply mkValue_evalWriter.
Qed.

Lemma sparsify_densify_id_equiv {n}:
  (@sparsify n ∘ densify) = id.
Proof.
  apply ext_equiv_applied_iff'.
  split; try apply vec_Setoid.
  intros x y E.
  unfold compose.
  rewrite E.
  reflexivity.
  crush.
  apply sparsify_densify_equiv.
Qed.


Section Matrix.
  (* Poor man's matrix is vector of vectors.
     TODO: If it grows, move to separate module. *)

  Set Implicit Arguments.
  Variables (A: Type) (m n:nat).

  Definition row
             {i:nat} (ic: i<m)
             (a: vector (vector A m) n)
    :=
      Vmap (Vnth_aux ic) a.

  Definition col
             {i:nat} (ic: i<n)
             (a: vector (vector A m) n)
    :=
      Vnth a ic.

  Definition transpose
             (a: vector (vector A m) n)
    :=
      Vbuild (fun j jc => row jc a).

End Matrix.

(* "sparse" matrix 'm' rows by 'n' columns *)
Notation smatrix m n := (vector (svector m) n) (only parsing).


Close Scope vector_scope.
Close Scope nat_scope.

