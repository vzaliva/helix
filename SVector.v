
Require Import Spiral.
Require Import Rtheta.

Require Import Arith.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import SpiralTactics.

Require Import MathClasses.interfaces.canonical_names.

Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Open Scope vector_scope.
Open Scope nat_scope.

(* "sparse" vector type: vector holding Rhteta values *)
Notation svector n := (vector Rtheta n) (only parsing).

Section SparseVectors.

  (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
  Definition svector_from_vector {n} (v:vector CarrierA n): svector n :=
    Vmap Rtheta_normal v.

  (* Project out carrier type values from vector of Rheta values *)
  Definition vector_from_svector {n} (v:svector n): vector CarrierA n :=
    Vmap RthetaVal v.

  (* Our definition of "dense" vector means that it does not contain "structural" values and errors. *)

  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall Is_Val v.

  (* Construct "Zero svector". All values are structural zeros. *)
  Definition szero_svector n: svector n := Vconst Rtheta_szero n.

End SparseVectors.

Section Sparse_Unions.

  (* Scalar union. NB: It is not Proper wrt 'equiv'! *)
  Definition Union
             (a b: Rtheta): Rtheta
    :=
      match a, b with
      |  (_, true, ae), (bv, false, be) => (bv, false, orb ae be)
      |  (av, false, ae), (_, true, be) => (av, false, orb ae be)
      |  (_, true, ae), (_, true, be) => (zero, true, orb ae be)
      |  (_, false, _), (_, false, _) => Rtheta_szero_err
      end.


  (* Stronger commutativity, wrt to 'eq' equality *)
  Lemma Union_comm: ∀ x y : Rtheta, Union x y ≡ Union y x.
  Proof.
    intros x y.
    destruct_Rtheta x.
    destruct_Rtheta y.
    destruct x1, x2, y1, y2; reflexivity.
  Qed.

  (* Weaker commutativity, wrt to 'equiv' equality *)
  Instance Rtheta_Commutative_Union:
    @Commutative Rtheta Rtheta_equiv Rtheta Union.
  Proof.
    unfold Commutative.
    intros x y.
    rewrite Union_comm.
    reflexivity.
  Qed.

  (* Unary union of vector's elements (fold) *)
  Definition VecUnion {n} (v:svector n): Rtheta :=
    Vfold_left Union Rtheta_szero v.

  (* Binary element-wise union of two vectors *)
  Definition Vec2Union {n} (a b: svector n): svector n
    := Vmap2 Union a b.

  Definition SumUnion
             {o n} (v: vector (svector o) n): svector o
    := Vfold_left Vec2Union (szero_svector o) v.

  Lemma VecUnion_cons:
    ∀ m x (xs : svector m),
      VecUnion (Vcons x xs) ≡ Union (VecUnion xs) x.
  Proof.
    intros m x xs.
    unfold VecUnion.
    rewrite Vfold_left_cons.
    reflexivity.
  Qed.

  Lemma Vec2Union_comm {n} {a b:svector n}:
    Vec2Union a b ≡ Vec2Union b a.
  Proof.
    induction n.
    VOtac; reflexivity.
    VSntac a. VSntac b.
    simpl.
    rewrite IHn, Union_comm.
    reflexivity.
  Qed.

  Lemma SumUnion_cons m n (x: svector m) (xs: vector (svector m) n):
    SumUnion (Vcons x xs) ≡ Vec2Union (SumUnion xs) x.
  Proof.
    unfold SumUnion.
    apply Vfold_left_cons.
  Qed.

  Lemma AbsorbUnionIndexBinary:
    ∀ (m k : nat) (kc : k < m) (a b : svector m),
      Vnth (Vec2Union a b) kc ≡ Union (Vnth a kc) (Vnth b kc).
  Proof.
    intros m k kc a b.
    unfold Vec2Union.
    apply Vnth_map2.
  Qed.

  Lemma AbsorbUnionIndex:
    forall m n (x: vector (svector m) n) k (kc: k<m),
      Vnth (SumUnion x) kc ≡ VecUnion (Vmap (fun v => Vnth v kc) x).
  Proof.
    intros m n x k kc.
    induction n.
    + dep_destruct x.
      unfold VecUnion, SumUnion,szero_svector; simpl.
      apply Vnth_const.
    + dep_destruct x.
      rewrite Vmap_cons, SumUnion_cons, AbsorbUnionIndexBinary, IHn, VecUnion_cons, Union_comm.
      reflexivity.
  Qed.

  (* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbIUnionIndex:
    forall m n (x: vector (svector m) n) k (kc: k<m),
      Vnth
        (SumUnion
           (Vbuild
              (fun (i : nat) (ic : i < n) =>
                 (Vnth x ic)
           ))
        ) kc ≡
        VecUnion
        (Vbuild
           (fun (i : nat) (ic : i < n) =>
              Vnth (Vnth x ic) kc
        )).
  Proof.
    intros m n x k kc.

    induction n.
    + dep_destruct x.
      rewrite 2!Vbuild_0.
      unfold VecUnion; simpl.
      unfold SumUnion; simpl.
      unfold szero_svector; apply Vnth_const.

    +
      dep_destruct x.
      remember (λ (i : nat) (ic : i < S n), Vnth (Vcons h x0) ic) as geni.
      remember (λ (i : nat) (ic : i < S n), Vnth (geni i ic) kc) as genik.

      (* RHS massaging *)
      rewrite Vbuild_cons with (gen:=genik).
      replace (genik 0 (lt_0_Sn n)) with (Vnth h kc)
        by (subst genik geni; reflexivity).
      rewrite VecUnion_cons.

      replace (λ (i : nat) (ip : i < n), genik (S i) (lt_n_S ip)) with
      (λ (i : nat) (ic : i < n), Vnth (Vnth x0 ic) kc).

      rewrite <- IHn.
      remember (λ (i : nat) (ic : i < n), Vnth x0 ic) as genX.

      rewrite Vbuild_cons with (gen:=geni).
      replace (geni 0 (lt_0_Sn n)) with h
        by (subst geni; reflexivity).
      subst geni.
      replace (λ (i : nat) (ip : i < n), Vnth (Vcons h x0) (lt_n_S ip)) with genX.
      rewrite SumUnion_cons.
      rewrite AbsorbUnionIndexBinary.
      reflexivity.

      subst genX.
      extensionality i.
      extensionality ic.
      simpl.
      rewrite NatUtil.lt_Sn_nS.
      reflexivity.

      extensionality i.
      extensionality ic.
      subst genik geni.
      simpl.
      rewrite NatUtil.lt_Sn_nS.
      reflexivity.
  Qed.


  Lemma Union_Val_with_Struct:
    ∀ x s , Is_Val x -> Is_StructNonErr s -> Union x s ≡ x.
  Proof.
    intros x s V S.
    unfold Is_Val, Is_StructNonErr, Is_Struct, Is_SErr in *.
    destruct V, S.
    destruct_Rtheta x.
    destruct_Rtheta s.
    destruct x1, x2, s1, s2; crush.
  Qed.

  
  Lemma Union_Struct_with_Val:
    ∀ x s , Is_Val x -> Is_StructNonErr s -> Union s x ≡ x.
  Proof.
    intros x s V S.
    unfold Is_Val, Is_StructNonErr, Is_Struct, Is_SErr in *.
    destruct V, S.
    destruct_Rtheta x.
    destruct_Rtheta s.
    destruct x1, x2, s1, s2; crush.
  Qed.

End Sparse_Unions.

Close Scope vector_scope.
Close Scope nat_scope.
