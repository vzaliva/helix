
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

  Definition Union
             (op: CarrierA -> CarrierA -> CarrierA)
             (a b: Rtheta)
  : Rtheta :=
    let '(a0,a1,a2) := a in
    let '(b0,b1,b2) := b in
    let s := andb a1 b1 in
    (op a0 b0, s, orb s (orb a2 b2)).

  Instance Union_proper:
    Proper (((=) ==> (=)) ==> (=) ==> (=)) (Union).
  Proof.
    simpl_relation.
    unfold RthetaVal, Union.
    repeat break_let.
    apply H ; [apply H0 | apply H1].
  Qed.
  
  (* Stronger commutativity, wrt to 'eq' equality *)
  Lemma Union_comm
        (op: CarrierA -> CarrierA -> CarrierA)
        `{C: !@Commutative CarrierA eq CarrierA op}
    : ∀ x y : Rtheta, Union op x y ≡ Union op y x.
  Proof.
    intros x y.
    destruct_Rtheta x.
    destruct_Rtheta y.
    destruct x1, x2, y1, y2;
      (unfold Union;       
       replace (op x0 y0) with (op y0 x0) by apply C;
       reflexivity).
  Qed.


  (* Weaker commutativity, wrt to 'equiv' equality *)
  Instance Rtheta_Commutative_Union
           (op: CarrierA -> CarrierA -> CarrierA)
           `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
           `{C: !Commutative op}
    :
    @Commutative Rtheta Rtheta_equiv Rtheta (Union op).
  Proof.
    intros x y.
    destruct_Rtheta x.
    destruct_Rtheta y.
    destruct x1, x2, y1, y2; 
      (unfold Union;
       unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal;
       setoid_replace (op x0 y0) with (op y0 x0) by apply C;
       reflexivity).
  Qed.
  
  (* Unary union of vector's elements (fold) *)
  Definition VecUnion {n} (op: CarrierA -> CarrierA -> CarrierA) (v:svector n): Rtheta :=
    Vfold_left (Union op) Rtheta_szero v.

  (* Binary element-wise union of two vectors *)
  Definition Vec2Union {n} (op: CarrierA -> CarrierA -> CarrierA) (a b: svector n): svector n
    := Vmap2 (Union op) a b.

  Definition SumUnion
             {o n} (op: CarrierA -> CarrierA -> CarrierA) (v: vector (svector o) n): svector o
    := Vfold_left (Vec2Union op) (szero_svector o) v.

  Lemma VecUnion_cons:
    ∀ (op: CarrierA -> CarrierA -> CarrierA) m x (xs : svector m),
      VecUnion op (Vcons x xs) ≡ Union op (VecUnion op xs) x.
  Proof.
    intros op m x xs.
    unfold VecUnion.
    rewrite Vfold_left_cons.
    reflexivity.
  Qed.

  Lemma Vec2Union_comm {n}
        (op: CarrierA -> CarrierA -> CarrierA)
        `{C: !@Commutative CarrierA eq CarrierA op}
        {a b:svector n}:
    Vec2Union op a b ≡ Vec2Union op b a.
  Proof.
    induction n.
    VOtac; reflexivity.
    VSntac a. VSntac b.
    simpl.
    rewrite IHn, Union_comm.
    reflexivity.
    apply C.
  Qed.

  Lemma SumUnion_cons {m n}
        (op: CarrierA -> CarrierA -> CarrierA)
        `{C: !@Commutative CarrierA eq CarrierA op}
        (x: svector m) (xs: vector (svector m) n):
    SumUnion op (Vcons x xs) ≡ Vec2Union op (SumUnion op xs) x.
  Proof.
    unfold SumUnion.
    apply Vfold_left_cons.
  Qed.

  Lemma AbsorbUnionIndexBinary:
    ∀ (op: CarrierA -> CarrierA -> CarrierA) (m k : nat) (kc : k < m) (a b : svector m),
      Vnth (Vec2Union op a b) kc ≡ Union op (Vnth a kc) (Vnth b kc).
  Proof.
    intros op m k kc a b.
    unfold Vec2Union.
    apply Vnth_map2.
  Qed.

  Lemma AbsorbUnionIndex:
    forall (op: CarrierA -> CarrierA -> CarrierA) `{C: !@Commutative CarrierA eq CarrierA op} m n (x: vector (svector m) n) k (kc: k<m),
      Vnth (SumUnion op x) kc ≡ VecUnion op (Vmap (fun v => Vnth v kc) x).
  Proof.
    intros op C m n x k kc.
    induction n.
    + dep_destruct x.
      unfold VecUnion, SumUnion,szero_svector; simpl.
      apply Vnth_const.
    + dep_destruct x.
      rewrite Vmap_cons, SumUnion_cons, AbsorbUnionIndexBinary, IHn, VecUnion_cons, Union_comm.
      reflexivity.
      apply C.
      apply C.
  Qed.

  (* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbIUnionIndex:
    forall (op: CarrierA -> CarrierA -> CarrierA) `{C: !@Commutative CarrierA eq CarrierA op} m n (x: vector (svector m) n) k (kc: k<m),
      Vnth
        (SumUnion op
           (Vbuild
              (fun (i : nat) (ic : i < n) =>
                 (Vnth x ic)
           ))
        ) kc ≡
        VecUnion op
        (Vbuild
           (fun (i : nat) (ic : i < n) =>
              Vnth (Vnth x ic) kc
        )).
  Proof.
    intros op C m n x k kc.

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
      apply C.
      extensionality i.
      extensionality ic.
      simpl.
      rewrite NatUtil.lt_Sn_nS.
      subst genX.
      reflexivity.

      extensionality i.
      extensionality ic.
      subst genik geni.
      simpl.
      rewrite NatUtil.lt_Sn_nS.
      reflexivity.
  Qed.

  Lemma Union_Val_with_Struct:
    ∀ (op: CarrierA -> CarrierA -> CarrierA) x s,
      Is_Val x -> Is_StructNonErr s -> Union op x s ≡ x.
  Proof.
    intros op x s V S.
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

  Lemma Vbreak_dense_vector {n1 n2} {x: svector (n1+n2)} {x0 x1}:
    Vbreak x ≡ (x0, x1) ->
    svector_is_dense x ->  (svector_is_dense x0) /\ (svector_is_dense x1).
  Proof.
    unfold svector_is_dense.
    apply Vbreak_preserves_P.
  Qed.

  Lemma Vec2Union_szero_svector {n} {a: svector n}:
    svector_is_dense a ->
    Vec2Union a (szero_svector n) ≡ a.
  Proof.
    intros D.
    unfold szero_svector.
    induction n.
    VOtac; reflexivity.
    simpl.
    rewrite_clear IHn.
    rewrite Union_Val_with_Struct.
    dep_destruct a; reflexivity.
    apply Vforall_hd; assumption.
    unfold Is_StructNonErr, Rtheta_szero, Is_Struct, RthetaIsStruct, Is_SErr, RthetaIsSErr.
    simpl; tauto.
    apply Vforall_tl; assumption.
  Qed.

End Sparse_Unions.

Close Scope vector_scope.
Close Scope nat_scope.
