
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

(* "sparse" vector for CarrierA type elements could be simulated using Rtheta *)
Notation svector n := (vector Rtheta n) (only parsing).

Section SparseVectors.

  (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
  Definition svector_from_vector {n} (v:vector CarrierA n): svector n :=
    Vmap Rtheta_normal v.

  (* Project out carrier type values from vector of Rheta values *)
  Definition vector_from_svector {n} (v:svector n): vector CarrierA n :=
    Vmap val v.

  (* Our definition of "dense" vector means that it does not contain "structural" values or structual collisions. *)

  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall Is_Val v.

  (* svector is structure collision-free *)
  Definition svector_is_non_col {n} (v:svector n) : Prop :=
    Vforall (not ∘ Is_Collision) v.

  (* Construct "Zero svector". All values are structural zeros. *)
  Definition szero_svector n: svector n := Vconst Rtheta_SZero n.

End SparseVectors.

Section Sparse_Unions.
  Open Local Scope bool_scope.

  Definition Union := Rtheta_binop. (* For sparse vectors binary operation on Rthetat is called Union (parametrized by binop kernel) *)

  (* Unary union of vector's elements (fold) *)
  Definition VecUnion {n} (op: CarrierA -> CarrierA -> CarrierA) (v:svector n): Rtheta :=
    Vfold_left (Union op) Rtheta_SZero v.

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
        `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
        `{C: !Commutative op}
        {a b:svector n}:
    Vec2Union op a b = Vec2Union op b a.
  Proof.
    induction n.
    VOtac; reflexivity.
    VSntac a. VSntac b.
    simpl.
    rewrite 2!Vcons_to_Vcons_reord.
    rewrite_clear IHn.
    setoid_replace (Union op (Vhead a) (Vhead b)) with (Union op (Vhead b) (Vhead a))
      by apply (@Rtheta_val_Commutative_Rtheta_binary op op_mor C).
    reflexivity.
  Qed.

  Lemma SumUnion_cons {m n}
        (op: CarrierA -> CarrierA -> CarrierA)
        (x: svector m) (xs: vector (svector m) n):
    SumUnion op (Vcons x xs) ≡ Vec2Union op (SumUnion op xs) x.
  Proof.
    unfold SumUnion.
    apply Vfold_left_cons.
  Qed.

  Lemma AbsorbUnionIndexBinary
        (op: CarrierA -> CarrierA -> CarrierA)
        (m k : nat)
        (kc : k < m)
        (a b : svector m):
    Vnth (Vec2Union op a b) kc ≡ Union op (Vnth a kc) (Vnth b kc).
  Proof.
    unfold Vec2Union.
    apply Vnth_map2.
  Qed.

  Lemma AbsorbUnionIndex
        (op: CarrierA -> CarrierA -> CarrierA)
        `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
        m n (x: vector (svector m) n) k (kc: k<m):
    Vnth (SumUnion op x) kc = VecUnion op (Vmap (fun v => Vnth v kc) x).
  Proof.
    induction n.
    + dep_destruct x.
      unfold VecUnion, SumUnion,szero_svector; simpl.
      rewrite Vnth_const; reflexivity.
    + dep_destruct x.
      rewrite Vmap_cons, SumUnion_cons, AbsorbUnionIndexBinary, IHn, VecUnion_cons.
      reflexivity.
  Qed.

  (* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbIUnionIndex
        (op: CarrierA -> CarrierA -> CarrierA)
        m n (x: vector (svector m) n) k (kc: k<m)
    :
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
 
  Lemma Union_Plus_SZero_r x:
    (Union (plus) x Rtheta_SZero) = x.
  Proof.
    unfold Union, equiv, Rtheta_val_equiv, Rtheta_rel_first.
    simpl.
    ring.
  Qed.  

  Lemma Union_Plus_SZero_l x:
    (Union (plus) Rtheta_SZero x) = x.
  Proof.
    unfold Union, equiv, Rtheta_val_equiv, Rtheta_rel_first.
    simpl.
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
    Vec2Union plus a (szero_svector n) = a.
  Proof.
    unfold szero_svector.
    induction n.
    VOtac; reflexivity.
    simpl.
    rewrite Vcons_to_Vcons_reord.
    rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
    rewrite Union_Plus_SZero_r.
    rewrite <- Vcons_to_Vcons_reord.
    dep_destruct a.
    crush.
  Qed.

  Lemma Vec2Union_szero_svector_l {n} {a: svector n}:
    Vec2Union plus (szero_svector n) a = a.
  Proof.
    unfold szero_svector.
    induction n.
    VOtac; reflexivity.
    simpl.
    rewrite Vcons_to_Vcons_reord.
    rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
    rewrite Union_Plus_SZero_l.
    rewrite <- Vcons_to_Vcons_reord.
    dep_destruct a.
    crush.
  Qed.
  
End Sparse_Unions.

Close Scope vector_scope.
Close Scope nat_scope.
