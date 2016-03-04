
Require Import Spiral.
Require Import Rtheta.
Require Import MRtheta.

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
Definition svector_from_vector {n} (v:vector CarrierA n): svector n :=
  Vmap Rtheta_normal v.

(* Project out carrier type values from vector of Rheta values *)
Definition vector_from_svector {n} (v:svector n): vector CarrierA n :=
  Vmap val v.

(* Our definition of "dense" vector means that it does not contain "structural" values *)

Definition svector_is_dense {n} (v:svector n) : Prop :=
  Vforall Is_Val v.

(* Construct "Zero svector". All values are structural zeros. *)
Definition szero_svector n: svector n := Vconst Rtheta_SZero n.

Notation mvector n := (vector (MRtheta) n) (only parsing).

Definition mvector_from_svector {n} (v:svector n): mvector n :=
  Vmap ret v.

Definition sector_from_mvector {n} (v:mvector n): svector n :=
  Vmap (@evalWriter RthetaFlags Rtheta Monoid_RthetaFlags) v.

Definition mvector_is_dense {n} (v:mvector n) : Prop :=
  Vforall (Is_Val ∘ (@evalWriter RthetaFlags Rtheta Monoid_RthetaFlags)) v.

Definition szero_mvector n: mvector n := Vconst MRtheta_SZero n.

Set Implicit Arguments.

Local Open Scope bool_scope.

(* Union is a binary operation on carrier type applied to Rhteta values, using State Monad to keep track of flags *)
Definition Union (op: Rtheta -> Rtheta -> Rtheta)
  := Rtheta_liftM2 op.

Lemma Union_comm:
  forall (op : Rtheta -> Rtheta -> Rtheta),
    @Commutative Rtheta Rtheta_val_equiv Rtheta op ->
    @Commutative (MRtheta) MRtheta_equiv (MRtheta) (Union op).
Proof.
  intros op C x y.
  unfold Union, equiv, MRtheta_equiv.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply C.
Qed.

Global Instance Union_proper
       (op: Rtheta -> Rtheta -> Rtheta)
       `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
  :
    Proper ((=) ==> (=) ==> (=))
           (Union op).
Proof.
  intros a b H x y E.
  unfold Union.
  unfold Union, equiv, MRtheta_equiv in *.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply op_mor; assumption.
Qed.

(* Unary union of vector's elements (left fold) *)
Definition VecUnion {n} (op: Rtheta -> Rtheta -> Rtheta) (v: mvector n): MRtheta :=
  Vfold_left (Union op) MRtheta_SZero v.

(* Binary element-wise union of two vectors *)
Definition Vec2Union {n} (op: Rtheta -> Rtheta -> Rtheta) (a b: mvector n): mvector n
  := Vmap2 (Union op) a b.

Definition SumUnion
           {o n} (op: Rtheta -> Rtheta -> Rtheta)
           (v: vector (mvector o) n): mvector o
  :=  Vfold_left (Vec2Union op) (szero_mvector o) v.

Lemma VecUnion_cons:
  ∀ (op: Rtheta -> Rtheta -> Rtheta) m x (xs : mvector m),
    VecUnion op (Vcons x xs) ≡ Union op (VecUnion op xs) x.
Proof.
  intros op m x xs.
  unfold VecUnion.
  rewrite Vfold_left_cons.
  reflexivity.
Qed.

Lemma Vec2Union_comm {n}
      (op: Rtheta -> Rtheta -> Rtheta)
      `{C: !Commutative op}:
  @Commutative (mvector n) _ (mvector n) (Vec2Union op).
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
      (op: Rtheta -> Rtheta -> Rtheta)
      (x: mvector m) (xs: vector (mvector m) n):
  SumUnion op (Vcons x xs) ≡ Vec2Union op (SumUnion op xs) x.
Proof.
  unfold SumUnion.
  apply Vfold_left_cons.
Qed.

Lemma AbsorbUnionIndexBinary
      (op: Rtheta -> Rtheta -> Rtheta)
      (m k : nat)
      (kc : k < m)
      (a b : mvector m):
  Vnth (Vec2Union op a b) kc ≡ Union op (Vnth a kc) (Vnth b kc).
Proof.
  unfold Vec2Union.
  apply Vnth_map2.
Qed.

Lemma AbsorbUnionIndex
      (op: Rtheta -> Rtheta -> Rtheta)
      `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
      m n (x: vector (mvector m) n) k (kc: k<m):
  Vnth (SumUnion op x) kc = VecUnion op (Vmap (fun v => Vnth v kc) x).
Proof.
  induction n.
  + dep_destruct x.
    unfold VecUnion, SumUnion, szero_mvector; simpl.
    rewrite Vnth_const; reflexivity.
  + dep_destruct x.
    rewrite Vmap_cons, SumUnion_cons, AbsorbUnionIndexBinary, IHn, VecUnion_cons.
    reflexivity.
Qed.

(* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
Lemma AbsorbIUnionIndex
      (op: Rtheta -> Rtheta -> Rtheta)
      m n (x: vector (mvector m) n) k (kc: k<m)
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

Lemma Union_Plus_MSZero_r x:
  (Union (plus) x MRtheta_SZero) = x.
Proof.
  unfold Union.
  unfold_MRtheta_equiv.
  rewrite evalWriter_Rtheta_liftM2.
  rewrite evalWriter_MRtheta_SZero.
  unfold_Rtheta_val_equiv.
  simpl.
  ring.
Qed.

Lemma Union_Plus_MSZero_l x:
  (Union (plus) MRtheta_SZero x) = x.
Proof.
  unfold Union.
  unfold_MRtheta_equiv.
  rewrite evalWriter_Rtheta_liftM2.
  rewrite evalWriter_MRtheta_SZero.
  unfold_Rtheta_val_equiv.
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

Lemma Vec2Union_szero_svector_r {n} {a: mvector n}:
  Vec2Union plus a (szero_mvector n) = a.
Proof.
  unfold szero_mvector.
  induction n.
  VOtac; reflexivity.
  simpl.
  rewrite Vcons_to_Vcons_reord.
  rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
  rewrite Union_Plus_MSZero_r.
  rewrite <- Vcons_to_Vcons_reord.
  dep_destruct a.
  crush.
Qed.

Lemma Vec2Union_szero_svector_l {n} {a: mvector n}:
  Vec2Union plus (szero_mvector n) a = a.
Proof.
  unfold szero_mvector.
  induction n.
  VOtac; reflexivity.
  simpl.
  rewrite Vcons_to_Vcons_reord.
  rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
  rewrite Union_Plus_MSZero_l.
  rewrite <- Vcons_to_Vcons_reord.
  dep_destruct a.
  crush.
Qed.


Close Scope vector_scope.
Close Scope nat_scope.

