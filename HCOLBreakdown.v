
Require Import Spiral.
Require Import Rtheta.
Require Import MRtheta.
Require Import SVector.

Require Import HCOL.
Require Import HCOLImpl.
Require Import THCOL.
Require Import THCOLImpl.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import SpiralTactics.

Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Open Scope vector_scope.
Open Scope hcol_scope.

Definition MaxAbs (a b: MRtheta): MRtheta := max (abs a) (abs b).

Global Instance MaxAbs_proper:
  Proper ((=) ==> (=) ==> (=)) (MaxAbs).
Proof.
  intros a a' aE b b' bE.
  unfold MaxAbs.
  rewrite aE, bE.
  reflexivity.
Qed.

Section HCOLBreakdown.

  Lemma Vmap2Indexed_to_VMap2 `{Setoid A} {n} {a b: vector A n}
        (f:A->A->A) `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
  :
    Vmap2 f a b = Vmap2Indexed (IgnoreIndex2 f) a b.
  Proof.
    unfold equiv, vec_equiv.
    apply Vforall2_intro_nth.
    intros i ip.
    rewrite Vnth_Vmap2Indexed.
    rewrite Vnth_map2.
    reflexivity.
  Qed.

  Lemma breakdown_ScalarProd: forall (n:nat) (a v: mvector n),
      ScalarProd (a,v) =
      (compose (Reduction (+) 0) (BinOp (IgnoreIndex2 mult))) (a,v).
  Proof.
    intros n a v.
    unfold compose, BinOp, Reduction, ScalarProd.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite Vmap2Indexed_to_VMap2.
    reflexivity.
    apply MRtheta_mult_proper.
  Qed.

  Fact breakdown_OScalarProd: forall {h:nat},
      HScalarProd (h:=h)
      =
      ((HReduction  (+) 0) ∘ (HBinOp (IgnoreIndex2 mult))).
  Proof.
    intros h.
    apply HOperator_functional_extensionality; intros v.
    unfold HScalarProd, HReduction, HBinOp.
    unfold vector2pair, compose, Lst, Vectorize.
    apply Vcons_single_elim.
    destruct (Vbreak v).
    apply breakdown_ScalarProd.
  Qed.

  Lemma breakdown_EvalPolynomial: forall (n:nat) (a: mvector (S n)) (v: MRtheta),
      EvalPolynomial a v = (
        compose (ScalarProd) (compose (pair a) (MonomialEnumerator n))
      ) v.
  Proof.
    intros n a v.
    unfold compose.
    induction n.
    - simpl (MonomialEnumerator 0 v).
      rewrite EvalPolynomial_reduce.
      dep_destruct (Vtail a).
      simpl. rewrite MRthetaSZero_Zero.
      ring.

    - rewrite EvalPolynomial_reduce, MonomialEnumerator_cons, ScalarProd_reduce.
      unfold Ptail.
      rewrite ScalarProd_comm.

      Opaque Scale ScalarProd.
      simpl.
      Transparent Scale ScalarProd.

      rewrite ScalarProduct_hd_descale, IHn, mult_1_r, ScalarProd_comm.
      reflexivity.
  Qed.

  Fact breakdown_OEvalPolynomial: forall (n:nat) (a: mvector (S n)),
      HEvalPolynomial a =
      (HScalarProd ∘
                   ((HPrepend  a) ∘
                                  (HMonomialEnumerator n))).
  Proof.
    intros n a.
    apply HOperator_functional_extensionality; intros v.
    unfold HEvalPolynomial, HScalarProd, HPrepend, HMonomialEnumerator.
    unfold vector2pair, HCompose, compose, Lst, Scalarize.
    rewrite Vcons_single_elim, Vbreak_app.
    apply breakdown_EvalPolynomial.
  Qed.

  Lemma breakdown_TInfinityNorm: forall (n:nat) (v: mvector n),
      InfinityNorm v = (Reduction MaxAbs 0) v.
  Proof.
    intros.
    unfold InfinityNorm, Reduction.

    dependent induction v.
    - reflexivity.
    - rewrite Vfold_right_reduce.
      unfold_MRtheta_equiv.
      rewrite evalWriter_Rtheta_liftM2.

      simpl.
      rewrite_clear IHv.

      assert (ABH: (abs (Vfold_right MaxAbs v 0)) =
                   (Vfold_right MaxAbs v 0)).
      {
        unfold MaxAbs.
        intros.
        dependent induction v.
        + simpl.
          apply abs_0_s.

        + apply MRtheta_TotalOrder.
          rewrite Vfold_right_reduce, IHv, <- abs_max_comm_2nd.
          reflexivity.
      }
      unfold MaxAbs.
      rewrite ABH.
      reflexivity.
  Qed.

  Fact breakdown_OTInfinityNorm:  forall (n:nat),
      HInfinityNorm =
      HReduction MaxAbs 0 (i:=n).
  Proof.
    intros n.
    apply HOperator_functional_extensionality; intros v.
    apply Vcons_single_elim.
    apply breakdown_TInfinityNorm.
  Qed.

  Lemma breakdown_MonomialEnumerator:
    forall (n:nat) (x:Rtheta),
      MonomialEnumerator n x = Induction (S n) (.*.) 1 x.
  Proof.
    intros n x.
    induction n.
    - reflexivity.
    - rewrite MonomialEnumerator_cons.
      rewrite Vcons_to_Vcons_reord.
      rewrite_clear IHn.
      symmetry.
      rewrite Induction_cons.
      rewrite Vcons_to_Vcons_reord.
      unfold Scale.

      rewrite 2!Vmap_to_Vmap_reord.
      setoid_replace (fun x0 : Rtheta => mult x0 x) with (mult x).
      reflexivity.
      +
        compute. intros.
        rewrite H. apply mult_comm.
  Qed.

  Fact breakdown_OMonomialEnumerator:
    forall (n:nat),
      HMonomialEnumerator n =
      HInduction (S n) (.*.) 1.
  Proof.
    intros n.
    apply HOperator_functional_extensionality; intros v.
    apply breakdown_MonomialEnumerator.
  Qed.

  Lemma breakdown_ChebyshevDistance:  forall (n:nat) (ab: (mvector n)*(mvector n)),
      ChebyshevDistance ab = (compose InfinityNorm VMinus) ab.
  Proof.
    intros.
    unfold compose, ChebyshevDistance, VMinus.
    destruct ab.
    reflexivity.
  Qed.

  Fact breakdown_OChebyshevDistance:  forall (n:nat),
      HChebyshevDistance n = (HInfinityNorm ∘ HVMinus).
  Proof.
    intros n.
    apply HOperator_functional_extensionality; intros v.
    unfold Lst, compose.
    apply Vcons_single_elim.
    apply breakdown_ChebyshevDistance.
  Qed.

  Lemma breakdown_VMinus:  forall (n:nat) (ab: (mvector n)*(mvector n)),
      VMinus ab =  BinOp (IgnoreIndex2 (compose plus negate)) ab.
  Proof.
    intros.
    unfold VMinus, BinOp.
    break_let.
    apply Vmap2Indexed_to_VMap2.
    crush.
  Qed.

  Fact breakdown_OVMinus:  forall (n:nat),
      HVMinus = HBinOp (o:=n) (IgnoreIndex2 (compose plus negate)).
  Proof.
    intros n.
    apply HOperator_functional_extensionality; intros v.
    unfold HVMinus.
    unfold compose at 2.
    unfold vector2pair.
    apply breakdown_VMinus.
  Qed.

  Fact breakdown_OTLess_Base: forall
      {i1 i2 o}
      `{o1pf: !HOperator (o1: mvector i1 -> mvector o)}
      `{o2pf: !HOperator (o2: mvector i2 -> mvector o)},
      HTLess o1 o2 = (HBinOp (IgnoreIndex2 Zless) ∘ HCross o1 o2).
  Proof.
    intros i1 i2 o o1 po1 o2 po2.
    apply HOperator_functional_extensionality; intros v.
    unfold HTLess, HBinOp, HCross.
    unfold HCompose, compose, BinOp.
    simpl.
    rewrite vp2pv.
    repeat break_let.
    unfold vector2pair in Heqp.
    rewrite Heqp in Heqp1.
    inversion Heqp0.
    inversion Heqp1.
    apply Vmap2Indexed_to_VMap2.
    crush.
  Qed.

End HCOLBreakdown.


(* Our top-level example goal *)
Theorem DynWinOSPL:  forall (a: mvector 3),
    (HTLess
       (HEvalPolynomial a)
       (HChebyshevDistance 2))
    =
    (HBinOp (IgnoreIndex2 Zless) ∘
            HCross
            ((HReduction plus 0 ∘ HBinOp (IgnoreIndex2 mult)) ∘ (HPrepend a ∘ HInduction _ mult 1))
            (HReduction MaxAbs 0 ∘ HBinOp (o:=2) (IgnoreIndex2 (compose plus negate)))).
Proof.
  intros a.
  rewrite breakdown_OTLess_Base.
  rewrite breakdown_OEvalPolynomial.
  rewrite breakdown_OScalarProd.
  rewrite breakdown_OMonomialEnumerator.
  rewrite breakdown_OChebyshevDistance.
  rewrite breakdown_OVMinus.
  rewrite breakdown_OTInfinityNorm.
  apply HOperator_functional_extensionality.
  reflexivity.
Qed.

