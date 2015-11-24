
Require Import Spiral.
Require Import Rtheta.
Require Import SVector.

Require Import HCOL.
Require Import HCOLSyntax.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program. 

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Open Scope vector_scope.


Definition MaxAbs (a b:Rtheta): Rtheta := max (abs a) (abs b).

Global Instance MaxAbs_proper:
  Proper ((=) ==> (=) ==> (=)) (MaxAbs).
Proof.
  intros a a' aE b b' bE.
  unfold MaxAbs.
  rewrite aE, bE.
  reflexivity.
Qed.

Definition orig_exp (a: svector 3) :=
  HOTLess 
    (HOEvalPolynomial a)
    (HOChebyshevDistance 2).

Definition rewritten_exp (a: svector 3) :=
  HOBinOp Zless ∘
          HOCross
          ((HOReduction plus 0 ∘ HOBinOp mult) ∘ (HOPrepend a ∘ HOInduction mult 1))
          (HOReduction MaxAbs 0 ∘ HOBinOp (o:=2) (plus∘negate)).

Section HCOLBreakdown.

  Import HCOLOperators.

    Context
    `{Ae: Equiv A}
    `{Az: Zero A} `{A1: One A}
    `{Aplus: Plus A} `{Amult: Mult A} 
    `{Aneg: Negate A}
    `{Ale: Le A}
    `{Alt: Lt A}
    `{Ato: !@TotalOrder A Ae Ale}
    `{Aabs: !@Abs A Ae Ale Az Aneg}
    `{Asetoid: !@Setoid A Ae}
    `{Aledec: !∀ x y: A, Decision (x ≤ y)}
    `{Aeqdec: !∀ x y, Decision (x = y)}
    `{Altdec: !∀ x y: A, Decision (x < y)}
    `{Ar: !Ring A}
    `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
    `{ASSO: !@StrictSetoidOrder A Ae Alt}
  .
  
  Add Ring RingA: (stdlib_ring_theory A).

  Lemma breakdown_ScalarProd: forall (n:nat) (a v: svector n),
      ScalarProd (a,v) = 
      ((Reduction (+) 0) ∘ (BinOp (.*.))) (a,v).
  Proof.
    intros n a v.
    unfold compose, BinOp, Reduction, ScalarProd.
    reflexivity.
  Qed.
  
  Fact breakdown_OScalarProd: forall {h:nat} v, 
      HOScalarProd (h:=h) v
      =
      ((HOReduction  (+) 0) ∘ (HOBinOp (.*.))) v.
  Proof.
    intros h v.
    unfold HOScalarProd, HOReduction, HOBinOp.
    unfold vector2pair, compose, Lst, Vectorize.
    apply Vcons_single_elim.
    destruct (Vbreak v).
    apply breakdown_ScalarProd.
  Qed.
  
  Lemma breakdown_EvalPolynomial: forall (n:nat) (a: svector (S n)) (v:Rtheta),
      EvalPolynomial a v = (
        (ScalarProd) ∘ (pair a) ∘ (MonomialEnumerator n)
      ) v.
  Proof.
    intros n a v.
    unfold compose.
    induction n.
    - simpl (MonomialEnumerator 0 v).
      rewrite EvalPolynomial_reduce.
      dep_destruct (Vtail a).
      simpl; ring.
      
    - rewrite EvalPolynomial_reduce, ScalarProd_reduce, MonomialEnumerator_cons.
      unfold Ptail.
      rewrite ScalarProd_comm.

      Opaque Scale ScalarProd. 
      simpl.
      Transparent Scale ScalarProd.

      rewrite ScalarProduct_hd_descale, IHn, mult_1_r, ScalarProd_comm.
      reflexivity.
  Qed.
  
  Fact breakdown_OEvalPolynomial: forall (n:nat) (a: svector (S n)) v,
      HOEvalPolynomial a v =
      (HOScalarProd ∘
                    ((HOPrepend  a) ∘
                                    (HOMonomialEnumerator n))) v.
  Proof.
    intros n a v.
    unfold HOEvalPolynomial, HOScalarProd, HOPrepend, HOMonomialEnumerator.
    unfold vector2pair, compose, Lst, Scalarize.
    rewrite Vcons_single_elim, Vbreak_app.
    apply breakdown_EvalPolynomial.
  Qed.
    
  Lemma breakdown_TInfinityNorm:  forall (n:nat) (v: svector n),
                                   InfinityNorm v = (Reduction MaxAbs 0) v.
  Proof.
    intros.
    unfold InfinityNorm, Reduction.

    dependent induction v.
    - reflexivity.
    - rewrite Vfold_right_reduce.
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
          
        + apply Rtheta_TotalOrder.
          rewrite Vfold_right_reduce, IHv, <- abs_max_comm_2nd.
          reflexivity.
      }
      unfold MaxAbs.
      rewrite ABH.
      reflexivity.
  Qed.

  Fact breakdown_OTInfinityNorm:  forall (n:nat) (v:svector n),
                                    HOInfinityNorm v  =
                                    HOReduction MaxAbs 0 v.
  Proof.
    intros n v.
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
    forall (n:nat) (v:svector 1),
      HOMonomialEnumerator n v =
      HOInduction (.*.) 1 v.
  Proof.
    intros n v.
    apply breakdown_MonomialEnumerator.
  Qed.

  Lemma breakdown_ChebyshevDistance:  forall (n:nat) (ab: (svector n)*(svector n)),
      ChebyshevDistance ab = (InfinityNorm  ∘ VMinus) ab.
  Proof.
    intros.
    unfold compose, ChebyshevDistance, VMinus.
    destruct ab.
    reflexivity.
  Qed.
  
  Fact breakdown_OChebyshevDistance:  forall (n:nat) v,
      HOChebyshevDistance n v = (HOInfinityNorm ∘ HOVMinus) v.
  Proof.
    intros n v.
    unfold Lst, compose.
    apply Vcons_single_elim.
    apply breakdown_ChebyshevDistance.
  Qed.
  
  Lemma breakdown_VMinus:  forall (n:nat) (ab: (svector n)*(svector n)),
      VMinus ab =  BinOp (plus∘negate) ab.
  Proof.
    crush.
  Qed.

  Fact breakdown_OVMinus:  forall (n:nat) (v:svector (n+n)),
      HOVMinus v = HOBinOp (plus∘negate) v.
  Proof.
    intros n v.
    unfold HOVMinus.
    unfold compose at 2.
    unfold vector2pair.
    apply breakdown_VMinus.
  Qed.
  
  Fact breakdown_OTLess_Base: forall
      {i1 i2 o}
      (o1: svector i1 -> svector o)
      (o2: svector i2 -> svector o)
      (v:svector (i1 + i2)),
      HOTLess o1 o2 v = (HOBinOp Zless ∘ HOCross o1 o2) v.
  Proof.
    intros i1 i2 o o1 o2 v.
    unfold HOTLess, HOBinOp, HOCross.
    unfold compose, BinOp.
    rewrite vp2pv.
    elim (vector2pair i1 v).
    reflexivity.
  Qed.

End HCOLBreakdown.


  (* Our top-level example goal *)
  Definition DynWinOSPL_def :=  forall (a: vector A 3),
                         HOTLess 1 4 1
                                 (HOEvalPolynomial a)
                                 (HOChebyshevDistance 2)
                         = HOCompose _ _
                                     (HOBinOp _ (Zless))
                                     (HOCross _ _ _ _
                                              (HOCompose _ _ 
                                                         (HOCompose _ _
                                                                    (HOReduction  _ (+) 0)
                                                                    (HOBinOp _ (.*.)))
                                                         (HOCompose _ _
                                                                    (HOPrepend _ a)
                                                                    (HOInduction _ (.*.) 1))
                                              )
                                              (HOCompose 4 _
                                                         (HOReduction _ MaxAbs 0)
                                                         (HOBinOp 2 (plus∘negate))
                                     )).

                           
  Theorem DynWinOSPL:   DynWinOSPL_def.
 Proof.
    unfold DynWinOSPL_def. intros. apply HCOL_extensionality.  intros.
    rewrite breakdown_OTLess_Base.
    rewrite breakdown_OEvalPolynomial.    
    rewrite breakdown_OScalarProd. 
    rewrite breakdown_OMonomialEnumerator.
    rewrite breakdown_OChebyshevDistance.
    rewrite breakdown_OVMinus.
    rewrite breakdown_OTInfinityNorm.
    reflexivity.
  Qed.
  
