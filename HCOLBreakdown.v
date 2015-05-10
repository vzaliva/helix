
Require Import Spiral.
Import Spiral.

Require Import HCOL.
Import HCOLOperators.
Require Import HCOLSyntax.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program. (* compose *)

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


Section HCOLBreakdown.
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
  
  Open Scope vector_scope.


  Definition MaxAbs (a b:A): A := max (abs a) (abs b).

  Global Instance MaxAbs_proper:
    Proper ((=) ==> (=) ==> (=)) (MaxAbs).
  Proof.
    intros a a' aE b b' bE.
    unfold MaxAbs.
    rewrite aE, bE.
    reflexivity.
  Qed.
  
  
  Lemma breakdown_ScalarProd: forall (n:nat) (a v: vector A n),
                                  ScalarProd (a,v) = 
                                  ((Reduction (+) 0) ∘ (PointWise2 (.*.))) (a,v).
  Proof.
    intros.
    unfold compose, PointWise2, Reduction, ScalarProd.
    reflexivity.
  Qed.

  Fact breakdown_OScalarProd: forall {h:nat},
                                HOScalarProd (h:=h)
                                =
                                HOCompose _ _
                                                    (HOReduction  _ (+) 0)
                                                    (HOPointWise2 _ (.*.)).
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    unfold vector2pair, compose, Lst.
    apply Vcons_single_elim.
    destruct  (Vbreak v).
    apply breakdown_ScalarProd.
  Qed.
  
  Lemma breakdown_EvalPolynomial: forall (n:nat) (a: vector A (S n)) (v:A),
                                   EvalPolynomial a v = (
                                     (ScalarProd) ∘ (Pair a) ∘ (MonomialEnumerator n)
                                   ) v.
  Proof.
    intros.
    unfold compose.
    induction n.
    simpl (MonomialEnumerator 0 v).
    rewrite EvalPolynomial_reduce.
    rewrite t0_nil with (x:=(Vtail a)).
    rewrite EvalPolynomial_0.
    unfold ScalarProd.
    simpl.
    rewrite mult_1_r, mult_0_r.
    reflexivity.

    rewrite EvalPolynomial_reduce.
    rewrite ScalarProd_reduce.
    
    assert (SR:SemiRing A). admit.   (* TODO!!! *)
    Set Typeclasses Debug.    
    rewrite MonomialEnumerator_reduce.
    
    unfold Ptail, Pair.
    rewrite ScalarProd_comm.
    replace (Vtail (Vcons 1 (Scale (v, MonomialEnumerator n v)))) with (Scale (v, MonomialEnumerator n v)) by auto.
    rewrite ScalarProduct_hd_descale.
    rewrite IHn. clear IHn.
    simpl  (Vhead (fst (a, Vcons 1 (Scale (v, MonomialEnumerator n v))))).
    simpl (Vhead (snd (a, Vcons 1 (Scale (v, MonomialEnumerator n v))))).    
    rewrite mult_1_r.
    unfold Pair.
    rewrite ScalarProd_comm.
    reflexivity.
  Qed.

  Fact breakdown_OEvalPolynomial: forall (n:nat) (a: vector A (S n)),
                                    HOEvalPolynomial a =
                                    HOCompose _ _
                                              (HOScalarProd)
                                              (HOCompose _ _
                                                         (HOAppend _ a)
                                                         (HOMonomialEnumerator _)).
                                             
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    unfold vector2pair, compose, Lst.
    apply Vcons_single_elim.
    rewrite Vbreak_app.
    apply breakdown_EvalPolynomial.
  Qed.
  
  
  Lemma breakdown_TInfinityNorm:  forall (n:nat) (v: vector A n),
                                   InfinityNorm v = (Reduction MaxAbs 0) v.
  Proof.
    intros.
    unfold InfinityNorm, Reduction.

    dependent induction v.
    Case "[]".
    VOtac.
    reflexivity.
    
    Case "Cons v".
    rewrite Vfold_right_reduce.
    simpl.
    rewrite IHv. clear IHv.
    simpl.

    assert (ABH: (abs (Vfold_right MaxAbs v 0)) =
                 (Vfold_right MaxAbs v 0)).
    unfold MaxAbs.
    intros.
    dependent induction v.
    SCase "v=[]".
    simpl.
    apply abs_0_s.
    (* rewrite le_equiv_lt. *)
    apply Ato.
    SCase "w!=[]".
    rewrite Vfold_right_reduce.
    simpl.

    rewrite IHv. clear IHv.
    rewrite <- abs_max_comm_2nd.
    reflexivity.
    unfold MaxAbs.
    rewrite ABH.
    reflexivity.
  Qed.

  Fact breakdown_OTInfinityNorm:  forall (n:nat),
                                    HOInfinityNorm  =
                                    HOReduction n MaxAbs 0.
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    apply Vcons_single_elim.
    apply breakdown_TInfinityNorm.
  Qed.
  
  Lemma breakdown_MonomialEnumerator:
    forall (n:nat) (x:A), 
      MonomialEnumerator n x = Induction (S n) (.*.) 1 x.
  Proof.
    intros.
    induction n.
    Case "n=0".
    reflexivity.
    Case "n=(S _)". 
    rewrite MonomialEnumerator_reduce.
    rewrite IHn. clear IHn.
    symmetry.
    rewrite Induction_reduce by apply Asetoid.
    unfold Scale.
    rewrite 2!Vmap_to_Vmap_reord.
    setoid_replace (fun x0 : A => mult x0 x) with (mult x).
    reflexivity.
    SCase "ext_eqiuv".     
    compute. intros.
    rewrite H. apply mult_comm.
  Qed.

  Fact breakdown_OMonomialEnumerator:
    forall (n:nat),
      HOMonomialEnumerator n =
      HOInduction _ (.*.) 1.
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    unfold compose.
    apply breakdown_MonomialEnumerator.
  Qed.

  Lemma breakdown_ChebyshevDistance:  forall (n:nat) (ab: (vector A n)*(vector A n)),
                                       ChebyshevDistance ab = (InfinityNorm  ∘ VMinus) ab.
  Proof.
    intros.
    unfold compose, ChebyshevDistance, VMinus.
    destruct ab.
    reflexivity.
  Qed.
  
  Fact breakdown_OChebyshevDistance:  forall (n:nat) ,
                                        HOChebyshevDistance n =
                                        HOCompose _ _
                                                  (HOInfinityNorm)
                                                  (HOVMinus _)
                                                 .
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    unfold Lst, compose.
    apply Vcons_single_elim.
    apply breakdown_ChebyshevDistance.
  Qed.
      
  Lemma breakdown_VMinus:  forall (n:nat) (ab: (vector A n)*(vector A n)),
                            VMinus ab =  PointWise2 (plus∘negate) ab.
  Proof.
    crush.
  Qed.

  Fact breakdown_OVMinus:  forall (n:nat) ,
                             HOVMinus _ =
                             HOPointWise2 n (plus∘negate).
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    unfold compose at 2.
    unfold vector2pair.
    apply breakdown_VMinus.
  Qed.
  
  Fact breakdown_OTLess_Base: forall
                               (i1 i2 o:nat)
                               (o1: HOperator i1 o)
                               (o2: HOperator i2 o),
                               
                               HOTLess i1 i2 o o1 o2 =
                               HOCompose _ _
                                         (HOPointWise2 o (Zless))
                                         (HOCross i1 o i2 o o1 o2).
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL at 1.
    fold (evalHCOL o1)  (evalHCOL o2).
    unfold evalHCOL at 3.
    fold (evalHCOL o1)  (evalHCOL o2).
    unfold compose, PointWise2.
    rewrite vp2pv.    
    elim (vector2pair i1 v).
    intros.
    unfold ZVLess.
    unfold Cross.
    reflexivity.
  Qed.


  (* Our top-level example goal *)
  Theorem DynWinOSPL:  forall (a: vector A 3),
                         HOTLess 1 4 1
                                 (HOEvalPolynomial a)
                                 (HOChebyshevDistance 2)
                         = HOCompose _ _
                                     (HOPointWise2 _ (Zless))
                                     (HOCross _ _ _ _
                                              (HOCompose _ _ 
                                                         (HOCompose _ _
                                                                    (HOReduction  _ (+) 0)
                                                                    (HOPointWise2 _ (.*.)))
                                                         (HOCompose _ _
                                                                    (HOPrepend _ a)
                                                                    (HOInduction _ (.*.) 1))
                                              )
                                              (HOCompose 4 _
                                                         (HOReduction _ MaxAbs 0)
                                                         (HOPointWise2 2 (plus∘negate))
                                              )).
  Proof.
    intros. apply HCOL_extensionality.  intros.
    rewrite breakdown_OTLess_Base.
    rewrite breakdown_OEvalPolynomial.    
    rewrite breakdown_OScalarProd. 
    rewrite breakdown_OMonomialEnumerator.
    rewrite breakdown_OChebyshevDistance.
    rewrite breakdown_OVMinus.
    rewrite breakdown_OTInfinityNorm.
    reflexivity.
  Qed.
  
  Close Scope vector_scope.
  
End HCOLBreakdown.
