
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

Context
  `{Plus Rtheta}
  `{Mult Rtheta}
  `{Negate Rtheta}
  `{Lt Rtheta}.

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
  
  Lemma breakdown_ScalarProd: forall (n:nat) (a v: vector A n),
    ScalarProd (a,v) = 
    ((Reduction (+) 0) ∘ (BinOp (.*.))) (a,v).
  Proof.
    intros.
    unfold compose, BinOp, Reduction, ScalarProd.
    reflexivity.
  Qed.

  Fact breakdown_OScalarProd: forall {h:nat},
                                HOScalarProd (h:=h)
                                =
                                HOCompose _ _
                                                    (HOReduction  _ (+) 0)
                                                    (HOBinOp _ (.*.)).
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL.
    unfold vector2pair, compose, Lst, Vectorize.
    apply Vcons_single_elim.
    destruct  (Vbreak v).
    apply breakdown_ScalarProd.
  Qed.
  
  Lemma breakdown_EvalPolynomial: forall (n:nat) (a: vector A (S n)) (v:A),
                                   EvalPolynomial a v = (
                                     (ScalarProd) ∘ (pair a) ∘ (MonomialEnumerator n)
                                   ) v.
  Proof.
    intros.
    unfold compose.
    induction n.
    simpl (MonomialEnumerator 0 v).
    rewrite EvalPolynomial_reduce.
    dep_destruct (Vtail a).
    rewrite EvalPolynomial_0.
    unfold ScalarProd.
    simpl.
    rewrite mult_1_r, mult_0_r.
    reflexivity.

    rewrite EvalPolynomial_reduce.
    rewrite ScalarProd_reduce.
    rewrite MonomialEnumerator_cons.
    unfold Ptail.
    rewrite ScalarProd_comm.
    replace (Vtail (Vcons 1 (Scale (v, MonomialEnumerator n v)))) with (Scale (v, MonomialEnumerator n v)) by auto.
    rewrite ScalarProduct_hd_descale.
    rewrite IHn. clear IHn.
    simpl  (Vhead (fst (a, Vcons 1 (Scale (v, MonomialEnumerator n v))))).
    simpl (Vhead (snd (a, Vcons 1 (Scale (v, MonomialEnumerator n v))))).    
    rewrite mult_1_r.
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
    rewrite MonomialEnumerator_cons.
    rewrite Vcons_to_Vcons_reord.
    rewrite IHn. clear IHn.
    symmetry.
    rewrite Induction_cons by apply Asetoid.
    rewrite Vcons_to_Vcons_reord.
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
                            VMinus ab =  BinOp (plus∘negate) ab.
  Proof.
    crush.
  Qed.

  Fact breakdown_OVMinus:  forall (n:nat) ,
                             HOVMinus _ =
                             HOBinOp n (plus∘negate).
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
                                         (HOBinOp o (Zless))
                                         (HOCross i1 o i2 o o1 o2).
  Proof.
    intros. apply HCOL_extensionality.  intros.
    unfold evalHCOL at 1.
    fold (evalHCOL o1)  (evalHCOL o2).
    unfold evalHCOL at 3.
    fold (evalHCOL o1)  (evalHCOL o2).
    unfold compose, BinOp.
    rewrite vp2pv.    
    elim (vector2pair i1 v).
    intros.
    unfold ZVLess.
    unfold Cross.
    reflexivity.
  Qed.


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
  
  Close Scope vector_scope.
  
End HCOLBreakdown.
