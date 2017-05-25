Require Import VecUtil.
Require Import VecSetoid.
Require Import SVector.
Require Import Spiral.
Require Import CarrierType.

Require Import HCOL.
Require Import HCOLImpl.
Require Import THCOL.
Require Import THCOLImpl.
Require Import Rtheta.
Require Import SigmaHCOL.
Require Import TSigmaHCOL.
Require Import IndexFunctions.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program.

Require Import SpiralTactics.

Require Import HCOLBreakdown.
Require Import SigmaHCOLRewriting.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.

Section HCOL_breakdown.

  (* Original dynamic window expression *)
  Definition dynwin_orig (a: avector 3) :=
    (HTLess
       (HEvalPolynomial a)
       (HChebyshevDistance 2)).

  (* dynamic window HCOL expression *)
  Definition dynwin_HCOL (a: avector 3) :=
    (HBinOp (IgnoreIndex2 Zless) ∘
            HCross
            ((HReduction plus 0 ∘ HBinOp (IgnoreIndex2 mult)) ∘ (HPrepend a ∘ HInduction _ mult 1))
            (HReduction minmax.max 0 ∘ (HPointwise (IgnoreIndex abs)) ∘ HBinOp (o:=2) (IgnoreIndex2 sub))).


  (* Initial HCOL breakdown proof *)
  Theorem DynWinHCOL:  forall (a: avector 3),
      dynwin_orig a = dynwin_HCOL a.
  Proof.
    intros a.
    unfold dynwin_orig, dynwin_HCOL.
    rewrite breakdown_OTLess_Base.
    rewrite breakdown_OEvalPolynomial.
    rewrite breakdown_OScalarProd.
    rewrite breakdown_OMonomialEnumerator.
    rewrite breakdown_OChebyshevDistance.
    rewrite breakdown_OVMinus.
    rewrite breakdown_OTInfinityNorm.
    HOperator_reflexivity.
  Qed.

End HCOL_breakdown.


Section SigmaHCOL_rewriting.

  Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

  (* --- HCOL -> Sigma->HCOL --- *)

  (*
Final Sigma-HCOL expression:

BinOp(1, Lambda([ r14, r15 ], geq(r15, r14))) o
SUMUnion(
  ScatHUnion(2, 1, 0, 1) o
  Reduction(3, (a, b) -> add(a, b), V(0.0), (arg) -> false) o
  PointWise(3, Lambda([ r16, i14 ], mul(r16, nth(D, i14)))) o
  Induction(3, Lambda([ r9, r10 ], mul(r9, r10)), V(1.0)) o
  GathH(5, 1, 0, 1),

  ScatHUnion(2, 1, 1, 1) o
  Reduction(2, (a, b) -> max(a, b), V(0.0), (arg) -> false) o
  PointWise(2, Lambda([ r11, i13 ], abs(r11))) o
  ISumUnion(i15, 2,
    ScatHUnion(2, 1, i15, 1) o
    BinOp(1, Lambda([ r12, r13 ], sub(r12, r13))) o
    GathH(4, 2, i15, 2)
  ) o
  GathH(5, 4, 1, 1)
)
   *)
  Definition dynwin_SHCOL (a: avector 3) :=
    (SafeCast (SHBinOp (IgnoreIndex2 THCOLImpl.Zless)))
      ⊚
      (HTSUMUnion _ plus (
                    ScatH _ 0 1
                          (range_bound := h_bound_first_half 1 1)
                          (snzord0 := @ScatH_stride1_constr 1 2)
                          ⊚
                          (liftM_HOperator _ (@HReduction _ plus CarrierAPlus_proper 0)  ⊚
                                           SafeCast (SHBinOp (IgnoreIndex2 mult))
                                           ⊚
                                           liftM_HOperator _ (HPrepend a )
                                           ⊚
                                           liftM_HOperator _ (HInduction 3 mult one))
                          ⊚
                          (GathH _ 0 1
                                 (domain_bound := h_bound_first_half 1 (2+2)))
                  )

                  (
                    (ScatH _ 1 1
                           (range_bound := h_bound_second_half 1 1)
                           (snzord0 := @ScatH_stride1_constr 1 2))
                      ⊚
                      (liftM_HOperator _ (@HReduction _ minmax.max _ 0))
                      ⊚
                      (SHPointwise _ (IgnoreIndex abs))
                      ⊚
                      (USparseEmbedding
                         (n:=2)
                         (mkSHOperatorFamily Monoid_RthetaFlags _ _ _
                                             (fun j _ => SafeCast (SHBinOp (o:=1)
                                                                        (SwapIndex2 j (IgnoreIndex2 HCOLImpl.sub)))))
                         (IndexMapFamily 1 2 2 (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j 2 1 jc))))
                         (f_inj := h_j_1_family_injective)
                         (IndexMapFamily _ _ 2 (fun j jc => h_index_map j 2 (range_bound:=GathH_jn_domain_bound j 2 jc))))
                      ⊚
                      (GathH _ 1 1
                             (domain_bound := h_bound_second_half 1 (2+2)))
                  )
      ).


  (* HCOL -> SigmaHCOL Value correctness. *)
  Theorem DynWinSigmaHCOL_Value_Correctness
          (a: avector 3)
    :
      liftM_HOperator Monoid_RthetaFlags (dynwin_HCOL a)
      =
      dynwin_SHCOL a.
  Proof.
    unfold dynwin_HCOL, dynwin_SHCOL.
    setoid_rewrite LiftM_Hoperator_compose.
    setoid_rewrite expand_HTDirectSum. (* this one does not work with Diamond'_arg_proper *)
    repeat setoid_rewrite LiftM_Hoperator_compose.
    repeat setoid_rewrite <- SHBinOp_equiv_lifted_HBinOp at 1.
    repeat setoid_rewrite <- SHPointwise_equiv_lifted_HPointwise at 1.
    setoid_rewrite expand_BinOp at 3.

    (* normalize associativity of composition *)
    repeat rewrite <- SHCompose_assoc.

    reflexivity.
  Qed.

  Require Import FinNatSet.

  (*Ltac break_Union :=
    match goal with
    | Union _ ?a ?b; idtac a
    end.
   *)

  Theorem DynWinSigmaHCOL_dense_input
          (a: avector 3)
    : Same_set _ (in_index_set _ (dynwin_SHCOL a)) (Full_set (FinNat _)).
  Proof.
    split.
    -
      unfold Included.
      intros [x xc].
      intros H.
      apply Full_intro.
    -
      unfold Included.
      intros x.
      intros H. clear H.
      unfold In in *.
      simpl.
      destruct x as [x xc].
      destruct x.
      +
        apply Union_introl.
        compute; tauto.
      +
        apply Union_intror.
        compute in xc.
        unfold In.
        unfold index_map_range_set.
        repeat (destruct x; crush).
  Qed.

  Theorem DynWinSigmaHCOL_dense_output
          (a: avector 3)
    : Same_set _ (out_index_set _ (dynwin_SHCOL a)) (Full_set (FinNat _)).
  Proof.
    split.
    -
      unfold Included.
      intros [x xc].
      intros H.
      apply Full_intro.
    -
      unfold Included.
      intros x.
      intros H. clear H.
      unfold In in *.
      simpl.
      apply Full_intro.
  Qed.

  Fact two_index_maps_span_I_2
       (x : FinNat 2)
       (b2 : forall (x : nat) (_ : x < 1), 0 + (x * 1) < 2)
       (b1 : forall (x : nat) (_ : x < 1), 1 + (x * 1) < 2)
    :
      Union (@sig nat (fun x0 : nat => x0 < 2))
            (@index_map_range_set 1 2 (@h_index_map 1 2 1 1 b1))
            (@index_map_range_set 1 2 (@h_index_map 1 2 O 1 b2)) x.
  Proof.
    let lu := fresh "LU" in
    let ru := fresh "RU" in
    match goal with
    | [ |- Union ?t ?a ?b ?x] => remember a as lu; remember b as ru
    end.

    destruct x as [x xc].
    dep_destruct x.
    -
      assert(H: RU (@mkFinNat 2 0 xc)).
      {
        subst RU.
        compute.
        tauto.
      }
      apply Union_introl with (C:=LU) in H.
      apply Union_comm.
      apply H.
    -
      destruct x0.
      +
        assert(H: LU (@mkFinNat 2 1 xc)).
        {
          subst LU.
          compute.
          tauto.
        }
        apply Union_intror with (B:=RU) in H.
        apply Union_comm.
        apply H.
      +
        crush.
  Qed.

  Fact two_h_index_maps_disjoint
       (m n: nat)
       (mnen : m ≢ n)
       (b2 : forall (x : nat) (_ : x < 1), n + (x*1) < 2)
       (b1 : forall (x : nat) (_ : x < 1), m + (x*1) < 2)
    :
      Disjoint (FinNat 2)
               (@index_map_range_set 1 2 (@h_index_map 1 2 m 1 b1))
               (@index_map_range_set 1 2 (@h_index_map 1 2 n 1 b2)).
  Proof.
    apply Disjoint_intro.
    intros x.
    unfold not, In.
    intros H.
    inversion H. clear H.
    subst.
    unfold In in *.
    unfold index_map_range_set in *.
    apply in_range_exists in H0.
    apply in_range_exists in H1.

    destruct H0 as [x0 [x0c H0]].
    destruct H1 as [x1 [x1c H1]].
    destruct x as [x xc].
    simpl in *.
    subst.
    crush.
    crush.
    crush.
  Qed.

  (* Presently the following proof is not automated. However it lends itself to automation. Few ideas for future:
      1. Reister _Facts class instances in a separate namespace
      2. Write a tactic which attempts to apply approriate instance
      3. Tactic should work repeatedly. For non-instance goals it encounter:
          1. Try [crush]
          2. Try [auto with typeclass_instances
          3. Look at goal after [crush] and if it is a set membership statement try to deveop custom tactics solving these types of problems specific to our application (with [index_range_set], [h_index_map], etc.)
   *)
  Instance DynWinSigmaHCOL_Facts
           (a: avector 3):
    SHOperator_Facts _ (dynwin_SHCOL a).
  Proof.
    unfold dynwin_SHCOL.

    apply SHCompose_Facts.
    apply SafeCast_Facts.
    apply SHBinOp_RthetaSafe_Facts.
    apply HTSUMUnion_Facts.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply Scatter_Rtheta_Facts.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply liftM_HOperator_Facts.
    apply MonoidLaws_RthetaFlags. (* or [auto with typeclass_instances]. *)
    apply SafeCast_Facts.
    apply SHBinOp_RthetaSafe_Facts.
    crush.
    apply liftM_HOperator_Facts. apply MonoidLaws_RthetaFlags.
    crush.
    apply liftM_HOperator_Facts. apply MonoidLaws_RthetaFlags.
    crush.
    crush.
    apply Gather_Facts.
    crush.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply Scatter_Rtheta_Facts.
    apply liftM_HOperator_Facts. apply MonoidLaws_RthetaFlags.
    crush.
    apply SHPointwise_Facts. apply MonoidLaws_RthetaFlags.
    crush.
    unfold USparseEmbedding.
    apply IUnion_Facts.

    intros.
    crush.
    apply SHCompose_Facts.
    apply SHCompose_Facts.
    apply Scatter_Rtheta_Facts.
    apply SafeCast_Facts.

    {
      match goal with
      | [ |- @SHOperator_Facts ?m ?i ?o (@SHBinOp ?o _ _) ] =>
        replace (@SHOperator_Facts m i) with (@SHOperator_Facts m (o+o)) by apply eq_refl
      end.
      apply SHBinOp_RthetaSafe_Facts.
    }

    crush.
    apply Gather_Facts.
    crush.
    {
      crush.
      apply two_h_index_maps_disjoint; assumption.
    }
    {
      crush.
      unfold Included, In.
      intros x H.
      replace (Union (FinNat 2) (index_map_range_set (h_index_map 0 1)) (Empty_set (FinNat 2))) with (@index_map_range_set (S O) (S (S O))
                                                                                                                           (@h_index_map (S O) (S (S O)) O (S O)
                                                                                                                                         (ScatH_1_to_n_range_bound O (S (S O)) (S O) (@le_S (S O) (S O) (le_n (S O)))))).
      -
        apply two_index_maps_span_I_2.
      -
        apply Extensionality_Ensembles.
        apply Union_Empty_set_lunit.
        apply h_index_map_range_set_dec.
    }
    apply Gather_Facts.
    {
      crush.
      unfold Included.
      intros x H.
      apply Full_intro.
    }
    {
      crush.
      apply two_h_index_maps_disjoint.
      unfold peano_naturals.nat_lt, peano_naturals.nat_plus,
      peano_naturals.nat_1, one, plus, lt.
      crush.
    }
    {
      crush.
      unfold Included, In.
      intros x H.
      apply Union_comm.
      apply two_index_maps_span_I_2.
    }
  Qed.

  (* --- SigmaHCOL -> Sigma->HCOL --- *)

  Parameter dynwin_SHCOL1: (avector 3) -> @SHOperator Monoid_RthetaFlags (1+(2+2)) 1.

  Theorem DynWinSigmaHCOL1_Value_Correctness
          (a: avector 3)
    :
      dynwin_SHCOL a
      =
      dynwin_SHCOL1 a.
  Proof.
    unfold dynwin_SHCOL.
    unfold USparseEmbedding.

    (* normalize to left-associativity of compose *)
    repeat rewrite <- SHCompose_assoc.
    rewrite SHCompose_mid_assoc with (g:=SHPointwise _ _).

    setoid_rewrite rewrite_PointWise_ISumUnion.
    Focus 2.
    intros j jc.
    apply abs_0_s.
    Focus 2.
    apply SparseEmbedding_Apply_Family_Single_NonZero_Per_Row.



  Admitted.

End SigmaHCOL_rewriting.
