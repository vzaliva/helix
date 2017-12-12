
Require Import Spiral.VecUtil.
Require Import Spiral.VecSetoid.
Require Import Spiral.SVector.
Require Import Spiral.Spiral.
Require Import Spiral.CarrierType.

Require Import Spiral.HCOL.
Require Import Spiral.HCOLImpl.
Require Import Spiral.THCOL.
Require Import Spiral.THCOLImpl.
Require Import Spiral.Rtheta.
Require Import Spiral.SigmaHCOL.
Require Import Spiral.TSigmaHCOL.
Require Import Spiral.IndexFunctions.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import Spiral.SpiralTactics.
Require Import Spiral.HCOLBreakdown.
Require Import Spiral.SigmaHCOLRewriting.

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
    (SafeCast (SHBinOp _ (IgnoreIndex2 THCOLImpl.Zless)))
      ⊚
      (HTSUMUnion _ plus (
                    ScatH _ 0 1
                          (range_bound := h_bound_first_half 1 1)
                          (snzord0 := @ScatH_stride1_constr 1 2)
                          zero
                          ⊚
                          (liftM_HOperator _ (@HReduction _ plus CarrierAPlus_proper 0)  ⊚
                                           SafeCast (SHBinOp _ (IgnoreIndex2 mult))
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
                           (snzord0 := @ScatH_stride1_constr 1 2)
                           zero)
                      ⊚
                      (liftM_HOperator _ (@HReduction _ minmax.max _ 0))
                      ⊚
                      (SHPointwise _ (IgnoreIndex abs))
                      ⊚
                      (USparseEmbedding
                         (n:=2)
                         (mkSHOperatorFamily Monoid_RthetaFlags _ _ _
                                             (fun j jc => SafeCast (SHBinOp _ (o:=1)
                                                                        (Fin1SwapIndex2 (mkFinNat jc) (IgnoreIndex2 HCOLImpl.sub)))))
                         (IndexMapFamily 1 2 2 (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j 2 1 jc))))
                         (f_inj := h_j_1_family_injective)
                         zero
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
    rewrite LiftM_Hoperator_compose.
    rewrite expand_HTDirectSum. (* this one does not work with Diamond'_arg_proper *)
    Opaque SHCompose.
    repeat rewrite LiftM_Hoperator_compose.
    repeat rewrite <- SHBinOp_equiv_lifted_HBinOp at 1.
    repeat rewrite <- SHPointwise_equiv_lifted_HPointwise at 1.
    setoid_rewrite expand_BinOp at 3.

    (* normalize associativity of composition *)
    repeat rewrite <- SHCompose_assoc.

    reflexivity.
    Transparent SHCompose.
  Qed.

Require Import Spiral.FinNatSet.


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

  Ltac solve_facs :=
    repeat match goal with
           | [ |- SHOperator_Facts _ _ ] => apply SHBinOp_RthetaSafe_Facts
           | [ |- @SHOperator_Facts ?m ?i ?o (@SHBinOp _ ?o _ _) ] =>
             replace (@SHOperator_Facts m i) with (@SHOperator_Facts m (o+o)) by apply eq_refl
           | [ |- SHOperator_Facts _ _ ] => apply SHCompose_Facts
           | [ |- SHOperator_Facts _ _ ] => apply SafeCast_Facts
           | [ |- SHOperator_Facts _ _ ] => apply HTSUMUnion_Facts
           | [ |- SHOperator_Facts _ _ ] => apply SHCompose_Facts
           | [ |- SHOperator_Facts _ _ ] => apply Scatter_Rtheta_Facts
           | [ |- SHOperator_Facts _ _ ] => apply liftM_HOperator_Facts
           | [ |- SHOperator_Facts _ _ ] => apply Gather_Facts
           | [ |- SHOperator_Facts _ _ ] => apply SHPointwise_Facts
           | [ |- SHOperator_Facts _ _ ] => apply IUnion_Facts
           | [ |- SHOperator_Facts _ (USparseEmbedding _ _) ] => unfold USparseEmbedding

           | [ |- Monoid.MonoidLaws Monoid_RthetaFlags] => apply MonoidLaws_RthetaFlags
           | _ => crush
           end.

  Instance DynWinSigmaHCOL_Facts
           (a: avector 3):
    SHOperator_Facts _ (dynwin_SHCOL a).
  Proof.
    unfold dynwin_SHCOL.

    (* First resolve all SHOperator_Facts typeclass instances *)
    solve_facs.

    (* Now let's take care of remaining proof obligations *)
    -
      apply two_h_index_maps_disjoint.
      assumption.

    -
      unfold Included, In.
      intros x H.

      replace (Union _ _ (Empty_set _)) with (@index_map_range_set 1 2 (@h_index_map 1 2 0 1 (ScatH_1_to_n_range_bound 0 2 1 (@le_S 1 1 (le_n 1))))).
      +
        apply two_index_maps_span_I_2.
      +
        apply Extensionality_Ensembles.
        apply Union_Empty_set_lunit.
        apply h_index_map_range_set_dec.

    -
      unfold Included.
      intros x H.
      apply Full_intro.

    -
      apply two_h_index_maps_disjoint.
      unfold peano_naturals.nat_lt, peano_naturals.nat_plus,
      peano_naturals.nat_1, one, plus, lt.
      crush.

    -
      unfold Included, In.
      intros x H.
      apply Union_comm.
      apply two_index_maps_span_I_2.

  Qed.

  (* --- SigmaHCOL -> Sigma->HCOL --- *)

  Parameter dynwin_SHCOL1: (avector 3) -> @SHOperator Monoid_RthetaFlags (1+(2+2)) 1.

  (* Special case when results of 'g' comply to P. In tihs case we can discard 'g' *)
  Lemma Apply_Family_Vforall_P_move_P
        {fm} {P:Rtheta' fm → Prop}
        {i1 o2 o3 n}
        (f: @SHOperator fm  o2 o3)
        (g: @SHOperatorFamily fm i1 o2 n)
    :
      (forall x, Vforall P ((op fm f) x)) ->
      Apply_Family_Vforall_P fm P (SHOperatorFamilyCompose fm f g).
  Proof.
    unfold Apply_Family_Vforall_P.
    intros H x j jc.
    apply Vforall_nth_intro.
    intros t tc.

    unfold SHOperatorFamilyCompose.
    unfold get_family_op.
    simpl.

    unfold compose.
    generalize (op fm (family_member fm g j jc) x).
    clear x. intros x.
    specialize (H x).
    eapply Vforall_nth in H.
    apply H.
  Qed.

  (* TODO: move to SigmaHCOLRewriting *)
  Lemma ApplyFamily_SHOperatorFamilyCompose
        {i1 o2 o3 n}
        {fm}
        (f: @SHOperator fm o2 o3)
        (g: @SHOperatorFamily fm i1 o2 n)
        {x}
    : Apply_Family fm (SHOperatorFamilyCompose fm f g) x ≡
      Vmap (op fm f) (Apply_Family fm g x).
  Proof.
    unfold Apply_Family, Apply_Family', SHOperatorFamilyCompose.
    rewrite Vmap_Vbuild.
    reflexivity.
  Qed.

  Lemma SHPointwise_preserves_Apply_Family_Single_NonUnit_Per_Row
        {i1 o2 n}
        (fam : @SHOperatorFamily Monoid_RthetaFlags i1 o2 n)
        (H: Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags fam 0)
        (f: FinNat o2 -> CarrierA -> CarrierA)
        {f_mor: Proper (equiv ==> equiv ==> equiv) f}
        (A: forall (i : nat) (ic : i<o2) (v : CarrierA), 0 ≠ f (mkFinNat ic) v -> 0 ≠ v):
    Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags
                                        (SHOperatorFamilyCompose
                                           Monoid_RthetaFlags
                                           (SHPointwise Monoid_RthetaFlags f (n:=o2))
                                           fam)
                                            zero.
  Proof.
    unfold Apply_Family_Single_NonUnit_Per_Row in *.
    intros x.

    rewrite ApplyFamily_SHOperatorFamilyCompose.
    specialize (H x).
    generalize dependent (Apply_Family Monoid_RthetaFlags fam x).
    clear x.
    intros x H.

    unfold transpose, row, Vnth_aux.
    rewrite Vforall_Vbuild.
    intros k kc.
    rewrite Vmap_map.
    simpl.
    unfold Vunique.
    intros j0 jc0 j1 jc1.
    repeat rewrite Vnth_map.
    intros [H0 H1].
    rewrite SHPointwise'_nth in H0, H1.


    unfold transpose, row, Vnth_aux in H.
    rewrite Vforall_Vbuild in H.
    specialize (H k kc).
    unfold Vunique in H.
    specialize (H j0 jc0 j1 jc1).

    repeat rewrite Vnth_map in H.
    apply H. clear H.
    unfold compose in *.
    rewrite evalWriter_mkValue in H0,H1.

    split; eapply A; [apply H0 | apply H1].
  Qed.

  Lemma op_Vforall_P_SHPointwise
        {m n: nat}
        {fm: Monoid.Monoid RthetaFlags}
        {f: CarrierA -> CarrierA}
        `{f_mor: !Proper ((=) ==> (=)) f}
        {P: CarrierA -> Prop}
        (F: @SHOperator fm m n)
    :
      (forall x, P (f x)) ->
           op_Vforall_P fm (liftRthetaP P)
                        (SHCompose fm
                                   (SHPointwise (n:=n) fm (IgnoreIndex f))
                                   F).
  Proof.
    intros H.
    unfold op_Vforall_P.
    intros x.
    apply Vforall_nth_intro.
    intros i ip.

    unfold SHCompose.
    simpl.
    unfold compose.
    generalize (op fm F x).
    intros v.
    unfold SHPointwise'.
    rewrite Vbuild_nth.
    unfold liftRthetaP.
    rewrite evalWriter_Rtheta_liftM.
    unfold IgnoreIndex, const.
    apply H.
  Qed.

  Theorem DynWinSigmaHCOL1_Value_Correctness (a: avector 3)
    : dynwin_SHCOL a = dynwin_SHCOL1 a.
  Proof.
    unfold dynwin_SHCOL.
    unfold USparseEmbedding.

    (* normalize to left-associativity of compose *)
    repeat rewrite <- SHCompose_assoc.
    rewrite SHCompose_mid_assoc with (g:=SHPointwise _ _).

    (* ### RULE: Reduction_ISumReduction *)
    rewrite rewrite_PointWise_ISumUnion.
    all:revgoals.
    (* solve 2 sub-dependent goals *)
    { apply SparseEmbedding_Apply_Family_Single_NonZero_Per_Row. }
    { intros j jc; apply abs_0_s. }

    (* Re-associate compositions before applying next rule *)
    rewrite SHCompose_mid_assoc with (f:=ISumUnion _).

    (* ### RULE: Reduction_ISumReduction *)
    rewrite rewrite_Reduction_IReduction_max_plus.
    all:revgoals.
    {
      remember (SparseEmbedding _ _ _ _) as t.
      generalize dependent t.
      intros fam _.

      apply Apply_Family_Vforall_P_move_P.
      intros x.

      apply Vforall_nth_intro.
      intros t tc.
      rewrite SHPointwise_nth_eq.
      unfold Is_NonNegative, liftRthetaP.
      rewrite evalWriter_Rtheta_liftM.
      unfold IgnoreIndex, const.
      apply abs_always_nonneg.
    }

    {
      remember (SparseEmbedding _ _ _ _ _) as fam.

      assert(Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags fam 0).
      {
        subst fam.
        apply SparseEmbedding_Apply_Family_Single_NonZero_Per_Row.
      }
      generalize dependent fam.
      intros fam _ H. clear a.

      apply SHPointwise_preserves_Apply_Family_Single_NonUnit_Per_Row.
      +
        apply H.
      +
        intros i ic v V.
        unfold IgnoreIndex, const in V.
        apply ne_sym in V.
        apply ne_sym.
        apply abs_nz_nz, V.
    }

    repeat rewrite SHCompose_assoc.
    rewrite rewrite_ISumXXX_YYY_IReduction_GathH.
    repeat rewrite <- SHCompose_assoc.

    rewrite rewrite_PointWise_ScatHUnion by apply abs_0_s.

    unfold SparseEmbedding, SHOperatorFamilyCompose, UnSafeFamilyCast; simpl.
    setoid_rewrite SHCompose_assoc at 5.
    setoid_rewrite <- SHCompose_assoc at 1.

    (* --- BEGIN: hack ---
    I would expect the following to work here:

    setoid_rewrite rewrite_Reduction_ScatHUnion_max_zero with
        (fm := Monoid_RthetaFlags)
        (m := 4%nat)
        (n := 1%nat).

     But it does not (hangs forever), so we have to do some manual rewriting
     *)

    match goal with
    | [ |- context G [ mkSHOperatorFamily _ _ _ _ ?f ]] =>
      match f with
      | (fun j jc => UnSafeCast (?torewrite ⊚ ?rest )) =>
        setoid_replace
          (mkSHOperatorFamily _ _ _ _ f) with
            (mkSHOperatorFamily _ _ _ _
                                (fun (j:nat) (jc:j<2) => UnSafeCast rest))
      end
    end.
    all:revgoals.
    f_equiv.
    intros j jc.
    f_equiv.
    apply rewrite_Reduction_ScatHUnion_max_zero.

    (* --- END: hack --- *)

    Opaque SHCompose.
    (* Obligations for `rewrite_Reduction_ScatHUnion_max_zero` *)
    setoid_rewrite SHCompose_assoc.
    eapply op_Vforall_P_SHPointwise, abs_always_nonneg.

    (* Gettting ready to apply GathH_GathH *)

    unfold SHFamilyOperatorCompose.
    simpl.
    setoid_rewrite UnSafeCast_SHCompose.
    setoid_rewrite UnSafeCast_Gather.
    setoid_rewrite SHCompose_assoc at 5.
    setoid_rewrite GathH_fold.

    (* Finally apply the rule *)
    setoid_rewrite rewrite_GathH_GathH.

    (* Preparing to apply PointWise_BinOp rule *)
    setoid_rewrite (SafeCast_SHBinOp 1).
    setoid_rewrite (rewrite_PointWise_BinOp 1).

    (* A bit of cleanup - removing unecessary casts *)
    setoid_rewrite (SafeCast_SHBinOp 3).
    setoid_rewrite (UnSafeCast_SHBinOp 1).

    unshelve setoid_rewrite terminate_ScatHUnion1; auto.
    Hint Opaque liftM_HOperator: rewrite.
    setoid_rewrite SafeCast_HReduction.
    setoid_rewrite terminate_Reduction.

    setoid_rewrite terminate_GathH1.

    Transparent SHCompose.
  Admitted.

End SigmaHCOL_rewriting.

