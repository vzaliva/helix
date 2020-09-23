Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNatSet.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.THCOL.

Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.

Require Import Helix.Tactics.HelixTactics.
Require Import Helix.HCOL.HCOLBreakdown.
Require Import Helix.SigmaHCOL.SigmaHCOLRewriting.


Require Import MathClasses.interfaces.canonical_names.

Require Import Helix.DynWin.DynWin.

Require Import Helix.Util.FinNatSet.

Require Import Helix.MSigmaHCOL.ReifySHCOL.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.MSigmaHCOL.ReifyProofs.
Require Import Helix.Util.MonoidalRestriction.

Require Import Helix.DSigmaHCOL.ReifyMSHCOL.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.
Require Import Helix.DSigmaHCOL.ReifyProofs.

Require Import Helix.FSigmaHCOL.ReifyDSHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Coq.Bool.Sumbool.
Require Import MathClasses.misc.decision.


Section HCOL_Breakdown.

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

End HCOL_Breakdown.

Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

(* This tactics solves both [SHOperator_Facts] and [MSHOperator_Facts]
   as well [SH_MSH_Operator_compat].

   Maybe it is better split into 2.
*)
Ltac solve_facts :=
  repeat match goal with
         | [ |- SHOperator_Facts _ (SumSparseEmbedding _ _ _) ] => unfold SumSparseEmbedding
         | [ |- SHOperator_Facts _ (ISumUnion _) ] => unfold ISumUnion
         | [ |- SHOperator_Facts _ (IUnion _ _) ] => apply IUnion_Facts; intros
         | [ |- SHOperator_Facts _ (SHBinOp _ _) ] => apply SHBinOp_RthetaSafe_Facts
         | [ |- @SHOperator_Facts ?m ?i ?o _ (@SHBinOp _ _ ?o _ _) ] =>
           replace (@SHOperator_Facts m i) with (@SHOperator_Facts m (o+o)) by apply eq_refl
         | [ |- SHOperator_Facts _ (SafeCast _)          ] => apply SafeCast_Facts
         | [ |- SHOperator_Facts _ (UnSafeCast _)        ] => apply UnSafeCast_Facts
         | [ |- SHOperator_Facts _ (Apply2Union _ _ _ _) ] => apply Apply2Union_Facts
         | [ |- SHOperator_Facts _ (Scatter _ _)         ] => apply Scatter_Rtheta_Facts
         | [ |- SHOperator_Facts _ (ScatH _ _)           ] => apply Scatter_Rtheta_Facts
         | [ |- SHOperator_Facts _ (ScatH _ _ _)         ] => apply Scatter_Rtheta_Facts
         | [ |- SHOperator_Facts _ (liftM_HOperator _ _) ] => apply liftM_HOperator_Facts
         | [ |- SHOperator_Facts _ (Gather _ _)          ] => apply Gather_Facts
         | [ |- SHOperator_Facts _ (GathH _ _)           ] => apply Gather_Facts
         | [ |- SHOperator_Facts _ (GathH _ _ _)         ] => apply Gather_Facts
         | [ |- SHOperator_Facts _ (SHPointwise _ _)     ] => apply SHPointwise_Facts
         | [ |- SHInductor_Facts _ (SHInductor _ _ _ _)  ] => apply SHInductor_Facts
         | [ |- SHOperator_Facts _ (IReduction _ _)      ] => apply IReduction_Facts; intros
         | [ |- SHOperator_Facts _ _                     ] => apply SHCompose_Facts
         | [ |- SH_MSH_Operator_compat (SafeCast _) _          ] => apply SafeCast_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (UnSafeCast _) _        ] => apply UnSafeCast_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (Apply2Union _ _ _ _) _ ] => apply Apply2Union_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (SHPointwise _ _) _     ] => apply SHPointwise_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (SHInductor _ _ _ _) _  ] => apply SHInductor_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (IReduction minmax.max _) _  ] =>
           apply IReduction_SH_MSH_Operator_compat with (SGP:=NN);
           [typeclasses eauto | apply CommutativeRMonoid_max_NN;typeclasses eauto | intros | | ]
         | [ |- SH_MSH_Operator_compat (IReduction plus _) _  ] =>
           apply IReduction_SH_MSH_Operator_compat with (SGP:=ATT CarrierA);
           [typeclasses eauto | apply Monoid2CommutativeRMonoid;typeclasses eauto | intros | | ]
         | [ |- SH_MSH_Operator_compat (IReduction _ _) _     ] => apply IReduction_SH_MSH_Operator_compat; intros
         | [ |- SH_MSH_Operator_compat (Embed _ _) _           ] => apply Embed_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (SHBinOp _ _) _        ] => apply SHBinOp_RthetaSafe_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat (IUnion _ _) _         ] => apply IUnion_SH_MSH_Operator_compat; intros
         | [ |- SH_MSH_Operator_compat (Pick _ _) _          ] => apply Pick_SH_MSH_Operator_compat
         | [ |- SH_MSH_Operator_compat _ _                    ] => apply SHCompose_SH_MSH_Operator_compat
         | [ |- Monoid.MonoidLaws Monoid_RthetaFlags] => apply MonoidLaws_RthetaFlags
         | [ |- Monoid.MonoidLaws Monoid_RthetaSafeFlags] => apply MonoidLaws_SafeRthetaFlags
         | [ |- MSHOperator_Facts _ ] => apply Apply2Union_MFacts
         | [ |- MSHOperator_Facts _ ] => apply Pick_MFacts
         | [ |- MSHOperator_Facts _ ] => apply SHPointwise_MFacts
         | [ |- MSHOperator_Facts _ ] => apply Embed_MFacts
         | [ |- MSHOperator_Facts _ ] => apply IUnion_MFacts; intros
         | [ |- MSHOperator_Facts _ ] => apply SHInductor_MFacts
         | [ |- MSHOperator_Facts _ ] => apply SHCompose_MFacts
         | [ |- MSHOperator_Facts _ ] => apply IReduction_MFacts; intros
         | [ |- MSHOperator_Facts _ ] => apply SHBinOp_MFacts
         | [ |- Disjoint _ (singleton _) (singleton _)] => apply Disjoined_singletons; auto
         | _ => crush
  end.

Section HCOL_to_SigmaHCOL.

  (* --- HCOL -> Sigma->HCOL --- *)

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
    rewrite expand_HTDirectSum. (* this one does not work with Diamond_arg_proper *)
    Opaque SHCompose.
    repeat rewrite LiftM_Hoperator_compose.
    repeat rewrite <- SHBinOp_equiv_lifted_HBinOp at 1.
    repeat rewrite <- SHPointwise_equiv_lifted_HPointwise at 1.
    setoid_rewrite expand_BinOp at 3.

    (* normalize associativity of composition *)
    repeat rewrite <- SHCompose_assoc.

    (* TODO: remove this once =CarrierAabs_proper= moved to =CarrierType.v= *)
    replace abstract_algebra.sm_proper with CarrierAabs_proper by apply proof_irrelevance.
    replace abstract_algebra.sg_op_proper with CarrierA_max_proper by apply proof_irrelevance.
    reflexivity.
    Transparent SHCompose.
  Qed.

  Lemma DynWinSigmaHCOL_dense_input
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
      intros _.
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

  Lemma DynWinSigmaHCOL_dense_output
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


  Instance DynWinSigmaHCOL_Facts
           (a: avector 3):
    SHOperator_Facts _ (dynwin_SHCOL a).
  Proof.
    unfold dynwin_SHCOL.

    (* First resolve all SHOperator_Facts typeclass instances *)
    solve_facts.

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

End HCOL_to_SigmaHCOL.

(* --- SigmaHCOL -> final SigmaHCOL --- *)
Section SigmaHCOL_rewriting.

  (*
           This assumptions is required for reasoning about non-negativity and [abs].
           It is specific to [abs] and this we do not make it a global assumption
           on [CarrierA] but rather assume for this particular SHCOL expression.
   *)
  Context `{CarrierASRO: @orders.SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle}.

   Instance DynWinSigmaHCOL1_Facts
           (a: avector 3):
    SHOperator_Facts _ (dynwin_SHCOL1 a).
  Proof.
    unfold dynwin_SHCOL1.
    solve_facts.
    (* Now let's take care of remaining proof obligations *)
    -
      unfold Included, In.
      intros x H.

      replace (Union (FinNat 2) (singleton 0) (Empty_set (FinNat 2))) with
          (singleton (n:=2) 0).
      {
        destruct x.
        destruct x.
        -
          apply Union_intror.
          unfold singleton, In.
          reflexivity.
        -
          destruct x.
          *
            apply Union_introl.
            unfold singleton, In.
            reflexivity.
          *
            crush.
      }
      apply Extensionality_Ensembles.
      apply Union_Empty_set_lunit.
      apply Singleton_FinNatSet_dec.
    -
      unfold Included, In.
      intros x H.

      destruct x.
      destruct x.
      apply Union_introl.
      unfold singleton, In.
      reflexivity.

      destruct x.
      apply Union_intror.
      unfold singleton, In.
      reflexivity.

      crush.
  Qed.

  Lemma op_Vforall_P_SHPointwise
        {m n: nat}
        {svalue: CarrierA}
        {fm: Monoid.Monoid RthetaFlags}
        {f: CarrierA -> CarrierA}
        `{f_mor: !Proper ((=) ==> (=)) f}
        {P: CarrierA -> Prop}
        (F: @SHOperator fm m n svalue)
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
    unfold SigmaHCOLImpl.SHPointwise_impl.
    rewrite Vbuild_nth.
    unfold liftRthetaP.
    rewrite evalWriter_Rtheta_liftM.
    unfold IgnoreIndex, const.
    apply H.
  Qed.

  (* Sigma-HCOL rewriting correctenss *)
  Lemma DynWinSigmaHCOL1_Value_Correctness
        (a: avector 3)
    : dynwin_SHCOL a = dynwin_SHCOL1 a.
  Proof.
    unfold dynwin_SHCOL.
    unfold SumSparseEmbedding.

    (* normalize to left-associativity of compose *)
    repeat rewrite <- SHCompose_assoc.
    rewrite SHCompose_mid_assoc with (g:=SHPointwise _ _).

    (* ### RULE: Reduction_ISumReduction *)
    rewrite rewrite_PointWise_ISumUnion.
    all:revgoals.
    (* solve 2 sub-dependent goals *)
    { apply SparseEmbedding_Apply_Family_Single_NonUnit_Per_Row. }
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

      apply Apply_Family_Vforall_SHOperatorFamilyCompose_move_P.
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
      remember (SparseEmbedding _ _ _ _) as fam.

      assert(Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags fam).
      {
        subst fam.
        apply SparseEmbedding_Apply_Family_Single_NonUnit_Per_Row.
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

    (* Next rule: ISumXXX_YYY *)
    repeat rewrite SHCompose_assoc.
    setoid_rewrite <- SafeCast_GathH.
    rewrite <- SafeCast_SHCompose.
    (* IReduction_absorb_operator as ISumXXX_YYY *)
    rewrite rewrite_IReduction_absorb_operator.
    repeat rewrite <- SHCompose_assoc.

    (* Next rule *)
    rewrite rewrite_PointWise_ScatHUnion by apply abs_0_s.

    (* Next rule *)
    unfold SparseEmbedding, SHOperatorFamilyCompose, UnSafeFamilyCast.
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
    | |- context [(SHFamilyOperatorCompose _ ?f _)] =>
      match f with
      | (fun jf => UnSafeCast (?torewrite ⊚ ?rest )) =>
        setoid_replace f with (fun (jf:FinNat 2) => UnSafeCast rest)
      end
    end.
    all:revgoals.
    unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
    intros [j jc].
    f_equiv.
    apply rewrite_Reduction_ScatHUnion_max_zero.
    (* --- END: hack --- *)

    Opaque SHCompose.
    (* Obligations for `rewrite_Reduction_ScatHUnion_max_zero` *)
    setoid_rewrite SHCompose_assoc.
    eapply op_Vforall_P_SHPointwise, abs_always_nonneg.

    (* Next rule *)
    unfold SHFamilyOperatorCompose.
    setoid_rewrite UnSafeCast_SHCompose.
    setoid_rewrite UnSafeCast_Gather.
    setoid_rewrite SHCompose_assoc at 5.
    setoid_rewrite GathH_fold.
    setoid_rewrite rewrite_GathH_GathH.

    (* Next rule *)
    setoid_rewrite (SafeCast_SHBinOp _ 1).
    setoid_rewrite (rewrite_PointWise_BinOp 1).

    (* Next rule *)
    setoid_rewrite (SafeCast_SHBinOp _ 3).
    setoid_rewrite (UnSafeCast_SHBinOp _ 1).
    unshelve setoid_rewrite terminate_ScatHUnion1; auto.
    Local Hint Opaque liftM_HOperator: rewrite.
    setoid_rewrite SafeCast_HReduction.

    (* Next rule *)
    unshelve rewrite terminate_Reduction by apply rings.plus_comm.
    typeclasses eauto. (* apply Zero_Plus_BFixpoint. *)

    (* Next rule *)
    setoid_rewrite terminate_GathH1.

    (* Next rule *)
    setoid_rewrite <- GathH_fold.
    setoid_rewrite <- UnSafeCast_Gather.
    setoid_rewrite GathH_fold.
    setoid_rewrite terminate_GathHN.

    (* some associativity reorganization and applying `SHBinOp_HPrepend_SHPointwise`. *)
    setoid_rewrite SHCompose_assoc at 3.
    setoid_rewrite SHBinOp_HPrepend_SHPointwise.

    (* Next rule: IReduction_SHPointwise *)
    rewrite <- SafeCast_SHPointwise.
    setoid_rewrite SHCompose_assoc at 3.
    rewrite <- SafeCast_SHCompose.
    (* IReduction_absorb_operator as IReduction_SHPointwise *)
    setoid_rewrite rewrite_IReduction_absorb_operator.

    (* Next rule: ISumXXX_YYY *)
    rewrite <- SafeCast_liftM_HOperator.
    setoid_rewrite SHCompose_assoc at 2.
    rewrite <- SafeCast_SHCompose.
    (* IReduction_absorb_operator as ISumXXX_YYY *)
    setoid_rewrite rewrite_IReduction_absorb_operator.

    (* Next rule: Pick_Pointwise *)
    unfold SHFamilyOperatorCompose.
    simpl.

    (* --- BEGIN: hack ---
    I would expect the following to work here:

    setoid_rewrite rewrite_Pick_SHPointwise
      with (g:=mult_by_1st (@le_S 2 2 (le_n 2)) a).

     But it does not (match fails), so we have to do some manual rewriting
     *)

    unfold Pickn.
    match goal with
    | [ |- context [ IReduction plus ?f ]] =>
      match f with
      | (fun (jf:FinNat 3) => SHCompose _ (SHCompose _ (Pick _ ?l) (SHPointwise _ ?c)) ?rest) =>  setoid_replace f with
            (fun (jf:FinNat 3) => SHCompose _ (SHCompose _ (SHPointwise _ (Fin1SwapIndex jf c)) (Pick _ l)) rest)
      end
    end.

    all:revgoals.
    unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
    intros [j jc].
    f_equiv.
    simpl.
    apply rewrite_Pick_SHPointwise.
    (* --- END: hack --- *)

    (* now solve some obligations *)
    {
      intros x z.
      unfold Fin1SwapIndex, const.
      reflexivity.
    }

    (* Next rule: Pick_Induction *)
    setoid_rewrite SHCompose_assoc at 2.

    setoid_rewrite rewrite_Pick_Induction.

    (* Bring `Pick` into `IReduction` *)
    setoid_rewrite SHCompose_assoc at 1.
    rewrite <- SafeCast_SHCompose.
    setoid_rewrite rewrite_IReduction_absorb_operator.

    (* Fix SHBinOp type *)
    rewrite <- SafeCast_SHBinOp.

    setoid_rewrite <- SHInductor_equiv_lifted_HInductor.

    unfold dynwin_SHCOL1.
    unfold NatAsNT.MNatAsNT.NTypeSetoid, NatAsNT.MNatAsNT.NTypeEquiv.
    unfold join_is_sg_op, meet_is_sg_op, le.
    simpl.


    (* we ended up here with two instances of [reflexive_proper_proxy].
       this is a small hack to unify them. Could be done more generaly
       by automation to unify up to proof irrelevance
     *)
    repeat match goal with
           | [|- context [(reflexive_proper_proxy ?a )] ] =>
             generalize (reflexive_proper_proxy a) ; intros
           end.
    replace p with p1 by apply proof_irrelevance.
    reflexivity.
  Qed.


  (* Couple additional structual properties: input and output of the
  dynwin_SHCOL1 is dense *)
  Lemma DynWinSigmaHCOL1_dense_input
        (a: avector 3)
    : Same_set _ (in_index_set _ (dynwin_SHCOL1 a)) (Full_set (FinNat _)).
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
      intros _.
      unfold In in *.
      Transparent  SHCompose.
      simpl.

      destruct x as [x xc].
      simpl in xc.

      (* The following could be automated with nifty tactics but for
      now we will do it manually. *)

      destruct x.
      (* 0 *)
      repeat apply Union_introl.
      compute; tauto.

      (* 1 *)
      compute in xc.
      destruct x.
      apply Union_intror.
      apply Union_intror.
      apply Union_introl.
      apply Union_intror.
      apply Union_introl.
      compute; tauto.

      (* 2 *)
      compute in xc.
      destruct x.
      apply Union_intror.
      apply Union_introl.
      apply Union_intror.
      apply Union_introl.
      compute; tauto.

      (* 3 *)
      compute in xc.
      destruct x.
      apply Union_intror.
      apply Union_intror.
      apply Union_introl.
      apply Union_introl.
      compute; tauto.

      (* 4 *)
      compute in xc.
      destruct x.
      apply Union_intror.
      apply Union_introl.
      apply Union_introl.
      compute; tauto.

      (* 5 *)
      compute in xc.
      exfalso.
      lia.
  Qed.

  Lemma DynWinSigmaHCOL1_dense_output
        (a: avector 3)
    : Same_set _ (out_index_set _ (dynwin_SHCOL1 a)) (Full_set (FinNat _)).
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
      intros _.
      unfold In in *.
      simpl.
      apply Full_intro.
  Qed.

  (* Putting it all together: Final proof of SigmaHCOL rewriting which
   includes both value and structual correctenss *)
  Theorem SHCOL_to_SHCOL1_Rewriting
          (a: avector 3)
    : @SHOperator_subtyping
        _ _ _ _
        (dynwin_SHCOL1 a)
        (dynwin_SHCOL a)
        (DynWinSigmaHCOL1_Facts _)
        (DynWinSigmaHCOL_Facts _).
  Proof.
    split.
    -
      symmetry.
      apply DynWinSigmaHCOL1_Value_Correctness.
    -
      split.
      +
        pose proof (DynWinSigmaHCOL_dense_input a) as E.
        pose proof (DynWinSigmaHCOL1_dense_input a) as E1.
        apply Extensionality_Ensembles in E.
        apply Extensionality_Ensembles in E1.
        unfold dynwin_i, dynwin_o in *.
        rewrite E, E1.
        unfold Included.
        intros x H.
        auto.
      +
        pose proof (DynWinSigmaHCOL_dense_output a) as E.
        pose proof (DynWinSigmaHCOL1_dense_output a) as E1.
        apply Extensionality_Ensembles in E.
        apply Extensionality_Ensembles in E1.
        unfold dynwin_i, dynwin_o in *.
        rewrite E, E1.
        unfold Same_set.
        split; unfold Included; auto.
  Qed.

End SigmaHCOL_rewriting.

Section SHCOL_to_MSHCOL.

  (*
           This assumptions is required for reasoning about non-negativity and [abs].
           It is specific to [abs] and this we do not make it a global assumption
           on [CarrierA] but rather assume for this particular SHCOL expression.
   *)
  Context `{CarrierASRO: @orders.SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle}.

  MetaCoq Run (reifySHCOL dynwin_SHCOL1 100 [(BasicAst.MPfile ["DynWin"; "DynWin"; "Helix"], "dynwin_SHCOL1")] "dynwin_MSHCOL1").

  Fact Set_Obligation_1:
    Included (FinNat 2) (Full_set (FinNat 2))
             (Union (FinNat 2) (singleton 1)
                    (Union (FinNat 2) (singleton 0) (Empty_set (FinNat 2)))).
  Proof.

    unfold Included, In.
    intros [x xc] _.

    destruct x.
    +
      apply Union_intror.
      apply Union_introl.
      reflexivity.
    +
      apply Union_introl.
      destruct x.
      *
        reflexivity.
      *
        crush.
  Qed.

  Fact Apply_Family_Vforall_ATT
        {fm}
        {i o n}
        {svalue: CarrierA}
        (op_family: @SHOperatorFamily fm i o n svalue):
    Apply_Family_Vforall_P fm (liftRthetaP (ATT CarrierA)) op_family.
  Proof.
    intros x j jc.
    apply Vforall_intro.
    intros y H.
    unfold liftRthetaP.
    cbv;tauto.
  Qed.


  Theorem dynwin_SHCOL_MSHCOL_compat {a}:
    SH_MSH_Operator_compat (dynwin_SHCOL1 a) (dynwin_MSHCOL1 a).
  Proof.
    unfold dynwin_SHCOL1, dynwin_MSHCOL1.
    unfold ISumUnion.

    solve_facts.
    -
      unfold Included, In.
      intros [x xc] H.

      destruct x.
      apply Union_introl.
      reflexivity.

      apply Union_intror.
      unfold singleton.
      destruct x; crush.
    -
      apply Apply_Family_Vforall_ATT.
    -
      apply Set_Obligation_1.
    -
      (* TODO: refactor to lemma
         [Apply_Family_Vforall_SHCompose_move_P].
       *)
      unfold Apply_Family_Vforall_P.
      intros x j jc.
      apply Vforall_nth_intro.
      intros t tc.
      unfold get_family_op.
      simpl.
      unfold compose.
      match goal with
      | [|- context[SigmaHCOLImpl.SHBinOp_impl ?ff ?g]] => generalize g
      end.
      clear x; intros x.
      unshelve erewrite SHBinOp_impl_nth.
      lia.
      lia.
      unfold NN, liftRthetaP.
      rewrite evalWriter_Rtheta_liftM2.
      unfold IgnoreIndex, const.
      apply abs_always_nonneg.
    -
      apply Set_Obligation_1.
    -
      apply Set_Obligation_1.
    -
      apply Set_Obligation_1.
    -
      apply Set_Obligation_1.
  Qed.

End SHCOL_to_MSHCOL.

Section MSHCOL_to_DSHCOL.

  Import MDSHCOLOnCarrierA.

  MetaCoq Run (reifyMSHCOL dynwin_MSHCOL1 [(BasicAst.MPfile ["DynWinProofs"; "DynWin"; "Helix"], "dynwin_MSHCOL1")] "dynwin_DSHCOL1" "dynwin_DSHCOL1_globals").

  (* Import DSHNotation. *)

  Definition nglobals := List.length (dynwin_DSHCOL1_globals). (* 1 *)
  Definition DSH_x_p := PVar (nglobals+1). (* PVar 2 *)
  Definition DSH_y_p := PVar (nglobals+0). (* PVar 1 *)


  (* This tactics solves both [MSH_DSH_compat] and [DSH_pure] goals along with typical
     obligations *)
  Ltac solve_MSH_DSH_compat :=
    repeat match goal with
      [ |-  @MSH_DSH_compat ?i ?o (@MSHBinOp ?p01 ?p02 ?p03) ?p1 ?p2 ?p3 ?p4 ?p5 ?p6] =>
      replace
        (@MSH_DSH_compat i o (@MSHBinOp p01 p02 p03) p1 p2 p3 p4 p5 p6) with
      (@MSH_DSH_compat (o+o) o (@MSHBinOp p01 p02 p03) p1 p2 p3 p4 p5 p6)
        by apply eq_refl ; eapply BinOp_MSH_DSH_compat; intros
    | |- MSH_DSH_compat (MSHCompose _ _) _ _ _ _ _ => unshelve eapply Compose_MSH_DSH_compat; intros
    | |- MSH_DSH_compat (MApply2Union _ _ _) _ _ _ _ _ => unshelve eapply Apply2Union_MSH_DSH_compat; intros
    | |- MSH_DSH_compat (@MSHIReduction _ _ (S _) _ _ _ _) _ _ _ _ _ => unshelve eapply IReduction_MSH_DSH_compat_S; intros
    | |- MSH_DSH_compat (MSHPick  _) _ _ _ _ _ => apply Pick_MSH_DSH_compat
    | |- MSH_DSH_compat (MSHInductor _ _ _) _ _ _ _ _ => unshelve eapply Inductor_MSH_DSH_compat; intros
    | |- MSH_DSH_compat (MSHPointwise _) _ _ _ _ _ => apply Pointwise_MSH_DSH_compat; intros
    | |- MSH_DSH_compat (MSHEmbed _) _ _ _ _ _ => apply Embed_MSH_DSH_compat; intros
    | |- MSH_DSH_compat (MSHIUnion _) _ _ _ _ _ => unshelve eapply IUnion_MSH_DSH_compat; intros

    (* DSH_Pure *)
    |  [ |-
        DSH_pure
          (DSHSeq
             (DSHMemInit _ _)
             (DSHAlloc ?o
                       (DSHLoop _
                                (DSHSeq
                                   _
                                   (DSHMemMap2 _ _ _ _ _)))))
          _] => apply IReduction_DSH_pure
    | [ |- DSH_pure (DSHSeq _ _) _] => apply Seq_DSH_pure
    | [ |- DSH_pure (DSHAssign _ _) _ ] => apply Assign_DSH_pure
    | [ |- DSH_pure (DSHPower _ _ _ _ _) _] => apply Power_DSH_pure
    | [ |- DSH_pure (DSHIMap _ _ _ _) _] => apply IMap_DSH_pure
    | [ |- DSH_pure (DSHLoop _ _) _] => apply Loop_DSH_pure
    | [ |- DSH_pure (DSHBinOp _ _ _ _) _] => apply BinOp_DSH_pure
    | [ |- DSH_pure (DSHAlloc _ (DSHSeq _ _)) _] => apply Compose_DSH_pure
    | [ |- PVar _ ≡ incrPVar 0 _] => auto

    (* Compat Obligations *)
    | [ |- MSH_DSH_IBinCarrierA_compat _ _ _ _] => constructor ; intros
    | [ |- MSH_DSH_BinCarrierA_compat _ _ _ _] => constructor
    | [ |- ErrorSetoid.herr_f _ _ _ _ _] =>
      let H := fresh "H" in
      constructor;
      cbv;
      intros H;
      inversion H
    | _ => try reflexivity
    end.

  (* TODO: This is a manual proof. To be automated in future. See [[../../doc/TODO.org]] for details *)
  Instance DynWin_pure
    :
      DSH_pure (dynwin_DSHCOL1) DSH_y_p.
  Proof.
    unfold dynwin_DSHCOL1, DSH_y_p, DSH_x_p.
    solve_MSH_DSH_compat.
  Qed.

  Section DummyEnv.

    Local Open Scope list_scope. (* for ++ *)

    (* Could be automatically universally quantified on these *)
    Parameter a:vector CarrierA 3.
    Parameter x:mem_block.

    Definition dynwin_a_addr:nat := 0.
    Definition dynwin_y_addr:nat := (nglobals+0).
    Definition dynwin_x_addr:nat := (nglobals+1).

    Definition dynwin_globals_mem :=
      (memory_set memory_empty dynwin_a_addr (avector_to_mem_block a)).

    (* Initialize memory with X and placeholder for Y. *)
    Definition dynwin_memory :=
      memory_set
        (memory_set dynwin_globals_mem dynwin_x_addr x)
        dynwin_y_addr mem_empty.

    Definition dynwin_σ_globals:evalContext :=
      [
        DSHPtrVal dynwin_a_addr 3
      ].

    Definition dynwin_σ:evalContext :=
      dynwin_σ_globals ++
      [
        DSHPtrVal dynwin_y_addr dynwin_o
        ; DSHPtrVal dynwin_x_addr dynwin_i
      ].

    (* TODO: move, but not sure where. We do not have MemorySetoid.v *)
    Lemma memory_lookup_not_next_equiv {m k v}:
      memory_lookup m k = Some v ->
      k ≢ memory_next_key m.
    Proof.
      intros H.
      destruct (eq_nat_dec k (memory_next_key m)) as [E|NE]; [exfalso|auto].
      rewrite E in H. clear E.
      pose proof (memory_lookup_memory_next_key_is_None m) as N.
      unfold util.is_None in N.
      break_match_hyp; [trivial|some_none].
    Qed.

    (* This lemma could be auto-generated from TemplateCoq *)
    Theorem DynWin_MSH_DSH_compat
      :
        @MSH_DSH_compat dynwin_i dynwin_o (dynwin_MSHCOL1 a) (dynwin_DSHCOL1)
                        dynwin_σ
                        dynwin_memory
                        DSH_x_p DSH_y_p
                        DynWin_pure.
    Proof.
      unfold dynwin_DSHCOL1, DSH_y_p, DSH_x_p.
      unfold dynwin_x_addr, dynwin_y_addr, dynwin_a_addr, nglobals in *.
      unfold dynwin_MSHCOL1.
      cbn in *.

      solve_MSH_DSH_compat.

      {
        cbn in *.
        do 2 inl_inr_inv.
        cbv in H, H0.
        lia.
      }

      (* This remailing obligation proof is not yet automated *)
      2: {
        (* [a] is defined in section *)
        constructor; intros.
        unfold evalIUnCType, Fin1SwapIndex.
        cbn.

        unfold mult_by_nth, const.
        subst tmpk.

        repeat match goal with
               | [H: memory_equiv_except ?m m'' _ |- _] => remember m as m0
               | [H: memory_subset_except _ ?m m' |- _] => remember m as m1
               end.
        cbn in *.

        inversion H. subst y_id; clear H.

        remember (avector_to_mem_block a) as v.
        assert(LM: memory_lookup m1 dynwin_a_addr = Some v).
        {
          subst m1.
          unfold dynwin_memory, dynwin_globals_mem.

          do 4 (rewrite memory_lookup_memory_set_neq
                 by (cbn;unfold dynwin_a_addr,dynwin_y_addr,dynwin_x_addr, nglobals; auto)).
          rewrite memory_lookup_memory_set_eq by reflexivity.
          subst v.
          reflexivity.
        }

        assert(LM': memory_lookup m' dynwin_a_addr = Some v).
        {
          clear - LM H0 Heqv.
          specialize (H0 dynwin_a_addr v LM).
          destruct H0 as [v' [L E]].
          autospecialize E ; [cbv;lia|].
          rewrite E.
          apply L.
        }

        assert(LM0: memory_lookup m0 dynwin_a_addr = Some v).
        {
          subst m0.
          rewrite memory_lookup_memory_set_neq.
          auto.
          apply memory_lookup_not_next_equiv in LM.
          auto.
        }

        assert(LM'': memory_lookup m'' dynwin_a_addr = Some v).
        {
          clear -LM0 H2 Heqv.
          specialize (H2 dynwin_a_addr).
          full_autospecialize H2.
          -
            apply memory_lookup_not_next_equiv in LM0.
            auto.
          -
            rewrite <- H2.
            apply LM0.
        }

        assert(LM''0: memory_lookup m''0 dynwin_a_addr = Some v).
        {
          clear - LM'' H3 Heqv.
          specialize (H3 dynwin_a_addr).
          full_autospecialize H3.
          -
            apply memory_lookup_not_next_equiv in LM''.
            auto.
          -
            rewrite <- H3.
            apply LM''.
        }

        repeat break_match; try inl_inr; try some_none.
        -
          exfalso.
          memory_lookup_err_to_option.
          eq_to_equiv_hyp.
          some_none.
        -
          inversion Heqs0; subst.
          exfalso; clear - Heqs1.
          unfold assert_NT_lt, NatAsNT.MNatAsNT.to_nat in Heqs1.
          destruct t.
          cbn in Heqs1.
          enough (E : x0 <=? 2 ≡ true) by (rewrite E in Heqs1; inversion Heqs1).
          clear - l.
          apply Nat.leb_le.
          lia.
        -
          memory_lookup_err_to_option.
          destruct t as [t tc].
          cbn in *.
          assert(m = avector_to_mem_block a) as C.
          {
            eq_to_equiv_hyp.
            rewrite LM''0 in Heqs2.
            some_inv.
            inversion Heqs0; subst m2 n.
            rewrite <- Heqs2.
            rewrite Heqv.
            reflexivity.
          }
          err_eq_to_equiv_hyp.
          rewrite C in Heqs.
          unfold mem_lookup_err in Heqs.
          rewrite mem_lookup_avector_to_mem_block_equiv with (kc:=tc) in Heqs.
          inversion Heqs.
        -
          memory_lookup_err_to_option.
          inl_inr_inv.
          subst.
          destruct t as [t tc].
          cbn in *.
          assert(m = avector_to_mem_block a) as C.
          {
            eq_to_equiv_hyp.
            rewrite LM''0 in Heqs2.
            some_inv.
            rewrite <- Heqs2.
            reflexivity.
          }
          err_eq_to_equiv_hyp.
          rewrite C in Heqs.
          unfold mem_lookup_err in Heqs.
          rewrite mem_lookup_avector_to_mem_block_equiv with (kc:=tc) in Heqs.
          inversion Heqs; subst.
          rewrite H4.
          reflexivity.
      }

      {
        cbn.
        discriminate.
      }

      {
        apply IReduction_MFacts.
        -
          intros.
          apply SHCompose_MFacts.
          constructor.
          apply SHCompose_MFacts.
          constructor.
          apply SHPointwise_MFacts.
          apply SHInductor_MFacts.
          apply Pick_MFacts.
        -
          intros.
          cbn.
          constructor.
          constructor.
          constructor.
      }

      {
        apply SHCompose_MFacts.
        constructor.
        apply SHCompose_MFacts.
        constructor.
        apply SHPointwise_MFacts.
        apply SHInductor_MFacts.
        apply Pick_MFacts.
      }

      {
        cbn in *.
        symmetry in H.
        memory_lookup_err_to_option.
        apply memory_lookup_not_next_equiv in H.
        congruence.
      }

      {

        cbn in *.
        unfold dynwin_x_addr in *.
        intros C.
        inl_inr_inv.
        subst.

        symmetry in H.
        memory_lookup_err_to_option.
        apply equiv_Some_is_Some in H.
        apply memory_is_set_is_Some in H.

        rename H into M0.
        rename m' into m0.
        remember (memory_set m0 (memory_next_key m0) mem_empty) as m1 eqn:M1.
        remember (memory_set m1 (memory_next_key m1) mb) as m2 eqn:M2.
        rename m'0 into m1_plus.
        inl_inr_inv.

        assert(memory_next_key m0 > 2) as LM0.
        {
          apply mem_block_exists_next_key_gt in M0.
          apply M0.
        }

        assert(memory_next_key m1 > 3) as LM1.
        {
          apply memory_set_memory_next_key_gt in M1.
          lia.
        }

        remember (memory_set m1_plus (memory_next_key m1_plus) mb) as
            m1_plus'.

        apply memory_set_memory_next_key_gt in Heqm1_plus'.
        apply memory_subset_except_next_keys in H1.
        subst_max.

        remember (memory_next_key (memory_set m0 (memory_next_key m0) mem_empty)) as x.
        clear Heqx.
        pose proof memory_set_memory_next_key_gt m1_plus (memory_set m1_plus x mb) mb x.
        autospecialize H; [reflexivity |].
        rewrite <-H4 in H.
        lia.
      }

      {
        apply IReduction_MFacts.
        -
          intros.
          apply SHCompose_MFacts.
          +
            cbn in *.
            clear H j jc.
            intros x IN.
            destruct x as [x X2].
            cbn in *.
            destruct x as [| x].
            *
              right.
              left.
              reflexivity.
            *
              inversion X2; [| lia].
              subst.
              left.
              reflexivity.
          +
            apply SHBinOp_MFacts
              with (f:= (λ (i : FinNat 1) (a0 b : CarrierA),
                         IgnoreIndex abs i (Fin1SwapIndex2
                                              (mkFinNat jc) (IgnoreIndex2 sub) i a0 b))).
          +
            apply IUnion_MFacts.
            intros.
            apply SHCompose_MFacts.
            constructor.
            apply Embed_MFacts.
            apply Pick_MFacts.
            intros.
            cbn.
            constructor.
            intros x C.
            inversion C; subst.
            inversion H1; subst.
            inversion H2; subst.
            contradict H0.
            reflexivity.
        -
          intros.
          cbn.
          constructor.
          constructor.
          constructor.
      }

      {
        apply SHCompose_MFacts.
        -
          cbn.
          intros x IN.
          destruct x as [x X2].
          cbn in *.
          destruct x as [| x].
          *
            right.
            left.
            reflexivity.
          *
            inversion X2; [| lia].
            subst.
            left.
            reflexivity.
        -
          clear.
          apply SHBinOp_MFacts with (f := λ (i : FinNat 1) (a0 b : CarrierA),
                                          IgnoreIndex abs i
                                                      (Fin1SwapIndex2 (mkFinNat jc)
                                                                      (IgnoreIndex2 sub)
                                                                      i a0 b)).
        -
          solve_facts.
      }

    Qed.

  End DummyEnv.

End MSHCOL_to_DSHCOL.

Section DHCOL_to_FHCOL.
  Definition dynwin_FSHCOL := DSCHOLtoFHCOL dynwin_DSHCOL1.

  Lemma simplCarrierARefl:
    forall a,
      (CarrierAequivdec a a) ≡ left
                             (@reflexivity
                                (Zero CarrierA)
                                (@equiv (Zero CarrierA) CarrierAe)
                                (@Equivalence_Reflexive (Zero CarrierA)
                                                        (@equiv (Zero CarrierA) CarrierAe)
                                                        (@abstract_algebra.setoid_eq (Zero CarrierA) CarrierAe CarrierAsetoid))
                                a
                              : @equiv (Zero CarrierA) CarrierAe a a).
  Proof.
    intros a.
    destruct (CarrierAequivdec a a) as [H|NH].
    -
      f_equiv.
      apply proof_irrelevance.
    -
      contradict NH.
      reflexivity.
  Qed.

  Lemma CarrierA_One_neq_Z: CarrierA1 ≠ CarrierAz.
  Proof.
    destruct (CarrierAequivdec CarrierA1 CarrierAz) as [H|NH].
    -
      symmetry in H.
      contradict H.
      apply CarrierA_Z_neq_One.
    -
      assumption.
  Qed.

  Lemma simplCarrierA_Z_neq_One:
    CarrierAequivdec CarrierAz CarrierA1 ≡ right CarrierA_Z_neq_One.
  Proof.
    destruct (CarrierAequivdec CarrierAz CarrierA1) as [H|NH].
    -
      contradict H.
      apply CarrierA_Z_neq_One.
    -
      f_equiv.
      apply proof_irrelevance.
  Qed.

  Lemma simplCarrierA_One_neq_Z:
    CarrierAequivdec CarrierA1 CarrierAz ≡ right CarrierA_One_neq_Z.
  Proof.
    destruct (CarrierAequivdec CarrierA1 CarrierAz) as [H|NH].
    -
      contradict H.
      apply CarrierA_One_neq_Z.
    -
      f_equiv.
      apply proof_irrelevance.
  Qed.

  Lemma simplCarrierA_One_eq_Z:
    CarrierAequivdec CarrierA1 CarrierAz ≡ right CarrierA_One_neq_Z.
  Proof.
    destruct (CarrierAequivdec CarrierA1 CarrierAz) as [H|NH].
    -
      contradict H.
      apply CarrierA_One_neq_Z.
    -
      f_equiv.
      apply proof_irrelevance.
  Qed.

  Hint Rewrite
       simplCarrierA_Z_neq_One
       simplCarrierA_Z_neq_One
       simplCarrierA_One_eq_Z
       simplCarrierARefl:
    CarrierAZ1equalities.

  Import FSigmaHCOL.MDSHCOLOnFloat64.
  Require Import AltBinNotations.

  (* Import DSHNotation. *)
  (* Notation for shorter printing of `int64` constants *)
  Local Declare Scope int64.
  Local Notation "v" := (Int64.mkint v _) (at level 10, only printing) : int64.
  Local Delimit Scope int64 with int64.

  Definition dynwin_FSHCOL1 : FSigmaHCOL.MDSHCOLOnFloat64.DSHOperator.
  Proof.
    remember dynwin_FSHCOL as a eqn:H.
    Opaque Float64asCT.Float64Zero.
    Opaque Float64asCT.Float64One.
    cbv in H.
    autorewrite with CarrierAZ1equalities in H.
    cbv in H.
    destruct a.
    -
      inv H.
    -
      inl_inr_inv.
      (* Set Printing All. *)
      (* Redirect "dynwin_FSHCOL" Show 1. *)
      exact d.
  Defined.

End DHCOL_to_FHCOL.
