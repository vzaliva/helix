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
Require Import Helix.MSigmaHCOL.RasCarrierA.
Require Import Helix.MSigmaHCOL.RasCT.
Require Import Helix.Util.MonoidalRestriction.

Require Import Helix.RSigmaHCOL.ReifyMSHCOL.
Require Import Helix.RSigmaHCOL.ReifyProofs.

Require Import Helix.RSigmaHCOL.RSigmaHCOL.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.ReifyRHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Coq.Bool.Sumbool.
Require Import MathClasses.misc.decision.

Require Import ExtLib.Structures.Monad.
Import MonadNotation.

Import HCOL_on_RasCT.

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

Local Notation "g ⊚ f" := (@SHCompose _ _ Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

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
         | [ |- SH_MSH_Operator_compat (IUnion _ _) _         ] => apply (@IUnion_SH_MSH_Operator_compat _ _); intros
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

  Remove Hints CarrierDefs_R CarrierProperties_R : typeclass_instances.
  Context `{CAPROPS: @CarrierProperties CADEFS}.
  
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

  Remove Hints CarrierDefs_R CarrierProperties_R : typeclass_instances.
  Context `{CAPROPS: @CarrierProperties CADEFS}.

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
        (F: @SHOperator _ fm m n svalue)
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
    | |- context [(SHFamilyOperatorCompose _ ?f)] =>
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
        _ _ _ _ _
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

Require Import Coq.Lists.List.
Import ListNotations.

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
        (op_family: @SHOperatorFamily _ fm i o n svalue):
    Apply_Family_Vforall_P fm (liftRthetaP (ATT CarrierA)) op_family.
  Proof.
    intros x j jc.
    apply Vforall_intro.
    intros y H.
    unfold liftRthetaP.
    cbv;tauto.
  Qed.


  Theorem dynwin_SHCOL_MSHCOL_compat (a: avector 3):
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
      Opaque SigmaHCOLImpl.SHBinOp_impl.
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
      epose proof abs_always_nonneg as abs_always_nonneg'.
      apply abs_always_nonneg'.
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

Section MSHCOL_to_RHCOL.

  Import RHCOLEval.

  Opaque CarrierAz zero CarrierA1 one.

  MetaCoq Run (reifyMSHCOL dynwin_MSHCOL1 [(BasicAst.MPfile ["DynWinProofs"; "DynWin"; "Helix"], "dynwin_MSHCOL1")] "dynwin_RHCOL" "dynwin_RHCOL_globals").
  Transparent CarrierAz zero CarrierA1 one.

  (* A sanity check as a side effect of [DynWin_RHCOL_hard] being hardcoded in
     [DynWin.v]. See also [DynWin_FHCOL_hard_check] *)
  Fact dynwin_RHCOL_hard_check :
    dynwin_RHCOL ≡ DynWin_RHCOL_hard.
  Proof.
    reflexivity.
  Qed.

  (* Import DSHNotation. *)

  Definition nglobals := List.length (dynwin_RHCOL_globals). (* 1 *)
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
      DSH_pure (dynwin_RHCOL) DSH_y_p.
  Proof.
    unfold dynwin_RHCOL, DSH_y_p, DSH_x_p.
    solve_MSH_DSH_compat.
  Qed.

  Section DummyEnv.

    Local Open Scope list_scope. (* for ++ *)

    (* Could be automatically universally quantified on these *)
    Variable a:vector CarrierA 3.
    Variable x:mem_block.

    Definition dynwin_a_addr:nat := 0.
    Definition dynwin_y_addr:nat := (nglobals+0).
    Definition dynwin_x_addr:nat := (nglobals+1).

    Definition dynwin_globals_mem :=
      (memory_set memory_empty dynwin_a_addr (ctvector_to_mem_block a)).

    (* Initialize memory with X and placeholder for Y. *)
    Definition dynwin_memory :=
      memory_set
        (memory_set dynwin_globals_mem dynwin_x_addr x)
        dynwin_y_addr mem_empty.
    
    (* TODO: this clashes with [dynwin_R_σ], which is more common, but less clean *)
    (*
    Definition dynwin_σ_globals:evalContext :=
      [
        (DSHPtrVal dynwin_a_addr 3,false)
      ].
    
    Definition dynwin_σ:evalContext :=
      dynwin_σ_globals ++
                       [
                         (DSHPtrVal dynwin_y_addr dynwin_o,false)
                         ; (DSHPtrVal dynwin_x_addr dynwin_i,false)
                       ].
     *)
    
    (* Initialize memory with X and placeholder for Y. *)
    Definition dynwin_R_memory (a:ctvector 3) (x:ctvector dynwin_i) :=
      RHCOLEval.memory_set
        (RHCOLEval.memory_set (RHCOLEval.memory_set
                                 RHCOLEval.memory_empty
                                 dynwin_a_addr
                                 (ctvector_to_mem_block a))
                              dynwin_x_addr
                              (ctvector_to_mem_block x))
        dynwin_y_addr
        RHCOLEval.mem_empty.
    
    Definition dynwin_R_σ := [
        (RHCOLEval.DSHPtrVal dynwin_a_addr 3,false)
        ; (RHCOLEval.DSHPtrVal dynwin_y_addr dynwin_o,false)
        ; (RHCOLEval.DSHPtrVal dynwin_x_addr dynwin_i,false)
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
        @MSH_DSH_compat dynwin_i dynwin_o (dynwin_MSHCOL1 a) (dynwin_RHCOL)
                        dynwin_R_σ
                        dynwin_memory
                        DSH_x_p DSH_y_p
                        DynWin_pure.
    Proof.
      unfold dynwin_RHCOL, DSH_y_p, DSH_x_p.
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

      repeat match goal with
      | [|- evalPExpr_id _ _ ≢ evalPExpr_id _ _] => cbn; apply inr_neq; auto
      end.

      1:{
        cbn in *; apply inr_neq.
        subst.
        invc H; clear H0.
        generalize dependent (memory_set m' 5 mb).
        clear.
        rename m'' into m'; intros m M'.
        intros C.
        rewrite C in M'; clear C.
        assert (memory_lookup m' (memory_next_key m') = Some mbt)
          by (remember (memory_next_key m') as k;
              now rewrite M', memory_lookup_memory_set_eq by reflexivity).
        now apply memory_lookup_not_next_equiv in H.
      }

      2:{
        cbn in *; apply inr_neq.
        inl_inr_inv.
        subst.

        rename m' into m, m'' into m', m''0 into m'', H2 into H1, H3 into H2.
        clear H2.

        remember (memory_next_key (memory_set m 5 mb)) as k.
        assert(kc: k>5).
        {
          subst k.
          eapply memory_set_memory_next_key_gt; eauto.
        }
        clear Heqk.
        specialize (H1 5).
        unfold memory_set in *.
        rewrite Memory.NP.F.add_neq_o in H1 by lia.
        rewrite Memory.NP.F.add_eq_o in H1 by reflexivity.
        apply memory_lookup_not_next_equiv in H1.
        congruence.
      }

      4:{
        cbn in *.
        symmetry in H.
        memory_lookup_err_to_option.
        apply memory_lookup_not_next_equiv in H.
        congruence.
      }

      4:{
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

        remember (memory_next_key (memory_set m0 (memory_next_key m0) mem_empty)) as xx.
        clear Heqxx.
        pose proof memory_set_memory_next_key_gt m1_plus (memory_set m1_plus xx mb) mb xx.
        autospecialize H; [reflexivity |].
        rewrite <-H4 in H.
        lia.
      }

      4:{
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

        remember (memory_next_key (memory_set m0 (memory_next_key m0) mem_empty)) as xx.
        clear Heqxx.
        pose proof memory_set_memory_next_key_gt m1_plus (memory_set m1_plus xx mb) mb xx.
        autospecialize H; [reflexivity |].
        rewrite H5 in H.
        lia.
      }

      6:{
        cbn; apply inr_neq.
        auto.
      }

      (* This remailing obligation proof is not yet automated *)
      1: {
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

        remember (ctvector_to_mem_block a) as v.
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

        (*
        assert(LM0: memory_lookup m0 dynwin_a_addr = Some v).
        {
          rewrite H2.
          rewrite memory_lookup_memory_set_neq.
          auto.
          apply memory_lookup_not_next_equiv in LM.
          auto.
        }
         *)

        assert(LM'': memory_lookup m'' dynwin_a_addr = Some v).
        {
          rewrite H2.
          rewrite memory_lookup_memory_set_neq.
          rewrite memory_lookup_memory_set_neq.
          assumption.
          apply memory_lookup_not_next_equiv in LM.
          congruence.
          assert (memory_next_key m1 > dynwin_a_addr)
            by (apply mem_block_exists_next_key_gt,
                  mem_block_exists_exists_equiv; eauto).
          remember(memory_set m' (memory_next_key m1) mb) as tm.
          apply memory_set_memory_next_key_gt in Heqtm.
          lia.
        }

        assert(LM''0: memory_lookup m''0 dynwin_a_addr = Some v).
        {
          rewrite H3.
          rewrite memory_lookup_memory_set_neq.
          assumption.
          apply memory_lookup_not_next_equiv in LM''.
          congruence.
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
          enough (E : x <=? 2 ≡ true) by (rewrite E in Heqs1; inversion Heqs1).
          clear - l.
          apply Nat.leb_le.
          lia.
        -
          memory_lookup_err_to_option.
          destruct t as [t tc].
          cbn in *.
          assert(m = ctvector_to_mem_block a) as C.
          {
            eq_to_equiv_hyp.
            rewrite LM''0 in Heqs2.
            some_inv.
            inversion Heqs0; subst m0 n.
            rewrite <- Heqs2.
            rewrite Heqv.
            reflexivity.
          }
          err_eq_to_equiv_hyp.
          rewrite C in Heqs.
          unfold mem_lookup_err in Heqs.
          rewrite mem_lookup_ctvector_to_mem_block_equiv with (kc:=tc) in Heqs.
          inversion Heqs.
        -
          memory_lookup_err_to_option.
          inl_inr_inv.
          subst.
          destruct t as [t tc].
          cbn in *.
          assert(m = ctvector_to_mem_block a) as C.
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
          rewrite mem_lookup_ctvector_to_mem_block_equiv with (kc:=tc) in Heqs.
          inversion Heqs; subst.
          rewrite H4.
          reflexivity.
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
        apply IReduction_MFacts.
        -
          intros.
          apply SHCompose_MFacts.
          +
            cbn in *.
            clear H j jc.
            intros xx IN.
            destruct xx as [xx X2].
            cbn in *.
            destruct xx as [| xx].
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
              with (f:= (λ (_ : FinNat 1) (a0 b : Rdefinitions.RbaseSymbolsImpl.R),
                          Rbasic_fun.Rabs
                            (Rdefinitions.RbaseSymbolsImpl.Rplus
                               (Rdefinitions.RbaseSymbolsImpl.Ropp a0) b))).
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
            intros xx C.
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
          intros xx IN.
          destruct xx as [xx X2].
          cbn in *.
          destruct xx as [| xx].
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
          apply SHBinOp_MFacts
            with (f := (λ (_ : FinNat 1) (a b : Rdefinitions.RbaseSymbolsImpl.R),
                         Rbasic_fun.Rabs
                           (Rdefinitions.RbaseSymbolsImpl.Rplus
                              (Rdefinitions.RbaseSymbolsImpl.Ropp a) b))).
        -
          solve_facts.
      }
    Qed.

    

  End DummyEnv.

End MSHCOL_to_RHCOL.

(* TODO: move *)
Require Import ZArith.

Section RCHOL_to_FHCOL.

  (* A sanity check as a side effect of [DynWin_RHCOL_hard] being hardcoded in
     [DynWin.v]. See also [DynWin_FHCOL_hard_check] *)
  Fact DynWin_FHCOL_hard_check :
    RHCOLtoFHCOL.translate dynwin_RHCOL ≡ inr DynWin_FHCOL_hard.
  Proof.
    cbn.

    assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
                  ≡ @inr string _ Float64asCT.Float64Zero).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      all: clear - n; contradict n; reflexivity.
    }

    assert (RF1 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeOne
                  ≡ @inr string _ Float64asCT.Float64One).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      -
        clear - e.
        cbv in e.
        pose proof MRasCT.CTypeZeroOneApart.
        cbv in H.
        congruence.
      -
        clear - n0.
        contradict n0.
        reflexivity.
    }

    repeat progress (try setoid_rewrite RF0;
                     try setoid_rewrite RF1).

    reflexivity.
  Qed.

  Context
    `{RF_CHE : RHCOLtoFHCOL.CTranslation_heq}.

  Definition heq_nat_int : nat -> MInt64asNT.t -> Prop :=
    fun n i => Z.of_nat n ≡ Int64.intval i.

  Global Instance RF_NHE : RHCOLtoFHCOL.NTranslation_heq.
  Proof.
    econstructor.
    instantiate (1:= heq_nat_int).
    -
      intros n1 n2 EN i1 i2 EI.
      unfold heq_nat_int.
      cbv in EN; subst n2; rename n1 into n.
      pose proof Integers.Int64.eq_spec i1 i2 as EQI.
      rewrite EI in EQI.
      apply f_equal with (f:=Int64.intval) in EQI.
      lia.
    -
      unfold RHCOLtoFHCOL.translateNTypeConst.
      unfold MInt64asNT.from_nat, NatAsNT.MNatAsNT.to_nat, MInt64asNT.from_Z.
      intros * TR.
      repeat break_match; invc TR.
      pose proof Integers.Int64.eq_spec
           {| Int64.intval := Z.of_nat x; Int64.intrange := conj l l0 |}
           x'
        as EQI.
      rewrite H1 in EQI.
      rewrite <-EQI.
      reflexivity.
  Defined.

  Global Instance RF_NTP : RHCOLtoFHCOL.NTranslationProps.
  Proof.
    constructor; intros *.
    all: unfold RF_NHE, heq_NType, heq_nat_int.
    all: unfold NatAsNT.MNatAsNT.to_nat, MInt64asNT.to_nat.
    all: unfold NatAsNT.MNatAsNT.from_nat, MInt64asNT.from_nat, MInt64asNT.from_Z.
    -
      intros NI.
      rewrite <-NI.
      rewrite Nat2Z.id.
      reflexivity.
    -
      unfold MInt64asNT.from_Z.
      repeat break_match;
        constructor.
      reflexivity.
  Qed.

End RCHOL_to_FHCOL.

(* TODO: move *)
Require Import Rdefinitions.

Section RHCOL_to_FHCOL_numerical.

  Context `{RF_CHE : RHCOLtoFHCOL.CTranslation_heq}.

  (* TODO: move *)
  Lemma trivial2_Proper `{AE : Equiv A} `{BE : Equiv B} :
    Proper (equiv ==> equiv ==> iff) (@trivial2 A B).
  Proof.
    repeat constructor.
  Qed.

  Ltac crush_int :=
    repeat rewrite !Int64.unsigned_repr;
    replace Int64.max_unsigned
      with 18446744073709551615%Z
      in *
        by reflexivity;
    try lia.

  Ltac unfold_RF_NType_ops :=
    unfold
      NatAsNT.MNatAsNT.to_nat,
      NatAsNT.MNatAsNT.from_nat
      in * ;
    unfold
      MInt64asNT.to_nat,
      MInt64asNT.from_nat
      in *;
    unfold
      NatAsNT.MNatAsNT.NTypePlus,
      NatAsNT.MNatAsNT.NTypeDiv,
      NatAsNT.MNatAsNT.NTypeMod,
      NatAsNT.MNatAsNT.NTypePlus,
      NatAsNT.MNatAsNT.NTypeMinus,
      NatAsNT.MNatAsNT.NTypeMult,
      NatAsNT.MNatAsNT.NTypeMin,
      NatAsNT.MNatAsNT.NTypeMax
      in *;
    unfold
      MInt64asNT.NTypePlus,
      MInt64asNT.NTypeDiv,
      MInt64asNT.NTypeMod,
      MInt64asNT.NTypePlus,
      MInt64asNT.NTypeMinus,
      MInt64asNT.NTypeMult,
      MInt64asNT.NTypeMin,
      MInt64asNT.NTypeMax
      in *;
    unfold
      Int64.divu,
      Int64.modu,
      Int64.add,
      Int64.sub,
      Int64.mul,
      Int64.lt
      in *.

  (* note: the two [try] blocks are for RHCOL/FHCOL lemma *)
  Ltac destruct_context_range_lookup ΣR x :=
    let TΣR := fresh "TΣR" in
    let nv := fresh "nv" in
    let p := fresh "p" in
    let NV := fresh "NV" in
    let Σ := fresh "Σ" in
    pose proof ΣR as TΣR;
    try (eapply RHCOLEval.evalContext_in_range_lookup_Index
          with (k:=x) in TΣR;
         [| reflexivity]);
    try (eapply FHCOLEval.evalContext_in_range_lookup_Index
          with (k:=x) in TΣR;
         [| reflexivity]);
    destruct TΣR as (nv & p & NV & Σ);
    rewrite Σ.

  (* Instances for trivial comparison of CType values
     in RHCOL->FHCOL translation.
     Any two numbers are considered "equal" ([trivial2]).

     These allow to infer structural properties of translation,
     while disregarding CType values (and CType values only).

     The statement [RF_Structural_Semantic_Preservation]
     is the full semantic preservation on RHCOL->FHCOL, up to CType values.
   *)
  Local Definition trivial_RF_CHE : RHCOLtoFHCOL.CTranslation_heq.
    econstructor.
    instantiate (1 := trivial2).
    typeclasses eauto.
    repeat constructor.
  Defined.

  Local Fact trivial_RF_COP
    : @RHCOLtoFHCOL.COpTranslationProps trivial_RF_CHE.
  Proof.
    repeat constructor.
  Qed.

  Definition RF_Structural_Semantic_Preservation :=
    @RHCOLtoFHCOL.translation_semantics_correct
      RF_NHE
      trivial_RF_CHE
      RF_NTP
      trivial_RF_COP.

  Lemma RHCOLtoFHCOL_NExpr_closure_trace_equiv
        (dynwin_F_σ : evalContext)
        (dynwin_FHCOL : FHCOL.DSHOperator)
    :
    RHCOLtoFHCOL.translate dynwin_RHCOL = inr dynwin_FHCOL ->

    RHCOLtoFHCOL.heq_evalContext dynwin_R_σ dynwin_F_σ ->

    hopt (herr (@RHCOLtoFHCOL.evalNExpr_closure_trace_equiv RF_NHE trivial_RF_CHE))
         (RHCOLEval.intervalEvalDSHOperator_σ
            dynwin_R_σ dynwin_RHCOL []
            (RHCOLEval.estimateFuel dynwin_RHCOL))
         (intervalEvalDSHOperator_σ
            dynwin_F_σ dynwin_FHCOL []
            (estimateFuel dynwin_FHCOL)).
  Proof.
    intros RF RFΣ.

    assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
                  ≡ @inr string _ Float64asCT.Float64Zero).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      all: clear - n; contradict n; reflexivity.
    }

    assert (RF1 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeOne
                  ≡ @inr string _ Float64asCT.Float64One).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      -
        clear - e.
        cbv in e.
        pose proof MRasCT.CTypeZeroOneApart.
        cbv in H.
        congruence.
      -
        clear - n0.
        contradict n0.
        reflexivity.
    }

    cbn in RF.
    repeat progress (try setoid_rewrite RF0 in RF;
                     try setoid_rewrite RF1 in RF).
    repeat inl_inr_inv.

    remember (FHCOLEval.DSHAlloc _ _) as dynwin_fhcol_comp eqn:FC.
    (* poor man's [rewrite <-RC, <-FC] *)
    assert (T2 : FHCOLEval.intervalEvalDSHOperator_σ
                   dynwin_F_σ dynwin_FHCOL []
                   (FHCOLEval.estimateFuel dynwin_FHCOL)
                 =
                   FHCOLEval.intervalEvalDSHOperator_σ
                     dynwin_F_σ dynwin_fhcol_comp []
                     (FHCOLEval.estimateFuel dynwin_fhcol_comp))
      by now rewrite RF.
    eapply hopt_proper;
      [ apply herr_proper, RHCOLtoFHCOL.evalNExpr_closure_trace_equiv_proper
      | reflexivity
      | apply T2
      | ].

    (** Following is the semi-manual "numerical analysis" part **)
    subst; cbn.
    repeat constructor.

    1,3,5,7,9-14: cbn.
    1-10: intros * ΣR ΣR' ΣE NE.
    1-10: pose proof ΣE as Σ3E.
    1-10: match goal with
          | [ |- context [ RHCOLEval.context_lookup _ _ ?k ]] =>
              eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=k) in Σ3E
          end.
    1-10: match goal with
          | [ |- context [ RHCOLEval.context_lookup _ _ ?n ]] =>
              destruct_context_range_lookup ΣR n;
              destruct_context_range_lookup ΣR' n
          end.
    1-10: constructor.
    1-10: rewrite Σ, Σ0 in Σ3E.
    1-10: cbn in Σ3E; invc Σ3E; invc H1; invc H0; assumption.

    (* TODO: all 4 subogals are exact copies *)
    -
      cbn.
      intros * ΣR ΣR' ΣE NE.

      destruct_context_range_lookup ΣR 3.
      destruct_context_range_lookup ΣR' 3.

      pose proof ΣE as Σ3E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=3) in Σ3E.
      rewrite Σ, Σ0 in Σ3E.
      cbn in Σ3E.
      invc Σ3E; invc H1; invc H0; invc H.

      destruct_context_range_lookup ΣR 1.
      destruct_context_range_lookup ΣR' 1.

      pose proof ΣE as Σ1E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=1) in Σ1E.
      rewrite Σ1, Σ2 in Σ1E.
      cbn in Σ1E.
      invc Σ1E; invc H1; invc H0; invc H.

      constructor.
      unfold_RF_NType_ops.
      cbn.

      unfold heq_NType, RF_NHE, heq_nat_int in *.
      replace (Int64.unsigned nv0)
        with (Z.of_nat nv)
        by (now unfold Int64.unsigned).
      replace (Int64.unsigned nv2)
        with (Z.of_nat nv1)
        by (now unfold Int64.unsigned).
      crush_int.
    -
      cbn.
      intros * ΣR ΣR' ΣE NE.

      destruct_context_range_lookup ΣR 3.
      destruct_context_range_lookup ΣR' 3.

      pose proof ΣE as Σ3E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=3) in Σ3E.
      rewrite Σ, Σ0 in Σ3E.
      cbn in Σ3E.
      invc Σ3E; invc H1; invc H0; invc H.

      destruct_context_range_lookup ΣR 1.
      destruct_context_range_lookup ΣR' 1.

      pose proof ΣE as Σ1E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=1) in Σ1E.
      rewrite Σ1, Σ2 in Σ1E.
      cbn in Σ1E.
      invc Σ1E; invc H1; invc H0; invc H.

      constructor.
      unfold_RF_NType_ops.
      cbn.

      unfold heq_NType, RF_NHE, heq_nat_int in *.
      replace (Int64.unsigned nv0)
        with (Z.of_nat nv)
        by (now unfold Int64.unsigned).
      replace (Int64.unsigned nv2)
        with (Z.of_nat nv1)
        by (now unfold Int64.unsigned).
      crush_int.
    -
      cbn.
      intros * ΣR ΣR' ΣE NE.

      destruct_context_range_lookup ΣR 3.
      destruct_context_range_lookup ΣR' 3.

      pose proof ΣE as Σ3E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=3) in Σ3E.
      rewrite Σ, Σ0 in Σ3E.
      cbn in Σ3E.
      invc Σ3E; invc H1; invc H0; invc H.

      destruct_context_range_lookup ΣR 1.
      destruct_context_range_lookup ΣR' 1.

      pose proof ΣE as Σ1E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=1) in Σ1E.
      rewrite Σ1, Σ2 in Σ1E.
      cbn in Σ1E.
      invc Σ1E; invc H1; invc H0; invc H.

      constructor.
      unfold_RF_NType_ops.
      cbn.

      unfold heq_NType, RF_NHE, heq_nat_int in *.
      replace (Int64.unsigned nv0)
        with (Z.of_nat nv)
        by (now unfold Int64.unsigned).
      replace (Int64.unsigned nv2)
        with (Z.of_nat nv1)
        by (now unfold Int64.unsigned).
      crush_int.
    -
      cbn.
      intros * ΣR ΣR' ΣE NE.

      destruct_context_range_lookup ΣR 3.
      destruct_context_range_lookup ΣR' 3.

      pose proof ΣE as Σ3E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=3) in Σ3E.
      rewrite Σ, Σ0 in Σ3E.
      cbn in Σ3E.
      invc Σ3E; invc H1; invc H0; invc H.

      destruct_context_range_lookup ΣR 1.
      destruct_context_range_lookup ΣR' 1.

      pose proof ΣE as Σ1E.
      eapply RHCOLtoFHCOL.heq_evalContext_heq_context_lookup with (n:=1) in Σ1E.
      rewrite Σ1, Σ2 in Σ1E.
      cbn in Σ1E.
      invc Σ1E; invc H1; invc H0; invc H.

      constructor.
      unfold_RF_NType_ops.
      cbn.

      unfold heq_NType, RF_NHE, heq_nat_int in *.
      replace (Int64.unsigned nv0)
        with (Z.of_nat nv)
        by (now unfold Int64.unsigned).
      replace (Int64.unsigned nv2)
        with (Z.of_nat nv1)
        by (now unfold Int64.unsigned).
      crush_int.
  Qed.

End RHCOL_to_FHCOL_numerical.

From Interval Require Import Tactic.

From Flocq Require Import Binary Bits Core.Defs.
Require Import Vellvm.Numeric.Floats.
Require Import Vellvm.Numeric.IEEE754_extra.

Require Import Float32asCT.
Section RHCOL_to_FHCOL_bounds.

  Context
    `{RF_CHE_32 : RHCOLtoFHCOL32.CTranslation_heq}
    `{RF_CHE : RHCOLtoFHCOL.CTranslation_heq}.

  Inductive is_NaN_32 : binary32 -> Prop :=
  | B754_nan_is_NaN_32 : forall s pl NPL,
      is_NaN_32 (@B754_nan _ _ s pl NPL).

  Definition le32 (a b : binary32) : Prop :=
    b32_compare a b ≡ Some Datatypes.Eq
    \/ b32_compare a b ≡ Some Datatypes.Lt.

  Definition lt32 (a b : binary32) : Prop :=
    b32_compare a b ≡ Some Datatypes.Lt.

  (* inclusive range check *)
  Definition in_range_32 : (binary32 * binary32) -> binary32 -> Prop
    := fun '(a,b) x =>
         not (is_NaN_32 x)
         /\ le32 a x
         /\ le32 x b.

  (* left excluded, right included range check *)
  Definition in_range_32_l : (binary32 * binary32) -> binary32 -> Prop
    := fun '(a,b) x =>
         not (is_NaN_32 x)
         /\ lt32 a x
         /\ le32 x b.


  Local Open Scope R_scope.

  Definition b32_0_1 := b32_of_bits 1036831949%Z. (* 0.1 *)
  Definition b32_0_01 := b32_of_bits 1008981770%Z. (* 0.01 *)

  Definition b32_0     := b32_of_bits 0%Z.
  Definition b32_1     := b32_of_bits 1065353216%Z.
  Definition b32_2     := b32_of_bits 1073741824%Z.
  Definition b32_5     := b32_of_bits 1084227584%Z.
  Definition b32_6     := b32_of_bits 1086324736%Z.
  Definition b32_10    := b32_of_bits 1092616192%Z.
  Definition b32_20    := b32_of_bits 1101004800%Z.
  Definition b32_100   := b32_of_bits 1120403456%Z.
  Definition b32_5000  := b32_of_bits 1167867904%Z.

  (** Constraints on physical parameters **)
  (* Obstacle velocity constraint *)
  (* 0 <= V <= 20. up to 20 m/s (72 Kmh) *)
  Definition V_constr := (b32_0, b32_20).
  (* 1 < b <= 6. m/s^2. https://copradar.com/chapts/references/acceleration.html *)
  Definition b_constr := (b32_1, b32_6).
  (* 0 <= A <= 5. m/s^2. https://hypertextbook.com/facts/2001/MeredithBarricella.shtml *)
  Definition A_constr := (b32_0, b32_5).
  Definition e_constr := (b32_0_01, b32_0_1). (* 1/100 <= e <= 1/10. 10-100 Hz *)
  (* Constraints for obstacle and robot coordinates.
     Our robot operates on cartesian grid ~10x10 Km *)
  Definition x_constr := (b32_opp b32_5000, b32_5000). (* -5000, 5000 *)
  Definition y_constr := (b32_opp b32_5000, b32_5000). (* -5000, 5000 *)
  (* Robot velocity constraint *)
  Definition v_constr := (b32_0, b32_20). (* 0, 20 *)

  (*
    "a" layout:
     a0 = (A/b + 1.0) * ((A/2.0)*e*e + e*V)
     a1 = V/b + e*(A/b+1.0)
     a2 = 1.0/(2.0*b)

    "x" layout:
    0. robot velocity
    1. robot position (X)
    2. robot position (Y)
    3. obstacle position (X)
    4. obstacle position (Y)
   *)
  Definition make_a32 (V32 b32 A32 e32 : binary32) : FHCOL32.mem_block :=
    let FT_div := b32_div FT_Rounding in (* DHCOL (and therefore CType) has no division *)
    let a0 :=
      MFloat32asCT.CTypeMult
        (MFloat32asCT.CTypePlus (FT_div A32 b32) b32_1)
        (MFloat32asCT.CTypePlus
           (MFloat32asCT.CTypeMult (MFloat32asCT.CTypeMult (FT_div A32 b32_2) e32) e32)
           (MFloat32asCT.CTypeMult e32 V32))
    in
    let a1 :=
      (MFloat32asCT.CTypePlus
         (FT_div V32 b32)
         (MFloat32asCT.CTypeMult
            e32
            (MFloat32asCT.CTypePlus (FT_div A32 b32) b32_1)))
    in
    let a2 :=
      FT_div 
        b32_1
        (MFloat32asCT.CTypeMult b32_2 b32)
    in
    FHCOLEval32.mem_add 0%nat a0
      (FHCOLEval32.mem_add 1%nat a1
         (FHCOLEval32.mem_add 2%nat a2
            (FHCOLEval32.mem_empty))).

  Definition make_x32 (r_v_32 r_x_32 r_y_32 o_x_32 o_y_32 : binary32) : FHCOL32.mem_block :=
    FHCOLEval32.mem_add 0%nat r_v_32
      (FHCOLEval32.mem_add 1%nat r_x_32
        (FHCOLEval32.mem_add 2%nat r_y_32
          (FHCOLEval32.mem_add 3%nat o_x_32
            (FHCOLEval32.mem_add 4%nat o_y_32
              (FHCOLEval32.mem_empty))))).

  (* Widen binary32 to binary64.  This is a loseless conversion and it
     always succeeds. *)
  Definition widen32_to_64 (x32:binary32): binary64
    := Float32.to_double x32.

  (* Proof that converting 32 to 64 float does not cause any data loss
     for finite (non-NaN) numbers.  It is not true another way around! *)
  Fact widen32_to_64_loseless :
    forall x32,
      is_finite _ _ x32 ≡ true ->
      B2R _ _ (widen32_to_64 x32) ≡ B2R _ _ x32.
  Proof.
    intros H x32.
    unfold widen32_to_64, Float32.to_double.
    Transparent Float.of_single Float.to_single.
    unfold Float.of_single, Float.to_single.
    apply IEEE754_extra.Bconv_widen_exact.
    - cbv; reflexivity.
    - lia.
    - lia.
    - assumption.
  Qed.

  (** Widen a memory block with 32-bit binary floats to memory block with
      64-binary floats. This is a loseless conversion and it always succeeds *)
  Definition widen32_to_64_mem_block : FHCOL32.mem_block → FHCOL.mem_block
    := Memory.NM.map widen32_to_64.

  (** Cast a 64-bit binary float to 32-binary float.  This is a lossy
      conversion and must model C doulbe to single precision cast.
      For example:
      LLVM: %1 = fptrunc double %2 to float
      X86: cvtsd2ss xmm0, xmm0
      ARM64: fcvt s0, d0
   *)
  Definition cast64_to_32 (x64:binary64): binary32
    := Float.to_single x64.

  (** Cast a 64-bit binary float to 32-binary float. This is a lossy
      conversion. See [cast64_to_32] *)
  Definition cast64_to_32_mem_block : FHCOL.mem_block → FHCOL32.mem_block
    := Memory.NM.map cast64_to_32.

  (* Constraints on input memory blocks which we assume to prove
     numerical stability of FHCOL DynWin code.  Here, we enforce some
     reasonable numerical bounds on dynwin physical parameters.  *)
  Definition DynWinInConstr (a:RHCOLEval.mem_block) (x:RHCOLEval.mem_block): Prop
    :=
    ∃ V32 (* max obstacle speed *)
      b32 (* max braking *)
      A32 (* max accel *)
      e32 (* sampling period *)
      r_v_32
      r_x_32
      r_y_32
      o_x_32
      o_y_32,

      in_range_32 V_constr V32
      /\ in_range_32_l b_constr b32
      /\ in_range_32 A_constr A32
      /\ in_range_32 e_constr e32
      /\ heq_mem_block a (make_a32 V32 b32 A32 e32)
      /\ in_range_32 v_constr r_v_32
      /\ in_range_32 x_constr r_x_32
      /\ in_range_32 y_constr r_y_32
      /\ in_range_32 x_constr o_x_32
      /\ in_range_32 y_constr o_y_32
      /\ heq_mem_block x (make_x32 r_v_32 r_x_32 r_y_32 o_x_32 o_y_32).


  (* Parametric relation between RHCOL and FHCOL coumputation results  *)
  Definition DynWinOutRel
             (a_r:RHCOLEval.mem_block)
             (x_r:RHCOLEval.mem_block)
             (y_r:RHCOLEval.mem_block)
             (y_64:FHCOLEval.mem_block): Prop
    :=
    (* cast 64 bit output to 32 bit, simlating
       C/LLVM cast as in [cast64_to_32]
       result of the cast should be the same as
       32 bit approximation of result on Reals *)
    heq_mem_block y_r (cast64_to_32_mem_block y_64).

  Global Instance DynWinOutRel_Proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (iff)) DynWinOutRel.
  Admitted.

End RHCOL_to_FHCOL_bounds.

Section TopLevel.

  (* RHCOL -> FHCOL *)
  Context
    `{RF_CHE_32 : RHCOLtoFHCOL32.CTranslation_heq}
    `{RF_CHE : RHCOLtoFHCOL.CTranslation_heq}.

  (*
  (* User can specify optional constraints on input values and
     arguments. For example, for cyber-physical system it could
     include ranges and relatoin between parameters. *)
  Parameter InConstr: (* a *) RHCOLEval.mem_block -> (*x*) RHCOLEval.mem_block -> Prop.

  (* Parametric relation between RHCOL and FHCOL coumputation results  *)
  Parameter OutRel : (* a *) RHCOLEval.mem_block ->
                     (* x *) RHCOLEval.mem_block ->
                     (* y *) RHCOLEval.mem_block ->
                     (* y_mem *) FHCOLEval.mem_block -> Prop.
   *)

  Lemma DynWin_RHCOL_to_FHCOL_op_OK :
    exists r, RHCOLtoFHCOL.translate dynwin_RHCOL = inr r.
  Proof.
    cbn.

    assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
                  ≡ @inr string _ Float64asCT.Float64Zero).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      all: clear - n; contradict n; reflexivity.
    }

    assert (RF1 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeOne
                  ≡ @inr string _ Float64asCT.Float64One).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      -
        clear - e.
        cbv in e.
        pose proof MRasCT.CTypeZeroOneApart.
        cbv in H.
        congruence.
      -
        clear - n0.
        contradict n0.
        reflexivity.
    }

    repeat progress (try setoid_rewrite RF0;
                     try setoid_rewrite RF1).
    now eexists.
  Qed.

  (*
    Translation validation proof of semantic preservation
    of successful translation of [dynwin_orig] into FHCOL program.

    Using following definitons from DynWin.v:
     1. dynwin_i
     2. dynwin_o
     3. dynwin_orig

     And the following definition are produced with TemplateCoq:
     1. dynwin_RHCOL
   *)
  Theorem HCOL_to_FHCOL_Correctness (a: ctvector 3):
    forall x y,
      (* evaluatoion of original operator *)
      dynwin_orig a x = y ->

      forall dynwin_F_memory dynwin_F_σ (dynwin_FHCOL:FHCOL.DSHOperator),
        (* Compile -> RHCOL -> FHCOL *)
        RHCOLtoFHCOL.translate dynwin_RHCOL = inr dynwin_FHCOL ->

        (* Equivalent inputs *)
        RHCOLtoFHCOL.heq_memory (dynwin_R_memory a x) dynwin_F_memory ->
        RHCOLtoFHCOL.heq_evalContext dynwin_R_σ dynwin_F_σ ->

        forall a_rmem x_rmem,
          RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_a_addr = Some a_rmem ->
          RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_x_addr = Some x_rmem ->
          DynWinInConstr a_rmem x_rmem ->

          (* Everything correct on Reals *)
          exists r_omemory y_rmem,
            RHCOLEval.evalDSHOperator
              dynwin_R_σ
              dynwin_RHCOL
              (dynwin_R_memory a x)
              (RHCOLEval.estimateFuel dynwin_RHCOL) = Some (inr r_omemory)
            /\ RHCOLEval.memory_lookup r_omemory dynwin_y_addr = Some y_rmem
            /\ ctvector_to_mem_block y = y_rmem

            (* And floats *)
            /\ exists f_omemory y_fmem,
              FHCOLEval.evalDSHOperator
                dynwin_F_σ dynwin_FHCOL
                dynwin_F_memory
                (FHCOLEval.estimateFuel dynwin_FHCOL) = (Some (inr f_omemory))
              /\ FHCOLEval.memory_lookup f_omemory dynwin_y_addr = Some y_fmem
              /\ DynWinOutRel a_rmem x_rmem y_rmem y_fmem.
  Proof.
    intros * HC * CR CRM CRE * RA RX C.

    remember (RHCOLEval.memory_set
                (dynwin_R_memory a x)
                dynwin_y_addr
                (ctvector_to_mem_block y)) as r_omemory eqn:ROM.

    assert(RHCOLEval.evalDSHOperator
             dynwin_R_σ
             dynwin_RHCOL
             (dynwin_R_memory a x)
             (RHCOLEval.estimateFuel dynwin_RHCOL) = Some (inr r_omemory)) as RO.
    {
      pose proof (DynWin_MSH_DSH_compat a) as MRHCOL.
      pose proof (DynWin_pure) as MAPURE.
      pose proof (dynwin_SHCOL_MSHCOL_compat a) as MCOMP.
      pose proof (SHCOL_to_SHCOL1_Rewriting a) as SH1.
      pose proof (DynWinSigmaHCOL_Value_Correctness a) as HSH.
      pose proof (DynWinHCOL a x x) as HH.
      autospecialize HH; [reflexivity|].
      rewrite HC in HH. clear HC.

      (* moved from [dynwin_orig] to [dynwin_HCOL] *)

      remember (sparsify Monoid_RthetaFlags x) as sx eqn:SX.
      remember (sparsify Monoid_RthetaFlags y) as sy eqn:SY.
      assert(SHY: op _ (dynwin_SHCOL a) sx = sy).
      {
        subst sy.
        rewrite_clear HH.

        specialize (HSH sx sx).
        autospecialize HSH; [reflexivity|].
        rewrite <- HSH. clear HSH.
        unfold liftM_HOperator.
        Opaque dynwin_HCOL equiv.
        cbn.
        unfold SigmaHCOLImpl.liftM_HOperator_impl.
        unfold compose.
        f_equiv.
        subst sx.
        rewrite densify_sparsify.
        reflexivity.
      }
      Transparent dynwin_HCOL equiv.
      clear HH HSH.

      (* moved from [dynwin_HCOL] to [dynwin_SHCOL] *)

      assert(SH1Y: op _ (dynwin_SHCOL1 a) sx = sy).
      {
        rewrite <- SHY. clear SHY.
        destruct SH1.
        rewrite H.
        reflexivity.
      }
      clear SHY SH1.

      (* moved from [dynwin_SHCOL] to [dynwin_SHCOL1] *)

      assert(M1: mem_op (dynwin_MSHCOL1 a) (svector_to_mem_block Monoid_RthetaFlags sx) = Some (svector_to_mem_block Monoid_RthetaFlags sy)).
      {
        cut(Some (svector_to_mem_block Monoid_RthetaFlags (op Monoid_RthetaFlags (dynwin_SHCOL1 a) sx)) = mem_op (dynwin_MSHCOL1 a) (svector_to_mem_block Monoid_RthetaFlags sx)).
        {
          intros M0.
          rewrite <- M0. clear M0.
          apply Some_proper.

          cut(svector_is_dense _ (op Monoid_RthetaFlags (dynwin_SHCOL1 a) sx)).
          intros YD.

          apply svector_to_mem_block_dense_kind_of_proper.
          apply YD.

          subst sy.
          apply sparsify_is_dense.
          typeclasses eauto.

          apply SH1Y.

          {
            pose proof (@out_as_range _ _ _ _ _ _ (DynWinSigmaHCOL1_Facts a)) as D.
            specialize (D sx).

            autospecialize D.
            {
              intros j jc H.
              destruct (dynwin_SHCOL1 a).
              cbn in H.
              subst sx.
              rewrite Vnth_sparsify.
              apply Is_Val_mkValue.
            }

                unfold svector_is_dense.
            apply Vforall_nth_intro.
            intros i ip.
            apply D.
            cbn.
            constructor.
          }
        }
        {
          destruct MCOMP.
          apply mem_vec_preservation.
          cut(svector_is_dense Monoid_RthetaFlags (sparsify _ x)).
          intros SD.
          unfold svector_is_dense in SD.
          intros j jc H.
          apply (Vforall_nth jc) in SD.
          subst sx.
          apply SD.
          apply sparsify_is_dense.
          typeclasses eauto.
        }
      }
      clear SH1Y MCOMP.

      (* moved from [dynwin_SHCOL1] to [dynwin_MSHCOL1] *)

      remember (svector_to_mem_block Monoid_RthetaFlags sx) as mx eqn:MX.
      remember (svector_to_mem_block Monoid_RthetaFlags sy) as my eqn:MY.

      specialize (MRHCOL (ctvector_to_mem_block x)).
      replace (dynwin_memory a (ctvector_to_mem_block x))
        with (dynwin_R_memory a x) in MRHCOL by reflexivity.
      destruct MRHCOL as [MRHCOL].
      specialize (MRHCOL (ctvector_to_mem_block x) RHCOLEval.mem_empty).
      autospecialize MRHCOL.
      reflexivity.
      autospecialize MRHCOL.
      reflexivity.

      destruct_h_opt_opterr_c MM AE.
      -
        destruct s; inversion_clear MRHCOL.
        f_equiv; f_equiv.
        rename m0 into m'.
        destruct (lookup_PExpr dynwin_R_σ m' DSH_y_p) eqn:RY.
        +
          exfalso.
          clear - MAPURE AE RY.
          cbn in RY.
          assert (RHCOL.mem_block_exists 1 m').
          {
            erewrite <-mem_stable.
            2: now rewrite AE.
            now apply RHCOLEval.memory_is_set_is_Some.
          }
          apply RHCOLEval.memory_is_set_is_Some in H.
          unfold util.is_Some, RHCOLEval.memory_lookup_err in *.
          break_match; try contradiction.
          inv RY.
        +
          inversion_clear H.
          rename m into ym.
          rename m0 into ym'.
          subst.
          destruct (dynwin_MSHCOL1 a).
          rewrite 2!svector_to_mem_block_ctvector_to_mem_block
            in M1
              by typeclasses eauto.
          Opaque ctvector_to_mem_block.
          cbn in M1, MM.
          rewrite MM in M1.
          clear MM.
          some_inv.
          Transparent ctvector_to_mem_block.

          rewrite <-M1.
          assert (YM : ym = ym').
          {
            clear - H0.
            intros k.
            specialize (H0 k).
            cbn in H0.
            unfold RHCOL.mem_lookup in *.
            inv H0.
            -
              unfold util.is_None in *.
              now break_match.
            -
              symmetry; assumption.
          }
          rewrite YM.

          clear - AE RY MAPURE.
          destruct MAPURE as [_ MWS].
          cbn; cbn in RY.
          eapply memory_equiv_except_memory_set_inv.
          eapply MWS.
          now erewrite AE.
          now cbv.
          eapply RHCOLEval.memory_lookup_err_inr_Some.
          now rewrite RY.
      -
        exfalso.
        pose proof (@RHCOLEval.evalDSHOperator_estimateFuel dynwin_R_σ dynwin_RHCOL (dynwin_R_memory a x)) as CC.
        clear - CC AE.
        apply util.is_None_def in AE.
        generalize dependent (RHCOLEval.evalDSHOperator dynwin_R_σ dynwin_RHCOL
                                                        (dynwin_R_memory a x) (RHCOLEval.estimateFuel dynwin_RHCOL)).
        intros o AE CC.
        some_none.
      -
        exfalso.
        remember (dynwin_MSHCOL1 a) as m.
        destruct m.
        subst sx mx.
        rewrite svector_to_mem_block_ctvector_to_mem_block in M1.
        eq_to_equiv.
        some_none.
        typeclasses eauto.
      -
        exfalso.
        remember (dynwin_MSHCOL1 a) as m.
        destruct m.
        subst sx mx.
        rewrite svector_to_mem_block_ctvector_to_mem_block in M1.
        eq_to_equiv.
        some_none.
        typeclasses eauto.
    }

    (* moved from [dynwin_MSHCOL1] to [dynwin_rhcol] *)

    generalize dependent (ctvector_to_mem_block y).
    intros y_rmem R_OMEM.

    exists r_omemory.
    exists y_rmem.

    split; [assumption |].
    split.
    1: {
      rewrite R_OMEM.
      now rewrite memory_lookup_memory_set_eq by reflexivity.
    }
    split; [reflexivity |].

    pose proof
         RF_Structural_Semantic_Preservation
         dynwin_RHCOL
         dynwin_FHCOL
         (RHCOLEval.estimateFuel dynwin_RHCOL)
         (FHCOLEval.estimateFuel dynwin_FHCOL)
         dynwin_R_σ
         dynwin_F_σ
         (dynwin_R_memory a x)
         dynwin_F_memory
      as HEQRF.
    full_autospecialize HEQRF.
    {
      now eapply RHCOLtoFHCOL.translation_syntax_always_correct.
    }
    {
      clear - CRE.
      induction CRE.
      -
        constructor.
      -
        constructor;
          [| apply IHCRE].
        unfold RHCOLtoFHCOL.heq_evalContextElem in *.
        repeat break_let; subst.
        repeat constructor.
        intuition.
        destruct H as [_ D].
        invc D; repeat constructor; assumption.
    }
    {
      clear - CRM.
      generalize dependent (dynwin_R_memory a x).
      clear.
      intros dynwin_R_memory M.

      intros k.
      specialize (M k).
      invc M; constructor.

      intros k'.
      specialize (H1 k').
      invc H1; constructor.
      constructor.
    }
    {
      now eapply @RHCOLtoFHCOL_NExpr_closure_trace_equiv.
    }

    subst r_omemory.
    destruct RHCOLEval.evalDSHOperator as [[e | r_omemory] |] eqn:RE in *;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.

    invc HEQRF; invc H1.
    rename b0 into f_omemory, H0 into F_EVAL, H2 into RF_OM.
    symmetry in RO, F_EVAL.

    exists f_omemory.

    unfold RHCOLEval.memory_set in RE.
    pose proof RF_OM as RF_YO.
    pose proof RO as R_YO.
    specialize (RF_YO dynwin_y_addr).
    specialize (R_YO dynwin_y_addr).
    unfold RHCOLEval.memory_set, RHCOLEval.memory_lookup in *.
    rewrite Memory.NP.F.add_eq_o in R_YO by reflexivity.

    invc RF_YO;
      [rewrite <-H0 in *; some_none |].
    rename b into y_fmem, H0 into Y_FMEM.
    rename a0 into y_rmem', H into Y_RMEM'.
    rename H1 into Y_RFE.
    symmetry in Y_RMEM', Y_FMEM.

    exists y_fmem.
    do 2 (split; [reflexivity |]).

    (* get rid of duplicate [y_rmem] *)
    rewrite Y_RMEM' in *.
    some_inv.
    rewrite R_YO.
    clear RO R_YO y_rmem.
    rename y_rmem' into y_rmem, Y_RMEM' into Y_RMEM.

    generalize dependent (dynwin_R_memory a x);
      intros r_imemory TRM A_RMEM X_RMEM R_EVAL.
    clear a x y HC.
    rename dynwin_F_memory into f_imemory, dynwin_F_σ into f_iσ.
    remember dynwin_R_σ as r_iσ.

    (* OutRel must hold (a,x,y_R,y_F) *)
    admit. (* this is provided by user *)

  Admitted.

End TopLevel.
