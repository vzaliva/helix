Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.VecSetoid.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.Util.Misc.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.HCOLImpl.
Require Import Helix.HCOL.THCOL.
Require Import Helix.HCOL.THCOLImpl.

Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.

Require Import Helix.Tactics.HelixTactics.
Require Import Helix.HCOL.HCOLBreakdown.
Require Import Helix.SigmaHCOL.SigmaHCOLRewriting.

Require Import MathClasses.interfaces.canonical_names.

Require Import Helix.DynWin.DynWin.

Require Import Helix.Util.FinNatSet.

(* dynamic window HCOL expression *)
Definition dynwin_HCOL (a: avector 3) :=
  (HBinOp (IgnoreIndex2 Zless) ∘
          HCross
          (HReduction plus 0 ∘ (HBinOp (IgnoreIndex2 mult) ∘ HPrepend a) ∘ HInduction _ mult 1)
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


Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

(*
Final HCOL -> Sigma-HCOL expression:

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
Definition dynwin_SHCOL (a: avector 3):
  @SHOperator Monoid_RthetaFlags (1+(2+2)) 1 zero :=

  (SafeCast (SHBinOp _ (IgnoreIndex2 Zless)))
    ⊚
    (HTSUMUnion _ plus (
                  ScatH _ 0 1
                        (range_bound := h_bound_first_half 1 1)
                        (snzord0 := @ScatH_stride1_constr 1 2)
                        ⊚
                        (liftM_HOperator _ (@HReduction _ plus 0)  ⊚
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
                         (snzord0 := @ScatH_stride1_constr 1 2))
                    ⊚
                    (liftM_HOperator _ (@HReduction _ minmax.max 0))
                    ⊚
                    (SHPointwise _ (IgnoreIndex abs))
                    ⊚
                    (SumSparseEmbedding
                       (n:=2)
                       (fun jf => SafeCast (SHBinOp _ (o:=1)
                                                 (Fin1SwapIndex2 jf (IgnoreIndex2 CarrierType.sub))))
                       (fun j => h_index_map (proj1_sig j) 1 (range_bound := (ScatH_1_to_n_range_bound (proj1_sig j) 2 1 (proj2_sig j))))
                       (f_inj := h_j_1_family_injective)
                       (fun j => h_index_map (proj1_sig j) 2 (range_bound:=GathH_jn_domain_bound (proj1_sig j) 2 (proj2_sig j))))
                    ⊚
                    (GathH _ 1 1
                           (domain_bound := h_bound_second_half 1 (2+2)))
                )
    ).


Require Import Helix.MSigmaHCOL.ReifyMSHCOL.
Run TemplateProgram (reifySHCOL dynwin_SHCOL1 100 ["dynwin_SHCOL1"] "dynwin_MSHCOL1").

Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.MSigmaHCOL.MemVecEq.

Ltac solve_facts :=
  repeat match goal with
         | [ |- SHOperator_Facts _ _ ] => apply SHBinOp_RthetaSafe_Facts
         | [ |- @SHOperator_Facts ?m ?i ?o _ (@SHBinOp _ _ ?o _ _) ] =>
           replace (@SHOperator_Facts m i) with (@SHOperator_Facts m (o+o)) by apply eq_refl
         | [ |- SHOperator_Facts _ _ ] => apply SHCompose_Facts
         | [ |- SHOperator_Facts _ _ ] => apply SafeCast_Facts
         | [ |- SHOperator_Facts _ _ ] => apply UnSafeCast_Facts
         | [ |- SHOperator_Facts _ _ ] => apply HTSUMUnion_Facts
         | [ |- SHOperator_Facts _ _ ] => apply SHCompose_Facts
         | [ |- SHOperator_Facts _ _ ] => apply Scatter_Rtheta_Facts
         | [ |- SHOperator_Facts _ _ ] => apply liftM_HOperator_Facts
         | [ |- SHOperator_Facts _ _ ] => apply Gather_Facts
         | [ |- SHOperator_Facts _ _ ] => apply SHPointwise_Facts
         | [ |- SHInductor_Facts _ _ ] => apply SHInductor_Facts
         | [ |- SHOperator_Facts _ _ ] => apply IUnion_Facts
         | [ |- SHOperator_Facts _ _ ] => apply IReduction_Facts
         | [ |- SHOperator_Facts _ (SumSparseEmbedding _ _) ] => unfold SumSparseEmbedding

         | [ |- Monoid.MonoidLaws Monoid_RthetaFlags] => apply MonoidLaws_RthetaFlags
         | _ => crush
         end.

Lemma dynwin_SHCOL_MSHCOL_compat {a}:
  SH_MSH_Operator_compat (dynwin_SHCOL1 a) (dynwin_MSHCOL1 a).
Proof.
  unfold dynwin_SHCOL1, dynwin_MSHCOL1.

  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply SafeCast_SH_MSH_Operator_compat.
  apply SHBinOp_RthetaSafe_SH_MSH_Operator_compat.
  apply HTSUMUnion_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply eUnion_SH_MSH_Operator_compat.
  { apply MonoidLaws_RthetaFlags. }
  apply SafeCast_SH_MSH_Operator_compat.
  apply IReduction_SH_MSH_Operator_compat.

  intros j jc.
  unfold SHFamilyOperatorCompose.
  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply SHPointwise_SH_MSH_Operator_compat.
  { apply MonoidLaws_SafeRthetaFlags. }
  apply SHInductor_SH_MSH_Operator_compat.
  { apply MonoidLaws_SafeRthetaFlags. }
  apply SHPointwise_SH_MSH_Operator_compat.
  { apply MonoidLaws_SafeRthetaFlags. }
  apply SHInductor_SH_MSH_Operator_compat.
  { apply MonoidLaws_SafeRthetaFlags. }

  solve_facts.
  apply SHInductor_MFacts.
  apply eT_SH_MSH_Operator_compat.
  solve_facts.
  solve_facts.

  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHPointwise_MFacts.
  apply SHInductor_MFacts.
  apply eT_MFacts.
  { simpl. admit. }
  solve_facts.
  solve_facts.
  apply eUnion_MFacts.
  apply IReduction_MFacts.
  intros j jc.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHPointwise_MFacts.
  apply SHInductor_MFacts.
  apply eT_MFacts.
  { simpl. admit. }

  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply eUnion_SH_MSH_Operator_compat.
  { apply MonoidLaws_RthetaFlags. }
  apply SafeCast_SH_MSH_Operator_compat.
  apply IReduction_SH_MSH_Operator_compat.
  intros j jc.
  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply SHBinOp_RthetaSafe_SH_MSH_Operator_compat.
  apply UnSafeCast_SH_MSH_Operator_compat.

  unfold ISumUnion.
  apply IUnion_SH_MSH_Operator_compat.
  intros j0 jc0.
  apply SHCompose_SH_MSH_Operator_compat.
  { simpl. admit. }
  apply eUnion_SH_MSH_Operator_compat.
  { apply MonoidLaws_RthetaFlags. }
  apply eT_SH_MSH_Operator_compat.
  apply eUnion_SH_MSH_Operator_compat.
  { apply MonoidLaws_RthetaFlags. }
  apply eT_SH_MSH_Operator_compat.
  apply eUnion_MFacts.
  apply eT_MFacts.
  { simpl. admit. }

  solve_facts.
  solve_facts.
  { simpl. admit. }
  apply SHBinOp_MFacts.
  apply IUnion_MFacts.
  intros j0 jc0.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply eUnion_MFacts.
  apply eT_MFacts.
  { simpl. admit. }
  { simpl. admit. }
  solve_facts.
  solve_facts.
  { simpl. admit. }
  { simpl. admit. }
  apply eUnion_MFacts.
  apply IReduction_MFacts.
  intros j jc.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHBinOp_MFacts.
  apply IUnion_MFacts.
  intros j0 jc0.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply eUnion_MFacts.
  apply eT_MFacts.
  { simpl. admit. }
  { simpl. admit. }
  typeclasses eauto. (* Monoid *)
  solve_facts.
  solve_facts.
  { simpl. admit. }
  { simpl. admit. }
  { simpl. admit. }
  apply SHBinOp_MFacts.
  apply HTSUMUnion_MFacts.
  { simpl. admit. }
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply eUnion_MFacts.
  apply IReduction_MFacts.
  intros j jc.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHPointwise_MFacts.
  apply SHInductor_MFacts.
  apply eT_MFacts.
  { simpl. admit. }
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply eUnion_MFacts.
  apply IReduction_MFacts.
  intros j jc.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply SHBinOp_MFacts.
  apply IUnion_MFacts.
  intros j0 jc0.
  apply SHCompose_MFacts.
  { simpl. admit. }
  apply eUnion_MFacts.
  apply eT_MFacts.
  { simpl. admit. }
  { simpl. admit. }
Qed.


Section SigmaHCOL_rewriting.

  (* --- HCOL -> Sigma->HCOL --- *)

  (* HCOL -> SigmaHCOL Value correctness. *)
  Lemma DynWinSigmaHCOL_Value_Correctness
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

  (* --- SigmaHCOL -> final SigmaHCOL --- *)

  Instance DynWinSigmaHCOL1_Facts
           (a: avector 3):
    SHOperator_Facts _ (dynwin_SHCOL1 a).
  Proof.
    unfold dynwin_SHCOL1.
    solve_facts.
    (* Now let's take care of remaining proof obligations *)
    -
      apply Disjoined_singletons.
      tauto.
    -
      unfold Included, In.
      intros x H.

      replace (Union (FinNat 2) (singleton 0) (Empty_set (FinNat 2))) with
          (singleton (n:=2) 0).
      {
        destruct x.
        destruct x.
        apply Union_intror.
        unfold singleton, In.
        crush.

        destruct x.
        apply Union_introl.
        unfold singleton, In.
        crush.

        crush.
      }
      apply Extensionality_Ensembles.
      apply Union_Empty_set_lunit.
      apply Singleton_FinNatSet_dec.
    -
      apply Disjoined_singletons.
      crush.
    -
      unfold Included, In.
      intros x H.

      destruct x.
      destruct x.
      apply Union_introl.
      unfold singleton, In.
      crush.

      destruct x.
      apply Union_intror.
      unfold singleton, In.
      crush.

      crush.
  Defined.

  (* Special case when results of 'g' comply to P. In tihs case we can discard 'g' *)
  Lemma Apply_Family_Vforall_P_move_P
        {fm}
        {svalue: CarrierA}
        {P:Rtheta' fm → Prop}
        {i1 o2 o3 n: nat}
        (f: @SHOperator fm o2 o3 svalue)
        (g: @SHOperatorFamily fm i1 o2 n svalue)
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
    generalize (op fm (g (mkFinNat jc)) x).
    clear x. intros x.
    specialize (H x).
    eapply Vforall_nth in H.
    apply H.
  Qed.

  Lemma SHPointwise_preserves_Apply_Family_Single_NonUnit_Per_Row
        {i1 o2 n: nat}
        (fam : @SHOperatorFamily Monoid_RthetaFlags i1 o2 n zero)
        (H: Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags fam)
        (f: FinNat o2 -> CarrierA -> CarrierA)
        {f_mor: Proper (equiv ==> equiv ==> equiv) f}
        (A: forall (i : nat) (ic : i<o2) (v : CarrierA), 0 ≠ f (mkFinNat ic) v -> 0 ≠ v):
    Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags
                                        (SHOperatorFamilyCompose
                                           Monoid_RthetaFlags
                                           (SHPointwise Monoid_RthetaFlags f (n:=o2))
                                           fam).
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
    unfold SHPointwise'.
    rewrite Vbuild_nth.
    unfold liftRthetaP.
    rewrite evalWriter_Rtheta_liftM.
    unfold IgnoreIndex, const.
    apply H.
  Qed.

  Lemma DynWinSigmaHCOL1_Value_Correctness (a: avector 3)
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
    Hint Opaque liftM_HOperator: rewrite.
    setoid_rewrite SafeCast_HReduction.

    (* Next rule *)
    rewrite terminate_Reduction by apply rings.plus_comm.

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

    (* Next rule: eT_Pointwise *)
    unfold SHFamilyOperatorCompose.
    simpl.

    (* --- BEGIN: hack ---
    I would expect the following to work here:

    setoid_rewrite rewrite_eT_SHPointwise
      with (g:=mult_by_1st (@le_S 2 2 (le_n 2)) a).

     But it does not (match fails), so we have to do some manual rewriting
     *)

    unfold eTn.
    match goal with
    | [ |- context [ IReduction plus ?f ]] =>
      match f with
      | (fun (jf:FinNat 3) => SHCompose _ (SHCompose _ (eT _ ?l) (SHPointwise _ ?c)) ?rest) =>  setoid_replace f with
            (fun (jf:FinNat 3) => SHCompose _ (SHCompose _ (SHPointwise _ (Fin1SwapIndex jf c)) (eT _ l)) rest)
      end
    end.

    all:revgoals.
    unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
    intros [j jc].
    f_equiv.
    simpl.
    apply rewrite_eT_SHPointwise.
    (* --- END: hack --- *)

    (* now solve some obligations *)
    {
      intros x z.
      unfold Fin1SwapIndex, const.
      reflexivity.
    }

    (* Next rule: eT_Induction *)
    setoid_rewrite SHCompose_assoc at 2.

    setoid_rewrite rewrite_eT_Induction.

    (* Bring `eT` into `IReduction` *)
    setoid_rewrite SHCompose_assoc at 1.
    rewrite <- SafeCast_SHCompose.
    setoid_rewrite rewrite_IReduction_absorb_operator.

    (* Fix SHBinOp type *)
    rewrite <- SafeCast_SHBinOp.

    setoid_rewrite <- SHInductor_equiv_lifted_HInductor.

    unfold dynwin_SHCOL1.

    reflexivity.
  Qed.

  (* Couple additional structual properties: input and output of the dynwin_SHCOL1 is dense *)

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

      (* The following could be automated with nifty tactics but for now we will do it manually. *)

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
      crush.
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

  (* Putting it all together: Final proof of SigmaHCOL rewriting *)
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
        rewrite E, E1.
        unfold Included.
        intros x H.
        auto.
      +
        pose proof (DynWinSigmaHCOL_dense_output a) as E.
        pose proof (DynWinSigmaHCOL1_dense_output a) as E1.
        apply Extensionality_Ensembles in E.
        apply Extensionality_Ensembles in E1.
        rewrite E, E1.
        unfold Same_set.
        split; unfold Included; auto.
  Qed.

End SigmaHCOL_rewriting.


Require Import Helix.MSigmaHCOL.MemVecEq.

Section SigmaHCOL_mem.

  Ltac solve_mem :=
    match goal with
    | [ |- SHOperator_Mem (SHCompose _ _ _)] => unshelve eapply SHCompose_Mem
    | [ |- SHOperator_Mem (SafeCast _ ) ] => unshelve eapply SafeCast_Mem
    | [ |- SHOperator_Mem (UnSafeCast _ ) ] => unshelve  eapply UnSafeCast_Mem
    | [ |- @SHOperator_Mem Monoid_RthetaSafeFlags ?mi ?mo ?msv (@SHBinOp _ _ ?o _ _) _ ] =>
      replace (@SHOperator_Mem Monoid_RthetaSafeFlags mi) with (@SHOperator_Mem Monoid_RthetaSafeFlags (o+o)) by f_equiv;
      unshelve eapply SHBinOp_RthetaSafe_Mem
    | [ |- SHOperator_Mem (HTSUMUnion _ _ _ _) ] => unshelve eapply HTSUMUnion_Mem
    | [ |- SHOperator_Mem (eUnion _ _) ] => unshelve eapply eUnion_Mem
    | [ |- SHOperator_Mem (IReduction _ _)] => unshelve eapply IReduction_Mem
    | [ |- SHOperator_Mem _ (SumSparseEmbedding _ _) ] => unfold SumSparseEmbedding
    | [ |- Monoid.MonoidLaws Monoid_RthetaFlags] => unshelve eapply MonoidLaws_RthetaFlags
    | [ |- SHOperator_Mem (SHPointwise _)] => unshelve eapply SHPointwise_Mem
    | [ |- SHInductor_Mem (SHInductor _ _ _) ] => unshelve eapply SHInductor_Mem
    | [ |- SHOperator_Mem (IUnion _ _) ] => unshelve eapply IUnion_Mem
    | [ |- SHOperator_Mem (ISumUnion _)] => unfold ISumUnion; unshelve eapply IUnion_Mem
    | [ |- SHOperator_Mem (eT _ _)] => unshelve eapply eT_Mem
    | [ |- @abstract_algebra.Monoid CarrierA CarrierAe (@plus CarrierA CarrierAplus)
                                   (@zero CarrierA CarrierAz)] => apply CarrierAr
    | _ => crush
    end.

  Fact Obligation_XXX:
    Included (FinNat 2) (Full_set (FinNat 2))
             (Union (FinNat 2) (singleton 1)
                    (Union (FinNat 2) (singleton 0) (Empty_set (FinNat 2)))).
  Proof.

    intros x H. unfold In in *.
    destruct x as [x xc].
    destruct x.
    -
      apply Union_intror.
      apply Union_introl.
      reflexivity.
    -
      destruct x.
      *
        apply Union_introl.
        reflexivity.
      *
        crush.
  Qed.

Instance DynWinSigmaHCOL1_Mem
         (a: avector 3):
  SHOperator_Mem (dynwin_SHCOL1 a) (facts := DynWinSigmaHCOL1_Facts a).
Proof.
  unfold dynwin_SHCOL1.

  Typeclasses eauto := 1.
  solve_mem.
  solve_facts.
  solve_facts.
  apply Disjoined_singletons; auto.
  apply Obligation_XXX.
  apply Disjoined_singletons; auto.
  {
    (* TODO: Automate Ensembles solving *)
    simpl.
    intros x H. unfold In in *.
    destruct x as [x xc].
    destruct x.
    apply Union_introl. unfold In, singleton. simpl. reflexivity.
    dep_destruct x.
    apply Union_intror. unfold In, singleton. simpl. reflexivity.
    crush.
  }
  solve_mem.
  solve_mem. (* eapply SHBinOp_RthetaSafe_Mem. *)
  solve_mem.
  solve_facts.
  solve_facts.
  apply Disjoined_singletons; auto.
  apply Obligation_XXX.
  {
    (* TODO: Automate Ensembles solving *)
    simpl.
    constructor.
    intros x.
    unfold In.
    intros H.
    inversion H.
    crush.
  }
  solve_mem.
  solve_facts.
  solve_facts.
  crush.
  solve_mem.
  solve_mem.
  solve_mem.
  solve_mem.
  solve_facts.
  solve_mem.
  unfold SHFamilyOperatorCompose.
  solve_mem.
  solve_facts.
  crush.
  solve_mem.
  solve_facts.
  solve_facts.
  crush.
  solve_mem.
  solve_mem.
  solve_mem.

  solve_mem.
  solve_mem.
  solve_mem.
  solve_facts.
  apply Disjoined_singletons; auto.
  apply Obligation_XXX.
  solve_mem.
  solve_mem.
  solve_mem.
  solve_mem.
  solve_facts.
  apply Disjoined_singletons; auto.
  apply Obligation_XXX.
  solve_mem.
  solve_mem.
  solve_facts.
  solve_facts.
  apply Disjoined_singletons; auto.
  apply Obligation_XXX.
  solve_mem.
  solve_mem.
  solve_mem.
  solve_mem.
  solve_facts.
  solve_mem.
  solve_mem.
  solve_facts.
  crush.
  solve_mem.
  solve_mem.
  {
    intros m mc n nc H.
    apply Disjoined_singletons, H.
  }
  crush.
  solve_mem.
Defined.


End SigmaHCOL_mem.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.ReifyDSHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import MathClasses.misc.util.

Section SigmaHCOL_to_DSHCOL.

  (* Obligation Tactic := solve_reifySHCOL_obligations dynwin_SHCOL1. *)
  Obligation Tactic := idtac.
  Run TemplateProgram (reifySHCOL dynwin_SHCOL1 "dynwin_DSHCOL1" "dynwin_SHCOL_DSHCOL").

  Print dynwin_DSHCOL1.
  Import DSHNotation.
  Print dynwin_DSHCOL1.

  (* Shows relations of cells before ([b]) and after ([a]) evaluating
     DSHCOL operator and a result of evaluating [mem_op] as [d] *)
  Inductive SHCOL_DSHCOL_cell_equiv (b a d: option CarrierA) : Prop :=
  | CellPreserve: is_None d -> b = a -> SHCOL_DSHCOL_cell_equiv b a d (* preserving memory state *)
  | CellExpected: is_Some d -> a = d -> SHCOL_DSHCOL_cell_equiv b a d (* expected results *).

  (* Shows relations of memory blocks before ([mb]) and after ([ma]) evaluating
     DSHCOL operator and a result of evaluating [mem_op] as [md] *)
  Definition SHCOL_DSHCOL_mem_block_equiv (mb ma md: mem_block) : Prop :=
    forall i,
      SHCOL_DSHCOL_cell_equiv
        (mem_lookup i mb)
        (mem_lookup i ma)
        (mem_lookup i md).


  (* Given SHCOL and DSHCOL operators are quivalent, if wrt [x_i] and
     input memory block addres and [y_i] as output.

     The [x_i] and [y_i] memory lookup must succeed.

     We do not require input block to be structurally correct, because
     [mem_op] will just return an error in this case.

     DSCHOL operators are implemented in more permissive manner
     and not necesseraly return error on invalid input.
   *)
  Class SHCOL_DSHCOL_equiv {i o:nat} {svalue:CarrierA} {fm}
        (sh_op: @SHOperator fm i o svalue)
        `{facts: !SHOperator_Facts fm sh_op}
        `{SHM: !SHOperator_Mem sh_op}
        (dsh_op: DSHOperator)
        (σ: evalContext)
        (m: memory)
        (x_i y_i: mem_block_id)
    := {
        eequiv:
          match memory_lookup m x_i, memory_lookup m y_i with
          | Some mx, (* input *) Some mb (* output before *) =>
            match mem_op mx, evalDSHOperator σ dsh_op m (estimateFuel dsh_op) with
            | None, _ => True (* assume they are equal on *invalid* inputs *)
            | Some md, (* memory diff *) Some m' (* memory state after execution *) =>
              match  memory_lookup m' y_i with
              | Some ma => SHCOL_DSHCOL_mem_block_equiv mb ma md
              | None => False (* out memory block dissapeared *)
              end
            | _, _ => False
            end
          | _, _ => False (* Either input our output not present *)
          end
      }.

  Instance SafeCast_SHCOL_DSHCOL
        {i o:nat} {svalue:CarrierA}
        {σ: evalContext}
        {s: @SHOperator Monoid_RthetaSafeFlags i o svalue}
        `{facts: !SHOperator_Facts _ s}
        `{mem: !SHOperator_Mem s}
        {d: DSHOperator}
        {m: memory}
        {x_i y_i: mem_block_id}:

    @SHCOL_DSHCOL_equiv i o svalue _ s facts mem d σ m x_i y_i ->

    @SHCOL_DSHCOL_equiv i o svalue _ (SafeCast s)
                        (@SafeCast_Facts _ _ _ s facts)
                        (SafeCast_Mem s)
                        d σ m x_i y_i .
  Proof.
    intros E.
    unfold SafeCast.
    constructor.
    destruct E as [E].
    unfold SafeCast', mem_op in *.
    destruct mem.
    eapply E.
  Qed.

  Instance SHCompose_SHCOL_DSHCOL
        {i1 o2 o3: nat}
        {svalue: CarrierA}
        {fm}
        {op1: @SHOperator fm o2 o3 svalue}
        {op2: @SHOperator fm i1 o2 svalue}
        {compat: Included _ (in_index_set fm op1) (out_index_set fm op2)}
        `{facts1 : !SHOperator_Facts fm op1}
        `{facts2 : !SHOperator_Facts fm op2}
        `{Meq1: !@SHOperator_Mem fm o2 o3 svalue op1 facts1}
        `{Meq2: !@SHOperator_Mem fm i1 o2 svalue op2 facts2}
        {σ: evalContext}
        {d1 d2: DSHOperator}
        {m: memory}
        {t_i x_i y_i: mem_block_id}
    :
      (@SHCOL_DSHCOL_equiv _ _ _ _ op1 facts1 Meq1 d1 σ (* TODO: add t_i to m *) m t_i y_i) ->
      (@SHCOL_DSHCOL_equiv _ _ _ _ op2 facts2 Meq2 d2 σ (* TODO: add t_i to m *) m x_i t_i) ->

      @SHCOL_DSHCOL_equiv i1 o3 svalue _ (SHCompose fm op1 op2)
                          (SHCompose_Facts fm svalue op1 op2 compat)
                          (SHCompose_Mem fm op1 op2 compat )
                          (DSHSeq (DSHAlloc o2 t_i) (DSHSeq d1 d2)) σ m x_i y_i.
  Proof.
    intros E1 E2.
    unfold SHCompose.
    constructor.
    destruct E1 as [E1].
    destruct E2 as [E2].
    unfold mem_op in *.
    unfold SHCompose_Mem, option_compose.
    destruct Meq1, Meq2.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    simpl in *.
    repeat break_match; intros; subst; auto.
  Admitted.

  (* High-level equivalence *)
  Instance dynwin_SHCOL_DSHCOL
           (a: vector CarrierA 3):
    @SHCOL_DSHCOL_equiv _ _ _ _ (dynwin_SHCOL1 a) _
                        (DynWinSigmaHCOL1_Mem a)
                        dynwin_DSHCOL1
                        [DSHvecVal a]
                        (* assuming reification uses [x_i=0] and [y_i=1] *)
                        (NM.add 1 mem_empty
                                (NM.add 0 mem_empty (NM.empty mem_block)))
                        0 1.
  Proof.
    unfold dynwin_DSHCOL1, dynwin_SHCOL1.
    unfold DynWinSigmaHCOL1_Mem, DynWinSigmaHCOL1_Facts.

    (* Normalize by unfolding [@zero] instances: *)
    unfold zero in *.
    (* Normalize dimensionality in DHSCOL. Due to refication,
       for example [o2:=1+1] in SHCOL is replaced with [2] in DHSCOL: *)
    (* simpl in *. *)


    Typeclasses eauto := 1.
    unfold In.
    eapply SHCompose_SHCOL_DSHCOL.
    eapply SafeCast_SHCOL_DSHCOL.


    match goal with
    | [|-  SHCOL_DSHCOL_equiv
            (facts:=?facts)
            (SHCompose ?fm ?op1 ?op2 (o2:=?o2))
            (DSHSeq (DSHAlloc ?o2 ?t_i) (DSHSeq ?d1 ?d2))
            ?σ ?m ?x_i ?y_i] =>
      unshelve eapply (SHCompose_SHCOL_DSHCOL 0 1
                                     (fm:=fm)
                                     (op1:=op1)
                                     (op2:=op2)
                                     (m:=m)
                                     (d1:=d1)
                                     (d2:=d2)
                                     (t_i:=t_i)
                                     (σ:=σ)
                                     (facts:=facts)

             )

    end.


    apply SafeCast_SHCOL_DSHCOL.
  Qed.



     "@SHCOL_DSHCOL_equiv (1 + (2 + 2)) 1 0 Monoid_RthetaFlags
    (?op1 ⊚ ?op2) ?facts
    (@SHCompose_Mem Monoid_RthetaFlags 0 (1 + (2 + 2)) ?o2 1
       ?op1 ?op2 ?compat ?facts1 ?Meq1 ?facts2 ?Meq2 ?facts)
    (DSHAlloc ?o2 ?t_i; ?d1; ?d2) [@DSHvecVal 3 a] ?m 0 1" with

    eapply (SHCompose_SHCOL_DSHCOL 0 1
                                   (i1:=1 + (2 + 2))
                                   (o3:=1)
                                   (svalue:=zero)
                                   (fm:=Monoid_RthetaFlags)
                                   (σ:=[DSHvecVal a])
           ).
    apply SafeCast_SHCOL_DSHCOL.
  Qed.

  (*
    Print dynwin_DSHCOL1.
    Check dynwin_SHCOL_DSHCOL.
   *)
End SigmaHCOL_to_DSHCOL.
