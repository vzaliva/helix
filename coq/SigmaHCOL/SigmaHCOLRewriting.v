Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.Util.VecSetoid.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.THCOL.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.Util.MonoidalRestriction.
Require Import Helix.Util.VecPermutation.
Require Import Helix.Util.FinNatSet.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Program.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.
Require Import Omega.

Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.setoids.

(* TODO: get rid of this
   Workaround for: https://github.com/coq/coq/issues/10583
   Some arith hints required for our proofs
 *)
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Module NM := FMapAVL.Make(Nat_as_OT).
(* --- end workaround *)

Require Import ExtLib.Structures.Monoid.
Import Monoid.

Import VectorNotations.

Local Open Scope vector_scope.
Local Open Scope nat_scope.

Section SigmaHCOLHelperLemmas.

  Variable svalue:CarrierA.

  (* UnSafeCast distributes over SHCompose *)
  Lemma UnSafeCast_SHCompose
        {i1 o2 o3: nat}
        (F: @SHOperator Monoid_RthetaFlags o2 o3 svalue)
        (G: @SHOperator Monoid_RthetaFlags i1 o2 svalue)
  :
    UnSafeCast (SHCompose Monoid_RthetaFlags F G)
    =
    (SHCompose Monoid_RthetaSafeFlags
               (UnSafeCast F)
               (UnSafeCast G)).
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, UnSafeCast, SHCompose.
    unfold UnSafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.
    f_equiv.
    unfold rsvector2rvector, rvector2rsvector.
    rewrite Vmap_map.

    setoid_replace (Vmap (λ x0 : Rtheta, RStheta2Rtheta (Rtheta2RStheta x0))
                         (op Monoid_RthetaFlags G (Vmap RStheta2Rtheta y))) with
        (op Monoid_RthetaFlags G (Vmap RStheta2Rtheta y)).
    -
      reflexivity.
    -
      vec_index_equiv j jc.
      rewrite Vnth_map.
      setoid_rewrite RStheta2Rtheta_Rtheta2RStheta_equiv.
      reflexivity.
  Qed.

  (* SafeCast distributes over SHCompose *)
  Lemma SafeCast_SHCompose
        {i1 o2 o3: nat}
        (F: @SHOperator _ o2 o3 svalue)
        (G: @SHOperator _ i1 o2 svalue)
  :
    SafeCast (SHCompose _ F G)
    =
    (SHCompose _
               (SafeCast F)
               (SafeCast G)).
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, SafeCast, SHCompose.
    unfold SafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.
    f_equiv.
    unfold rsvector2rvector, rvector2rsvector.
    rewrite Vmap_map.

    setoid_replace (Vmap (λ x0 : RStheta, Rtheta2RStheta (RStheta2Rtheta x0))
                         (op Monoid_RthetaSafeFlags G (Vmap Rtheta2RStheta y))) with
        (op Monoid_RthetaSafeFlags G (Vmap Rtheta2RStheta y)).

    -
      reflexivity.
    -
      vec_index_equiv j jc.
      rewrite Vnth_map.
      rewrite Rtheta2RStheta_RStheta2Rtheta.
      reflexivity.
  Qed.

  Lemma SafeCast_HReduction
        {i: nat}
        (f: CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
  :
    liftM_HOperator (svalue:=svalue) Monoid_RthetaFlags (HReduction (i:=i) f svalue) =
    SafeCast (liftM_HOperator Monoid_RthetaSafeFlags (HReduction f svalue)).
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, SafeCast.
    unfold SafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.
    vec_index_equiv j jc.
    unfold liftM_HOperator_impl, compose, sparsify, densify.
    rewrite Vnth_map.
    unfold HReduction, compose, HCOLImpl.Vectorize.

    rewrite 2!Vnth_1.
    clear x j jc.

    unfold RStheta2Rtheta.
    symmetry.
    apply castWriter_equiv with (fmx:=Monoid_RthetaSafeFlags).
    rewrite 2!evalWriter_mkValue.
    unfold rvector2rsvector.
    rewrite Vmap_map.
    reflexivity.
  Qed.

  Lemma SafeCast_SHBinOp
        (o: nat)
        (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    :
      SafeCast (@SHBinOp Monoid_RthetaSafeFlags svalue o f pF) =
      @SHBinOp Monoid_RthetaFlags svalue o f pF.
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, SafeCast.
    unfold SafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.

    vec_index_equiv j jc.
    unfold rsvector2rvector.
    rewrite Vnth_map.
    unfold rvector2rsvector.
    unfold_Rtheta_equiv.

    assert(jc1: j < o + o) by omega.
    assert(jc2: j + o < o + o) by omega.
    setoid_rewrite SHBinOp_impl_nth with (jc1:=jc1) (jc2:=jc2).

    rewrite 2!Vnth_map.
    f_equiv.

    unfold_Rtheta_equiv.
    rewrite evalWriter_Rtheta_liftM2.
    unfold RStheta2Rtheta, Rtheta2RStheta.
    rewrite WriterMonadNoT.evalWriter_castWriter.
    rewrite evalWriter_Rtheta_liftM2.
    repeat rewrite WriterMonadNoT.evalWriter_castWriter.
    reflexivity.
  Qed.

  Lemma SafeCast_liftM_HOperator
        {i o}
        (op: avector i -> avector o)
        `{HOP: HOperator i o op}
    :
      SafeCast (svalue:=svalue) (liftM_HOperator Monoid_RthetaSafeFlags op) =
      liftM_HOperator Monoid_RthetaFlags op.
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, SafeCast.
    unfold SafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.

    vec_index_equiv j jc.
    unfold rsvector2rvector.
    setoid_rewrite Vnth_map.
    unfold rvector2rsvector.
    unfold liftM_HOperator_impl.
    unfold sparsify, densify, compose.
    setoid_rewrite Vnth_map.
    rewrite Vmap_map.

    unfold RStheta2Rtheta.
    unfold_Rtheta_equiv.
    rewrite WriterMonadNoT.evalWriter_castWriter.
    reflexivity.
  Qed.

  Lemma SafeCast_SHPointwise
        {n: nat}
        (f: FinNat n -> CarrierA -> CarrierA)
        `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
  :
      SafeCast (@SHPointwise Monoid_RthetaSafeFlags svalue n f f_mor) =
      @SHPointwise Monoid_RthetaFlags svalue n f f_mor.
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, SafeCast.
    unfold SafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.

    vec_index_equiv j jc.
    unfold rsvector2rvector.
    setoid_rewrite Vnth_map.
    unfold rvector2rsvector.
    setoid_rewrite SHPointwise_impl_nth.
    unfold RStheta2Rtheta.
    unfold_Rtheta_equiv.
    rewrite WriterMonadNoT.evalWriter_castWriter.
    setoid_rewrite Vnth_map.
    unfold Rtheta2RStheta.
    rewrite WriterMonadNoT.evalWriter_castWriter.
    reflexivity.
  Qed.

  Lemma UnSafeCast_Gather
        {i o: nat}
        (f: index_map o i)
    :
      UnSafeCast (svalue:=svalue) (Gather Monoid_RthetaFlags f)
      =
      Gather Monoid_RthetaSafeFlags f.
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, UnSafeCast.
    unfold UnSafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.

    vec_index_equiv j jc.
    unfold rvector2rsvector.
    rewrite Vnth_map.
    unfold rsvector2rvector.
    unfold_Rtheta_equiv.
    setoid_rewrite Gather_impl_spec.
    unfold VnthIndexMapped.
    rewrite Vnth_map.
    f_equiv.
    setoid_rewrite Rtheta2RStheta_RStheta2Rtheta.
    reflexivity.
  Qed.

  Lemma SafeCast_GathH
        {i o}
        (base stride: nat)
        {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
  :
      SafeCast (@GathH Monoid_RthetaSafeFlags svalue i o base stride domain_bound) =
      @GathH Monoid_RthetaFlags svalue i o base stride domain_bound.
  Proof.
    unfold_RStheta_equiv.
    unfold SHOperator_equiv, SafeCast.
    unfold SafeCast', compose.
    simpl.
    intros x y E.
    rewrite_clear E.

    vec_index_equiv j jc.
    unfold rsvector2rvector.
    rewrite Vnth_map.
    unfold rvector2rsvector.
    unfold_Rtheta_equiv.
    setoid_rewrite Gather_impl_spec.
    unfold VnthIndexMapped.
    rewrite Vnth_map.
    f_equiv.
    setoid_rewrite RStheta2Rtheta_Rtheta2RStheta.
    reflexivity.
  Qed.

  Section WithMonoid.

    Variable fm:Monoid RthetaFlags.

    Lemma Gather_impl_composition
          {i o t: nat}
          (f: index_map o t)
          (g: index_map t i):
      Gather_impl (fm:=fm) f ∘ Gather_impl g = Gather_impl (index_map_compose g f).
    Proof.
      apply ext_equiv_applied_equiv.
      -
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv);
          apply Gather_impl_proper; reflexivity.
      -
        split; try apply vec_Setoid.
        apply Gather_impl_proper; reflexivity.
      -
        intros v.
        unfold compose.
        vec_index_equiv j jp.

        unfold Gather_impl.
        rewrite 2!Vbuild_nth.
        unfold VnthIndexMapped.
        destruct f as [f fspec].
        destruct g as [g gspec].
        unfold index_map_compose, compose.
        simpl.
        rewrite Vbuild_nth.
        reflexivity.
    Qed.

    Lemma Scatter_impl_composition
          {i o t: nat}
          (f: index_map i t)
          (g: index_map t o)
          {f_inj: index_map_injective f}
          {g_inj: index_map_injective g}
          (idv: CarrierA):
      @Scatter_impl fm _ _ g g_inj idv ∘ @Scatter_impl fm _ _ f f_inj idv
      = @Scatter_impl fm _ _ (index_map_compose g f) (index_map_compose_injective g f g_inj f_inj) idv.
    Proof.
      apply ext_equiv_applied_equiv.
      -
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv);
          apply Scatter_impl_proper; reflexivity.
      -
        split; try apply vec_Setoid.
        apply Scatter_impl_proper; reflexivity.
      -
        intros v.
        unfold compose.
        vec_index_equiv j jp.
        unfold Scatter_impl.
        rewrite 2!Vbuild_nth.
        break_match.
        + rewrite Vbuild_nth.
          simpl in *.
          break_match.
          *
            break_match.
            apply VecSetoid.Vnth_equiv.
            -- apply composition_of_inverses_to_invese_of_compositions; assumption.
            -- reflexivity.
            -- (* i1 contradicts n *)
              contradict n.
              apply in_range_index_map_compose; try assumption.
          * break_match.
            --
              contradict n.
              apply in_range_index_map_compose_right; try assumption.
            -- reflexivity.
        +
          simpl.
          break_match.
          contradict n.
          apply in_range_index_map_compose_left in i0; try assumption.
          reflexivity.
    Qed.

    Lemma LiftM_Hoperator_compose
          {i1 o2 o3: nat}
          `{HOperator o2 o3 op1}
          `{HOperator i1 o2 op2}
      :
        liftM_HOperator (svalue:=svalue) fm (op1 ∘ op2) =
        SHCompose fm
                  (liftM_HOperator fm op1)
                  (liftM_HOperator fm op2).
    Proof.
      unfold equiv, SHOperator_equiv; simpl.
      apply ext_equiv_applied_equiv.
      -
        split.
        + apply vec_Setoid.
        + apply vec_Setoid.
        + apply liftM_HOperator_impl_proper.
          apply compose_HOperator.
      -
        split.
        + apply vec_Setoid.
        + apply vec_Setoid.
        + apply compose_proper with (RA:=equiv) (RB:=equiv).
          apply liftM_HOperator_impl_proper; assumption.
          apply liftM_HOperator_impl_proper; assumption.
      -
        intros v.
        unfold liftM_HOperator_impl, compose.
        unfold sparsify, densify.
        rewrite Vmap_map.

        vec_index_equiv i ip.
        repeat rewrite Vnth_map.
        f_equiv.
        apply VecSetoid.Vnth_arg_equiv.
        f_equiv.
        vec_index_equiv i0 ip0.
        repeat rewrite Vnth_map.
        f_equiv.
    Qed.

    Fact snzord0_1_1_2: (1 ≢ 0 ∨ (1 < 2))%nat.
    Proof.
      auto.
    Qed.

    Fact ScatH_stride1_constr:
    forall {a b:nat}, 1 ≢ 0 ∨ a < b.
    Proof.
      auto.
    Qed.

    Fact h_bound_first_half (o1 o2:nat):
      ∀ x : nat, x < o1 → 0 + x * 1 < o1 + o2.
    Proof.
      intros.
      lia.
    Qed.

    Fact h_bound_second_half (o1 o2:nat):
      ∀ x : nat, x < o2 → o1 + x * 1 < o1 + o2.
    Proof.
      intros.
      lia.
    Qed.

    Fact ScatH_1_to_n_range_bound base o stride:
      base < o ->
      ∀ x : nat, x < 1 → base + x * stride < o.
    Proof.
      intros.
      nia.
    Qed.

    Fact GathH_j1_domain_bound base i (bc:base<i):
      ∀ x : nat, x < 1 → base + x * 1 < i.
    Proof.
      intros.
      lia.
    Qed.

    Lemma UnionFold_a_zero_structs
          (m : nat)
          (x : svector fm m)
          `{uf_zero: MonUnit CarrierA}
          `{f: SgOp CarrierA}
          `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
          `{f_left_id : @LeftIdentity CarrierA CarrierA CarrierAe
                                      (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}
      :
        Vforall (Is_ValX uf_zero) x → Is_ValX uf_zero (UnionFold fm f uf_zero x).
    Proof.
      intros H.
      unfold UnionFold.
      induction x.
      -
        unfold Is_ValX.
        unfold_Rtheta_equiv.
        reflexivity.
      - simpl in H. destruct H as [Hh Hx].
        Opaque Monad.ret. simpl. Transparent Monad.ret.

        unfold Is_ValX.
        decide_CarrierA_equality E NE.
        +
          auto.
        +
          unfold Is_ValX in Hh.
          rewrite evalWriterUnion in NE.
          rewrite <- Hh in NE.
          specialize (IHx Hx).
          unfold Is_ValX in IHx.
          contradict NE.
          rewrite Hh.
          rewrite IHx.
          apply f_left_id.
    Qed.

    (* Specialized version of [UnionFold_a_zero_structs]. *)
    Lemma UnionFold_zero_structs
          (m : nat) (x : svector fm m):
      Vforall Is_ValZero x → Is_ValZero (UnionFold fm plus zero x).
    Proof.
      apply UnionFold_a_zero_structs; typeclasses eauto.
    Qed.

    Fact Is_ValX_not_not'
         `{uf_zero: MonUnit CarrierA}:
      (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) = Is_ValX uf_zero.
    Proof.
      unfold Is_ValX.
      unfold compose, equiv, ext_equiv.
      simpl_relation.
      rewrite_clear H.
      unfold MonUnit.
      generalize dependent (@WriterMonadNoT.evalWriter RthetaFlags CarrierA fm y).
      intros c.
      destruct (CarrierAequivdec uf_zero c) as [E|NE]; crush.
    Qed.

    Lemma UnionFold_VallButOne_a_zero
          {n : nat}
          (v : svector fm n)
          {i : nat}
          (ic : i < n)

          `{uf_zero: MonUnit CarrierA}
          `{f: SgOp CarrierA}
          `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
          `{f_left_id : @LeftIdentity CarrierA CarrierA CarrierAe
                                      (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}
          `{f_right_id : @RightIdentity CarrierA CarrierAe CarrierA
                                        (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}
      :
        VAllButOne i ic
                   (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) v -> UnionFold fm f uf_zero v = Vnth v ic.
    Proof.
      intros U.
      dependent induction n.
      - crush.
      -
        dep_destruct v.
        destruct (eq_nat_dec i 0).
        +
          (* Case ("i=0"). *)
          rewrite Vnth_cons_head by assumption.
          rewrite UnionFold_cons.

          assert(H: Vforall (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) x).
          {
            apply Vforall_nth_intro.
            intros j jp.
            assert(ipp:S j < S n) by lia.
            unfold MonUnit in *.
            unfold Rtheta',Monad_RthetaFlags,WriterMonadNoT.writer in x.
            replace (Vnth x jp) with (Vnth (Vcons h x) ipp) by apply Vnth_Sn.
            apply U.
            omega.
          }

          assert(UZ: Is_ValX uf_zero (UnionFold fm f uf_zero x)).
          {
            apply UnionFold_a_zero_structs.
            apply f_mor.
            apply f_left_id.

            (* Roundabout way to do:  [rewrite <- Is_ValX_not_not ; apply H.]. We have to do this because we do not have Vforal Proper morphism proven *)
            rewrite Vforall_eq.
            rewrite Vforall_eq in H.
            intros x0 H0.
            apply (Is_ValX_not_not' x0); auto.
          }

          unfold_Rtheta_equiv.
          rewrite evalWriterUnion.
          unfold Is_ValX in UZ.
          setoid_replace (WriterMonadNoT.evalWriter (UnionFold fm f uf_zero x)) with uf_zero by apply UZ.
          apply f_left_id.
        +
          (* Case ("i!=0"). *)
          rewrite UnionFold_cons.
          assert (HS: Is_ValX uf_zero h).
          {
            cut (Is_ValX uf_zero (Vnth (Vcons h x) (zero_lt_Sn n))).
            rewrite Vnth_0.
            auto.
            unfold VAllButOne in U.
            assert(jc: 0 < S n) by omega.
            specialize (U 0 jc n0).
            apply not_not_on_decidable.
            unfold Is_ValX.
            typeclasses eauto.
            setoid_replace (λ x0 : Rtheta' fm, WriterMonadNoT.evalWriter x0 = uf_zero)
              with (equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm)).
            * apply U.
            *
              unfold compose.
              apply ext_equiv_applied_equiv.
              split; try typeclasses eauto.
              solve_proper.
              split; try typeclasses eauto.
              intros x0.

              unfold equiv.
              unfold Equiv_instance_0.
              split; intros H; symmetry; apply H.
          }

          destruct i; try congruence.
          simpl.
          generalize (lt_S_n ic).
          intros l.
          rewrite IHn with (ic:=l); try typeclasses eauto.
          *
            unfold_Rtheta_equiv.
            rewrite evalWriterUnion.
            unfold Is_ValX in HS.
            rewrite HS.
            apply f_right_id.
          *
            apply VAllButOne_Sn with (h0:=h) (ic0:=ic).
            apply U.
    Qed.


    (* Specialized version of [UnionFold_VallButOne_a_zero]. *)
    Lemma UnionFold_VallButOne_zero:
      ∀ {n : nat} (v : svector fm n) {k : nat} (kc : k < n),
        VAllButOne k kc (Is_ValZero) v → UnionFold fm plus zero v = Vnth v kc.
    Proof.
      intros n v i ic U.
      apply UnionFold_VallButOne_a_zero; try typeclasses eauto.
      unfold VAllButOne in *.
      intros j jc H.
      specialize (U j jc H).
      unfold MonUnit.
      unfold Rtheta', Monad_RthetaFlags, WriterMonadNoT.writer in U.
      generalize dependent (@Vnth (@WriterMonad.writerT RthetaFlags fm IdentityMonad.ident CarrierA) n v j jc).
      unfold compose, Is_ValZero.
      intros w.
      unfold Is_ValX.
      auto.
    Qed.


    (* Formerly Lemma3. Probably will be replaced by UnionFold_VallButOne *)
    Lemma SingleValueInZeros
          {m} (x:svector fm m) j (jc:j<m):
      (forall i (ic:i<m), i ≢ j -> Is_ValZero (Vnth x ic)) -> (UnionFold fm plus zero x = Vnth x jc).
    Proof.
      intros SZ.
      dependent induction m.
      - dep_destruct x.
        destruct j; omega.
      -
        dep_destruct x.
        destruct (eq_nat_dec j 0).
        +
          (* Case ("j=0"). *)
          rewrite Vnth_cons_head; try assumption.
          rewrite UnionFold_cons.
          assert(Vforall Is_ValZero x0).
          {
            apply Vforall_nth_intro.
            intros.
            assert(ipp:S i < S m) by lia.
            replace (Vnth x0 ip) with (Vnth (Vcons h x0) ipp) by apply Vnth_Sn.
            apply SZ; lia.
          }

          assert(UZ: Is_ValZero (UnionFold fm plus zero x0))
            by apply UnionFold_zero_structs, H.
          setoid_replace (UnionFold fm plus zero x0) with (@mkSZero fm)
            by apply Is_ValZero_to_mkSZero, UZ.
          clear UZ.
          apply Union_SZero_l.
        +
          (* Case ("j!=0"). *)
          rewrite UnionFold_cons.
          assert(Zc: 0<(S m)) by lia.

          assert (HS: Is_ValZero h).
          {
            cut (Is_ValZero (Vnth (Vcons h x0) Zc)).
            rewrite Vnth_0.
            auto.
            apply SZ; auto.
          }

          destruct j; try congruence.
          simpl.
          generalize (lt_S_n jc).
          intros l.
          rewrite IHm with (jc:=l).

          setoid_replace h with (@mkSZero fm) by apply Is_ValZero_to_mkSZero, HS.
          apply Union_SZero_r.

          intros i ic.
          assert(ics: S i < S m) by lia.
          rewrite <- Vnth_Sn with (v:=h) (ip:=ics).
          specialize SZ with (i:=S i) (ic:=ics).
          auto.
    Qed.


    Fact GathH_jn_domain_bound i n:
      i < n ->
      ∀ x : nat, x < 2 → i + x * n < (n+n).
    Proof.
      intros.
      nia.
    Qed.

    Lemma UnSafeCast_SHBinOp
          (o:nat)
          (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      :
        UnSafeCast (@SHBinOp _ svalue o f pF) =
        @SHBinOp _ svalue o f pF.
    Proof.
      unfold_RStheta_equiv.
      unfold SHOperator_equiv, UnSafeCast.
      unfold UnSafeCast', compose.
      simpl.
      intros x y E.
      rewrite_clear E.

      vec_index_equiv j jc.
      unfold rvector2rsvector.
      rewrite Vnth_map.
      unfold rsvector2rvector.
      unfold_Rtheta_equiv.

      assert(jc1: j < o + o) by omega.
      assert(jc2: j + o < o + o) by omega.
      setoid_rewrite SHBinOp_impl_nth with (jc1:=jc1) (jc2:=jc2).

      rewrite 2!Vnth_map.
      f_equiv.

      unfold_RStheta_equiv.
      rewrite evalWriter_Rtheta_liftM2.
      unfold RStheta2Rtheta, Rtheta2RStheta.
      rewrite WriterMonadNoT.evalWriter_castWriter.
      rewrite evalWriter_Rtheta_liftM2.
      repeat rewrite WriterMonadNoT.evalWriter_castWriter.
      reflexivity.
    Qed.

    Fact GathH_fold
         {i o base stride: nat}
         {domain_bound: forall x : nat, (x < i) -> (base + x * stride < o)}
      :
        Gather (svalue:=svalue) fm (@h_index_map i o base stride domain_bound)
               ≡
               GathH fm base stride (domain_bound:=domain_bound).
    Proof.
      auto.
    Qed.

  End WithMonoid.

End SigmaHCOLHelperLemmas.

Section SigmaHCOLExpansionRules.

  Variable svalue:CarrierA.

  Section Value_Correctness.

    Lemma SHInductor_equiv_lifted_HInductor
          {fm}
          {n: nat}
          {initial: CarrierA}
          {f: CarrierA -> CarrierA -> CarrierA}
          `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    :
      SHInductor (svalue:=svalue) fm n f initial = liftM_HOperator fm (HInductor n f initial).
    Proof.
      apply SHOperator_ext_equiv_applied.
      intros v.
      simpl.
      destruct n.
      -
        reflexivity.
      -
        unfold SHInductor_impl.
        unfold liftM_HOperator_impl, compose.
        unfold sparsify, HInductor, compose, Lst.
        simpl Vmap.
        apply Vcons_proper. 2:reflexivity.
        unfold_Rtheta_equiv.
        rewrite evalWriter_Rtheta_liftM.
        rewrite evalWriter_mkValue.
        unfold HCOLImpl.Scalarize, densify.
        rewrite Vhead_Vmap.
        reflexivity.
    Qed.

    Lemma SHBinOp_equiv_lifted_HBinOp
          {o}
          (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    :
      SafeCast (@SHBinOp _ svalue o f pF) = @liftM_HOperator Monoid_RthetaFlags (o+o) o svalue (@HBinOp o f) _ .
    Proof.
      apply ext_equiv_applied_equiv.
      -
        simpl.
        split.
        + apply vec_Setoid.
        + apply vec_Setoid.
        + apply SafeCast'_proper, SHBinOp_impl_proper, pF.
      -
        simpl.
        split.
        + apply vec_Setoid.
        + apply vec_Setoid.
        + apply liftM_HOperator_impl_proper.
          apply HBinOp_HOperator.
          apply pF.
      -
        intros x.
        simpl.

        vec_index_equiv j jc.

        unfold SafeCast', rsvector2rvector, rvector2rsvector, compose.
        rewrite Vnth_map.


        assert(jc1: j<o+o) by omega.
        assert(jc2: j+o<o+o) by omega.
        rewrite SHBinOp_impl_nth with (fm:=Monoid_RthetaSafeFlags)
                                  (jc1:=jc1) (jc2:=jc2).


        unfold liftM_HOperator_impl.
        unfold compose.
        unfold sparsify.
        repeat rewrite Vnth_map.
        rewrite (@HBinOp_nth o f _ j jc jc1 jc2).
        unfold densify; rewrite 2!Vnth_map.

        rewrite <- evalWriter_Rtheta_liftM2 by apply fml.
        rewrite mkValue_evalWriter.
        apply RStheta2Rtheta_liftM2.
        apply pF.
        reflexivity.
    Qed.

    Lemma h_j_1_family_injective {n}:
      index_map_family_injective
        (fun j => h_index_map (proj1_sig j) 1 (range_bound := (ScatH_1_to_n_range_bound (proj1_sig j) n 1 (proj2_sig j)))).
    Proof.
      unfold index_map_family_injective.
      crush.
    Qed.

    Lemma U_SAG2:
      ∀ (n : nat) (x : rvector (n + n))
        (f: FinNat n -> CarrierA -> CarrierA -> CarrierA)
        `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (k : nat) (kp : k < n),

        Vnth
          (SumUnion Monoid_RthetaFlags
                    (Vbuild
                       (λ (j : nat) (jc : j < n),
                        @Scatter_impl Monoid_RthetaFlags 1 _
                                 (h_index_map j 1 (range_bound:=ScatH_1_to_n_range_bound j n 1 jc))
                                 (@index_map_family_member_injective 1 n n
                                          (fun j0 => @h_index_map 1 n (proj1_sig j0) 1
                                                                                                             (ScatH_1_to_n_range_bound (proj1_sig j0) n 1 (proj2_sig j0))) (@h_j_1_family_injective n) (mkFinNat jc)) zero
                                 (SafeCast' (@SHBinOp_impl Monoid_RthetaSafeFlags 1 (Fin1SwapIndex2 (mkFinNat jc) f))
                                            (Gather_impl (@h_index_map (1+1) (n+n) j n (GathH_jn_domain_bound j n jc)) x)))
          )) kp
        = Vnth ((@SHBinOp_impl _ n f) x) kp.
    Proof.
      intros n x f f_mor k kp.

      remember (fun i jc => Scatter_impl _ _) as bf.


      (* Lemma5 embedded below*)
      rewrite AbsorbSumUnionIndex_Vmap by solve_proper.
      rewrite Vmap_Vbuild.

      (* Preparing to apply Lemma3. Prove some peoperties first. *)
      remember (Vbuild  _ ) as b.

      assert
        (L3pre: forall ib (icb:ib<n),
            ib ≢ k -> Is_ValZero (Vnth b icb)).
      {
        intros ib icb.
        subst.
        rewrite Vbuild_nth.
        unfold Scatter_impl.
        rewrite Vbuild_nth; intros H.
        break_match.
        - unfold h_index_map in i.
          simpl in i.
          destruct (Nat.eq_dec ib 0).
          +  subst.
             simpl in i.
             break_match.
             congruence.
             crush.
          +

            generalize (@inverse_index_f_spec (S O) n
                                              (@h_index_map (S O) n ib (S O) (ScatH_1_to_n_range_bound ib n (S O) icb))
                                              (@build_inverse_index_map (S O) n
                                                                        (@h_index_map (S O) n ib (S O) (ScatH_1_to_n_range_bound ib n (S O) icb))) k
                                              i) as l.
            intros l.
            break_if.
            rewrite <- plus_n_O in e.
            congruence.
            simpl in *.
            crush.
        - apply SZero_is_ValZero.
      }
      rewrite SingleValueInZeros with (j:=k) (jc:=kp).
      -  subst b.
         rewrite Vbuild_nth.
         subst bf.
         unfold Scatter_impl.
         rewrite Vbuild_nth.
         break_match.
         +
           clear L3pre.

           unfold SafeCast', rsvector2rvector, rvector2rsvector, compose.
           rewrite Vnth_map.

           unshelve erewrite SHBinOp_impl_nth with (fm:=Monoid_RthetaSafeFlags).
           crush.
           destruct (Nat.eq_dec (k + 0) k).
           auto.
           tauto.

           crush.
           destruct (Nat.eq_dec (k + 0) k).
           auto.
           tauto.

           rewrite 2!Vnth_map.
           unshelve erewrite SHBinOp_impl_nth.
           crush.
           crush.


           rewrite 2!Gather_impl_spec with (fm:=Monoid_RthetaFlags).
           unfold VnthIndexMapped.

           unfold inverse_index_f, build_inverse_index_map, const.
           unfold h_index_map.

           Opaque Rtheta2RStheta Monad.liftM2.
           simpl.


           generalize (lt_plus_trans k n n kp) as kc1.
           generalize (Plus.plus_lt_compat_r k n n kp) as kc2.
           intros kc2 kc1.

           rewrite Vnth_cast_index with (j:=k) (jc:=kc1).
           setoid_rewrite Vnth_cast_index with (j:=k+n) (jc:=kc2) at 2.

           apply RStheta2Rtheta_liftM2.
           solve_proper.

           break_if; crush.
           break_if; crush.
         +
           unfold in_range in n0.
           simpl in n0.
           break_if; crush.
      -
        apply L3pre.
    Qed.


    (*
    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N),
        ISumUnion(i, i.range, OLCompose(
        ScatHUnion(o.N, 1, i, 1),
        BinOp(1, o.op),
        GathH(2*o.N, 2, i, o.N)
        )))),
     *)
    Theorem expand_BinOp
            (n:nat)
            (f: FinNat n -> CarrierA -> CarrierA -> CarrierA)
            `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      :
        SafeCast (SHBinOp _ f)
        =
        SumSparseEmbedding (f_inj:=h_j_1_family_injective)
                         (fun jf => SafeCast (SHBinOp _ (Fin1SwapIndex2 jf f)))
                         (fun j => h_index_map (proj1_sig j) 1 (range_bound := (ScatH_1_to_n_range_bound (proj1_sig j) n 1 (proj2_sig j))))
                         (fun j => h_index_map (proj1_sig j) n (range_bound:=GathH_jn_domain_bound (proj1_sig j) n (proj2_sig j))).
    Proof.
      apply SHOperator_ext_equiv_applied.
      -
        simpl.
        intros x.
        vec_index_equiv i ip.

        unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
        rewrite Vnth_map.

        assert(ip1: i<n+n) by omega.
        assert(ip2: (i+n) < (n+n)) by omega.
        setoid_rewrite SHBinOp_impl_nth with (jc1:=ip1) (jc2:=ip2).


        unfold Diamond.
        rewrite AbsorbMUnionIndex_Vmap.
        (* OR rewrite AbsorbMUnionIndex_Vbuild.*)
        unfold Apply_Family'.
        rewrite Vmap_Vbuild.

        (* Not sure below here *)
        unfold SparseEmbedding, Diamond, Apply_Family', MUnion.
        unfold SHCompose, compose, get_family_op.
        simpl.

        rewrite <- AbsorbISumUnionIndex_Vbuild.

        setoid_rewrite U_SAG2.
        setoid_rewrite SHBinOp_impl_nth with (jc:=ip) (jc1:=ip1) (jc2:=ip2).

        repeat rewrite Vnth_map.
        apply RStheta2Rtheta_liftM2.
        apply f_mor.
        reflexivity.
        apply f_mor.
    Qed.


    (*
   ApplyFunc(SUMUnion, List([1..Length(ch)], i->OLCompose(
            ScatHUnion(Rows(o), Rows(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[1])), 1),
            self(ch[i], opts),
            GathH(Cols(o), Cols(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[2])), 1))))),
     *)
    (* This could be generalized for `Monoid (plus, zero)` *)
    Theorem expand_HTDirectSum
            {fm: Monoid RthetaFlags}
            {fml: @MonoidLaws RthetaFlags fm}
            {i1 o1 i2 o2}
            (f: avector i1 -> avector o1)
            (g: avector i2 -> avector o2)
            `{hop1: !HOperator f}
            `{hop2: !HOperator g}
      :
        liftM_HOperator fm (svalue:=zero) (HTDirectSum f g)
        =
        HTSUMUnion
          _
          plus
          (SHCompose fm
                     (ScatH fm 0 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_first_half o1 o2))
                     (SHCompose fm
                                (liftM_HOperator fm f)
                                (GathH fm 0 1 (domain_bound := h_bound_first_half i1 i2))))

          (SHCompose fm
                     (ScatH fm o1 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_second_half o1 o2))
                     (SHCompose fm
                                (liftM_HOperator fm g)
                                (GathH fm i1 1 (domain_bound := h_bound_second_half i1 i2)))).
    Proof.
      unfold equiv, SHOperator_equiv.
      simpl.
      eapply ext_equiv_applied_equiv.
      -
        split; try apply vec_Setoid.
        solve_proper.
      -
        split; try apply vec_Setoid.
        apply HTSUMUnion'_proper.
        solve_proper.
        +
          apply ext_equiv_applied_equiv.

          split; try apply vec_Setoid.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          solve_proper.

          split; try apply vec_Setoid.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          solve_proper.
          intros.
          reflexivity.
        +
          apply ext_equiv_applied_equiv.

          split; try apply vec_Setoid.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          solve_proper.

          split; try apply vec_Setoid.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          solve_proper.
          solve_proper.
          intros.
          reflexivity.
      -
        intros x.
        unfold liftM_HOperator_impl at 1.
        unfold compose.
        unfold HTDirectSum, HCross, THCOLImpl.Cross, compose,
        HTSUMUnion', pair2vector.

        break_let. break_let.
        rename t1 into x0, t2 into x1.
        tuple_inversion.
        symmetry.

        assert(LS: (@Scatter_impl fm o1 (Init.Nat.add o1 o2)
                              (@h_index_map o1 (Init.Nat.add o1 o2) O (S O) (h_bound_first_half o1 o2))
                              (@h_index_map_is_injective o1 (Init.Nat.add o1 o2) O
                                                         (S O) (h_bound_first_half o1 o2) (@ScatH_stride1_constr o1 (S (S O))))
                              zero
                              (@liftM_HOperator_impl fm i1 o1 f
                                                 (@Gather_impl fm (Init.Nat.add i1 i2) i1
                                                           (@h_index_map i1 (Init.Nat.add i1 i2) O (S O) (h_bound_first_half i1 i2))
                                                           x))) = Vapp (sparsify fm (f x0)) (szero_svector fm o2)).
        {
          setoid_replace (@Gather_impl fm (Init.Nat.add i1 i2) i1
                                   (@h_index_map i1 (Init.Nat.add i1 i2) O (S O) (h_bound_first_half i1 i2))
                                   x) with (sparsify fm x0).
          -
            vec_index_equiv i ip.
            unfold Scatter_impl.
            rewrite Vbuild_nth.

            unfold sparsify.
            rewrite Vnth_app.

            destruct(le_gt_dec o1 i).
            + (* Second half of x, which is all zeros *)
              unfold szero_svector.
              rewrite Vnth_const.
              break_match.
              *
                (* get rid of it to be able manipulate dependent hypothesis i0 *)
                exfalso.
                apply in_range_of_h in i0.
                crush.
                rewrite <- H in l.
                omega.
                apply ip.
              * reflexivity.
            + (* First half of x, which is fx0 *)
              rewrite Vnth_map.
              break_match.
              * simpl.
                unfold liftM_HOperator_impl, sparsify, compose.
                rewrite Vnth_map.
                unfold densify.
                rewrite Vmap_map.
                unfold mkValue, WriterMonadNoT.evalWriter.
                unfold equiv, Rtheta'_equiv.
                unfold WriterMonadNoT.evalWriter, compose, WriterMonadNoT.runWriter.
                simpl.

                replace (Vmap (λ x2 : CarrierA, x2) x0) with x0
                  by (symmetry; apply Vmap_id).

                replace (Vnth
                           (f x0)
                           (gen_inverse_index_f_spec
                              (h_index_map 0 1) i i0)) with
                    (Vnth (f x0) g0).

                reflexivity.
                generalize (f x0) as fx0. intros fx0.
                apply Vnth_eq.
                symmetry.

                apply build_inverse_index_map_is_left_inverse; try assumption.
                apply h_index_map_is_injective; left; auto.

                unfold h_index_map.
                simpl.
                rewrite Nat.mul_comm, Nat.mul_1_l.
                reflexivity.
              * contradict n.
                apply in_range_of_h.
                apply ip.
                exists i, g0.
                simpl.
                rewrite Nat.mul_comm, Nat.mul_1_l.
                reflexivity.
          -
            unfold Gather_impl.
            vec_index_equiv i ip.

            rewrite Vnth_sparsify.
            rewrite Vbuild_nth.

            unfold h_index_map.
            unfold VnthIndexMapped.
            simpl.

            rename Heqp0 into H.
            apply Vbreak_arg_app in H.
            assert(ip1: S i <= i1 + i2) by omega.
            apply Vnth_arg_eq with (ip:=ip1) in H.
            rewrite Vnth_app in H.
            break_match.
            crush.
            replace g0 with ip in H.
            rewrite <- H.
            clear H g0.
            unfold densify.
            rewrite Vnth_map.
            rewrite mkValue_evalWriter.
            apply Vnth_equiv.
            rewrite Mult.mult_1_r; reflexivity.
            reflexivity.
            apply le_unique.
        }

        assert(RS: (@Scatter_impl fm o2 (Init.Nat.add o1 o2)
                              (@h_index_map o2 (Init.Nat.add o1 o2) o1 (S O) (h_bound_second_half o1 o2))
                              (@h_index_map_is_injective o2 (Init.Nat.add o1 o2) o1
                                                         (S O) (h_bound_second_half o1 o2) (@ScatH_stride1_constr o2 (S (S O))))
                              zero
                              (@liftM_HOperator_impl fm i2 o2 g
                                                 (@Gather_impl fm (Init.Nat.add i1 i2) i2
                                                           (@h_index_map i2 (Init.Nat.add i1 i2) i1 (S O)
                                                                         (h_bound_second_half i1 i2)) x))) = Vapp (szero_svector fm o1) (sparsify fm (g x1))).
        {
          setoid_replace (@Gather_impl fm (Init.Nat.add i1 i2) i2
                                   (@h_index_map i2 (Init.Nat.add i1 i2) i1 (S O)
                                                 (h_bound_second_half i1 i2)) x) with (sparsify fm x1).
          -
            unfold Scatter_impl.
            vec_index_equiv i ip.
            rewrite Vbuild_nth.
            rewrite Vnth_app.
            break_match.
            + (* Second half of x, which is gx0 *)
              break_match.
              * simpl.
                unfold liftM_HOperator_impl, sparsify, compose.
                rewrite 2!Vnth_map.
                unfold densify.
                rewrite Vmap_map.
                unfold mkValue, WriterMonadNoT.evalWriter.
                unfold equiv, Rtheta'_equiv.
                unfold WriterMonadNoT.evalWriter, compose, WriterMonadNoT.runWriter.
                simpl.

                replace (Vmap (λ x2 : CarrierA, x2) x1) with x1
                  by (symmetry; apply Vmap_id).
                replace (Vnth
                           (g x1)
                           (gen_inverse_index_f_spec
                              (h_index_map o1 1) i i0)) with
                    (Vnth
                       (g x1) (Vnth_app_aux o2 ip l)).
                reflexivity.
                generalize (g x1) as gx1. intros gx1.
                apply Vnth_eq.
                symmetry.

                apply build_inverse_index_map_is_left_inverse; try assumption.
                apply h_index_map_is_injective; left; auto.
                lia.

                unfold h_index_map.
                simpl.
                lia.
              *
                exfalso.
                rewrite in_range_of_h in i0.
                destruct i0 as [z H].
                destruct H as [zc H].
                rewrite Nat.mul_1_r in H.
                rewrite <- H in g0.
                crush.
                apply ip.
            + (* First half of x, which is all zeros *)
              unfold szero_svector.
              break_match.
              *
                contradict n.
                apply in_range_of_h.
                apply ip.
                exists (i-o1).
                assert (oc: i - o1 < o2) by crush.
                exists oc.
                replace (o1 + (i - o1) * 1) with i by omega.
                reflexivity.
              *
                rewrite Vnth_const.
                reflexivity.
          - unfold Gather_impl.
            vec_index_equiv i ip.
            rewrite Vbuild_nth.
            unfold h_index_map.
            unfold VnthIndexMapped.
            simpl.

            rename Heqp0 into H.
            apply Vbreak_arg_app in H.
            unfold sparsify.
            rewrite Vnth_map.

            assert(ip1: i+i1 < i1 + i2) by omega.
            apply Vnth_arg_eq with (i:=i+i1) (ip:=ip1) in H.
            unfold densify in H.
            rewrite Vnth_map in H.
            rewrite Vnth_app in H.
            break_match.
            revert H.
            generalize (Vnth_app_aux i2 ip1 l).
            intros g0 H.
            assert(M: (Vnth x1 ip) ≡ (Vnth x1 g0)).
            {
              apply Vnth_eq.
              crush.
            }
            rewrite <- M in H.
            rewrite <- H.
            clear M H g0.
            rewrite mkValue_evalWriter.
            apply Vnth_equiv.
            rewrite Mult.mult_1_r,  Plus.plus_comm; reflexivity.
            reflexivity.
            crush.
        }
        rewrite LS, RS.
        (* destruct Heqp0.*)
        unfold Vec2Union. rewrite VMapp2_app.
        setoid_replace (Vmap2 (SVector.Union _ plus) (sparsify _ (f x0)) (szero_svector fm o1)) with (sparsify fm (f x0)).
        setoid_replace (Vmap2 (SVector.Union _ plus) (szero_svector fm o2) (sparsify fm (g x1))) with (sparsify fm (g x1)).
        unfold sparsify.
        rewrite Vmap_app.
        reflexivity.
        apply Vec2Union_szero_svector_l.
        apply Vec2Union_szero_svector_r.
    Qed.

  End Value_Correctness.

End SigmaHCOLExpansionRules.

Section SigmaHCOLRewritingRules.
  Section Value_Correctness.

    Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

    Theorem rewrite_PointWise_ISumUnion
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n _)
          (pf: { j | j<o} -> CarrierA -> CarrierA)
          `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}
          (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero) (* function with the fixed point 0 *)
          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family)
      :
        (@SHPointwise _ _ o pf pf_mor) ⊚ (@ISumUnion i o n op_family)
        =
        (@ISumUnion i o n
                    (SHOperatorFamilyCompose _
                                             (@SHPointwise _ _ o pf pf_mor)
                                             op_family)
        ).
    Proof.
      unfold SHOperatorFamilyCompose.
      unfold SHCompose.
      unfold equiv, SHOperator_equiv, SHCompose; simpl.
      apply ext_equiv_applied_equiv.
      -
        (* LHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply SHPointwise_impl_proper.
        apply pf_mor.
        apply Diamond_proper.
        + apply CarrierAPlus_proper.
        + reflexivity.
        + intros k kc.
          apply op_proper.
      -
        (* RHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply Diamond_proper.
        + apply CarrierAPlus_proper.
        + reflexivity.
        + intros k kc.
          apply op_proper.
      -
        intros x.
        unfold Diamond.
        unfold compose.
        vec_index_equiv j jc. (* fix column *)
        setoid_rewrite SHPointwise_impl_nth; try apply MonoidLaws_RthetaFlags.

        unfold Apply_Family'.
        rewrite 2!AbsorbMUnionIndex_Vbuild.

        (* -- Now we are dealing with UnionFolds only -- *)
        unfold Apply_Family_Single_NonUnit_Per_Row in Uz.
        specialize (Uz x).
        apply Vforall_nth with (ip:=jc) in Uz.
        unfold Apply_Family, Apply_Family', transpose in Uz.
        rewrite Vbuild_nth in Uz.
        unfold row in Uz.
        rewrite Vmap_Vbuild in Uz.
        unfold Vnth_aux in Uz.

        apply Vunique_cases in Uz.
        destruct Uz as [Uzeros | Uone].
        +
          (* all zeros in in vbuild *)
          (* prove both sides are 0 *)
          revert Uzeros.
          set (vl:=(@Vbuild (Rtheta' Monoid_RthetaFlags) n
                            (fun (z : nat) (zi : Peano.lt z n) =>
                               @Vnth (Rtheta' Monoid_RthetaFlags) o
                                     (@get_family_op Monoid_RthetaFlags i o n _ op_family z zi x) j jc))).
          intros Uzeros.
          assert(H:UnionFold _ plus zero vl = mkSZero).
          {
            generalize dependent vl.
            intros vl Uzeros.
            unfold UnionFold.
            clear op_family.
            induction vl.
            -
              unfold mkSZero.
              reflexivity.
            -
              simpl in Uzeros. destruct Uzeros as [Hh Hx].
              Opaque Monad.ret. simpl. Transparent Monad.ret.
              rewrite IHvl.
              *
                rewrite Union_SZero_l by apply MonoidLaws_RthetaFlags.
                unfold compose, Is_ValZero in Hh.
                unfold_Rtheta_equiv.
                rewrite evalWriter_Rtheta_SZero.
                unfold equiv.
                destruct(CarrierAequivdec (WriterMonadNoT.evalWriter h) zero) as [E | NE].
                apply E.
                crush.
              *
                apply Hx.
          }
          rewrite_clear H.
          rewrite evalWriter_Rtheta_SZero.
          rewrite pfzn.

          set (vr:=Vbuild _).

          assert(H: UnionFold _ plus zero vr = mkSZero).
          {
            assert(H: Vbuild (λ (i0 : nat) (ic : i0 < n), Vnth (@SHPointwise_impl Monoid_RthetaFlags _ pf (op Monoid_RthetaFlags (op_family (mkFinNat ic)) x)) jc) =
                      Vbuild (λ (i0 : nat) (ic : i0 < n), mkValue (pf (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth (op Monoid_RthetaFlags (op_family (mkFinNat ic)) x) jc))))).
            {
              vec_index_equiv k kc.
              rewrite 2!Vbuild_nth.
              rewrite SHPointwise_impl_nth by apply pf_mor.
              reflexivity.
            }

            subst vl vr.

            unfold UnionFold.
            rewrite_clear H.
            rewrite Vforall_Vbuild in Uzeros.
            rewrite <- 3!Vmap_Vbuild.
            rewrite 2!Vmap_map.

            assert(H: (Vmap
                         (λ x0 : WriterMonad.writerT Monoid_RthetaFlags IdentityMonad.ident CarrierA,
                                 mkValue (pf (j ↾ jc) (WriterMonadNoT.evalWriter x0)))
                         (Vbuild
                            (λ (z : nat) (zi : z < n),
                             Vnth
                               (op Monoid_RthetaFlags (op_family (mkFinNat zi)) x)
                               jc))) = szero_svector Monoid_RthetaFlags n).
            {
              unfold szero_svector.
              vec_index_equiv k kc.
              rewrite Vnth_map.
              rewrite Vnth_const.
              rewrite Vbuild_nth.
              specialize (Uzeros k kc).
              setoid_replace (Vnth
                                (op Monoid_RthetaFlags (op_family (mkFinNat kc)) x)
                                jc) with (@mkSZero Monoid_RthetaFlags).
              -
                rewrite evalWriter_Rtheta_SZero.
                rewrite pfzn.
                unfold_Rtheta_equiv.
                rewrite evalWriter_Rtheta_SZero.
                reflexivity.
              -
                unfold compose, Is_ValZero in Uzeros.
                unfold_Rtheta_equiv.
                rewrite evalWriter_Rtheta_SZero.
                unfold equiv.
                unfold Rtheta.
                unfold get_family_op in Uzeros.
                generalize dependent (Vnth (op Monoid_RthetaFlags (op_family (mkFinNat kc)) x) jc).
                intros h Uzeros.
                destruct (CarrierAequivdec (WriterMonadNoT.evalWriter h) zero) as [E | NE].
                apply E.
                crush.
            }
            rewrite_clear H.
            fold (@UnionFold Monoid_RthetaFlags n plus zero (szero_svector _ n)).
            apply UnionFold_zero_structs; try apply MonoidLaws_RthetaFlags.
            apply szero_svector_all_zeros.
          }
          rewrite_clear H.
          unfold_Rtheta_equiv.
          rewrite evalWriter_Rtheta_SZero.
          reflexivity.
        +
          (* one non zero in vbuild. *)
          (* Prove both sides are this value *)

          (* lhs *)
          revert Uone.
          set (vl:=Vbuild _).
          intros Uone.
          inversion Uone as [k H]; clear Uone.
          inversion H as [kc Uone]; clear H.
          rewrite UnionFold_VallButOne_zero with (kc:=kc).
          *
            subst vl.
            rewrite Vbuild_nth.

            (* rhs *)
            unfold get_family_op; simpl.
            set (vr:=Vbuild _).
            assert(H: VAllButOne k kc Is_ValZero vr).
            {
              subst vr.
              unfold VAllButOne.
              intros t tc H.
              rewrite Vbuild_nth.
              unfold Is_ValZero, Is_ValX.
              rewrite SHPointwise_impl_nth by apply pf_mor.

              unfold VAllButOne in Uone.
              specialize (Uone t tc H).
              rewrite Vbuild_nth in Uone.


              apply not_not_on_decidable with (A:=CarrierA) in Uone.
              symmetry in Uone.
              crush.
              reflexivity.
              typeclasses eauto.
            }

            rewrite UnionFold_VallButOne_zero with (kc:=kc).
            ** subst vr.
               rewrite Vbuild_nth.
               rewrite SHPointwise_impl_nth.
               reflexivity.
            ** apply H.
          *
            apply VallButOneSimpl with (P1:=Is_ValZero) in Uone.
            apply Uone.

            intros x0 H.
            apply not_not_on_decidable with (A:=CarrierA) in H.
            unfold Is_ValZero, Is_ValX.
            symmetry.
            apply H.
            typeclasses eauto.
        +
          intros.
          unfold compose, Is_ValZero.
          generalize (WriterMonadNoT.evalWriter a).
          intros c.
          assert(Z: Decision (c=zero)) by apply CarrierAequivdec.
          unfold Decision in Z.
          destruct Z.
          right; auto.
          left; auto.
    Qed.

    Lemma RStheta2Rtheta_Vfold_left_rev_mkValue
          {n:nat}
          {v:rsvector n}
          {f: CarrierA -> CarrierA -> CarrierA}
          {initial: CarrierA}
          `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
      :
        RStheta2Rtheta
          (Vfold_left_rev (SVector.Union Monoid_RthetaSafeFlags f) (mkStruct initial) v) =
        mkValue
          (Vfold_left_rev f initial (densify _ v)).
    Proof.
      induction v.
      -
        compute.
        reflexivity.
      -
        rewrite Vfold_left_rev_cons.
        rewrite RStheta2Rtheta_over_Union.
        rewrite IHv. clear IHv.

        unfold densify.
        simpl.

        generalize (@Vfold_left_rev CarrierA CarrierA f n initial
                                    (@Vmap (Rtheta' Monoid_RthetaSafeFlags) CarrierA
                                           (@WriterMonadNoT.evalWriter RthetaFlags CarrierA Monoid_RthetaSafeFlags)
                                           n v)).
        intros c. clear v.

        unfold SVector.Union, Monad.liftM2, mkValue.
        simpl.
        rewrite 2!RthetaFlags_runit.
        unfold equiv, Rtheta_equiv, Rtheta'_equiv.
        unfold WriterMonadNoT.evalWriter, WriterMonadNoT.runWriter.
        unfold compose.
        reflexivity.
    Qed.

    Fact UnionFold_all_zeroes
         {n:nat}
         `{uf_zero: MonUnit CarrierA}
         `{f: SgOp CarrierA}
         `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
         `{f_left_id : @LeftIdentity CarrierA CarrierA CarrierAe
                                     (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}

         (vl : vector (Rtheta' Monoid_RthetaFlags) n)
         (Uzeros : Vforall
                     (not
                        ∘ (not ∘ equiv uf_zero
                               ∘ WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))) vl)
      :
        UnionFold Monoid_RthetaFlags f uf_zero vl = mkStruct uf_zero.
    Proof.
      unfold UnionFold.
      induction vl.
      -
        unfold mkStruct.
        reflexivity.
      -
        simpl in Uzeros. destruct Uzeros as [Hh Hx].
        Opaque Monad.ret. simpl. Transparent Monad.ret.
        specialize (IHvl Hx).
        rewrite_clear IHvl.
        +
          unfold SVector.Union.
          unfold_Rtheta_equiv.
          rewrite evalWriter_Rtheta_liftM2.
          destruct(CarrierAequivdec (WriterMonadNoT.evalWriter h) uf_zero) as [E | NE].
          *
            rewrite E.
            apply f_left_id.
          *
            crush.
    Qed.

    (* Basically states that 'Diamond' applied to a family which
       guarantees single-non zero value per row dows not depend on the
       function implementation.

       TODO: Perhaps use [[https://argumatronic.com/posts/2019-06-21-algebra-cheatsheet.html#ring-like-structures][quazi-ring]] structure to describe 2 monoids?
     *)
    Lemma Diamond_f_subst
          {i o n}

          (* Common unit for both monoids *)
          `{uf_zero: MonUnit CarrierA}

          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n uf_zero)

          (* 1st Monoid. Used in reduction *)
          `{f: SgOp CarrierA}
          `{f_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ f uf_zero}
          (* 2nd Monoid. Used in IUnion *)
          `{u: SgOp CarrierA}
          `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}
      :
        Apply_Family_Single_NonUnit_Per_Row _ op_family
        ->
        Diamond f uf_zero (get_family_op Monoid_RthetaFlags op_family) =
        Diamond u uf_zero (get_family_op Monoid_RthetaFlags op_family).
    Proof.
      intros Uz.
      apply ext_equiv_applied_equiv; try (split; typeclasses eauto).
      intros x.
      unfold Diamond.

      vec_index_equiv j jc.
      unfold Apply_Family'.
      rewrite 2!AbsorbMUnionIndex_Vbuild.

      (* -- Now we are dealing with UnionFolds only -- *)
      unfold Apply_Family_Single_NonUnit_Per_Row in Uz.
      specialize (Uz x).
      apply Vforall_nth with (ip:=jc) in Uz.
      unfold Apply_Family, Apply_Family', transpose in Uz.
      rewrite Vbuild_nth in Uz.
      unfold row in Uz.
      rewrite Vmap_Vbuild in Uz.
      unfold Vnth_aux in Uz.

      apply Vunique_cases in Uz.
      destruct Uz as [Uzeros | Uone].
      -
        (* all zeros in in vbuild *)
        revert Uzeros.
        set (vl:=Vbuild _).
        generalize dependent vl.
        intros vl Uzeros.
        erewrite 2!UnionFold_all_zeroes; auto.
      -
        (* one non zero in vbuild. *)
        revert Uone.
        set (vl:=Vbuild _).
        intros Uone.
        inversion Uone as [k H]; clear Uone.
        inversion H as [kc Uone]; clear H.

        rewrite 2!UnionFold_VallButOne_a_zero with (ic:=kc); try typeclasses eauto.
        reflexivity.
        apply Uone.
        apply Uone.
      -
        intros a.
        unfold not, compose.
        destruct(CarrierAequivdec uf_zero (WriterMonadNoT.evalWriter a)) as [E | NE].
        right; auto.
        left; auto.
    Qed.


    (* An unfortunatly named section for a group on lemmas related to operations on a type constrained by predicate. *)
    Section Under_P.

      Fact UnionFold_all_zeroes_under_P
           {fm}
           {n:nat}
           `{uf_zero: MonUnit CarrierA}
           `{f: SgOp CarrierA}
           (vl : vector (Rtheta' fm) n)

           (* Monoid on restriction on f *)
           {P: SgPred CarrierA}
           `{f_mon: @RMonoid _ _ f uf_zero P}

           `{Fpos: Vforall (liftRthetaP P) vl}

           (Uzeros : Vforall
                       (not
                          ∘ (not ∘ equiv uf_zero
                                 ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) vl)
      :
        UnionFold fm f uf_zero vl = mkStruct uf_zero.
      Proof.
        unfold UnionFold.
        dependent induction n.
        +
          dep_destruct vl.
          reflexivity.
        +
          dep_destruct vl.
          rename h into v0, x into vs.

          simpl in Uzeros. destruct Uzeros as [Hh Hx].
          Opaque Monad.ret. simpl. Transparent Monad.ret.

          assert(f_mor : Proper (equiv ==> equiv ==> equiv) f).
          {
            destruct f_mon.
            apply rsg_op_proper.
          }

          rewrite_clear IHn; try eauto.
          *
            unfold SVector.Union.
            unfold_Rtheta_equiv.
            rewrite evalWriter_Rtheta_liftM2.
            destruct(CarrierAequivdec (WriterMonadNoT.evalWriter v0) uf_zero) as [E | NE].
            --
              rewrite E.
              remember (WriterMonadNoT.evalWriter (mkStruct uf_zero)) as z.
              destruct f_mon.
              apply rmonoid_right_id.
              subst z.
              apply mon_restriction.
            --
              crush.
          *
            crush.
      Qed.

      (* A variant of [UnionFold_VallButOne_a_zero] taking into account restriction *)
      Lemma UnionFold_VallButOne_a_zero_under_P
            {fm}
            {n : nat}
            (v : svector fm n)
            {i : nat}
            (ic : i < n)

            `{uf_zero: MonUnit CarrierA}
            `{f: SgOp CarrierA}

            (* Monoid on restriction on f *)
            {P: SgPred CarrierA}
            `{f_mon: @RMonoid _ _ f uf_zero P}

            `{Fpos: Vforall (liftRthetaP P) v}
        :
          VAllButOne i ic
                     (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) v -> UnionFold fm f uf_zero v = Vnth v ic.
      Proof.
        intros U.

        assert(f_mor : Proper (equiv ==> equiv ==> equiv) f).
        {
          destruct f_mon.
          apply rsg_op_proper.
        }

        dependent induction n.
        - crush.
        -
          dep_destruct v.
          destruct (eq_nat_dec i 0).
          +
            (* Case ("i=0"). *)
            rewrite Vnth_cons_head by assumption.
            rewrite UnionFold_cons.

            assert(H: Vforall (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) x).
            {
              apply Vforall_nth_intro.
              intros j jp.
              assert(ipp:S j < S n) by lia.
              unfold MonUnit in *.
              unfold Rtheta',Monad_RthetaFlags,WriterMonadNoT.writer in x.
              replace (Vnth x jp) with (Vnth (Vcons h x) ipp) by apply Vnth_Sn.
              apply U.
              omega.
            }

            assert(UZ: Is_ValX uf_zero (UnionFold fm f uf_zero x)).
            {
              rewrite UnionFold_all_zeroes_under_P; eauto.
              -
                apply Is_ValX_mkStruct.
              -
                apply Fpos.
            }

            unfold_Rtheta_equiv.
            rewrite evalWriterUnion.
            unfold Is_ValX in UZ.
            setoid_replace (WriterMonadNoT.evalWriter (UnionFold fm f uf_zero x)) with uf_zero by apply UZ.

            remember (WriterMonadNoT.evalWriter h) as hc.
            destruct f_mon.
            apply rmonoid_left_id.
            crush.
          +
            (* Case ("i!=0"). *)
            rewrite UnionFold_cons.
            assert (HS: Is_ValX uf_zero h).
            {
              cut (Is_ValX uf_zero (Vnth (Vcons h x) (zero_lt_Sn n))).
              rewrite Vnth_0.
              auto.
              unfold VAllButOne in U.
              assert(jc: 0 < S n) by omega.
              specialize (U 0 jc n0).
              apply not_not_on_decidable.
              typeclasses eauto.
              unfold Is_ValX.

              setoid_replace (λ x0 : Rtheta' fm, WriterMonadNoT.evalWriter x0 = uf_zero)
                with (equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm)).

              * apply U.
              *
                unfold compose.
                apply ext_equiv_applied_equiv.
                split; try typeclasses eauto.
                solve_proper.
                split; try typeclasses eauto.
                intros x0.

                unfold equiv.
                unfold Equiv_instance_0.
                split; intros H; symmetry; apply H.
            }

            destruct i; try congruence.
            simpl.
            generalize (lt_S_n ic).
            intros l.
            rewrite IHn with (ic:=l); eauto.
            *
              unfold_Rtheta_equiv.
              rewrite evalWriterUnion.
              unfold Is_ValX in HS.
              rewrite HS.

              destruct f_mon.
              apply rmonoid_right_id.
              --
                assert(l': S i < S n) by auto.
                apply Vforall_nth with (ip:=l') in Fpos.
                simpl in Fpos.
                replace l with (lt_S_n l') by apply le_unique.
                apply Fpos.
            *
              crush.
            *
              apply VAllButOne_Sn with (h0:=h) (ic0:=ic).
              apply U.
      Qed.

      (*        TODO: Perhaps use [[https://argumatronic.com/posts/2019-06-21-algebra-cheatsheet.html#ring-like-structures][quazi-ring]] structure to describe 2 monoids?
       *)
      Lemma Diamond_f_subst_under_P
            {i o n}

            (* Common unit for both monoids *)
            `{uf_zero: MonUnit CarrierA}

            (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n uf_zero)


            `{f: SgOp CarrierA}

            (* Monoid on restriction on f *)
            {P: SgPred CarrierA}
            `{f_mon: @RMonoid _ _ f uf_zero P}

            (* 2nd Monoid *)
            `{u: SgOp CarrierA}
            `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}

            (Upoz: Apply_Family_Vforall_P _ (liftRthetaP P) op_family)
            (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family)
        :
          Diamond f uf_zero (get_family_op Monoid_RthetaFlags op_family) =
          Diamond u uf_zero (get_family_op Monoid_RthetaFlags op_family).
      Proof.

        assert(f_mor : Proper (equiv ==> equiv ==> equiv) f).
        {
          destruct f_mon.
          apply rsg_op_proper.
        }

        apply ext_equiv_applied_equiv; try (split; typeclasses eauto).
        intros x.
        unfold Diamond.

        vec_index_equiv j jc.
        unfold Apply_Family'.
        rewrite 2!AbsorbMUnionIndex_Vbuild.

        (* -- Now we are dealing with UnionFolds only -- *)
        unfold Apply_Family_Single_NonUnit_Per_Row in Uz.
        specialize (Uz x).
        apply Vforall_nth with (ip:=jc) in Uz.
        unfold Apply_Family, Apply_Family', transpose in Uz.
        rewrite Vbuild_nth in Uz.
        unfold row in Uz.
        rewrite Vmap_Vbuild in Uz.
        unfold Vnth_aux in Uz.

        apply Vunique_cases in Uz.
        destruct Uz as [Uzeros | Uone].
        -
          (* all zeros in in vbuild *)
          revert Uzeros.
          set (vl:=Vbuild _).
          assert(Fpos: Vforall (liftRthetaP P) vl).
          {
            subst vl.
            apply Vforall_Vbuild.
            intros t tc.
            unfold Apply_Family_Vforall_P in Upoz.
            specialize (Upoz x t tc).
            apply Vforall_nth.
            apply Upoz.
          }

          generalize dependent vl.
          intros vl Uzeros Uone.
          rewrite UnionFold_all_zeroes_under_P; eauto.
          rewrite UnionFold_all_zeroes; eauto.
        -
          (* one non zero in vbuild. *)
          revert Uone.
          set (vl:=Vbuild _).
          intros Uone.
          inversion Uone as [k H]; clear Uone.
          inversion H as [kc Uone]; clear H.

          (* RHS rewrites OK, as we have a Monoid there for [u] *)
          setoid_rewrite UnionFold_VallButOne_a_zero with (ic:=kc) at 2; try typeclasses eauto; try apply Uone.

          assert(Fpos: Vforall (liftRthetaP P) vl).
          {
            clear Uone.
            subst vl.
            apply Vforall_Vbuild.
            intros t tc.
            unfold Apply_Family_Vforall_P in Upoz.
            specialize (Upoz x t tc).
            apply Vforall_nth.
            apply Upoz.
          }
          rewrite UnionFold_VallButOne_a_zero_under_P with (ic:=kc);  eauto.
        -
          intros a.
          unfold not, compose.
          destruct(CarrierAequivdec uf_zero (WriterMonadNoT.evalWriter a)) as [E | NE].
          right; auto.
          left; auto.
      Qed.

      Fact eval_2D_Fold
           {o n : nat}
           (uf_zero : CarrierA)
           (f : CarrierA -> CarrierA -> CarrierA)
           (f_mor : Proper (equiv ==> equiv ==> equiv) f)
           (lst : vector (rvector o) n)
        :
          Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
               (Vfold_left_rev (Vmap2 (Monad.liftM2 f) (n:=o))
                               (Vconst (mkStruct uf_zero) o)
                               lst)
          =
          Vfold_left_rev (Vmap2 f (n:=o)) (Vconst uf_zero o)
                         (Vmap (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags)) (n:=o)) lst).
      Proof.

        induction n.
        -
          dep_destruct lst.
          simpl.
          vec_index_equiv j jc.
          rewrite Vnth_map.
          repeat rewrite Vnth_const.
          rewrite evalWriter_mkStruct; reflexivity.
        -
          dep_destruct lst. clear lst.
          simpl.
          specialize (IHn x).

          rewrite <- IHn; clear IHn.

          (* Vconst as Vmap *)
          replace (Vconst (mkStruct (fm:=Monoid_RthetaFlags) uf_zero) o) with
              (Vmap (mkStruct (fm:=Monoid_RthetaFlags)) (Vconst uf_zero o)) at 1
            by apply Vmap_Vconst.

          rewrite Vmap2_Vmap.

          replace (fun a b => _)
            with (fun a b => WriterMonadNoT.evalWriter
                            (Monad.liftM2 f a b)) by auto.
          rewrite Vmap_Vconst.
          vec_index_equiv j jc.
          repeat rewrite Vnth_map.
          repeat rewrite Vnth_map2.
          reflexivity.
      Qed.

      Lemma Vfold_right_under_P
            {A: Type} `{Ae: Equiv A}
            {z: MonUnit A}
            {f: SgOp A}
            (P: SgPred A)
            {f_mon: @CommutativeRMonoid _ _ f z P}
            {n:nat}
            (v:vector A n):
        Vforall P v → P (Vfold_right f v z).
      Proof.
        intros U.
        induction v.
        -
          apply f_mon.
        -
          simpl.
          apply f_mon.
          +
            apply U.
          +
            apply IHv.
            apply U.
      Qed.

      Lemma Vfold_right_left_rev_under_P
            {A: Type} `{Ae: Equiv A}
            {z: MonUnit A}
            {f: SgOp A}
            (P: SgPred A)
            {f_mon: @CommutativeRMonoid _ _ f z P}
            {n:nat}
            (v:vector A n)
            (U: Vforall P v):
        Vfold_left_rev f z v = Vfold_right f v z.
      Proof.
        induction v.
        -
          crush.
        -
          simpl.
          rewrite IHv.
          destruct f_mon eqn:F.
          apply rcommutativity.
          simpl in *.
          apply (Vfold_right_under_P P).
          apply U.
          apply U.
          apply U.
      Qed.

      Lemma VFold_right_split_under_P
            {A: Type}
            {Ae: Equiv A}
            {m n : nat}
            {z: MonUnit A}
            {f: SgOp A}
            (P: SgPred A)
            {f_mon: @CommutativeRMonoid _ _ f z P}
            (h : vector A m)
            (t : vector A n)
            (Uh: Vforall P h)
            (Ut: Vforall P t)
        :
          f (Vfold_right f h z)
            (Vfold_right f t z)
          =
          Vfold_right f (Vapp h t) z.
      Proof.
        remember (Vapp h t) as ht.
        assert(Uht:  Vforall P ht).
        {
          subst ht.
          apply Vforall_app.
          auto.
        }
        replace h with (fst (@Vbreak _ m n ht)).
        replace t with (snd (@Vbreak _ m n ht)).
        -
          clear Heqht h t Uh Ut.
          induction m.
          +
            simpl.
            destruct f_mon eqn:F.
            destruct comrmonoid_rmon.
            apply rmonoid_left_id.
            apply (Vfold_right_under_P P).
            apply Uht.
          +
            assert(C:S m + n ≡ S (m + n)) by omega.
            replace (@Vfold_right A A f (S m + n) ht z)
              with (@Vfold_right A A f (S (m + n)) (@Vcast _ _ ht (S (m + n)) C) z)
              by
                (rewrite Vcast_refl; reflexivity).

            replace (Vfold_right f (Vcast ht C) z)
              with (f (Vhead (Vcast ht C)) (Vfold_right f (Vtail (Vcast ht C)) z))
              by
                (rewrite Vfold_right_reduce; reflexivity).
            rewrite <- IHm.
            *
              simpl.
              destruct f_mon eqn: FM, comrmonoid_rmon.
              repeat rewrite Vcast_refl.
              rewrite rmonoid_ass.
              --
                reflexivity.
              --
                apply Vforall_Vhead.
                apply Uht.
              --
                apply (Vfold_right_under_P P).
                apply Vforall_nth_intro.
                intros i ip.
                assert(ip': i < m + n) by lia.
                rewrite Vnth_fst_Vbreak with (jc1:=ip').
                rewrite Vnth_tail.
                apply Vforall_nth.
                apply Uht.
              --
                apply (Vfold_right_under_P P).
                apply Vforall_nth_intro.
                intros i ip.
                assert(ip': i + m < m + n) by lia.
                rewrite Vnth_snd_Vbreak with (jc2:=ip').
                rewrite Vnth_tail.
                apply Vforall_nth.
                apply Uht.
            *
              rewrite Vcast_refl.
              apply Vforall_Vtail.
              apply Uht.
        -

          subst ht.
          rewrite Vbreak_app.
          auto.
        -
          subst ht.
          rewrite Vbreak_app.
          auto.
      Qed.

    End Under_P.


    (* TODO: move this and other helper lemmas to SigmaHCOLHelperLemmas section above *)
    Section VecMap2CommutativeRMonoid.

      Variable n:nat.
      Variable A: Type.
      Variable Ae: Equiv A.
      Variable As: @Setoid A Ae.
      Variable z: MonUnit A.
      Variable f: SgOp A.
      Variable P: SgPred A.

      Global Instance VecMonRestrictionMap2
             {f_mon: @MonRestriction A f z P}:
        @MonRestriction
          (vector A n)
          (Vmap2 f (n:=n))
          (Vconst z n)
          (Vforall P (n:=n)).
      Proof.
        split.
        +
          unfold sg_P, mon_unit.
          apply Vforall_Vconst.
          apply f_mon.
        +
          intros a b Ha Hb.
          apply Vforall_Vmap2.
          apply f_mon.
          apply Ha.
          apply Hb.
      Qed.

      Global Instance VecRMonoidMap2
             {f_mon: @RMonoid A Ae f z P}
        :
          @RMonoid
            (vector A n)
            (=)
            (Vmap2 f (n:=n))
            (Vconst z n)
            (Vforall P (n:=n)).
      Proof.
        split; try typeclasses eauto.
        +
          intros a b c Ha Hb Hc.
          unfold sg_op.
          vec_index_equiv j jc.
          repeat rewrite Vnth_map2.
          destruct f_mon.
          apply rmonoid_ass.
          apply Vforall_nth, Ha.
          apply Vforall_nth, Hb.
          apply Vforall_nth, Hc.
        +
          intros y H.
          unfold sg_op.
          vec_index_equiv j jc.
          rewrite Vnth_map2.
          destruct f_mon.
          unfold mon_unit. rewrite Vnth_const.
          apply rmonoid_left_id.
          apply Vforall_nth, H.
        +
          intros y H.
          unfold sg_op.
          vec_index_equiv j jc.
          rewrite Vnth_map2.
          destruct f_mon.
          unfold mon_unit. rewrite Vnth_const.
          apply rmonoid_right_id.
          apply Vforall_nth, H.
      Qed.

      Global Instance VecCommutativeRMonoidMap2
             {f_mon: @CommutativeRMonoid A Ae f z P}
        :
          @CommutativeRMonoid
            (vector A n)
            (=)
            (Vmap2 f (n:=n))
            (Vconst z n)
            (Vforall P (n:=n)).
      Proof.
        split.
        -
          apply VecRMonoidMap2.
        -
          intros a b Hx Hy.
          unfold sg_op.
          induction n.
          +
            dep_destruct a.
            dep_destruct b.
            reflexivity.
          +
            simpl.
            destruct f_mon.

            assert(@sg_P A P (Vhead a))
              by apply Vforall_Vhead, Hx.
            assert(@sg_P A P (Vhead b))
              by apply Vforall_Vhead, Hy.

            assert(@sg_P (vector A n0) (@Vforall A P n0) (Vtail a))
              by apply Vforall_Vtail, Hx.
            assert(@sg_P (vector A n0) (@Vforall A P n0) (Vtail b))
              by apply Vforall_Vtail, Hy.


            rewrite rcommutativity; try assumption.
            rewrite <- IHn0; try assumption.
            reflexivity.
      Qed.

    End VecMap2CommutativeRMonoid.

    Fact Vhead_Vfold_right_Vmap2
         {A:Type}
         (m n : nat)
         (z : A)
         (f : A -> A -> A)
         (gen : forall p : nat, p < n → vector A (S m))
         (tmn : ∀ t : nat, t < S m * n → t mod n < n)
         (tndm : ∀ t : nat, t < S m * n → t / n < S m)
      :
        Vhead
          (Vfold_right
             (λ v1 v2 : vector A (S m),
                        Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2)))
             (Vbuild gen) (Vcons z (Vconst z m)))
          ≡ Vfold_right f
          (Vbuild
             (λ (t : nat) (tc : t < n),
              Vnth (gen (t mod n) (tmn t (Nat.lt_lt_add_r t n (m * n) tc)))
                   (tndm t (Nat.lt_lt_add_r t n (m * n) tc)))) z.
    Proof.
      replace (fun v1 v2 : vector A (S m) => Vcons (f (Vhead v1) (Vhead v2)) (@Vmap2 A A A f m (Vtail v1) (Vtail v2)))
        with (@Vmap2 A A A f (S m)) by reflexivity.
      replace (Vcons z (Vconst z m)) with (Vconst z (S m)) by reflexivity.

      replace (fun (t : nat) (tc : t < n) =>
                 Vnth (gen (t mod n) (tmn t (Nat.lt_lt_add_r t n (m * n) tc)))
                      (tndm t (Nat.lt_lt_add_r t n (m * n) tc))) with
          (fun (t : nat) (tc : t < n) =>
             Vhead (gen (t mod n) (tmn t (Nat.lt_lt_add_r t n (m * n) tc)))).
      {
        clear tndm.
        induction n.
        +
          reflexivity.
        +
          setoid_rewrite Vbuild_Sn at 2.
          rewrite Vfold_right_cons.
          pose (gen' := (fun p pc => gen (S p) (lt_n_S pc))).

          assert(tmn' : forall t : nat, t < S m * n → t mod n < n).
          {
            intros t H.
            apply modulo_smaller_than_devisor.
            lia.
          }

          specialize (IHn gen' tmn').

          replace (fun (i : nat) (ip : i < n) =>
                     Vhead
                       (gen (S i mod S n)
                            (tmn (S i) (Nat.lt_lt_add_r (S i) (S n) (m * S n) (lt_n_S ip)))))
            with
              (fun (t : nat) (tc : t < n) =>
                 Vhead (gen' (t mod n) (tmn' t (Nat.lt_lt_add_r t n (m * n) tc)))).
          {
            rewrite <- IHn.
            clear IHn tmn'.
            rewrite Vbuild_Sn.
            cbn.
            repeat f_equal.
            generalize (tmn 0 (Nat.lt_lt_add_r 0 (S n) (m * S n) (Nat.lt_0_succ n))) as ic.
            clear.
            revert gen.
            simpl.
            rewrite Nat.sub_diag.
            intros gen ic.
            apply f_equal, le_unique.
          }

          extensionality t.
          extensionality tc.

          unfold gen'.
          repeat f_equiv.
          clear - tc.
          assert(S t < S n) as stc by lia.

          generalize (lt_n_S (tmn' t (Nat.lt_lt_add_r t n (m * n) tc))).
          generalize (tmn (S t) (Nat.lt_lt_add_r (S t) (S n) (m * S n) (lt_n_S tc))).
          repeat rewrite (Nat.mod_small) by auto.
          intros l l0.
          replace l0 with l by apply NatUtil.lt_unique.
          reflexivity.
      }

      extensionality t.
      extensionality tc.
      generalize (tndm t (Nat.lt_lt_add_r t n (m * n) tc)).
      generalize (tmn t (Nat.lt_lt_add_r t n (m * n) tc)).
      rewrite Nat.mod_small by auto.
      rewrite Nat.div_small by auto.
      intros l l0.
      rewrite Vnth_0.
      reflexivity.
    Qed.

    Lemma Vtail_Vfold_right_Vmap2
          {A:Type}
          (m n : nat)
          (z : A)
          (f : A -> A -> A)
          (gen : ∀ p : nat, p < n → vector A (S m)):
      Vtail
        (Vfold_right
           (λ v1 v2 : vector A (S m),
                      Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2)))
           (Vbuild gen) (Vcons z (Vconst z m)))
        ≡ Vfold_right (Vmap2 f (n:=m)) (Vbuild (λ (p : nat) (pc : p < n), Vtail (gen p pc)))
        (Vconst z m).
    Proof.
      replace (fun v1 v2 : vector A (S m) => Vcons (f (Vhead v1) (Vhead v2)) (@Vmap2 A A A f m (Vtail v1) (Vtail v2)))
        with (@Vmap2 A A A f (S m)) by reflexivity.
      replace (Vcons z (Vconst z m)) with (Vconst z (S m)) by reflexivity.

      induction n.
      -
        reflexivity.
      -
        pose (gen' := (fun p pc => gen (S p) (lt_n_S pc))).

        specialize (IHn gen' ).
        setoid_rewrite Vbuild_Sn at 2.
        rewrite Vfold_right_cons.
        replace (Vbuild (λ (i : nat) (ip : i < n), Vtail (gen (S i) (lt_n_S ip))))
          with (Vbuild (λ (p : nat) (pc : p < n), Vtail (gen' p pc))) by reflexivity.

        rewrite <- IHn. clear IHn.
        subst gen'.

        setoid_rewrite Vbuild_Sn.
        rewrite Vfold_right_cons.

        vec_index_equiv i ip.
        rewrite Vnth_tail.
        rewrite 2!Vnth_map2.
        rewrite 2!Vnth_tail.
        reflexivity.
    Qed.


    Section Vec_Permutations.
      (* TODO: think of good place to move this. Depdens on both [IndexFunctions] and [VecPermutation] *)
      Lemma Vbuild_permutation
            {A: Type}
            {n: nat}
            {f: forall i : nat, i < n -> A}
            (t: index_map n n)
            (P: index_map_bijective t)
      :
        VPermutation A n (Vbuild f) (Vbuild (fun i ic =>
                                               f (⟦t⟧ i) («t» i ic)
                                    )).
      Proof.
        induction n.
        -
          crush.
        -
          rewrite Vbuild_Sn.

          pose(t' := build_inverse_index_map t).
          assert(P': inverse_index_map_bijective t')
            by apply build_inverse_index_map_is_bijective, P.

          pose (k := inverse_index_f _ t' 0).
          assert(L: k<S n).
          {
            apply inverse_index_f_spec.
            apply in_range_exists.
            +
              apply zero_lt_Sn.
            +
              apply P.
              apply zero_lt_Sn.
          }

          assert(K: ⟦ t ⟧ k ≡ 0).
          {
            subst k t'.
            apply build_inverse_index_map_is_right_inverse.
            -
              apply P.
            -
              apply index_map_surjective_in_range.
              apply P.
              apply zero_lt_Sn.
            -
              reflexivity.
          }

          assert(E0: k + (S (n - k)) ≡ S n) by lia.
          rewrite Vbuild_range_cast with (E:=E0).
          rewrite Vbuild_split_at.

          match goal with
            [ |- VPermutation _ _ ?l ?r ] => remember l as lhs; remember r as rhs
          end.

          assert(E1: (k + (n - k)) ≡ n) by lia.
          assert(T1: VPermutation A _
                                  (Vcons
                                     (f (⟦ t ⟧ k)
                                        (« t » k
                                           (eq_lt_lt E0
                                                     (VecUtil.Vbuild_split_at_def_obligation_2 k (n - k)))))
                                     (Vcast
                                        (Vapp
                                           (Vbuild
                                              (λ (t0 : nat) (tc : t0 < k),
                                               f (⟦ t ⟧ t0)
                                                 (« t » t0
                                                    (eq_lt_lt E0
                                                              (VecUtil.Vbuild_split_at_def_obligation_1 k (n - k) t0 tc)))))

                                           (Vbuild
                                              (λ (t0 : nat) (tc : t0 < n - k),
                                               f (⟦ t ⟧ (t0 + 1 + k))
                                                 (« t » (t0 + 1 + k)
                                                    (eq_lt_lt E0
                                                              (VecUtil.Vbuild_split_at_def_obligation_3 k
                                                                                                        (n - k) t0 tc)))))) E1))

                                  rhs).
          {
            subst rhs.
            eapply ListVecPermutation; auto.
            simpl.
            repeat rewrite list_of_vec_Vcast.
            rewrite 2!list_of_vec_Vapp.
            apply Permutation.Permutation_middle.
          }
          remember (Vcons _ _) as t1 in T1.
          apply vperm_trans with (l':=t1), T1; clear rhs Heqrhs T1.

          replace (f (⟦ t ⟧ k)
                     (« t » k
                        (eq_lt_lt E0 (VecUtil.Vbuild_split_at_def_obligation_2 k (n - k)))))
            with (f 0 (Nat.lt_0_succ n)) in Heqt1.
          +
            subst lhs t1.
            eapply vperm_skip.
            pose(f' := fun i (ic:i<n) => f (S i) (lt_n_S ic)).
            specialize (IHn f').
            unfold f' in IHn.

            pose(h_func := fun x => pred (match Compare_dec.lt_dec x k  with
                                       | in_left => ⟦ t ⟧ x
                                       | in_right => ⟦ t ⟧ (S x)
                                       end)
                ).

            assert(h_spec: forall x, x<n -> (h_func x) < n).
            {
              intros x H.
              unfold h_func.
              break_match.
              -
                destruct t.
                simpl in *.
                assert(SL: index_f x  < S n) by auto.
                crush.
              -
                destruct t.
                simpl in *.
                assert(SL: index_f (S x) < S n).
                crush.
                crush.
            }
            pose(h := IndexMap _ _ h_func h_spec).

            assert(NK: forall p, p < S n -> p ≢ k -> ⟦ t ⟧ p ≢ 0).
            {
              intros p pc H.
              contradict H.
              apply P; auto.
              rewrite K, H.
              reflexivity.
            }

            assert(H_b: index_map_bijective h).
            {
              assert(Hinj: index_map_injective h).
              {
                (* injectivity *)
                destruct P as [Pi Ps].
                unfold index_map_injective in *.
                intros x y xc yc H.
                simpl in *. clear h.

                unfold h_func in H.
                repeat break_match.
                +
                  (* x,y < k *)
                  apply Pi; auto.
                  assert(⟦ t ⟧ x ≢ 0) by auto.
                  assert(⟦ t ⟧ y ≢ 0) by auto.

                  destruct (⟦ t ⟧ x); try congruence.
                  destruct (⟦ t ⟧ y); try congruence.
                  rewrite <- 2!pred_Sn in H.
                  auto.
                +
                  (* impossible case: x,y on different sides of k *)
                  clear E0 E1 h_func h_spec IHn P' f' t'.
                  generalize dependent k.
                  intros k L K NK l n1.

                  assert(⟦ t ⟧ x ≢ 0) by auto.

                  destruct (eq_nat_dec k (S y)) as [Ek | NEk].
                  *
                    rewrite <- Ek in H.
                    rewrite K in H.
                    destruct (⟦ t ⟧ x) eqn:Hx.
                    --
                      congruence.
                    --
                      lia.
                  *
                    destruct (⟦ t ⟧ x) eqn:Hx, (⟦ t ⟧ (S y)) eqn:Hy; try congruence.
                    --
                      rewrite <- K in Hy.
                      crush.
                    --
                      rewrite <- 2!pred_Sn in H.
                      subst_max.
                      rewrite <- Hy in Hx.
                      apply Pi in Hx; crush.
                +
                  (* impossible case: x,y on different sides of k *)
                  clear E0 E1 h_func h_spec IHn P' f' t'.
                  generalize dependent k.
                  intros k L K NK l n0.

                  assert(⟦ t ⟧ y ≢ 0) by auto.

                  destruct (eq_nat_dec k (S x)) as [Ek | NEk].
                  *
                    rewrite <- Ek in H.
                    rewrite K in H.
                    destruct (⟦ t ⟧ y) eqn:Hx.
                    --
                      congruence.
                    --
                      lia.
                  *
                    destruct (⟦ t ⟧ y) eqn:Hx, (⟦ t ⟧ (S x)) eqn:Hy; try congruence.
                    --
                      rewrite <- K in Hy.
                      crush.
                    --
                      rewrite <- 2!pred_Sn in H.
                      subst_max.
                      rewrite <- Hy in Hx.
                      apply Pi in Hx; crush.
                +
                  (* x,y > k *)
                  apply eq_add_S.
                  apply Pi; try lia.

                  destruct (eq_nat_dec k (S x)), (eq_nat_dec k (S y)).
                  *
                    rewrite <- e, <- e0.
                    reflexivity.
                  *
                    crush.
                  *
                    crush.
                  *
                    assert(⟦ t ⟧ (S x) ≢ 0).
                    {
                      apply NK.
                      lia.
                      auto.
                    }

                    assert(⟦ t ⟧ (S y) ≢ 0).
                    {
                      apply NK; auto.
                      lia.
                    }

                    destruct (⟦ t ⟧ (S x)); try congruence.
                    destruct (⟦ t ⟧ (S y)); try congruence.
                    rewrite <- 2!pred_Sn in H.
                    auto.
              }

              assert(Hsurj: index_map_surjective h).
              {
                clear IHn E0 E1 f f'.
                unfold index_map_surjective in *.
                intros y yc.

                pose(h'_func := fun y => let x0 := (inverse_index_f t t' (S y)) in
                                      match Compare_dec.lt_dec x0 k  with
                                      | in_left => x0
                                      | in_right => pred x0
                                      end).
                exists (h'_func y).

                assert(h'_spec: h'_func y < n).
                {
                  unfold h'_func.
                  break_if.
                  - lia.
                  -
                    assert (inverse_index_f t t' (S y) < S n).
                    {
                      apply (inverse_index_f_spec t t' (S y)).
                      apply index_map_surjective_in_range.
                      apply P.
                      apply lt_n_S, yc.
                    }
                    lia.
                }
                exists h'_spec.


                assert(K': inverse_index_f t t' 0 ≡ k).
                {
                  apply build_inverse_index_map_is_left_inverse.
                  apply P.
                  apply L.
                  apply K.
                }

                assert(NK': forall p, p < S n -> p ≢ 0 -> (inverse_index_f t t' p ≢ k)).
                {
                  intros p pc H.
                  contradict H.
                  apply P'; try lia.
                  apply index_map_surjective_in_range.
                  apply P. apply pc.
                  apply index_map_surjective_in_range.
                  apply P. lia.
                }

                simpl.
                unfold h_func, h'_func.
                repeat break_if.
                -
                  assert(H: ⟦ t ⟧ (inverse_index_f t t' (S y)) ≢ 0).
                  {
                    apply NK.
                    apply (inverse_index_f_spec t t' (S y)).
                    apply index_map_surjective_in_range.
                    apply P.
                    apply lt_n_S, yc.
                    apply NK'.
                    lia.
                    auto.
                  }

                  apply eq_add_S.
                  rewrite S_pred_simpl by apply H.
                  apply build_inverse_index_map_is_right_inverse; auto.
                  apply P.
                  apply index_map_surjective_in_range.
                  apply P.
                  lia.
                -
                  assert(KK: inverse_index_f t t' (S y) ≡ k) by lia.
                  rewrite <- KK in K'.
                  apply P' in K'.
                  +
                    congruence.
                  +
                    apply index_map_surjective_in_range.
                    apply P.
                    lia.
                  +
                    apply index_map_surjective_in_range.
                    apply P.
                    lia.
                -
                  lia.
                -
                  remember (inverse_index_f t t' (S y)) as x0.
                  remember (Init.Nat.pred x0) as x1.
                  apply eq_add_S.
                  rewrite S_pred_simpl.
                  +
                    subst x1.
                    destruct x0.
                    *
                      (* x0 = 0? *)
                      clear n0. (* same as n1 *)
                      simpl.
                      destruct k.
                      --
                        rewrite <- K' in Heqx0.
                        apply P' in Heqx0.
                        ++
                          congruence.
                        ++
                          apply index_map_surjective_in_range.
                          apply P.
                          lia.
                        ++
                          apply index_map_surjective_in_range.
                          apply P.
                          lia.
                      --
                        lia.
                    *
                      rewrite S_pred_simpl.
                      --
                        apply build_inverse_index_map_is_right_inverse.
                        apply P.
                        apply index_map_surjective_in_range.
                        apply P.
                        lia.
                        rewrite Heqx0.
                        reflexivity.
                      --
                        lia.
                  +
                    intros H.
                    rewrite <- K in H.
                    apply P in H; try lia.
                    assert(x0 < S n).
                    {
                      subst x0.
                      apply (inverse_index_f_spec t t' (S y)).
                      apply index_map_surjective_in_range.
                      apply P.
                      lia.
                    }
                    lia.
              }
              split; auto.
            }
            specialize (IHn h H_b).
            rewrite_clear IHn.
            remember (Vcast _ _) as l1.
            replace (Vbuild _ ) with l1.
            apply VPermutation_refl.
            subst l1.

            vec_index_equiv i ip.
            rewrite Vbuild_nth.
            rewrite Vnth_cast.
            rewrite Vnth_app.
            break_match.
            *
              rewrite Vbuild_nth.
              subst h.
              unfold h_func.
              simpl.
              assert(E: (⟦ t ⟧ (i - k + 1 + k)) ≡ (S (Init.Nat.pred (if Compare_dec.lt_dec i k then ⟦ t ⟧ i else ⟦ t ⟧ (S i))))).
              {
                break_if.
                - crush.
                -
                  replace (i - k + 1 + k) with (S i) by omega.
                  destruct (⟦ t ⟧ (S i)) eqn:T.
                  +
                    rewrite <- K in T.
                    apply P in T; crush.
                  +
                    reflexivity.
              }
              forall_n_lt_eq.
            *
              rewrite Vbuild_nth.
              subst h.
              unfold h_func.
              simpl.
              symmetry.
              assert(E: (S (Init.Nat.pred (if Compare_dec.lt_dec i k then ⟦ t ⟧ i else ⟦ t ⟧ (S i)))) ≡⟦ t ⟧ i ).
              {
                break_if; try omega.
                destruct (⟦ t ⟧ i) eqn:T.
                +
                  rewrite <- K in T.
                  apply P in T; crush.
                +
                  reflexivity.
              }
              forall_n_lt_eq.
          +
            symmetry.
            clear Heqt1.
            forall_n_lt_eq.
      Qed.

      Lemma Vfold_VPermutation
            {n : nat}
            {A: Type} `{Ae: Equiv A}
            (z : MonUnit A)
            (f : SgOp A)
            (f_mon: CommutativeMonoid A):
        forall v1 v2 : vector A n,
          VPermutation A n v1 v2 → Vfold_right f v1 z = Vfold_right f v2 z.
      Proof.
        intros v1 v2 V.
        induction V.
        -
          reflexivity.
        -
          simpl.
          rewrite IHV.
          reflexivity.
        -
          simpl.
          destruct f_mon, commonoid_mon, monoid_semigroup.
          repeat rewrite sg_ass.
          setoid_replace (y & x) with (x & y).
          reflexivity.
          apply commonoid_commutative.
        -
          auto.
      Qed.

    End Vec_Permutations.

    Lemma Fold_right_sig_wrap_equiv
          {n : nat}
          {A : Type}
          `{As: Setoid A}
          (f : A → A → A)
          {f_mor: Proper (equiv ==> equiv ==> equiv) f}
          (P : A → Prop)
          (f_P_closed: forall a b : A, P a → P b → P (f a b))
          (v : vector A n) (P1 : Vforall P v)
          (z : A) (Pz: P z):
      Vfold_right f v z =
      `
        (Vfold_right
           (λ xs ys : {x : A | P x},
                      f (` xs) (` ys) ↾ f_P_closed (` xs) (` ys) (proj2_sig xs) (proj2_sig ys))
           (Vsig_of_forall P1) (z ↾ Pz)).
    Proof.
      induction v.
      -
        crush.
      -
        simpl.
        rewrite IHv.
        reflexivity.
    Qed.

    Lemma ComutativeRMonoid_to_sig_CommutativeMonoid
          {A : Type}
          {Ae: Equiv A}
          (z : MonUnit A)
          (f : SgOp A)
          (P : SgPred A)
          (CMR: @CommutativeRMonoid A Ae f z P)
      :
        @CommutativeMonoid {x : A | P x} (@Sig_Equiv A Ae P)
                           (λ (xs ys : {x : A | P x}) (x:=` xs) (y:=` ys),
                            f x y ↾ rmonoid_plus_closed A x y (@proj2_sig A P xs) (@proj2_sig A P ys))
                           (z ↾ (rmonoid_unit_P _)).
    Proof.
      destruct CMR, comrmonoid_rmon, mon_restriction.

      split.
      split.
      split.
      -
        apply sig_setoid.
      -
        intros a b c.
        apply rmonoid_ass; auto.
      -
        unfold sg_op.
        simpl.
        simpl_relation.
        unfold equiv, Sig_Equiv in H; simpl in H.
        unfold equiv, Sig_Equiv in H0; simpl in H0.
        rewrite H, H0.
        reflexivity.
      -
        intros a.
        destruct a.
        apply rmonoid_left_id.
        auto.
      -
        intros a.
        destruct a.
        apply rmonoid_right_id.
        auto.
      -
        intros a b.
        destruct a,b.
        apply rcommutativity; auto.
    Qed.

    Lemma Vfold_VPermutation_CM
          {n : nat}
          {A: Type}
          `{As: Equiv A}
          (z : MonUnit A)
          (f : SgOp A)
          (P : SgPred A)
          (f_mon: CommutativeRMonoid A)
          (v1 v2 : vector A n)
          (P1: Vforall P v1)
          (P2: Vforall P v2):
      VPermutation A n v1 v2 -> Vfold_right f v1 z = Vfold_right f v2 z.
    Proof.
      intros V.

      pose(sz := z ↾ (rmonoid_unit_P _)).
      pose(sv1 := Vsig_of_forall P1).
      pose(sv2 := Vsig_of_forall P1).
      pose(sf:= fun (xs ys: sig P) =>
                  let x := proj1_sig xs in
                  let y := proj1_sig ys in
                  @exist A P (f x y)
                         (rmonoid_plus_closed _ x y (proj2_sig xs) (proj2_sig ys))
          ).

      assert(CA: @CommutativeMonoid (sig P) (Sig_Equiv) sf sz)
        by apply ComutativeRMonoid_to_sig_CommutativeMonoid.

      (* Not sure why Coq does not properly guess varables here... *)
      rewrite Fold_right_sig_wrap_equiv with (P0:=P) (Pz:=rmonoid_unit_P _) (f0:=f) (f_P_closed:=rmonoid_plus_closed _) (P3:=P1) by apply rsg_op_proper.
      rewrite Fold_right_sig_wrap_equiv with (P0:=P) (Pz:=rmonoid_unit_P _) (f0:=f) (f_P_closed:=rmonoid_plus_closed _) (P3:=P2) by apply rsg_op_proper.

      f_equiv.

      apply Vfold_VPermutation.
      apply CA.
      apply VPermutation_Vsig_of_forall, V.
    Qed.

    (* In SPIRAL it is called [Reduction_ISumReduction]
       TODO: Perhaps use [[https://argumatronic.com/posts/2019-06-21-algebra-cheatsheet.html#ring-like-structures][quazi-ring]] structure to describe 2 monoids?
     *)
    Theorem rewrite_Reduction_IReduction
            {i o n}

            (* Common unit for both monoids *)
            `{uf_zero: MonUnit CarrierA}

            (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n uf_zero)


            (* 1st Monoid. Used in reduction *)
            `{f: SgOp CarrierA}

            (* Monoid on restriction on f *)
            `{P: SgPred CarrierA}
            `{f_mon: @CommutativeRMonoid _ _ f uf_zero P}

            (* 2nd Monoid. Used in IUnion *)
            `{u: SgOp CarrierA}
            `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}

            (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family)
            (Upoz: Apply_Family_Vforall_P _ (liftRthetaP P) op_family)
            `{u_scompat: BFixpoint uf_zero u}
            `{f_scompat: BFixpoint uf_zero f}
      :

        (liftM_HOperator Monoid_RthetaFlags (@HReduction _ f uf_zero))
          ⊚ (@IUnion uf_zero i o n u _ u_scompat op_family)
        =
        SafeCast (IReduction f
                             (UnSafeFamilyCast
                                (SHOperatorFamilyCompose _ (liftM_HOperator Monoid_RthetaFlags (@HReduction _ f uf_zero)) op_family))).
    Proof.
      unfold SHOperatorFamilyCompose, SHCompose.
      unfold equiv, SHOperator_equiv, SHCompose; simpl.
      unfold UnSafeFamilyCast, get_family_op.
      simpl.
      (* Noramlized form. Diamond all around *)

      (* To use Diamond_f_subst_under_P we need to convert body_f back to operator family *)
      replace (λ (j : nat) (jc : j < n),
               op Monoid_RthetaFlags (op_family (mkFinNat jc))) with  (get_family_op _ op_family) by reflexivity.

      rewrite <- Diamond_f_subst_under_P with (f0:=f) (u0:=u) (P0:=P); auto ; try apply f_mon.
      clear u u_mon u_scompat.  (* No more 'u' *)
      clear Uz. (* Single non-unit per row constaint no longer needed *)

      apply ext_equiv_applied_equiv.
      -
        (* LHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply liftM_HOperator_impl_proper.
        apply HReduction_HOperator.
        typeclasses eauto.
        apply Diamond_proper.
        +
          apply f_mon.
        +
          reflexivity.
        + intros k kc.
          apply op_proper.
      -
        (* RHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply SafeCast'_proper.
        apply Diamond_proper.
        + apply f_mon.
        + reflexivity.
        + intros k kc.
          apply UnSafeCast'_proper.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          *
            apply liftM_HOperator_impl_proper.
            apply HReduction_HOperator.
            typeclasses eauto.
          *
            apply op_proper.
      -
        intros x.

        vec_index_equiv j jc.

        unfold SafeCast', rsvector2rvector, compose.
        unfold liftM_HOperator_impl, compose, sparsify.
        rewrite 2!Vnth_map.

        unfold HReduction, compose, HCOLImpl.Vectorize.
        rewrite Vnth_1.
        unfold UnSafeCast'.
        unfold compose.
        unfold rvector2rsvector.
        simpl.

        unfold densify.
        unfold HCOLImpl.Reduction.

        rewrite Vfold_right_Vmap.

        dep_destruct j; [idtac | crush].

        unfold Diamond.
        unfold Apply_Family'.
        unfold RStheta.
        rewrite AbsorbMUnionIndex_Vbuild.
        simpl.

        unfold UnionFold.
        unfold MUnion.

        rewrite RStheta2Rtheta_Vfold_left_rev_mkValue.
        f_equiv.

        unfold densify.
        rewrite Vmap_Vbuild.

        Local Opaque WriterMonadNoT.evalWriter.
        setoid_rewrite evalWriter_Rtheta2RStheta_mkValue_equiv.
        setoid_rewrite Vfold_right_Vmap_equiv.
        clear jc j.

        unfold rsvector2rvector.
        rewrite Vmap_map.

        replace (λ x0 : Rtheta, RStheta2Rtheta (Rtheta2RStheta x0)) with (@id Rtheta) by
            (extensionality z; rewrite RStheta2Rtheta_Rtheta2RStheta; reflexivity).
        setoid_rewrite Vmap_id.

        (* unfold Vec2Union. *)
        specialize (Upoz x).

        setoid_rewrite <- Vfold_right_Vmap_equiv.
        unfold Vec2Union.
        unfold SVector.Union.

        (* Get rid of [get_family_op] *)
        unfold get_family_op in *.

        eta_reduce_all.

        (* 1. In LHS push [evalWriter] all the way down to [get_family_op] *)

        rewrite eval_2D_Fold by apply f_mon.
        rewrite Vmap_Vbuild.

        assert(Upoz': forall (j : nat) (jc : j < n), Vforall P
                                                      (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                            (op Monoid_RthetaFlags (op_family (mkFinNat jc)) x))).
        {
          intros j jc.
          specialize (Upoz j jc).
          unfold liftRthetaP in Upoz.
          apply Vforall_map_intro in Upoz.
          apply Upoz.
        }
        clear Upoz. rename Upoz' into Upoz.


        (* TODO:  Manual generalization. Try to automate. See https://stackoverflow.com/questions/46458710/generalizing-expressions-under-binders   *)

        change (Vbuild
                  (λ (z : nat) (zi : z < n),
                   Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                        (op Monoid_RthetaFlags (op_family (mkFinNat zi)) x))) with (Vbuild
                                                                                                              (λ (z : nat) (zi : z < n),
                                                                                                               (fun p pi =>
                                                                                                                  (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                                                                                        (op Monoid_RthetaFlags (op_family (mkFinNat pi)) x))) z zi)).

        change (Vbuild
                  (λ (z : nat) (zi : z < n),
                   Vfold_right f
                               (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                     (op Monoid_RthetaFlags (op_family (mkFinNat zi)) x))
                               uf_zero)) with (Vbuild
                                                 (λ (z : nat) (zi : z < n),
                                                  Vfold_right f
                                                              ((fun p pi =>
                                                                  (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                                        (op Monoid_RthetaFlags (op_family (mkFinNat pi)) x))) z zi)
                                                              uf_zero)).

        revert Upoz.

        change (∀ (j : nat) (jc : j < n),
                   Vforall P
                           (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags)) (op Monoid_RthetaFlags (op_family (mkFinNat jc)) x))) with
            (∀ (j : nat) (jc : j < n),
                Vforall P
                        ((fun (p:nat) (pi:p<n) =>
                            (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags)) (op Monoid_RthetaFlags (op_family (mkFinNat pi)) x))) j jc)).

        generalize (fun (p:nat) (pi:p<n) =>
                      (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                            (op Monoid_RthetaFlags (op_family (mkFinNat pi)) x))) as gen.

        (* cleanup *)
        intros gen Upoz.
        clear x op_family i.
        rename o into m.
        eta_reduce_all.

        (* 2. Prove equality using RMonoid. *)

        set (rhs := Vfold_left_rev f _ _).
        set (lhs := Vfold_right _ _ _).

        assert(tmdn: forall t, t < m * n -> t / m < n).
        {
          intros t H.
          apply Nat.div_lt_upper_bound; auto.
          destruct m;auto.
          simpl in H.
          nat_lt_0_contradiction.
        }

        assert(tmm: forall t,t < m * n -> t mod m < m).
        {
          intros t H.
          apply Nat.mod_upper_bound.
          destruct m; auto.
          simpl in H.
          nat_lt_0_contradiction.
        }

        remember (Vbuild (λ (z : nat) (zi : z < n), Vfold_right f (gen z zi) uf_zero)) as lcols.
        assert(CP: Vforall P lcols).
        {
          clear rhs lhs tmdn tmm.
          subst lcols.
          apply Vforall_Vbuild.
          intros i ip.
          specialize (Upoz i ip).
          generalize dependent (gen i ip).
          intros v Upoz.
          clear i ip gen.
          apply (Vfold_right_under_P P).
          apply Upoz.
        }

        (* linear shaped equivalent of RHS *)
        pose (rnorm := Vfold_right f (Vbuild
                                        (fun (t:nat) (it:t < (m*n)) =>
                                           @Vnth CarrierA m
                                                 (gen (t/m) (tmdn t it))
                                                 (t mod m)
                                                 (tmm t it)
                                        )
                                     ) uf_zero ).

        assert(NR: rhs = rnorm).
        {
          subst rhs rnorm.
          clear lhs.
          rewrite (Vfold_right_left_rev_under_P P); try apply CP.

          induction n.
          -
            crush.
            destruct (Vbuild _).
            crush.
            specialize (tmdn 0 (Nat.lt_0_succ n)).
            nat_lt_0_contradiction.
          -
            dep_destruct lcols.
            simpl.
            pose (gen' := (fun p pc => gen (S p) (lt_n_S pc))).

            assert(Upoz': forall (j : nat) (jc : j < n), Vforall P (gen' j jc)).
            {
              intros j jc.
              subst gen'.
              apply Vforall_nth_intro.
              intros i ip.
              specialize (Upoz (S j) (lt_n_S jc)).
              apply Vforall_nth with (ip:=ip) in Upoz.
              apply Upoz.
            }

            simpl in CP.
            destruct CP as [Ph Px].

            assert(tmdn' : forall t : nat, t < m * n → t / m < n).
            {
              clear_all.
              intros t H.
              apply Nat.div_lt_upper_bound; auto.
              destruct m;auto.
              simpl in H.
              nat_lt_0_contradiction.
            }

            assert(tmm': forall t,t < m * n -> t mod m < m).
            {
              clear_all.
              intros t H.
              apply Nat.mod_upper_bound.
              destruct m; auto.
              simpl in H.
              nat_lt_0_contradiction.
            }

            specialize (IHn gen' Upoz' x).
            rewrite IHn with (tmdn:=tmdn') (tmm:=tmm');
              (rewrite Vbuild_Sn in Heqlcols;
               apply Vcons_eq_elim in Heqlcols;
               destruct Heqlcols as [Hh Hx]).
            clear IHn.
            +
              unfold gen'.
              subst h; remember (gen 0 (Nat.lt_0_succ n)) as h.
              remember (Vbuild (λ (t : nat) (it : t < m * n),
                                Vnth (gen (S (t / m)) (lt_n_S (tmdn' t it))) (tmm' t it))) as t.

              remember (Vbuild
                          (λ (t0 : nat) (it : t0 < m * S n), Vnth (gen (t0 / m) (tmdn t0 it)) (tmm t0 it))) as ht.
              assert (F: m * S n ≡ m + m * n) by lia.
              assert(C:m * S n ≡ m + m*n) by omega.
              clear F. (*TODO: weird shit. cleanup later *)
              replace (Vfold_right f ht uf_zero) with
                  (Vfold_right f
                               (@Vcast _ _ ht _ C)
                               uf_zero).
              replace (Vcast ht C) with (Vapp h t).
              apply (VFold_right_split_under_P P).
              *
                subst h.
                apply Upoz.
              *
                subst t.
                apply Vforall_Vbuild.
                intros i ip.
                apply Vforall_nth.
                apply Upoz.
              *
                subst.
                vec_index_equiv i ip.
                rewrite Vnth_app.
                break_match.
                --
                  rewrite Vbuild_nth.
                  rewrite Vnth_cast.
                  rewrite Vbuild_nth.

                  destruct (eq_nat_dec m 0) as [MZ | MNZ].
                  ++
                    (* Get rid of m=0 case *)
                    subst m.
                    simpl in *.
                    nat_lt_0_contradiction.
                  ++
                    assert (E: (i - m) mod m ≡ i mod m).
                    {
                      revert l MNZ; clear_all; intros H MNZ.
                      rewrite <- Nat.mod_add with (a:=i-m) (b:=1).
                      replace (i - m + 1 * m) with i by omega.
                      reflexivity.
                      apply MNZ.
                    }

                    Vnth_eq_index_to_val_eq.

                    (* m ≢ 0 *)
                    assert (E: S ((i - m) / m) ≡ i / m).
                    {
                      revert l MNZ; clear_all; intros H MNZ.
                      rewrite <- NatUtil.plus_1_S.
                      rewrite <- Nat.div_add by apply MNZ.
                      ring_simplify (i - m + 1 * m).
                      rewrite Nat.add_comm.
                      rewrite Nat.add_sub_assoc by apply H.
                      rewrite minus_plus.
                      reflexivity.
                    }

                    forall_n_lt_eq.
                --
                  rewrite Vnth_cast.
                  rewrite Vbuild_nth.
                  remember (gen 0 _) as lgen.
                  remember (gen (i/m) _) as rgen.
                  generalize (Vnth_cast_aux C ip).
                  intros gr.
                  replace lgen with rgen.
                  ++
                    apply Vnth_eq.
                    symmetry.
                    apply Nat.mod_small.
                    auto.
                  ++
                    subst.

                    assert (E: i/m ≡ 0) by apply Nat.div_small, g.
                    forall_n_lt_eq.
              *
                (* TODO: The following could be generalized as LTAC. Used in few more places in this proof. *)
                remember (Vcast _ _) as ht'.
                remember (m * S n) as Q.
                rewrite C in HeqQ.
                subst Q.
                subst.
                rewrite Vcast_refl.
                reflexivity.
            +
              subst x.
              reflexivity.
            +
              apply Px.
        }

        assert(tmn: forall t,t < m * n -> t mod n < n).
        {
          intros t H.
          apply Nat.mod_upper_bound.
          destruct n; auto.
          rewrite Nat.mul_0_r in H.
          nat_lt_0_contradiction.
        }

        assert(tndm: forall t, t < m * n -> t / n < m).
        {
          intros t H.
          apply Nat.div_lt_upper_bound; auto.
          destruct n;auto.
          rewrite Nat.mul_0_r in H.
          nat_lt_0_contradiction.
          rewrite Nat.mul_comm.
          apply H.
        }

        (* linear shaped equivalent of LHS *)
        pose (lnorm := Vfold_right f (Vbuild
                                        (fun (t:nat) (it:t < (m*n)) =>
                                           @Vnth CarrierA m
                                                 (gen (t mod n) (tmn t it))
                                                 (t/n) (tndm t it)
                                        )
                                     ) uf_zero ).

        assert(NL: lhs = lnorm).
        {
          subst lhs lnorm.
          clear rhs NR Heqlcols CP lcols rnorm tmm tmdn.

          rewrite (Vfold_right_left_rev_under_P (Vforall P (n:=m))).
          remember (Vfold_right _ (Vbuild gen) _) as lrows.
          induction m.
          +
            simpl.
            dep_destruct (Vbuild gen); crush.
          +
            pose (gen' := (fun p (pc:p<n) => Vtail (gen p pc))).

            assert(Upoz': forall (j : nat) (jc : j < n), Vforall P (gen' j jc)).
            {
              intros j jc.
              subst gen'.
              apply Vforall_nth_intro.
              intros i ip.
              rewrite Vnth_tail.
              eapply Vforall_nth in Upoz.
              apply Upoz.
            }

            assert(tmn' : forall t : nat, t < m * n → t mod n < n).
            {
              clear_all.
              intros t H.
              apply modulo_smaller_than_devisor.
              destruct n.
              rewrite Nat.mul_0_r in H.
              nat_lt_0_contradiction.
              auto.
            }

            assert(tndm' : forall t : nat, t < m * n → t / n < m).
            {
              clear_all.
              intros t H.
              destruct (eq_nat_dec n 0).
              -
                dep_destruct n.
                rewrite Nat.mul_0_r in H.
                nat_lt_0_contradiction.
                crush.
              -
                apply Nat.div_lt_upper_bound.
                assumption.
                rewrite Nat.mul_comm.
                apply H.
            }

            dep_destruct lrows.
            specialize (IHm gen' Upoz' tmn' tndm' x).
            simpl.
            rewrite_clear IHm.
            *
              rewrite Vbuild_Vapp.
              rewrite <- VFold_right_split_under_P.
              --
                rewrite VSn_eq in Heqlrows.
                Veqtac.
                replace (Vfold_right f (Vbuild (fun (t : nat) (tc : t < n) => Vnth (gen (t mod n) (tmn t (Nat.lt_lt_add_r t n (m * n) tc))) (tndm t (Nat.lt_lt_add_r t n (m * n) tc)))) uf_zero) with h.
                replace (Vbuild (fun (t : nat) (it : t < m * n) => Vnth (gen' (t mod n) (tmn' t it)) (tndm' t it))) with (Vbuild (fun (t : nat) (tc : t < m * n) => Vnth (gen ((t + n) mod n) (tmn (t + n) (add_lt_lt tc))) (tndm (t + n) (add_lt_lt tc)))).
                ++
                  reflexivity.
                ++
                  replace  (fun (t : nat) (tc : t < m * n) => Vnth (gen ((t + n) mod n) (tmn (t + n) (add_lt_lt tc))) (tndm (t + n) (add_lt_lt tc))) with (fun (t : nat) (it : t < m * n) => Vnth (gen' (t mod n) (tmn' t it)) (tndm' t it)).
                  reflexivity.
                  extensionality j.
                  extensionality jc.
                  unfold gen'.
                  rewrite Vnth_tail.
                  generalize (lt_n_S (tndm' j jc)).
                  generalize (tndm (j + n) (add_lt_lt jc)).
                  intros i0 i1.
                  remember ((j + n) / n) as Q.
                  replace ((j + n) / n) with (S (j / n)) in HeqQ.
                  subst Q.
                  rewrite (le_unique _ _ i1 i0). clear i1.
                  apply Vnth_arg_eq.
                  **
                    generalize (tmn' j jc).
                    generalize (tmn (j + n) (add_lt_lt jc)).
                    intros k0 k1.
                    remember ((j + n) mod n) as Q.
                    rewrite <- Nat.mul_1_l with (n:=n) in HeqQ at 1.
                    rewrite Nat.mod_add in HeqQ.
                    subst Q.
                    apply f_equal, le_unique.
                    crush.
                  **
                    rewrite <- Nat.mul_1_l with (n:=n) at 2.
                    rewrite Nat.div_add with (a:=j) (b:=1) (c:=n).
                    ring.
                    crush.
                ++
                  subst h.
                  clear x H1 gen' Upoz' tmn' tndm'.
                  apply Vhead_Vfold_right_Vmap2.
              --
                typeclasses eauto.
              --
                apply Vforall_Vbuild.
                intros i ip.
                apply Vforall_nth.
                auto.
              --
                apply Vforall_Vbuild.
                intros i ip.
                apply Vforall_nth.
                auto.
            *
              rewrite VSn_eq in Heqlrows.
              Veqtac.
              subst x.
              clear h H0.
              unfold gen'.
              apply Vtail_Vfold_right_Vmap2.
          +
            apply Vforall_Vbuild, Upoz.
        }

        rewrite NR, NL.
        clear  rhs lhs NR NL lcols Heqlcols CP.
        subst lnorm rnorm.
        (* TODO: prove that rnorm and lnorm are equaul being permutations *)

        pose (mat := fun y (yc:y<n) x (xc:x<m) => Vnth (gen y yc) xc).

        replace
          (Vbuild (fun (t : nat) (it : t < m * n) => Vnth (gen (t mod n) (tmn t it)) (tndm t it)))
          with
            (Vbuild (fun (t : nat) (it : t < m * n) =>
                       mat (t mod n) (tmn t it) (t/n) (tndm t it)
            )) by reflexivity.

        replace
          (Vbuild (fun (t : nat) (it : t < m * n) => Vnth (gen (t / m) (tmdn t it)) (tmm t it)))
          with
            (Vbuild (fun (t : nat) (it : t < m * n) => mat (t / m) (tmdn t it) (t mod m) (tmm t it))) by reflexivity.

        assert(Mpos: forall y (yc:y<n) x (xc:x<m), P (mat y yc x xc)).
        {
          intros y yc x xc.
          unfold mat.
          apply Vforall_nth.
          apply Upoz.
        }

        generalize dependent mat.
        intros mat Mpoz.
        clear Upoz gen.
        rename uf_zero into z.

        pose(lr := fun x => x/n+(x mod n)*m).
        assert(lrc: forall x (xc:x<m*n), lr x < m*n).
        {
          clear z f P f_mon f_scompat mat Mpoz.
          subst lr.
          intros x xc.
          assert(x mod n < n) by auto.
          assert(x/n < m) by auto.
          cbv beta.
          nia.
        }
        pose(lrm := IndexMap _ _ lr lrc).

        pose(rl := fun x => x/m + (x mod m)*n).
        assert(rlc: forall x (xc:x<m*n), rl x < m*n).
        {
          clear z f P f_mon f_scompat mat Mpoz.
          subst rl.
          intros x xc.
          assert(x mod m < m) by auto.
          assert(x/m < n) by auto.
          cbv beta.
          nia.
        }

        assert(RLR: forall x (xc:x<m*n), lr (rl x) ≡ x).
        {
          intros x xc.
          clear z f P f_mon f_scompat mat Mpoz lrm.
          subst lr rl.
          simpl in *.
          assert(NZ: n ≢ 0) by crush.
          assert(MZ: m ≢ 0) by crush.
          rewrite Nat.div_add; auto.
          rewrite Nat.div_div; auto.
          rewrite Nat.div_small; auto.
          rewrite Nat.add_0_l.
          rewrite Nat.add_mod; auto.
          rewrite Nat.mod_mul; auto.
          rewrite Nat.add_0_r.
          rewrite Nat.mod_mod; auto.
          setoid_rewrite Nat.mod_small at 2; auto.
          symmetry.
          rewrite Nat.add_comm.
          rewrite Nat.mul_comm.
          apply Nat.div_mod; auto.
        }

        assert(LRL: forall x (xc:x<m*n), rl (lr x) ≡ x).
        {
          intros x xc.
          clear z f P f_mon f_scompat mat Mpoz lrm RLR.
          subst lr rl.
          simpl in *.
          assert(NZ: n ≢ 0) by crush.
          assert(MZ: m ≢ 0) by crush.
          rewrite Nat.div_add; auto.
          rewrite Nat.div_div; auto.
          rewrite Nat.div_small; try lia.
          rewrite Nat.add_0_l.
          rewrite Nat.add_mod; auto.
          rewrite Nat.mod_mul; auto.
          rewrite Nat.add_0_r.
          rewrite Nat.mod_mod; auto.
          setoid_rewrite Nat.mod_small at 2; auto.
          symmetry.
          rewrite Nat.add_comm.
          rewrite Nat.mul_comm.
          apply Nat.div_mod; auto.
        }

        remember (λ (t : nat) (it : t < m * n), mat (t mod n) (tmn t it) (t / n) (tndm t it)) as l.
        remember (λ (t : nat) (it : t < m * n), mat (t / m) (tmdn t it) (t mod m) (tmm t it)) as r.

        pose(rlm := IndexMap _ _ rl rlc).
        assert(RLMB: index_map_bijective rlm).
        {
          clear z f P f_mon f_scompat mat Mpoz Heql Heqr.
          split.
          -
            (* injectivity *)
            unfold index_map_injective.
            intros x y xc yc H.
            simpl in *.
            clear rlm.

            rewrite <- RLR by apply yc.
            replace x with (lr (rl x)) by apply RLR, xc.
            rewrite H.
            reflexivity.
          -
            (* surjectivity *)
            unfold index_map_surjective.
            intros y yc.
            simpl in *.
            clear lrm RLR.
            exists (lr y).
            eexists.
            + apply (lrc y), yc.
            + apply LRL, yc.
        }

        replace (Vbuild r) with (Vbuild (fun t it => l (⟦ rlm ⟧ t) (« rlm » t it))).
        *
          remember (Vbuild l) as b1.
          remember (Vbuild (λ (t : nat) (it : t < m * n), l (⟦ rlm ⟧ t) (« rlm » t it))) as b2.
          assert(VPermutation CarrierA (m*n) b1 b2).
          {
            subst b1 b2.
            apply Vbuild_permutation with (t:=rlm).
            auto.
          }
          assert(Bb1: Vforall P (b1)).
          {
            subst b1.
            apply Vforall_Vbuild.
            intros i ip.
            subst l.
            apply Mpoz.
          }
          assert(Bb2: Vforall P (b2)).
          {
            subst b2.
            apply Vforall_Vbuild.
            intros i ip.
            subst l.
            apply Mpoz.
          }
          apply Vfold_VPermutation_CM with (P0:=P); assumption.
        *
          vec_index_equiv i ip.
          rewrite 2!Vbuild_nth.
          subst r l rl.
          simpl.
          assert (YE: (i / m + i mod m * n) mod n ≡ i/m).
          {
            assert(NZ: n ≢ 0) by crush.
            assert(MZ: m ≢ 0) by crush.
            rewrite Nat.add_mod; auto.
            rewrite Nat.mod_mul; auto.
            rewrite Nat.add_0_r.
            rewrite Nat.mod_mod; auto.
            setoid_rewrite Nat.mod_small; auto.
          }

          assert (XE: (i / m + i mod m * n) / n ≡ i mod m).
          {
            assert(NZ: n ≢ 0) by crush.
            assert(MZ: m ≢ 0) by crush.
            rewrite Nat.div_add; auto.
            rewrite Nat.div_div; auto.
            rewrite Nat.div_small; try lia.
          }

          forall_nm_lt_eq.
    Qed.

    Global Instance max_Assoc:
      @Associative CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec).
    Proof.
      unfold Associative, HeteroAssociative.
      intros x y z.
      unfold max, sort.
      repeat break_if; unfold snd in *; crush.
      clear Heqd Heqd0 Heqd1 Heqd2.
      clear_dups.
      apply le_flip in n.
      apply le_flip in n0.
      apply eq_iff_le.
      auto.
    Qed.

    Global Instance max_Comm:
      @Commutative CarrierA CarrierAe CarrierA (@max CarrierA CarrierAle CarrierAledec).
    Proof.
      unfold Commutative.
      intros x y.
      unfold max, sort.
      repeat break_if; unfold snd; auto.
      -
        apply eq_iff_le; auto.
      -
        clear Heqd Heqd0.
        apply le_flip in n.
        apply le_flip in n0.
        apply eq_iff_le.
        auto.
    Qed.

    Section NN.
      (* Non-negative CarrierA subtype *)

      Global Instance NN:
        SgPred CarrierA := CarrierAle CarrierAz.

      Global Instance RMonoid_max_NN:
        @RMonoid CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
      Proof.
        repeat split; try typeclasses eauto.
        -
          (* zero in P *)
          unfold sg_P, mon_unit, NN.
          reflexivity.
        -
          (* closed *)
          intros a b M0 M1.
          unfold sg_op, max, equiv, mon_unit, sort.
          break_if; crush.
        -
          (* assoc *)
          intros x y z H H0 H1.
          unfold sg_op, max, sort.
          repeat break_if; unfold snd in *; crush.
          clear Heqd Heqd0 Heqd1 Heqd2.
          clear_dups.
          apply le_flip in n0.
          apply le_flip in n.
          apply eq_iff_le.
          auto.
        -
          (* left_unit *)
          intros y H.
          unfold sg_op, max, equiv, mon_unit, sort.
          break_if; crush.
        -
          (* right_unit *)
          intros x H.
          unfold sg_op, max, equiv, mon_unit, sort.
          break_if; crush.
          unfold le in l.
          apply eq_iff_le.
          auto.
      Qed.

      Global Instance CommutativeRMonoid_max_NN:
        @CommutativeRMonoid CarrierA CarrierAe (@minmax.max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
      Proof.
        split.
        -
          apply RMonoid_max_NN.
        -
          (* commutativity *)
          intros x y H H0.
          apply max_Comm.
      Qed.

    End NN.

    (* Specialized version of rewrite_Reduction_IReduction *)
    Theorem rewrite_Reduction_IReduction_max_plus
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n zero)
          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family)
          (Upoz: Apply_Family_Vforall_P _ Is_NonNegative op_family)
      :
        (liftM_HOperator Monoid_RthetaFlags (@HReduction _ max zero))
          ⊚ (ISumUnion op_family)
        =
        SafeCast (IReduction max
                             (UnSafeFamilyCast
                                (SHOperatorFamilyCompose _ (liftM_HOperator Monoid_RthetaFlags (@HReduction _ max zero)) op_family))).
    Proof.
      unfold ISumUnion.

      (* TODO: see if I can get rid of proof_irreleance here *)
      replace (@sg_op_proper _ _ _ _) with (@rsg_op_proper CarrierA CarrierAe max zero NN
                                                           (@comrmonoid_rmon CarrierA CarrierAe max zero NN CommutativeRMonoid_max_NN)) by apply proof_irrelevance.

      replace CarrierAPlus_proper with (@sg_op_proper CarrierA CarrierAe CarrierAplus
                                                      (@monoid_semigroup CarrierA CarrierAe CarrierAplus zero
                                                                         (@commonoid_mon CarrierA CarrierAe CarrierAplus zero CommutativeMonoid_plus_zero))) by apply proof_irrelevance.

      eapply rewrite_Reduction_IReduction ; auto.
    Qed.

    (* Variant of SPIRAL's `rewrite_ISumXXX_YYY` rule for [IReduction] and [GatH]
and `ISumReduction_PointWise` *)
    Theorem rewrite_IReduction_absorb_operator
            (i0 i o n:nat)
            (z: CarrierA)
            (f: CarrierA -> CarrierA -> CarrierA)
            (f_mor: Proper (equiv ==> equiv ==> equiv) f)
            (F: @SHOperatorFamily Monoid_RthetaSafeFlags i o n z)
            (G: @SHOperator Monoid_RthetaSafeFlags i0 i z)
            `{scompat: BFixpoint z f}
      :
        SHCompose _
                  (@IReduction z i o n f _ scompat F)
                  G
        =
        @IReduction z i0 o n f _ scompat
                    (SHFamilyOperatorCompose _
                                             F
                                             G).
    Proof.
      unfold IReduction, SHFamilyOperatorCompose, SHCompose, compose.
      unfold equiv, SHOperator_equiv.
      simpl.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite <- E. clear y E.
      unfold get_family_op.
      simpl.
      reflexivity.
    Qed.

    Lemma SHPointwise_impl_distr_over_Scatter_impl
          {fm : Monoid RthetaFlags}
          {o i : nat}
          (pf : CarrierA → CarrierA)
          (pf_mor : Proper (equiv ==> equiv) pf)
          (pfzn: pf zero = zero) (* function with the fixed point 0 *)
          (v : svector fm i)
          (f : index_map i o)
          (f_inj : index_map_injective f):
      SHPointwise_impl (IgnoreIndex pf) (@Scatter_impl fm _ _ f f_inj zero v) =
      @Scatter_impl fm _ _ f f_inj zero (SHPointwise_impl (IgnoreIndex pf) v).
    Proof.
      vec_index_equiv j jc.
      rewrite SHPointwise_impl_nth.
      unfold equiv, Rtheta'_equiv.
      rewrite evalWriter_mkValue.
      (* unfold IgnoreIndex, const. *)

      destruct (in_range_dec f j) as [R | NR].
      -
        (* `j` in dense position *)
        unfold Scatter_impl.
        simpl.
        rewrite 2!Vbuild_nth.
        break_match; auto.
        unfold IgnoreIndex, const.
        rewrite SHPointwise_impl_nth.
        rewrite evalWriter_mkValue.
        reflexivity.
      -
        (* `j` in sparse position *)
        remember (@Scatter_impl fm _ _ f f_inj zero v) as s0.
        assert(VZ0: Is_ValZero (Vnth s0 jc)).
        {
          subst s0.
          apply Scatter_impl_Unit_at_sparse; assumption.
        }
        setoid_replace (WriterMonadNoT.evalWriter (Vnth s0 jc) ) with CarrierAz.
        2: {
          rewrite Is_ValZero_to_mkSZero in VZ0.
          rewrite_clear VZ0.
          rewrite evalWriter_Rtheta_SZero.
          reflexivity.
        }

        rewrite pfzn.
        remember (@Scatter_impl fm _ _ f _ zero (SHPointwise_impl (IgnoreIndex pf) v)) as s1.
        assert(VZ1: Is_ValZero (Vnth s1 jc)).
        {
          subst s1.
          apply Scatter_impl_Unit_at_sparse; assumption.
        }
        setoid_replace (WriterMonadNoT.evalWriter (Vnth s1 jc) ) with CarrierAz.
        reflexivity.
        rewrite Is_ValZero_to_mkSZero in VZ1.
        rewrite_clear VZ1.
        rewrite evalWriter_Rtheta_SZero.
        reflexivity.
    Qed.

    (* TODO: see if [zero] could be generelized here to [svalue]. Also
     see if there is a Monoid-like alebraic structure [(A,pf,svalue)] *)
    Theorem rewrite_PointWise_ScatHUnion
          {fm: Monoid RthetaFlags}

          (* -- SE params -- *)
          {n i o ki ko}
          (* Kernel *)
          (kernel: @SHOperatorFamily fm ki ko n zero)
          (* Scatter index map *)
          (f: index_map_family ko o n)
          {f_inj : index_map_family_injective f}
          (* Gather index map *)
          (g: index_map_family ki i n)

          (* -- Scatter params -- *)
          (pf: CarrierA -> CarrierA)
          `{pf_mor: !Proper ((=) ==> (=)) pf}
          (pfzn: pf zero = zero) (* function with the fixed point 0 *)
      :
        SHOperatorFamilyCompose fm
                                (SHPointwise fm (IgnoreIndex pf))
                                (SparseEmbedding fm kernel f g (f_inj:=f_inj))
        =
        SparseEmbedding fm
                        (SHOperatorFamilyCompose fm
                                                 (SHPointwise fm (IgnoreIndex pf))
                                                 kernel)
                        f g (f_inj:=f_inj).
    Proof.
      unfold SHOperatorFamilyCompose, IReduction, SafeCast, equiv, SHOperatorFamily_equiv, pointwise_relation, SHOperator_equiv, Diamond.
      intros [j jc].
      simpl.
      unfold SparseEmbedding, SHCompose, compose, equiv, ext_equiv, mkFinNat.
      intros x y E.
      simpl.
      rewrite_clear E.
      apply SHPointwise_impl_distr_over_Scatter_impl, pfzn.
      apply pf_mor.
    Qed.

    Theorem rewrite_Reduction_ScatHUnion
          {n m:nat}
          {fm: Monoid RthetaFlags}

          `{g: SgOp CarrierA}
          `{mzero: MonUnit CarrierA}
          `{P: SgPred CarrierA}
          `(g_mon: @CommutativeRMonoid _ _ g mzero P)

          (F: @SHOperator fm m 1 mzero)
          (f:index_map 1 (S n))
          (f_inj: index_map_injective f)
          (FP: op_Vforall_P fm (liftRthetaP P) F)
      :
        SHCompose fm
                  (SHCompose fm
                             (liftM_HOperator fm (HReduction g mzero))
                             (Scatter fm f (f_inj:=f_inj)))
                  F
        =
        F.
    Proof.
      unfold_Rtheta_equiv.
      unfold SHOperator_equiv.
      unfold SHCompose.
      simpl.
      unfold compose.
      intros x y E.
      rewrite <- E; clear y E.
      specialize (FP x).

      generalize dependent (op fm F x).
      intros y FP.
      clear x F.

      vec_index_equiv j jc.
      unfold liftM_HOperator_impl, compose.
      rewrite Vnth_sparsify.
      unfold densify.

      induction n.
      +
        simpl.
        break_match; simpl.
        *
          unfold Scatter_impl.
          rewrite Vbuild_Sn.
          simpl.
          unfold decide.
          break_match; simpl.
          --
            rewrite Vnth_0 ; clear j jc Heqn.
            rewrite Vnth_1_Vhead.
            unfold HCOLImpl.Reduction.
            simpl.
            apply Vforall_Vhead in FP.
            destruct g_mon, comrmonoid_rmon.
            rewrite rmonoid_right_id; try auto.
            rewrite mkValue_evalWriter.
            reflexivity.
          --
            contradiction n.
            apply in_range_exists; auto.
            eexists 0.
            eexists; auto.
            destruct f.
            simpl in *.
            assert(index_f 0 < 1).
            {
              apply index_f_spec.
              auto.
            }

            clear Heqd.
            dep_destruct (index_f 0).
            reflexivity.
            omega.
        *
          crush.
      +
        remember (S n) as sn.
        erewrite Scatter_impl_1_Sn.

        break_match.
        *
          simpl.
          break_match.
          --
            unfold HCOLImpl.Reduction.
            rewrite Vmap_Vconst.
            simpl.
            match goal with
            | [ |- context[g _ ?f]] => setoid_replace f with mzero
            end.
            ++
              destruct g_mon eqn:H1, comrmonoid_rmon eqn:H2.
              rewrite rmonoid_right_id.
              rewrite mkValue_evalWriter.
              rewrite Vnth_0.
              reflexivity.
              apply Vforall_Vhead.
              apply FP.
            ++
              symmetry.
              clear IHn f f_inj e j jc Heqn0 Heqsn.
              induction sn.
              ** crush.
              ** simpl.
                 rewrite <- IHsn.
                 destruct g_mon eqn:H1, comrmonoid_rmon eqn:H2.
                 rewrite rmonoid_left_id; auto.
                 apply mon_restriction.
          --
            crush.
        *
          erewrite <- IHn with (f:=shrink_index_map_1_range f n0).
          f_equiv.
          apply Vnth_arg_equiv.
          rewrite Vmap_cons.
          unfold HReduction, compose.
          unfold HCOLImpl.Reduction.
          simpl.

          destruct g_mon eqn:H1, comrmonoid_rmon eqn:H2.
          rewrite evalWriter_mkStruct.
          rewrite rmonoid_left_id.
          --
            reflexivity.
          --
            apply Vfold_right_under_P; auto.
            apply Vforall_nth_intro.
            intros i ip.

            assert(H: Vforall (fun p => (Vin p y) \/ (p ≡ mkStruct mzero))
                              (@Scatter_impl fm _ _ (shrink_index_map_1_range f n0)
                                        (shrink_index_map_1_range_inj f n0 f_inj)
                                        mzero y)) by apply Scatter_impl_is_almost_endomorphism.
            apply Vforall_nth with (ip:=ip) in H.
            destruct H.
            ++
              apply Vin_1 with (v:=y) in H.
              rewrite Vnth_map.
              rewrite H.
              apply Vforall_Vhead.
              apply FP.
            ++
              rewrite Vnth_map.
              rewrite H.
              apply mon_restriction.
    Qed.

    Theorem rewrite_Reduction_ScatHUnion_max_zero
          (n m: nat)
          (fm: Monoid.Monoid RthetaFlags)
          (F: @SHOperator fm m 1 zero)
          (f: index_map 1 (S n))
          (f_inj: index_map_injective f)
          (FP: op_Vforall_P fm Is_NonNegative F)
      :
        SHCompose fm
                  (SHCompose fm
                             (liftM_HOperator fm (HReduction minmax.max zero))
                             (Scatter fm f (f_inj:=f_inj)))
                  F
        =
        F.
    Proof.
      replace (@Is_NonNegative fm) with (@liftRthetaP fm NN) in FP by auto.
      apply (rewrite_Reduction_ScatHUnion CommutativeRMonoid_max_NN F f f_inj FP).
    Qed.

    Theorem rewrite_GathH_GathH
            {fm}
            {svalue: CarrierA}
            {i o t: nat}
            {b0 b1 s0 s1: nat}
            {bound0}
            {bound1}
      :
        SHCompose fm
                  (@GathH fm svalue t o b0 s0 bound0)
                  (@GathH fm svalue i t b1 s1 bound1)
        =
        GathH fm (b1+b0*s1) (s0*s1)
              (domain_bound:=h_index_map_compose_range_bound bound0 bound1).
    Proof.
      unfold SHCompose.
      unfold GathH.
      unfold equiv, SHOperator_equiv.
      simpl.

      rewrite Gather_impl_composition.
      rewrite h_index_map_compose.
      apply Gather_impl_proper.
      reflexivity.
    Qed.

    (*
     Motivating example:

    SHPointwise fm (IgnoreIndex abs) ⊚
    SHBinOp fm (SwapIndex2 j (IgnoreIndex2 sub))

     *)
    Global Instance FinNat_f1_over_g2_proper
           {n: nat}
           (f: FinNat n -> CarrierA -> CarrierA)
           (g: FinNat n -> CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=)) f}
          `{pG: !Proper ((=) ==> (=) ==> (=) ==> (=)) g}
      :
        Proper (equiv ==> equiv ==> equiv ==> equiv)
               (λ (i : FinNat n) (a b : CarrierA), f i (g i a b)).
    Proof.
      solve_proper.
    Qed.

    Theorem rewrite_PointWise_BinOp
            {fm}
            {svalue:CarrierA}
            (n: nat)
            (f: FinNat n -> CarrierA -> CarrierA)
            `{pF: !Proper ((=) ==> (=) ==> (=)) f}
            (g: FinNat n -> CarrierA -> CarrierA -> CarrierA)
            `{pG: !Proper ((=) ==> (=) ==> (=) ==> (=)) g}
      :
        SHCompose fm (svalue:=svalue)
                  (SHPointwise fm f)
                  (SHBinOp fm g) =
        SHBinOp fm (fun i a b => f i (g i a b)).
    Proof.

      unfold equiv, SHOperator_equiv.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite <- E. clear E.
      vec_index_equiv j jc.

      unfold SHCompose, compose, equiv, SHOperator_equiv; simpl.
      unfold SHPointwise_impl.
      rewrite Vbuild_nth.

      assert(jc1: j<n+n) by omega.
      assert(jc2: (j+n) < (n+n)) by omega.
      setoid_rewrite SHBinOp_impl_nth with (jc1:=jc1) (jc2:=jc2).
      unfold Rtheta'_equiv.
      rewrite evalWriter_Rtheta_liftM.
      rewrite 2!evalWriter_Rtheta_liftM2.
      unfold mkFinNat.
      reflexivity.
    Qed.

    Lemma terminate_ScatHUnion1
          {fm: Monoid RthetaFlags}
          {o b s: nat}
          {z: CarrierA}
          (bc: b<o)
          {range_bound: forall x : nat, x < 1 → b + x * s < o}
          {snzord: s ≢ 0 ∨ 1 < 2}
      :
        ScatH fm (svalue:=z) b s
              (snzord0 := snzord) (* Also `or_intror Nat.lt_1_2` *)
              (range_bound:=range_bound)
        = Embed fm bc.
    Proof.
      unfold equiv, ext_equiv, SHOperator_equiv.
      unfold equiv, ext_equiv.
      intros x y Exy.
      vec_index_equiv j jc.
      simpl.

      unfold Embed_impl.
      rewrite Vbuild_nth.
      break_if.
      +
        rewrite Vhead_nth.
        rewrite Scatter_impl_spec with
            (idv  := z)
            (f    := @h_index_map (S O) o b s range_bound)
            (f_inj:= @h_index_map_is_injective (S O) o b s range_bound snzord).
        unfold VnthIndexMapped.
        apply Vnth_equiv.
        *
          subst.
          simpl.
          ring_simplify.
          reflexivity.
        *
          rewrite_clear Exy.
          reflexivity.
      +
        unfold Scatter_impl.
        rewrite Vbuild_nth.
        break_match.
        *
          exfalso.
          eapply in_range_of_h in i; try assumption.
          destruct i as [i [ic H]].
          destruct i.
          -- ring_simplify in H.
             congruence.
          -- lia.
        *
          reflexivity.
    Qed.

    (* Special `n by n` family of sequentially indexed `Pick` operators *)
    Definition Pickn
               {fm}
               {svalue: CarrierA}
               (n:nat)
      : @SHOperatorFamily fm n 1 n svalue := fun jf => Pick _ (proj2_sig jf).

    Theorem terminate_Reduction
            {n}
            (f: CarrierA -> CarrierA -> CarrierA)
            `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
            `{f_comm: @Commutative CarrierA _ CarrierA f}
            (idv: CarrierA)
            `{scompat : BFixpoint idv f}
      :
        liftM_HOperator Monoid_RthetaSafeFlags (HReduction f idv)
        =
        IReduction f (svalue:=idv) (Pickn n).
    Proof.
      unfold IReduction, liftM_HOperator,liftM_HOperator_impl.
      unfold compose, sparsify, densify.
      unfold equiv,SHOperator_equiv.
      simpl.
      unfold Diamond.
      unfold equiv, ext_equiv.
      intros x y H.
      unfold HCOLImpl.Reduction.
      rewrite Vfold_right_Vmap.
      unfold MUnion.
      apply vector1_equiv_Vhead_equiv.
      unfold Apply_Family'.
      simpl.

      induction n.
      -
        dep_destruct x.
        dep_destruct y.
        simpl.
        unfold equiv, Rtheta'_equiv.
        rewrite evalWriter_mkValue.
        rewrite evalWriter_mkStruct.
        reflexivity.
      -
        VSntac x.
        VSntac y.
        rewrite Vfold_right_cons.

        unfold compose in *.
        rewrite mkValue_RStheta_dist_liftM2 by apply f_mor.
        unshelve rewrite IHn with (x:=Vtail x) (y:=Vtail y).
        *
          clear IHn.
          rewrite Vbuild_Sn.
          rewrite Vfold_left_rev_cons.
          unfold Vec2Union.
          unfold SVector.Union.
          Opaque Monad.liftM2.
          simpl.
          remember (Monad.liftM2 f) as lf.
          assert(Commutative lf).
          {
            intros a b.
            subst lf.
            unfold equiv, RStheta_equiv, Rtheta'_equiv.
            rewrite 2!evalWriter_Rtheta_liftM2.
            apply f_comm.
          }
          rewrite commutativity.
          subst lf.
          f_equiv; auto.
          --
            f_equiv.
            eapply Vfold_left_rev_proper.
            {
              intros a b Hab c d Hcd.
              apply Vcons_single_elim.
              rewrite Hab, Hcd.
              reflexivity.
            }
            reflexivity.
            vec_index_equiv j jc.
            rewrite 2!Vbuild_nth.
            unfold get_family_op.
            simpl.
            unfold Pick_impl.
            apply Vcons_single_elim.
            rewrite <- Vnth_tail.
            reflexivity.
          --
            rewrite H.
            apply mkValue_evalWriter.
        *
          rewrite H.
          reflexivity.
    Qed.


    Fact GathH1_domain_bound_to_base_bound
      {i base stride: nat}
      : (forall x : nat, x < 1 → base + x * stride < i) -> base < i.
    Proof.
      intros H.
      specialize (H 0).
      lia.
    Qed.

    Theorem terminate_GathH1
            {i: nat}
            {svalue: CarrierA}
            {fm}
            (base stride: nat)
            {domain_bound: ∀ x : nat, x < 1 → base + x * stride < i}
      :
        @GathH fm svalue i 1 base stride domain_bound = @Pick fm svalue i base (GathH1_domain_bound_to_base_bound domain_bound).
    Proof.
      unfold GathH.
      unfold equiv, SHOperator_equiv.
      unfold equiv, ext_equiv.
      intros x y H.
      simpl.

      unfold Pick_impl.
      vec_index_equiv j jc.
      destruct j.
      -
        rewrite Gather_impl_spec.
        unfold VnthIndexMapped.
        simpl.
        apply Vnth_equiv.
        + rewrite <- plus_n_O; reflexivity.
        + apply H.
      -
        omega.
    Qed.

    Lemma Vfold_left_rev_Vbuild_zeroes
          `{Ae: !Equiv A}

          `{z: MonUnit A}
          `{f: SgOp A}
          `{f_mon: @MathClasses.interfaces.abstract_algebra.Monoid _ _ f z}

          {o: nat}
      :
        Vfold_left_rev f z (Vbuild (λ (i0 : nat) (_ : i0 < o), z)) = z.
    Proof.
      induction o.
      --
        simpl.
        reflexivity.
      --
        rewrite Vbuild_Sn.
        Opaque Vbuild.
        simpl.
        rewrite IHo; clear IHo.
        apply monoid_left_id, f_mon.
    Qed.

    Lemma Vfold_left_rev_Vbuild_single
          `{Ae: !Equiv A}
          (x: A)
          (o j: nat)
          {jc: j<o}
          `{z: MonUnit A}
          `{f: SgOp A}
          `{f_mon: @MathClasses.interfaces.abstract_algebra.Monoid _ _ f z}
      :
        Vfold_left_rev f z
                       (Vbuild
                          (λ (i0 : nat) (ic : i0 < o),
                           if Nat.eq_dec j i0 then x else z)) = x.
    Proof.
      dependent induction o.
      -
        nat_lt_0_contradiction.
      -
        rewrite Vbuild_Sn.
        Opaque Vbuild.
        simpl.
        destruct j.
        simpl.
        rewrite Vfold_left_rev_Vbuild_zeroes;auto.
        apply monoid_left_id, f_mon.

        break_if; try congruence.
        destruct f_mon eqn:F.
        rewrite monoid_right_id.
        replace (fun (i : nat) (_ : i < o) => if Nat.eq_dec (S j) (S i) then x else z)
          with
            (fun (i : nat) (_ : i < o) => if Nat.eq_dec j i then x else z).
        specialize (IHo j (lt_S_n jc) z f).
        rewrite IHo.
        reflexivity.
        apply f_mon.
        extensionality p.
        extensionality pc.
        break_if.
        break_if.
        reflexivity.
        congruence.
        break_if.
        congruence.
        reflexivity.
    Qed.

    (* TODO: move *)
    Lemma Rtheta'_lift_Monoid
          (z : MonUnit CarrierA)
          (f : SgOp CarrierA)
          (f_mon: @abstract_algebra.Monoid CarrierA CarrierAe f z)
      :
        @abstract_algebra.Monoid (Rtheta' Monoid_RthetaFlags)
                                 (@Rtheta'_equiv Monoid_RthetaFlags)
                                 (@Monad.liftM2 (Monad_RthetaFlags Monoid_RthetaFlags)
                                                (@WriterMonad.Monad_writerT RthetaFlags Monoid_RthetaFlags
                                                                            IdentityMonad.ident IdentityMonad.Monad_ident) CarrierA CarrierA
                                                CarrierA f)
                                 (@mkStruct Monoid_RthetaFlags z).
    Proof.
      repeat split; try typeclasses eauto.
      -
        unfold sg_op.
        unfold Associative, HeteroAssociative.
        intros a b c.
        unfold equiv, Rtheta'_equiv.
        repeat rewrite evalWriter_Rtheta_liftM2.
        apply sg_ass, f_mon.
      -
        unfold sg_op.
        solve_proper.
      -
        unfold LeftIdentity, sg_op, mon_unit.
        intros a.
        unfold equiv, Rtheta'_equiv.
        rewrite evalWriter_Rtheta_liftM2.
        rewrite evalWriter_mkStruct.
        apply monoid_left_id, f_mon.
      -
        unfold RightIdentity, sg_op, mon_unit.
        intros a.
        unfold equiv, Rtheta'_equiv.
        rewrite evalWriter_Rtheta_liftM2.
        rewrite evalWriter_mkStruct.
        apply monoid_right_id, f_mon.
    Qed.

    Lemma terminate_GathHN_generic
          {i o: nat}
          `{z: MonUnit CarrierA}
          `{f: SgOp CarrierA}
          `{f_mon: @MathClasses.interfaces.abstract_algebra.Monoid _ _ f z}
          (base stride: nat)
          {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
          `{scompat : BFixpoint z f}
      :
        @GathH _ z i o base stride domain_bound
        =
        @IUnion z i o o f _ _ (fun jf =>
                                SHCompose _
                                          (@Embed _ z o (proj1_sig jf) (proj2_sig jf))
                                          (@Pick _ z i (base+(proj1_sig jf)*stride) (domain_bound (proj1_sig jf) (proj2_sig jf))
                                          )
                             ).
    Proof.
      unfold GathH.
      unfold equiv, SHOperator_equiv.
      simpl.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite <- E; clear y E.
      vec_index_equiv j jc.
      rewrite Gather_impl_spec.
      unfold VnthIndexMapped.
      unfold Diamond.
      unfold Apply_Family'.
      rewrite AbsorbMUnionIndex_Vbuild.
      unfold get_family_op.
      simpl.

      unfold UnionFold.
      unfold Embed_impl, compose, Pick_impl.
      setoid_rewrite Vbuild_nth.
      simpl.
      match goal with
      | [|- context[Vnth x ?o]] => generalize o; intros l
      end.
      unfold SVector.Union.
      symmetry.
      replace (λ (i0 : nat) (ic : i0 < o),
               if Nat.eq_dec j i0 then Vnth x (domain_bound i0 ic) else mkStruct z)
        with
          (λ (i0 : nat) (ic : i0 < o),
           if Nat.eq_dec j i0 then Vnth x l else mkStruct z).

      apply Vfold_left_rev_Vbuild_single.
      apply jc.
      apply Rtheta'_lift_Monoid, f_mon.
      extensionality p.
      extensionality pc.
      break_if.
      apply Vnth_eq; auto.
      reflexivity.
    Qed.

    Theorem terminate_GathHN
            {i o: nat}
            (base stride: nat)
            {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
      :
        @GathH _ zero i o base stride domain_bound
        =
        @ISumUnion i o o  (fun jf =>
                             SHCompose _
                                       (@Embed _ zero o _ (proj2_sig jf))
                                       (@Pick _ zero i (base+(proj1_sig jf)*stride) (domain_bound _ (proj2_sig jf))
                                       )
                   ).
    Proof.
      (* This lemma is just a special case of more generic lemma *)
      eapply terminate_GathHN_generic.
    Qed.

    Global Instance mult_by_nth_proper
           {n:nat}
           (a: vector CarrierA n)
      : Proper (equiv ==> equiv ==> equiv) (mult_by_nth a).
    Proof.
      unfold mult_by_nth.
      intros i j Eij x y Exy.
      rewrite_clear Exy.
      f_equiv.
      apply Vnth_eq.
      inversion Eij; auto.
    Qed.

    (*
      In our original HCOL proof we used slughly different fomulation of operators/rules which required this rule to bring it back to original SPIRAL's formulation.
     *)
    Lemma SHBinOp_HPrepend_SHPointwise
          {n: nat}
          {svalue: CarrierA}
          (a : vector CarrierA n)
      :
        SHBinOp (svalue:=svalue) Monoid_RthetaFlags (IgnoreIndex2 mult) ⊚ liftM_HOperator Monoid_RthetaFlags (HPrepend a) =
        SHPointwise Monoid_RthetaFlags (mult_by_nth a).
    Proof.
      unfold SHCompose, equiv, SHOperator_equiv.
      simpl.

      unfold compose, liftM_HOperator_impl,sparsify, densify, SHBinOp_impl, vector2pair, SHPointwise_impl, mult_by_nth, HPrepend, compose, IgnoreIndex2.
      Opaque Monad.liftM.
      simpl.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite Vmap_app.
      rewrite Vmap_map.
      rewrite Vbreak_app.

      vec_index_equiv j jc.
      repeat rewrite Vbuild_nth.
      repeat rewrite Vnth_map.
      rewrite mkValue_evalWriter.

      unfold const.
      unfold equiv, Rtheta'_equiv.
      rewrite evalWriter_Rtheta_liftM2.
      rewrite evalWriter_mkValue.
      rewrite evalWriter_Rtheta_liftM.
      rewrite mult_comm.
      setoid_replace (Vnth x jc) with (Vnth y jc).
      reflexivity.
      apply Vnth_equiv.
      reflexivity.
      apply E.
    Qed.

    Import Coq.Arith.PeanoNat.Nat.

    (* We will use this rule to rewrite in left-to-right direction. Howver instead of putting concrete implementation of `g` which shrinks domain of `f` we chose to formulate it in a way that will allow to rewrite in opposite direction as well.
     *)
    Lemma rewrite_Pick_SHPointwise
          (n:nat)
          {svalue: CarrierA}
          {b:nat}
          {bc: b<n}
          (fm: Monoid RthetaFlags)
          (f: FinNat n -> CarrierA -> CarrierA)
          `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
          (g: FinNat 1 -> CarrierA -> CarrierA)
          `{g_mor: !Proper ((=) ==> (=) ==> (=)) g}
          (fg: forall x z, f (mkFinNat bc) x = g z x)
      :
        SHCompose (svalue:=svalue) fm (Pick fm bc) (SHPointwise fm f) =
        SHCompose fm (SHPointwise fm g) (Pick fm bc).
    Proof.
      unfold SHCompose, compose.
      unfold equiv, SHOperator_equiv.
      simpl.

      unfold equiv, ext_equiv.
      intros x y E.
      rewrite <- E; clear E y.

      vec_index_equiv j jc.
      unfold Pick_impl.

      rewrite Vnth_1.
      rewrite 2!SHPointwise_impl_nth.
      rewrite Vnth_1.
      f_equiv.
      apply fg.
    Qed.

    Lemma Induction_Vnth_S
          (n: nat)
          (f:CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=)) f}
          (initial: CarrierA)
          (v: CarrierA)
          (b: nat)
          (bc : b < n)
          (bc1 : b < S n)
      :
        Vnth (HCOLImpl.Induction n f initial v) bc =
        Vnth (HCOLImpl.Induction (S n) f initial v) bc1.
    Proof.
      replace bc1 with (lt_lt_succ_r bc) by apply NatUtil.lt_unique.
      clear bc1.
      setoid_rewrite (Vnth_arg_equiv _ _ _ _ _ _ _
                                     (HCOLImpl.Induction_cons)).
      rewrite Vnth_cons.
      break_match.
      -
        rewrite Vnth_map.
        destruct b.
        nat_lt_0_contradiction.
        generalize (Vnth_cons_tail_aux (lt_lt_succ_r bc) l).
        clear l.
        simpl.
        remember (b-0) as B.
        rewrite sub_0_r in HeqB.
        subst B.
        intros bc1.
        (* Checkpoint: Vnth (HCOLImpl.Induction n f initial v) bc = f (Vnth (HCOLImpl.Induction n f initial v) bc1) v.
https://stackoverflow.com/questions/47934884/proving-two-fixpoint-functions-by-induction
         *)
        {
          induction n in b, bc, bc1 |- *; simpl.
          - bang.
          - rewrite Vnth_map. f_equiv.
            destruct b.
            + destruct n. simpl. bang. reflexivity.
            + rewrite Vnth_map. apply IHn.
        }
      -
        destruct n.
        crush.
        simpl.
        break_match; crush.
    Qed.

    Lemma rewrite_Pick_Induction
          (n:nat)
          {svalue:CarrierA}
          {b:nat}
          {bc: b<n}
          (fm: Monoid RthetaFlags)
          (f: CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=)) f}
          (initial: CarrierA)
      :
        SHCompose (svalue:=svalue) fm (Pick fm bc) (liftM_HOperator fm (HInduction n f initial)) =
        liftM_HOperator fm (HInductor b f initial).
    Proof.
      unfold SHCompose, compose.
      unfold equiv, SHOperator_equiv.
      simpl.

      unfold equiv, ext_equiv.
      intros x y E.
      rewrite <- E; clear E y.

      vec_index_equiv j jc.
      apply Vnth_equiv.
      reflexivity.

      unfold Pick_impl.
      clear j jc.
      vec_index_equiv j jc.
      rewrite Vnth_1.

      unfold liftM_HOperator_impl, compose, sparsify.
      rewrite 2!Vnth_map.
      f_equiv.

      unfold HInduction, compose, HCOLImpl.Scalarize, densify.
      unfold HInductor, Lst, compose, HCOLImpl.Scalarize.
      dep_destruct x. clear x.
      dep_destruct x0. clear x0.
      rename h into x.
      dep_destruct j; try omega.
      simpl.

      generalize (WriterMonadNoT.evalWriter x) as y.
      intros y; clear x j jc.

      induction b,n.
      - crush.
      - crush.
      - crush.
      -
        simpl.
        unshelve rewrite <- IHb; clear IHb.
        (* no more inductor *)
        apply lt_succ_l, bc.
        rewrite Vnth_map.
        f_equiv.

        generalize (lt_S_n bc) as bc0. intros bc0.
        generalize (lt_succ_l b (S n) bc) as bc1. intros bc1.

        apply Induction_Vnth_S, pF.
    Qed.

  End Value_Correctness.

End SigmaHCOLRewritingRules.

