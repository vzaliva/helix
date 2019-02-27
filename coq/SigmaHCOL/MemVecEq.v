Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SigmaHCOLMem.
Require Import Helix.HCOL.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import Helix.Tactics.HelixTactics.
Require Import Psatz.
Require Import Omega.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.theory.setoids.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Import Monoid.

Import VectorNotations.
Open Scope vector_scope.

Class SHOperator_MemVecEq
      {fm}
      {i o: nat}
      (f: @SHOperator fm i o)
      `{facts: SHOperator_Facts _ _ _ f}
  :=
    {
      mem_vec_preservation:
        forall x,

          (* Only for inputs which comply to `facts` *)
          (∀ (j : nat) (jc : (j < i)%nat),
              in_index_set fm f (mkFinNat jc) → Is_Val (Vnth x jc))
          ->
          Some (svector_to_mem_block (op fm f x)) =
          mem_op fm f (svector_to_mem_block x)
      ;
    }.


Section MemVecEq.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Global Instance compose_MemVecEq
         {i1 o2 o3}
         (op1: @SHOperator fm o2 o3)
         (op2: @SHOperator fm i1 o2)
         `{fop1: SHOperator_Facts fm _ _ op1}
         `{fop2: SHOperator_Facts fm _ _ op2}
         (compat: Included _ (in_index_set fm op1) (out_index_set fm op2))
         `{Meq1: SHOperator_MemVecEq fm o2 o3 op1}
         `{Meq2: SHOperator_MemVecEq fm i1 o2 op2}
    : SHOperator_MemVecEq
        (facts:=SHCompose_Facts fm fml op1 op2 compat)
        (SHCompose fm op1 op2).
  Proof.
    split.
    intros x G.
    simpl.
    unfold option_compose, compose.

    pose proof (mem_out_some fm x) as Rm.
    specialize (Rm G).
    apply is_Some_equiv_def in Rm.
    destruct Rm as [m2 Rm].
    break_match; try some_none.
    clear Rm m2.
    pose proof (mem_op_proper _ op1) as P.
    setoid_replace m with (svector_to_mem_block (op fm op2 x)).
    apply Meq1.
    {
      intros j jc H.
      apply fop2. (* out_as_range *)
      apply G.
      apply compat, H.
    }

    apply Some_inj_equiv.
    rewrite <- Heqo.
    symmetry.
    apply Meq2, G.
  Qed.

  Global Instance liftM_MemVecEq
         {i o}
         (hop: avector i -> avector o)
         `{HOP: HOperator i o hop}
    : SHOperator_MemVecEq (liftM_HOperator fm hop).
  Proof.
    assert (facts: SHOperator_Facts fm (liftM_HOperator fm hop)) by
        typeclasses eauto.
    split.
    intros x G.
    simpl.
    unfold mem_op_of_hop.
    unfold liftM_HOperator', avector_to_mem_block, svector_to_mem_block, compose in *.

    svector_to_mem_block_to_spec m0 H0 I0 O0.
    svector_to_mem_block_to_spec m1 H1 I1 O1.
    break_match.
    -
      f_equiv.
      avector_to_mem_block_to_spec m2 H2 O2.
      simpl in *.
      unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equiv.
      split.
      *
        (* In *)
        intros.
        destruct (NatUtil.lt_ge_dec k o) as [H | H].
        --
          clear O0 O1 O2.
          split.
          ++
            intros H3.
            specialize (H2 k H).
            unfold mem_lookup in *.
            apply NMS.F.in_find_iff.
            crush.
          ++
            intros H3.
            specialize (H0 k H).
            unfold mem_lookup in *.
            apply NMS.F.in_find_iff.
            assert(V: Is_Val (Vnth (sparsify fm (hop (densify fm x))) H)).
            {
              destruct facts.
              apply out_as_range.
              intros j jc H4.
              apply G.
              apply Full_intro.
              apply Full_intro.
            }
            rewrite NMS.F.find_mapsto_iff in H0.
            crush.
        --
          clear H0 H1 H2.
          split.
          ++
            intros H3; apply NMS.In_MapsTo in H3; destruct H3 as [e H3]; apply NM.find_1 in H3.
            specialize (O0 k H); unfold mem_lookup in O0.
            congruence.
          ++
            intros H3; apply NMS.In_MapsTo in H3; destruct H3 as [e H3]; apply NM.find_1 in H3.
            specialize (O2 k H); unfold mem_lookup in O2.
            congruence.
      *
        (* MapsTo *)
        intros k e e' H3 H4.
        destruct (NatUtil.lt_ge_dec k o) as [H | H].
        --
          clear O0 O1 O2.
          specialize (H0 k H).
          specialize (H2 k H).
          assert(V: Is_Val (Vnth (sparsify fm (hop (densify fm x))) H)).
          {
            destruct facts.
            apply out_as_range.
            intros j jc H9.
            apply G.
            apply Full_intro.
            apply Full_intro.
          }
          rewrite NMS.F.find_mapsto_iff in H0.
          apply H0 in V.
          unfold mem_lookup in *.
          apply NM.find_1 in H4; rewrite H2 in H4; inversion_clear H4; clear H2.
          apply NM.find_1 in H3; rewrite V in H3; inversion_clear H3; clear H0.
          unfold sparsify.
          rewrite Vnth_map.
          rewrite evalWriter_mkValue.
          unfold densify.
          simpl.

          unfold mem_block_to_avector, mem_lookup in Heqo0.
          apply vsequence_Vbuild_eq_Some in Heqo0.

          apply Vnth_arg_equiv.
          f_equiv.
          vec_index_equiv j jc.
          assert(V0: Is_Val (Vnth x jc)).
          {
            apply G.
            apply Full_intro.
          }
          apply H1 in V0.
          rewrite NMS.F.find_mapsto_iff in V0.
          rewrite Vnth_map.
          apply Vnth_arg_eq with (ip:=jc) in Heqo0.
          rewrite Vbuild_nth in Heqo0.
          rewrite Vnth_map in Heqo0.
          rewrite V0 in Heqo0.
          inversion Heqo0.
          reflexivity.
        --
          clear H0 H1 H2.
          apply NM.find_1 in H4.
          specialize (O2 k H); unfold mem_lookup in O2.
          congruence.
    -
      simpl in *.
      unfold mem_block_to_avector in Heqo0.
      apply vsequence_Vbuild_eq_None in Heqo0.
      destruct Heqo0 as [j [jc Heqo0]].
      assert(V0: Is_Val (Vnth x jc)).
      {
        apply G.
        apply Full_intro.
      }
      apply H1 in V0. clear H1.
      apply NMS.F.find_mapsto_iff in V0.
      unfold mem_lookup in Heqo0.
      congruence.
  Qed.

  Global Instance eUnion_MemVecEq
         {o b:nat}
         (bc: b < o)
         (z: CarrierA)
    : SHOperator_MemVecEq (eUnion fm bc z).
  Proof.
    assert (facts: SHOperator_Facts fm (eUnion fm bc z)) by
        typeclasses eauto.
    split.
    intros x G.
    simpl.
    unfold eUnion_mem, map_mem_block_elt.

    unfold svector_to_mem_block.
    svector_to_mem_block_to_spec m0 H0 I0 O0.
    svector_to_mem_block_to_spec m1 H1 I1 O1.

    break_match; unfold mem_lookup in *; simpl in *.
    -
      f_equiv.
      unfold mem_add, mem_empty.
      assert(Vb: Is_Val (Vnth (eUnion' bc z x) bc)).
      {
        destruct facts.
        apply out_as_range.
        -
          intros j jc H.
          apply G.
          auto.
        -
          simpl.
          reflexivity.
      }
      unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equiv.
      split; intros.
      +
        (* In *)
        split.
        *
          intros H2.
          destruct (eq_nat_dec b k) as [E | NE].
          --
            apply NMS.F.add_in_iff.
            left.
            apply E.
          --
            exfalso.
            destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
            ++
              (* k in range *)
              clear O0 O1.
              (* clear m1 H1 Heqo0 c G. *)
              assert(H: Is_Struct (Vnth (eUnion' bc z x) kc)).
              {
                pose proof (no_vals_at_sparse fm x) as S.
                auto.
              }
              assert(C: Is_Val (Vnth (eUnion' bc z x) kc))
                by apply I0, H2.
              rewrite <- not_Is_Struct_Is_Val in C.
              congruence.
            ++
              (* k is oob *)
              specialize (O0 k kc).
              apply NMS.F.in_find_iff in H2.
              congruence.
        *
          intros H2.
          apply NMS.F.add_in_iff in H2.
          destruct H2.
          --
            destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
            ++
              (* k in range *)
              clear O0 O1.
              subst k.
              apply H0 in Vb.
              apply NMS.MapsTo_In in Vb.
              apply Vb.
            ++
              (* k is oob *)
              specialize (O0 k kc).
              apply H0 in Vb.
              apply NMS.MapsTo_In in Vb.
              congruence.
          --
            exfalso.
            apply NMS.F.empty_in_iff in H.
            destruct H.
      +
        (* MapsTo *)
        destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
        *
          (* k<0, which is normal *)
          clear O0 O1.
          destruct (eq_nat_dec b k) as [E | NE].
          --
            subst k.
            specialize (H0 b bc).
            specialize (I0 b bc).
            apply H0 in Vb; clear H0.
            apply NM.find_1 in H.
            apply NM.find_1 in H2.
            apply NM.find_1 in Vb.

            rewrite NMS.F.add_eq_o in H2 by reflexivity.
            rewrite H in Vb; clear H.
            symmetry in H2.
            rewrite <- Heqo0 in H2; clear Heqo0.

            specialize (H1 0 (lt_0_Sn 0)).
            specialize (I1 0 (lt_0_Sn 0)).
            rewrite NMS.F.find_mapsto_iff in H1.

            assert(V0: Is_Val (Vnth x (Nat.lt_0_succ 0))).
            {
              apply G.
              apply Full_intro.
            }
            apply H1 in V0.
            unfold zero in V0.
            rewrite V0 in H2.

            unfold eUnion' in Vb.
            rewrite Vbuild_nth in Vb.
            dep_destruct (Nat.eq_dec b b); try congruence.
            rewrite Vnth_0 in H2.
            rewrite <- H2 in Vb.
            inversion Vb.
            subst.
            reflexivity.
          --
            apply NM.add_3 in H2; auto.
            apply NMS.F.empty_mapsto_iff in H2.
            destruct H2.
        *
          (* k>=0, oob case *)
          specialize (O0 k kc).
          apply NM.find_1 in H.
          rewrite O0 in H.
          some_none.
    -
      exfalso.
      assert(V:Is_Val (Vnth x (Nat.lt_0_succ 0))).
      {
        apply G.
        apply Full_intro.
      }
      specialize (H1 0 (lt_0_Sn 0)).
      apply H1 in V; clear H1.
      apply NMS.F.find_mapsto_iff in V.
      unfold zero in *.
      congruence.
  Qed.

End MemVecEq.