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
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.SigmaHCOLMem.
Require Import Helix.SigmaHCOL.MemSetoid.
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

Require Import CoLoR.Util.List.ListUtil.

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

  Section WithMonoid.
    Variable fm:Monoid RthetaFlags.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

    Global Instance compose_MemVecEq
           {i1 o2 o3}
           (op1: @SHOperator fm o2 o3)
           (op2: @SHOperator fm i1 o2)
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
        apply facts0. (* out_as_range *)
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
        unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
        intros k.
        destruct (NatUtil.lt_ge_dec k o) as [H | H].
        +
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
          rewrite NF.find_mapsto_iff in H0.
          apply H0 in V.
          unfold mem_lookup in *.

          rewrite H2, V. clear H2 V.
          unfold sparsify.
          rewrite Vnth_map.
          rewrite evalWriter_mkValue.
          unfold densify.
          unfold mem_block_to_avector, mem_lookup in Heqo0.
          apply vsequence_Vbuild_eq_Some in Heqo0.
          f_equiv.
          apply Vnth_arg_equiv.
          f_equiv.
          vec_index_equiv j jc.
          assert(V0: Is_Val (Vnth x jc)).
          {
            apply G.
            apply Full_intro.
          }
          apply H1 in V0.
          rewrite NF.find_mapsto_iff in V0.
          rewrite Vnth_map.
          apply Vnth_arg_eq with (ip:=jc) in Heqo0.
          rewrite Vbuild_nth in Heqo0.
          rewrite Vnth_map in Heqo0.
          rewrite V0 in Heqo0.
          inversion Heqo0.
          reflexivity.
        +
          rewrite O0, O2 by apply H.
          reflexivity.
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
        apply NF.find_mapsto_iff in V0.
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
        unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
        intros k.
        (* MapsTo *)
        destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
        +
          (* k<o, which is normal *)
          clear O0 O1.
          destruct (eq_nat_dec b k) as [E | NE].
          *
            (* b = k *)
            subst k.
            specialize (H0 b bc).
            specialize (I0 b bc).
            apply H0 in Vb; clear H0.
            apply NM.find_1 in Vb.
            rewrite_clear Vb.
            rewrite NF.add_eq_o by reflexivity.
            f_equiv.
            unfold eUnion'.
            rewrite Vbuild_nth.
            dep_destruct (Nat.eq_dec b b); try congruence.

            specialize (H1 0 (lt_0_Sn 0)).
            specialize (I1 0 (lt_0_Sn 0)).
            rewrite NF.find_mapsto_iff in H1.

            assert(V0: Is_Val (Vnth x (Nat.lt_0_succ 0))).
            {
              apply G.
              apply Full_intro.
            }
            apply H1 in V0.
            unfold zero in V0.
            rewrite V0 in Heqo0.
            some_inv.
            rewrite Vnth_0.
            reflexivity.
          *
            (* k<o, which is normal *)
            (* b!=k *)
            rewrite NF.add_neq_o by apply NE.
            rewrite NF.empty_o.

            assert(Vk: Is_Struct (Vnth (eUnion' bc z x) kc)).
            {
              destruct facts.
              apply no_vals_at_sparse.
              auto.
            }
            clear H1 I1 m1 Heqo0.

            apply NF.not_find_in_iff.
            unfold not.
            intros H.

            specialize (I0 k kc).
            apply I0 in H.
            crush.
        +
          (* k>=o, oob case *)
          specialize (O0 k kc).
          rewrite_clear O0.
          rewrite NF.add_neq_o by (unfold lt, nat_lt in bc;omega).
          rewrite NF.empty_o.
          reflexivity.
      -
        exfalso.
        assert(V:Is_Val (Vnth x (Nat.lt_0_succ 0))).
        {
          apply G.
          apply Full_intro.
        }
        specialize (H1 0 (lt_0_Sn 0)).
        apply H1 in V; clear H1.
        apply NF.find_mapsto_iff in V.
        unfold zero in *.
        congruence.
    Qed.

    Global Instance eT_MemVecEq
           {o b:nat}
           (bc: b < o)
      : SHOperator_MemVecEq (eT fm bc).
    Proof.
      assert (facts: SHOperator_Facts fm (eT fm bc)) by
          typeclasses eauto.
      split.
      intros x G.
      simpl.

      unfold eT_mem , map_mem_block_elt.
      unfold svector_to_mem_block.
      svector_to_mem_block_to_spec m0 H0 I0 O0.
      svector_to_mem_block_to_spec m1 H1 I1 O1.
      Opaque Vnth.
      simpl in *.

      break_match.
      -
        f_equiv.
        unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
        intros k.
        destruct (NatUtil.lt_ge_dec k 1) as [kc | kc].
        +
          clear O0 O1 I0 I1.

          assert (Is_Val (Vnth x bc)) as V.
          {
            apply G.
            reflexivity.
          }
          apply H1 in V. clear H1.
          apply NM.find_1 in V.
          unfold mem_lookup in Heqo0.
          rewrite Heqo0 in V. clear Heqo0 m1.
          some_inv. clear c H1.

          assert(Is_Val (Vnth (eT' bc x) (lt_0_Sn O))) as V0.
          {
            unfold eT'.
            rewrite Vnth_0.
            simpl.
            apply G.
            reflexivity.
          }
          rewrite H0 in V0. clear H0.
          apply NM.find_1 in V0.
          rewrite NF.add_eq_o by omega.
          destruct k.
          *
            rewrite V0.
            f_equiv.
          *
            omega.
        +
          unfold mem_lookup in *.
          rewrite O0 by apply kc.
          rewrite NF.add_neq_o by omega.
          rewrite NF.empty_o.
          reflexivity.
      -
        assert (Is_Val (Vnth x bc)) as V.
        {
          apply G.
          reflexivity.
        }
        apply H1 in V.
        apply NM.find_1 in V.
        unfold mem_lookup in Heqo0.
        congruence.
    Qed.

    Global Instance SHPointwise_MemVecEq
           {n: nat}
           (f: FinNat n -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      : SHOperator_MemVecEq (SHPointwise fm f).
    Proof.
      assert (facts: SHOperator_Facts fm (SHPointwise fm f)) by
          typeclasses eauto.

      split.
      intros x G.
      simpl.

      pose proof (@mem_out_some _ _ _ _ facts x G) as M.
      apply is_Some_equiv_def in M.
      destruct M as [y M].
      rewrite M.
      f_equiv.
      unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
      intros k.

      unfold svector_to_mem_block in *.
      svector_to_mem_block_to_spec m0 H0 I0 O0.
      svector_to_mem_block_to_spec m1 H1 I1 O1.
      simpl in *.

      unfold mem_op_of_hop in M.
      break_match_hyp; try some_none.
      some_inv.
      rewrite <- M. clear M.

      unfold avector_to_mem_block.
      avector_to_mem_block_to_spec m2 H2 O2.
      unfold mem_lookup in *. simpl in *.

      destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
      +
        (* k<n, which is normal *)
        clear O0 O1 O2.
        specialize (H0 k kc). specialize (I0 k kc).
        specialize (H1 k kc). specialize (I1 k kc).
        assert(V0: Is_Val (Vnth x kc)).
        {
          apply G.
          apply Full_intro.
        }

        assert(V: Is_Val (Vnth (SHPointwise' f x) kc)).
        {
          unfold SHPointwise'.
          rewrite Vbuild_nth.
          apply Is_Val_liftM.
          apply V0.
        }

        rewrite H0 in V.
        apply NM.find_1 in V.
        rewrite V.

        unfold SHPointwise'.
        rewrite Vbuild_nth.
        rewrite H2 with (ip:=kc).
        rewrite HPointwise_nth.
        rewrite evalWriter_Rtheta_liftM.
        f_equiv.
        f_equiv.

        unfold mem_block_to_avector in Heqo.
        apply vsequence_Vbuild_eq_Some in Heqo.
        apply Vnth_arg_eq with (ip:=kc) in Heqo.
        rewrite Vbuild_nth in Heqo.
        rewrite Vnth_map in Heqo.
        unfold mem_lookup in Heqo.

        apply H1 in V0.
        apply NM.find_1 in V0.
        rewrite Heqo in V0.
        some_inv.
        reflexivity.
      +
        rewrite O0 by apply kc.
        rewrite O2 by apply kc.
        reflexivity.
    Qed.

  End WithMonoid.

  Global Instance SHBinOp_RthetaSafe_MemVecEq
         {o}
         (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : SHOperator_MemVecEq (@SHBinOp Monoid_RthetaSafeFlags o f pF).
  Proof.
    assert (facts: SHOperator_Facts _ (SHBinOp Monoid_RthetaSafeFlags f)) by
        typeclasses eauto.

    split.
    intros x G.
    simpl.

    pose proof (@mem_out_some _ _ _ _ facts x G) as M.
    apply is_Some_equiv_def in M.
    destruct M as [y M].
    rewrite M.
    f_equiv.
    unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
    intros k.

    unfold svector_to_mem_block in *.
    svector_to_mem_block_to_spec m0 H0 I0 O0.
    svector_to_mem_block_to_spec m1 H1 I1 O1.
    simpl in *.

    unfold mem_op_of_hop in M.
    break_match_hyp; try some_none.
    some_inv.
    rewrite <- M. clear M.

    unfold avector_to_mem_block.
    avector_to_mem_block_to_spec m2 H2 O2.
    unfold mem_lookup in *. simpl in *.

    destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
    +
      (* k<n, which is normal *)
      clear O0 O1 O2.
      specialize (H0 k kc). specialize (I0 k kc).
      assert (k < o + o)%nat as kc1 by omega.
      assert(V1: Is_Val (Vnth x kc1)).
      {
        apply G.
        apply Full_intro.
      }

      assert (k + o < o + o)%nat as kc2 by omega.
      assert(V2: Is_Val (Vnth x kc2)).
      {
        apply G.
        apply Full_intro.
      }

      assert(V: Is_Val (Vnth (SHBinOp' f x) kc)).
      {
        erewrite SHBinOp'_nth with (jc:=kc).
        apply Is_Val_Safe_liftM2.
        apply V1.
        apply V2.
      }

      rewrite H0 in V.
      apply NM.find_1 in V.
      rewrite V.

      rewrite H2 with (ip:=kc).
      f_equiv.
      rewrite SHBinOp'_nth with (jc:=kc) (jc1:=kc1) (jc2:=kc2).
      rewrite HBinOp_nth with (jc:=kc) (jc1:=kc1) (jc2:=kc2).

      rewrite evalWriter_Rtheta_liftM2.
      f_equiv.
      *
        specialize (H1 k kc1).
        unfold mem_block_to_avector in Heqo0.
        apply vsequence_Vbuild_eq_Some in Heqo0.
        apply Vnth_arg_eq with (ip:=kc1) in Heqo0.
        rewrite Vbuild_nth in Heqo0.
        rewrite Vnth_map in Heqo0.
        unfold mem_lookup in Heqo0.

        apply H1 in V1.
        apply NM.find_1 in V1.
        rewrite Heqo0 in V1.
        some_inv.
        reflexivity.
      *
        specialize (H1 (k+o)%nat kc2).
        unfold mem_block_to_avector in Heqo0.
        apply vsequence_Vbuild_eq_Some in Heqo0.
        apply Vnth_arg_eq with (ip:=kc2) in Heqo0.
        rewrite Vbuild_nth in Heqo0.
        rewrite Vnth_map in Heqo0.
        unfold mem_lookup in Heqo0.

        apply H1 in V2.
        apply NM.find_1 in V2.
        rewrite Heqo0 in V2.
        some_inv.
        reflexivity.
    +
      rewrite O0 by apply kc.
      rewrite O2 by apply kc.
      reflexivity.
  Qed.

  (* TODO: move somewhere in Utils *)
  Fixpoint set_of_list {A:Type} (l : list A) {struct l}: Ensemble A :=
    match l with
    | nil => Empty_set A
    | List.cons hd tl => Add A (set_of_list tl) hd
    end.

  (* TODO: could be proven <-> *)
  Lemma mem_merge_is_Some (m0 m1 : mem_block):
    Disjoint nat (set_of_list (mem_keys m0))
             (set_of_list (mem_keys m1)) → is_Some (mem_merge m0 m1).
  Proof.
    intros D.
    unfold mem_merge.
    rewrite NM.fold_1.
    unfold mem_keys in *.
    remember (NM.elements m0) as e0.
    induction e0.
    -
      simpl; tauto.
    -
      admit.
  Admitted.

  (* TODO: move somewhere in Memory *)
  Lemma mem_merge_key_either
        (m m0 m1 : mem_block)
        (MM : mem_merge m0 m1 ≡ Some m)
    :
      forall k, NM.In k m -> {NM.In k m0}+{NM.In k m1}.
  Proof.
    intros k H.
    unfold mem_merge in MM.
    rewrite NM.fold_1 in MM.
    (* TODO: turn everything to NM.elements *)
    induction (NM.elements m0).
    -
      simpl in *.
      some_inv.
      right.
      apply H.
    -
      destruct a as [k' v].
      destruct (eq_nat_dec k k').
      +
        subst.
        left.
        (* ListUtil.In_fold_left *)
        admit.
  Admitted.

  (* TODO: move somewhere in Utils *)
  Lemma In_Add_eq
        {T:Type}
        {a b: T}
        {l: Ensemble T}
    :
      a≡b -> In T (Add T l a) b.
  Proof.
  Admitted.

  (* TODO: move somewhere in Utils *)
  Lemma In_Add_neq
        {T:Type}
        (a b: T)
        {l: Ensemble T}
    :
      a≢b -> In T l b <-> In T (Add T l a) b.
  Proof.
  Admitted.

  Lemma In_NM_In
        {k:nat}
        {m: mem_block}:
    In nat (set_of_list (mem_keys m)) k <->
    NM.In k m.
  Proof.
    split.
    -
      intros H.
      apply NF.elements_in_iff.
      unfold mem_keys in *.
      induction (NM.elements m).
      +
        inversion H.
      +
        destruct (eq_nat_dec k (fst a)).
        *
          subst.
          destruct a; simpl in *.
          exists c.
          apply InA_cons_hd.
          reflexivity.
        *
          destruct a; simpl in *.
          apply In_Add_neq in H; auto.
          apply IHl in H.
          destruct H as [e H].
          exists e.
          apply InA_cons_tl.
          apply H.
    -
      (* not needed yet *)
      intros H.
      apply NF.elements_in_iff in H.
      destruct H as [v H].
      unfold mem_keys.
      revert H.
      induction (NM.elements m).
      +
        intros H.
        inversion H.
      +
        intros H.
        simpl.
        destruct (eq_nat_dec k (fst a)).
        *
          subst.
          apply In_Add_eq, reflexivity.
        *
          rewrite <- In_Add_neq with (a0:=fst a) by auto.
          apply IHl; clear IHl.
          inversion H;subst.
          --
            destruct a.
            simpl in n.
            inversion H1.
            crush.
          --
            apply H1.
  Qed.

  Global Instance HTSUMUnion_MemVecEq
         {i o: nat}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
         (op1 op2: @SHOperator Monoid_RthetaFlags i o)
         (compat: Disjoint _
                           (out_index_set _ op1)
                           (out_index_set _ op2)
         )
         `{Meq1: SHOperator_MemVecEq _ i o op1}
         `{Meq2: SHOperator_MemVecEq _ i o op2}

    : SHOperator_MemVecEq
        (facts := HTSUMUnion_Facts dot op1 op2 compat)
        (HTSUMUnion Monoid_RthetaFlags dot op1 op2).
  Proof.
    split.
    intros x G.
    simpl.
    unfold HTSUMUnion', Vec2Union, HTSUMUnion_mem.
    break_match.
    -
      break_match.
      +
        rename m into m1, m0 into m2. (* to match operator indices *)
        destruct (mem_merge m1 m2) eqn:MM.
        *
          apply RelUtil.opt_r_Some.
          unfold mem_block_Equiv, mem_block_equiv, NM.Equal.
          intros k.
          pose proof (mem_merge_key_either m m1 m2 MM k) as E.
          unfold svector_to_mem_block.
          svector_to_mem_block_to_spec m' H0 H1 I2.
          simpl in *.
          destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
          --
            clear I2.
            (* k<o. Normal *)
            remember (mkFinNat kc) as kf.
            (* each kf could be either in out_set of op1 or op2 *)
            admit.
          --
            (* k>=o. m[k] should be None *)
            clear H0 H1.
            specialize (I2 k kc).
            unfold mem_lookup in I2.
            rewrite_clear I2.
            symmetry.
            apply NF.not_find_in_iff.
            intros N.
            apply E in N.
            destruct N as [N1 | N2].
            ++
              (* prove contradiction in N1 *)
              admit.
            ++
              (* prove contradiction in N1 *)
              admit.
        *
          exfalso.
          contradict MM.
          apply is_Some_ne_None.
          apply mem_merge_is_Some.
          apply Disjoint_intro.
          intros k.
          intros H.
          unfold In in H.
          destruct H.
          rename x0 into k.
          rename H into IN1, H0 into IN2.
          apply In_NM_In in IN1.
          apply In_NM_In in IN2.
          unfold svector_to_mem_block in Heqo0.
          svector_to_mem_block_to_spec m1' H1 I1 O1.
          unfold svector_to_mem_block in Heqo1.
          svector_to_mem_block_to_spec m2' H2 I2 O2.
          simpl in *.
          admit.
      +
        contradict Heqo1.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H.
        apply G.
        simpl.
        apply Union_intror.
        apply H.
    -
      contradict Heqo0.
      apply is_Some_ne_None.
      apply mem_out_some; auto.
      intros j jc H.
      apply G.
      simpl.
      apply Union_introl.
      apply H.
  Qed.


End MemVecEq.