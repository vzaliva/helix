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

Require Import Coq.Lists.SetoidList.
Require Import CoLoR.Util.List.ListUtil.
Require Import CoLoR.Util.Nat.NatUtil.

Import Monoid.

Import VectorNotations.
Open Scope vector_scope.

Open Scope nat_scope.

Class SHOperator_Mem
      {fm}
      {i o: nat}
      (xop: @SHOperator fm i o)
      `{facts: SHOperator_Facts fm _ _ xop}
  :=
    {
      (* -- implementation on memory blocks -- *)
      mem_op: mem_block -> option mem_block;
      mem_op_proper: Proper ((=) ==> (=)) mem_op;
      (* -- Structural properties for [mem_op] -- *)

      (* sufficiently (values in right places, no info on empty
         spaces) filled input memory block guarantees that `mem_op`
         will not fail.  *)
      mem_out_some: forall m,
          (forall j (jc:j<i), in_index_set fm xop (mkFinNat jc) -> mem_in j m)
          ->
          is_Some (mem_op m);

      (* Output memory block always have values in right places, and
             does not have value in sparse positions *)
      out_mem_fill_pattern: forall m0 m,
          mem_op m0 ≡ Some m
          ->
          forall j (jc:j<o), out_index_set fm xop (mkFinNat jc) <-> mem_in j m;

      (* Do not access memory outside of bounds *)
      out_mem_oob: forall m0 m,
          mem_op m0 ≡ Some m -> forall j (jc:j>=o), not (mem_in j m);

      (* -- Semantics eqivalence -- *)

      mem_vec_preservation:
        forall x,

          (* Only for inputs which comply to `facts` *)
          (∀ (j : nat) (jc : (j < i)%nat),
              in_index_set fm xop (mkFinNat jc) → Is_Val (Vnth x jc))
          ->
          Some (svector_to_mem_block (op fm xop x)) =
          mem_op (svector_to_mem_block x);
    }.


Section MemVecEq.

  (* !!!
  (* Shinks family from [(S (S n))] to [(S n)], assuming [j] is below [(S n)] *)
  Fact IUnion_mem_aux_shrink
       {i o: nat}
       (n : nat)
       (j: nat) (jc: j<S n)
       (op_family : SHOperatorFamily Monoid_RthetaFlags)
       (m : NatMap CarrierA)
    :
      IUnion_mem_aux jc
                     (get_family_mem_op Monoid_RthetaFlags
                                        (shrink_op_family Monoid_RthetaFlags op_family))
                     m
                     ≡ IUnion_mem_aux
                     (Nat.lt_lt_succ_r jc)
                     (get_family_mem_op (i:=i) (o:=o) Monoid_RthetaFlags op_family) m.
  Proof.
    induction j.
    -
      unfold get_family_mem_op, shrink_op_family, mkFinNat.
      simpl.
      f_equiv; f_equiv; f_equiv.
      apply le_unique.
    -
      simpl.
      replace (get_family_mem_op Monoid_RthetaFlags
                                 (shrink_op_family Monoid_RthetaFlags op_family) (S j) jc m)
        with
          (get_family_mem_op Monoid_RthetaFlags op_family (S j) (Nat.lt_lt_succ_r jc) m).
      2:{
        unfold get_family_mem_op, shrink_op_family, mkFinNat.
        simpl.
        f_equiv; f_equiv; f_equiv.
        apply le_unique.
      }
      break_match; try reflexivity.
      rewrite IHj.
      replace (Nat.lt_lt_succ_r (Nat.lt_succ_l j (S n) jc)) with
          (Nat.lt_succ_l j (S (S n)) (Nat.lt_lt_succ_r jc)) by apply le_unique.
      reflexivity.
  Qed.
   *)

  Definition FinNatSet_to_natSet {n:nat} (f: FinNatSet n): Ensemble nat
    := fun j => match lt_ge_dec j n with
             | left jc => f (mkFinNat jc)
             | in_right => False
             end.

  Lemma FinNatSet_to_natSet_Empty (f: FinNatSet 0):
    FinNatSet_to_natSet f ≡ Empty_set _.
  Proof.
    apply Extensionality_Ensembles.
    split; intros H P.
    -
      exfalso.
      unfold FinNatSet_to_natSet in P.
      unfold Ensembles.In in *.
      break_match.
      nat_lt_0_contradiction.
      congruence.
    -
      contradict P.
  Qed.

  Lemma Disjoint_FinNat_to_nat {n:nat} (A B: FinNatSet n):
    Disjoint _ A B ->
    Disjoint nat (FinNatSet_to_natSet A) (FinNatSet_to_natSet B).
  Proof.
    intros D.
    apply Disjoint_intro.
    intros k C.
    destruct D as [D].
    destruct C as [k C1 C2].
    unfold FinNatSet_to_natSet in *.
    unfold Ensembles.In in *.
    destruct (lt_ge_dec k n) as [kc | nkc].
    -
      specialize (D (mkFinNat kc)).
      contradict D.
      apply Intersection_intro.
      + apply C1.
      + apply C2.
    -
      tauto.
  Qed.

  Lemma mem_keys_set_to_out_index_set
        (i o: nat)
        {fm}
        (xop: @SHOperator fm i o)
        `{mop: SHOperator_Mem fm _ _ xop}
        (m m0: mem_block)
    :
      (mem_op m0 ≡ Some m)
      ->
      FinNatSet_to_natSet (out_index_set fm xop) ≡ NE.mkEns (mem_keys_set m).
  Proof.
    intros H.
    pose proof (out_mem_fill_pattern _ _ H) as H1.
    pose proof (out_mem_oob _ _ H) as H2.
    clear H.
    unfold mem_in in *.
    apply Extensionality_Ensembles.
    unfold Same_set.
    split.
    -
      unfold Ensembles.Included.
      intros k H.
      destruct (lt_ge_dec k o) as [kc | nkc].
      +
        clear H2.
        specialize (H1 k kc).
        apply mem_keys_set_In.
        apply H1. clear H1.
        unfold Ensembles.In in *.
        generalize dependent (out_index_set fm xop).
        intros s H.
        unfold FinNatSet_to_natSet in H.
        break_match_hyp; try contradiction.
        replace l with kc in H by apply lt_unique.
        apply H.
      +
        exfalso.
        clear H1.
        specialize (H2 k nkc).
        (* H is false, as k is out of range *)
        unfold Ensembles.In in H.
        unfold FinNatSet_to_natSet in H.
        break_match_hyp; try omega.
    -
      unfold Ensembles.Included.
      intros k H.
      unfold Ensembles.In in *.
      destruct (lt_ge_dec k o) as [kc | nkc].
      +
        clear H2.
        specialize (H1 k kc).
        unfold FinNatSet_to_natSet.
        break_match; try omega.
        replace l with kc by apply lt_unique.
        apply H1.
        apply mem_keys_set_In.
        apply H.
      +
        apply mem_keys_set_In in H.
        specialize (H2 k nkc).
        congruence.
  Qed.

  (*
  Lemma IUnion_mem_aux_step_disjoint
        (i o n : nat)
        (j: nat) (jc: j < S (S n))
        (k: nat) (kc: k < S (S n))
        (jk: j<k)
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o (S (S n)))
        (op_family_facts: ∀ (j : nat) (jc : j < S (S n)),
            @SHOperator_Facts Monoid_RthetaFlags i o
                              (op_family (@mkFinNat (S (S n)) j jc)))

        (compat : ∀ (m0 : nat) (mc : m0 < S (S n)) (n0 : nat) (nc : n0 < S (S n)),
            m0 ≢ n0
            → Disjoint (FinNat o)
                       (@out_index_set Monoid_RthetaFlags i o (op_family (@mkFinNat (S (S n)) m0 mc)))
                       (@out_index_set Monoid_RthetaFlags i o (op_family (@mkFinNat (S (S n)) n0 nc))))

        (m m0 m1 : mem_block)

        (H0: @get_family_mem_op Monoid_RthetaFlags i o (S (S n)) op_family
                                k kc m
                                ≡ @Some mem_block m0)
        (H1:
           @IUnion_mem_aux (S (S n))
                           j jc
                           (@get_family_mem_op
                              Monoid_RthetaFlags i o
                              (S (S n)) op_family) m
                           ≡ @Some mem_block m1)
    :
      Disjoint nat
               (NE.mkEns (mem_keys_set m0))
               (NE.mkEns (mem_keys_set m1)).
  Proof.
    unfold get_family_mem_op in *.
    revert m0 m1 k kc jk H0 H1.
    induction j; intros.
    -
      assert(P: k <> 0) by auto.
      assert(P1: k < S (S n)) by omega.
      assert(P2: 0 < S (S n)) by lia.
      specialize (compat k P1 0 P2 P).
      clear P.
      simpl in *.
      apply Disjoint_FinNat_to_nat in compat.
      rewrite
        mem_keys_set_to_out_index_set
        with (m:=m0) (m0:=m),
             mem_keys_set_to_out_index_set
        with (m:=m1) (m0:=m) in compat; auto.

      rewrite <- H1; unfold mkFinNat;f_equiv; f_equiv; f_equiv; apply lt_unique.
      rewrite <- H0; unfold mkFinNat; f_equiv; f_equiv;f_equiv; apply lt_unique.
    -
      simpl in *.
      repeat break_match_hyp; try some_none.
      apply (Disjoint_of_mem_merge H1).
      +
        assert(P: k ≢ S j) by lia.
        specialize (compat k kc (S j) jc P).
        simpl in compat.
        erewrite <- 2!mem_keys_set_to_out_index_set.
        apply Disjoint_FinNat_to_nat.
        eapply compat.
        eauto.
        eauto.
        eauto.
        eauto.
      +
        unshelve eapply IHj ; try auto; try omega.
        replace (dec_not_not _ _ _) with (Nat.lt_succ_l j (S (S n)) jc)
          by apply lt_unique.
        apply Heqo1.
  Qed.

  (* Shinks family from `(S (S n))` to `(S n)`, assuming `j` is below `(S n)` *)
  Fact IReduction_mem_aux_shrink
       {i o: nat}
       (n : nat)
       (j: nat) (jc: j<S n)
       (dot : CarrierA → CarrierA → CarrierA)
       (op_family : SHOperatorFamily Monoid_RthetaSafeFlags)
       (m : NatMap CarrierA)
    :
      IReduction_mem_aux jc dot
                         (get_family_mem_op Monoid_RthetaSafeFlags
                                            (shrink_op_family Monoid_RthetaSafeFlags op_family))
                         m
                         ≡ IReduction_mem_aux
                         (Nat.lt_lt_succ_r jc)
                         dot
                         (get_family_mem_op (i:=i) (o:=o) Monoid_RthetaSafeFlags op_family) m.
  Proof.
    induction j.
    -
      unfold get_family_mem_op, shrink_op_family, mkFinNat.
      simpl.
      f_equiv; f_equiv; f_equiv.
      apply le_unique.
    -
      simpl.
      replace (get_family_mem_op Monoid_RthetaSafeFlags
                                 (shrink_op_family Monoid_RthetaSafeFlags op_family) (S j) jc m)
        with
          (get_family_mem_op Monoid_RthetaSafeFlags op_family (S j) (Nat.lt_lt_succ_r jc) m).
      2:{
        unfold get_family_mem_op, shrink_op_family, mkFinNat.
        simpl.
        f_equiv; f_equiv; f_equiv.
        apply le_unique.
      }
      break_match; try reflexivity.
      rewrite IHj.
      replace (Nat.lt_lt_succ_r (Nat.lt_succ_l j (S n) jc)) with
          (Nat.lt_succ_l j (S (S n)) (Nat.lt_lt_succ_r jc)) by apply le_unique.
      reflexivity.
  Qed.
   *)

  Section WithMonoid.

    Variable fm: Monoid RthetaFlags.
    Variable fml: @MonoidLaws RthetaFlags RthetaFlags_type fm.

    Global Instance compose_Mem
           {i1 o2 o3}
           (op1: @SHOperator fm o2 o3)
           (op2: @SHOperator fm i1 o2)
           (compat: Included _ (in_index_set fm op1) (out_index_set fm op2))
           `{Meq1: SHOperator_Mem fm o2 o3 op1}
           `{Meq2: SHOperator_Mem fm i1 o2 op2}
      : SHOperator_Mem
          (facts:=SHCompose_Facts fm op1 op2 compat)
          (SHCompose fm op1 op2).
    Proof.
      unshelve esplit.
      -
        exact (option_compose (mem_op (xop:=op1))
                              (mem_op (xop:=op2))
              ).
      -
        apply option_compose_proper; [ apply Meq1 | apply Meq2].
      -
        (* mem_out_some *)
        intros m H.
        unfold is_Some, option_compose in *.
        simpl in *.
        unfold option_compose.
        repeat break_match; try some_none; try auto.
        +
          contradict Heqo.
          apply is_Some_ne_None.
          apply mem_out_some.
          pose proof (out_mem_fill_pattern m m0 Heqo0) as P.
          intros j jc H0.
          specialize (P j jc).
          apply P.
          apply compat.
          apply H0.
        +
          clear Heqo.
          pose proof (@mem_out_some _ _ _ _ _ _ _ H) as C.
          unfold is_Some in C.
          break_match; [ some_none | tauto].
      -
        (* out_mem_fill_pattern *)
        intros m0 m H.
        split.
        +
          simpl in *.
          unfold option_compose in H.
          break_match_hyp; try some_none.
          pose proof (out_mem_fill_pattern  m1 m H) as P1.
          apply P1; auto.
        +
          simpl in *.
          unfold option_compose in H.
          break_match_hyp; try some_none.
          pose proof (out_mem_fill_pattern m1 m H) as P2.
          apply P2; auto.
      -
        (* mem_out_oob *)
        intros m0 m H.
        unfold option_compose in H.
        break_match_hyp; try some_none.
        pose proof (out_mem_oob  m1 m H) as P2.
        apply P2; auto.
      -
        (* mem_vec_preservation *)
        intros x G.
        unfold option_compose, compose.
        simpl in G.

        pose proof (@mem_out_some fm _ _ op2 _ Meq2 (svector_to_mem_block x) ) as Rm.
        assert(G0: (∀ (j : nat) (jc : (j < i1)%nat), in_index_set fm op2 (mkFinNat jc)
                                                 → mem_in j (svector_to_mem_block x))).
        {
          intros j jc H.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply G,H.
        }
        specialize (Rm G0).
        apply is_Some_equiv_def in Rm.
        destruct Rm as [m2 Rm].
        break_match; try some_none.
        clear Rm m2.
        pose proof (mem_op_proper (xop:=op1)) as P.
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

    Global Instance liftM_Mem
           {i o}
           (hop: avector i -> avector o)
           `{HOP: HOperator i o hop}
      : SHOperator_Mem (liftM_HOperator fm hop).
    Proof.
      unshelve esplit.
      -
        exact (mem_op_of_hop hop).
      -
        typeclasses eauto.
      -
        (* mem_out_some *)
        intros m H.
        apply mem_out_some_mem_op_of_hop, H.
      -
        simpl.
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        simpl.
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        (* mem_vec_preservation *)
        assert (facts: SHOperator_Facts fm (liftM_HOperator fm hop)) by
            typeclasses eauto.

        intros x G.
        simpl.
        unfold mem_op_of_hop.
        unfold liftM_HOperator', avector_to_mem_block, svector_to_mem_block, compose in *.

        svector_to_mem_block_to_spec m0 H0 I0 O0.
        svector_to_mem_block_to_spec m1 H1 I1 O1.
        break_match.
        +
          f_equiv.
          avector_to_mem_block_to_spec m2 H2 O2.
          simpl in *.
          unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
          intros k.
          destruct (NatUtil.lt_ge_dec k o) as [H | H].
          *
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
            rewrite NP.F.find_mapsto_iff in H0.
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
            rewrite NP.F.find_mapsto_iff in V0.
            rewrite Vnth_map.
            apply Vnth_arg_eq with (ip:=jc) in Heqo0.
            rewrite Vbuild_nth in Heqo0.
            rewrite Vnth_map in Heqo0.
            rewrite V0 in Heqo0.
            inversion Heqo0.
            reflexivity.
          *
            rewrite O0, O2 by apply H.
            reflexivity.
        +
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
          apply NP.F.find_mapsto_iff in V0.
          unfold mem_lookup in Heqo0.
          congruence.
    Qed.

    Global Instance eUnion_Mem
           {o b:nat}
           (bc: b < o)
           (z: CarrierA)
      : SHOperator_Mem (eUnion fm bc z).
    Proof.

      unshelve esplit.
      -
        apply (eUnion_mem b).
      -
        typeclasses eauto.
      -
        (* mem_out_some *)
        intros m H.
        unfold is_Some, eUnion, eUnion_mem, map_mem_block_elt, mem_lookup. simpl.
        repeat break_match; try some_none; try tauto.
        clear Heqo0. rename Heqo1 into M.
        simpl in *.
        assert(P: Full_set (FinNat 1) (mkFinNat Nat.lt_0_1)) by apply Full_intro.
        apply H in P.
        unfold mem_lookup, mem_in in *.
        apply NP.F.not_find_in_iff in M.
        congruence.
      -
        (* out_mem_fill_pattern *)
        intros m0 m H.
        split.
        +
          simpl in *.
          unfold eUnion_mem, map_mem_block_elt, mem_lookup, mem_in, mem_add, mem_empty in *.
          break_match_hyp; try some_none.
          some_inv.
          subst m.
          intros O.
          destruct (eq_nat_dec j b).
          --
            apply NP.F.in_find_iff.
            rewrite NP.F.add_eq_o; auto.
            some_none.
          --
            unfold FinNatSet.singleton, mkFinNat in O.
            simpl in O.
            congruence.
        +
          simpl in *.
          unfold eUnion_mem, map_mem_block_elt, mem_lookup, mem_in, mem_add, mem_empty in *.
          break_match_hyp; try some_none.
          some_inv.
          subst m.
          intros I.
          unfold FinNatSet.singleton, mkFinNat.
          destruct (eq_nat_dec j b); auto.
          exfalso.
          apply NP.F.in_find_iff in I.
          rewrite NP.F.add_neq_o in I ; auto.
      -
        intros m0 m H j jc C.
        simpl in H.
        unfold eUnion_mem, map_mem_block_elt, mem_lookup, mem_in in *. simpl in *.
        break_match; try some_none.
        some_inv.
        subst m.
        unfold mem_add, mem_empty in C.
        destruct (eq_nat_dec j b); try omega.
        apply NP.F.in_find_iff in C.
        rewrite NP.F.add_neq_o in C; auto.
      -
        assert (facts: SHOperator_Facts fm (eUnion fm bc z)) by
            typeclasses eauto.
        intros x G.
        simpl.
        unfold eUnion_mem, map_mem_block_elt.

        unfold svector_to_mem_block.
        svector_to_mem_block_to_spec m0 H0 I0 O0.
        svector_to_mem_block_to_spec m1 H1 I1 O1.

        break_match; unfold mem_lookup in *; simpl in *.
        +
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
          *
            (* k<o, which is normal *)
            clear O0 O1.
            destruct (eq_nat_dec b k) as [E | NE].
            --
              (* b = k *)
              subst k.
              specialize (H0 b bc).
              specialize (I0 b bc).
              apply H0 in Vb; clear H0.
              apply NM.find_1 in Vb.
              rewrite_clear Vb.
              rewrite NP.F.add_eq_o by reflexivity.
              f_equiv.
              unfold eUnion'.
              rewrite Vbuild_nth.
              dep_destruct (Nat.eq_dec b b); try congruence.

              specialize (H1 0 (lt_0_Sn 0)).
              specialize (I1 0 (lt_0_Sn 0)).
              rewrite NP.F.find_mapsto_iff in H1.

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
            --
              (* k<o, which is normal *)
              (* b!=k *)
              rewrite NP.F.add_neq_o by apply NE.
              rewrite NP.F.empty_o.

              assert(Vk: Is_Struct (Vnth (eUnion' bc z x) kc)).
              {
                destruct facts.
                apply no_vals_at_sparse.
                auto.
              }
              clear H1 I1 m1 Heqo0.

              apply NP.F.not_find_in_iff.
              unfold not.
              intros H.

              specialize (I0 k kc).
              apply I0 in H.
              crush.
          *
            (* k>=o, oob case *)
            specialize (O0 k kc).
            rewrite_clear O0.
            rewrite NP.F.add_neq_o by (unfold lt, nat_lt in bc;omega).
            rewrite NP.F.empty_o.
            reflexivity.
        +
          exfalso.
          assert(V:Is_Val (Vnth x (Nat.lt_0_succ 0))).
          {
            apply G.
            apply Full_intro.
          }
          specialize (H1 0 (lt_0_Sn 0)).
          apply H1 in V; clear H1.
          apply NP.F.find_mapsto_iff in V.
          unfold zero in *.
          congruence.
    Qed.

    Global Instance eT_Mem
           {o b:nat}
           (bc: b < o)
      : SHOperator_Mem (eT fm bc).
    Proof.
      unshelve esplit.
      -
        apply (eT_mem b).
      -
        typeclasses eauto.
      -
        (* mem_out_some *)
        intros v H.
        unfold is_Some, eT, eT_mem, map_mem_block_elt, mem_lookup. simpl.
        repeat break_match; try some_none; try tauto.
        clear Heqo0. rename Heqo1 into M.
        simpl in *.
        assert(P: FinNatSet.singleton b (mkFinNat bc)).
        {
          unfold FinNatSet.singleton, mkFinNat.
          auto.
        }
        apply H in P.
        unfold mem_lookup, mem_in in *.
        apply NP.F.not_find_in_iff in M.
        congruence.
      -
        (* out_mem_fill_pattern *)
        intros m0 m H.
        simpl in *.
        unfold eT_mem, map_mem_block_elt, mem_lookup, mem_in in *.
        destruct j; try omega.
        split.
        +
          intros F.
          break_match_hyp; try some_none.
          some_inv.
          subst m.
          unfold mem_add, mem_empty.
          apply NP.F.in_find_iff.
          rewrite NP.F.add_eq_o.
          some_none.
          reflexivity.
        +
          intros I.
          apply Full_intro.
      -
        intros m0 m H.
        simpl in *.
        unfold eT_mem, map_mem_block_elt, mem_lookup, mem_in in *.

        intros j jc.
        unfold not.
        intros C.
        break_match_hyp; try some_none.
        some_inv.
        subst m.
        unfold mem_add, mem_empty in *.
        destruct (eq_nat_dec j 0) as [z | nz].
        +
          lia.
        +
          apply NP.F.add_neq_in_iff in C.
          apply NP.F.empty_in_iff in C.
          tauto.
          auto.
      -
        assert (facts: SHOperator_Facts fm (eT fm bc)) by
            typeclasses eauto.
        intros x G.
        simpl.

        unfold eT_mem , map_mem_block_elt.
        unfold svector_to_mem_block.
        svector_to_mem_block_to_spec m0 H0 I0 O0.
        svector_to_mem_block_to_spec m1 H1 I1 O1.
        Opaque Vnth.
        simpl in *.
        break_match.
        +
          f_equiv.
          unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
          intros k.
          destruct (NatUtil.lt_ge_dec k 1) as [kc | kc].
          *
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
            rewrite NP.F.add_eq_o by omega.
            destruct k.
            --
              rewrite V0.
              f_equiv.
            --
              omega.
          *
            unfold mem_lookup in *.
            rewrite O0 by apply kc.
            rewrite NP.F.add_neq_o by omega.
            rewrite NP.F.empty_o.
            reflexivity.
        +
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

    Global Instance SHPointwise_Mem
           {n: nat}
           (f: FinNat n -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      : SHOperator_Mem (SHPointwise fm f).
    Proof.
      unshelve esplit.
      -
        apply (mem_op_of_hop (HPointwise f)).
      -
        typeclasses eauto.
      -
        (* mem_out_some *)
        intros v H.
        apply mem_out_some_mem_op_of_hop, H.
      -
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        assert (facts: SHOperator_Facts fm (SHPointwise fm f)) by
            typeclasses eauto.

        intros x G.
        simpl.

        assert((∀ (j : nat) (jc : j < n), in_index_set fm
                                                     (SHPointwise fm f)
                                                     (mkFinNat jc) →
                                        mem_in j (svector_to_mem_block x))
               → is_Some (mem_op_of_hop (HPointwise f) (svector_to_mem_block x))) as M by apply mem_out_some_mem_op_of_hop.
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
        +
          intros j jc HH.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply G,HH.
    Qed.

    Global Instance SHInductor_Mem
           (n:nat)
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial: CarrierA):
      SHOperator_Mem (SHInductor fm n f initial).
    Proof.
      unshelve esplit.
      -
        apply (mem_op_of_hop (HInductor n f initial)).
      -
        typeclasses eauto.
      -
        (* mem_out_some *)
        intros v H.
        apply mem_out_some_mem_op_of_hop, H.
      -
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        intros x H.
        simpl.
        unfold SHInductor', HInductor, compose, mem_op_of_hop, HCOLImpl.Scalarize, Lst.
        Opaque liftM.
        simpl.
        break_match.
        +
          f_equiv.
          dep_destruct t.
          dep_destruct x0. clear x0 t.
          unfold svector_to_mem_block, avector_to_mem_block.
          svector_to_mem_block_to_spec m0 H0 I0 O0.
          avector_to_mem_block_to_spec m2 H2 O2.
          simpl in *.
          unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal.
          intros k.
          destruct (lt_ge_dec k 1) as [kc | nkc].
          *
            clear O0 O2 I0.
            unfold mem_lookup, mem_empty in *.
            dep_destruct k; try lia.
            specialize (H2 0 kc).
            rewrite H2; clear H2.
            rewrite Vnth_0.
            simpl.
            specialize (H0 0 kc).
            rewrite Vnth_0 in H0.
            destruct H0 as [H0 _].
            unfold Is_Val, compose in H0.
            simpl in H0.
            rewrite execWriter_liftM in H0.
            dep_destruct x.
            dep_destruct x0. clear x.
            simpl in H0.

            destruct (IsVal_dec (execWriter h)) as [V|NV].
            --
              specialize (H0 V).
              clear V H.
              apply NM.find_1 in H0.
              rewrite H0.
              f_equiv.
              rewrite evalWriter_Rtheta_liftM.
              replace h0 with (evalWriter h).
              reflexivity.

              rename Heqo into C.
              unfold svector_to_mem_block, mem_block_to_avector in C.
              simpl in C.
              break_match_hyp; try some_none.
              unfold mem_lookup, mem_add, mem_empty in *.
              break_if.
              ++
                erewrite NP.F.add_eq_o in Heqo by reflexivity.
                repeat some_inv.
                subst.
                reflexivity.
              ++
                contradict Heqo.
                apply None_ne_Some.
                apply NP.F.empty_o.
            --
              contradict NV.
              specialize (H 0 kc).
              apply H.
              apply Full_intro.
          *
            rewrite O0, O2; auto.
        +
          exfalso.
          rename Heqo into C.
          dep_destruct x.
          dep_destruct x0.
          unfold svector_to_mem_block, mem_block_to_avector in C.
          simpl in C.
          break_match_hyp; try some_none.
          clear C; rename Heqo into C.
          unfold mem_lookup, mem_add, mem_empty in *.
          break_if.
          *
            erewrite NP.F.add_eq_o in C by reflexivity.
            some_none.
          *
            clear C.
            simpl in *.
            clear Heqd.
            contradict n0.
            specialize (H 0 Nat.lt_0_1).
            rewrite Vnth_0 in H.
            simpl in H.
            eapply H.
            apply Full_intro.
    Qed.

  End WithMonoid.

  (* TODO: move somewhere in Utils *)
  Lemma In_Add_eq
        {T:Type}
        {a b: T}
        {l: Ensemble T}
    :
      a≡b -> Ensembles.In T (Ensembles.Add T l a) b.
  Proof.
    intros E.
    unfold Ensembles.Add.
    apply Union_intror.
    rewrite E.
    apply Ensembles.In_singleton.
  Qed.

  (* TODO: move somewhere in Utils *)
  Lemma In_Add_neq
        {T:Type}
        (a b: T)
        {l: Ensemble T}
    :
      a≢b -> Ensembles.In T l b <-> Ensembles.In T (Ensembles.Add T l a) b.
  Proof.
    intros E.
    split.
    -
      intros H.
      unfold Ensembles.Add.
      apply Union_introl, H.
    -
      intros H.
      unfold Ensembles.Add in H.
      destruct H.
      + apply H.
      + exfalso.
        unfold Ensembles.In in H.
        destruct H.
        congruence.
  Qed.

  Section MonoidSpecific.

    Global Instance SHBinOp_RthetaSafe_Mem
           {o}
           (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : SHOperator_Mem (@SHBinOp Monoid_RthetaSafeFlags o f pF).
    Proof.
      unshelve esplit.
      -
        apply (mem_op_of_hop (HBinOp f)).
      -
        typeclasses eauto.
      -
        intros v H.
        apply mem_out_some_mem_op_of_hop, H.
      -
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      -
        assert (facts: SHOperator_Facts _ (SHBinOp Monoid_RthetaSafeFlags f)) by
            typeclasses eauto.

        intros x G.
        simpl.

        assert((∀ (j : nat) (jc : j < o+o), in_index_set Monoid_RthetaSafeFlags
                                                       (SHBinOp Monoid_RthetaSafeFlags f)
                                                       (mkFinNat jc) →
                                          mem_in j (svector_to_mem_block x))
               → is_Some (mem_op_of_hop (HBinOp f) (svector_to_mem_block x))) as M by apply mem_out_some_mem_op_of_hop.
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
        +
          intros j jc HH.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply G,HH.
    Qed.

    (* TODO: move to memory. add similar to m2. *)
    Lemma mem_keys_disjoint_inr
          (m1 m2: mem_block)
          (k: NM.key):
      is_disjoint (mem_keys_set m1) (mem_keys_set m2) ≡ true
      -> mem_in k m1 -> not (mem_in k m2).
    Proof.
      intros D M1 M2.
      apply mem_keys_set_In in M1.
      apply mem_keys_set_In in M2.
      generalize dependent (mem_keys_set m1).
      generalize dependent (mem_keys_set m2).
      intros s1 M1 s2 D M2.
      clear m1 m2.
      apply is_disjoint_Disjoint in D.
      rewrite NE.In_In in M1.
      rewrite NE.In_In in M2.
      destruct D as [D].
      specialize (D k).
      contradict D.
      unfold Ensembles.In.
      apply Intersection_intro; auto.
    Qed.

    (* TODO: move to memory.v *)
    Lemma is_disjoint_sym {a b}:
      is_disjoint a b ≡ is_disjoint b a .
    Proof.
      destruct (is_disjoint a b) eqn:AB;
        destruct (is_disjoint a b) eqn:BA; try inversion AB.
      -
        clear AB.
        symmetry.
        rewrite <- is_disjoint_Disjoint.
        rewrite <- is_disjoint_Disjoint in BA.
        apply Disjoint_intro.
        intros x.
        destruct BA as [BA].
        specialize (BA x).
        intros AB.
        contradict BA.
        apply Constructive_sets.Intersection_inv in AB.
        destruct AB as [A B].
        unfold Ensembles.In.
        apply Intersection_intro; auto.
      -
        clear AB. rename BA into AB.
        symmetry.
        apply not_true_is_false.
        rewrite <- is_disjoint_Disjoint.
        apply BoolUtil.false_not_true in AB.
        rewrite <- is_disjoint_Disjoint in AB.
        intros BA.
        contradict AB.
        apply Disjoint_intro.
        intros x.
        destruct BA as [BA].
        specialize (BA x).
        intros AB.
        contradict BA.
        apply Constructive_sets.Intersection_inv in AB.
        destruct AB as [A B].
        unfold Ensembles.In.
        apply Intersection_intro; auto.
    Qed.

    Fact HTSUMUnion_mem_out_fill_pattern
         {i o : nat}
         {dot : SgOp CarrierA}
         {dot_mor : Proper (equiv ==> equiv ==> equiv) dot}
         (op1 op2 : SHOperator Monoid_RthetaFlags)
         `{Meq1: SHOperator_Mem _ i o op1}
         `{Meq2: SHOperator_Mem _ i o op2} :
      forall (m0 m : mem_block),
        HTSUMUnion_mem (mem_op (xop:=op1)) (mem_op (xop:=op2)) m0 ≡ Some m
        → forall (j : nat) (jc : j < o),
          out_index_set (i:=i) Monoid_RthetaFlags
                        (HTSUMUnion Monoid_RthetaFlags dot op1
                                    op2) (mkFinNat jc) ↔
                        mem_in j m.
    Proof.
      intros m0 m E.
      split; intros H.
      +
        simpl in *.
        unfold HTSUMUnion_mem in E.
        repeat break_match_hyp; try some_none.
        apply mem_merge_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
        destruct E as [E0 E1].
        dependent destruction H; apply E1.
        *
          left.
          eapply (out_mem_fill_pattern _ _ Heqo0); eauto.
        *
          right.
          eapply (out_mem_fill_pattern _ _ Heqo1); eauto.
      +
        simpl in *.
        unfold HTSUMUnion_mem in E.
        repeat break_match_hyp; try some_none.
        apply mem_merge_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
        destruct E as [E0 E1].
        specialize (E0 H). clear H E1.
        destruct E0 as [M1 | M2].
        *
          apply Union_introl.
          eapply (out_mem_fill_pattern _ _ Heqo0); eauto.
        *
          right.
          eapply (out_mem_fill_pattern _ _ Heqo1); eauto.
    Qed.

    Global Instance HTSUMUnion_Mem
           {i o: nat}
           `{dot: SgOp CarrierA}
           `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
           (op1 op2: @SHOperator Monoid_RthetaFlags i o)
           (compat: Disjoint _
                             (out_index_set _ op1)
                             (out_index_set _ op2)
           )
           `{Meq1: SHOperator_Mem _ i o op1}
           `{Meq2: SHOperator_Mem _ i o op2}

           `{a_zero: MonUnit CarrierA}
           (* `a_zero` together with `dot` form a monoid. NONE: using `eq` here *)
           `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA (@eq CarrierA) dot a_zero}

           (* Structural values in `op1` output evaluate to `a_zero` *)
           (Z1: forall x (t:nat) (tc:t<o),
               ¬ out_index_set _ op1 (mkFinNat tc) ->
               evalWriter (Vnth (op Monoid_RthetaFlags op1 x) tc) ≡ a_zero)

           (* Structural values in `op2` output evaluate to `a_zero` *)
           (Z2: forall x (t:nat) (tc:t<o),
               ¬ out_index_set _ op2 (mkFinNat tc) ->
               evalWriter (Vnth (op Monoid_RthetaFlags op2 x) tc) ≡ a_zero)

      : SHOperator_Mem
          (facts := HTSUMUnion_Facts dot op1 op2 compat)
          (HTSUMUnion Monoid_RthetaFlags dot op1 op2).
    Proof.
      unshelve esplit.
      -
        apply (HTSUMUnion_mem
                 (mem_op (xop:=op1))
                 (mem_op (xop:=op2))).
      -
        apply HTSUMUnion_mem_proper; [apply Meq1 | apply Meq2].
      -
        (* mem_out_some *)
        intros m H.
        unfold is_Some, HTSUMUnion, HTSUMUnion_mem in *.
        simpl in *.
        repeat break_match; try some_none; try auto.
        +
          contradict Heqo0.
          clear H.
          apply mem_merge_is_Some.
          pose proof (out_mem_fill_pattern m m0 Heqo1) as P1.
          pose proof (out_mem_oob m m0 Heqo1) as NP1.
          pose proof (out_mem_fill_pattern m m1 Heqo2) as P2.
          pose proof (out_mem_oob m m1 Heqo2) as NP2.

          apply Disjoint_intro.
          intros j.
          destruct (NatUtil.lt_ge_dec j o) as [jc | jc].
          *
            clear NP1 NP2.
            specialize (P1 j jc).
            specialize (P2 j jc).
            destruct compat as [compat].
            specialize (compat (mkFinNat jc)).
            intros C.
            unfold In, not  in *.
            destruct C as [j H0 H1].

            apply NE.In_In, mem_keys_set_In, P1 in H0. clear P1.
            apply NE.In_In, mem_keys_set_In, P2 in H1. clear P2.
            destruct compat.
            apply Intersection_intro; auto.
          *
            specialize (NP1 j jc).
            intros C.
            destruct C as [j H0 _].
            apply NE.In_In, mem_keys_set_In in H0.
            unfold mem_in in NP1.
            congruence.
        +
          clear Heqo0.
          contradict Heqo2.
          apply is_Some_ne_None.
          apply mem_out_some; auto.
          intros j jc H0.
          specialize (H j jc).
          apply H.
          apply Union_intror.
          apply H0.
        +
          clear Heqo0.
          contradict Heqo1.
          apply is_Some_ne_None.
          apply mem_out_some; auto.
          intros j jc H0.
          specialize (H j jc).
          apply H.
          apply Union_introl.
          apply H0.
      -
        (* out_mem_fill_pattern *)
        apply HTSUMUnion_mem_out_fill_pattern.
      -
        intros m0 m E j jc H.
        simpl in *.
        unfold HTSUMUnion_mem in E.
        repeat break_match_hyp; try some_none.
        apply mem_merge_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
        destruct E as [E0 E1].
        specialize (E0 H). clear H E1.
        destruct E0 as [M0 | M1].
        --
          eapply (out_mem_oob _ _ Heqo0); eauto.
        --
          eapply (out_mem_oob _ _ Heqo1); eauto.
      -
        intros x G.
        simpl.
        unfold HTSUMUnion', Vec2Union, HTSUMUnion_mem.
        break_match.
        +
          break_match.
          *
            (* both mem_ops return Some *)
            rename m into m1, m0 into m2. (* to match operator indices *)
            destruct (mem_merge m1 m2) eqn:MM.
            --
              apply RelUtil.opt_r_Some.
              unfold mem_block_Equiv, mem_block_equiv, NM.Equal.
              intros k.
              unfold svector_to_mem_block.
              svector_to_mem_block_to_spec m' H0 H1 I2.
              simpl in *.
              destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
              ++
                clear I2.
                (* k<o. Normal *)
                (* each k could be either in out_set of op1 or op2 *)
                specialize (H0 k kc).
                specialize (H1 k kc).

                rename facts0 into facts2,  facts into facts1.

                pose proof (HTSUMUnion_mem_out_fill_pattern op1 op2 ) as P.
                specialize (P (svector_to_mem_block x) m).
                simpl in P.
                unfold HTSUMUnion_mem in P.
                break_match_hyp; try some_none.
                break_match_hyp; try some_none.
                some_inv; subst m3.
                some_inv; subst m0.
                specialize (P MM).
                specialize (P k kc).
                destruct (NP.F.In_dec m k) as [K | NK].
                **
                  (* k in m *)
                  pose proof (mem_merge_key_dec m m1 m2 MM k) as [MD _].
                  specialize (MD K).
                  clear H1.
                  apply P in K; clear P.
                  pose proof (out_as_range _ x (SHOperator_Facts:=HTSUMUnion_Facts dot op1 op2 compat) G k kc) as V.
                  apply V in K; clear V.
                  assert(V:=K).
                  apply H0 in K; clear H0.
                  apply NM.find_1 in K.
                  rewrite_clear K.
                  rewrite Vnth_map2.

                  simpl in V.
                  unfold mem_merge in MM.
                  break_if; try some_none.
                  some_inv.
                  subst m.
                  unfold mem_union.
                  rewrite NM.map2_1 by (destruct MD; auto).

                  inversion MD.
                  ---
                    (* k in m1 *)
                    rename H into M1.
                    assert(NM2: not (NM.In (elt:=CarrierA) k m2)).
                    {
                      apply mem_keys_disjoint_inr with (m1:=m1).
                      apply Heqb.
                      apply M1.
                    }
                    break_match; try (apply NP.F.not_find_in_iff in Heqo0; congruence).


                    (* derive m1[k] *)
                    assert (G1: (∀ (j : nat) (jc : (j < i)%nat), in_index_set Monoid_RthetaFlags op1 (mkFinNat jc) →  Is_Val (Vnth x jc))).
                    {
                      intros j jc H.
                      apply G.
                      apply Union_introl.
                      apply H.
                    }
                    apply Meq1 in G1.
                    rewrite Heqo2 in G1.
                    some_inv.
                    unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal in G1.
                    rewrite <- Heqo0.
                    rewrite <- G1.

                    rewrite find_svector_to_mem_block_some with (kc:=kc).
                    2:{
                      apply NP.F.in_find_iff.
                      rewrite G1.
                      apply NP.F.in_find_iff.
                      apply M1.
                    }

                    f_equiv.
                    unfold SVector.Union.
                    rewrite evalWriter_Rtheta_liftM2.

                    pose proof (out_mem_fill_pattern _ _ Heqo3) as P2.
                    unfold mem_in in P2. specialize (P2 k kc).
                    apply not_iff_compat in P2.
                    apply P2 in NM2.
                    apply Z2 with (x:=x) in NM2.
                    rewrite NM2.
                    apply monoid_right_id.
                    apply af_mon.
                  ---
                    (* k in m2 *)
                    rename H into M2.
                    assert(NM1: not (NM.In (elt:=CarrierA) k m1)).
                    {
                      apply mem_keys_disjoint_inr with (m1:=m2).
                      rewrite is_disjoint_sym.
                      apply Heqb.
                      apply M2.
                    }
                    break_match; try (apply NP.F.not_find_in_iff in NM1; congruence).
                    clear Heqo0.

                    (* derive m2[k] *)
                    assert (G2: (∀ (j : nat) (jc : (j < i)%nat), in_index_set Monoid_RthetaFlags op2 (mkFinNat jc) →  Is_Val (Vnth x jc))).
                    {
                      intros j jc H.
                      apply G.
                      apply Union_intror.
                      apply H.
                    }
                    apply Meq2 in G2.
                    rewrite Heqo3 in G2.
                    some_inv.
                    unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal in G2.
                    rewrite <- G2.

                    rewrite find_svector_to_mem_block_some with (kc:=kc).
                    2:{
                      apply NP.F.in_find_iff.
                      rewrite G2.
                      apply NP.F.in_find_iff.
                      apply M2.
                    }

                    f_equiv.
                    unfold SVector.Union.
                    rewrite evalWriter_Rtheta_liftM2.

                    pose proof (out_mem_fill_pattern _ _ Heqo2) as P1.
                    unfold mem_in in P1. specialize (P1 k kc).
                    apply not_iff_compat in P1.
                    apply P1 in NM1.
                    apply Z1 with (x:=x) in NM1 .
                    rewrite NM1.
                    apply monoid_left_id.
                    apply af_mon.
                **
                  (* k not in m *)
                  replace (NM.find (elt:=CarrierA) k m) with (@None CarrierA)
                    by (symmetry; apply NP.F.not_find_in_iff, NK).
                  apply not_iff_compat in P.
                  apply P in NK; clear P.
                  pose proof (no_vals_at_sparse _ x k kc (SHOperator_Facts:=HTSUMUnion_Facts dot op1 op2 compat)) as NV.
                  apply NV in NK; clear NV.
                  apply not_Is_Val_Is_Struct in NK.
                  apply not_iff_compat in H1.
                  apply H1 in NK; clear H1.
                  apply NP.F.not_find_in_iff in NK.
                  rewrite NK.
                  reflexivity.
              ++
                (* k>=o. m[k] should be None *)
                clear H0 H1.
                specialize (I2 k kc).
                unfold mem_lookup in I2.
                rewrite_clear I2.
                symmetry.
                apply NP.F.not_find_in_iff.
                intros N.
                apply (mem_merge_key_dec m m1 m2 MM k) in N.
                generalize dependent (svector_to_mem_block x).
                intros m0 H1 H2.
                destruct N as [IN1 | IN2].
                **
                  (* prove contradiction in N1 *)
                  pose proof (out_mem_oob _ _ H1) as NP1.
                  specialize (NP1 k kc).
                  unfold mem_in in NP1.
                  congruence.
                **
                  (* prove contradiction in N1 *)
                  pose proof (out_mem_oob _ _ H2) as NP2.
                  specialize (NP2 k kc).
                  unfold mem_in in NP2.
                  congruence.
            --
              contradict MM.
              apply mem_merge_is_Some.
              apply Disjoint_intro.
              intros k.
              intros H.
              unfold Ensembles.In in H.
              destruct H.
              rename x0 into k.
              rename H into IN1, H0 into IN2.
              apply NE.In_In, mem_keys_set_In in IN1.
              apply NE.In_In,mem_keys_set_In in IN2.
              generalize dependent (svector_to_mem_block x).
              intros m H1 H2.
              (* by `compat` hypothes, output index sets of op1 and op2 are disjoint.
               yet, but IN1 and IN2, 'k' belongs to both *)
              pose proof (out_mem_fill_pattern _ _ H1) as P1.
              pose proof (out_mem_oob _ _ H1) as NP1.
              pose proof (out_mem_fill_pattern _ _ H2) as P2.
              pose proof (out_mem_oob _ _ H2) as NP2.
              destruct (NatUtil.lt_ge_dec k o) as [kc | nkc].
              ++
                clear NP1 NP2.
                apply (P1 k kc) in IN1; clear P1.
                apply (P2 k kc) in IN2; clear P2.
                inversion_clear compat.
                specialize (H (mkFinNat kc)).
                crush.
              ++
                specialize (NP1 k nkc).
                unfold mem_in in NP1.
                congruence.
          *
            contradict Heqo1.
            apply is_Some_ne_None.
            apply mem_out_some; auto.
            intros j jc H.
            apply svector_to_mem_block_In with (jc0:=jc).
            apply G.
            simpl.
            apply Union_intror.
            apply H.
        +
          contradict Heqo0.
          apply is_Some_ne_None.
          apply mem_out_some; auto.
          intros j jc H.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply G.
          simpl.
          apply Union_introl.
          apply H.
    Qed.

    Definition get_family_mem_op
               {fm}
               {i o n}
               {op_family: @SHOperatorFamily fm i o n}
               {op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc))}
               (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
               (op_family: @SHOperatorFamily fm i o n):
      forall j (jc:j<n), mem_block -> option mem_block
      := fun j (jc:j<n) => mem_op (SHOperator_Mem:=op_family_mem j jc).


    Global Instance get_family_mem_op_proper
           {fm}
           {i o n}
           (j: nat) (jc: j<n)
           {op_family: @SHOperatorFamily fm i o n}
           {op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc))}
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
           (op_family: @SHOperatorFamily fm i o n):
      Proper ((=) ==> (=)) (get_family_mem_op op_family_mem op_family j jc).
    Proof.
      intros x y E.
      unfold get_family_mem_op.
      apply mem_op_proper, E.
    Qed.

    Global Instance IReduction_mem_aux_proper
           {i o n: nat}
           (j: nat) (jc: j<n)
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
           (op_family_facts: forall j (jc:j<n), SHOperator_Facts Monoid_RthetaSafeFlags (op_family (mkFinNat jc)))
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
      :
        Proper ((=) ==> (=)) (@IReduction_mem_aux n j jc dot (get_family_mem_op op_family_mem op_family)).
    Proof.
      intros x y E.
      induction j.
      -
        simpl.
        rewrite E.
        reflexivity.
      -
        simpl.
        repeat break_match; try some_none.
        +
          f_equiv.
          apply Option_equiv_eq in Heqo0.
          apply Option_equiv_eq in Heqo1.
          apply Option_equiv_eq in Heqo2.
          apply Option_equiv_eq in Heqo3.
          rewrite E in Heqo0.
          rewrite IHj in Heqo1.
          rewrite Heqo1 in Heqo3; clear Heqo1; some_inv.
          rewrite Heqo0 in Heqo2; clear Heqo0; some_inv.
          apply mem_merge_with_arg_proper; auto.
        +
          exfalso.
          apply Option_equiv_eq in Heqo1.
          apply Option_equiv_eq in Heqo3.
          rewrite IHj in Heqo1.
          rewrite Heqo1 in Heqo3.
          some_none.
        +
          exfalso.
          apply Option_equiv_eq in Heqo0.
          apply Option_equiv_eq in Heqo2.
          rewrite E in Heqo0.
          rewrite Heqo0 in Heqo2.
          some_none.
        +
          exfalso.
          apply Option_equiv_eq in Heqo1.
          apply Option_equiv_eq in Heqo3.
          rewrite IHj in Heqo1.
          rewrite Heqo1 in Heqo3.
          some_none.
        +
          exfalso.
          apply Option_equiv_eq in Heqo0.
          apply Option_equiv_eq in Heqo1.
          rewrite E in Heqo0.
          rewrite Heqo0 in Heqo1.
          some_none.
    Qed.

    Fact IReduction_mem_aux_Some
         {i o k}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k)
         (op_family_facts: forall j (jc:j<k), SHOperator_Facts Monoid_RthetaSafeFlags (op_family (mkFinNat jc)))
         (op_family_mem: forall j (jc:j<k), SHOperator_Mem (op_family (mkFinNat jc)))
         (j: nat) (jc: j<k)
         (m: mem_block)
         (initial : CarrierA)
         (H: forall (j0 : nat) (jc0 : j0 < i), in_index_set Monoid_RthetaSafeFlags
                                                     (IReduction dot initial op_family)
                                                     (mkFinNat jc0) → mem_in j0 m)
      :
        is_Some (IReduction_mem_aux jc dot (get_family_mem_op op_family_mem op_family) m).
    Proof.
      induction j.
      -
        simpl in *.
        apply op_family_mem.
        intros t tc H0.
        specialize (H t tc).
        apply H.
        pose proof (family_in_set_includes_members) as P.
        unfold Included,Ensembles.In  in P.
        eapply P.
        eauto.
      -
        simpl.
        repeat break_match; try some_none.
        +
          crush.
        +
          exfalso.
          contradict Heqo1.
          apply is_Some_ne_None.
          apply IHj.
        +
          contradict Heqo0.
          apply is_Some_ne_None.
          apply mem_out_some.
          simpl in *.
          intros t tc H0.
          specialize (H t tc).
          apply H.
          pose proof (family_in_set_includes_members) as P.
          unfold Included,Ensembles.In  in P.
          eapply P.
          eauto.
    Qed.

    Global Instance IReduction_mem_proper
           {i o n}
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
           (op_family_facts: forall j (jc:j<n), SHOperator_Facts Monoid_RthetaSafeFlags (op_family (mkFinNat jc)))
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
      :
        Proper (equiv ==> equiv) (IReduction_mem dot (get_family_mem_op op_family_mem op_family)).
    Proof.
      intros x y E.
      unfold IReduction_mem.
      repeat break_match; try some_none; try reflexivity.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance IReduction_Mem
           {i o k}
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k)
           (op_family_facts: forall j (jc:j<k), SHOperator_Facts Monoid_RthetaSafeFlags (op_family (mkFinNat jc)))
           (op_family_mem: forall j (jc:j<k), SHOperator_Mem (op_family (mkFinNat jc)))
      : SHOperator_Mem (IReduction dot initial op_family).
    Proof.
      unshelve esplit.
      -
        apply (IReduction_mem dot (get_family_mem_op op_family_mem op_family)).
      -
        apply IReduction_mem_proper, pdot.
      -
        (* mem_out_some *)
        intros m H.
        unfold IReduction_mem.
        break_match.
        crush.
        eapply IReduction_mem_aux_Some, H.
      -


    Qed.


  End MonoidSpecific.


End MemVecEq.