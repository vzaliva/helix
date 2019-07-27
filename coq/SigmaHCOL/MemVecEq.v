Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.

Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.MSigmaHCOL.
Require Import Helix.SigmaHCOL.MemSetoid.

Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.SetoidList.

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


Class SHOperator_MSHOperator_compat
      {i o: nat}
      {fm}
      {svalue: CarrierA}
      (sop: @SHOperator fm i o svalue)
      (mop: @MSHOperator i o)
      `{facts: !SHOperator_Facts fm sop}
  :=
    {

      in_pattern_compat:
        Same_set _ (in_index_set fm sop) (m_in_index_set mop);

      out_pattern_compat:
        Same_set _ (in_index_set fm sop) (m_in_index_set mop);

      (* -- Semantics eqivalence -- *)
      mem_vec_preservation:
        forall x,

          (* Only for inputs which comply to `facts` *)
          (∀ (j : nat) (jc : (j < i)%nat),
              in_index_set fm sop (mkFinNat jc) → Is_Val (Vnth x jc))
          ->
          Some (svector_to_mem_block (op fm sop x)) =
          mem_op mop (svector_to_mem_block x)
    }.


Section MemVecEq.

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
        {fm}
        (i o: nat)
        {svalue: CarrierA}
        (xop: @SHOperator fm i o svalue)
        `{mop: SHOperator_Mem fm _ _ _ xop}
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

  Section WithMonoid.

    Variable fm: Monoid RthetaFlags.
    Variable fml: @MonoidLaws RthetaFlags RthetaFlags_type fm.

    Global Instance SHCompose_Mem
           {svalue: CarrierA}
           {i1 o2 o3}
           (op1: @SHOperator fm o2 o3 svalue)
           (op2: @SHOperator fm i1 o2 svalue)
           (compat: Included _ (in_index_set fm op1) (out_index_set fm op2))
           `{Meq1: SHOperator_Mem fm o2 o3 _ op1}
           `{Meq2: SHOperator_Mem fm i1 o2 _ op2}
           `{facts: SHOperator_Facts fm _ _ _ (SHCompose fm op1 op2)}
      : SHOperator_Mem
          (SHCompose fm op1 op2).
    Proof.
        (* mem_vec_preservation *)
        intros x G.
        unfold option_compose, compose.
        simpl in G.

        pose proof (@mem_out_some fm _ _ _ op2 _ Meq2 (svector_to_mem_block x) ) as Rm.
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
    Defined.

    Global Instance eUnion_Mem
           {svalue: CarrierA}
           {o b:nat}
           (bc: b < o)
      : SHOperator_Mem (svalue:=svalue) (eUnion fm bc).
    Proof.
        assert (facts: SHOperator_Facts fm (svalue:=svalue) (eUnion fm bc)) by
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
          assert(Vb: Is_Val (Vnth (eUnion' bc svalue x) bc)).
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
          mem_index_equiv k.

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

              assert(Vk: Is_Struct (Vnth (eUnion' bc svalue x) kc)).
              {
                destruct facts.
                apply no_vals_at_sparse.
                auto.
              }
              clear H1 I1 m1 Heqo0.
              apply Option_equiv_eq.
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
    Defined.

    Global Instance eT_Mem
           {svalue: CarrierA}
           {o b:nat}
           (bc: b < o)
      : SHOperator_Mem (svalue:=svalue) (eT fm bc).
    Proof.
      -
        assert (facts: SHOperator_Facts fm (svalue:=svalue) (eT fm bc)) by
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
          mem_index_equiv k.
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
    Defined.

    Global Instance SHPointwise_Mem
           {svalue: CarrierA}
           {n: nat}
           (f: FinNat n -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      : SHOperator_Mem (svalue:=svalue) (SHPointwise fm f).
    Proof.
        assert (facts: SHOperator_Facts fm (svalue:=svalue) (SHPointwise fm f)) by
            typeclasses eauto.

        intros x G.
        simpl.

        assert((∀ (j : nat) (jc : j < n), in_index_set fm (svalue:=svalue)
                                                       (SHPointwise fm f)
                                                       (mkFinNat jc) →
                                        mem_in j (svector_to_mem_block x))
               → is_Some (mem_op_of_hop (HPointwise f) (svector_to_mem_block x))) as M by apply mem_out_some_mem_op_of_hop.
        apply is_Some_equiv_def in M.
        destruct M as [y M].
        rewrite M.
        f_equiv.
        mem_index_equiv k.

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
    Defined.

    Global Instance SHInductor_Mem
           {svalue: CarrierA}
           (n:nat)
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial: CarrierA):
      SHOperator_Mem (svalue:=svalue) (SHInductor fm n f initial).
    Proof.
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
          mem_index_equiv k.
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
    Defined.

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

    Global Instance SafeCast_Mem
           {svalue: CarrierA}
           {i o}
           (f: @SHOperator Monoid_RthetaSafeFlags i o svalue)
           `{f_mem: SHOperator_Mem _ _ _ _ f}
      :
        SHOperator_Mem (svalue:=svalue) (SafeCast f).
    Proof.
      destruct f_mem.
      unshelve esplit; try assumption.
      intros x H.
      unfold SafeCast, SafeCast'.
      simpl in *.
      specialize (mem_vec_preservation0 (rvector2rsvector _ x)).
      unfold compose.
      rewrite svector_to_mem_block_rsvector2rvector.
      rewrite svector_to_mem_block_rvector2rsvector in mem_vec_preservation0.
      rewrite <- mem_vec_preservation0.
      - reflexivity.
      -
        intros j jc H0.
        specialize (H j jc H0).
        unfold rvector2rsvector.
        rewrite Vnth_map.
        apply Is_Val_Rtheta2RStheta.
        assumption.
    Defined.

    Global Instance UnSafeCast_Mem
           {svalue: CarrierA}
           {i o}
           (f: @SHOperator Monoid_RthetaFlags i o svalue)
           `{f_mem: SHOperator_Mem _ _ _ _ f}
      :
        SHOperator_Mem (svalue:=svalue) (UnSafeCast f).
    Proof.
      destruct f_mem.
      unshelve esplit; try assumption.
      intros x H.
      unfold UnSafeCast, UnSafeCast'.
      simpl in *.
      specialize (mem_vec_preservation0 (rsvector2rvector _ x)).
      unfold compose.
      rewrite svector_to_mem_block_rvector2rsvector.
      rewrite svector_to_mem_block_rsvector2rvector in mem_vec_preservation0.
      rewrite <- mem_vec_preservation0.
      - reflexivity.
      -
        intros j jc H0.
        specialize (H j jc H0).
        unfold rsvector2rvector.
        rewrite Vnth_map.
        apply Is_Val_Rtheta2RStheta.
        assumption.
    Defined.

    Global Instance SHBinOp_RthetaSafe_Mem
           {svalue: CarrierA}
           {o: nat}
           (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
           {facts : SHOperator_Facts Monoid_RthetaSafeFlags (SHBinOp Monoid_RthetaSafeFlags f)}
    : SHOperator_Mem (@SHBinOp Monoid_RthetaSafeFlags svalue o f pF) (facts:=facts).
    Proof.
      -
        intros x G.
        simpl.

        assert((∀ (j : nat) (jc : j < o+o), in_index_set Monoid_RthetaSafeFlags (svalue:=svalue)
                                                         (SHBinOp Monoid_RthetaSafeFlags f)
                                                         (mkFinNat jc) →
                                            mem_in j (svector_to_mem_block x))
               → is_Some (mem_op_of_hop (HBinOp f) (svector_to_mem_block x))) as M by apply mem_out_some_mem_op_of_hop.
        apply is_Some_equiv_def in M.
        destruct M as [y M].
        rewrite M.
        f_equiv.
        mem_index_equiv k.

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
    Defined.

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

    Global Instance HTSUMUnion_Mem
           {a_zero: MonUnit CarrierA}
           {i o: nat}
           `{dot: SgOp CarrierA}
           `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
           `{scompat: BFixpoint a_zero dot}
           (op1 op2: @SHOperator Monoid_RthetaFlags i o a_zero)
           (compat: Disjoint _
                             (out_index_set _ op1)
                             (out_index_set _ op2)
           )
           `{Meq1: SHOperator_Mem _ i o _ op1}
           `{Meq2: SHOperator_Mem _ i o _ op2}

           `{hfacts: SHOperator_Facts Monoid_RthetaFlags _ _ a_zero (HTSUMUnion Monoid_RthetaFlags dot op1 op2)}

           (* `a_zero` together with `dot` form a monoid.  *)
           `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot a_zero}

      : SHOperator_Mem
          (HTSUMUnion Monoid_RthetaFlags dot op1 op2 (svalue:=a_zero)).
    Proof.
        (* mem_vec_preservation *)
        intros x G.
        simpl.
        unfold HTSUMUnion, Vec2Union, HTSUMUnion_mem.
        break_match.
        +
          break_match.
          *
            (* both mem_ops return Some *)
            rename m into m1, m0 into m2. (* to match operator indices *)
            destruct (mem_merge m1 m2) eqn:MM.
            --
              (* mem_merge succeeds *)
              apply RelUtil.opt_r_Some.
              mem_index_equiv k.
              unfold svector_to_mem_block.
              svector_to_mem_block_to_spec m' H0 H1 I2.
              simpl in *.
              destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
              ++
                (* k<o. Normal *)
                clear I2.
                (* each k could be either in out_set of op1 or op2 *)
                specialize (H0 k kc).
                specialize (H1 k kc).

                rename facts0 into facts2,  facts into facts1.

                pose proof (HTSUMUnion_mem_out_fill_pattern
                              op1 op2
                              (svector_to_mem_block x) m) as P.
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
                  unfold HTSUMUnion', Vec2Union.
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
                    unfold equiv, mem_block_Equiv, NM.Equal in G1.
                    rewrite <- Heqo0.
                    rewrite <- G1.

                    rewrite find_svector_to_mem_block_some with (kc:=kc).
                    2:{
                      apply NP.F.in_find_iff.
                      apply None_nequiv_neq.
                      rewrite G1.
                      apply None_nequiv_neq.
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
                    apply svalue_at_sparse with (v:=x) in NM2.
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
                    unfold equiv, mem_block_Equiv in G2.
                    rewrite <- G2.

                    rewrite find_svector_to_mem_block_some with (kc:=kc).
                    2:{
                      apply NP.F.in_find_iff.
                      apply None_nequiv_neq.
                      rewrite G2.
                      apply None_nequiv_neq.
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
                    apply svalue_at_sparse with (v:=x) in NM1.

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
                apply None_equiv_eq.
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
              (* mem_merge fails *)
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
    Defined.

    Definition shrink_op_family_mem
               {svalue: CarrierA}
               {fm}
               {i o k : nat}
               (op_family : SHOperatorFamily fm (svalue:=svalue))
               (op_family_facts: ∀ (j : nat) (jc : j < S k), @SHOperator_Facts fm i o _ (op_family (mkFinNat jc)))
               (op_family_mem: forall j (jc:j< S k), SHOperator_Mem (op_family (mkFinNat jc)))
      :
        (forall (j : nat) (jc : j < k),
            @SHOperator_Mem fm i o svalue
                            ((shrink_op_family fm op_family) (mkFinNat jc))
                            ((shrink_op_family_facts _ _ op_family_facts) j jc))

      :=
        fun j jc => op_family_mem j (le_S jc).

    Definition shrink_op_family_mem_up
               {svalue: CarrierA}
               {fm}
               {i o k : nat}
               (op_family : SHOperatorFamily fm (svalue:=svalue))
               (op_family_facts: ∀ (j : nat) (jc : j < S k), @SHOperator_Facts fm i o _ (op_family (mkFinNat jc)))
               (op_family_mem: forall j (jc:j< S k), SHOperator_Mem (op_family (mkFinNat jc)))
      :
        (forall (j : nat) (jc : j < k),
            @SHOperator_Mem fm i o svalue
                            ((shrink_op_family_up fm op_family) (mkFinNat jc))
                            ((shrink_op_family_facts_up _ _ op_family_facts) j jc))
      := fun j jc => op_family_mem (S j) (lt_n_S jc).

    (* Like [shrink_op_family_mem_up] by [n] times *)
    Definition shrink_op_family_mem_up_n
               {svalue: CarrierA}
               {fm}
               {i o k: nat}
               (d: nat)
               (op_family : SHOperatorFamily fm (svalue:=svalue))
               (op_family_facts: ∀ (j : nat) (jc : j < (k+d)), @SHOperator_Facts fm i o _ (op_family (mkFinNat jc)))
               (op_family_mem: forall j (jc:j < (k+d)), SHOperator_Mem (op_family (mkFinNat jc)))
      :
        (forall (j : nat) (jc : j < k),
            @SHOperator_Mem fm i o svalue
                            ((shrink_op_family_up_n fm d op_family) (mkFinNat jc))
                            ((shrink_op_family_facts_up_n fm d op_family op_family_facts) j jc))
      := fun j jc => op_family_mem (j+d) (Plus.plus_lt_compat_r _ _ _ jc).

    Lemma svector_to_mem_block_equiv
          {fm : Monoid RthetaFlags}
          {n:  nat}
          {a b: svector fm n}
      :
          Vforall2 (fun (x y:Rtheta' fm) => evalWriter x ≡ evalWriter y) a b ->
          Vforall2 (fun (x y:Rtheta' fm) => execWriter x = execWriter y) a b ->
          svector_to_mem_block a = svector_to_mem_block b.
    Proof.
      intros V S.
      unfold svector_to_mem_block.
      svector_to_mem_block_to_spec ma Ma Ia Oa.
      svector_to_mem_block_to_spec mb Mb Ib Ob.
      unfold mem_lookup in *.
      simpl in *.
      mem_index_equiv k.
      destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
      -
        clear Ob Oa.
        specialize (Ma k kc).
        specialize (Mb k kc).
        specialize (Ia k kc).
        specialize (Ib k kc).
        apply Vforall2_elim_nth with (ip:=kc) in V.
        apply Vforall2_elim_nth with (ip:=kc) in S.

        generalize dependent (Vnth a kc).
        generalize dependent (Vnth b kc).
        clear a b.
        intros a Ma Ia b V S Mb Ib.

        destruct (Is_Val_dec a), (Is_Val_dec b).
        +
          apply Ma in i.
          apply Mb in i0.
          apply NM.find_1 in i.
          apply NM.find_1 in i0.
          rewrite i, i0.
          f_equiv.
          rewrite V.
          reflexivity.
        +
          inversion S.
          unfold Is_Val, compose, IsVal, Is_true, not in *.
          repeat break_if; try crush.
        +
          inversion S.
          unfold Is_Val, compose, IsVal, Is_true, not in *.
          repeat break_if; try crush.
        +
          apply not_iff_compat in Ia.
          apply not_iff_compat in Ib.
          apply Ia in n0.
          apply Ib in n1.
          apply NP.F.not_find_in_iff in n0.
          apply NP.F.not_find_in_iff in n1.
          rewrite n0, n1.
          reflexivity.
      -
        rewrite Ob by auto.
        rewrite Oa by auto.
        reflexivity.
    Qed.

    Lemma svector_to_mem_block_Vec2Union_mem_merge_with_def
          {n: nat}
          {a b: svector Monoid_RthetaSafeFlags n}
          {dot: CarrierA -> CarrierA -> CarrierA}
          (def: CarrierA)
          `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
          (compata: Vforall (fun x => not (Is_Val x) -> evalWriter x ≡ def) a)
          (compatb: Vforall Is_Val b)
      :
        svector_to_mem_block (Vec2Union _ dot a b)
        =
        mem_merge_with_def dot
                           def
                          (svector_to_mem_block a)
                          (svector_to_mem_block b).
    Proof.
      unfold Vec2Union.
      mem_index_equiv k.

      unfold svector_to_mem_block.
      svector_to_mem_block_to_spec m0 H0 I0 O0.
      svector_to_mem_block_to_spec m1 H1 I1 O1.
      svector_to_mem_block_to_spec m2 H2 I2 O2.
      simpl in *.
      destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
      -
        clear O0 O1 O2.
        specialize (I0 k kc).
        specialize (I1 k kc).
        specialize (I2 k kc).
        specialize (H0 k kc).
        specialize (H1 k kc).
        specialize (H2 k kc).

        rewrite Vnth_map2 in H0, I0.
        rewrite evalWriterUnion in H0.
        rewrite <- ValUnionIsVal_Safe in I0, H0.

        apply Vforall_nth with (ip:=kc) in compata.
        apply Vforall_nth with (ip:=kc) in compatb.


        generalize dependent (Vnth a kc).
        clear a. intros a compata H0 I0 H1 I1.

        generalize dependent (Vnth b kc).
        clear b. intros b compatb H2 I2 H0 I0.

        unfold mem_merge_with_def.
        rewrite NP.F.map2_1bis by reflexivity.

        pose proof (not_iff_compat H0) as NH0.
        pose proof (not_iff_compat H1) as NH1.
        pose proof (not_iff_compat H2) as NH2.
        pose proof (not_iff_compat I0) as NI0.
        pose proof (not_iff_compat I1) as NI1.
        pose proof (not_iff_compat I2) as NI2.
        destruct H1, H2, H0, NH1, NH2, NH0, NI1, NI2, NI0.
        destruct
          (Is_Val_dec a) as [VA | NVA], (Is_Val_dec b) as [VB | NVB], (NM.find (elt:=CarrierA) k m0) as [vd|] eqn:FD, (NM.find (elt:=CarrierA) k m1) as [va|] eqn:FA, (NM.find (elt:=CarrierA) k m2) as [vb|] eqn:FB;

          repeat match goal with
                 | [H: NM.MapsTo _ _ _ |- _ ]  => apply NM.find_1 in H
                 | [H: context[NM.MapsTo _ _ _] |- _ ]  => rewrite NP.F.find_mapsto_iff in H
                 | [H: not (Is_Val ?x), H': not (Is_Val ?x) ->  _ |- _ ] => specialize (H' H)
                 | [H: Is_Val ?x, H': Is_Val ?x ->  _ |- _ ] => specialize (H' H)
                 | [H: Is_Val ?a, H': Is_Val ?a \/ Is_Val _ ->  _ |- _ ] => specialize (H' (or_introl H))
                 | [H: Is_Val ?b, H': Is_Val _ \/ Is_Val ?b ->  _ |- _ ] => specialize (H' (or_intror H))
                 | [H: ?p, H': ?p -> _ |- _ ] => specialize (H' H)
                 | [ H1: NM.find ?k ?m ≡ Some ?x, H2: NM.find ?k ?m ≡ Some ?y |- _] =>
                   assert (x≡y) by
                       (apply Some_inj_eq;
                        rewrite <- H1, <- H2;
                        reflexivity); subst
                 | [H: NM.find ?k ?m ≡ Some _, H': not (NM.In ?k ?m)  |- _ ] => 
                   apply Some_ne_None in H;  apply NP.F.in_find_iff in H; congruence
        end; simpl; try reflexivity; try congruence.
      -
        clear H0 H1 H2.
        specialize (O0 k kc).
        specialize (O1 k kc).
        specialize (O2 k kc).
        unfold mem_lookup in *.
        rewrite O0.
        symmetry.
        unfold mem_merge_with_def.
        rewrite NP.F.map2_1bis by reflexivity.
        rewrite O1, O2.
        reflexivity.
    Qed.

    (* Set of indices of non-structural elements of a vector *)
    Definition vector_val_index_set
               {fm}
               {n:nat}
               (x: svector fm n): FinNatSet n
      := fun jf => Is_Val (Vnth x (proj2_sig jf)).

    Lemma out_index_set_same_vector_val_index_set
          {svalue: CarrierA}
          {fm}
          {i o: nat}
          (x: svector fm i)
          (xop : @SHOperator fm i o svalue)
          (facts: SHOperator_Facts fm xop)
          (H: forall (j : nat) (jc : j < i), in_index_set fm xop
                                                   (mkFinNat jc) → Is_Val (Vnth x jc))
      :
        Same_set _
                 (out_index_set fm xop)
                 (vector_val_index_set (op fm xop x)).
    Proof.
      split.
      -
        unfold vector_val_index_set.
        unfold Same_set, Included.
        intros t H0.
        unfold Ensembles.In in *.
        destruct t as [j jc].
        eapply out_as_range; eauto.
      -
        unfold vector_val_index_set.
        unfold Same_set, Included.
        intros t H0.
        unfold Ensembles.In in *.
        destruct t as [j jc].

        destruct (out_dec fm (mkFinNat jc)).
        apply H1.
        apply no_vals_at_sparse with (v:=x) in H1; eauto.
        apply not_Is_Val_Is_Struct in H1.
        contradict H1; apply H0. (* strangely congruence does not work here *)
    Qed.

    (* Variant of [out_index_set_same_vector_val_index_set] used in rewriting *)
    Lemma out_index_set_eq_vector_val_index_set
          {svalue: CarrierA}
          {fm}
          {i o: nat}
          (x: svector fm i)
          (xop : @SHOperator fm i o svalue)
          (facts: SHOperator_Facts fm xop)
          (H: forall (j : nat) (jc : j < i), in_index_set fm xop
                                                   (mkFinNat jc) → Is_Val (Vnth x jc))
      :
        (out_index_set fm xop) ≡ (vector_val_index_set (op fm xop x)).
    Proof.
      apply Extensionality_Ensembles.
      apply out_index_set_same_vector_val_index_set; eauto.
    Qed.
    
    Lemma mkEns_mem_keys_In
          (k:nat)
          (m:mem_block)
      :
      NE.mkEns (NSP.of_list (mem_keys_lst m)) k <-> NM.In (elt:=CarrierA) k m.
    Proof.
      unfold mem_keys_lst.
      split.
      -
        intros H.
        apply mem_keys_set_In.
        apply H.
      -
        intros H.
        apply mem_keys_set_In.
        apply H.
    Qed.

    Lemma svector_to_mem_block_index_sets
          {fm}
          {n: nat}
          {v: svector fm n}:
      Same_set _
               (FinNatSet_to_natSet (vector_val_index_set v))
               (NE.mkEns (mem_keys_set (svector_to_mem_block v))).
    Proof.
      unfold vector_val_index_set.
      unfold mem_keys_set.
      unfold svector_to_mem_block.

      svector_to_mem_block_to_spec m0 H0 I0 O0.
      unfold FinNatSet_to_natSet.
      simpl in *.
      unfold Same_set, Included, Ensembles.In.
      split.
      -
        intros k H.
        break_match. 2:inversion H.
        eapply mkEns_mem_keys_In, I0, H.
      -
        intros k H.
        break_match.
        +
          eapply I0, mkEns_mem_keys_In, H.
        +
          apply mkEns_mem_keys_In in H.
          unfold mem_lookup in O0.
          specialize (O0 k g).
          apply NP.F.not_find_in_iff in O0.
          congruence.
    Qed.

    Ltac svector_to_mem_block_to_set_spec H0 :=
      match goal with
      | [ |- context[svector_to_mem_block_spec ?v]] =>
        pose proof (svector_to_mem_block_index_sets (v:=v)) as H0;
        unfold svector_to_mem_block in H0
      | [ H: context[svector_to_mem_block_spec ?v] |- _ ] =>
        pose proof (svector_to_mem_block_index_sets (v:=v)) as H0;
        unfold svector_to_mem_block in H0
      end.

    Lemma svector_to_mem_block_Vec2Union_mem_merge
          {n: nat}
          {a b: svector Monoid_RthetaFlags n}
          (dot: CarrierA → CarrierA → CarrierA)
          `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
          (compat: Disjoint _
                            (vector_val_index_set a)
                            (vector_val_index_set b))

          `{a_zero: MonUnit CarrierA}
          (* `a_zero` together with `dot` form a monoid.  *)
          `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot a_zero}

          (Za: Vforall (fun x => not (Is_Val x) -> evalWriter x = a_zero) a)
          (Zb: Vforall (fun x => not (Is_Val x) -> evalWriter x = a_zero) b)
      :
        Some (svector_to_mem_block (Vec2Union _ dot a b))
        =
        mem_merge
          (svector_to_mem_block a)
          (svector_to_mem_block b).
    Proof.
      unfold Vec2Union.

      unfold svector_to_mem_block.
      svector_to_mem_block_to_set_spec S0.
      svector_to_mem_block_to_spec m0 H0 I0 O0.
      svector_to_mem_block_to_set_spec S1.
      svector_to_mem_block_to_spec m1 H1 I1 O1.
      svector_to_mem_block_to_set_spec S2.
      svector_to_mem_block_to_spec m2 H2 I2 O2.
      simpl in *.
      unfold mem_merge.
      break_if.
      -
        rename Heqb0 into D.
        f_equiv.
        unfold mem_union.
        mem_index_equiv k.
        rewrite NP.F.map2_1bis.

        destruct (NM.find (elt:=CarrierA) k m1) eqn: F1, (NM.find (elt:=CarrierA) k m2) eqn: F2.
        +
          (* both m1 and m2 - impossible *)
          exfalso.
          apply mem_keys_disjoint_inr with (k:=k) in D.
          apply Some_ne_None, NP.F.in_find_iff in F2.
          unfold mem_in in D.
          congruence.
          apply Some_ne_None, NP.F.in_find_iff in F1.
          apply F1.
        +
          (* k in m1 *)
          rewrite <- F1.

          rename F1 into H.
          apply Some_ne_None in H.
          apply NP.F.in_find_iff in H.

          destruct (lt_ge_dec k n) as [kc | nkc].
          *
            clear O0 O1 O2 S0 S1 S2 H2 O2.
            specialize (H0 k kc).
            specialize (H1 k kc).
            specialize (I0 k kc).
            specialize (I1 k kc).
            specialize (I2 k kc).
            rewrite Vnth_map2 in H0.
            rewrite Vnth_map2 in I0.

            apply I1 in H.
            assert(Is_Val (SVector.Union Monoid_RthetaFlags dot (Vnth a kc) (Vnth b kc))) as V.
            {
              apply ValUnionIsVal.
              left.
              apply H.
            }

            apply H1 in H.
            apply NP.F.find_mapsto_iff in H.
            rewrite H.

            apply Some_ne_None, NP.F.in_find_iff in H.

            apply H0 in V.
            apply NP.F.find_mapsto_iff in V.
            rewrite_clear V.

            f_equiv. f_equiv.

            apply NP.F.not_find_in_iff in F2.

            apply I1 in H.
            apply not_iff_compat in I2.
            apply I2 in F2.
            apply Vforall_nth with (ip:=kc) in Zb.
            apply Zb in F2.

            unfold SVector.Union.
            unfold_Rtheta_equiv.
            rewrite evalWriter_Rtheta_liftM2.
            rewrite F2.
            apply monoid_right_id, af_mon.
          *
            unfold mem_lookup in *.
            rewrite O1, O0 by auto.
            reflexivity.
        +
          (* k in m2 *)
          rewrite <- F2.

          rename F2 into H.
          apply Some_ne_None in H.
          apply NP.F.in_find_iff in H.

          destruct (lt_ge_dec k n) as [kc | nkc].
          *
            clear O0 O1 O2 S0 S1 S2 H1 O1.
            specialize (H0 k kc).
            specialize (H2 k kc).
            specialize (I0 k kc).
            specialize (I1 k kc).
            specialize (I2 k kc).
            rewrite Vnth_map2 in H0.
            rewrite Vnth_map2 in I0.

            apply I2 in H.
            assert(Is_Val (SVector.Union Monoid_RthetaFlags dot (Vnth a kc) (Vnth b kc))) as V.
            {
              apply ValUnionIsVal.
              right.
              apply H.
            }

            apply H2 in H.
            apply NP.F.find_mapsto_iff in H.
            rewrite H.

            apply Some_ne_None, NP.F.in_find_iff in H.

            apply H0 in V.
            apply NP.F.find_mapsto_iff in V.
            rewrite_clear V.

            f_equiv. f_equiv.

            apply NP.F.not_find_in_iff in F1.

            apply I2 in H.
            apply not_iff_compat in I1.
            apply I1 in F1.
            apply Vforall_nth with (ip:=kc) in Za.
            apply Za in F1.

            unfold SVector.Union.
            unfold_Rtheta_equiv.
            rewrite evalWriter_Rtheta_liftM2.
            rewrite F1.
            apply monoid_left_id, af_mon.
          *
            unfold mem_lookup in *.
            rewrite O2, O0 by auto.
            reflexivity.
        +
          (* neither in m1 or m2 *)
          destruct (lt_ge_dec k n) as [kc | nkc].
          *
            clear O0 O1 O2 S0 S1 S2 H0 H1 H2.
            specialize (I0 k kc).
            specialize (I1 k kc).
            specialize (I2 k kc).
            apply Option_equiv_eq.
            apply NP.F.not_find_in_iff.
            apply not_iff_compat in I0.
            apply I0. clear I0.
            rewrite Vnth_map2.
            apply not_Is_Val_Is_Struct.
            apply StructUnionIsStruct.
            split; apply not_Is_Val_Is_Struct.
            --
              apply not_iff_compat in I1.
              apply I1.
              apply NP.F.not_find_in_iff, F1.
            --
              apply not_iff_compat in I2.
              apply I2.
              apply NP.F.not_find_in_iff, F2.
          *
            apply Option_equiv_eq.
            apply O0; auto.
        +
          reflexivity.
      -
        contradict Heqb0.
        apply not_false_iff_true.
        apply is_disjoint_Disjoint.
        apply Extensionality_Ensembles in S1.
        apply Extensionality_Ensembles in S2.
        rewrite <- S1, <- S2.
        clear S1 S2.
        apply Disjoint_FinNat_to_nat.
        apply compat.
    Qed.

    Fact Vec2Union_fold_zeros_dense
         {svalue: CarrierA}
         (i o n : nat)
         (x: svector Monoid_RthetaSafeFlags i)
         (dot : CarrierA → CarrierA → CarrierA)
         (initial : CarrierA)
         (op_family : SHOperatorFamily Monoid_RthetaSafeFlags (svalue:=svalue))
         (op_family_facts: forall (j : nat) (jc : j < S n), SHOperator_Facts Monoid_RthetaSafeFlags
                                                                      (op_family (mkFinNat jc)))
         (H : forall (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaSafeFlags op_family
                                                          (mkFinNat jc) → Is_Val (Vnth x jc))

         (v: vector (svector Monoid_RthetaSafeFlags o) n)
         (V:  v ≡ Vbuild
                (λ (i0 : nat) (ip : i0 < n),
                 get_family_op _ op_family
                               (S i0)
                               (lt_n_S ip) x))
         (compat : forall (j : nat) (jc : j < n),
             Same_set (FinNat o)
                      (out_index_set _ (svalue:=svalue) (shrink_op_family_up _ op_family (mkFinNat jc)))
                      (Full_set (FinNat o)))
      :
        Vforall
          (λ a : Rtheta' Monoid_RthetaSafeFlags, ¬ Is_Val a → evalWriter a ≡ initial)
          (Vfold_left_rev
             (Vec2Union Monoid_RthetaSafeFlags dot)
             (Vconst (mkStruct initial) o)
             v).
    Proof.
      apply Vforall_nth_intro.
      intros j jc VV.

      (* [v] is always dense *)

      destruct n.
      -
        dep_destruct v.
        simpl.
        rewrite Vnth_const.
        apply evalWriter_mkStruct.
      -
        contradict VV.
        dep_destruct v; clear v; rename h into v0, x0 into v.
        simpl.
        rewrite AbsorbUnionIndexBinary.
        apply ValUnionIsVal_Safe.
        right.
        rewrite Vbuild_cons in V.
        inversion V.
        apply op_family_facts.
        intros t tc H0.
        apply H.
        eapply family_in_set_includes_members.
        apply H0.
        apply compat.
        apply Full_intro.
    Qed.

    Fact Vec2Union_fold_zeros
         `{svalue: MonUnit CarrierA}
         (i o n : nat)
         (x: svector Monoid_RthetaFlags i)
         `{dot: SgOp CarrierA}
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (op_family : SHOperatorFamily Monoid_RthetaFlags (svalue:=svalue))
         (op_family_facts: forall (j : nat) (jc : j < n), SHOperator_Facts Monoid_RthetaFlags
                                                                    (op_family (mkFinNat jc)))
         (H : forall (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaFlags op_family
                                                          (mkFinNat jc) → Is_Val (Vnth x jc))

         (v: vector (svector Monoid_RthetaFlags o) n)
         (V:  v ≡ Vbuild
                (λ (i0 : nat) (ip : i0 < n),
                 get_family_op _ op_family i0 ip x))
         `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot svalue}
      :
        Vforall
          (λ a : Rtheta' Monoid_RthetaFlags, ¬ Is_Val a → evalWriter a = svalue)
          (Vfold_left_rev
             (Vec2Union Monoid_RthetaFlags dot)
             (Vconst (mkStruct svalue) o)
             v).
    Proof.
      apply Vforall_nth_intro.

      dependent induction n.
      -
        intros j jc H0.
        dep_destruct v.
        simpl.
        rewrite Vnth_const.
        rewrite evalWriter_mkStruct.
        reflexivity.
      -
        intros j jc.
        dep_destruct v. clear v. rename h into v0, x0 into v.
        rewrite Vfold_left_rev_cons.
        rewrite AbsorbUnionIndexBinary.
        rewrite evalWriterUnion.
        intros H0.
        apply NotValUnionNotIsVal in H0.
        destruct H0 as [H0 H2].

        specialize (IHn
                      x
                      dot
                      pdot
                      (shrink_op_family_up _ op_family)
                      (shrink_op_family_facts_up _ _ op_family_facts)
                   ).

        rewrite Vbuild_cons in V;
          apply Vcons_eq_elim in V;
          destruct V as [V0 V].

        rewrite IHn; clear IHn.
        +
          unfold get_family_op in V0.
          pose proof (svalue_at_sparse _ (op_family (mkFinNat (Nat.lt_0_succ n)))) as S.
          specialize (S x j jc).
          subst v0.
          unshelve eapply Not_Is_Val_Not_In_outset in H2.
          intros j0 jc0 H1.
          specialize (H j0 jc0).
          apply H.
          eapply family_in_set_includes_members.
          eapply H1.
          rewrite S.
          *
            apply monoid_left_id.
            apply af_mon.
          *
            apply H2.
        +
          rewrite family_in_index_set_eq in H.
          intros j0 jc0 H1.
          apply family_in_set_implies_members in H1.
          destruct H1 as [t [tc H1]].
          apply H. clear H.
          simpl in *.
          unfold shrink_op_family_up, shrink_op_family in *.
          simpl in *.
          apply Union_intror.
          unfold Ensembles.In in *.
          eapply family_in_set'_includes_members.
          unfold Ensembles.In.
          simpl.
          eapply H1.
        +
          subst v.
          f_equiv.
        +
          apply af_mon.
        +
          apply H0.
    Qed.

    Global Instance IReduction_Mem
           {svalue: CarrierA}
           {i o k: nat}
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           `{scompat: BFixpoint svalue dot}
           (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k svalue)
           (op_family_facts: forall j (jc:j<k), SHOperator_Facts Monoid_RthetaSafeFlags (op_family (mkFinNat jc)))
           (op_family_mem: forall j (jc:j<k), SHOperator_Mem (op_family (mkFinNat jc)))
           (facts : SHOperator_Facts Monoid_RthetaSafeFlags (IReduction dot op_family))
           (compat: forall j (jc:j<k),
               Ensembles.Same_set _
                                  (out_index_set _ (op_family (mkFinNat jc)))
                                  (Full_set _))
      : SHOperator_Mem (IReduction dot op_family) (facts:=facts).
    Proof.
        (* mem_vec_preservation *)
        intros x H.
        rename k into n.
        unfold IReduction, IReduction_mem, Diamond in *.
        simpl in *.
        break_match; rename Heqo0 into A.
        +
          f_equiv.
          remember (Apply_Family' (get_family_op Monoid_RthetaSafeFlags op_family) x)
            as v eqn:A1.

          revert l A A1.
          induction n; intros.
          *
            subst v.
            simpl.
            f_equiv.
            unfold Diamond, MUnion.
            assert(length l = 0) as L by apply (Apply_mem_Family_length A).
            destruct l; try inversion L.
            simpl.
            apply svector_to_mem_block_Vconst_mkStruct.
          *
            assert(length l = S n) as L by apply (Apply_mem_Family_length A).
            destruct l; try inversion L.
            rename m into l0.
            apply Apply_mem_Family_cons in A.
            destruct A as [A0 A].
            assert(forall (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaSafeFlags
                                     (shrink_op_family_up Monoid_RthetaSafeFlags
                                        op_family) (mkFinNat jc) →
                                           Is_Val (Vnth x jc)) as P.
            {
              intros j jc H0.
              apply H.
              apply family_in_set_implies_members in H0.
              destruct H0 as [t [tc H0]].
              unfold shrink_op_family_up in H0.
              eapply family_in_set_includes_members.
              unfold Ensembles.In.
              eapply H0.
            }
            unfold Apply_Family' in A1.
            rewrite Vbuild_cons in A1.
            dep_destruct v.
            clear v. rename h into v0, x0 into v.
            inversion A1 as [[V0 V]]. clear A1.
            apply inj_pair2 in V.

            (* shrink compat *)
            assert(compat': forall (j : nat) (jc : j < n), Same_set (FinNat o)
                             (out_index_set Monoid_RthetaSafeFlags
                                (shrink_op_family_up Monoid_RthetaSafeFlags op_family
                                                     (mkFinNat jc))) (Full_set (FinNat o))).
            {
              intros j jc.
              apply compat.
            }
            specialize (IHn
                          (shrink_op_family_up _ op_family)
                          (shrink_op_family_facts_up _ _ op_family_facts)
                          (shrink_op_family_mem_up _ _ op_family_mem)
                          _
                          compat'
                          P
                          v l
                          A V
                       ).
            clear P.
            unfold MUnion in *.
            simpl.
            rewrite (svector_to_mem_block_Vec2Union_mem_merge_with_def svalue).
            --
              rewrite IHn; clear IHn.
              apply mem_merge_with_def_proper; auto.
              apply Some_inj_equiv.
              rewrite <- A0. clear A0.
              unfold get_family_op, get_family_mem_op.
              eapply mem_vec_preservation.
              intros j jc H0.
              apply H.
              eapply family_in_set_includes_members.
              apply H0.
            --
              apply Vec2Union_fold_zeros_dense with (op_family0:=op_family) (x0:=x); auto.
            --
              apply Vforall_nth_intro.
              intros j jc.
              apply (op_family_facts 0 (Nat.lt_0_succ n)).
              intros t tc HH.
              specialize (H t tc).
              apply H.
              eapply family_in_set_includes_members.
              eapply HH.
              apply compat.
              apply Full_intro.
        +
          (* [A] could not happen *)
          exfalso.
          unfold Apply_mem_Family in A.
          apply monadic_Lbuild_op_eq_None in A.
          destruct A as [t [tc A]].
          contradict A.
          apply is_Some_ne_None.
          apply mem_out_some.
          intros j jc H0.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply H.
          eapply family_in_set_includes_members.
          apply H0.
    Defined.

    Global Instance IUnion_mem_proper
           {svalue: CarrierA}
           {fm}
           {i o n: nat}
           (op_family: @SHOperatorFamily fm i o n svalue)
           (op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc)))
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
      :
        Proper (equiv ==> equiv) (IUnion_mem (get_family_mem_op op_family_mem)).
    Proof.
      intros x y E.
      unfold IUnion_mem.
      simpl.
      repeat break_match.
      -
        apply monadic_fold_left_rev_opt_proper.
        apply mem_merge_proper.
        unshelve eapply Option_equiv_eq in Heqo0; try typeclasses eauto.
        unshelve eapply Option_equiv_eq in Heqo1; try typeclasses eauto.
        rewrite E in Heqo0.
        rewrite Heqo0 in Heqo1.
        some_inv.
        apply Heqo1.
      -
        unshelve eapply Option_equiv_eq in Heqo0; try typeclasses eauto.
        unshelve eapply Option_equiv_eq in Heqo1; try typeclasses eauto.
        rewrite E in Heqo0.
        rewrite Heqo0 in Heqo1.
        some_none.
      -
        unshelve eapply Option_equiv_eq in Heqo0; try typeclasses eauto.
        unshelve eapply Option_equiv_eq in Heqo1; try typeclasses eauto.
        rewrite E in Heqo0.
        rewrite Heqo0 in Heqo1.
        some_none.
      -
        reflexivity.
    Qed.

    Lemma Apply_mem_Family_eq_Some
          {svalue: CarrierA}
          {i o k : nat}
          {op_family : @SHOperatorFamily Monoid_RthetaFlags i o k svalue}
          {op_family_facts : ∀ (j : nat) (jc : j < k), SHOperator_Facts Monoid_RthetaFlags
                                                                      (op_family (mkFinNat jc))}
          {op_family_mem : ∀ (j : nat) (jc : j < k), SHOperator_Mem (op_family (mkFinNat jc))}
          {m : NatMap CarrierA}
          {l: list mem_block}
      :
        (Apply_mem_Family (get_family_mem_op op_family_mem) m ≡ Some l)
        -> (forall (j : nat) (jc : j < k), nth_error l j ≡ get_family_mem_op op_family_mem j jc m).
    Proof.
      unfold Apply_mem_Family.
      apply monadic_Lbuild_op_eq_Some.
    Qed.

    (* TODO: move *)
    Definition cast_op_family
               {svalue: CarrierA}
               {fm}
               {i o n m: nat}
               (op_family: @SHOperatorFamily fm i o m svalue)
               (E: m≡n)
      :
      @SHOperatorFamily fm i o n svalue
      :=
        match E in _ ≡ p return (@SHOperatorFamily fm i o p svalue) with
        | eq_refl => op_family
        end.

    Lemma cast_op_family_facts
          {svalue: CarrierA}
          {fm}
          {i o n m: nat}
          {op_family: @SHOperatorFamily fm i o m svalue}
          (op_family_facts : forall (j: nat) (jc: j < m),
              SHOperator_Facts fm
                               (op_family (mkFinNat jc)))
          (E: m≡n):
      forall (j : nat) (jc : j < n),
        SHOperator_Facts fm (cast_op_family op_family E (mkFinNat jc)).
    Proof.
      intros j jc.
      crush.
      (* TODO: better proof. *)
    Defined.

    Lemma cast_op_family_mem
          {svalue: CarrierA}
          {fm}
          {i o n m: nat}
          {op_family: @SHOperatorFamily fm i o m svalue}
          {op_family_facts : forall (j: nat) (jc: j < m),
              SHOperator_Facts fm (op_family (mkFinNat jc))}
          (op_family_mem : forall (j: nat) (jc: j < m),
              SHOperator_Mem (facts:=op_family_facts j jc) (op_family (mkFinNat jc)))
          (E: m≡n):
      forall (j : nat) (jc : j < n),
        SHOperator_Mem
          (facts:=cast_op_family_facts op_family_facts E j jc)
          (cast_op_family op_family E (mkFinNat jc)).
    Proof.
      intros j jc.
      unfold cast_op_family.
      break_match.
      auto.
    Defined.

    Lemma cast_mem_op_eq
          {svalue: CarrierA}
          {fm}
          {i o n m : nat}
          (t t': nat)
          (Et: t ≡ t')
          {tm: t<m}
          {tn: t'<n}
          {op_family: @SHOperatorFamily fm i o m svalue}
          {op_family_facts : forall (j: nat) (jc: j < m),
              SHOperator_Facts fm (op_family (mkFinNat jc))}
          (op_family_mem : forall (j: nat) (jc: j < m),
              SHOperator_Mem (facts:=op_family_facts j jc) (op_family (mkFinNat jc)))
          (E: m≡n):

      (@mem_op fm i o _
               (cast_op_family op_family E (mkFinNat tn))
               (cast_op_family_facts op_family_facts E t' tn)
               (cast_op_family_mem op_family_mem E t' tn))
        ≡
        (@mem_op fm i o _
                 (op_family (mkFinNat tm))
                 (op_family_facts t tm)
                 (op_family_mem t tm)).
    Proof.
      subst.
      replace tm with tn by apply lt_unique.
      reflexivity.
    Qed.

    Lemma cast_op_eq
          {svalue: CarrierA}
          {fm}
          {i o n m : nat}
          {x: svector fm i}
          (t t': nat)
          (Et: t ≡ t')
          {tm: t<m}
          {tn: t'<n}
          {op_family: @SHOperatorFamily fm i o m svalue}
          (E: m≡n):

      @get_family_op fm i o m svalue op_family t tm x
                     ≡
      @get_family_op fm i o n svalue
                     (cast_op_family op_family E) t' tn x.
    Proof.
      subst.
      replace tm with tn by apply lt_unique.
      reflexivity.
    Qed.

    Lemma cast_out_index_set_eq
          {svalue: CarrierA}
          {fm}
          {i o n m : nat}
          (t: nat)
          {tm: t<m}
          {tn: t<n}
          {op_family: @SHOperatorFamily fm i o m svalue}
          {op_family_facts : forall (j: nat) (jc: j < m),
              SHOperator_Facts fm (op_family (mkFinNat jc))}
          (E: m≡n):
      out_index_set fm (op_family (mkFinNat tm))
                    ≡
                    out_index_set fm
                    (cast_op_family op_family E (mkFinNat tn)).
    Proof.
      subst.
      replace tm with tn by apply lt_unique.
      reflexivity.
    Qed.

    Lemma cast_in_index_set_eq
          {svalue: CarrierA}
          {fm}
          {i o n m : nat}
          (t: nat)
          {tm: t<m}
          {tn: t<n}
          {op_family: @SHOperatorFamily fm i o m svalue}
          {op_family_facts : forall (j: nat) (jc: j < m),
              SHOperator_Facts fm (op_family (mkFinNat jc))}
          (E: m≡n):
      in_index_set fm (op_family (mkFinNat tm))
                    ≡
                    in_index_set fm
                    (cast_op_family op_family E (mkFinNat tn)).
    Proof.
      subst.
      replace tm with tn by apply lt_unique.
      reflexivity.
    Qed.

    Fact IUnion_mem_step_disjoint
         {svalue: CarrierA}
         {i o n : nat}
         (d: nat)
         (op_family: @SHOperatorFamily Monoid_RthetaFlags i o (n+d) svalue)
         (op_family_facts: ∀ (j : nat) (jc : j < (n+d)),
             @SHOperator_Facts Monoid_RthetaFlags i o _
                               (op_family (@mkFinNat (n+d) j jc)))

         (op_family_mem: forall j (jc: j < (n+d)), SHOperator_Mem (op_family (mkFinNat jc)))

         (compat : ∀ (m0 : nat) (mc : m0 < (n+d)) (n0 : nat) (nc : n0 < (n+d)),
             m0 ≢ n0
             → Disjoint (FinNat o)
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat mc)))
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat nc))))

         (m m0 m1 : mem_block)
         (l: list mem_block)
         (A : Apply_mem_Family
                (get_family_mem_op
                   (shrink_op_family_mem_up_n d op_family op_family_facts op_family_mem)) m
                ≡ Some l)

         (t:nat)
         (tc: t<d)
         (tc1: t<n+d)
         (H0: get_family_mem_op op_family_mem t tc1 m ≡ Some m0)

         (H1: monadic_fold_left_rev mem_merge mem_empty l ≡ Some m1)
      :
        Disjoint nat
                 (NE.mkEns (mem_keys_set m1))
                 (NE.mkEns (mem_keys_set m0)).
    Proof.
      pose proof (Apply_mem_Family_length A) as L.
      dependent induction n.
      -
        destruct l. 2:inversion L.
        simpl in *.
        some_inv.
        subst.
        unfold mem_empty, mem_keys_set.
        simpl.
        apply Disjoint_intro.
        intros x C.
        unfold Ensembles.In in C.
        destruct C.
        inversion H.
      -
        destruct l as [| m1h m1t];  inversion L.
        apply Apply_mem_Family_cons in A.
        destruct A as [A0 A].
        simpl in H1.
        break_match_hyp; try some_none.
        apply Disjoint_Symmetric.
        apply (Disjoint_of_mem_merge H1 (m0:=m0)).
        +
          apply Disjoint_Symmetric.
          assert(K: (Init.Nat.add (S n) d) ≡ (Init.Nat.add n (S d))) by lia.

          assert(tc2: S t <= n + S d).
          {
            rewrite <- K.
            apply tc1.
            (* (eq_ind (S n + d) (λ n0 : nat, S t <= n0) tc1 (n + S d) K) *)
          }
          specialize IHn with (d:=(S d))
                              (m:=m)
                              (m0:=m0)
                              (l:=m1t)
                              (t:=t)
                              (tc1:=tc2)
                              (op_family:=cast_op_family op_family K)
                              (op_family_facts:=cast_op_family_facts op_family_facts K)
                              (op_family_mem:=cast_op_family_mem op_family_mem K)
          .

          eapply IHn; eauto.
          *
            intros m0' mc' n0' nc' H.
            assert(mc'': m0' < S n + d) by lia.
            assert(nc'': n0' < S n + d) by lia.
            specialize (compat m0' mc'' n0' nc'' H).

            erewrite <- cast_out_index_set_eq.
            erewrite <- cast_out_index_set_eq.
            apply compat.
            eapply op_family_facts.
            eapply op_family_facts.
          *
            rewrite <- A.
            unfold shrink_op_family_mem_up, shrink_op_family_up, shrink_op_family_facts_up,
            shrink_op_family_mem, shrink_op_family, shrink_op_family_facts,
            shrink_op_family_up_n, shrink_op_family_facts_up_n, shrink_op_family_mem_up_n.
            clear.
            f_equiv.
            unfold get_family_mem_op.
            extensionality j.
            extensionality jc.
            simpl.
            apply cast_mem_op_eq.
            lia.
          *
            rewrite <- H0.
            clear.
            unfold get_family_mem_op.
            apply equal_f.
            apply cast_mem_op_eq; auto.
        +
          clear IHn A Heqo0.
          unfold get_family_mem_op in A0, H0.
          unfold shrink_op_family_mem_up, shrink_op_family_up, shrink_op_family_facts_up,
          shrink_op_family_mem, shrink_op_family, shrink_op_family_facts,
          shrink_op_family_up_n, shrink_op_family_facts_up_n, shrink_op_family_mem_up_n
            in *.
          simpl in *.
          specialize (compat t tc1).
          specialize (compat d (Plus.plus_lt_compat_r O (S n) d (Nat.lt_0_succ n))).
          apply Disjoint_FinNat_to_nat in compat.
          rewrite (mem_keys_set_to_out_index_set _ _ _ _ _ H0) in compat.
          rewrite (mem_keys_set_to_out_index_set _ _ _ _ _ A0) in compat.
          apply compat.
          lia.
    Qed.

    Fact IUnion_mem_1_step_disjoint
         {svalue: CarrierA}
         {i o n : nat}
         (op_family: @SHOperatorFamily Monoid_RthetaFlags i o (S n) svalue)
         (op_family_facts: ∀ (j : nat) (jc : j < (S n)),
             @SHOperator_Facts Monoid_RthetaFlags i o _
                               (op_family (@mkFinNat (S n) j jc)))

         (op_family_mem: forall j (jc: j < (S n)), SHOperator_Mem (op_family (mkFinNat jc)))

         (compat : ∀ (m0 : nat) (mc : m0 < (S n)) (n0 : nat) (nc : n0 < (S n)),
             m0 ≢ n0
             → Disjoint (FinNat o)
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat mc)))
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat nc))))

         (m m0 m1 : mem_block)
         (l: list mem_block)
         (A : Apply_mem_Family
                (get_family_mem_op
                   (shrink_op_family_mem_up op_family op_family_facts op_family_mem)) m
                ≡ Some l)

         (t:nat)
         (H0: get_family_mem_op op_family_mem 0 (Nat.lt_0_succ n) m ≡ Some m0)

         (H1: monadic_fold_left_rev mem_merge mem_empty l ≡ Some m1)
      :
        Disjoint nat
                 (NE.mkEns (mem_keys_set m1))
                 (NE.mkEns (mem_keys_set m0)).
    Proof.
      (* same as [IUnion_mem_step_disjoint] with [d:=1] *)
      assert(E: S n ≡ n + 1) by lia.
      assert(zc2: 0 < n + 1) by lia.
      eapply IUnion_mem_step_disjoint with
          (d:=1)
          (t0:=0)
          (tc1:=zc2)
          (m2:=m)
          (op_family_mem0 := cast_op_family_mem op_family_mem E); eauto.
      -
        intros m0' mc' n0' nc' H.
        assert(mc'': m0' < S n ) by lia.
        assert(nc'': n0' < S n ) by lia.
        specialize (compat m0' mc'' n0' nc'' H).
        erewrite <- cast_out_index_set_eq.
        erewrite <- cast_out_index_set_eq.
        apply compat.
        eapply op_family_facts.
        eapply op_family_facts.
      -
        rewrite <- A.
        unfold shrink_op_family_mem_up, shrink_op_family_up, shrink_op_family_facts_up,
        shrink_op_family_mem, shrink_op_family, shrink_op_family_facts,
        shrink_op_family_up_n, shrink_op_family_facts_up_n, shrink_op_family_mem_up_n.
        clear.
        f_equiv.
        unfold get_family_mem_op.
        extensionality j.
        extensionality jc.
        apply cast_mem_op_eq.
        lia.
      -
        rewrite <- H0.
        clear.
        unfold get_family_mem_op.
        apply equal_f.
        apply cast_mem_op_eq; auto.
    Qed.

    Lemma vector_val_index_set_Vconst_Empty
          {fm}
          {fml: @MonoidLaws RthetaFlags RthetaFlags_type fm}
          {n:nat}
          {svalue: CarrierA}
      :
        vector_val_index_set (fm:=fm) (Vconst (mkStruct svalue) n)
                             ≡ Empty_set (FinNat n).
    Proof.
      apply Extensionality_Ensembles.
      split; intros j H.
      -
        exfalso.
        unfold Ensembles.In in H.
        unfold vector_val_index_set in H.
        destruct j as [j jc].
        rewrite Vnth_const in H.
        apply Is_Val_mkStruct in H.
        tauto.
      -
        apply Constructive_sets.Noone_in_empty in H.
        tauto.
    Qed.

    Lemma sparse_outputs_not_in_out_set
          {svalue: CarrierA}
          {fm}
          {i o t: nat}
          (tc: t<o)
          (x: svector fm i)
          (xop: @SHOperator fm i o svalue)
          (facts: SHOperator_Facts fm xop)
          (G: forall (j : nat) (jc : j < i), in_index_set fm xop
                                                   (mkFinNat jc) → Is_Val (Vnth x jc))
      :
        ¬ Is_Val (Vnth (op _ xop x) tc) -> ¬ out_index_set _ xop (mkFinNat tc).
    Proof.
      intros H.
      contradict H.
      apply out_as_range ; eauto.
    Qed.

    (* This lemma could be proven for both [Monoid_RthetaFlags]
       and [Monoid_RthetaSafeFlags] but not for generic [fm].

       Since we currently need it only for [Monoid_RthetaFlags]
       this is what we prove here.
     *)
    Lemma vector_val_index_set_Vec2Union
          {n}
          (dot: CarrierA -> CarrierA -> CarrierA)
          (a b: svector Monoid_RthetaFlags n)
      :
      vector_val_index_set (Vec2Union _ dot a b) ≡
                           Union _
                           (vector_val_index_set a)
                           (vector_val_index_set b).
    Proof.
      unfold Vec2Union.
      apply Extensionality_Ensembles.
      split.
      -
        unfold Included.
        intros x H.
        unfold Ensembles.In in *.
        unfold vector_val_index_set in *.
        rewrite Vnth_map2 in H.
        apply ValUnionIsVal in H.
        destruct H as [Ha | Hb].
        +
          apply Union_introl.
          apply Ha.
        +
          apply Union_intror.
          apply Hb.
      -
        unfold Included.
        intros x H.
        unfold Ensembles.In in *.
        unfold vector_val_index_set in *.
        rewrite Vnth_map2.
        apply ValUnionIsVal.
        destruct H; auto.
    Qed.


    (* Due to dependency on [vector_val_index_set_Vec2Union] this lemma could
       be proven for both [Monoid_RthetaFlags]  and [Monoid_RthetaSafeFlags] but
       not for generic [fm].

       Since we currently need it only for [Monoid_RthetaFlags]
       this is what we prove here. *)
    Lemma vector_val_index_set_Apply_Family
          {svalue : CarrierA}
          {i o n : nat}
          (dot : CarrierA → CarrierA → CarrierA)
          (x : vector (Rtheta' _) i)
          (op_family : @SHOperatorFamily Monoid_RthetaFlags i o n svalue)
          {op_family_facts : forall (j : nat) (jc : j < n),
              SHOperator_Facts _ (op_family (mkFinNat jc))}
          {H : ∀ (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaFlags op_family
                                                           (mkFinNat jc) → Is_Val (Vnth x jc)}
      :
        vector_val_index_set
          (Vfold_left_rev (Vec2Union _ dot) (Vconst (mkStruct svalue) o)
                          (Apply_Family _ op_family x))
          ≡ family_out_index_set' _ op_family.
    Proof.
      unfold Apply_Family, Apply_Family'.


      rewrite family_in_index_set_eq in *.
      dependent induction n.
      -
        apply vector_val_index_set_Vconst_Empty.
      -
        rewrite Vbuild_cons.
        rewrite Vfold_left_rev_cons.
        simpl.
        rewrite Union_comm_eq.
        rewrite vector_val_index_set_Vec2Union.
        f_equiv.
        +
          specialize (IHn dot x
                          (shrink_op_family_up _ op_family)
                          (shrink_op_family_facts_up _ op_family op_family_facts)
                     ).
          rewrite <- IHn; clear IHn.
          *
            unfold shrink_op_family_up, get_family_op.
            simpl.
            reflexivity.
          *
            intros j jc H0.
            apply H; clear H.
            (* could be a sub-lemma *)
            apply family_in_set'_implies_members in H0.
            destruct H0 as [t [tc H0]].
            destruct t;
              simpl in *;
              apply Union_intror;
              unfold Ensembles.In;
              eapply family_in_set'_includes_members;
              eauto.
        +
          rewrite out_index_set_eq_vector_val_index_set with (x0:=x).
          *
            unfold get_family_op.
            repeat f_equiv.
            apply lt_unique.
          *
            apply op_family_facts.
          *
            intros j jc H0.
            apply H.
            apply family_in_set'_includes_members in H0.
            apply H0.
    Qed.

    Lemma IUnion_vector_val_index_set_step_disjoint
          (svalue : CarrierA)
          (i o n d : nat)

          (t:nat)
          (tc: t<d)
          (tc1: t<n+d)

          (dot : CarrierA → CarrierA → CarrierA)
          (op_family : @SHOperatorFamily Monoid_RthetaFlags i o (n+d) svalue)
          {op_family_facts : forall (j : nat) (jc : j < (n+d)), SHOperator_Facts Monoid_RthetaFlags
                                                                        (op_family (mkFinNat jc))}
          (compat: ∀ (m : nat) (mc : m < (n+d)) (n0 : nat) (nc : n0 < (n+d)),
              m ≢ n0
              →
              Disjoint (FinNat o)
                       (@out_index_set _ i o svalue
                                       (op_family (mkFinNat mc)))
                       (@out_index_set _ i o svalue
                                       (op_family (mkFinNat nc))))

          (x : vector (Rtheta' Monoid_RthetaFlags) i)
          (v : vector (svector Monoid_RthetaFlags o) n)

          (V : v ≡ Apply_Family _ (shrink_op_family_up_n _ d op_family) x)

          (f0 : @SHOperator Monoid_RthetaFlags i o svalue)
          (F0 : f0 ≡ op_family (@mkFinNat (n+d) t tc1))
          {H : ∀ (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaFlags op_family
                                                           (mkFinNat jc) → Is_Val (Vnth x jc)}
      :
        Disjoint (FinNat o)
                 (@vector_val_index_set _ o
                                        (@Vfold_left_rev
                                           (svector Monoid_RthetaFlags o)
                                           (svector Monoid_RthetaFlags o)
                                           (@Vec2Union Monoid_RthetaFlags o dot) n
                                           (Vconst
                                              (@mkStruct Monoid_RthetaFlags svalue) o)
                                           v))
                 (@out_index_set _ i o svalue f0).
    Proof.

      subst v.
      rewrite vector_val_index_set_Apply_Family.
      -
        subst f0.
        clear - tc compat.
        split.
        intros jf D.
        destruct D as [jf D0 D1].
        unfold Ensembles.In in *.
        destruct jf as [j jc].
        eapply family_out_set'_implies_members in D0.
        destruct D0 as [p [pc D0]].

        assert(pc1: p+d < n+d) by omega.
        specialize (compat t tc1 (p+d) pc1).
        destruct (eq_nat_dec t (p+d)) as [E | NE].
        +
          omega.
        +
          specialize (compat NE).
          destruct compat.
          specialize (H (mkFinNat jc)).
          contradict H.
          split; unfold Ensembles.In.
          *
            assumption.
          *
            unfold shrink_op_family_up_n in D0.
            simpl in D0.
            replace pc1 with (Plus.plus_lt_compat_r p n d pc) by
                apply le_unique.
            assumption.
      -
        apply (shrink_op_family_facts_up_n _ d op_family op_family_facts).
      -
        intros j jc H0.
        apply H; clear H.
        (* could be a sub-lemma *)
        unfold shrink_op_family_mem_up_n in H0.
        apply family_in_set_implies_members in H0.
        destruct H0 as [p [pc H0]].
        eapply family_in_set_includes_members.
        eapply H0.
    Qed.

    Lemma IUnion_vector_val_index_set_1_step_disjoint
          {svalue : CarrierA}
          {i o n : nat}
          {dot : CarrierA → CarrierA → CarrierA}
          {op_family : SHOperatorFamily Monoid_RthetaFlags (svalue:=svalue)}
          {op_family_facts : forall (j : nat) (jc : j < S n), SHOperator_Facts Monoid_RthetaFlags
                                                                        (op_family (mkFinNat jc))}
          (compat : forall (m : nat) (mc : m < S n) (n0 : nat) (nc : n0 < S n),
              m ≢ n0
              → Disjoint (FinNat o) (out_index_set Monoid_RthetaFlags (op_family (mkFinNat mc)))
                         (out_index_set Monoid_RthetaFlags (op_family (mkFinNat nc))))

          {x : vector (Rtheta' Monoid_RthetaFlags) i}
          {H : ∀ (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaFlags op_family
                                                           (mkFinNat jc) → Is_Val (Vnth x jc)}
          {v : vector (svector Monoid_RthetaFlags o) n}
          {V : v
                 ≡ Vbuild
                 (λ (i0 : nat) (ip : i0 < n), get_family_op Monoid_RthetaFlags op_family
                                                          (S i0) (lt_n_S ip) x)}
      :
        Disjoint (FinNat o)
                 (vector_val_index_set
                    (Vfold_left_rev (Vec2Union Monoid_RthetaFlags dot) (Vconst (mkStruct svalue) o)
                                    v))
                 (vector_val_index_set
                    (get_family_op Monoid_RthetaFlags op_family 0 (Nat.lt_0_succ n) x)).
    Proof.
      unfold get_family_op.
      unshelve rewrite <- out_index_set_eq_vector_val_index_set.
      2: apply op_family_facts.
      2:{
        intros j jc H0.
        apply H.
        eapply family_in_set_includes_members.
        eapply H0.
      }
      assert(E: S n ≡ n + 1) by lia.
      assert(zc: 0 < 1) by lia.
      assert(zc1: 0 < n + 1) by lia.

      remember (op_family (@mkFinNat (S n) 0 (Nat.lt_0_succ n))) as f0 eqn:F0.

      unshelve eapply IUnion_vector_val_index_set_step_disjoint with
          (dot:=dot)
          (d:=1)
          (t0:=0)
          (tc1:=zc1)
          (op_family := cast_op_family op_family E); eauto.
      -
        apply (cast_op_family_facts op_family_facts E).
      -
        intros m mc n0 nc H1.
        unfold cast_op_family.
        break_match; auto.
      -
        subst v.
        unfold Apply_Family, Apply_Family', cast_op_family, shrink_op_family_up_n.
        f_equiv.
        extensionality j.
        extensionality jc.
        apply cast_op_eq; simpl; lia.
      -
        subst f0.
        unfold cast_op_family.
        break_match; auto.
        f_equiv.
        f_equiv.
        apply lt_unique.
      -
        intros j jc H0.
        apply H.
        apply family_in_set_implies_members in H0.
        destruct H0 as [t [tc H0]].
        assert(tc1: t < S n) by omega.
        apply family_in_set_includes_members with (jc:=tc1).
        rewrite cast_in_index_set_eq with (E0:=E) (tn:=tc).
        apply H0.
        assumption.
    Qed.

    Global Instance IUnion_Mem
           {i o k: nat}
           `{svalue: MonUnit CarrierA}
           `{dot: SgOp CarrierA}
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot svalue}
           (op_family: @SHOperatorFamily Monoid_RthetaFlags i o k svalue)
           (op_family_facts: forall j (jc: j<k), SHOperator_Facts Monoid_RthetaFlags (op_family (mkFinNat jc)))
           (op_family_mem: forall j (jc:j<k), SHOperator_Mem (op_family (mkFinNat jc)))
           (compat: forall m (mc:m<k) n (nc:n<k), m ≢ n -> Disjoint _
                                                              (out_index_set _ (op_family (mkFinNat mc)))
                                                              (out_index_set _ (op_family (mkFinNat nc))))
           `{scompat: BFixpoint svalue dot}
           (facts: @SHOperator_Facts Monoid_RthetaFlags i o svalue
                                     (IUnion dot op_family (pdot:=pdot) ))
      :  SHOperator_Mem (IUnion dot op_family (pdot:=pdot))
                        (facts:=facts).
    Proof.
      unshelve esplit.
      -
        exact (IUnion_mem (get_family_mem_op op_family_mem)).
      -
        apply IUnion_mem_proper.
      -
        (* mem_out_some *)
        intros m H.
        unfold IUnion_mem, is_Some.
        simpl.
        repeat break_match; try tauto.
        +
          contradict Heqo0.
          rename Heqo1 into A.
          pose proof (Apply_mem_Family_eq_Some A) as F.
          pose proof (Apply_mem_Family_length A) as L.
          revert l A F L.
          induction k; intros.
          *
            simpl in *.
            dep_destruct l. 2: inversion L.
            simpl.
            some_none.
          *
            dep_destruct l. inversion L.
            simpl.
            break_match.
            --
              clear IHk.
              apply mem_merge_is_Some.
              apply Apply_mem_Family_cons in A.
              destruct A as [A0 A].
              simpl in *.
              inversion L; clear l L; rename H1 into L, x into l.
              eapply IUnion_mem_1_step_disjoint; eauto.
            --
              contradict Heqo0.
              specialize (IHk
                            (shrink_op_family_up _ op_family)
                            (shrink_op_family_facts_up _ _ op_family_facts)
                            (shrink_op_family_mem_up _ _ op_family_mem)
                         ).
              apply IHk; clear IHk.
              ++
                intros m1 mc n nc H0.
                apply compat.
                simpl.
                crush.
              ++
                apply IUnion_Facts; auto.
                apply shrink_op_family_facts_up; eauto.
                intros m2 mc n nc H1.
                unfold shrink_op_family_up.
                auto.
              ++
                intros j jc H0.
                simpl in H0.
                specialize (H j jc).
                Opaque family_in_index_set.
                simpl in H.
                rewrite family_in_index_set_eq in H.
                rewrite family_in_index_set_eq in H0.
                Transparent family_in_index_set.
                simpl in H.
                apply H.
                apply Union_intror.
                unfold Ensembles.In.
                apply H0.
              ++
                apply Apply_mem_Family_cons in A.
                apply A.
              ++
                intros j jc.
                specialize (F (S j) (lt_n_S jc)).
                crush.
              ++
                crush.
        +
          (* [Apply_mem_Family] could not be [None] *)
          clear Heqo0.
          rename Heqo1 into A.
          unfold Apply_mem_Family in A.
          induction k.
          *
            simpl in A.
            some_none.
          *
            simpl in A.
            repeat break_match_hyp; try some_none; clear A.
            --
              specialize (IHk
                            (shrink_op_family_up _ op_family)
                            (shrink_op_family_facts_up _ _ op_family_facts)
                            (shrink_op_family_mem_up _ _ op_family_mem)
                         ).

              assert (∀ (j : nat) (jc : j < i), in_index_set _
                                                           (IUnion dot
                                                                   (shrink_op_family_up _
                                                                                        op_family)) (mkFinNat jc) →
                                              mem_in j m) as P.
              {
                clear IHk Heqo1.
                intros j jc H0.
                simpl in H0.
                specialize (H j jc).
                Opaque family_in_index_set.
                simpl in H.
                rewrite family_in_index_set_eq in H.
                rewrite family_in_index_set_eq in H0.
                Transparent family_in_index_set.
                simpl in H.
                apply H.
                apply Union_intror.
                unfold Ensembles.In.
                apply H0.
              }
              assert(F: @SHOperator_Facts Monoid_RthetaFlags i o svalue
                                          (@IUnion svalue i o k dot pdot scompat (@shrink_op_family_up Monoid_RthetaFlags i o k svalue op_family))).
              {
                apply IUnion_Facts; auto.
                apply shrink_op_family_facts_up; eauto.
                intros m2 mc n nc H1.
                unfold shrink_op_family_up.
                auto.
              }
              assert(compat':
                       ∀ (m : nat) (mc : m < k) (n : nat) (nc : n < k), m ≢ n
                                                  → Disjoint
                                                      (FinNat o)
                                                      (out_index_set Monoid_RthetaFlags
                                                         (shrink_op_family_up
                                                          Monoid_RthetaFlags op_family
                                                          (mkFinNat mc)))
                                                      (out_index_set Monoid_RthetaFlags
                                                         (shrink_op_family_up
                                                          Monoid_RthetaFlags op_family
                                                          (mkFinNat nc)))).
              {
                intros m1 mc n nc H0.
                apply compat.
                auto.
              }
              specialize (IHk compat' F P). clear P compat'.
              contradict IHk.
              unfold get_family_mem_op in *.
              rewrite <- Heqo1.
              unfold shrink_op_family_up, shrink_op_family_facts_up, shrink_op_family_mem_up.
              f_equiv.
              extensionality j.
              extensionality jc.
              replace (@strictly_order_preserving _ _ _ _ _ _ _ _ j k jc)
                with (@lt_n_S j k jc) by apply lt_unique.
              reflexivity.
            --
              clear IHk.
              contradict Heqo0.
              apply is_Some_ne_None.
              apply op_family_mem.
              Opaque family_in_index_set.
              simpl in H.
              rewrite family_in_index_set_eq in H.
              Transparent family_in_index_set.
              simpl in H.
              intros j jc H0.
              specialize (H j jc).
              apply H. clear H.
              apply Union_introl.
              unfold Ensembles.In.
              replace (zero_lt_Sn k) with (Nat.lt_0_succ k) by apply lt_unique.
              apply H0.
      -
        (* out_mem_fill_pattern *)
        intros m0 m H j jc.
        unfold IUnion_mem in H.
        simpl in *.
        break_match_hyp ; try some_none.
        rename Heqo0 into A.
        split.
        +
          rewrite family_out_index_set_eq.
          dependent induction k; intros.
          *
            simpl in *.
            inversion H0.
          *
            assert(length l = S k) as L by apply (Apply_mem_Family_length A).
            destruct l as [| l0]; try inversion L.

            apply Apply_mem_Family_cons in A.
            destruct A as [A0 A].
            simpl in H.
            break_match_hyp; try some_none.

            apply (mem_merge_as_Union _ _ _ _ H).
            simpl in *.
            dependent destruction H0.
            --
              clear IHk A.
              right.
              unfold Ensembles.In in H0.
              eapply (out_mem_fill_pattern _ _ A0) with (jc:=jc).
              replace (Nat.lt_0_succ k) with (zero_lt_Sn k)
                by apply lt_unique.
              auto.
            --
              clear A0.
              left.

              specialize (IHk
                            _
                            dot
                            pdot
                            _
                            (shrink_op_family_up _ op_family)
                            (shrink_op_family_facts_up _ _ op_family_facts)
                            (shrink_op_family_mem_up _ _ op_family_mem)
                         ).
              eapply IHk;eauto.
              apply IUnion_Facts; auto.
              apply shrink_op_family_facts_up; eauto.
              intros m2 mc n nc H1.
              unfold shrink_op_family_up.
              auto.
        +
          assert(length l = k) as L by apply (Apply_mem_Family_length A).
          rewrite family_out_index_set_eq.
          dependent induction k; intros.
          *
            simpl in *.
            dep_destruct l; try inversion L.
            simpl in H.
            some_inv.
            subst m.
            unfold mem_in, mem_empty in H0.
            apply NP.F.empty_in_iff in H0.
            tauto.
          *
            destruct l as [| l0]; try inversion L.
            apply Apply_mem_Family_cons in A.
            destruct A as [A0 A].
            simpl in H.
            break_match_hyp; try some_none.
            simpl in *.
            apply (mem_merge_as_Union _ _ _ _ H) in H0.
            dependent destruction H0.
            --
              clear A0.
              right.

              specialize (IHk
                            _
                            dot
                            pdot
                            _
                            (shrink_op_family_up _ op_family)
                            (shrink_op_family_facts_up _ _ op_family_facts)
                            (shrink_op_family_mem_up _ _ op_family_mem)
                         ).
              eapply IHk;eauto.
              apply IUnion_Facts; auto.
              apply shrink_op_family_facts_up; eauto.
              intros m2 mc n nc H1.
              unfold shrink_op_family_up.
              auto.
            --
              clear IHk A.
              left.
              unfold Ensembles.In.
              unfold get_family_mem_op in A0.
              eapply out_mem_fill_pattern with (jc0:=jc) in A0.
              replace (Nat.lt_0_succ k) with (zero_lt_Sn k) in A0
                by apply lt_unique.
              apply A0.
              auto.
      -
        (* out_mem_oob *)
        intros m0 m H j jc.
        unfold IUnion_mem in H.
        simpl in *.
        break_match_hyp ; try some_none.
        rename Heqo0 into A.
        dependent induction k.
        +
          unfold Apply_mem_Family in A.
          simpl in A.
          some_inv.
          subst l.
          simpl in *.
          some_inv.
          unfold mem_in,  mem_empty.
          intros C.
          apply NP.F.empty_in_iff in C.
          tauto.
        +
          assert(length l = S k) as L by apply (Apply_mem_Family_length A).
          destruct l as [| l0]; try inversion L.
          simpl.
          apply Apply_mem_Family_cons in A.
          destruct A as [A0 A].
          intros C.
          simpl in *.
          break_match_hyp ; try some_none.
          apply (mem_merge_as_Union _ _ _ _ H) in C.
          destruct C.
          --
            clear A0.
            specialize (IHk
                          _
                          dot
                          pdot
                          _
                          (shrink_op_family_up _ op_family)
                          (shrink_op_family_facts_up _ _ op_family_facts)
                          (shrink_op_family_mem_up _ _ op_family_mem)
                       ).
            eapply IHk;eauto.
            apply IUnion_Facts; auto.
            apply shrink_op_family_facts_up; eauto.
            intros m2 mc n nc H2.
            unfold shrink_op_family_up.
            auto.
          --
            apply out_mem_oob with (j0:=j) in A0; auto.
      -
        (* mem_vec_preservation *)
        intros x H.
        rename k into n.
        unfold IUnion, IUnion_mem, Diamond.
        simpl in *.
        break_match; rename Heqo0 into A.
        +
          f_equiv.
          remember (Apply_Family' (get_family_op Monoid_RthetaFlags op_family) x)
            as v eqn:A1.

          revert l A A1.
          induction n; intros.
          *
            subst v.
            simpl.
            f_equiv.
            unfold Diamond, MUnion.
            assert(length l = 0) as L by apply (Apply_mem_Family_length A).
            destruct l; try inversion L.
            simpl.
            f_equiv.
            apply svector_to_mem_block_Vconst_mkStruct.
          *
            assert(length l = S n) as L by apply (Apply_mem_Family_length A).
            destruct l; try inversion L.
            rename m into l0.
            apply Apply_mem_Family_cons in A.
            destruct A as [A0 A].
            assert(forall (j : nat) (jc : j < i), family_in_index_set Monoid_RthetaFlags
                                     (shrink_op_family_up Monoid_RthetaFlags
                                        op_family) (mkFinNat jc) →
                                           Is_Val (Vnth x jc)) as P.
            {
              intros j jc H0.
              apply H.
              apply family_in_set_implies_members in H0.
              destruct H0 as [t [tc H0]].
              unfold shrink_op_family_up in H0.
              eapply family_in_set_includes_members.
              unfold Ensembles.In.
              eapply H0.
            }
            unfold Apply_Family' in A1.
            rewrite Vbuild_cons in A1.
            dep_destruct v.
            clear v. rename h into v0, x0 into v.
            inversion A1 as [[V0 V]]. clear A1.
            apply inj_pair2 in V.

            (* shrink compat *)
            assert(compat': ∀ (m : nat) (mc : m < n) (n0 : nat) (nc : n0 < n),
                      m ≢ n0
                      → Disjoint (FinNat o)
                                 (out_index_set _
                                                (shrink_op_family_up _ op_family (mkFinNat mc)))
                                 (out_index_set _
                                                (shrink_op_family_up _ op_family (mkFinNat nc)))
                  ).
            {
              intros m mc n0 nc H0.
              apply compat.
              auto.
            }

            assert(facts': SHOperator_Facts Monoid_RthetaFlags (IUnion dot (shrink_op_family_up Monoid_RthetaFlags op_family))).
            {
              apply IUnion_Facts; auto.
              intros j jc.
              apply shrink_op_family_facts_up; auto.
            }
            specialize (IHn
                          (shrink_op_family_up _ op_family)
                          (shrink_op_family_facts_up _ _ op_family_facts)
                          (shrink_op_family_mem_up _ _ op_family_mem)
                          compat'
                          facts'
                          P
                          v l
                          A V
                       ).

            unfold MUnion in *.
            simpl.

            break_match; try some_none.
            rewrite svector_to_mem_block_Vec2Union_mem_merge
              with (a_zero:=svalue).
            --
              some_inv.
              rewrite IHn; clear IHn.
              apply mem_merge_proper; auto.
              apply Some_inj_equiv.
              rewrite <- A0. clear A0.
              unfold get_family_op, get_family_mem_op.
              eapply mem_vec_preservation.
              intros j jc H0.
              apply H.
              eapply family_in_set_includes_members.
              apply H0.
            --
              apply pdot.
            --
              eapply IUnion_vector_val_index_set_1_step_disjoint; eauto.
            --
              typeclasses eauto.
            --
              apply Vec2Union_fold_zeros with
                  (op_family0:=shrink_op_family_up _ op_family)
                  (x0:=x); auto.
              apply (shrink_op_family_facts_up _ _ op_family_facts).
            --
              apply Vforall_nth_intro.
              clear P.
              intros t tc P.
              eapply svalue_at_sparse.
              eapply sparse_outputs_not_in_out_set; eauto.
              intros j jc H0.
              specialize (H j jc).
              apply H.
              apply family_in_set_includes_members in H0.
              apply H0.
        +
          (* [A] could not happen *)
          exfalso.
          unfold Apply_mem_Family in A.
          apply monadic_Lbuild_op_eq_None in A.
          destruct A as [t [tc A]].
          contradict A.
          apply is_Some_ne_None.
          apply mem_out_some.
          intros j jc H0.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply H.
          eapply family_in_set_includes_members.
          apply H0.
    Defined.

  End MonoidSpecific.

End MemVecEq.
