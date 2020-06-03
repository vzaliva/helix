Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.

Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.MemoryOfCarrierA.

Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.
Require Import Helix.Util.MonoidalRestriction.

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

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Require Import Coq.Lists.SetoidList.
Require Import CoLoR.Util.List.ListUtil.
Require Import CoLoR.Util.Nat.NatUtil.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.theory.setoids.

Import Monoid.

Import VectorNotations.
Open Scope vector_scope.

Import MonadNotation.
Open Scope monad_scope.

Open Scope nat_scope.

Import MMemoryOfCarrierA.

Section SVector.

  Variable fm:Monoid RthetaFlags.

  Program Definition svector_to_mem_block_spec
          {n : nat}
          (v : svector fm n):
    { m : mem_block |
      (
        (forall i (ip : i < n), Is_Val (Vnth v ip) <-> NM.MapsTo i (evalWriter (Vnth v ip)) m)
        /\
        (forall i (ip : i < n), NM.In i m <-> Is_Val (Vnth v ip))
      )
    }
    := Vfold_right_indexed' 0
                            (fun k r m =>
                               if Is_Val_dec r then mem_add k (evalWriter r) m
                               else m
                            )
                            v mem_empty.
  Next Obligation.
    unfold mem_lookup, mem_add, mem_empty.
    split.
    -
      (* Is_Val <-> MapsTo *)
      split.
      +
        (* Is_Val -> MapsTo *)
        revert ip. revert i.
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v;clear v.
          simpl.
          destruct i.
          --
            destruct (Is_Val_dec h).
            ++
              apply NM.add_1.
              reflexivity.
            ++
              simpl in H.
              crush.
          --
            destruct (Is_Val_dec h).
            ++
              apply NM.add_2; auto.
              assert (N: i<n) by apply Lt.lt_S_n, ip.
              simpl in H.
              replace (Lt.lt_S_n ip) with N by apply le_unique.
              assert(V: Is_Val (Vnth x N)).
              {
                replace N with (lt_S_n ip) by apply le_unique.
                apply H.
              }
              specialize (IHn x i N V).
              apply NM.find_1 in IHn.
              apply NM.find_2.
              rewrite <- IHn; clear IHn.
              rewrite find_fold_right_indexed'_S_P.
              reflexivity.
            ++
              simpl in H.
              assert (N: i<n) by apply Lt.lt_S_n, ip.
              replace (Lt.lt_S_n ip) with N by apply le_unique.
              assert(V: Is_Val (Vnth x N)).
              {
                replace N with (lt_S_n ip) by apply le_unique.
                apply H.
              }
              specialize (IHn x i N V).
              apply NM.find_1 in IHn.
              apply NM.find_2.
              rewrite find_fold_right_indexed'_S_P.
              apply IHn.
      +
        (* MapsTo -> Is_Val *)
        revert i ip.
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v; clear v.
          simpl.
          destruct i.
          --
            clear IHn.
            apply NM.find_1 in H.
            simpl in H.
            destruct (Is_Val_dec h); auto.
            rewrite find_fold_right_indexed_oob in H.
            some_none.
            auto.
          --
            apply IHn; clear IHn.
            apply NM.find_1 in H.
            apply NM.find_2.
            simpl (Some _) in H.
            assert (N: i<n) by apply Lt.lt_S_n, ip.
            replace (Lt.lt_S_n ip) with N in * by apply le_unique.
            rewrite <- H; clear H ip.
            rewrite <- find_fold_right_indexed'_S_P.
            symmetry.
            apply find_fold_right_indexed'_cons_P.
    -
      split.
      +
        revert i ip.
        (* In -> Is_Val *)
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v; clear v.
          simpl.
          destruct i.
          --
            clear IHn.
            simpl in H.
            destruct (Is_Val_dec h); auto.
            apply In_MapsTo in H.
            destruct H as [e H].
            apply NP.F.find_mapsto_iff in H.
            rewrite find_fold_right_indexed_oob in H.
            some_none.
            auto.
          --
            apply IHn; clear IHn.
            apply In_MapsTo in H.
            destruct H as [e H].
            apply NP.F.find_mapsto_iff in H.
            apply MapsTo_In with (e:=e).
            apply NP.F.find_mapsto_iff.
            rewrite <- H. clear H ip.
            rewrite <- find_fold_right_indexed'_S_P.
            symmetry.
            apply find_fold_right_indexed'_cons_P.
      +
        (* Is_Val -> NM.In *)
        revert i ip.
        (* In -> Is_Val *)
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v; clear v.
          simpl.
          destruct i.
          --
            clear IHn.
            simpl.
            break_if.
            ++
              apply NP.F.add_in_iff.
              auto.
            ++
              exfalso.
              contradict H.
              simpl.
              auto.
          --
            break_if.
            ++
              apply NP.F.add_neq_in_iff; auto.
              simpl in *.
              apply IHn in H. clear IHn.
              apply In_MapsTo in H.
              destruct H as [e H].
              apply NP.F.find_mapsto_iff in H.
              apply MapsTo_In with (e:=e).
              apply NP.F.find_mapsto_iff.
              rewrite <- H. clear H ip.
              rewrite <- find_fold_right_indexed'_S_P.
              reflexivity.
            ++
              simpl in H.
              apply IHn in H. clear IHn.
              apply In_MapsTo in H.
              destruct H as [e H].
              apply NP.F.find_mapsto_iff in H.
              apply MapsTo_In with (e:=e).
              apply NP.F.find_mapsto_iff.
              rewrite <- H. clear H ip.
              rewrite <- find_fold_right_indexed'_S_P.
              reflexivity.
  Qed.

  Definition svector_to_mem_block {n} (v: svector fm n) := proj1_sig (svector_to_mem_block_spec v).

  (* This could be only proven for [eq] in for svectors, as their
     structural properites are affecting the result. *)
  Global Instance svector_to_mem_block_proper
         {n: nat}:
    Proper ((eq) ==> (equiv)) (@svector_to_mem_block n).
  Proof.
    solve_proper.
  Qed.

  Lemma svector_to_mem_block_key_oob {n:nat} {v: svector fm n}:
    forall (k:nat) (kc:ge k n), mem_lookup k (svector_to_mem_block v) ≡ None.
  Proof.
    intros k kc.
    unfold svector_to_mem_block.
    simpl.
    revert k kc; induction v; intros.
    -
      reflexivity.
    -
      unfold mem_lookup.
      simpl.
      destruct k.
      +
        omega.
      +
        break_if.
        *
          rewrite NP.F.add_neq_o by omega.
          rewrite find_fold_right_indexed'_S_P.
          rewrite IHv.
          reflexivity.
          omega.
        *
          rewrite find_fold_right_indexed'_S_P.
          rewrite IHv.
          reflexivity.
          omega.
  Qed.

  Definition mem_block_to_svector {n} (m: mem_block): svector fm n
    := Vbuild (fun i (ic:i<n) =>
                 match mem_lookup i m with
                 | None => mkSZero (* maybe other structural value? *)
                 | Some x => mkValue x
                 end
              ).

  Global Instance mem_block_to_svector_proper
         {n: nat}:
    Proper ((=) ==> (=)) (@mem_block_to_svector n).
  Proof.
    intros a b H.
    unfold equiv, mem_block_Equiv in H.
    unfold mem_block_to_svector.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    specialize (H j).
    unfold mem_lookup.
    break_match; break_match; try some_none; try reflexivity.
    some_inv.
    f_equiv.
    apply H.
  Qed.

End SVector.

Ltac svector_to_mem_block_to_spec m H0 H1 H2 :=
  match goal with
  | [ |- context[svector_to_mem_block_spec ?fm ?v]] =>
    pose proof (svector_to_mem_block_key_oob fm (v:=v)) as H2;
    unfold svector_to_mem_block in H2 ;
    destruct (svector_to_mem_block_spec fm v) as [m [H0 H1]]

  | [ H: context[svector_to_mem_block_spec ?fm ?v] |- _ ] =>
    pose proof (svector_to_mem_block_key_oob fm (v:=v)) as H2;
    unfold svector_to_mem_block in H2 ;
    destruct (svector_to_mem_block_spec fm v) as [m [H0 H1]]
  end.

Lemma find_svector_to_mem_block_some (n k:nat) (kc:k<n) {fm} (x:svector fm n)
  :
    NM.In (elt:=CarrierA) k (svector_to_mem_block fm x) ->
    NM.find (elt:=CarrierA) k (svector_to_mem_block fm x)
            ≡ Some (evalWriter (Vnth x kc)).
Proof.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m' H0 H1 I2.
  intros H.
  simpl in *.
  unfold mem_lookup in *.
  apply NM.find_1.
  apply H0, H1, H.
Qed.

Lemma svector_to_mem_block_In
      {n:nat}
      {fm}
      (x: svector fm n)
      (j:nat)
      (jc:j<n):
  Is_Val (Vnth x jc) -> mem_in j (svector_to_mem_block fm x).
Proof.
  intros H.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m0 I0 H1 O0.
  simpl in *.
  specialize (H1 j jc).
  apply H1, H.
Qed.

Lemma svector_to_mem_block_Vconst_mkStruct
      {fm}
      {fml : MonoidLaws fm}
      (n : nat)
      (v : CarrierA):
  svector_to_mem_block fm (Vconst (mkStruct (fm:=fm) v) n) = mem_empty.
Proof.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  simpl in *.
  mem_index_equiv k.
  rewrite NP.F.empty_o.
  destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
  -
    apply None_equiv_eq.
    apply NP.F.not_find_in_iff.

    specialize (I0 k kc).
    apply not_iff_compat in I0.
    apply I0.
    rewrite Vnth_const.
    apply Is_Val_mkStruct.
  -
    apply None_equiv_eq.
    apply O0, kc.
Qed.

Lemma svector_to_mem_block_rvector2rsvector
      {n x}:
  svector_to_mem_block _ (rvector2rsvector n x) = svector_to_mem_block _ x.
Proof.
  unfold svector_to_mem_block, rvector2rsvector, Rtheta2RStheta.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  svector_to_mem_block_to_spec m1 H1 I1 O1.
  simpl in *.
  mem_index_equiv k.
  destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
  -
    clear O0 O1.
    specialize (H0 k kc).
    specialize (H1 k kc).
    unfold equiv, option_Equiv.
    rewrite Vnth_map in H0.
    unfold Is_Val,compose in H0.
    rewrite execWriter_castWriter in H0.
    unfold Is_Val, compose in H1.
    rewrite evalWriter_castWriter in H0.

    specialize (I0 k kc).
    specialize (I1 k kc).
    rewrite Vnth_map in I0.
    unfold Is_Val,compose in I0.
    rewrite execWriter_castWriter in I0.
    unfold Is_Val, compose in I1.

    destruct (IsVal_dec (execWriter (Vnth x kc))) as [V|NV].
    +
      destruct H0 as [H0 _].
      destruct H1 as [H1 _].
      apply NM.find_1 in H0; auto.
      apply NM.find_1 in H1; auto.
      rewrite H0, H1.
      reflexivity.
    +
      unfold Rtheta in *.
      generalize dependent (Vnth x kc).
      intros r H0 I0 H1 I1 NV.
      apply not_iff_compat in I0.
      apply not_iff_compat in I1.
      destruct I0 as [_ I0].
      destruct I1 as [_ I1].
      specialize (I0 NV).
      specialize (I1 NV).
      clear NV.
      apply NP.F.not_find_in_iff in I0.
      apply NP.F.not_find_in_iff in I1.
      rewrite I0, I1.
      reflexivity.
  -
    rewrite O0 by assumption.
    rewrite O1 by assumption.
    reflexivity.
Qed.


Lemma svector_to_mem_block_rsvector2rvector
      {n x}:
  svector_to_mem_block _ (rsvector2rvector n x) = svector_to_mem_block _ x.
Proof.
  unfold svector_to_mem_block, rsvector2rvector, RStheta2Rtheta.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  svector_to_mem_block_to_spec m1 H1 I1 O1.
  simpl in *.
  mem_index_equiv k.
  destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
  -
    clear O0 O1.
    specialize (H0 k kc).
    specialize (H1 k kc).
    unfold equiv, option_Equiv.
    rewrite Vnth_map in H0.
    unfold Is_Val,compose in H0.
    rewrite execWriter_castWriter in H0.
    unfold Is_Val, compose in H1.
    rewrite evalWriter_castWriter in H0.

    specialize (I0 k kc).
    specialize (I1 k kc).
    rewrite Vnth_map in I0.
    unfold Is_Val,compose in I0.
    rewrite execWriter_castWriter in I0.
    unfold Is_Val, compose in I1.

    destruct (IsVal_dec (execWriter (Vnth x kc))) as [V|NV].
    +
      destruct H0 as [H0 _].
      destruct H1 as [H1 _].
      apply NM.find_1 in H0; auto.
      apply NM.find_1 in H1; auto.
      rewrite H0, H1.
      reflexivity.
    +
      unfold RStheta in *.
      generalize dependent (Vnth x kc).
      intros r H0 I0 H1 I1 NV.
      apply not_iff_compat in I0.
      apply not_iff_compat in I1.
      destruct I0 as [_ I0].
      destruct I1 as [_ I1].
      specialize (I0 NV).
      specialize (I1 NV).
      clear NV.
      apply NP.F.not_find_in_iff in I0.
      apply NP.F.not_find_in_iff in I1.
      rewrite I0, I1.
      reflexivity.
  -
    rewrite O0 by assumption.
    rewrite O1 by assumption.
    reflexivity.
Qed.


Class SH_MSH_Operator_compat
      {i o: nat}
      {fm: Monoid RthetaFlags}
      {svalue: CarrierA}
      (sop: @SHOperator fm i o svalue)
      (mop: @MSHOperator i o)
  :=
    {
      sfacts:
        SHOperator_Facts fm sop;

      mfacts:
        MSHOperator_Facts mop;

      (* input sparsity contracts must match *)
      in_pattern_compat:
        Same_set _ (in_index_set fm sop) (m_in_index_set mop);

      (* output sparsity contracts must match *)
      out_pattern_compat:
        Same_set _ (out_index_set fm sop) (m_out_index_set mop);

      (* -- Semantics eqivalence -- *)
      mem_vec_preservation:
        forall x,

          (* Only for inputs which comply to sparsity contract *)
          (∀ (j : nat) (jc : (j < i)%nat),
              in_index_set fm sop (mkFinNat jc) → Is_Val (Vnth x jc))
          ->
          Some (svector_to_mem_block _ (op fm sop x)) =
          mem_op mop (svector_to_mem_block _ x)
    }.

Section OperatorPairwiseProofs.

  Section WithMonoid.

    Variable fm: Monoid RthetaFlags.
    Variable fml: @MonoidLaws RthetaFlags fm.

    Global Instance SHCompose_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {i1 o2 o3: nat}
           (op1: @SHOperator fm o2 o3 svalue)
           (op2: @SHOperator fm i1 o2 svalue)
           (compat: Included _ (in_index_set fm op1) (out_index_set fm op2))
           (mop1: @MSHOperator o2 o3)
           (mop2: @MSHOperator i1 o2)
           `{Meq1: SH_MSH_Operator_compat _ _ _ _ op1 mop1}
           `{Meq2: SH_MSH_Operator_compat _ _ _ _ op2 mop2}
           `{facts1: SHOperator_Facts fm _ _ _ op1}
           `{facts2: SHOperator_Facts fm _ _ _ op2}
           `{mfacts1: MSHOperator_Facts _ _ mop1}
           `{mfacts2: MSHOperator_Facts _ _ mop2}
      : SH_MSH_Operator_compat
          (SHCompose fm op1 op2) (MSHCompose mop1 mop2).
    Proof.
      split.
      -
        apply SHCompose_Facts; auto.
      -
        apply SHCompose_MFacts; auto.
        revert compat.
        eapply Included_mor; [apply Meq1 | apply Meq2].
      -
        (* in_pattern_compat *)
        apply Meq2.
      -
        (* out_pattern_compat *)
        apply Meq1.
      -
        (* mem_vec_preservation *)
        intros x G.
        unfold SHCompose, MSHCompose.
        unfold option_compose, compose.
        simpl in G.

        pose proof (@mem_out_some _ _ mop2 mfacts2 (svector_to_mem_block _ x)) as Rm.
        assert(G0: (∀ (j : nat) (jc : (j < i1)%nat), m_in_index_set mop2 (mkFinNat jc)
                                                 → mem_in j (svector_to_mem_block _ x))).
        {
          intros j jc H.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply G.
          apply in_pattern_compat.
          apply H.
        }
        specialize (Rm G0).
        apply is_Some_equiv_def in Rm.
        destruct Rm as [m2 Rm].
        simpl.
        break_match; try some_none.
        clear Rm m2.
        pose proof (mem_op_proper mop1) as P.
        setoid_replace m with (svector_to_mem_block _ (op fm op2 x)).
        apply Meq1.
        {
          intros j jc H.
          apply facts2.
          apply G.
          apply compat, H.
        }

        apply Some_inj_equiv.
        rewrite <- Heqo.
        symmetry.
        apply Meq2, G.
    Qed.

    Global Instance Embed_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {o b: nat}
           (bc: b < o)
      : SH_MSH_Operator_compat (Embed (svalue:=svalue) fm bc) (MSHEmbed bc).
    Proof.
      split.
      -
        typeclasses eauto.
      -
        typeclasses eauto.
      -
        reflexivity.
      -
        reflexivity.
      -
        assert (facts: SHOperator_Facts fm (svalue:=svalue) (Embed fm bc)) by
            typeclasses eauto.
        intros x G.
        simpl.
        unfold Embed_mem, map_mem_block_elt.

        unfold svector_to_mem_block.
        svector_to_mem_block_to_spec m0 H0 I0 O0.
        svector_to_mem_block_to_spec m1 H1 I1 O1.

        break_match; unfold mem_lookup in *; simpl in *.
        +
          f_equiv.
          unfold mem_add, mem_empty.
          assert(Vb: Is_Val (Vnth (Embed_impl bc svalue x) bc)).
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
              unfold Embed_impl.
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

              assert(Vk: Is_Struct (Vnth (Embed_impl bc svalue x) kc)).
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
    Qed.

    Global Instance Pick_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {o b:nat}
           (bc: b < o)
      : SH_MSH_Operator_compat (Pick (svalue:=svalue) fm bc) (MSHPick bc).
    Proof.
      split.
      -
        typeclasses eauto.
      -
        typeclasses eauto.
      -
        reflexivity.
      -
        reflexivity.
      -
        assert (facts: SHOperator_Facts fm (svalue:=svalue) (Pick fm bc)) by
            typeclasses eauto.
        intros x G.
        simpl.

        unfold Pick_mem , map_mem_block_elt.
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

            assert(Is_Val (Vnth (Pick_impl bc x) (lt_0_Sn O))) as V0.
            {
              unfold Pick_impl.
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

    Global Instance SHPointwise_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {n: nat}
           (f: FinNat n -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      : SH_MSH_Operator_compat
          (SHPointwise (svalue:=svalue) fm f)
          (MSHPointwise f).
    Proof.
      split.
      -
        typeclasses eauto.
      -
        typeclasses eauto.
      -
        reflexivity.
      -
        reflexivity.
      -
        assert (facts: SHOperator_Facts fm (svalue:=svalue) (SHPointwise fm f)) by
            typeclasses eauto.

        intros x G.
        simpl.

        assert((∀ (j : nat) (jc : j < n), in_index_set fm (svalue:=svalue)
                                                       (SHPointwise fm f)
                                                       (mkFinNat jc) →
                                        mem_in j (svector_to_mem_block _ x))
               → is_Some (mem_op_of_hop (HPointwise f) (svector_to_mem_block _ x))) as M by apply mem_out_some_mem_op_of_hop.
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

          assert(V: Is_Val (Vnth (SHPointwise_impl f x) kc)).
          {
            unfold SHPointwise_impl.
            rewrite Vbuild_nth.
            apply Is_Val_liftM.
            apply V0.
          }

          rewrite H0 in V.
          apply NM.find_1 in V.
          rewrite V.

          unfold SHPointwise_impl.
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

    Global Instance SHInductor_SH_MSH_Operator_compat
           {svalue: CarrierA}
           (n:nat)
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial: CarrierA):
      SH_MSH_Operator_compat
        (SHInductor (svalue:=svalue) fm n f initial)
        (MSHInductor n f initial).
    Proof.
      destruct n.
      -
        split.
        +
          typeclasses eauto.
        +
          typeclasses eauto.
        +
          reflexivity.
        +
          reflexivity.
        +
          intros x H.

          cbn in H.
          assert(0<1) as jc by lia.
          assert(Full_set (FinNat 1) (mkFinNat jc)) as F by constructor.
          specialize (H 0 jc F). clear F.
          simpl.
          unfold SHInductor_impl, HInductor, compose, mem_op_of_hop, HCOLImpl.Scalarize, Lst.
          f_equiv.
          Opaque liftM.
          cbn.
          break_if.
          *
            reflexivity.
          *
            clear Heqd H.
            contradict n.
            apply Is_Val_mkValue.
      -
        split.
        +
          typeclasses eauto.
        +
          typeclasses eauto.
        +
          reflexivity.
        +
          reflexivity.
        +
          intros x H.
          simpl.
          unfold SHInductor_impl, HInductor, compose, mem_op_of_hop, HCOLImpl.Scalarize, Lst.
          Opaque liftM.
          simpl.
          break_match.
          *
            f_equiv.
            dep_destruct t.
            dep_destruct x0. clear x0 t.
            unfold svector_to_mem_block, avector_to_mem_block.
            svector_to_mem_block_to_spec m0 H0 I0 O0.
            avector_to_mem_block_to_spec m2 H2 O2.
            simpl in *.
            mem_index_equiv k.
            destruct (lt_ge_dec k 1) as [kc | nkc].
            --
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
              ++
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
                rewrite Vbuild_Sn in C; cbn in C.
                break_match_hyp; try some_none.
                unfold mem_lookup, mem_add, mem_empty in *.
                break_if.
                **
                  erewrite NP.F.add_eq_o in Heqo by reflexivity.
                  repeat some_inv.
                  subst.
                  reflexivity.
                **
                  contradict Heqo.
                  apply None_ne_Some.
                  apply NP.F.empty_o.
              ++
                contradict NV.
                specialize (H 0 kc).
                apply H.
                apply Full_intro.
            --
              rewrite O0, O2; auto.
          *
            exfalso.
            rename Heqo into C.
            dep_destruct x.
            dep_destruct x0.
            unfold svector_to_mem_block, mem_block_to_avector in C.
            rewrite Vbuild_Sn in C; cbn in C.
            break_match_hyp; try some_none.
            clear C; rename Heqo into C.
            unfold mem_lookup, mem_add, mem_empty in *.
            break_if.
            --
              erewrite NP.F.add_eq_o in C by reflexivity.
              some_none.
            --
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

  Section MonoidSpecific.

    Global Instance SafeCast_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {i o: nat}
           (f: @SHOperator Monoid_RthetaSafeFlags i o svalue)
           (mf: @MSHOperator i o)
           `{f_mem: SH_MSH_Operator_compat _ _ _ _ f mf}
      :
        SH_MSH_Operator_compat (SafeCast f) mf.
    Proof.
      split.
      -
        apply SafeCast_Facts.
        apply f_mem.
      -
        apply f_mem.
      -
        apply f_mem.
      -
        apply f_mem.
      -
        destruct f_mem.
        intros x H.
        unfold SafeCast, SafeCast'.
        simpl in *.
        specialize (mem_vec_preservation0 (rvector2rsvector _ x)).
        unfold compose.
        rewrite svector_to_mem_block_rsvector2rvector.
        destruct mf.
        rewrite svector_to_mem_block_rvector2rsvector in mem_vec_preservation0.
        rewrite <- mem_vec_preservation0.
        reflexivity.
        intros j jc H0.
        specialize (H j jc H0).
        unfold rvector2rsvector.
        rewrite Vnth_map.
        apply Is_Val_Rtheta2RStheta.
        assumption.
    Qed.

    Global Instance UnSafeCast_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {i o}
           (f: @SHOperator Monoid_RthetaFlags i o svalue)
           (mf: @MSHOperator i o)
           `{f_mem: SH_MSH_Operator_compat _ _ _ _ f mf}
      :
        SH_MSH_Operator_compat (UnSafeCast f) mf.
    Proof.
      split.
      -
        apply UnSafeCast_Facts.
        apply f_mem.
      -
        apply f_mem.
      -
        apply f_mem.
      -
        apply f_mem.
      -
        destruct f_mem.
        intros x H.
        unfold UnSafeCast, UnSafeCast'.
        simpl in *.
        specialize (mem_vec_preservation0 (rsvector2rvector _ x)).
        unfold compose.
        rewrite svector_to_mem_block_rvector2rsvector.
        destruct mf.
        rewrite svector_to_mem_block_rsvector2rvector in mem_vec_preservation0.
        rewrite <- mem_vec_preservation0.
        reflexivity.
        intros j jc H0.
        specialize (H j jc H0).
        unfold rsvector2rvector.
        rewrite Vnth_map.
        apply Is_Val_Rtheta2RStheta.
        assumption.
    Qed.

    Global Instance SHBinOp_RthetaSafe_SH_MSH_Operator_compat
           {svalue: CarrierA}
           {o: nat}
           (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      : SH_MSH_Operator_compat
          (@SHBinOp Monoid_RthetaSafeFlags svalue o f pF)
          (MSHBinOp f).
    Proof.
      split.
      -
        typeclasses eauto.
      -
        typeclasses eauto.
      -
        reflexivity.
      -
        reflexivity.
      -
        intros x G.
        simpl.

        assert((∀ (j : nat) (jc : j < o+o), in_index_set Monoid_RthetaSafeFlags (svalue:=svalue)
                                                         (SHBinOp Monoid_RthetaSafeFlags f)
                                                         (mkFinNat jc) →
                                            mem_in j (svector_to_mem_block _ x))
               → is_Some (mem_op_of_hop (HBinOp f) (svector_to_mem_block _ x))) as M by apply mem_out_some_mem_op_of_hop.
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

          assert(V: Is_Val (Vnth (SHBinOp_impl f x) kc)).
          {
            erewrite SHBinOp_impl_nth with (jc:=kc).
            apply Is_Val_Safe_liftM2.
            apply V1.
            apply V2.
          }

          rewrite H0 in V.
          apply NM.find_1 in V.
          rewrite V.

          rewrite H2 with (ip:=kc).
          f_equiv.
          rewrite SHBinOp_impl_nth with (jc:=kc) (jc1:=kc1) (jc2:=kc2).
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

    Global Instance HTSUMUnion_SH_MSH_Operator_compat
           {a_zero: MonUnit CarrierA}
           {i o: nat}
           `{dot: SgOp CarrierA}
           `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
           (op1 op2: @SHOperator Monoid_RthetaFlags i o a_zero)
           (mop1 mop2: @MSHOperator i o)
           `{scompat: BFixpoint a_zero dot}
           {compat: Disjoint _
                             (out_index_set _ op1)
                             (out_index_set _ op2)}
           `{Meq1: SH_MSH_Operator_compat _ _ _ _ op1 mop1}
           `{Meq2: SH_MSH_Operator_compat _ _ _ _ op2 mop2}

           (* `a_zero` together with `dot` form a monoid.  *)
           `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot a_zero}

      : SH_MSH_Operator_compat
          (HTSUMUnion Monoid_RthetaFlags dot op1 op2
                      (scompat:=scompat)
          )
          (MHTSUMUnion dot mop1 mop2).
    Proof.
      split.
      -
        apply HTSUMUnion_Facts.
        apply Meq1.
        apply Meq2.
        apply compat.
      -
        apply HTSUMUnion_MFacts.
        eapply Disjoint_mor; eauto.
        apply Meq1.
        apply Meq2.
        apply Meq1.
        apply Meq2.
      -
        simpl.
        destruct Meq1.
        apply Extensionality_Ensembles in in_pattern_compat0.
        rewrite in_pattern_compat0.
        destruct Meq2.
        apply Extensionality_Ensembles in in_pattern_compat1.
        rewrite in_pattern_compat1.
        reflexivity.
      -
        simpl.
        destruct Meq1.
        apply Extensionality_Ensembles in out_pattern_compat0.
        rewrite out_pattern_compat0.
        destruct Meq2.
        apply Extensionality_Ensembles in out_pattern_compat1.
        rewrite out_pattern_compat1.
        reflexivity.
      -
        (* mem_vec_preservation *)
        intros x G.
        simpl.
        unfold HTSUMUnion, Vec2Union, HTSUMUnion_mem.

        pose proof (@out_pattern_compat _ _ _ _ op1 mop1 Meq1) as O1.
        pose proof (@out_pattern_compat _ _ _ _ op2 mop2 Meq2) as O2.
        apply Extensionality_Ensembles in O1.
        apply Extensionality_Ensembles in O2.
        simpl.
        break_match.
        +
          break_match.
          *
            (* both mem_ops return Some *)
            rename m into m2, m0 into m1. (* to match operator indices *)
            destruct (mem_merge m2 m1) eqn:MM.
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

                unshelve epose proof (@HTSUMUnion_mem_out_fill_pattern
                              _ _ _
                              mop1 mop2
                              _ _
                              (svector_to_mem_block _ x) m) as P.
                apply Meq1.
                apply Meq2.
                simpl in P.
                unfold HTSUMUnion_mem in P. simpl in P.
                break_match_hyp; try some_none.
                break_match_hyp; try some_none.
                some_inv; subst m3.
                some_inv; subst m0.
                apply mem_merge_to_mem_union in MM.
                apply Some_inj_eq in MM.
                specialize (P MM).
                apply Some_inj_eq in MM.
                specialize (P k kc).
                destruct (NP.F.In_dec m k) as [K | NK].
                **
                  (* k in m *)
                  pose proof (mem_union_key_dec m m2 m1 MM k) as [MD _].
                  specialize (MD K).
                  clear H1.
                  apply P in K; clear P.

                  unshelve epose proof (HTSUMUnion_Facts dot op1 op2 compat) as facts.
                  apply Meq1.
                  apply Meq2.
                  pose proof (out_as_range _ x (SHOperator_Facts:=facts) G k kc) as V.
                  unfold HTSUMUnion in V; simpl in V.

                  rewrite <- O1 in K.
                  rewrite <- O2 in K.

                  apply V in K; clear V.
                  assert(V:=K).
                  apply H0 in K; clear H0.
                  apply NM.find_1 in K.
                  rewrite_clear K.
                  unfold HTSUMUnion', Vec2Union.
                  simpl.
                  rewrite Vnth_map2.

                  simpl in V.
                  unfold mem_union in MM; simpl in MM.
                  subst m.
                  unfold mem_union.
                  rewrite NM.map2_1 by (destruct MD; auto).

                  inversion MD.
                  ---
                    (* k in m2 *)
                    rename H into M1.
                    assert(NM1: not (NM.In (elt:=CarrierA) k m1)).
                    {
                      apply mem_keys_disjoint_inr with (m1:=m2).
                      rewrite is_disjoint_sym.
                      destruct Meq1.
                      apply Extensionality_Ensembles in out_pattern_compat0.
                      rewrite out_pattern_compat0 in compat.
                      destruct Meq2.
                      apply Extensionality_Ensembles in out_pattern_compat1.
                      rewrite out_pattern_compat1 in compat.
                      apply is_disjoint_Disjoint.
                      erewrite <- 2!mem_keys_set_to_m_out_index_set.
                      apply Disjoint_FinNat_to_nat.
                      eapply compat.
                      typeclasses eauto.
                      eauto.
                      eauto.
                      eauto.
                      eauto.
                    }

                    break_match; try (apply NP.F.not_find_in_iff in Heqo2; congruence).

                    (* derive m1[k] *)
                    assert (G1: (∀ (j : nat) (jc : (j < i)%nat), in_index_set Monoid_RthetaFlags op2 (mkFinNat jc) →  Is_Val (Vnth x jc))).
                    {
                      intros j jc H.
                      apply G.
                      right.
                      apply H.
                    }
                    apply Meq2 in G1.
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

                    unshelve epose proof (out_mem_fill_pattern _ _ Heqo3) as P2.
                    apply Meq1.
                    unfold mem_in in P2. specialize (P2 k kc).
                    apply not_iff_compat in P2.
                    apply P2 in NM1.
                    rewrite <- O1 in NM1.
                    apply svalue_at_sparse with (v:=x) in NM1.
                    rewrite NM1.
                    apply monoid_left_id.
                    apply af_mon.

                    rewrite <-NP.F.not_find_in_iff in Heqo0.
                    congruence.
                  ---
                    (* k in m2 *)
                    rename H into M2.
                    assert(NM2: not (NM.In (elt:=CarrierA) k m2)).
                    {
                      apply mem_keys_disjoint_inr with (m1:=m1).
                      destruct Meq2.
                      apply Extensionality_Ensembles in out_pattern_compat0.
                      rewrite out_pattern_compat0 in compat.
                      destruct Meq1.
                      apply Extensionality_Ensembles in out_pattern_compat1.
                      rewrite out_pattern_compat1 in compat.
                      apply is_disjoint_Disjoint.
                      erewrite <- 2!mem_keys_set_to_m_out_index_set.
                      apply Disjoint_FinNat_to_nat.
                      eapply compat.
                      typeclasses eauto.
                      eauto.
                      eauto.
                      eauto.
                      eauto.
                    }
                    break_match; try (apply NP.F.not_find_in_iff in NM2; congruence).
                    clear Heqo0.

                    (* derive m2[k] *)
                    assert (G2: (∀ (j : nat) (jc : (j < i)%nat), in_index_set Monoid_RthetaFlags op1 (mkFinNat jc) →  Is_Val (Vnth x jc))).
                    {
                      intros j jc H.
                      apply G.
                      left.
                      apply H.
                    }
                    apply Meq1 in G2.
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

                    unshelve epose proof (out_mem_fill_pattern _ _ Heqo2) as P1.
                    apply Meq2.
                    unfold mem_in in P1. specialize (P1 k kc).
                    apply not_iff_compat in P1.
                    apply P1 in NM2.
                    rewrite <- O2 in NM2.
                    apply svalue_at_sparse with (v:=x) in NM2.
                    rewrite NM2.
                    apply monoid_right_id.
                    apply af_mon.
                **
                  (* k not in m *)
                  rewrite MM.
                  replace (NM.find (elt:=CarrierA) k m) with (@None CarrierA)
                    by (symmetry; apply NP.F.not_find_in_iff, NK).
                  apply not_iff_compat in P.
                  apply P in NK; clear P.
                  unshelve epose proof (HTSUMUnion_Facts dot op1 op2 compat) as facts.
                  apply Meq1.
                  apply Meq2.
                  pose proof (no_vals_at_sparse _ x k kc ) as NV.
                  simpl in NV.
                  rewrite <- O1 in NK.
                  rewrite <- O2 in NK.
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
                apply mem_merge_to_mem_union in MM.
                rewrite MM in N.
                apply (mem_union_key_dec m m2 m1 MM k) in N.
                generalize dependent (svector_to_mem_block _ x).
                intros m0 H1 H2.
                destruct N as [IN1 | IN2].
                **
                  (* prove contradiction in N1 *)
                  unshelve epose proof (out_mem_oob _ _ H1) as NP1.
                  apply Meq2.
                  specialize (NP1 k kc).
                  unfold mem_in in NP1.
                  congruence.
                **
                  (* prove contradiction in N1 *)
                  unshelve epose proof (out_mem_oob _ _ H2) as NP2.
                  apply Meq1.
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
              generalize dependent (svector_to_mem_block _ x).
              intros m H1 H2.
              (* by `compat` hypothes, output index sets of op1 and op2 are disjoint.
               yet, but IN1 and IN2, 'k' belongs to both *)
              unshelve epose proof (out_mem_fill_pattern _ _ H1) as P1.
              apply Meq2.
              unshelve epose proof (out_mem_oob _ _ H1) as NP1.
              apply Meq2.
              unshelve epose proof (out_mem_fill_pattern _ _ H2) as P2.
              apply Meq1.
              unshelve epose proof (out_mem_oob _ _ H2) as NP2.
              apply Meq1.
              destruct (NatUtil.lt_ge_dec k o) as [kc | nkc].
              ++
                clear NP1 NP2.
                apply (P1 k kc) in IN1; clear P1.
                apply (P2 k kc) in IN2; clear P2.
                inversion_clear compat.
                specialize (H (mkFinNat kc)).
                apply out_pattern_compat in IN1.
                apply out_pattern_compat in IN2.
                crush.
              ++
                specialize (NP1 k nkc).
                unfold mem_in in NP1.
                congruence.
          *
            contradict Heqo1.
            apply is_Some_ne_None.
            unshelve eapply mem_out_some; eauto.
            apply Meq1.
            intros j jc H.
            apply svector_to_mem_block_In with (jc0:=jc).
            apply G.
            simpl.
            left.
            apply in_pattern_compat.
            apply H.
        +
          contradict Heqo0.
          apply is_Some_ne_None.
          unshelve eapply mem_out_some; eauto.
          apply Meq2.
          intros j jc H.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply G.
          simpl.
          right.
          apply in_pattern_compat.
          apply H.
    Qed.

    Definition shrink_SH_MSH_Operator_compat_family
               {svalue: CarrierA}
               {fm}
               {i o k : nat}
               (op_family : SHOperatorFamily fm (svalue:=svalue))
               (mop_family: MSHOperatorFamily)
               {Meq: forall j (jc:j< S k), SH_MSH_Operator_compat
                                        (op_family (mkFinNat jc))
                                        (mop_family (mkFinNat jc))}
      :
        (forall (j : nat) (jc : j < k),
            @SH_MSH_Operator_compat i o fm svalue
                                    ((shrink_op_family fm op_family) (mkFinNat jc))
                                    ((shrink_m_op_family mop_family) (mkFinNat jc))
        ).
      Proof.
        intros j jc.
        split.
        -
          apply shrink_op_family_facts.
          apply Meq.
        -
          apply shrink_m_op_family_facts.
          apply Meq.
        -
          apply Meq.
        -
          apply Meq.
        -
          apply Meq.
      Defined.

    Definition shrink_SH_MSH_Operator_compat_family_up
               {svalue: CarrierA}
               {fm}
               {i o k : nat}
               {op_family : SHOperatorFamily fm (svalue:=svalue)}
               {mop_family: MSHOperatorFamily}
               (Meq: forall j (jc:j< S k), SH_MSH_Operator_compat
                                        (op_family (mkFinNat jc))
                                        (mop_family (mkFinNat jc))
               )
      :
        (forall (j : nat) (jc : j < k),
            @SH_MSH_Operator_compat i o fm svalue
                            ((shrink_op_family_up fm op_family) (mkFinNat jc))
                            ((shrink_m_op_family_up mop_family) (mkFinNat jc))).

      Proof.
        intros j jc.
        split.
        -
          apply shrink_op_family_facts_up.
          apply Meq.
        -
          apply shrink_m_op_family_facts_up.
          apply Meq.
        -
          apply Meq.
        -
          apply Meq.
        -
          apply Meq.
      Defined.

    (* Like [shrink_op_family_mem_up] by [n] times *)
    Definition shrink_SH_MSH_Operator_compat_family_up_n
               {svalue: CarrierA}
               {fm}
               {i o k: nat}
               (d: nat)
               (op_family: SHOperatorFamily fm (svalue:=svalue))
               (mop_family: MSHOperatorFamily)
               {Meq: forall j (jc:j < (k+d)), SH_MSH_Operator_compat
                                           (op_family (mkFinNat jc))
                                           (mop_family (mkFinNat jc))
               }
      :
        (forall (j : nat) (jc : j < k),
            @SH_MSH_Operator_compat i o fm svalue
                            ((shrink_op_family_up_n fm d op_family) (mkFinNat jc))
                            ((shrink_m_op_family_up_n d mop_family) (mkFinNat jc))).
    Proof.
        intros j jc.
        split.
        -
          apply shrink_op_family_facts_up_n.
          apply Meq.
        -
          apply shrink_m_op_family_facts_up_n.
          apply Meq.
        -
          apply Meq.
        -
          apply Meq.
        -
          apply Meq.
      Defined.

    Lemma svector_to_mem_block_equiv
          {fm : Monoid RthetaFlags}
          {n:  nat}
          {a b: svector fm n}
      :
          Vforall2 (fun (x y:Rtheta' fm) => evalWriter x ≡ evalWriter y) a b ->
          Vforall2 (fun (x y:Rtheta' fm) => execWriter x = execWriter y) a b ->
          svector_to_mem_block _ a = svector_to_mem_block _ b.
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
          repeat break_if.
          1,3,4: intuition.
          rewrite H0 in *.
          congruence.
        +
          inversion S.
          unfold Is_Val, compose, IsVal, Is_true, not in *.
          repeat break_if.
          1,2,4: intuition.
          rewrite H0 in *.
          congruence.
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
        svector_to_mem_block _ (Vec2Union _ dot a b)
        =
        mem_merge_with_def dot
                           def
                          (svector_to_mem_block _ a)
                          (svector_to_mem_block _ b).
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
               (NE.mkEns (mem_keys_set (svector_to_mem_block _ v))).
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
      | [ |- context[svector_to_mem_block_spec ?fm ?v]] =>
        pose proof (svector_to_mem_block_index_sets (v:=v)) as H0;
        unfold svector_to_mem_block in H0
      | [ H: context[svector_to_mem_block_spec ?fm ?v] |- _ ] =>
        pose proof (svector_to_mem_block_index_sets (v:=v)) as H0;
        unfold svector_to_mem_block in H0
      end.

    Lemma svector_to_mem_block_Vec2Union_mem_union
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
        svector_to_mem_block _ (Vec2Union _ dot a b)
        =
        mem_union
          (svector_to_mem_block _ a)
          (svector_to_mem_block _ b).
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

      assert(D: is_disjoint (mem_keys_set m1) (mem_keys_set m2) ≡ true).
      {
        apply is_disjoint_Disjoint.
        apply Extensionality_Ensembles in S1.
        apply Extensionality_Ensembles in S2.
        rewrite <- S1, <- S2.
        apply Disjoint_FinNat_to_nat.
        apply compat.
      }
      unfold mem_union.
      mem_index_equiv k.
      rewrite NP.F.map2_1bis.

      destruct (NM.find (elt:=CarrierA) k m1) eqn: F1, (NM.find (elt:=CarrierA) k m2) eqn: F2.
      -
        (* both m1 and m2 - impossible *)
        exfalso.
        apply mem_keys_disjoint_inr with (k:=k) in D.
        apply Some_ne_None, NP.F.in_find_iff in F2.
        unfold mem_in in D.
        congruence.
        apply Some_ne_None, NP.F.in_find_iff in F1.
        apply F1.
      -
        (* k in m1 *)
        rewrite <- F1.

        rename F1 into H.
        apply Some_ne_None in H.
        apply NP.F.in_find_iff in H.

        destruct (lt_ge_dec k n) as [kc | nkc].
        +
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
        +
          unfold mem_lookup in *.
          rewrite O1, O0 by auto.
          reflexivity.
      -
        (* k in m2 *)
        rewrite <- F2.

        rename F2 into H.
        apply Some_ne_None in H.
        apply NP.F.in_find_iff in H.

        destruct (lt_ge_dec k n) as [kc | nkc].
        +
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
        +
          unfold mem_lookup in *.
          rewrite O2, O0 by auto.
          reflexivity.
      -
        (* neither in m1 or m2 *)
        destruct (lt_ge_dec k n) as [kc | nkc].
        +
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
          *
            apply not_iff_compat in I1.
            apply I1.
            apply NP.F.not_find_in_iff, F1.
          *
            apply not_iff_compat in I2.
            apply I2.
            apply NP.F.not_find_in_iff, F2.
        +
          apply Option_equiv_eq.
          apply O0; auto.
      -
        reflexivity.
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
        rewrite Vbuild_Sn in V.
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

        rewrite Vbuild_Sn in V;
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

    (* Extending [SH_MSH_Operator_compat]'s [in_pattern_compat] to families *)
    Lemma SH_MSH_family_in_pattern_compat
          {svalue : CarrierA}
          {fm}
          {i o k : nat}
          (op_family : SHOperatorFamily fm)
          (mop_family : @MSHOperatorFamily i o k)
          (Meq: ∀ (j : nat) (jc : j < k),
              SH_MSH_Operator_compat
                (op_family (mkFinNat jc))
                (mop_family (mkFinNat jc)))
      :
        Same_set _
                 (family_in_index_set (svalue:=svalue) fm op_family)
                 (m_family_in_index_set mop_family).
    Proof.
      induction k.
      -
        crush.
      -
        simpl.
        eapply Union_mor_Same_set.
        apply Meq.
        apply IHk.
        apply shrink_SH_MSH_Operator_compat_family.
        assumption.
    Qed.

    (* Extending [SH_MSH_Operator_compat]'s [out_pattern_compat] to families *)
    Lemma SH_MSH_family_out_pattern_compat
          {svalue : CarrierA}
          {fm}
          {i o k : nat}
          (op_family : SHOperatorFamily fm)
          (mop_family : @MSHOperatorFamily i o k)
          (Meq: ∀ (j : nat) (jc : j < k),
              SH_MSH_Operator_compat
                (op_family (mkFinNat jc))
                (mop_family (mkFinNat jc)))
      :
        Same_set _
                 (family_out_index_set (svalue:=svalue) fm op_family)
                 (m_family_out_index_set mop_family).
    Proof.
      induction k.
      -
        crush.
      -
        simpl.
        eapply Union_mor_Same_set.
        apply Meq.
        apply IHk.
        apply shrink_SH_MSH_Operator_compat_family.
        assumption.
    Qed.

    Ltac Lpos2 Lpos :=
      apply Forall_inv_tail in Lpos;
      apply Forall_inv in Lpos;
      apply Lpos.

    Ltac Lpos1 Lpos :=
      apply Forall_inv in Lpos; apply Lpos.

    Ltac Lpos_tail Lpos :=
      apply Forall_inv_tail in Lpos;
      apply Lpos.

    Ltac Lpos_tail2 Lpos :=
      apply Forall_inv_tail in Lpos;
      apply Forall_inv_tail in Lpos;
      apply Lpos.

    Ltac solve_Lpos Lpos :=
      try Lpos1 Lpos;
      try Lpos2 Lpos;
      try Lpos_tail Lpos;
      try Lpos_tail2 Lpos.

    Fact fold_left_closed_under_P
         {A : Type}
         `{Ae: Equiv A}
         (l : list A)
         (e : A)
         (f : A -> A -> A)
         `{P : SgPred A}
         `{CM: @CommutativeRMonoid _ _ f e P} (* we just need commutativity and associativity, but it is shoert to state it this way *)
         (Lpos: Forall P l)
      :
        P (fold_left f l e).
    Proof.
      destruct CM.
      destruct comrmonoid_rmon.
      clear rmonoid_left_id.
      clear rmonoid_right_id.
      destruct mon_restriction.
      revert e rmonoid_unit_P Lpos.
      induction l; intros.
      -
        apply rmonoid_unit_P.
      -
        cbn.
        apply IHl.
        solve_Lpos Lpos.
        apply rmonoid_plus_closed.
        apply rmonoid_unit_P.
        solve_Lpos Lpos.
        solve_Lpos Lpos.
    Qed.

    (* Similar to [fold_left_fold_left_rev] but using setoid equality under restriction *)
    Lemma fold_left_fold_left_rev_restricted
          {A : Type}
          `{Ae: Equiv A}
          `{Aeq: Equivalence A Ae}
          (l : list A)
          (e : A)
          (f : A -> A -> A)
          `{P : SgPred A}
          `{CM: @CommutativeRMonoid _ _ f e P} (* we just need commutativity and associativity, but it is shoert to state it this way *)
          (Lpos: Forall P l)
      :
        ListUtil.fold_left_rev f e l = fold_left f l e.
    Proof.
      rewrite fold_left_rev_def.
      rewrite <- fold_left_rev_right.
      rewrite rev_involutive.
      induction l; [reflexivity |].
      cbn.
      rewrite_clear IHl; try solve_Lpos Lpos.
      generalize dependent a.
      induction l; [reflexivity |].
      intros.
      cbn.
      setoid_rewrite <- rmonoid_ass; unfold sg_P; try typeclasses eauto; auto; solve_Lpos Lpos.
      unfold sg_op.
      setoid_rewrite <- IHl; try solve_Lpos Lpos.
      2:{
        apply Forall_cons.
        apply CM.
        Lpos1 Lpos.
        Lpos2 Lpos.
        Lpos_tail2 Lpos.
      }
      setoid_rewrite <- rmonoid_ass; try typeclasses eauto; try solve_Lpos Lpos.
      f_equiv.
      unfold sg_op.
      unshelve eapply rcommutativity; try typeclasses eauto; try solve_Lpos Lpos.
      apply fold_left_closed_under_P; try typeclasses eauto; auto; try solve_Lpos Lpos.
      apply CM.
    Qed.

    Definition dense_block (k:nat) (m: mem_block) : Prop :=
      forall j, (j<k) <-> is_Some (NM.find j m).

    Global Instance dense_block_proper:
      Proper ((=) ==> (=) ==> iff) dense_block.
    Proof.
      intros n m Enm a b Eab.
      cbv in Enm; subst m.
      unfold dense_block.
      do 2 split; intros.
      all: rewrite H in *.
      all: rewrite is_Some_equiv_def in *.
      all: destruct H0.
      all: try rewrite Eab in H0; eauto.
      all: try rewrite <-Eab in H0; eauto.
    Qed.

    Definition mem_block_SGP (SGP : SgPred CarrierA) (m : mem_block) :=
      forall k x, NM.find (elt:=CarrierA) k m = Some x -> SGP x.

    Instance mem_block_SGP_proper (SGP : SgPred CarrierA) :
      Proper ((=) ==> iff) (mem_block_SGP SGP).
    Proof.
      intros m1 m2 ME.
      unfold mem_block_SGP.
      split; intros.
      all: apply H with (k:=k).
      rewrite ME; assumption.
      rewrite <-ME; assumption.
    Qed.

    (* Dense block where all values satisfiy [SGP] *)
    Definition dense_block_SGP
               (SGP : SgPred CarrierA)
               (k:nat)
               (m: mem_block) : Prop
      := (dense_block k m) /\ (mem_block_SGP SGP m).

    Instance dense_block_SGP_proper (SGP : SgPred CarrierA) :
      Proper ((=) ==> (=) ==> iff) (dense_block_SGP SGP).
    Proof.
      intros n' n NE m1 m2 ME.
      cbv in NE; subst.
      unfold dense_block_SGP.
      rewrite ME.
      reflexivity.
    Qed.

    Lemma dense_block_find_Some
          {k n : nat}
          {m : mem_block}
          {c: CarrierA}:
      dense_block n m →
      NM.find (elt:=CarrierA) k m ≡ Some c ->
      k<n.
    Proof.
      intros D F.
      apply D.
      rewrite F; reflexivity.
   Qed.

    Lemma dense_block_find_not_None
          {n : nat}
          {m : mem_block}:
      dense_block n m → forall k : NM.key, k<n -> NM.find (elt:=CarrierA) k m ≢ None.
    Proof.
      intros H k kc.
      apply is_Some_ne_None.
      apply H.
      assumption.
    Qed.

    Ltac dense_find_contr :=
      match goal with
      | [D: dense_block ?n0 ?x0,
            F: NM.find (elt:=CarrierA) ?k ?x0 ≡ Some ?c0,
               D1: dense_block ?n ?x,
                   F1: NM.find (elt:=CarrierA) ?k ?x ≡ None
         |- _
        ] =>
        pose proof (dense_block_find_Some D F);
        contradict F1; eapply dense_block_find_not_None; eauto
      end.

    Lemma mem_block_Equiv_decidable (m1 m2 : mem_block) :
      {mem_block_Equiv m1 m2} + {not (mem_block_Equiv m1 m2)}.
    Proof.
      intros.
      destruct (NM.equal CarrierA_beq m1 m2) eqn:EQ.
      -
        left.
        apply NP.F.equal_iff in EQ.
        rewrite <-NP.F.Equiv_Equivb
          with (eq_elt:=(=))
          in EQ
          by (unfold NP.F.compat_cmp; apply CarrierA_eqb_equiv).
        inversion_clear EQ as [K E].
        
        intros k.
        specialize (K k); specialize (E k).
        destruct NM.find eqn:KM1 at 1, NM.find eqn:KM2 at 1.
        +
          rewrite <-NP.F.find_mapsto_iff in *.
          specialize (E c c0 KM1 KM2).
          rewrite E; reflexivity.
        +
          apply NP.F.not_find_in_iff in KM2.
          contradict KM2.
          apply K.
          apply NP.F.in_find_iff.
          congruence.
        +
          apply NP.F.not_find_in_iff in KM1.
          contradict KM1.
          apply K.
          apply NP.F.in_find_iff.
          congruence.
        +
          reflexivity.
      -
        right.
        intros C.
        contradict EQ.
        apply not_false_iff_true.
        apply NP.F.equal_iff.
        rewrite <-NP.F.Equiv_Equivb
          with (eq_elt:=(=))
          by (unfold NP.F.compat_cmp; apply CarrierA_eqb_equiv).
        constructor.
        +
          intros k; specialize (C k).
          destruct NM.find eqn:KM1, NM.find eqn:KM2 in C; try some_none.
          all: repeat rewrite NP.F.in_find_iff.
          all: rewrite KM1, KM2.
          all: split; intros; congruence.
        +
          intros k e1 e2 KM1 KM2; specialize (C k).
          rewrite NP.F.find_mapsto_iff in *.
          rewrite KM1, KM2 in C.
          some_inv; assumption.
    Qed.

    Definition empty_or_dense_block_SGP (SGP : SgPred CarrierA) (k : nat) (m : mem_block) :=
      m = mem_empty \/ dense_block_SGP SGP k m.

    Lemma mem_merge_with_def_dense_preserve
          (m1 m2 : mem_block)
          (dot : CarrierA -> CarrierA -> CarrierA)
          (init : CarrierA)
          (k : nat)
          (D1 : dense_block k m1)
          (D2 : dense_block k m2)
      :
        dense_block k (mem_merge_with_def dot init m1 m2).
    Proof.
      unfold dense_block, mem_merge_with_def in *.
      intros.
      specialize (D1 j); specialize (D2 j).
      repeat rewrite NP.F.map2_1bis by reflexivity.
      repeat break_match.
      all: try apply Some_ne_None in Heqo.
      all: try apply Some_ne_None in Heqo0.
      all: try rewrite <-NP.F.in_find_iff in *.
      all: try rewrite <-NP.F.not_find_in_iff in *.
      all: split; intros; tauto.
    Qed.

    Lemma mem_merge_with_def_empty_dense_preserve_l
          (m2 : mem_block)
          (dot : CarrierA -> CarrierA -> CarrierA)
          (init : CarrierA)
          (k : nat)
          (D2 : dense_block k m2)
      :
        dense_block k (mem_merge_with_def dot init mem_empty m2).
    Proof.
      unfold dense_block, mem_merge_with_def in *.
      intros.
      specialize (D2 j).
      repeat rewrite NP.F.map2_1bis by reflexivity.
      repeat break_match.
      all: try apply Some_ne_None in Heqo.
      all: try apply Some_ne_None in Heqo0.
      all: try rewrite <-NP.F.in_find_iff in *.
      all: try rewrite <-NP.F.not_find_in_iff in *.
      all: split; intros; try tauto.
      inversion Heqo; inversion H0.
      inversion Heqo; inversion H0.
    Qed.

    Lemma mem_merge_with_def_empty_dense_preserve_r
          (m1 : mem_block)
          (dot : CarrierA -> CarrierA -> CarrierA)
          (init : CarrierA)
          (k : nat)
          (D1 : dense_block k m1)
      :
        dense_block k (mem_merge_with_def dot init m1 mem_empty).
    Proof.
      unfold dense_block, mem_merge_with_def in *.
      intros.
      specialize (D1 j).
      repeat rewrite NP.F.map2_1bis by reflexivity.
      repeat break_match.
      all: try apply Some_ne_None in Heqo.
      all: try apply Some_ne_None in Heqo0.
      all: try rewrite <-NP.F.in_find_iff in *.
      all: try rewrite <-NP.F.not_find_in_iff in *.
      all: split; intros; try tauto.
      inversion Heqo0; inversion H0.
      inversion Heqo0; inversion H0.
    Qed.

    Lemma mem_merge_with_def_SGP_preserve
          (m1 m2 : mem_block)
          (svalue : CarrierA)
          (dot : CarrierA → CarrierA → CarrierA)
          (SGP : SgPred CarrierA)
          `{SPGP : !Proper ((=) ==> impl) SGP}
          (CM : @CommutativeRMonoid CarrierA CarrierAe dot svalue SGP)
          (SM1 : mem_block_SGP SGP m1)
          (SM2 : mem_block_SGP SGP m2)
      :
        mem_block_SGP SGP (mem_merge_with_def dot svalue m1 m2).
    Proof.
      unfold mem_block_SGP in *.
      intros.
      specialize (SM1 k); specialize (SM2 k) (* ; specialize (SK k) *).
      unfold mem_merge_with_def in H.
      rewrite NP.F.map2_1bis in H by reflexivity.
      repeat break_match; try some_none; some_inv.
      -
        specialize (SM1 c); autospecialize SM1; [reflexivity |].
        specialize (SM2 c0); autospecialize SM2; [reflexivity |].
        apply (SPGP (dot c c0) x H).
        eapply rmonoid_plus_closed with (Aunit:=svalue); try eassumption.
        typeclasses eauto.
      -
        specialize (SM1 c); autospecialize SM1; [reflexivity |].
        apply (SPGP (dot c svalue) x H).
        eapply rmonoid_plus_closed with (Aunit:=svalue); try eassumption.
        typeclasses eauto.
        eapply rmonoid_unit_P with (Aunit:=svalue) (Aop:=dot).
        typeclasses eauto.
      -
        specialize (SM2 c); autospecialize SM2; [reflexivity |].
        apply (SPGP (dot svalue c) x H).
        clear H x Heqo0 Heqo k m1 m2.
        eapply rmonoid_plus_closed with (Aunit:=svalue); try eassumption.
        typeclasses eauto.
        eapply rmonoid_unit_P with (Aunit:=svalue) (Aop:=dot).
        typeclasses eauto.
    Qed.

    Lemma mem_empty_SGP (SGP : SgPred CarrierA) :
      mem_block_SGP SGP mem_empty.
    Proof.
      unfold mem_block_SGP.
      intros k x C; inversion C.
    Qed.

    Lemma exists_or {A : Type} (P Q : A -> Prop) :
      (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
    Proof.
      split; intros.
      -
        destruct H as [x [Px | Qx]]; [left | right].
        all: exists x; assumption.
      -
        destruct H as [[x Px] | [x Py]]; exists x; [left | right].
        all: assumption.
    Qed.

    Lemma InA_eqA_swap
          {A : Type}
          (eqA1 eqA2 : A -> A -> Prop)
          (x : A)
          (l : list A)
          (EQA : forall x1 x2, eqA1 x1 x2 <-> eqA2 x1 x2)
      :
        InA eqA1 x l <-> InA eqA2 x l.
    Proof.
      induction l.
      -
        split; intros C; inversion C.
      -
        split; intros.
        all: inversion H; [constructor 1; apply EQA | constructor 2; apply IHl].
        all: assumption.
    Qed.

    Lemma mem_merge_with_def_empty_const
          (dot : CarrierA -> CarrierA -> CarrierA)
          (init : CarrierA)
          (mb : mem_block)
          (n : nat)
          (MD : forall k, k < n -> mem_in k mb)
      :
        mem_merge_with_def dot init mem_empty mb =
        mem_merge_with_def dot init (mem_const_block n init) mb.
    Proof.
      intros.
      intros k.
      destruct (le_lt_dec n k).
      -
        unfold mem_lookup, mem_merge_with_def.
        repeat rewrite NP.F.map2_1bis by reflexivity.
        rewrite mem_const_block_find_oob by assumption.
        reflexivity.
      -
        unfold mem_lookup, mem_merge_with_def.
        repeat rewrite NP.F.map2_1bis by reflexivity.
        rewrite mem_const_block_find by assumption.
        cbn.
        break_match; try reflexivity.
        specialize (MD k l).
        unfold mem_in in MD.
        apply NP.F.in_find_iff in MD.
        congruence.
    Qed.

    Lemma fold_left_init_swap
          {A B : Type}
          {EqA : Equiv A}
          {EqAE : Equivalence EqA}
          (f : A -> B -> A)
          (PF : Proper ((=) ==> (≡) ==> (=)) f)
          (h : B)
          (tl : list B)
          (init1 init2 : A)
      :
        f init1 h = f init2 h ->
        fold_left f (h :: tl) init1 = fold_left f (h :: tl) init2.
    Proof.
      intros.
      cbn.
      rewrite H.
      reflexivity.
    Qed.

    (* TODO: move  *)
    Lemma NM_find_In_elments
          (a : mem_block)
          (x : CarrierA)
          (k : NM.key):
      NM.find (elt:=CarrierA) k a ≡ Some x →
      In (k, x) (NM.elements (elt:=CarrierA) a).
    Proof.
      intros F.
      rewrite NP.F.elements_o in F.
      apply In_InA_eq.
      apply findA_NoDupA in F.
      -

        generalize dependent (NM.elements a).
        intros e F.
        induction e.
        +
          apply InA_nil in F.
          tauto.
        +
          destruct a0 as [k' x'].
          apply InA_cons in F.
          destruct F as [[Fhk Fhx] | Ft]; apply InA_cons.
          *
            left.
            cbn in *.
            subst.
            reflexivity.
          *
            right.
            apply IHe, Ft.
      -
        typeclasses eauto.
      -
        apply NM.elements_3w.
    Qed.

    (* TODO: move  *)
    Lemma NM_find_not_In_elments
          (a : mem_block)
          (k : NM.key):
      NM.find (elt:=CarrierA) k a ≡ None →
      forall x, not (In (k, x) (NM.elements (elt:=CarrierA) a)).
    Proof.
      intros F x H.
      rewrite NP.F.elements_o in F.
      apply In_InA_eq in H.
      generalize dependent (NM.elements a).
      intros e F H.
      induction e.
      +
        inv H.
      +
        destruct a0 as [k' x'].
        apply InA_cons in H.
        destruct H.
        *
          tuple_inversion.
          inv F.
          break_if.
          some_none.
          unfold NP.F.eqb in Heqb.
          break_if; crush.
        *
          apply IHe.
          --
            inv F.
            break_if.
            some_none.
            reflexivity.
          --
            apply H.
    Qed.

    Fact find_mem_empty_eq_None (mb : mem_block) :
      mb = mem_empty ->
      forall k, NM.find (elt:=CarrierA) k mb ≡ None.
    Proof.
      intros.
      apply None_equiv_eq.
      apply H.
    Qed.

    Lemma CarrierA_equiv_eq (a1 a2 : CarrierA) :
      a1 ≡ a2 -> a1 = a2.
    Proof.
      intros; subst; reflexivity.
    Qed.

    Ltac assert_SGPs :=
      repeat match goal with
             | [S : mem_block_SGP _ ?mb, F : NM.find _ ?mb ≡ Some _ |- _] =>
               apply Option_equiv_eq, S in F
             | [S : mem_block_SGP _ ?mb, F : NM.find _ ?mb = Some _ |- _] =>
               apply S in F
             end.

    Local Instance mem_merge_with_def_CM
          (n: nat)
          (svalue : CarrierA)
          (dot : CarrierA → CarrierA → CarrierA)
          (SGP : SgPred CarrierA)
          `{SPGP: !Proper ((=) ==> impl) SGP}
          (CM: @CommutativeRMonoid CarrierA CarrierAe dot svalue SGP):
      @CommutativeRMonoid mem_block mem_block_Equiv
                          (mem_merge_with_def dot svalue) mem_empty
                          (empty_or_dense_block_SGP SGP n).
    Proof.
      split.
      -
        split.
        split; typeclasses eauto.
        +
          (* MonRestriction *)
          split.
          unfold mon_unit, sg_P.
          unfold empty_or_dense_block_SGP.
          left; reflexivity.
          intros a b H H0.
          unfold sg_P in *.
          unfold sg_op, empty_or_dense_block_SGP.
          destruct H, H0.
          *
            left.
            rewrite H, H0.
            intros k.
            unfold mem_merge_with_def.
            repeat rewrite NP.F.map2_1bis by reflexivity.
            reflexivity.
          *
            right.
            unfold dense_block_SGP in *.
            destruct H0 as [DB SB].
            split.
            rewrite_clear H.
            apply mem_merge_with_def_empty_dense_preserve_l; assumption.
            apply mem_merge_with_def_SGP_preserve; try assumption.
            rewrite H.
            apply mem_empty_SGP.
          *
            right.
            unfold dense_block_SGP in *.
            destruct H as [DB SB].
            split.
            rewrite_clear H0.
            apply mem_merge_with_def_empty_dense_preserve_r; assumption.
            apply mem_merge_with_def_SGP_preserve; try assumption.
            rewrite H0.
            apply mem_empty_SGP.
          *
            right.
            unfold dense_block_SGP in *.
            destruct H as [DA SA], H0 as [DB SB].
            split.
            apply mem_merge_with_def_dense_preserve; assumption.
            apply mem_merge_with_def_SGP_preserve; assumption.
        +
          (* Proper sg_op *)
          intros l1 l2 LE r1 r2 RE.
          intros k.
          specialize (LE k); specialize (RE k).
          unfold sg_op, mem_merge_with_def.
          repeat rewrite NP.F.map2_1bis by reflexivity.
          repeat break_match; try some_none; repeat some_inv.
          all: try rewrite LE; try rewrite RE; reflexivity.
        +
          (* assoc *)
          inversion_clear CM as [RM COMM].
          inversion_clear RM as [S MR SP ASS LID RID].
          inversion_clear MR as [UP PC].
          intros x y z SGX SGY SGZ.
          intros k.
          unfold sg_op, mem_merge_with_def.
          repeat rewrite NP.F.map2_1bis by reflexivity.
          destruct SGX as [Ex | [Dx Sx]],
                   SGY as [Ey | [Dy Sy]],
                   SGZ as [Ez | [Dz Sz]].
          (* doing three rewrites with set blocks, because they are not found otherwise *)
          all: repeat rewrite find_mem_empty_eq_None with (mb:=x) by assumption.
          all: repeat rewrite find_mem_empty_eq_None with (mb:=y) by assumption.
          all: repeat rewrite find_mem_empty_eq_None with (mb:=z) by assumption.
          all: repeat break_match; try some_none; repeat some_inv.
          all: f_equiv.
          all: try apply CarrierA_equiv_eq in H0.
          all: try apply CarrierA_equiv_eq in H1.
          all: repeat rewrite LID; try reflexivity.
          all: repeat rewrite RID; try reflexivity.
          all: assert_SGPs.
          all: try assumption.
          all: try (apply PC; assumption).
          apply ASS; assumption.
        +
          (* left id *)
          intros x [Ex | [Pxd Px]].
          {
            (* empty x *)
            intros k.
            unfold sg_op, mem_merge_with_def.
            rewrite NP.F.map2_1bis by reflexivity.
            cbn.
            rewrite find_mem_empty_eq_None by assumption.
            reflexivity.
          }
          unfold equiv, mem_block_Equiv.
          intros k.
          unfold sg_op.
          unfold mem_merge_with_def.
          repeat rewrite NP.F.map2_1bis by reflexivity.
          repeat break_match; try some_none;
            repeat some_inv;
            f_equiv;
            subst.
          *
            unfold mon_unit, mem_empty in *.
            pose proof (NP.F.empty_o CarrierA k); some_none.
          *
            unfold mon_unit, mem_empty in *.
            pose proof (NP.F.empty_o CarrierA k); some_none.
          *
            clear Heqo.
            eapply rmonoid_left_id.
            apply CM.
            eapply Px.
            rewrite Heqo0; reflexivity.
        +
          (* right id *)
          intros x [Ex | [Pxd Px]].
          {
            (* empty x *)
            intros k.
            unfold sg_op, mem_merge_with_def.
            rewrite NP.F.map2_1bis by reflexivity.
            cbn.
            rewrite find_mem_empty_eq_None by assumption.
            reflexivity.
          }
          intros k.
          unfold sg_op.
          unfold mem_merge_with_def.
          repeat rewrite NP.F.map2_1bis by reflexivity.
          repeat break_match; try some_none;
            repeat some_inv;
            f_equiv;
            subst.
          *
            unfold mon_unit, mem_empty in *.
            pose proof (NP.F.empty_o CarrierA k); some_none.
          *
            eapply rmonoid_right_id.
            apply CM.
            eapply Px.
            rewrite Heqo; reflexivity.
          *
            unfold mon_unit, mem_empty in *.
            pose proof (NP.F.empty_o CarrierA k); some_none.
      -
        (* commutativity *)
        intros x y [Ex | [Hxd Hx]] [Ey | [Hyd Hy]].
        all: intros k.
        all: unfold sg_op, mem_merge_with_def.
        all: repeat rewrite NP.F.map2_1bis.
        (* doing three rewrites with set blocks, because they are not found otherwise *)
        all: repeat rewrite find_mem_empty_eq_None with (mb:=x) by assumption.
        all: repeat rewrite find_mem_empty_eq_None with (mb:=y) by assumption.
        all: repeat rewrite find_mem_empty_eq_None with (mb:=z) by assumption.
        all: try reflexivity.
        +
          break_match; f_equiv.
          apply rcommutativity with (Aunit:=svalue) (Ares:=SGP).
          typeclasses eauto.
          apply rmonoid_unit_P with (Aop:=dot) (Aunit:=svalue) (Apred:=SGP).
          typeclasses eauto.
          assert_SGPs.
          assumption.
        +
          break_match; f_equiv.
          apply rcommutativity with (Aunit:=svalue) (Ares:=SGP).
          typeclasses eauto.
          assert_SGPs.
          assumption.
          apply rmonoid_unit_P with (Aop:=dot) (Aunit:=svalue) (Apred:=SGP).
          typeclasses eauto.
        +
          repeat break_match; f_equiv.
          all: apply rcommutativity with (Aunit:=svalue) (Ares:=SGP);
            [typeclasses eauto | |].
          all: assert_SGPs; try assumption.
          all: apply rmonoid_unit_P with (Aop:=dot) (Aunit:=svalue) (Apred:=SGP).
          all: typeclasses eauto.
    Qed.

    (* Positivity propagation *)
    Fact Apply_mem_Family_lift_SGP
         {i o k: nat}
         (svalue : CarrierA)
         `{SGP : SgPred CarrierA}
         `{SPGP: !Proper ((=) ==> impl) SGP}
         (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k svalue)
         (mop_family : MSHOperatorFamily)
         (Upoz: Apply_Family_Vforall_P _ (liftRthetaP SGP) op_family)
         (Meq: forall j (jc:j<k), SH_MSH_Operator_compat
                               (op_family (mkFinNat jc))
                               (mop_family (mkFinNat jc)))
         (compat: forall j (jc:j<k),
             Ensembles.Same_set _
                                (out_index_set _ (op_family (mkFinNat jc)))
                                (Full_set _))
         (x : vector (Rtheta' Monoid_RthetaSafeFlags) i)
         (l : list mem_block)
         (A: Apply_mem_Family (n:=k) (get_family_mem_op (i:=i) (o:=o) mop_family)
                              (@svector_to_mem_block Monoid_RthetaSafeFlags i x) ≡
             Some l)
         (W : forall (j : nat) (jc : j < i),
             family_in_index_set Monoid_RthetaSafeFlags op_family (mkFinNat jc)
             -> Is_Val (Vnth x jc))
      :
        Forall (empty_or_dense_block_SGP SGP o) l.
    Proof.
      apply Forall_forall.
      intros v N.
      apply In_nth_error in N.
      destruct N as [t N].
      pose proof (ListNth.nth_error_length_lt _ _ N) as tc.
      pose proof (Apply_mem_Family_length A) as L.
      rewrite L in tc.

      specialize (Meq t tc).
      destruct Meq as [H1 H2 H3 H4 ME].
      specialize (ME x).

      apply Apply_mem_Family_eq_Some with (jc:=tc) in A.
      unfold mem_block in A, N.
      rewrite A in N; clear A.
      unfold empty_or_dense_block_SGP, dense_block_SGP.
      right.
      assert(dense_block o v) as D.
      {
        unfold dense_block.
        intros j.
        split.
        -
          intros jc.
          unfold get_family_mem_op in N.
          eapply out_mem_fill_pattern with (jc0:=jc) in N.
          apply is_Some_ne_None.
          apply NP.F.in_find_iff.
          apply N.

          unfold Same_set in *.
          apply H4.
          specialize (compat t tc).
          destruct compat as [C1 C2].
          unfold Included in *.
          apply C2.
          apply Full_intro.
        -
          intros H.
          destruct (lt_ge_dec j o); auto.
          unfold get_family_mem_op in N.
          apply out_mem_oob with (j0:=j) in N.
          apply is_Some_ne_None in H.
          apply NP.F.in_find_iff in H.
          unfold mem_in in N.
          congruence.
          auto.
      }
      split; [ apply D|].
      intros j m M.
      specialize (Upoz x t tc).
      destruct (lt_ge_dec j o) as [jc|njc].
      -
        apply Vforall_nth with (ip:=jc) in Upoz.
        unfold get_family_op in Upoz.
        unfold get_family_mem_op in N.
        repeat eq_to_equiv_hyp.
        rewrite <- ME in N;[|intros;apply W].
        some_inv.
        rewrite <- N in M.
        unfold mem_lookup in M.
        rewrite find_svector_to_mem_block_some with (kc:=jc) in M.
        2:{
          (* could be derived from 'compat' *)
          apply NP.F.in_find_iff.
          apply Some_nequiv_None in M.
          apply None_nequiv_neq.
          apply M.
        }
        some_inv.
        unfold liftRthetaP in Upoz.
        rewrite M in Upoz.
        apply Upoz.
        eapply family_in_set_includes_members.
        eapply H.
      -
        exfalso.
        unfold get_family_mem_op in N.
        apply out_mem_oob with (j0:=j) in N.
        destruct (NM.find (elt:=CarrierA) j) eqn:FF.
        apply Some_ne_None, NP.F.in_find_iff in FF.
        unfold mem_in in N.
        congruence.
        some_none.
        assumption.
    Qed.

    Global Instance IReduction_SH_MSH_Operator_compat
           {i o k: nat}
           (svalue: CarrierA)
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot} (* might not be needed *)
           `{SGP : SgPred CarrierA}
           `{SPGP: !Proper ((=) ==> impl) SGP}
           `{CM: @CommutativeRMonoid _ _ dot svalue SGP}
           `{scompat: BFixpoint svalue dot} (* TODO: try to remove. Follows from CommutativeRMonoid *)
           (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k svalue)
           (mop_family: MSHOperatorFamily)
           (Meq: forall j (jc:j<k), SH_MSH_Operator_compat
                                 (op_family (mkFinNat jc))
                                 (mop_family (mkFinNat jc)))
           (compat: forall j (jc:j<k),
               Ensembles.Same_set _
                                  (out_index_set _ (op_family (mkFinNat jc)))
                                  (Full_set _))
           (Upoz: Apply_Family_Vforall_P _ (liftRthetaP SGP) op_family)
      : SH_MSH_Operator_compat
          (IReduction dot op_family)
          (MSHIReduction svalue dot mop_family).
    Proof.
      split.
      -
        apply IReduction_Facts.
        apply Meq.
      -
        apply IReduction_MFacts.
        apply Meq.
        intros j jc.
        specialize (compat j jc).
        apply Extensionality_Ensembles in compat.
        rewrite <- compat.
        symmetry.
        apply Meq.
      -
        simpl.
        apply SH_MSH_family_in_pattern_compat.
        assumption.
      -
        apply SH_MSH_family_out_pattern_compat.
        assumption.
      -
        (* mem_vec_preservation *)
        intros x H.
        rename k into n.
        unfold MSHIReduction, IReduction, IReduction_mem, Diamond in *.
        simpl in *.
        break_match; rename Heqo0 into A.
        +
          f_equiv.
          unshelve rewrite <- fold_left_fold_left_rev_restricted.
          exact (empty_or_dense_block_SGP SGP o).
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
            rewrite Vbuild_Sn in A1.
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
            (* shrink Upoz *)
            assert(Upoz': Apply_Family_Vforall_P Monoid_RthetaSafeFlags (liftRthetaP SGP)(shrink_op_family_up Monoid_RthetaSafeFlags op_family)).
            {
              intros x' j jc.
              apply Upoz.
            }
            
            specialize (IHn
                          (shrink_op_family_up _ op_family)
                          (shrink_m_op_family_up mop_family)
                          _
                          compat'
                          Upoz'
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
              f_equiv. apply pdot.
              apply Some_inj_equiv.
              rewrite <- A0. clear A0.
              unfold get_family_op, get_family_mem_op.
              eapply mem_vec_preservation.
              intros j jc H0.
              apply H.
              eapply family_in_set_includes_members.
              apply H0.
              exact o. (* TODO: not sure where this is coming from *)
            --
              apply Vec2Union_fold_zeros_dense with (op_family0:=op_family) (x0:=x); auto.
              apply Meq.
            --
              apply Vforall_nth_intro.
              intros j jc.
              apply Meq.
              intros t tc HH.
              specialize (H t tc).
              apply H.
              eapply family_in_set_includes_members.
              eapply HH.
              apply compat.
              apply Full_intro.
          *
            typeclasses eauto.
          *
            eapply Apply_mem_Family_lift_SGP; eauto.
        +
          (* [A] could not happen *)
          exfalso.
          unfold Apply_mem_Family in A.
          apply monadic_Lbuild_op_eq_None in A.
          destruct A as [t [tc A]].
          contradict A.
          apply is_Some_ne_None.
          apply Meq.
          intros j jc H0.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply H.
          eapply family_in_set_includes_members.
          apply Meq.
          apply H0.
    Qed.

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
        SHOperator_Facts fm (cast_op_family fm op_family E (mkFinNat jc)).
    Proof.
      crush.
      (* TODO: better proof. *)
    Qed.

    Lemma cast_SH_MSH_Operator_compat
          {svalue: CarrierA}
          {fm}
          {i o n m: nat}
          {op_family: @SHOperatorFamily fm i o m svalue}
          {mop_family: @MSHOperatorFamily i o m}
          {op_family_facts : forall (j: nat) (jc: j < m),
              SHOperator_Facts fm (op_family (mkFinNat jc))}
          (op_family_mem : forall (j: nat) (jc: j < m),
              SH_MSH_Operator_compat
                (op_family (mkFinNat jc))
                (mop_family (mkFinNat jc)))
          (E: m≡n):
      forall (j : nat) (jc : j < n),
        SH_MSH_Operator_compat
          (cast_op_family _ op_family E (mkFinNat jc))
          (cast_m_op_family mop_family E (mkFinNat jc)).
    Proof.
      intros j jc.
      unfold cast_op_family.
      break_match.
      auto.
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
                     (cast_op_family _ op_family E) t' tn x.
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
                    (cast_op_family _ op_family E (mkFinNat tn)).
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
                    (cast_op_family _ op_family E (mkFinNat tn)).
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
         (mop_family: MSHOperatorFamily)
         (Meq: forall j (jc: j < (n+d)), SH_MSH_Operator_compat
                                      (op_family (mkFinNat jc))
                                      (mop_family (mkFinNat jc)))

         (compat : ∀ (m0 : nat) (mc : m0 < (n+d)) (n0 : nat) (nc : n0 < (n+d)),
             m0 ≢ n0
             → Disjoint (FinNat o)
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat mc)))
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat nc))))

         (m m0 m1 : mem_block)
         (l: list mem_block)
         (A : Apply_mem_Family
                (get_family_mem_op
                   (shrink_m_op_family_up_n d mop_family)) m
                ≡ Some l)

         (t:nat)
         (tc: t<d)
         (tc1: t<n+d)
         (H0: get_family_mem_op mop_family _ tc1 m ≡ Some m0)

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

          apply IHn with (d:=(S d))
                         (m:=m)
                         (m0:=m0)
                         (l:=m1t)
                         (t:=t)
                         (tc1:=tc2)
                         (op_family:=cast_op_family _ op_family K)
                         (mop_family:=cast_m_op_family mop_family K); eauto.
          *
            intros j jc.

            unfold cast_op_family, cast_m_op_family.
            break_match.
            apply Meq.
          *
            intros m0' mc' n0' nc' H.
            assert(mc'': m0' < S n + d) by lia.
            assert(nc'': n0' < S n + d) by lia.
            specialize (compat m0' mc'' n0' nc'' H).

            erewrite <- cast_out_index_set_eq.
            erewrite <- cast_out_index_set_eq.
            apply compat.
            apply Meq.
            apply Meq.
          *
            rewrite <- A.
            unfold shrink_m_op_family_up, shrink_op_family_up, shrink_op_family_facts_up,
            shrink_m_op_family, shrink_op_family, shrink_op_family_facts,
            shrink_op_family_up_n, shrink_op_family_facts_up_n, shrink_m_op_family_up_n.
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
          unfold shrink_m_op_family_up, shrink_op_family_up, shrink_op_family_facts_up,
          shrink_m_op_family, shrink_op_family, shrink_op_family_facts,
          shrink_op_family_up_n, shrink_op_family_facts_up_n, shrink_m_op_family_up_n
            in *.
          simpl in *.
          specialize (compat t tc1).
          specialize (compat d (Plus.plus_lt_compat_r O (S n) d (Nat.lt_0_succ n))).
          apply Disjoint_FinNat_to_nat in compat.

          pose proof (@out_pattern_compat _ _ _ _
                                          (op_family (mkFinNat tc1))
                                          (mop_family (mkFinNat tc1))
                                          (Meq t tc1)
                     ) as P1.
          apply Extensionality_Ensembles in P1.
          rewrite P1 in compat. clear P1.

          remember (Plus.plus_lt_compat_r 0 (S n) d (Nat.lt_0_succ n)) as zc.
          epose proof (@out_pattern_compat _ _ _ _
                                           (op_family (mkFinNat zc))
                                           (mop_family (mkFinNat zc))
                                           (Meq (0+d) _)

                      ) as P2.
          apply Extensionality_Ensembles in P2.
          unfold mkFinNat in compat, P2.
          simpl in compat, P2.
          rewrite P2 in compat.
          clear P2 Heqzc.
          erewrite mem_keys_set_to_m_out_index_set in compat.
          erewrite mem_keys_set_to_m_out_index_set in compat.
          eapply compat.
          apply Meq.
          eauto.
          apply Meq.
          eauto.
          lia.
    Qed.

    Fact IUnion_mem_1_step_disjoint
         {svalue: CarrierA}
         {i o n : nat}
         (op_family: @SHOperatorFamily Monoid_RthetaFlags i o (S n) svalue)
         (mop_family: MSHOperatorFamily)
         (Meq: forall j (jc: j < (S n)), SH_MSH_Operator_compat
                                      (op_family (mkFinNat jc))
                                      (mop_family (mkFinNat jc)))

         (compat : ∀ (m0 : nat) (mc : m0 < (S n)) (n0 : nat) (nc : n0 < (S n)),
             m0 ≢ n0
             → Disjoint (FinNat o)
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat mc)))
                        (@out_index_set Monoid_RthetaFlags i o _ (op_family (mkFinNat nc))))

         (m m0 m1 : mem_block)
         (l: list mem_block)
         (A : Apply_mem_Family
                (get_family_mem_op
                   (shrink_m_op_family_up mop_family)) m
                ≡ Some l)

         (t:nat)
         (H0: get_family_mem_op mop_family _ (Nat.lt_0_succ n) m ≡ Some m0)

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
          (m2:=m).
      -
        eapply cast_SH_MSH_Operator_compat.
        eapply Meq.
      -
        intros m0' mc' n0' nc' H.
        assert(mc'': m0' < S n ) by lia.
        assert(nc'': n0' < S n ) by lia.
        specialize (compat m0' mc'' n0' nc'' H).
        erewrite <- cast_out_index_set_eq.
        erewrite <- cast_out_index_set_eq.
        apply compat.
        eapply Meq.
        eapply Meq.
      -
        rewrite <- A.
        unfold shrink_m_op_family_up, shrink_op_family_up, shrink_op_family_facts_up,
        shrink_m_op_family, shrink_op_family, shrink_op_family_facts,
        shrink_op_family_up_n, shrink_op_family_facts_up_n, shrink_m_op_family_up_n.
        clear.
        f_equiv.
        unfold get_family_mem_op.
        extensionality j.
        extensionality jc.
        apply cast_mem_op_eq.
        lia.
      -
        lia.
      -
        rewrite <- H0.
        clear.
        unfold get_family_mem_op.
        apply equal_f.
        apply cast_mem_op_eq; auto.
      -
        assumption.

        Unshelve.
        apply Meq.
        lia.
    Qed.

    Lemma vector_val_index_set_Vconst_Empty
          {fm}
          {fml: @MonoidLaws RthetaFlags fm}
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
        rewrite Vbuild_Sn.
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
        unfold shrink_m_op_family_up_n in H0.
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
          (op_family := cast_op_family _ op_family E); eauto.
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

    Global Instance IUnion_SH_MSH_Operator_compat
           {i o k: nat}
           `{svalue: MonUnit CarrierA}
           `{dot: SgOp CarrierA}
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot svalue}
           (op_family: @SHOperatorFamily Monoid_RthetaFlags i o k svalue)
           (mop_family: MSHOperatorFamily)
           (Meq: forall j (jc:j<k), SH_MSH_Operator_compat
                                           (op_family (mkFinNat jc))
                                           (mop_family (mkFinNat jc)))
           (compat: forall m (mc:m<k) n (nc:n<k), m ≢ n -> Disjoint _
                                                              (out_index_set _ (op_family (mkFinNat mc)))
                                                              (out_index_set _ (op_family (mkFinNat nc))))
           `{scompat: BFixpoint svalue dot}
      :  SH_MSH_Operator_compat
           (IUnion dot op_family (pdot:=pdot))
           (MSHIUnion mop_family).
    Proof.
      split.
      -
        apply IUnion_Facts.
        apply Meq.
        apply compat.
      -
        apply IUnion_MFacts.
        +
          intros j jc.
          specialize (compat j jc).
          apply Meq.
        +
          intros m mc n nc H.
          specialize (compat m mc n nc H).
          eapply Disjoint_mor.
          apply Meq.
          apply Meq.
          apply compat.
      -
        simpl.
        apply SH_MSH_family_in_pattern_compat.
        assumption.
      -
        apply SH_MSH_family_out_pattern_compat.
        assumption.
      -
        (* mem_vec_preservation *)
        intros x H.
        rename k into n.
        unfold MSHIUnion, IUnion, IUnion_mem, Diamond.
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
            rewrite Vbuild_Sn in A1.
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

            specialize (IHn
                          (shrink_op_family_up _ op_family)
                          (shrink_m_op_family_up mop_family)
                          (shrink_SH_MSH_Operator_compat_family_up Meq)
                          compat'
                          P
                          v l
                          A V
                       ).

            unfold MUnion in *.
            simpl.

            rewrite svector_to_mem_block_Vec2Union_mem_union
              with (a_zero:=svalue).
            --
              rewrite IHn; clear IHn.
              apply mem_union_proper; auto.
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
              unshelve eapply IUnion_vector_val_index_set_1_step_disjoint; eauto.
              apply Meq.
            --
              typeclasses eauto.
            --
              apply Vec2Union_fold_zeros with
                  (op_family0:=shrink_op_family_up _ op_family)
                  (x0:=x); auto.
              unshelve eapply (shrink_op_family_facts_up _ _ _).
              apply Meq.
            --
              apply Vforall_nth_intro.
              clear P.
              intros t tc P.
              eapply svalue_at_sparse.
              eapply sparse_outputs_not_in_out_set; eauto.
              apply Meq.
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
          apply Meq.
          intros j jc H0.
          apply svector_to_mem_block_In with (jc0:=jc).
          apply H.
          eapply family_in_set_includes_members.
          apply Meq.
          apply H0.
    Qed.

  End MonoidSpecific.

End OperatorPairwiseProofs.
