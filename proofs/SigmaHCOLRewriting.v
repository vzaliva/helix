
Global Generalizable All Variables.

Require Import VecUtil.
Require Import Spiral.
Require Import Rtheta.
Require Import VecSetoid.
Require Import SVector.
Require Import HCOL.
Require Import THCOL.
Require Import SigmaHCOL.
Require Import TSigmaHCOL.
Require Import IndexFunctions.
Require Import MonoidalRestriction.
Require Import VecPermutation.

Require Import Coq.Arith.Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.
Require Import Omega.

Require Import SpiralTactics.

(* CoRN Math-classes *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.setoids.

(* ExtLib *)
Require Import ExtLib.Structures.Monoid.
Import Monoid.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Local Open Scope vector_scope.
Local Open Scope nat_scope.

Section SigmaHCOLHelperLemmas.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Lemma Gather'_composition
        {i o t: nat}
        (f: index_map o t)
        (g: index_map t i):
    Gather' fm f ∘ Gather' fm g = Gather' fm (index_map_compose g f).
  Proof.
    apply ext_equiv_applied_equiv.
    -
      split; try apply vec_Setoid.
      apply compose_proper with (RA:=equiv) (RB:=equiv);
        apply Gather'_proper.
    -
      split; try apply vec_Setoid.
      apply Gather'_proper.
    -
      intros v.
      unfold compose.
      vec_index_equiv j jp.

      unfold Gather'.
      rewrite 2!Vbuild_nth.
      unfold VnthIndexMapped.
      destruct f as [f fspec].
      destruct g as [g gspec].
      unfold index_map_compose, compose.
      simpl.
      rewrite Vbuild_nth.
      reflexivity.
  Qed.

  Lemma Scatter'_composition
        {i o t: nat}
        (f: index_map i t)
        (g: index_map t o)
        {f_inj: index_map_injective f}
        {g_inj: index_map_injective g}:
    Scatter' fm g (f_inj:=g_inj) ∘ Scatter' fm f (f_inj:=f_inj)
    = Scatter' fm (index_map_compose g f) (f_inj:=index_map_compose_injective g f g_inj f_inj).
  Proof.
    apply ext_equiv_applied_equiv.
    -
      split; try apply vec_Setoid.
      apply compose_proper with (RA:=equiv) (RB:=equiv);
        apply Scatter'_proper.
    -
      split; try apply vec_Setoid.
      apply Scatter'_proper.
    -
      intros v.
      unfold compose.
      vec_index_equiv j jp.
      unfold Scatter'.
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
      liftM_HOperator fm (op1 ∘ op2) =
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
      + apply liftM_HOperator'_proper.
        apply compose_HOperator.
    -
      split.
      + apply vec_Setoid.
      + apply vec_Setoid.
      + apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply liftM_HOperator'_proper; assumption.
        apply liftM_HOperator'_proper; assumption.
    -
      intros v.
      unfold liftM_HOperator', compose.
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

End SigmaHCOLHelperLemmas.



Section SigmaHCOLExpansionRules.
  Section Value_Correctness.

    Lemma SHBinOp_equiv_lifted_HBinOp
          {o}
          (f: nat -> CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    :
      SafeCast (@SHBinOp o f pF) = @liftM_HOperator Monoid_RthetaFlags (o+o) o (@HBinOp o f pF) _ .
    Proof.
      apply ext_equiv_applied_equiv.
      -
        simpl.
        split.
        + apply vec_Setoid.
        + apply vec_Setoid.
        + apply SafeCast'_proper;
            apply SHBinOp'_proper.
      -
        simpl.
        split.
        + apply vec_Setoid.
        + apply vec_Setoid.
        + apply liftM_HOperator'_proper.
          apply HBinOp_HOperator.
      -
        intros x.
        simpl.

        vec_index_equiv j jc.

        unfold SafeCast', rsvector2rvector, rvector2rsvector, compose.
        rewrite Vnth_map.


        assert(jc1: j<o+o) by omega.
        assert(jc2: j+o<o+o) by omega.
        rewrite SHBinOp'_nth with (fm:=Monoid_RthetaSafeFlags)
                                  (jc1:=jc1) (jc2:=jc2).


        unfold liftM_HOperator'.
        unfold compose.
        unfold sparsify.
        repeat rewrite Vnth_map.
        rewrite (@HBinOp_nth o f pF _ j jc jc1 jc2).
        unfold densify; rewrite 2!Vnth_map.

        rewrite <- evalWriter_Rtheta_liftM2 by apply fml.
        rewrite mkValue_evalWriter.
        apply RStheta2Rtheta_liftM2.
        apply pF.
        reflexivity.
    Qed.


    Lemma h_j_1_family_injective {n}:
      index_map_family_injective
        (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j n 1 jc)))).
    Proof.
      unfold index_map_family_injective.
      crush.
    Qed.


    (* TODO: should be deriavale from 'h_j_1_family_injective' and 'index_map_family_member_injective' *)
    Lemma h_j_1_family_member_injective {n}:
      forall t (tc:t<n),
        @index_map_injective 1 n
                             ((fun (j:nat) (jc:j<n) =>
                                 @h_index_map 1 n j 1 (ScatH_1_to_n_range_bound j n (S O) jc)) t tc).
    Proof.
      unfold index_map_injective.
      crush.
    Qed.

    Lemma U_SAG2:
      ∀ (n : nat) (x : rvector (n + n))
        (f: nat -> CarrierA -> CarrierA -> CarrierA)
        `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (k : nat) (kp : k < n),

        Vnth
          (SumUnion Monoid_RthetaFlags
                    (Vbuild
                       (λ (j : nat) (jc : j < n),
                        Scatter' Monoid_RthetaFlags (i:=1)
                                 (h_index_map j 1 (range_bound:=ScatH_1_to_n_range_bound j n 1 jc))
                                 (f_inj :=
                                    @index_map_family_member_injective 1 n n (IndexMapFamily 1 n n
                                                                                             (fun (j0 : nat) (jc0 : j0<n) =>
                                                                                                @h_index_map 1 n j0 1
                                                                                                             (ScatH_1_to_n_range_bound j0 n 1 jc0))) (@h_j_1_family_injective n) j jc)
                                 (SafeCast' (SHBinOp' Monoid_RthetaSafeFlags (SwapIndex2 j f))
                                            (Gather' Monoid_RthetaFlags (@h_index_map (1+1) (n+n) j n (GathH_jn_domain_bound j n jc)) x))))) kp
        = Vnth ((SHBinOp' _ (o:=n) f) x) kp.
    Proof.
      intros n x f f_mor k kp.

      remember (fun i jc => Scatter' _  _ _) as bf.


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
        unfold Scatter'.
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
         unfold Scatter'.
         rewrite Vbuild_nth.
         break_match.
         +
           clear L3pre.

           unfold SafeCast', rsvector2rvector, rvector2rsvector, compose.
           rewrite Vnth_map.

           unshelve erewrite SHBinOp'_nth with (fm:=Monoid_RthetaSafeFlags).
           crush.
           destruct (Nat.eq_dec (k + 0) k).
           auto.
           tauto.

           crush.
           destruct (Nat.eq_dec (k + 0) k).
           auto.
           tauto.

           rewrite 2!Vnth_map.
           unshelve erewrite SHBinOp'_nth.
           crush.
           crush.


           rewrite 2!Gather'_spec with (fm:=Monoid_RthetaFlags).
           unfold VnthIndexMapped.

           unfold SwapIndex2, inverse_index_f, build_inverse_index_map, const.
           unfold h_index_map.

           Opaque Rtheta2RStheta Monad.liftM2.
           unfold IndexFunctions.h_index_map_obligation_1.
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
            (f: nat -> CarrierA -> CarrierA -> CarrierA)
            `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      :
        SafeCast (SHBinOp f)
        =
        USparseEmbedding (f_inj:=h_j_1_family_injective)
                         (mkSHOperatorFamily Monoid_RthetaFlags _ _ _
                                             (fun j _ => SafeCast (SHBinOp (SwapIndex2 j f))))
                         (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j n 1 jc))))
                         (IndexMapFamily _ _ n (fun j jc => h_index_map j n (range_bound:=GathH_jn_domain_bound j n jc))).
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
        setoid_rewrite SHBinOp'_nth with (jc1:=ip1) (jc2:=ip2).


        unfold Diamond'.
        rewrite AbsorbMUnion'Index_Vmap.
        (* OR rewrite AbsorbMUnion'Index_Vbuild.*)
        unfold Apply_Family'.
        rewrite Vmap_Vbuild.

        (* Not sure below here *)
        unfold SparseEmbedding, Diamond', Apply_Family', MUnion'.
        unfold SHCompose, compose, get_family_op.
        simpl.

        rewrite <- AbsorbISumUnionIndex_Vbuild.

        setoid_rewrite U_SAG2.
        setoid_rewrite SHBinOp'_nth with (jc:=ip) (jc1:=ip1) (jc2:=ip2).

        repeat rewrite Vnth_map.
        apply RStheta2Rtheta_liftM2.
        apply f_mor.
        reflexivity.
    Qed.

    (*
   ApplyFunc(SUMUnion, List([1..Length(ch)], i->OLCompose(
            ScatHUnion(Rows(o), Rows(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[1])), 1),
            self(ch[i], opts),
            GathH(Cols(o), Cols(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[2])), 1))))),
     *)
    (* TODO: perhaps could be generalized for generic operation, not just plus *)
    Theorem expand_HTDirectSum
            {fm: Monoid RthetaFlags}
            {fml: @MonoidLaws RthetaFlags RthetaFlags_type fm}
            {i1 o1 i2 o2}
            (f: avector i1 -> avector o1)
            (g: avector i2 -> avector o2)
            `{hop1: !HOperator f}
            `{hop2: !HOperator g}
      :
        liftM_HOperator fm (HTDirectSum f g)
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
        unfold liftM_HOperator' at 1.
        unfold compose.
        unfold HTDirectSum, HCross, THCOLImpl.Cross, compose,
        HTSUMUnion', pair2vector.

        break_let. break_let.
        rename t1 into x0, t2 into x1.
        tuple_inversion.
        symmetry.

        assert(LS: (@Scatter' fm o1 (Init.Nat.add o1 o2)
                              (@h_index_map o1 (Init.Nat.add o1 o2) O (S O) (h_bound_first_half o1 o2))
                              (@h_index_map_is_injective o1 (Init.Nat.add o1 o2) O
                                                         (S O) (h_bound_first_half o1 o2) (@ScatH_stride1_constr o1 (S (S O))))
                              (@liftM_HOperator' fm i1 o1 f
                                                 (@Gather' fm (Init.Nat.add i1 i2) i1
                                                           (@h_index_map i1 (Init.Nat.add i1 i2) O (S O) (h_bound_first_half i1 i2))
                                                           x))) = Vapp (sparsify fm (f x0)) (szero_svector fm o2)).
        {
          setoid_replace (@Gather' fm (Init.Nat.add i1 i2) i1
                                   (@h_index_map i1 (Init.Nat.add i1 i2) O (S O) (h_bound_first_half i1 i2))
                                   x) with (sparsify fm x0).
          -
            vec_index_equiv i ip.
            unfold Scatter'.
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
                unfold liftM_HOperator', sparsify, compose.
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
            unfold Gather'.
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

        assert(RS: (@Scatter' fm o2 (Init.Nat.add o1 o2)
                              (@h_index_map o2 (Init.Nat.add o1 o2) o1 (S O) (h_bound_second_half o1 o2))
                              (@h_index_map_is_injective o2 (Init.Nat.add o1 o2) o1
                                                         (S O) (h_bound_second_half o1 o2) (@ScatH_stride1_constr o2 (S (S O))))
                              (@liftM_HOperator' fm i2 o2 g
                                                 (@Gather' fm (Init.Nat.add i1 i2) i2
                                                           (@h_index_map i2 (Init.Nat.add i1 i2) i1 (S O)
                                                                         (h_bound_second_half i1 i2)) x))) = Vapp (szero_svector fm o1) (sparsify fm (g x1))).
        {
          setoid_replace (@Gather' fm (Init.Nat.add i1 i2) i2
                                   (@h_index_map i2 (Init.Nat.add i1 i2) i1 (S O)
                                                 (h_bound_second_half i1 i2)) x) with (sparsify fm x1).
          -
            unfold Scatter'.
            vec_index_equiv i ip.
            rewrite Vbuild_nth.
            rewrite Vnth_app.
            break_match.
            + (* Second half of x, which is gx0 *)
              break_match.
              * simpl.
                unfold liftM_HOperator', sparsify, compose.
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
          - unfold Gather'.
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
        setoid_replace (Vmap2 (Union _ plus) (sparsify _ (f x0)) (szero_svector fm o1)) with (sparsify fm (f x0)).
        setoid_replace (Vmap2 (Union _ plus) (szero_svector fm o2) (sparsify fm (g x1))) with (sparsify fm (g x1)).
        unfold sparsify.
        rewrite Vmap_app.
        reflexivity.
        apply Vec2Union_szero_svector_l.
        apply Vec2Union_szero_svector_r.
    Qed.

  End Value_Correctness.

  Section Structural_Correctness.

    (* TODO *)

  End Structural_Correctness.


End SigmaHCOLExpansionRules.

Section SigmaHCOLRewritingRules.
  Section Value_Correctness.

    Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

    Lemma rewrite_PointWise_ISumUnion
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
          (pf: { j | j<o} -> CarrierA -> CarrierA)
          `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}
          (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero) (* function with the fixed point 0 *)
          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family zero)
      :
        (@SHPointwise _ o pf pf_mor) ⊚ (@ISumUnion i o n op_family)
        =
        (@ISumUnion i o n
                    (SHOperatorFamilyCompose _
                                             (@SHPointwise _ o pf pf_mor)
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
        apply SHPointwise'_proper.
        apply Diamond'_proper.
        + apply CarrierAPlus_proper.
        + reflexivity.
        + intros k kc.
          apply op_proper.
      -
        (* RHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply Diamond'_proper.
        + apply CarrierAPlus_proper.
        + reflexivity.
        + intros k kc.
          apply op_proper.
      -
        intros x.
        unfold Diamond'.
        unfold compose.
        vec_index_equiv j jc. (* fix column *)
        setoid_rewrite SHPointwise'_nth; try apply MonoidLaws_RthetaFlags.

        unfold Apply_Family'.
        rewrite 2!AbsorbMUnion'Index_Vbuild.

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
                                     (@get_family_op Monoid_RthetaFlags i o n op_family z zi x) j jc))).
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
            assert(H: Vbuild (λ (i0 : nat) (ic : i0 < n), Vnth (SHPointwise' Monoid_RthetaFlags pf (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family i0 ic) x)) jc) =
                      Vbuild (λ (i0 : nat) (ic : i0 < n), mkValue (pf (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family i0 ic) x) jc))))).
            {
              vec_index_equiv k kc.
              rewrite 2!Vbuild_nth.
              rewrite SHPointwise'_nth by apply MonoidLaws_RthetaFlags.
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
                               (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family z zi) x)
                               jc))) = szero_svector Monoid_RthetaFlags n).
            {
              unfold szero_svector.
              vec_index_equiv k kc.
              rewrite Vnth_map.
              rewrite Vnth_const.
              rewrite Vbuild_nth.
              specialize (Uzeros k kc).
              setoid_replace (Vnth
                                (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family k kc) x)
                                jc) with (@mkSZero Monoid_RthetaFlags).
              -
                rewrite evalWriter_Rtheta_SZero.
                rewrite pfzn.
                unfold_Rtheta_equiv.
                rewrite  evalWriter_Rtheta_SZero.
                reflexivity.
              -
                unfold compose, Is_ValZero in Uzeros.
                unfold_Rtheta_equiv.
                rewrite evalWriter_Rtheta_SZero.
                unfold equiv.
                unfold Rtheta.
                unfold get_family_op in Uzeros.
                generalize dependent (Vnth (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family k kc) x) jc).
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
          (* rewrite Is_ValZero_not_not in Uone. *)
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
              rewrite SHPointwise'_nth by apply MonoidLaws_RthetaFlags.

              unfold VAllButOne in Uone.
              specialize (Uone t tc H).
              rewrite Vbuild_nth in Uone.

              apply not_not_on_decidable in Uone.
              symmetry in Uone.
              crush.
              reflexivity.
            }

            rewrite UnionFold_VallButOne_zero with (kc:=kc).
            ** subst vr.
               rewrite Vbuild_nth.
               rewrite SHPointwise'_nth.
               reflexivity.
            ** apply H.
          *
            apply VallButOneSimpl with (P1:=Is_ValZero) in Uone.
            apply Uone.

            intros x0 H.
            apply not_not_on_decidable in H.
            unfold Is_ValZero, Is_ValX.
            symmetry.
            apply H.
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
          (Vfold_left_rev (Union Monoid_RthetaSafeFlags f) (mkStruct initial) v) =
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

        unfold Union, Monad.liftM2, mkValue.
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
          unfold Union.
          unfold_Rtheta_equiv.
          rewrite evalWriter_Rtheta_liftM2.
          destruct(CarrierAequivdec (WriterMonadNoT.evalWriter h) uf_zero) as [E | NE].
          *
            rewrite E.
            apply f_left_id.
          *
            crush.
    Qed.

    (* Basically states that 'Diamon' applied to a family which guarantees
       single-non zero value per row dows not depend on the function implementation *)
    Lemma Diamond'_f_subst
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)

          (* Common unit for both monoids *)
          `{uf_zero: MonUnit CarrierA}

          (* 1st Monoid. Used in reduction *)
          `{f: SgOp CarrierA}
          `{f_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ f uf_zero}
          (* 2nd Monoid. Used in IUnion *)
          `{u: SgOp CarrierA}
          `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}
      :
        Apply_Family_Single_NonUnit_Per_Row _ op_family uf_zero
        ->
        Diamond' f uf_zero (get_family_op Monoid_RthetaFlags op_family) =
        Diamond' u uf_zero (get_family_op Monoid_RthetaFlags op_family).
    Proof.
      intros Uz.
      apply ext_equiv_applied_equiv; try (split; typeclasses eauto).
      intros x.
      unfold Diamond'.

      vec_index_equiv j jc.
      unfold Apply_Family'.
      rewrite 2!AbsorbMUnion'Index_Vbuild.

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
            unfold Union.
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
                apply evalWriter_mkStruct.
              -
                crush.
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

      Lemma Diamond'_f_subst_under_P
            {i o n}
            (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)

            (* Common unit for both monoids *)
            `{uf_zero: MonUnit CarrierA}

            `{f: SgOp CarrierA}

            (* Monoid on restriction on f *)
            {P: SgPred CarrierA}
            `{f_mon: @RMonoid _ _ f uf_zero P}

            (* 2nd Monoid *)
            `{u: SgOp CarrierA}
            `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}

            (Upoz: Apply_Family_Vforall_P _ (liftRthetaP P) op_family)
            (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family uf_zero)
        :
          Diamond' f uf_zero (get_family_op Monoid_RthetaFlags op_family) =
          Diamond' u uf_zero (get_family_op Monoid_RthetaFlags op_family).
      Proof.

        assert(f_mor : Proper (equiv ==> equiv ==> equiv) f).
        {
          destruct f_mon.
          apply rsg_op_proper.
        }

        apply ext_equiv_applied_equiv; try (split; typeclasses eauto).
        intros x.
        unfold Diamond'.

        vec_index_equiv j jc.
        unfold Apply_Family'.
        rewrite 2!AbsorbMUnion'Index_Vbuild.

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
          apply evalWriter_mkStruct.
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
            rewrite Vcons_to_Vcons_reord.
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
            rewrite Vcons_to_Vcons_reord.
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
      -
        clear tndm.
        induction n.
        +
          reflexivity.
        +

          setoid_rewrite Vbuild_cons at 2.
          rewrite Vfold_right_cons.

          pose (gen' := (fun p pc => gen (S p) (lt_n_S pc))).

          assert(tmn' : forall t : nat, t < S m * n → t mod n < n).
          {
            intros t H.
            apply modulo_smaller_than_devisor.
            crush.
          }

          specialize (IHn gen' tmn').

          replace (fun (i : nat) (ip : i < n) =>
                     Vhead
                       (gen (S i mod S n)
                            (tmn (S i) (Nat.lt_lt_add_r (S i) (S n) (m * S n) (lt_n_S ip)))))
            with
              (fun (t : nat) (tc : t < n) =>
                 Vhead (gen' (t mod n) (tmn' t (Nat.lt_lt_add_r t n (m * n) tc)))).
          *
            rewrite <- IHn.
            clear IHn tmn'.
            simpl.
            replace (gen 0 (VecUtil.Vbuild_spec_obligation_4 gen eq_refl))
              with
                (gen (n - n) (tmn 0 (Nat.lt_lt_add_r 0 (S n) (m * S n) (Nat.lt_0_succ n)))).
            replace (fun v1 v2 : vector A (S m) =>
                       Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2)))
              with (fun v1 v2 : vector A (S m) =>
                      Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2))).

            replace (` (Vbuild_spec (fun (i : nat) (ip : i < n) => gen (S i) (VecUtil.Vbuild_spec_obligation_3 gen eq_refl ip))))
              with
                (Vbuild gen').
            reflexivity.
            --
              apply Veq_nth.
              intros i ip.
              rewrite Vbuild_nth.
              destruct (Vbuild_spec _).
              simpl.
              rewrite e.
              unfold gen'.
              apply f_equal, le_unique.
            --
              reflexivity.
            --
              generalize (tmn 0 (Nat.lt_lt_add_r 0 (S n) (m * S n) (Nat.lt_0_succ n))) as ic0.
              generalize (VecUtil.Vbuild_spec_obligation_4 gen eq_refl) as ic1.
              intros ic0 ic1.
              clear gen' tmn f z.
              revert ic0 ic1; simpl; rewrite Nat.sub_diag; intros ic0 ic1.
              apply f_equal, le_unique.
          *
            extensionality t.
            extensionality tc.

            generalize (tmn' t (Nat.lt_lt_add_r t n (m * n) tc)).
            generalize (tmn (S t) (Nat.lt_lt_add_r (S t) (S n) (m * S n) (lt_n_S tc))).
            intros i0 i1.

            remember (S t mod S n) as Q.
            rewrite Nat.mod_small in HeqQ by lia.
            subst Q.

            remember (t mod n) as Q.
            rewrite Nat.mod_small in HeqQ by auto.
            subst Q.

            unfold gen'.
            apply f_equal, f_equal, le_unique.
      -
        extensionality t.
        extensionality tc.
        generalize (tndm t (Nat.lt_lt_add_r t n (m * n) tc)) as zc.
        intros zc.
        remember (t/n) as Q.
        rewrite Nat.div_small in HeqQ by apply tc.
        subst Q.
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
        setoid_rewrite Vbuild_cons at 2.
        rewrite Vfold_right_cons.
        replace (Vbuild (λ (i : nat) (ip : i < n), Vtail (gen (S i) (lt_n_S ip))))
          with (Vbuild (λ (p : nat) (pc : p < n), Vtail (gen' p pc))) by reflexivity.

        rewrite <- IHn. clear IHn.
        subst gen'.

        setoid_rewrite Vbuild_cons.
        rewrite Vfold_right_cons.

        apply Veq_nth.
        intros i ip.
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
          rewrite Vbuild_cons.

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
                  assert(⟦ t ⟧ x ≢ 0).
                  {
                    apply NK; auto.
                    apply Nat.le_neq; auto.
                  }

                  assert(⟦ t ⟧ y ≢ 0).
                  {
                    apply NK; auto.
                    apply Nat.le_neq; auto.
                  }

                  destruct (⟦ t ⟧ x); try congruence.
                  destruct (⟦ t ⟧ y); try congruence.
                  rewrite <- 2!pred_Sn in H.
                  auto.
                +
                  (* impossible case: x,y on different sides of k *)
                  clear E0 E1 h_func h_spec IHn P' f' t'.
                  generalize dependent k.
                  intros k L K NK l n1.

                  assert(⟦ t ⟧ x ≢ 0).
                  {
                    apply NK; auto.
                    apply Nat.le_neq; auto.
                  }

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

                  assert(⟦ t ⟧ y ≢ 0).
                  {
                    apply NK; auto.
                    apply Nat.le_neq; auto.
                  }

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

            apply Veq_nth.
            intros i ip.
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

    Lemma Vold_right_sig_wrap_equiv
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
          {As: @Setoid A Ae}
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
          `{As: Setoid A}
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
      rewrite Vold_right_sig_wrap_equiv with (P0:=P) (Pz:=rmonoid_unit_P _) (f0:=f) (f_P_closed:=rmonoid_plus_closed _) (P3:=P1) by apply rsg_op_proper.
      rewrite Vfold_right_to_Vfold_right_reord.
      rewrite Vold_right_sig_wrap_equiv with (P0:=P) (Pz:=rmonoid_unit_P _) (f0:=f) (f_P_closed:=rmonoid_plus_closed _) (P3:=P2) by apply rsg_op_proper.
      rewrite <- Vfold_right_to_Vfold_right_reord.

      f_equiv.

      apply Vfold_VPermutation.
      apply CA.
      apply VPermutation_Vsig_of_forall, V.
    Qed.

    (* In SPIRAL it is called [Reduction_ISumReduction] *)
    Lemma rewrite_Reduction_IReduction
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)

          (* Common unit for both monoids *)
          `{uf_zero: MonUnit CarrierA}

          (* 1st Monoid. Used in reduction *)
          `{f: SgOp CarrierA}

          (* Monoid on restriction on f *)
          `{P: SgPred CarrierA}
          `{f_mon: @CommutativeRMonoid _ _ f uf_zero P}

          (* 2nd Monoid. Used in IUnion *)
          `{u: SgOp CarrierA}
          `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}

          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family uf_zero)
          (Upoz: Apply_Family_Vforall_P _ (liftRthetaP P) op_family)
      :

        (liftM_HOperator Monoid_RthetaFlags (@HReduction _ f _ uf_zero))
          ⊚ (@IUnion i o n u _ uf_zero op_family)
        =
        SafeCast (IReduction f uf_zero
                             (UnSafeFamilyCast
                                (SHOperatorFamilyCompose _ (liftM_HOperator Monoid_RthetaFlags (@HReduction _ f _ uf_zero)) op_family))).
    Proof.
      (*
      assert(f_mor : Proper (equiv ==> equiv ==> equiv) f)
        by apply rsg_op_proper.
      assert(u_mor : Proper (equiv ==> equiv ==> equiv) u)
        by apply sg_op_proper.
       *)
      unfold SHOperatorFamilyCompose, SHCompose.
      unfold equiv, SHOperator_equiv, SHCompose; simpl.
      unfold UnSafeFamilyCast, get_family_op.
      simpl.
      (* Noramlized form. Diamond' all around *)

      (* To use Diamond'_f_subst_under_P we need to convert body_f back to operator family *)
      replace (λ (j : nat) (jc : j < n),
               op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family j jc)) with  (get_family_op _ op_family) by reflexivity.

      rewrite <- Diamond'_f_subst_under_P with (f0:=f) (u0:=u) (P0:=P); auto ; try apply f_mon.
      clear u u_mon.  (* No more 'u' *)
      clear Uz. (* Single non-unit per row constaint no longer needed *)

      apply ext_equiv_applied_equiv.
      -
        (* LHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply liftM_HOperator'_proper.
        apply HReduction_HOperator.
        apply Diamond'_proper.
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
        apply Diamond'_proper.
        + apply f_mon.
        + reflexivity.
        + intros k kc.
          apply UnSafeCast'_proper.
          apply compose_proper with (RA:=equiv) (RB:=equiv).
          *
            apply liftM_HOperator'_proper.
            apply HReduction_HOperator.
          *
            apply op_proper.
      -
        intros x.

        vec_index_equiv j jc.

        unfold SafeCast', rsvector2rvector, compose.
        unfold liftM_HOperator', compose, sparsify.
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

        unfold Diamond'.
        unfold Apply_Family'.
        unfold RStheta.
        rewrite AbsorbMUnion'Index_Vbuild.
        simpl.

        unfold UnionFold.
        unfold MUnion'.

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
        unfold Union.

        (* Get rid of [get_family_op] *)
        unfold get_family_op in *.

        eta_reduce_all.

        (* 1. In LHS push [evalWriter] all the way down to [get_family_op] *)

        rewrite Vfold_right_to_Vfold_right_reord.
        rewrite eval_2D_Fold by apply f_mon.
        rewrite <- Vfold_right_to_Vfold_right_reord.

        rewrite Vmap_Vbuild.

        assert(Upoz': forall (j : nat) (jc : j < n), Vforall P
                                                      (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                            (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family j jc) x))).
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
                        (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family z zi) x))) with (Vbuild
                                                                                                              (λ (z : nat) (zi : z < n),
                                                                                                               (fun p pi =>
                                                                                                                  (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                                                                                        (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family p pi) x))) z zi)).

        change (Vbuild
                  (λ (z : nat) (zi : z < n),
                   Vfold_right f
                               (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                     (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family z zi) x))
                               uf_zero)) with (Vbuild
                                                 (λ (z : nat) (zi : z < n),
                                                  Vfold_right f
                                                              ((fun p pi =>
                                                                  (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                                        (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family p pi) x))) z zi)
                                                              uf_zero)).

        revert Upoz.

        change (∀ (j : nat) (jc : j < n), Vforall P
                                                (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                      (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family j jc) x))) with   (∀ (j : nat) (jc : j < n),
                                                                                                                                               Vforall P
                                                                                                                                                       ((fun p pi =>
                                                                                                                                                           (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                                                                                                                                                                 (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family p pi) x))) j jc)).

        generalize (fun p pi =>
                      (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
                            (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family p pi) x))) as gen.

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
              (rewrite Vbuild_cons in Heqlcols;
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
                apply Veq_nth.
                intros i ip.
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

          setoid_rewrite Vfold_right_to_Vfold_right_reord.
          rewrite (Vfold_right_left_rev_under_P (Vforall P (n:=m))).
          setoid_rewrite <- Vfold_right_to_Vfold_right_reord.

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
          clear z f P f_mon mat Mpoz.
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
          clear z f P f_mon mat Mpoz.
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
          clear z f P f_mon mat Mpoz lrm.
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
          clear z f P f_mon mat Mpoz lrm RLR.
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
          clear z f P f_mon mat Mpoz Heql Heqr.
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
          apply Veq_nth.
          intros i ip.
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
        @CommutativeRMonoid CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
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
    Lemma rewrite_Reduction_IReduction_max_plus
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family zero)
          (Upoz: Apply_Family_Vforall_P _ Is_NonNegative op_family)
      :
        (liftM_HOperator Monoid_RthetaFlags (@HReduction _ max _ zero))
          ⊚ (ISumUnion op_family)
        =
        SafeCast (IReduction max zero
                             (UnSafeFamilyCast
                                (SHOperatorFamilyCompose _ (liftM_HOperator Monoid_RthetaFlags (@HReduction _ max _ zero)) op_family))).
    Proof.
      unfold ISumUnion.

      (* TODO: see if I can get rid of proof_irreleance here *)
      replace (@sg_op_proper _ _ _ _) with (@rsg_op_proper CarrierA CarrierAe max zero NN
                                                           (@comrmonoid_rmon CarrierA CarrierAe max zero NN CommutativeRMonoid_max_NN)) by apply proof_irrelevance.

      replace CarrierAPlus_proper with (@sg_op_proper CarrierA CarrierAe CarrierAplus
                                                      (@monoid_semigroup CarrierA CarrierAe CarrierAplus zero
                                                                         (@commonoid_mon CarrierA CarrierAe CarrierAplus zero CommutativeMonoid_plus_zero))) by apply proof_irrelevance.

      eapply rewrite_Reduction_IReduction; auto.
    Qed.

    (* Variant of SPIRAL's `rewrite_ISumXXX_YYY` rule for [IReduction] and [GatH] *)
    Lemma rewrite_ISumXXX_YYY_IReduction_GathH
          {i0 i o n b s : nat}
          {db}
          (dot: CarrierA -> CarrierA -> CarrierA)
          `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
          (initial: CarrierA)
          (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
      :
        SHCompose Monoid_RthetaFlags
                  (SafeCast (IReduction dot initial op_family))
                  (@GathH Monoid_RthetaFlags i0 i b s db)
        =
        SafeCast
          (IReduction dot initial
                      (SHFamilyOperatorCompose Monoid_RthetaSafeFlags
                                               op_family
                                               (GathH Monoid_RthetaSafeFlags b s (domain_bound:=db))
          )).
    Proof.
      unfold IReduction, SafeCast, equiv, SHOperator_equiv, Diamond'.
      simpl.
      unfold SafeCast', compose.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite_clear E.
      f_equiv.
      unfold vec_Equiv; apply Vforall2_intro_nth; intros j jc; apply Vnth_arg_equiv; clear j jc.

      destruct op_family.
      induction n.
      -
        reflexivity.
      -
        unfold Apply_Family' in *.
        rewrite Vbuild_cons.
        rewrite MUnion'_cons.
        unfold get_family_op in *.
        simpl in *.
        erewrite IHn.

        rewrite Vbuild_cons.
        rewrite MUnion'_cons.
        unfold compose.
        simpl.
        f_equiv.
        apply pdot.
        f_equiv.

        unfold equiv, vec_Equiv; apply Vforall2_intro_nth; intros j jc.
        unfold rvector2rsvector.
        rewrite Vnth_map.

        rewrite Gather'_spec.
        unfold Rtheta; rewrite Gather'_spec.
        unfold VnthIndexMapped.
        rewrite Vnth_map.
        reflexivity.
    Qed.

    Lemma SHPointwise'_distr_over_Scatter'
          {fm : Monoid RthetaFlags}
          {o i : nat}
          (pf : CarrierA → CarrierA)
          (pf_mor : Proper (equiv ==> equiv) pf)
          (pfzn: pf zero = zero) (* function with the fixed point 0 *)
          (v : svector fm i)
          (f : index_map i o)
          (f_inj : index_map_injective f):
      SHPointwise' fm (IgnoreIndex pf) (Scatter' fm f v (f_inj:=f_inj)) =
      Scatter' fm f (SHPointwise' fm (IgnoreIndex pf) v) (f_inj:=f_inj).
    Proof.
      vec_index_equiv j jc.
      rewrite SHPointwise'_nth.
      unfold equiv, Rtheta'_equiv.
      rewrite evalWriter_mkValue.
      (* unfold IgnoreIndex, const. *)

      destruct (in_range_dec f j) as [R | NR].
      -
        (* `j` in dense position *)
        unfold Scatter'.
        simpl.
        rewrite 2!Vbuild_nth.
        break_match; auto.
        unfold IgnoreIndex, const.
        rewrite SHPointwise'_nth.
        rewrite evalWriter_mkValue.
        reflexivity.
      -
        (* `j` in sparse position *)
        remember (Scatter' fm f v (f_inj:=f_inj)) as s0.
        assert(VZ0: Is_ValZero (Vnth s0 jc)).
        {
          subst s0.
          apply Scatter'_Zero_at_sparse; assumption.
        }
        setoid_replace (WriterMonadNoT.evalWriter (Vnth s0 jc) ) with CarrierAz.
        Focus 2.
        rewrite Is_ValZero_to_mkSZero in VZ0.
        rewrite_clear VZ0.
        rewrite evalWriter_Rtheta_SZero.
        reflexivity.

        rewrite pfzn.
        remember (Scatter' fm f (SHPointwise' fm (IgnoreIndex pf) v)) as s1.
        assert(VZ1: Is_ValZero (Vnth s1 jc)).
        {
          subst s1.
          apply Scatter'_Zero_at_sparse; assumption.
        }
        setoid_replace (WriterMonadNoT.evalWriter (Vnth s1 jc) ) with CarrierAz.
        reflexivity.
        rewrite Is_ValZero_to_mkSZero in VZ1.
        rewrite_clear VZ1.
        rewrite evalWriter_Rtheta_SZero.
        reflexivity.
    Qed.

    Lemma rewrite_PointWise_ScatHUnion
          {fm: Monoid RthetaFlags}

          (* -- SE params -- *)
          {n i o ki ko}
          (* Kernel *)
          (kernel: @SHOperatorFamily fm ki ko n)
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
      unfold SHOperatorFamilyCompose, IReduction, SafeCast, equiv, SHOperatorFamily_equiv, SHOperator_equiv, Diamond'.
      intros j jc.
      simpl.
      unfold SHCompose, compose, equiv, ext_equiv.
      intros x y E.
      simpl.
      rewrite_clear E.
      apply SHPointwise'_distr_over_Scatter', pfzn.
    Qed.


    Lemma rewrite_Reduction_ScatHUnion
          {n m:nat}
          {fm: Monoid RthetaFlags}

          `{g: SgOp CarrierA}
          `{mzero: MonUnit CarrierA}
          `{P: SgPred CarrierA}
          `{g_mon: @CommutativeRMonoid _ _ g mzero P}
          (F: @SHOperator fm m 1)
          {f:index_map 1 n}
          {f_inj: index_map_injective f}
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
    Admitted.

    Lemma rewrite_SHCompose_IdOp
          {n m: nat}
          {fm}
          (in_out_set: FinNatSet.FinNatSet n)
          (F: @SHOperator fm n m)
      :
      SHCompose fm
                F
                (IdOp fm in_out_set)
      =
      F.
    Proof.
      unfold SHCompose, compose, equiv, SHOperator_equiv; simpl.
      f_equiv.
    Qed.

  End Value_Correctness.

End SigmaHCOLRewritingRules.
