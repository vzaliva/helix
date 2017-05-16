
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
  (*

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Lemma Gather_composition
        {i o t: nat}
        (f: index_map o t)
        (g: index_map t i):
    Gather fm f ∘ Gather fm g = Gather fm (index_map_compose g f).
  Proof.
    apply SHOperator_functional_extensionality.
    -
      apply SHOperator_compose.
      apply SHOperator_Gather.
      apply SHOperator_Gather.
    -
      apply SHOperator_Gather.
    -
      intros v.
      unfold compose.
      vec_index_equiv j jp.

      unfold Gather.
      rewrite 2!Vbuild_nth.
      unfold VnthIndexMapped.
      destruct f as [f fspec].
      destruct g as [g gspec].
      unfold index_map_compose, compose.
      simpl.
      rewrite Vbuild_nth.
      reflexivity.
  Qed.

  Lemma Scatter_composition
        {i o t: nat}
        (f: index_map i t)
        (g: index_map t o)
        {f_inj: index_map_injective f}
        {g_inj: index_map_injective g}:
    Scatter fm g (f_inj:=g_inj) ∘ Scatter fm f (f_inj:=f_inj)
    = Scatter fm (index_map_compose g f) (f_inj:=index_map_compose_injective g f g_inj f_inj).
  Proof.
    apply SHOperator_functional_extensionality.
    -
      apply SHOperator_compose.
      apply SHOperator_Scatter.
      apply SHOperator_Scatter.
    -
      apply SHOperator_Scatter.
    -
      intros v.
      unfold compose.
      vec_index_equiv j jp.
      unfold Scatter.
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

   *)

  Lemma LiftM_Hoperator_compose
        {fm: Monoid RthetaFlags}
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

  Lemma UnionFold_zero_structs
        {fm:Monoid RthetaFlags}
        (m : nat) (x : svector fm m):
    Vforall Is_ValZero x → Is_ValZero (UnionFold fm plus zero x).
  Proof.
    intros H.
    unfold UnionFold.
    induction x.
    -
      unfold Is_ValZero.
      unfold_Rtheta_equiv.
      reflexivity.
    - simpl in H. destruct H as [Hh Hx].
      Opaque Monad.ret.
      simpl.
      Transparent Monad.ret.
      rewrite Is_ValZero_to_mkSZero in Hh.
      rewrite Is_ValZero_to_mkSZero.
      rewrite Hh.
      rewrite Union_SZero_r.
      apply IHx, Hx.
  Qed.

  Lemma UnionFold_VallButOne_zero
        {fm:Monoid RthetaFlags}:
    ∀ {n : nat} (v : svector fm n) {k : nat} (kc : k < n),
      VAllButOne k kc (Is_ValZero) v → UnionFold fm plus zero v = Vnth v kc.
  Proof.
    intros n v i ic U.

    dependent induction n.
    - crush.
    -
      dep_destruct v.
      destruct (eq_nat_dec i 0).
      +
        (* Case ("i=0"). *)
        rewrite Vnth_cons_head; try assumption.
        rewrite UnionFold_cons.
        assert(Vforall Is_ValZero x).
        {
          apply Vforall_nth_intro.
          intros j jp.
          assert(ipp:S j < S n) by lia.
          replace (Vnth x jp) with (Vnth (Vcons h x) ipp) by apply Vnth_Sn.
          apply U.
          omega.
        }

        assert(UZ: Is_ValZero (UnionFold fm plus zero x))
          by apply UnionFold_zero_structs, H.
        setoid_replace (UnionFold fm plus zero x) with (@mkSZero fm)
          by apply Is_ValZero_to_mkSZero, UZ.
        clear UZ.
        apply Union_SZero_l.
      +
        (* Case ("i!=0"). *)
        rewrite UnionFold_cons.
        assert (HS: Is_ValZero h).
        {
          cut (Is_ValZero (Vnth (Vcons h x) (zero_lt_Sn n))).
          rewrite Vnth_0.
          auto.
          apply U; auto.
        }

        destruct i; try congruence.
        simpl.
        generalize (lt_S_n ic).
        intros l.
        rewrite IHn with (ic:=l).

        setoid_replace h with (@mkSZero fm) by apply Is_ValZero_to_mkSZero, HS.
        apply Union_SZero_r.
        apply VAllButOne_Sn with (h0:=h) (ic0:=ic).
        apply U.
  Qed.



  (* Formerly Lemma3. Probably will be replaced by UnionFold_VallButOne *)
  Lemma SingleValueInZeros
        {fm:Monoid RthetaFlags}
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
           destruct (NPeano.Nat.eq_dec (k + 0) k).
           auto.
           tauto.

           crush.
           destruct (NPeano.Nat.eq_dec (k + 0) k).
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
            apply proof_irrelevance.
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

(*
Ltac HOperator_HBinOp_Type_Fix :=
  match goal with
  | [ |- (@HOperator ?i ?o (@HBinOp ?o _ _)) ] =>
    replace (@HOperator i) with (@HOperator (Init.Nat.add o o)) by apply eq_refl; apply HBinOp_HOperator
  end.

Hint Extern 0 (@HOperator _ ?o (@HBinOp ?o _ _)) => HOperator_HBinOp_Type_Fix : typeclass_instances.

Ltac SHOperator_SHBinOp_Type_Fix :=
  match goal with
  | [ |- (@SHOperator ?i ?o (@SHBinOp ?o _ _)) ] =>
    replace (@SHOperator i) with (@SHOperator (Init.Nat.add o o)) by apply eq_refl; apply SHOperator_SHBinOp
  end.

Hint Extern 0 (@SHOperator _ ?o (@SHBinOp ?o _ _)) => SHOperator_SHBinOp_Type_Fix : typeclass_instances.
 *)

(* Hint Extern 0 (@Proper _ _ (compose)) => apply compose_proper with (RA:=equiv) (RB:=equiv) : typeclass_instances.
 *)

(*
Ltac HOperator_HPrepend_Type_Fix :=
  match goal with
  | [ |- (@HOperator ?i ?o (@HPrepend ?n ?i ?a)) ] =>
    replace (@HOperator i o) with (@HOperator i (Init.Nat.add n i)) by apply eq_refl; apply HPrepend_HOperator
  end.

Hint Extern 0 (@HOperator ?i _ (@HPrepend _ ?i _)) => HOperator_HPrepend_Type_Fix : typeclass_instances.
 *)

Section SigmaHCOLRewritingRules.
  Section Value_Correctness.

    (*
    Global Instance Apply_Family_Pointwise_compose_Single_NonZero_Per_Row
           {fm: Monoid RthetaFlags}
           {fml: @MonoidLaws RthetaFlags RthetaFlags_type fm}
           {i o n}
           (op_family: forall k, (k<n) -> svector fm i -> svector fm o)
           `{Koperator: forall k (kc: k<n), @SHOperator fm i o (op_family k kc)}
           `{Uf: !Apply_Family_Single_NonZero_Per_Row fm op_family}
           (pf: { j | j<o} -> CarrierA -> CarrierA)
           (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero)
           `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}
    :
      Apply_Family_Single_NonZero_Per_Row fm
                                          (fun j jc => SHPointwise fm pf ∘ op_family j jc).
    Proof.
      unfold Apply_Family_Single_NonZero_Per_Row.
      intros x.
      apply Vforall_nth_intro.
      intros j jc.
      unfold Vunique.
      intros i0 ic0 i1 ic1.
      unfold transpose.
      rewrite Vbuild_nth.
      unfold row.
      rewrite 2!Vnth_map.
      unfold Apply_Family.
      rewrite 2!Vbuild_nth.
      unfold Vnth_aux.
      unfold compose.
      rewrite 2!SHPointwise_nth; try apply fml.

      unfold Apply_Family_Single_NonZero_Per_Row in Uf.
      specialize (Uf x).
      apply Vforall_nth with (ip:=jc) in Uf.
      unfold Vunique in Uf.
      specialize (Uf i0 ic0 i1 ic1).

      unfold transpose, Apply_Family, compose, row in Uf.
      rewrite Vbuild_nth in Uf.
      rewrite 2!Vnth_map in Uf.
      unfold Vnth_aux in Uf.
      rewrite 2!Vbuild_nth in Uf.

      generalize dependent (Vnth (op_family i0 ic0 x) jc).
      generalize dependent (Vnth (op_family i1 ic1 x) jc).
      intros x0 x1 Uf. clear x.
      intros [H0 H1].
      apply Uf. clear Uf.

      split.
      + contradict H0.
        rewrite Is_ValZero_to_mkSZero in H0.
        rewrite_clear H0.
        rewrite evalWriter_Rtheta_SZero.
        rewrite pfzn.
        unfold Is_ValZero.
        reflexivity.
      + contradict H1.
        rewrite Is_ValZero_to_mkSZero in H1.
        rewrite_clear H1.
        rewrite evalWriter_Rtheta_SZero.
        rewrite pfzn.
        unfold Is_ValZero.
        reflexivity.
    Qed.

    Global Instance Apply_Family_Pointwise_compose_SumUnionFriendly
           {i o n}
           (op_family: forall k, (k<n) -> rvector i -> rvector o)
           `{Koperator: forall k (kc: k<n), @SHOperator _ i o (op_family k kc)}
           `{Uf: !FamilyIUnionFriendly op_family}
           (pf: { j | j<o} -> CarrierA -> CarrierA)
           (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero)
           `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}
      :
        FamilyIUnionFriendly
          (fun j jc => SHPointwise _ pf ∘ op_family j jc).
    Proof.
      unfold FamilyIUnionFriendly.
      intros x.
      apply Vforall_nth_intro.
      intros j jc.
      unfold Vunique.
      intros i0 ic0 i1 ic1.
      unfold transpose.
      rewrite Vbuild_nth.
      unfold row.
      rewrite 2!Vnth_map.
      unfold Apply_Family.
      rewrite 2!Vbuild_nth.
      unfold Vnth_aux.
      unfold compose.
      rewrite 2!SHPointwise_nth_eq.

      unfold FamilyIUnionFriendly in Uf.
      specialize (Uf x).
      apply Vforall_nth with (ip:=jc) in Uf.
      unfold Vunique in Uf.
      specialize (Uf i0 ic0 i1 ic1).

      unfold transpose, Apply_Family, compose, row in Uf.
      rewrite Vbuild_nth in Uf.
      rewrite 2!Vnth_map in Uf.
      unfold Vnth_aux in Uf.
      rewrite 2!Vbuild_nth in Uf.

      generalize dependent (Vnth (op_family i0 ic0 x) jc).
      generalize dependent (Vnth (op_family i1 ic1 x) jc).
      intros x0 x1 [H0 H1].
      apply Uf. clear Uf.
      unfold Is_Val, IsVal, compose in *.
      crush.
    Qed.

     *)

    Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

    Lemma rewrite_PointWise_ISumUnion
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
          {Uz: Apply_Family_Single_NonZero_Per_Row _ op_family}
          (pf: { j | j<o} -> CarrierA -> CarrierA)
          (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero)
          `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}
          {iset oset}
      :
        (@SHPointwise _ o pf pf_mor) ⊚ (@ISumUnion i o n op_family)

        =

        (@ISumUnion i o n
                    (mkSHOperatorFamily _ i o n
                                        (fun (j:nat) (jc:j<n) =>
                                           (@mkSHOperator _ i o
                                                          ((op _ (@SHPointwise _ o pf pf_mor)) ∘ (get_family_op _ op_family j jc)) _ iset oset)
                    ))
        ).
    Proof.
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
        unfold Apply_Family_Single_NonZero_Per_Row in Uz.
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
                tauto.
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
          rewrite UnionFold_VallButOne_zero with (kc0:=kc).
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
              unfold Is_ValZero.
              rewrite SHPointwise'_nth by apply MonoidLaws_RthetaFlags.

              unfold VAllButOne in Uone.
              specialize (Uone t tc H).
              rewrite Vbuild_nth in Uone.

              apply Is_ValZero_not_not_impl in Uone.
              crush.
              reflexivity.
            }

            rewrite UnionFold_VallButOne_zero with (kc0:=kc).
            ** subst vr.
               rewrite Vbuild_nth.
               rewrite SHPointwise'_nth.
               reflexivity.
            ** apply H.
          *
            apply VallButOneSimpl with (P0:=(not ∘ (not ∘ Is_ValZero))).
            apply Is_ValZero_not_not_impl.
            apply Uone.
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


  (*
    Lemma rewrite_Reduction_ISumReduction
          {i o n}
          (op_family: forall k, (k<n) -> svector i -> svector o)
          `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
          `{Uz: !Apply_Family_Single_NonZero_Per_Row op_family}
          `{Uf: !FamilyIUnionFriendly op_family}
          (f: Rtheta -> Rtheta -> Rtheta)
          `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
      :
      SHOperator_hequiv _
        Reduction(2, (a, b) -> max(a, b), V(0.0), (arg) -> false) ∘ (ISumUnion op_family) =
        ISumReduction (Uf := Apply_Family_Pointwise_compose_SumUnionFriendly op_family pf pfzn)
                  (fun j jc => Reduction ∘ op_family j jc).
    Proof.
    Qed.
   *)
  End Value_Correctness.
End SigmaHCOLRewritingRules.

(*
Hint Extern 0 (Apply_Family_Single_NonZero_Per_Row (SparseEmbedding _ _ _)) => apply Apply_Family_SparseEmbedding_Single_NonZero_Per_Row : typeclass_instances.

Hint Extern 0 (FamilyIUnionFriendly (SparseEmbedding _ _ _)) => apply Apply_Family_SparseEmbedding_SumUnionFriendly : typeclass_instances.
 *)
