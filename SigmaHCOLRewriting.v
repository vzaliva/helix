
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

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.

(* CoRN Math-classes *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.setoids.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Local Open Scope vector_scope.
Local Open Scope nat_scope.

Lemma Gather_composition
      {i o t: nat}
      (f: index_map o t)
      (g: index_map t i):
  Gather f ∘ Gather g = Gather (index_map_compose g f).
Proof.
  assert(SHOperator (Gather f ∘ Gather g)).
  {
    apply SHOperator_compose; apply SHOperator_Gather.
  }
  apply SHOperator_functional_extensionality.
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
  Scatter g (f_inj:=g_inj) ∘ Scatter f (f_inj:=f_inj)
  = Scatter (index_map_compose g f) (f_inj:=index_map_compose_injective g f g_inj f_inj).
Proof.
  assert(SC: SHOperator (Scatter g (f_inj:=g_inj) ∘ Scatter f (f_inj:=f_inj)))
    by (apply SHOperator_compose; apply SHOperator_Scatter).
  apply SHOperator_functional_extensionality. clear SC.
  intros v.
  unfold compose.
  vec_index_equiv j jp.
  unfold Scatter.
  rewrite 2!Vbuild_nth.
  break_match.
  - rewrite Vbuild_nth.
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
  -
    simpl.
    break_match.
    +
      contradict n.
      apply in_range_index_map_compose_left in i0; try assumption.
    + reflexivity.
Qed.

Lemma LiftM_Hoperator_compose
      {i1 o2 o3}
      `{HOperator o2 o3 op1}
      `{HOperator i1 o2 op2}
  :
    liftM_HOperator (op1 ∘ op2) = (liftM_HOperator op1) ∘ (liftM_HOperator op2).
Proof.
  apply SHOperator_functional_extensionality.
  intros v.
  unfold liftM_HOperator, compose.
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

Lemma VecUnion_structs:
  ∀ (m : nat) (x : svector m),
    Vforall Is_ValZero x → Is_ValZero (VecUnion x).
Proof.
  intros m x H.
  unfold VecUnion.
  induction x.
  -
    unfold Is_ValZero.
    unfold_Rtheta_equiv.
    reflexivity.
  - simpl in H. destruct H as [Hh Hx].
    Opaque Monad.ret.
    simpl.
    Transparent Monad.ret.
    rewrite Is_ValZero_to_mkSZero in *.
    rewrite Hh.
    rewrite Union_SZero_r.
    apply IHx, Hx.
Qed.

(* Formerly Lemma3 *)
Lemma SingleValueInZeros m j (x:svector m) (jc:j<m):
  (forall i (ic:i<m),
      i ≢ j -> Is_ValZero (Vnth x ic)) -> (VecUnion x = Vnth x jc).
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
      rewrite VecUnion_cons.
      assert(Vforall Is_ValZero x0).
      {
        apply Vforall_nth_intro.
        intros.
        assert(ipp:S i < S m) by lia.
        replace (Vnth x0 ip) with (Vnth (Vcons h x0) ipp) by apply Vnth_Sn.
        apply SZ; lia.
      }

      assert(UZ: Is_ValZero (VecUnion x0))
        by apply VecUnion_structs, H.
      setoid_replace (VecUnion x0) with mkSZero
        by apply Is_ValZero_to_mkSZero, UZ.
      clear UZ.
      apply Union_SZero_l.
    +
      (* Case ("j!=0"). *)
      rewrite VecUnion_cons.
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

      setoid_replace h with mkSZero by apply Is_ValZero_to_mkSZero, HS.
      apply Union_SZero_r.

      intros i ic.
      assert(ics: S i < S m) by lia.
      rewrite <- Vnth_Sn with (v:=h) (ip:=ics).
      specialize SZ with (i:=S i) (ic:=ics).
      auto.
Qed.

(* TODO: Currently unused except in U_SAG1_PW. Remove? *)
Lemma U_SAG1:
  ∀ (n : nat) (x : avector n)
    (f: { i | i<n} -> CarrierA -> CarrierA)
    `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    (i : nat) (ip : i < n),
    Vnth
      (SumUnion
         (Vbuild
            (λ (i0 : nat) (id : i0 < n),
             (
               (ScatH i0 1
                      (snzord0:=ScatH_stride1_constr)
                      (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id))
                 ∘ (liftM_HOperator (HAtomic (f (i0 ↾ id))))
                 ∘ (GathH i0 1
                          (domain_bound:=GathH_j1_domain_bound i0 n id))
             ) (sparsify x)))) ip
    =
    mkValue (Vnth (HPointwise f x) ip).
Proof.
  intros n x f pF i ip.
  remember (λ (i0 : nat) (id : i0 < n),
            (
              (ScatH i0 1
                     (snzord0:=ScatH_stride1_constr)
                     (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id))
                ∘ (liftM_HOperator (HAtomic (f (i0 ↾ id))))
                ∘ (GathH i0 1
                         (domain_bound:=GathH_j1_domain_bound i0 n id))
            ) (sparsify x)) as bf.
  assert(B1: bf ≡ (λ (i0 : nat) (id : i0 < n),
                   ScatH i0 1
                         (snzord0:=ScatH_stride1_constr)
                         (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id)
                         ((liftM_HOperator (HAtomic (f (i0 ↾ id))))
                            [Vnth (sparsify x) id]))).
  {
    subst bf.
    extensionality j.
    extensionality jn.
    unfold GathH, Gather.
    unfold compose.
    rewrite Vbuild_1.
    unfold VnthIndexMapped.
    simpl.
    generalize (IndexFunctions.h_index_map_obligation_1 1 n j 1
                                                        (GathH_j1_domain_bound j n jn) 0 (lt_0_Sn 0)).
    intros ln.
    simpl in ln.
    rewrite Vnth_cast_index with (jc:=jn) by omega.
    reflexivity.
  }
  assert (B2: bf ≡ (λ (i0 : nat) (id : i0 < n),
                    ScatH i0 1 (snzord0:=ScatH_stride1_constr) (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id) (sparsify [f (i0 ↾ id) (Vnth x id)]))).
  {
    rewrite B1.
    extensionality j.
    extensionality jn.
    unfold liftM_HOperator, HAtomic, compose.
    unfold sparsify.
    simpl.
    rewrite Vnth_map.
    reflexivity.
  }
  rewrite B2.
  clear B1 B2 Heqbf bf.

  unfold HPointwise.
  rewrite Vbuild_nth.

  (* Lemma5 emebdded below *)
  rewrite AbsorbUnionIndex by solve_proper.
  rewrite Vmap_Vbuild.

  (* Preparing to apply Lemma3. Prove some peoperties first. *)
  remember (Vbuild
              (λ (z : nat) (zi : z < n),
               Vnth (ScatH z 1 (sparsify [f (z ↾ zi) (Vnth x zi)])) ip)) as b.


  assert
    (L3pre: forall ib (icb:ib<n),
        ib ≢ i -> Is_ValZero (Vnth b icb)).
  {
    intros ib icb.
    subst.
    rewrite Vbuild_nth.
    unfold ScatH, Scatter.
    rewrite Vbuild_nth; intros H.
    break_match.
    - unfold h_index_map in i0.
      simpl in i0.
      destruct (Nat.eq_dec ib 0).
      +  subst.
         simpl in i0.
         break_match.
         congruence.
         crush.
      +
        generalize (@inverse_index_f_spec 1 n
                                          (@h_index_map 1 n ib 1 (ScatH_1_to_n_range_bound ib n 1 icb))
                                          (@build_inverse_index_map 1 n
                                                                    (@h_index_map 1 n ib 1 (ScatH_1_to_n_range_bound ib n 1 icb))) i
                                          i0).
        intros l.
        break_if.
        rewrite <- plus_n_O in e.
        congruence.
        simpl in *.
        crush.
    - apply SZero_is_ValZero.
  }
  rewrite SingleValueInZeros with (j:=i) (jc:=ip) by apply L3pre.
  clear L3pre.
  subst b.
  rewrite Vbuild_nth.
  unfold ScatH, Scatter.
  rewrite Vbuild_nth.
  break_match.
  +
    rewrite Vnth_sparsify.
    rewrite Vnth_1.
    reflexivity.
  +
    unfold in_range in n0.
    simpl in n0.
    break_if; crush.
Qed.

(* TODO: Currently unused. Remove? *)
Lemma U_SAG1_PW:
  forall n (x:avector n)
    (f: { i | i<n} -> CarrierA -> CarrierA)
    `{pF: !Proper ((=) ==> (=) ==> (=)) f},
    SumUnion
      (@Vbuild (svector n) n
               (fun i id =>
                  (
                    (ScatH i 1
                           (snzord0:=ScatH_stride1_constr)
                           (range_bound:=ScatH_1_to_n_range_bound i n 1 id))
                      ∘ (liftM_HOperator (HAtomic (f (i ↾ id))))
                      ∘ (GathH i 1
                               (domain_bound:=GathH_j1_domain_bound i n id)
                        )
                  ) (sparsify x)
      ))
    =
    sparsify (HPointwise f x).
Proof.
  intros n x f pF.
  vec_index_equiv i ip.
  rewrite Vnth_sparsify.
  apply U_SAG1.
Qed.


Fact GathH_jn_domain_bound i n:
  i < n ->
  ∀ x : nat, x < 2 → i + x * n < (n+n).
Proof.
  intros.
  nia.
Qed.

Lemma U_SAG2:
  ∀ (n : nat) (x : svector (n + n))
    (f: nat -> CarrierA -> CarrierA -> CarrierA)
    `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    (k : nat) (kp : k < n),
    Vnth
      (SumUnion
         (@Vbuild (svector n) n
                  (fun i id =>
                     ((ScatH i 1
                             (snzord0:=ScatH_stride1_constr)
                             (range_bound:=ScatH_1_to_n_range_bound i n 1 id))
                        ∘ (SHBinOp (o:=1) (SwapIndex2 i f))
                        ∘ (GathH i n
                                 (domain_bound:=GathH_jn_domain_bound i n id))
                     ) x
      ))) kp
    = Vnth ((SHBinOp (o:=n) f) x) kp.
Proof.
  intros n x f f_mor k kp.
  unfold compose.

  remember (fun i id =>
              ScatH i 1
                    (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                    (SHBinOp (o:=1) (SwapIndex2 i f)
                             (GathH i n
                                    (domain_bound:=GathH_jn_domain_bound i n id) x)))
    as bf.

  assert(ILTNN: forall y:nat,  y<n -> y<(n+n)) by (intros; omega).
  assert(INLTNN: forall y:nat,  y<n -> y+n<(n+n)) by (intros; omega).

  assert(B1: bf ≡ (fun i id =>
                     (ScatH i 1
                            (snzord0:=ScatH_stride1_constr)
                            (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                            (SHBinOp (o:=1) (SwapIndex2 i f)
                                     [(Vnth x (ILTNN i id));  (Vnth x (INLTNN i id))])))).
  {
    subst bf.
    extensionality j. extensionality jn.
    unfold GathH, Gather, compose.
    rewrite Vbuild_2.
    unfold VnthIndexMapped.
    generalize
      (index_f_spec 2 (n + n) (@h_index_map 2 (n + n) j n (GathH_jn_domain_bound j n jn)) 0  (lt_0_SSn 0)) as l0
                                                                                                              , (index_f_spec 2 (n + n) (@h_index_map 2 (n + n) j n (GathH_jn_domain_bound j n jn)) 1  (lt_1_SSn 0)) as l1,  (ILTNN j jn) as l00, (INLTNN j jn) as l01.
    intros.
    simpl in *.
    rewrite Vnth_cast_index with (jc:=l00) (ic:=l0) by omega.
    rewrite Vnth_cast_index with (jc:=l01) (ic:=l1) by omega.
    reflexivity.
  }

  assert (B2: bf ≡ (λ (i : nat) (id : i < n),
                    ScatH i 1
                          (snzord0:=ScatH_stride1_constr)
                          (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                          [Monad.liftM2 (SwapIndex2 i f 0) (Vnth x (ILTNN i id))
                                        (Vnth x (INLTNN i id))]
         )).
  {
    rewrite B1.
    extensionality i.
    extensionality id.
    unfold sparsify.
    unfold SHBinOp, vector2pair.
    break_let.
    simpl in Heqp.
    inversion Heqp.
    subst t t0.
    rewrite Vbuild_1.
    simpl ((Vnth [Vnth x (ILTNN i id)] (Nat.lt_0_succ 0))).
    simpl (Vnth [Vnth x (INLTNN i id)] (Nat.lt_0_succ 0)).
    reflexivity.
  }
  rewrite B2.
  clear B1 B2 Heqbf bf.

  (* Lemma5 embedded below*)
  rewrite AbsorbUnionIndex by solve_proper.
  rewrite Vmap_Vbuild.

  (* Preparing to apply Lemma3. Prove some peoperties first. *)
  remember (Vbuild
              (λ (z : nat) (zi : z < n),
               Vnth (ScatH z 1 [Monad.liftM2 (SwapIndex2 z f 0) (Vnth x (ILTNN z zi))
                                             (Vnth x (INLTNN z zi))]) kp)) as b.

  assert
    (L3pre: forall ib (icb:ib<n),
        ib ≢ k -> Is_ValZero (Vnth b icb)).
  {
    intros ib icb.
    subst.
    rewrite Vbuild_nth.
    unfold ScatH, Scatter.
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
        generalize (@inverse_index_f_spec 1 n
                                          (@h_index_map 1 n ib 1 (ScatH_1_to_n_range_bound ib n 1 icb))
                                          (@build_inverse_index_map 1 n
                                                                    (@h_index_map 1 n ib 1 (ScatH_1_to_n_range_bound ib n 1 icb))) k i).
        intros l.
        break_if.
        rewrite <- plus_n_O in e.
        congruence.
        simpl in *.
        crush.
    - apply SZero_is_ValZero.
  }
  rewrite SingleValueInZeros with (j:=k) (jc:=kp) by apply L3pre.
  subst b.
  rewrite Vbuild_nth.
  unfold ScatH, Scatter.
  rewrite Vbuild_nth.
  break_match.
  +
    rewrite Vnth_1.
    rewrite (@SHBinOp_nth n f _ x _ kp (ILTNN k kp) (INLTNN k kp)).
    reflexivity.
  +
    unfold in_range in n0.
    simpl in n0.
    break_if; crush.
Qed.

Section SigmaHCOLExpansionRules.
  Section Value_Correctness.

    Lemma h_j_1_family_injective {n}:
      index_map_family_injective
        (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j n 1 jc)))).
    Proof.
      unfold index_map_family_injective.
      crush.
    Qed.


    (*
    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N),
        ISumUnion(i, i.range, OLCompose(
        ScatHUnion(o.N, 1, i, 1),
        BinOp(1, o.op),
        GathH(2*o.N, 2, i, o.N)
        )))),

       This is not typical operaror extensional equality, as implicit argument x must be provided and will be embedded in RHS expression.
     *)
    Theorem expand_BinOp:
      forall (n:nat)
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f},
        SHBinOp (o:=n) f
        =
        USparseEmbedding (i:=n+n) (o:=n)
                         (fun j _ => SHBinOp (o:=1) (SwapIndex2 j f))
                         (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j n 1 jc))))
                         (f_inj := h_j_1_family_injective)
                         (IndexMapFamily _ _ n (fun j jc => h_index_map j n (range_bound:=GathH_jn_domain_bound j n jc))).
    Proof.
      intros n f pF.
      apply ext_equiv_applied_iff'.
      {
        typeclasses eauto.
      }
      {
        split; try apply vec_Setoid.
        unfold USparseEmbedding, Apply_Family, SparseEmbedding.
        solve_proper.
      }
      intros x.
      vec_index_equiv i ip.
      symmetry.
      unfold USparseEmbedding, Apply_Family, SparseEmbedding. simpl.
      apply U_SAG2; assumption.
    Qed.


    (*
   ApplyFunc(SUMUnion, List([1..Length(ch)], i->OLCompose(
            ScatHUnion(Rows(o), Rows(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[1])), 1),
            self(ch[i], opts),
            GathH(Cols(o), Cols(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[2])), 1))))),
     *)
    Theorem expand_HTDirectSum
            {i1 o1 i2 o2}
            (f: avector i1 -> avector o1)
            (g: avector i2 -> avector o2)
            `{hop1: !HOperator f}
            `{hop2: !HOperator g}
      :
        liftM_HOperator (HTDirectSum f g) =
        (HTSUMUnion
           ((ScatH 0 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_first_half o1 o2)
            ) ∘ (liftM_HOperator f) ∘ (GathH 0 1 (domain_bound := h_bound_first_half i1 i2)))
           ((ScatH o1 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_second_half o1 o2)
            ) ∘ (liftM_HOperator g) ∘ (GathH i1 1 (domain_bound := h_bound_second_half i1 i2)))).
    Proof.
      eapply ext_equiv_applied_iff'.

      {
        split; try apply vec_Setoid.
        intros x y E.
        rewrite E. reflexivity.
      }

      {
        split; try apply vec_Setoid.
        intros x y E.
        rewrite E. reflexivity.
      }

      intros x.

      unfold liftM_HOperator at 1.
      unfold compose.
      unfold HTDirectSum, HCross, THCOLImpl.Cross, compose,
      HTSUMUnion, pair2vector.

      break_let. break_let.
      rename t1 into x0, t2 into x1.
      tuple_inversion.
      symmetry.

      assert(LS: @ScatH o1 (o1 + o2) 0 1 (h_bound_first_half o1 o2)
                        (@ScatH_stride1_constr o1 2)
                        (liftM_HOperator f (@GathH (i1 + i2) i1 0 1 (h_bound_first_half i1 i2) x)) = Vapp (sparsify (f x0)) (szero_svector o2)).
      {
        setoid_replace (@GathH (i1 + i2) i1 0 1 (h_bound_first_half i1 i2) x) with (sparsify x0).
        -
          vec_index_equiv i ip.
          unfold ScatH, Scatter.
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
              unfold liftM_HOperator, sparsify, compose.
              rewrite Vnth_map.
              unfold densify.
              rewrite Vmap_map.
              unfold mkValue, WriterMonadNoT.evalWriter.
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
          unfold GathH, Gather.
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

      assert(RS: @ScatH o2 (o1 + o2) o1 1 (h_bound_second_half o1 o2)
                        (@ScatH_stride1_constr o2 2)
                        (liftM_HOperator g (@GathH (i1 + i2) i2 i1 1 (h_bound_second_half i1 i2) x)) = Vapp (szero_svector o1) (sparsify (g x1))).
      {
        setoid_replace (@GathH (i1 + i2) i2 i1 1 (h_bound_second_half i1 i2) x) with (sparsify x1).
        -
          unfold ScatH, Scatter.
          vec_index_equiv i ip.
          rewrite Vbuild_nth.
          rewrite Vnth_app.
          break_match.
          + (* Second half of x, which is gx0 *)
            break_match.
            * simpl.
              unfold liftM_HOperator, sparsify, compose.
              rewrite 2!Vnth_map.
              unfold densify.
              rewrite Vmap_map.
              unfold mkValue, WriterMonadNoT.evalWriter.
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
        - unfold GathH, Gather.
          vec_index_equiv i ip.
          rewrite Vbuild_nth.
          unfold h_index_map.
          unfold VnthIndexMapped.
          simpl.


          rename Heqp0 into H.
          apply Vbreak_arg_app in H.
          unfold sparsify.
          rewrite Vnth_map.

          (*
          generalize (IndexFunctions.h_index_map_obligation_1 i2 (i1 + i2) i1 1
       (h_bound_second_half i1 i2) i ip) as l.
          intros l.
           *)

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
      setoid_replace (Vmap2 (Union) (sparsify (f x0)) (szero_svector o1)) with (sparsify (f x0)).
      setoid_replace (Vmap2 (Union) (szero_svector o2) (sparsify (g x1))) with (sparsify (g x1)).
      unfold sparsify.
      rewrite Vmap_app.
      reflexivity.
      apply Vec2Union_szero_svector_l.
      apply Vec2Union_szero_svector_r.
    Qed.


    (* Tactic to normalize type expressions and apply expand_HTDirectSum rewriting *)
  End Value_Correctness.

  Section Structural_Correctness.

    Global Instance HBinOp_DensityPreserving
           (n:nat)
           (f: nat -> CarrierA -> CarrierA -> CarrierA)
           `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
      DensityPreserving (liftM_HOperator (HBinOp (o:=n) f)).
    Proof.
      apply liftM_HOperator_DensityPreserving.
      typeclasses eauto.
    Qed.

    Global Instance HBinOp_expansion_DensityPreserving
           (n:nat)
           (f: nat -> CarrierA -> CarrierA -> CarrierA)
           `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
           (nz: n ≢ 0) (* Additional constraint! *)
      :
        DensityPreserving (
            USparseEmbedding (i:=n+n) (o:=n)
                             (fun j _ => SHBinOp (o:=1) (SwapIndex2 j f))
                             (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j n 1 jc))))
                             (f_inj := h_j_1_family_injective)
                             (IndexMapFamily _ _ n (fun j jc => h_index_map j n (range_bound:=GathH_jn_domain_bound j n jc)))).
    Proof.
      unfold DensityPreserving.
      intros x Dx.
      apply USparseEmbeddingIsDense.

      - unfold index_map_family_surjective.
        unfold h_index_map.
        simpl.
        intros y yc.
        exists 0, y.
        eexists.
        auto.
        eexists.
        assumption.
        auto.
      -
        assumption.
      - simpl.
        intros j jc k kc.
        unfold svector_is_dense in Dx.
        generalize ((IndexFunctions.h_index_map_obligation_1 2 (n + n) j n
                                                             (GathH_jn_domain_bound j n jc) k kc)).
        intros l.
        eapply Vforall_nth in Dx.
        apply Dx.
    Qed.


    Global Instance HTDirectSum_DensityPreserving
           {i1 o1 i2 o2}
           (f: avector i1 -> avector o1)
           (g: avector i2 -> avector o2)
           `{hop1: !HOperator f}
           `{hop2: !HOperator g}
      : DensityPreserving (liftM_HOperator (HTDirectSum f g)).
    Proof.
      apply liftM_HOperator_DensityPreserving.
      typeclasses eauto.
    Qed.

    Global Instance HTDirectSum_expansion_DensityPreserving
           {i1 o1 i2 o2}
           (f: avector i1 -> avector o1)
           (g: avector i2 -> avector o2)
           `{hop1: !HOperator f}
           `{hop2: !HOperator g}
      : DensityPreserving (
            (HTSUMUnion
               ((ScatH 0 1
                       (snzord0:=ScatH_stride1_constr)
                       (range_bound := h_bound_first_half o1 o2)
                ) ∘
                  (liftM_HOperator f) ∘
                  (GathH 0 1 (domain_bound := h_bound_first_half i1 i2)))

               ((ScatH o1 1
                       (snzord0:=ScatH_stride1_constr)
                       (range_bound := h_bound_second_half o1 o2)
                ) ∘
                  (liftM_HOperator g) ∘
                  (GathH i1 1 (domain_bound := h_bound_second_half i1 i2))))).
    Proof.
      unfold DensityPreserving.
      intros x Dx.

      unfold svector_is_dense, compose.
      apply Vforall_nth_intro.
      intros i ip.
      unfold HTSUMUnion.
      unfold GathH.

      (* Generalize Gathers *)
      remember (@Gather (i1 + i2) i2
                        (@h_index_map i2 (i1 + i2) i1 1
                                      (h_bound_second_half i1 i2)) x) as gx1.
      assert(Dxg1: svector_is_dense gx1).
      {
        subst.
        apply Gather_preserves_density, Dx.
      }
      generalize dependent gx1.
      intros gx1 Heqgx Dxg1. clear Heqgx.

      remember (@Gather (i1 + i2) i1
                        (@h_index_map i1 (i1 + i2) 0 1
                                      (h_bound_first_half i1 i2)) x) as gx2.
      assert(Dxg2: svector_is_dense gx2).
      {
        subst.
        apply Gather_preserves_density, Dx.
      }
      generalize dependent gx2.
      intros gx2 Heqgx Dxg2. clear Heqgx.
      clear Dx x.

      (* Generalize nested operators' application *)
      assert(svector_is_dense (liftM_HOperator f gx2)).
      {
        apply liftM_HOperator_DensityPreserving.
        apply hop1.
        apply Dxg2.
      }
      generalize dependent (liftM_HOperator f gx2). intros fgx2 Dfgx2.
      clear Dxg2 gx2  hop1 f.

      assert(svector_is_dense (liftM_HOperator g gx1)).
      {
        apply liftM_HOperator_DensityPreserving.
        apply hop2.
        apply Dxg1.
      }
      generalize dependent (liftM_HOperator g gx1). intros ggx1 Dggx1.
      clear Dxg1 gx1 hop2 g.

      unfold Vec2Union.
      rewrite Vnth_map2.

      apply ValUnionIsVal.
      unfold ScatH.

      destruct (Coq.Arith.Compare_dec.lt_dec i o1).
      -
        left.
        unfold Scatter.
        rewrite Vbuild_nth.
        break_match.
        + simpl.
          unfold svector_is_dense in Dfgx2.
          apply Vforall_nth, Dfgx2.
        +
          contradict n.
          apply in_range_exists.
          apply ip.
          simpl.
          exists i,l.
          lia.
      -
        right.
        unfold Scatter.
        rewrite Vbuild_nth.
        break_match.
        + simpl.
          unfold svector_is_dense in Dggx1.
          apply Vforall_nth, Dggx1.
        +
          contradict n0.
          apply in_range_exists.
          apply ip.
          simpl.
          exists (i-o1).
          assert(l: (i - o1) < o2).
          omega.
          exists l.
          omega.
    Qed.

  End Structural_Correctness.


End SigmaHCOLExpansionRules.

Ltac HOperator_HBinOp_Type_Fix :=
  match goal with
  | [ |- (@HOperator ?i ?o (@HBinOp ?o _ _)) ] =>
    replace (@HOperator i) with (@HOperator (Init.Nat.add o o)) by apply eq_refl; apply HBinOp_HOperator
  end.

Hint Extern 0 (@HOperator _ ?o (@HBinOp ?o _ _)) => HOperator_HBinOp_Type_Fix : typeclass_instances.

(* Ltac SHOperator_SHBinOp_Type_Fix :=
  match goal with
  | [ |- (@SHOperator ?i ?o (@SHBinOp ?o _ _)) ] =>
    replace (@SHOperator i) with (@SHOperator (Init.Nat.add o o)) by apply eq_refl; apply SHOperator_SHBinOp
  end.

Hint Extern 0 (@SHOperator _ ?o (@SHBinOp ?o _ _)) => SHOperator_SHBinOp_Type_Fix : typeclass_instances.
 *)

(* Hint Extern 0 (@Proper _ _ (compose)) => apply compose_proper with (RA:=equiv) (RB:=equiv) : typeclass_instances.
 *)

Ltac HOperator_HPrepend_Type_Fix :=
  match goal with
  | [ |- (@HOperator ?i ?o (@HPrepend ?n ?i ?a)) ] =>
    replace (@HOperator i o) with (@HOperator i (Init.Nat.add n i)) by apply eq_refl; apply HPrepend_HOperator
  end.

Hint Extern 0 (@HOperator ?i _ (@HPrepend _ ?i _)) => HOperator_HPrepend_Type_Fix : typeclass_instances.

Section SigmaHCOLRewritingRules.
  Section Value_Correctness.


    (*
    Lemma Vunique_cases
          {n}
          (x:svector n):

      Vunique Is_Val x ->
      {Vforall (not ∘ Is_Val) x} + {∃ i (ic: i<n), Is_Val (Vnth x ic)}.
    Proof.
      intros U.
      unfold Vunique in U.

      apply Vforall_notP_Vunique.


    Qed.
     *)

    Lemma rewrite_PointWise_ISumUnion
          {i o n}
          (op_family: forall k, (k<n) -> svector i -> svector o)
          `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
          `{Uf: !Apply_Family_SumUnionFriendly op_family}
          {NC: forall k (kc: k<n), CauseNoCol (op_family k kc)}
          (pf: { j | j<o} -> CarrierA -> CarrierA)
          (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero)
          `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}:
      
      SHPointwise pf ∘ SumUnion ∘ Apply_Family op_family =
      SumUnion ∘ (Apply_Family (fun j jc =>
                                  SHPointwise pf ∘ op_family j jc)
                 ).
    Proof.
      apply ext_equiv_applied_iff'.
      -
        (* LHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply SHOperator_SHPointwise.
        apply SumUnion_proper.
        apply Apply_Family_proper.
      -
        (* RHS Setoid_Morphism *)
        split; try apply vec_Setoid.
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply SumUnion_proper.
        apply Apply_Family_proper.
      -
        intros x.
        unfold compose.
        vec_index_equiv j jc. (* fix column *)
        setoid_rewrite SHPointwise_nth.

        unfold Apply_Family.
        rewrite 2!AbsorbIUnionIndex.

        (* -- Now we are dealing with VecUnions only -- *)

        (*
        SingleValueInZeros
          : ∀ (m j : nat) (x : vector Rtheta m) (jc : j < m),
            (∀ (i : nat) (ic : i < m), i ≢ j → Is_ValZero (Vnth x ic))
            → VecUnion x = Vnth x jc *)



        unfold Apply_Family_SumUnionFriendly in Uf.
        specialize (Uf x).
        apply Vforall_nth with (ip:=jc) in Uf.
        unfold Apply_Family, transpose in Uf.
        rewrite Vbuild_nth in Uf.
        unfold row in Uf.
        rewrite Vmap_Vbuild in Uf.
        unfold Vnth_aux in Uf.


        HERE
        erewrite SingleValueInZeros.


    Qed.





























  (*
        induction n.
        + (* prove induction hypothesis *)
          rewrite 2!Vbuild_0.
          unfold VecUnion.
          crush.
          unfold mkSZero.
          unfold_Rtheta_equiv.
          reflexivity.
        +
          rewrite 2!Vbuild_cons.
          rewrite 2!VecUnion_cons.

          (* -- Only one element of Union has value. Perform case analysis -- *)
          case (in_range_dec (⦃ f ⦄ 0 (Nat.lt_0_succ n)) j); intros R.
          * (* 2nd argument of Union has value *)
            (* LHS *)
            assert(HL: Is_ValZero (@VecUnion n
                                             (@Vbuild Rtheta n
                                                      (fun (i0 : nat) (ip : Peano.lt i0 n) =>
                                                         @Vnth Rtheta o
                                                               (@Scatter ko o
                                                                         (family_f ko o (S n) f (S i0) (@lt_n_S i0 n ip))
                                                                         (@index_map_family_member_injective ko o
                                                                                                             (S n) f f_inj (S i0)
                                                                                                             (@lt_n_S i0 n ip))
                                                                         (kernel (S i0) (@lt_n_S i0 n ip)
                                                                                 x)) j jc)))).
            {
              apply VecUnion_structs.
              apply Vforall_nth_intro.
              intros t tc.
              rewrite Vbuild_nth.
              apply Is_ValZero_to_mkSZero.

              apply Is_SZero_Scatter.
              crush.

              apply index_map_family_injective_in_range_once
              with (i0:=0) (ic:=Nat.lt_0_succ n)
                           (j0:=S t) (jc0:=lt_n_S tc)
                           (y:=j)
                in f_inj; try assumption.
              congruence.
            }
            rewrite evalWriterUnion.
            unfold Is_ValZero in HL.
            rewrite_clear HL.
            (* TODO remove 0+ using rewrite right_absorb. *)

            (* RHS *)

            assert(HR: Is_ValZero
                         (@VecUnion n
                                    (@Vbuild Rtheta n
                                             (fun (i0 : nat) (ip : Peano.lt i0 n) =>
                                                @Vnth Rtheta o
                                                      (@SHPointwise o pf pf_mor
                                                                    (@Scatter ko o
                                                                              (family_f ko o (S n) f (S i0) (@lt_n_S i0 n ip))
                                                                              (@index_map_family_member_injective ko o
                                                                                                                  (S n) f f_inj (S i0) (@lt_n_S i0 n ip))
                                                                              (kernel (S i0) (@lt_n_S i0 n ip)
                                                                                      x)))
                                                      j jc)))).
            {
              apply VecUnion_structs.
              apply Vforall_nth_intro.
              intros t tc.
              rewrite Vbuild_nth.
              apply Is_ValZero_to_mkSZero.

              rewrite SHPointwise_nth_eq.
              rewrite Scatter_eq_mkSZero.

              unfold_Rtheta_equiv.
              rewrite evalWriter_Rtheta_SZero.
              rewrite evalWriter_Rtheta_liftM.
              apply pfzn.
              crush.

              apply index_map_family_injective_in_range_once
              with (i0:=0) (ic:=Nat.lt_0_succ n)
                           (j0:=S t) (jc0:=lt_n_S tc)
                           (y:=j)
                in f_inj; try assumption.
              congruence.
            }

            unfold_Rtheta_equiv.
            rewrite evalWriterUnion.
            unfold Is_ValZero in HR.
            rewrite_clear HR.

            ring_simplify.
            rewrite SHPointwise_nth.
            f_equiv.
            f_equiv.
            f_equiv.
            ring_simplify.
            reflexivity.
          * (* 1st argument of Union has value *)

            rewrite Scatter_eq_mkSZero; try apply R.
            rewrite Union_SZero_r.

            rewrite SHPointwise_nth_eq.
            rewrite Scatter_eq_mkSZero; try apply R.

            clear R.

            setoid_replace (Monad.liftM (pf (j ↾ jc)) mkSZero) with mkSZero.
            rewrite Union_SZero_r.

            admit.

            {
              (* proving Monad.liftM (pf (j ↾ jc)) mkSZero = mkSZero *)
              unfold_Rtheta_equiv.
              rewrite evalWriter_Rtheta_liftM.
              rewrite evalWriter_Rtheta_SZero.
              apply pfzn.
            }

    Admitted.
 *)
  End Value_Correctness.
End SigmaHCOLRewritingRules.
