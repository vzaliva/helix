
Require Import VecUtil.
Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import SigmaHCOL.
Require Import HCOL.
Require Import THCOL.
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
Require Import CaseNaming.
Require Import SpiralTactics.

(* CoRN Math-classes *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Section SigmaHCOLRewriting.

  Local Open Scope hcol_scope. (* for compose *)
  Open Scope vector_scope.
  Global Open Scope nat_scope.

  Section Value_Correctness.

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
          Case ("j=0").
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
          Case ("j!=0").
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

    Lemma InverseIndex_1_hit:
      ∀ (n k s : nat) (kp : k < n) (v : Rtheta),
        (@VnthInverseIndexMapped 1 n [v]
                                 (@build_inverse_index_map 1 n
                                                           (@h_index_map 1 n k s
                                                                         (ScatH_1_to_n_range_bound k n s kp) )) k kp) ≡ v.
    Proof.
      intros n k s kp v.
      destruct (@build_inverse_index_map 1 n
                                         (@h_index_map 1 n k s
                                                       (ScatH_1_to_n_range_bound k n s kp) )) as [h' h'_spec] eqn:P.
      unfold h_index_map in P.
      inversion P. rename H0 into HH. symmetry in HH. clear P.
      assert(PH': h' k ≡ Some 0).
      {
        subst h'.
        break_if; [reflexivity | omega].
      }
      unfold VnthInverseIndexMapped, partial_index_f, partial_index_f_spec.
      generalize (h'_spec k).
      destruct (h' k); crush.
    Qed.

    Lemma InverseIndex_1_miss:
      ∀ (n s i j : nat) (ip : i < n) (jp: j<n) (v : Rtheta),
        i ≢ j ->
        @VnthInverseIndexMapped 1 n [v]
                                (@build_inverse_index_map 1 n
                                                          (@h_index_map 1 n j s
                                                                        (ScatH_1_to_n_range_bound j n s jp)
                                ))
                                i ip ≡ mkSZero.
    Proof .
      intros n s i j ip jp v N.
      destruct (@build_inverse_index_map 1 n
                                         (@h_index_map 1 n j s
                                                       (ScatH_1_to_n_range_bound j n s jp)
               )) as [h' h'_spec] eqn:P.
      unfold h_index_map in P.
      inversion P. rename H0 into HH. symmetry in HH.
      assert(PH': h' i ≡ None).
      {
        subst h'.
        break_if ; [omega | reflexivity ].
      }
      assert (N0: i ≢ j + 0) by omega.
      unfold VnthInverseIndexMapped, partial_index_f, partial_index_f_spec.
      generalize (h'_spec i).
      destruct (h' i); crush.
    Qed.

    Fact ScatH_stride1_constr:
    forall {a b:nat}, 1 ≢ 0 ∨ a < b.
    Proof.
      auto.
    Qed.

    Definition liftM_HOperator
               {i o}
               (op: avector i -> avector o)
               `{hop: !HOperator op}
      : svector i -> svector o :=
      sparsify ∘ op ∘ densify.


    Lemma U_SAG1:
      ∀ (n : nat) (x : avector n)
        (f: { i | i<n} -> CarrierA -> CarrierA) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
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
        simpl.
        rewrite InverseIndex_1_miss.
        apply SZero_is_ValZero.
        auto.
      }
      rewrite SingleValueInZeros with (j:=i) (jc:=ip) by apply L3pre.
      subst b.
      rewrite Vbuild_nth.
      unfold ScatH, Scatter.
      rewrite Vbuild_nth.
      simpl.
      rewrite InverseIndex_1_hit.
      reflexivity.
    Qed.

    Lemma U_SAG1_PW:
      forall n (x:avector n)
             (f: { i | i<n} -> CarrierA -> CarrierA) `{pF: !Proper ((=) ==> (=) ==> (=)) f},
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
      apply Vforall2_intro_nth.
      intros i ip.
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

    Lemma HBinOp_nth:
      ∀ (n : nat) (x : avector (n + n))
        (f : nat -> CarrierA → CarrierA → CarrierA)
        `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (k : nat) (kp : k < n) (kn: k < n + n) (knn: k + n < n + n),
        Vnth (HBinOp f x) kp ≡ f k (Vnth x kn) (Vnth x knn).
    Proof.
      intros n x f f_mor k kp kn knn.
      unfold HBinOp, compose, vector2pair, HCOLImpl.BinOp.
      break_let.  rename t into a. rename t0 into b.

      rewrite Vnth_Vmap2Indexed.
      assert(A: Vnth a kp ≡ Vnth x kn).
      {
        apply Vbreak_arg_app in Heqp.
        subst x.
        rewrite Vnth_app.
        break_match.
        crush.
        replace kp with g by apply proof_irrelevance.
        reflexivity.
      }
      assert(B: Vnth b kp ≡ Vnth x knn).
      {
        apply Vbreak_arg_app in Heqp.
        subst x.
        rewrite Vnth_app.
        break_match.
        generalize (Vnth_app_aux n knn l) as g.
        intros.
        apply Vnth_cast_index.
        omega.
        crush.
      }
      rewrite A, B.
      reflexivity.
    Qed.

    Lemma U_SAG2:
      ∀ (n : nat) (x : avector (n + n))
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
                            ∘ (liftM_HOperator (HBinOp (o:=1) (SwapIndex2 i f)))
                            ∘ (GathH i n
                                     (domain_bound:=GathH_jn_domain_bound i n id))
                         ) (sparsify x)
          ))) kp
        = mkValue (Vnth (HBinOp (o:=n) (f) x) kp).
    Proof.
      intros n x f f_mor k kp.
      unfold compose.

      remember (fun i id =>
                  ScatH i 1
                        (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                        (liftM_HOperator (HBinOp (o:=1) (SwapIndex2 i f))
                                         (GathH i n
                                                (domain_bound:=GathH_jn_domain_bound i n id) (sparsify x))))
        as bf.

      assert(ILTNN: forall y:nat,  y<n -> y<(n+n)) by (intros; omega).
      assert(INLTNN: forall y:nat,  y<n -> y+n<(n+n)) by (intros; omega).

      assert(B1: bf ≡ (fun i id =>
                         (ScatH i 1
                                (snzord0:=ScatH_stride1_constr)
                                (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                                (liftM_HOperator (HBinOp (o:=1) (SwapIndex2 i f))
                                                 [(Vnth (sparsify x) (ILTNN i id));  (Vnth (sparsify x) (INLTNN i id))])))).
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
                              (sparsify
                                 [ f i (Vnth x (ILTNN i id)) (Vnth x (INLTNN i id))]))).
      {
        rewrite B1.
        extensionality i.
        extensionality id.
        unfold liftM_HOperator, compose, sparsify.
        rewrite 2!Vnth_map.
        simpl.
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
                   Vnth (ScatH z 1 (sparsify [f z (Vnth x (ILTNN z zi)) (Vnth x (INLTNN z zi))])) kp)) as b.

      assert
        (L3pre: forall ib (icb:ib<n),
            ib ≢ k -> Is_ValZero (Vnth b icb)).
      {
        intros ib icb.
        subst.
        rewrite Vbuild_nth.
        unfold ScatH, Scatter.
        rewrite Vbuild_nth.
        intros H.
        simpl.
        rewrite InverseIndex_1_miss.
        apply SZero_is_ValZero.
        auto.
      }
      rewrite SingleValueInZeros with (j:=k) (jc:=kp) by apply L3pre.
      subst b.
      rewrite Vbuild_nth.
      unfold ScatH, Scatter.
      rewrite Vbuild_nth.
      simpl.
      rewrite InverseIndex_1_hit.
      setoid_rewrite HBinOp_nth with (kn:=(ILTNN k kp)) (knn:=(INLTNN k kp)).
      reflexivity.
    Qed.

    (*
    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N),
        ISumUnion(i, i.range, OLCompose(
        ScatHUnion(o.N, 1, i, 1),
        BinOp(1, o.op),
        GathH(2*o.N, 2, i, o.N)
        )))),
     *)
    Theorem expand_BinOp:
      forall n (x:avector (n+n))
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f},
        sparsify (HBinOp (o:=n) (f) x) =
        SumUnion
          (@Vbuild (svector n) n
                   (fun i id =>
                      (
                        (ScatH i 1
                               (snzord0:=ScatH_stride1_constr)
                               (range_bound:=ScatH_1_to_n_range_bound i n 1 id))
                          ∘ (liftM_HOperator (HBinOp (o:=1) (SwapIndex2 i f)))
                          ∘ (GathH i n
                                   (domain_bound:=GathH_jn_domain_bound i n id)
                            )
                      ) (sparsify x)
          )).
    Proof.
      intros n x f pF.
      apply Vforall2_intro_nth.
      intros i ip.
      symmetry.
      rewrite Vnth_sparsify.
      apply U_SAG2; assumption.
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

    Lemma Copy_one_half_get_same_part_is_Some:
      ∀ (o1 o2 i : nat) (partial_index_f : nat → option nat),
        partial_index_f
          ≡ (λ y : nat,
                   List.fold_right
                     (λ (x' : nat) (p : option nat),
                      if eq_nat_dec y (o1 + x' * 1) then Some x' else p) None
                     (rev_natrange_list o2))
        → (o1 <= i) /\ (i < o1 + o2)
        -> partial_index_f i ≡ Some (i-o1).
    Proof.
      intros.
      subst.
      induction o2.
      crush.
      simpl.
      break_if.
      crush.
      rewrite IHo2.
      reflexivity.
      omega.
    Qed.

    Lemma Copy_one_half_get_another_is_None:
      ∀ (o1 o2 i : nat) (partial_index_f : nat → option nat),
        partial_index_f
          ≡ (λ y : nat,
                   List.fold_right
                     (λ (x' : nat) (p : option nat),
                      if eq_nat_dec y (o1 + x' * 1) then Some x' else p) None
                     (rev_natrange_list o2))
        → (o1 > i) \/ (i>=o1+o2)
        → is_None (partial_index_f i).
    Proof.
      intros.
      subst.
      apply is_None_def.

      induction o2.
      crush.
      simpl.
      break_if.
      crush.
      rewrite IHo2.
      reflexivity.
      omega.
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
            (x: avector (i1+i2)) (* input vector *)
      :
        sparsify (HTDirectSum f g x) =
        (HTSUMUnion
           ((ScatH 0 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_first_half o1 o2)
            ) ∘ (liftM_HOperator f) ∘ (GathH 0 1 (domain_bound := h_bound_first_half i1 i2)))
           ((ScatH o1 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_second_half o1 o2)
            ) ∘ (liftM_HOperator g) ∘ (GathH i1 1 (domain_bound := h_bound_second_half i1 i2))))
          (sparsify x).
    Proof.
      unfold HTDirectSum, HCross, THCOLImpl.Cross, HCompose, compose,
      HTSUMUnion, pair2vector.
      break_let. break_let.
      rename t1 into x0, t2 into x1.
      tuple_inversion.
      symmetry.

      assert(LS: @ScatH o1 (o1 + o2) 0 1 (h_bound_first_half o1 o2)
                        (@ScatH_stride1_constr o1 2)
                        (liftM_HOperator f (@GathH (i1 + i2) i1 0 1 (h_bound_first_half i1 i2) (sparsify x))) ≡ Vapp (sparsify (f x0)) (szero_svector o2)).
      {
        replace (@GathH (i1 + i2) i1 0 1 (h_bound_first_half i1 i2) (sparsify x)) with (sparsify x0).
        -
          unfold ScatH, Scatter.
          apply Veq_nth.
          intros.
          rewrite Vbuild_nth.

          unfold sparsify.
          rewrite Vnth_app.
          break_match.
          + (* Second half of x, which is all zeros *)
            unfold szero_svector.
            rewrite Vnth_const.
            remember ((build_inverse_index_map (h_index_map 0 1))) as h'.

            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped.
            simpl.
            assert (HZI: partial_index_f i ≡ None).
            {
              apply is_None_def.
              apply Copy_one_half_get_another_is_None with (o1:=0) (o2:=o1).
              assumption.
              simpl.
              omega.
            }
            generalize (partial_index_f_spec i ip).
            rewrite HZI.
            reflexivity.
          + (* First half of x, which is fx0 *)
            remember ((build_inverse_index_map (h_index_map 0 1))) as h'.
            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped; simpl.
            assert (HZI: partial_index_f i ≡ Some i).
            {
              replace (Some i) with (Some (i-0)).
              apply Copy_one_half_get_same_part_is_Some with (o2:=o1) (o1:=O).
              assumption.
              split; omega.
              f_equal; omega.
            }
            generalize (partial_index_f_spec i ip) as some_spec.
            rewrite HZI.
            intros.
            replace (some_spec i eq_refl) with g0 by apply proof_irrelevance.
            rewrite Vnth_map.
            unfold liftM_HOperator, sparsify, compose.
            rewrite Vnth_map.
            unfold densify.
            rewrite Vmap_map.

            unfold mkValue, WriterMonadNoT.evalWriter.
            simpl.
            replace (Vmap (λ x2 : CarrierA, x2) x0) with x0
              by (symmetry; apply Vmap_id).
            reflexivity.
        - unfold GathH, Gather.
          apply Veq_nth.
          intros.
          rewrite Vbuild_nth.
          unfold h_index_map.
          unfold VnthIndexMapped.
          simpl.
          apply Vbreak_arg_app in Heqp0.
          subst x.
          unfold sparsify.
          rewrite 2!Vnth_map.
          rewrite Vnth_app.
          break_match.
          omega.
          revert g0.
          rewrite Mult.mult_1_r.
          unfold gt.
          intros g0.
          replace g0 with ip by apply proof_irrelevance.
          reflexivity.
      }

      assert(RS: @ScatH o2 (o1 + o2) o1 1 (h_bound_second_half o1 o2)
                        (@ScatH_stride1_constr o2 2)
                        (liftM_HOperator g (@GathH (i1 + i2) i2 i1 1 (h_bound_second_half i1 i2) (sparsify x))) ≡ Vapp (szero_svector o1) (sparsify (g x1))).
      {
        replace (@GathH (i1 + i2) i2 i1 1 (h_bound_second_half i1 i2) (sparsify x)) with (sparsify x1).
        -
          unfold ScatH, Scatter.
          apply Veq_nth.
          intros.
          rewrite Vbuild_nth.
          rewrite Vnth_app.
          break_match.
          + (* Second half of x, which is gx0 *)
            remember (build_inverse_index_map (h_index_map o1 1)) as h'.
            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped; simpl.
            assert (HZI: partial_index_f i ≡ Some (i-o1)).
            {
              apply Copy_one_half_get_same_part_is_Some with (o2:=o2).
              assumption.
              split; assumption.
            }
            generalize (partial_index_f_spec i ip) as some_spec.
            rewrite HZI.
            intros.
            replace (some_spec (i-o1) eq_refl) with (Vnth_app_aux o2 ip l) by apply proof_irrelevance.

            unfold liftM_HOperator, sparsify, compose.
            rewrite Vnth_map.
            unfold densify.
            rewrite Vmap_map.

            unfold mkValue, WriterMonadNoT.evalWriter.
            simpl.
            rewrite Vnth_map.
            replace (Vmap (λ x2 : CarrierA, x2) x1) with x1
              by (symmetry; apply Vmap_id).
            reflexivity.
          + (* First half of x, which is all zeros *)
            unfold szero_svector.  rewrite Vnth_const.
            remember ((build_inverse_index_map (h_index_map o1 1))) as h'.
            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped.
            simpl.
            assert (HZI: partial_index_f i ≡ None).
            {
              apply is_None_def.
              apply Copy_one_half_get_another_is_None with (o1:=o1) (o2:=o2).
              assumption.
              omega.
            }
            generalize (partial_index_f_spec i ip).
            rewrite HZI.
            reflexivity.
        - unfold GathH, Gather.
          apply Veq_nth.
          intros.
          rewrite Vbuild_nth.
          unfold h_index_map.
          unfold VnthIndexMapped.
          simpl.
          apply Vbreak_arg_app in Heqp0.
          subst x.
          unfold sparsify.
          rewrite 2!Vnth_map.
          rewrite Vnth_app.
          break_match.
          generalize (Vnth_app_aux i2
                                   (IndexFunctions.h_index_map_obligation_1 i2 (i1 + i2) i1 1
                                                                            (h_bound_second_half i1 i2) i ip) l) as ip'.
          revert ip.
          replace (i1 + i * 1 - i1) with i by omega.
          intros ip ip'.
          replace ip with ip' by apply proof_irrelevance.
          reflexivity.
          crush. (* contradiction in g0 *)
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

  End Value_Correctness.

  Section Structural_Correctness.

    (* Strong condition: operator preserves vectors' density *)
    Class DensityPreserving {i o:nat} (op: svector i -> svector o) :=
      o_den_pres : forall x, svector_is_dense x -> svector_is_dense (op x).

    (* All lifted HOperators are naturally density preserving *)
    Instance liftM_HOperator_DensityPreserving
             {i o}
             (op: avector i -> avector o)
             `{hop: !HOperator op}
      : DensityPreserving (liftM_HOperator op).
    Proof.
      unfold DensityPreserving.
      intros x D.

      unfold liftM_HOperator, compose.
      generalize (op (densify x)) as y. intros y.
      unfold svector_is_dense, sparsify.
      apply Vforall_map_intro.
      apply Vforall_nth_intro.
      intros i0 ip.
      apply IsVal_mkValue.
    Qed.


    (* Weaker condition: applied to a dense vector without collisions does not produce strucural collisions *)
    Class DenseCauseNoCol {i o:nat} (op: svector i -> svector o) :=
      o_den_non_col : forall x,
        svector_is_dense x ->
        svector_is_non_collision x ->
        svector_is_non_collision (op x).

    Instance liftM_HOperator_DenseCauseNoCol
             {i o}
             (op: avector i -> avector o)
             `{hop: !HOperator op}
      : DenseCauseNoCol (liftM_HOperator op).
    Proof.
      unfold DenseCauseNoCol.
      intros x D NC.
      unfold liftM_HOperator, compose.
      apply sparsify_non_coll.
    Qed.

    Definition SparseEmbedding
               {i o ki ko}
               (kernel: avector ki -> avector ko)
               (f: index_map ko o)
               {f_inj : index_map_injective f}
               (g: index_map ki i)
               `{Koperator: @HOperator ki ko kernel}
               (x: svector i)
               {g_dense: forall k (kc:k<ki), Is_Val (Vnth x («g» k kc))}

      :=
        (Scatter f (f_inj:=f_inj)
                 ∘ (liftM_HOperator kernel)
                 ∘ (Gather g)) x.

    Definition USparseEmbedding
               {n i o ki ko}
               (kernel: forall k, (k<n) -> avector ki -> avector ko)
               (f: index_map_family ko o n)
               {f_inj : index_map_family_injective f}
               (g: index_map_family ki i n)
               `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
               (x: svector i)
               {g_dense: forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))}
               {nz: n ≢ 0} (* only defined for non-empty iterator *)
      :=
        (SumUnion
           (Vbuild
              (λ (j:nat) (jc:j<n),
               SparseEmbedding
                 (f_inj:=index_map_family_member_injective f_inj j jc)
                 (g_dense:=g_dense j jc)
                 (kernel j jc)
                 ( ⦃f⦄ j jc)
                 ( ⦃g⦄ j jc)
                 x
        ))).

    (* Applying Scatter to collision-free vector, using injective family of functions will not cause any collisions *)
    Lemma ScatterCollisionFree
          {i o}
          (f: index_map i o)
          {f_inj: index_map_injective f}
          (x: svector i)
          (Xcf: svector_is_non_collision x)
      :
        svector_is_non_collision (@Scatter i o f f_inj x).
    Proof.
      unfold svector_is_non_collision, Not_Collision in *.
      apply Vforall_nth_intro.
      intros j jp.
      unfold Is_Collision in *.

      assert(E: Vforall
                  (fun p => (Vin p x) \/ (p ≡ mkSZero))
                  (Scatter f (f_inj:=f_inj) x)) by
          apply Scatter_is_almost_endomorphism.

      apply Vforall_nth with (ip:=jp) in E.

      generalize dependent (Vnth (Scatter f (f_inj:=f_inj) x) jp).
      intros v E.
      destruct E.
      -
        unfold svector_is_non_collision in Xcf.
        apply Vforall_in with (v:=x); assumption.
      -
        rewrite_clear H.
        auto.
    Qed.

    Lemma GatherCollisionFree
          {i o: nat}
          (x: svector i)
          (Xcf: svector_is_non_collision x)
      :
        forall f, svector_is_non_collision (@Gather i o f x).
    Proof.
      apply Gather_preserves_P, Xcf.
    Qed.

    Lemma USparseEmbeddingIsDense
          {n i o ki ko}
          (kernel: forall k, (k<n) -> avector ki -> avector ko)
          (f: index_map_family ko o n)
          {f_inj: index_map_family_injective f} (* gives non-col *)
          {f_sur: index_map_family_surjective f} (* gives density *)
          (g: index_map_family ki i n)
          `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
          (x: svector i)
          {g_dense: forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))}
          {nz: n ≢ 0}
      :
        svector_is_dense
          (@USparseEmbedding n i o ki ko kernel f f_inj g Koperator x g_dense nz).
    Proof.
      apply Vforall_nth_intro.
      intros oi oic.
      unfold compose.
      unfold USparseEmbedding, SparseEmbedding.
      rewrite AbsorbIUnionIndex.
      unfold compose.
      destruct n.
      - congruence.
      - clear nz.
        apply Is_Val_VecUnion.
        apply Vexists_Vbuild.
        unfold index_map_family_surjective in f_sur.
        specialize (f_sur oi oic).
        destruct f_sur as [z [p [zc [pc F]]]].
        exists p, pc.

        assert(Vforall Is_Val (Gather (⦃g ⦄ p pc) x))
          by apply Gather_dense_constr, g_dense.
        generalize dependent (Gather (⦃g ⦄ p pc) x).
        intros gx GD.
        clear g_dense g.

        assert(Vforall Is_Val (liftM_HOperator (kernel p pc) gx))
          by apply liftM_HOperator_DensityPreserving, GD.

        generalize dependent (liftM_HOperator (kernel p pc) gx).
        intros kx KD.
        clear GD gx Koperator kernel.

        rewrite Scatter_rev_spec.
        apply index_map_family_member_injective with (jc:=pc) in f_inj.
        generalize dependent (⦃f ⦄ p pc). intros fp fp_inj F.
        clear f.

        assert(ZI: partial_index_f _ _ (build_inverse_index_map fp) oi ≡ Some z)
          by (apply build_inverse_index_map_is_left_inverse; assumption).
        clear F fp_inj F.

        unfold VnthInverseIndexMapped.
        (* Ugly code below. needs to be cleaned up *)
        generalize dependent (build_inverse_index_map fp). intros pm ZI.

        unfold partial_index_f.
        break_match.
        simpl.
        generalize (partial_index_f_spec oi oic). intros.
        break_match.
        apply Vforall_nth, KD.
        simpl in *.
        congruence.
    Qed.


    (* Pre-condition for VecUnion not causing any collisions *)
    Lemma Not_Collision_VecUnion
          {n}
          {v: svector n}
      :
        Vforall Not_Collision v -> Vunique Is_Val v -> Not_Collision (VecUnion v).
    Proof.
      intros VNC H.
      dependent induction n.
      + dep_destruct v.
        compute.
        trivial.
      +
        dep_destruct v.
        rewrite VecUnion_cons.
        simpl in VNC. destruct VNC as [VNCh VNCx].
        apply UnionCollisionFree.
        *
          apply IHn.
          -- apply VNCx.
          -- clear IHn.
             apply Vunique_cons_tail in H.
             apply H.
        * apply VNCh.
        * cut(¬(Is_Val (VecUnion x)) \/ (¬ (Is_Val h))).
          firstorder.
          assert(D: Decision (Is_Val h)) by apply Is_Val_dec.
          destruct D as [Ph | Phn].
          -- left.
             clear VNCh VNCx IHn.

             unfold not. intros H0.
             apply Is_Val_VecUnion in H0.
             apply Vexists_eq in H0.
             destruct H0 as [x0 [V1 V2]].
             apply Vin_nth in V1.
             destruct V1 as [i [ip Vx]].
             subst x0.

             unfold Vunique in H.
             assert(jc: 0 < S n) by omega.
             assert(ip': S i < S n) by omega.
             specialize (H 0 jc (S i) ip').
             simpl (Vnth (Vcons h x) jc) in H.
             simpl (Vnth (Vcons h x) ip') in H.
             replace (lt_S_n ip') with ip in H by apply proof_irrelevance.
             assert(H1: Is_Val h ∧ Is_Val (Vnth x ip)) by auto.
             apply H in H1.
             congruence.
          -- right.
             apply Phn.
    Qed.

    (* TODO: maybe iff  *)
    Lemma Is_Val_Scatter
          {m n: nat}
          (f: index_map m n)
          {f_inj: index_map_injective f}
          (x: svector m)
          (XD: svector_is_dense x)
          (j: nat) (jc : j < n):
      Is_Val (Vnth (Scatter f (f_inj:=f_inj) x) jc) ->
      (exists i (ic:i<m), ⟦f⟧ i ≡ j).
    Proof.
      intros H.
      unfold svector_is_dense in XD.
      rewrite Scatter_rev_spec in H.
      unfold VnthInverseIndexMapped, partial_index_f in H.

      break_let.
      simpl in *.

      generalize dependent (partial_index_f_spec j jc).
      intros f_spec H.
      break_match.
      -
        exists n0.
        assert(nc: n0<m) by (apply f_spec; reflexivity).
        exists nc.
        replace (f_spec n0 eq_refl) with nc in H by apply proof_irrelevance.
        apply build_inverse_index_map_is_right_inverse; auto.
        inversion Heqp.
        rewrite Heqp.
        apply Heqo.
      -
        apply Is_Val_mkStruct in H.
        inversion H. (* for some reason congruence fails *)
    Qed.

    Lemma USparseEmbeddingCauseNoCol
          {n i o ki ko}
          (kernel: forall k, (k<n) -> avector ki -> avector ko)
          (f: index_map_family ko o n)
          {f_inj: index_map_family_injective f} (* gives non-col *)
          {f_sur: index_map_family_surjective f} (* gives density *)
          (g: index_map_family ki i n)
          `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
          (x: svector i)
          {g_dense: forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))}
          {nz: n ≢ 0}
      :

        (forall j (jc:j<n) k (kc:k<ki), Not_Collision (Vnth x («⦃g⦄ j jc» k kc))) ->
        svector_is_non_collision
          (@USparseEmbedding n i o ki ko kernel f f_inj g Koperator x g_dense nz).
    Proof.
      intros GNC.
      apply Vforall_nth_intro.
      intros oi oic.
      unfold compose.
      unfold USparseEmbedding, SparseEmbedding.
      rewrite AbsorbIUnionIndex.


      destruct n.
      - congruence.
      - (* driving towards apply Not_Collision_VecUnion. *)
        apply Not_Collision_VecUnion.
        +
          clear nz.
          apply Vforall_Vbuild.
          intros j jn.
          unfold compose.
          specialize (GNC j jn).

          (* Get rid of Gather, carring over its properties *)
          assert(GXD: svector_is_dense (Gather (⦃ g ⦄ j jn) x)).
          {
            unfold svector_is_dense.
            apply Vforall_nth_intro.
            intros.
            rewrite Gather_spec.
            apply g_dense.
          }

          assert(GXNC: svector_is_non_collision (Gather (⦃ g ⦄ j jn) x)).
          {
            unfold svector_is_non_collision.
            apply Vforall_nth_intro.
            intros.
            rewrite Gather_spec.
            apply GNC.
          }
          generalize dependent (Gather (⦃ g ⦄ j jn) x).
          intros gx GXD GXNC.
          clear GNC g_dense.

          (* Get rid of lifted kernel, carring over its properties *)
          assert(LD: svector_is_dense (liftM_HOperator (kernel j jn) gx))
            by apply liftM_HOperator_DensityPreserving, GXD.

          assert(KNC: svector_is_non_collision (liftM_HOperator (kernel j jn) gx)).
          {
            apply liftM_HOperator_DenseCauseNoCol, GXNC.
            apply GXD.
          }
          generalize dependent (liftM_HOperator (kernel j jn) gx).
          intros kx KD KNC.
          clear GXD GXNC gx.

          (* Get rid of Scatter  *)
          assert(SNC: svector_is_non_collision (@Scatter ko o (family_f ko o (S n) f j jn)
                                                         (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx)).

          apply ScatterCollisionFree, KNC.
          generalize dependent (@Scatter ko o (family_f ko o (S n) f j jn)
                                         (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx).
          intros sx SNC.
          unfold svector_is_non_collision in SNC.
          apply Vforall_nth with (ip:=oic) in SNC.
          apply SNC.
        +
          unfold Vunique.
          intros i0 ic j jc.

          rewrite 2!Vbuild_nth.
          unfold compose.

          (* Get rid of Gather, carring over its properties *)
          assert(GXDi0: svector_is_dense (Gather (⦃ g ⦄ i0 ic) x)).
          {
            unfold svector_is_dense.
            apply Vforall_nth_intro.
            intros.
            rewrite Gather_spec.
            apply g_dense.
          }
          generalize dependent (Gather (⦃ g ⦄ i0 ic) x).
          intros gxi0 GXDi0.

          assert(GXDj: svector_is_dense (Gather (⦃ g ⦄ j jc) x)).
          {
            unfold svector_is_dense.
            apply Vforall_nth_intro.
            intros.
            rewrite Gather_spec.
            apply g_dense.
          }
          generalize dependent (Gather (⦃ g ⦄ j jc) x).
          intros gxj GXDj.
          clear GNC g_dense.

          (* Get rid of lifted kernel, carring over its properties *)
          assert(svector_is_dense (@liftM_HOperator ki ko (kernel i0 ic) (Koperator i0 ic) gxi0)) by apply liftM_HOperator_DensityPreserving, GXDi0.
          generalize dependent (@liftM_HOperator ki ko (kernel i0 ic) (Koperator i0 ic) gxi0).
          intros kxi KXDi0.
          clear gxi0 GXDi0.

          assert (svector_is_dense (@liftM_HOperator ki ko (kernel j jc) (Koperator j jc) gxj)) by apply liftM_HOperator_DensityPreserving, GXDj.
          generalize dependent (@liftM_HOperator ki ko (kernel j jc) (Koperator j jc) gxj).
          intros kxj KXDj.
          clear gxj GXDj.


          (* housekeeping *)
          clear Koperator g kernel nz x i ki f_sur.
          rename
            i0 into i,
          n into k,
          kxi into x,
          o into n,
          oi into m,
          oic into mc,
          kxj into y,
          KXDj into YD,
          KXDi0 into XD,
          ko into l.

          intros [Hi Hj].

          apply Is_Val_Scatter in Hi; try assumption; clear XD.
          apply Is_Val_Scatter in Hj; try assumption; clear YD.

          elim Hi; clear Hi; intros x0 H.
          elim H; clear H; intros x0c H0.

          elim Hj; clear Hj; intros x1 H.
          elim H; clear H; intros x1c H1.

          subst m;  clear mc.

          unfold index_map_family_injective in f_inj.
          symmetry in H1.
          specialize (f_inj i j ic jc x0 x1 x0c x1c H1).

          apply f_inj.
    Qed.


  (*

    Instance HTDirectSumExpansion_DensityPreserving
             {i1 o1 i2 o2}
             (f: mvector i1 -> mvector o1)
             (g: mvector i2 -> mvector o2)
             `{hop1: !HOperator f}
             `{hop2: !HOperator g}
             `{DP1: !DensityPreserving f}
             `{DP2: !DensityPreserving g}
      : DensityPreserving
          (HTSUMUnion

             ((ScatH 0 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_first_half o1 o2)
              ) ∘ f ∘ (GathH 0 1 (domain_bound := h_bound_first_half i1 i2)))
             ((ScatH o1 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_second_half o1 o2)
              ) ∘ g ∘ (GathH i1 1 (domain_bound := h_bound_second_half i1 i2)))).
    Proof.
      unfold DensityPreserving.
      intros x Dx.
      unfold mvector_is_dense.
      repeat unfold HCompose, compose.
      apply Vforall_nth_intro.
      intros i ip.
      unfold HTSUMUnion.
      unfold GathH.

      (* Generalize Gathers *)
      remember (@Gather (i1 + i2) i2
                        (@h_index_map i2 (i1 + i2) i1 1
                                      (h_bound_second_half i1 i2)) x) as gx1.
      assert(Dxg1: mvector_is_dense gx1).
      {
        subst.
        apply Gather_preserves_density, Dx.
      }
      generalize dependent gx1.
      intros gx1 Heqgx Dxg1. clear Heqgx.

      remember (@Gather (i1 + i2) i1
                        (@h_index_map i1 (i1 + i2) 0 1
                                      (h_bound_first_half i1 i2)) x) as gx2.
      assert(Dxg2: mvector_is_dense gx2).
      {
        subst.
        apply Gather_preserves_density, Dx.
      }
      generalize dependent gx2.
      intros gx2 Heqgx Dxg2. clear Heqgx.
      clear Dx x.

      (* Generalize nested operators' application *)
      assert(mvector_is_dense (f gx2)) by apply DP1, Dxg2.
      generalize dependent (f gx2). intros fgx2 Dfgx2.
      clear Dxg2 gx2 DP1 hop1 f.

      assert(mvector_is_dense (g gx1)) by apply DP2, Dxg1.
      generalize dependent (g gx1). intros ggx1 Dggx1.
      clear Dxg1 gx1 DP2 hop2 g.

      unfold Vec2Union.
      rewrite Vnth_map2.

      unfold ScatH.
      rewrite 2!Scatter_rev_spec.

      destruct (lt_dec i o1).
      assert(ihit:
               is_Some
                 ((partial_index_f (o1 + o2) o1
                                   ((@build_inverse_index_map o1 (o1 + o2)
                                                              (@h_index_map o1 (o1 + o2) 0 1 (h_bound_first_half o1 o2))))
                  ) i)
            ). admit.

      assert(imiss:
               MRtheta_Is_Val
                 (@VnthInverseIndexMapped o1 (o1 + o2) fgx2
                                          (@build_inverse_index_map o1 (o1 + o2)
                                                                    (@h_index_map o1 (o1 + o2) 0 1 (h_bound_first_half o1 o2))) i ip)).
      {
        destruct (partial_index_f (Peano.plus o1 o2) o1
                                  (build_inverse_index_map (h_index_map O (S O))) i) eqn: PFI.
        + unfold VnthInverseIndexMapped.
          simpl in *.
          revert PFI.
          admit.
        + destruct ihit.
      }

      admit.
      admit.
    Qed.
   *)

  End Structural_Correctness.


End SigmaHCOLRewriting.




