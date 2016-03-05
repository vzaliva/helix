
Require Import Spiral.
Require Import Rtheta.
Require Import MRtheta.
Require Import SVector.
Require Import SigmaHCOL.
Require Import HCOL.
Require Import THCOL.
Require Import IndexFunctions.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

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

Local Open Scope hcol_scope. (* for compose *)

Section SigmaHCOLRewriting.

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

    Lemma Is_Struct_Rtheta_SZero:
      Is_Struct Rtheta_SZero.
    Proof.
      unfold Rtheta_SZero.
      unfold Is_Struct.
      simpl.
      trivial.
    Qed.

    Lemma VecUnion_structs:
      ∀ (m : nat) (x : mvector m),
        Vforall Is_MValZero x → Is_MValZero (VecUnion plus x).
    Proof.
      intros m x H.
      unfold VecUnion.
      induction x.
      -
        unfold Is_MValZero, Is_ValZero.
        unfold_MRtheta_equiv.
        reflexivity.
      - simpl in H. destruct H as [Hh Hx].
        Opaque Monad.ret.
        simpl.
        Transparent Monad.ret.
        apply Is_MValZero_to_MSZero in Hh.
        rewrite Hh.
        rewrite Union_Plus_MSZero_r.
        apply IHx, Hx.
    Qed.

    (* Formerly Lemma3 *)
    Lemma SingleValueInZeros m j (x:mvector m) (jc:j<m):
      (forall i (ic:i<m),
          i ≢ j -> Is_MValZero (Vnth x ic)) -> (VecUnion plus x = Vnth x jc).
    Proof.
      intros SZ.
      dependent induction m.
      - dep_destruct x.
        destruct j.
        omega.
        omega.
      -
        dep_destruct x.
        destruct (eq_nat_dec j 0).
        +
          Case ("j=0").
          rewrite Vnth_cons_head; try assumption.
          rewrite VecUnion_cons.
          assert(Vforall Is_MValZero x0).
          {
            apply Vforall_nth_intro.
            intros.
            assert(ipp:S i < S m) by lia.
            replace (Vnth x0 ip) with (Vnth (Vcons h x0) ipp) by apply Vnth_Sn.
            apply SZ; lia.
          }

          assert(UZ: Is_MValZero (VecUnion plus x0))
            by apply VecUnion_structs, H.
          setoid_replace (VecUnion plus x0) with MRtheta_SZero
            by apply Is_ValZero_to_zero, UZ.
          clear UZ.
          apply Union_Plus_MSZero_l.
        +
          Case ("j!=0").
          rewrite VecUnion_cons.
          assert(Zc: 0<(S m)) by lia.

          assert (HS: Is_MValZero h).
          {
            cut (Is_MValZero (Vnth (Vcons h x0) Zc)).
            rewrite Vnth_0.
            auto.
            apply SZ; auto.
          }

          destruct j; try congruence.
          simpl.
          generalize (lt_S_n jc).
          intros l.
          rewrite IHm with (jc:=l).

          setoid_replace h with MRtheta_SZero by apply Is_ValZero_to_zero, HS.
          apply Union_Plus_MSZero_r.

          intros i ic.
          assert(ics: S i < S m) by lia.
          rewrite <- Vnth_Sn with (v:=h) (ip:=ics).
          specialize SZ with (i:=S i) (ic:=ics).
          auto.
    Qed.

    Lemma InverseIndex_1_hit:
      ∀ (n k s : nat) (kp : k < n) (v : MRtheta),
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
      ∀ (n s i j : nat) (ip : i < n) (jp: j<n) (v : MRtheta),
        i ≢ j ->
        @VnthInverseIndexMapped 1 n [v]
                                (@build_inverse_index_map 1 n
                                                          (@h_index_map 1 n j s
                                                                        (ScatH_1_to_n_range_bound j n s jp)
                                ))
                                i ip ≡ MRtheta_SZero.
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

    Lemma U_SAG1:
      ∀ (n : nat) (x : mvector n)
        (f: { i | i<n} -> MRtheta -> MRtheta) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (i : nat) (ip : i < n),
        Vnth
          (SumUnion plus
                    (Vbuild
                       (λ (i0 : nat) (id : i0 < n),
                        ((ScatH i0 1
                                (snzord0:=ScatH_stride1_constr)
                                (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id))
                           ∘ Atomic (f (i0 ↾ id))
                           ∘ (GathH i0 1
                                    (domain_bound:=GathH_j1_domain_bound i0 n id))
                        ) x))) ip
        =
        Vnth (Pointwise f x) ip.
    Proof.
      intros n x f pF i ip.
      unfold HCompose, compose.
      remember (λ (i0 : nat) (id : i0 < n),
                ScatH i0 1 (Atomic (f (i0 ↾ id)) (GathH i0 1 x))) as bf.
      assert(B1: bf ≡ (λ (i0 : nat) (id : i0 < n),
                       ScatH i0 1 (snzord0:=ScatH_stride1_constr) (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id) (Atomic (f (i0 ↾ id)) [Vnth x id]))
            ).
      {
        subst bf.
        extensionality j.
        extensionality jn.
        unfold GathH, Gather.
        rewrite Vbuild_1.
        unfold VnthIndexMapped.
        simpl.
        generalize (h_index_map_obligation_1 1 n j 1
                                             (GathH_j1_domain_bound j n jn) 0 (lt_0_Sn 0)).
        intros ln.
        simpl in ln.
        rewrite Vnth_cast_index with (jc:=jn) by omega.
        reflexivity.
      }
      assert (B2: bf ≡ (λ (i0 : nat) (id : i0 < n),
                        ScatH i0 1 (snzord0:=ScatH_stride1_constr) (range_bound:=ScatH_1_to_n_range_bound i0 n 1 id)  [f (i0 ↾ id) (Vnth x id)])).
      {
        rewrite B1.
        extensionality j.
        extensionality jn.
        unfold Atomic.
        reflexivity.
      }
      rewrite B2.
      clear B1 B2 Heqbf bf.

      unfold Pointwise.
      rewrite Vbuild_nth.

      (* Lemma5 emebdded below *)
      rewrite AbsorbUnionIndex by solve_proper.
      rewrite Vmap_Vbuild.

      (* Preparing to apply Lemma3. Prove some peoperties first. *)
      remember (Vbuild
                  (λ (z : nat) (zi : z < n), Vnth (ScatH z 1 [f (z ↾ zi) (Vnth x zi)]) ip)) as b.

      assert
        (L3pre: forall ib (icb:ib<n),
            ib ≢ i -> Is_MValZero (Vnth b icb)).
      {
        intros ib icb.
        subst.
        rewrite Vbuild_nth.
        unfold ScatH, Scatter.
        rewrite Vbuild_nth.
        intros H.
        rewrite InverseIndex_1_miss.
        apply SZero_is_ValZero.
        auto.
      }
      rewrite SingleValueInZeros with (j:=i) (jc:=ip) by apply L3pre.
      subst b.
      rewrite Vbuild_nth.
      unfold ScatH, Scatter.
      rewrite Vbuild_nth.
      rewrite InverseIndex_1_hit.
      reflexivity.
    Qed.

    Lemma U_SAG1_PW:
      forall n (x:mvector n)
        (f: { i | i<n} -> MRtheta -> MRtheta) `{pF: !Proper ((=) ==> (=) ==> (=)) f},
        SumUnion plus
                 (@Vbuild (mvector n) n
                          (fun i id =>
                             (
                               (ScatH i 1
                                      (snzord0:=ScatH_stride1_constr)
                                      (range_bound:=ScatH_1_to_n_range_bound i n 1 id))
                                 ∘ (Atomic (f (i ↾ id)))
                                 ∘ (GathH i 1
                                          (domain_bound:=GathH_j1_domain_bound i n id)
                                   )
                             ) x
                 ))
        =
        Pointwise f x.
    Proof.
      intros n x f pF.
      apply Vforall2_intro_nth.
      intros i ip.
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
      ∀ (n : nat) (x : mvector (n + n))
        (f : nat -> MRtheta → MRtheta → MRtheta)
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
      ∀ (n : nat) (x : mvector (n + n))
        (f: nat -> MRtheta -> MRtheta -> MRtheta)
        `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (k : nat) (kp : k < n),
        Vnth
          (SumUnion plus
                    (@Vbuild (mvector n) n
                             (fun i id =>
                                ((ScatH i 1
                                        (snzord0:=ScatH_stride1_constr)
                                        (range_bound:=ScatH_1_to_n_range_bound i n 1 id))
                                   ∘ (HBinOp (o:=1) (SwapIndex2 i f))
                                   ∘ (GathH i n
                                            (domain_bound:=GathH_jn_domain_bound i n id))
                                ) x
          ))) kp
        = Vnth (HBinOp (o:=n) (f) x) kp.
    Proof.
      intros n x f f_mor k kp.
      unfold HCompose, compose.

      remember (fun i id =>
                  ScatH i 1
                        (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                        (HBinOp (o:=1) (SwapIndex2 i f)
                                (GathH i n
                                       (domain_bound:=GathH_jn_domain_bound i n id) x)))
        as bf.

      assert(ILTNN: forall y:nat,  y<n -> y<(n+n)) by (intros; omega).
      assert(INLTNN: forall y:nat,  y<n -> y+n<(n+n)) by (intros; omega).

      assert(B1: bf ≡ (fun i id =>
                         (ScatH i 1
                                (snzord0:=ScatH_stride1_constr)
                                (range_bound:=ScatH_1_to_n_range_bound i n 1 id)
                                (HBinOp (o:=1) (SwapIndex2 i f)
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
                              [ f i (Vnth x (ILTNN i id)) (Vnth x (INLTNN i id)) ])).
      {
        rewrite B1.
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
                   Vnth (ScatH z 1 [f z (Vnth x (ILTNN z zi)) (Vnth x (INLTNN z zi))]) kp)) as b.

      assert
        (L3pre: forall ib (icb:ib<n),
            ib ≢ k -> Is_MValZero (Vnth b icb)).
      {
        intros ib icb.

        subst.
        rewrite Vbuild_nth.
        unfold ScatH, Scatter.
        rewrite Vbuild_nth.
        intros H.
        rewrite InverseIndex_1_miss.
        apply SZero_is_ValZero.
        auto.
      }
      rewrite SingleValueInZeros with (j:=k) (jc:=kp) by apply L3pre.
      subst b.
      rewrite Vbuild_nth.
      unfold ScatH, Scatter.
      rewrite Vbuild_nth.
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
      forall n (x:mvector (n+n))
        (f: nat -> MRtheta -> MRtheta -> MRtheta)
        `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f},
        HBinOp (o:=n) (f) x =
        SumUnion plus
                 (@Vbuild (mvector n) n
                          (fun i id =>
                             (
                               (ScatH i 1
                                      (snzord0:=ScatH_stride1_constr)
                                      (range_bound:=ScatH_1_to_n_range_bound i n 1 id))
                                 ∘ (HBinOp (o:=1) (SwapIndex2 i f))
                                 ∘ (GathH i n
                                          (domain_bound:=GathH_jn_domain_bound i n id)
                                   )
                             ) x
                 )).
    Proof.
      intros n x f pF.
      apply Vforall2_intro_nth.
      intros i ip.
      symmetry.
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

    Lemma Partial_index_in_range:
      ∀ (o1 o2 i : nat) (partial_index_f : nat → option nat),
        partial_index_f
          ≡ (λ y : nat,
                   List.fold_right
                     (λ (x' : nat) (p : option nat),
                      if eq_nat_dec y (o1 + x' * 1) then Some x' else p) None
                     (rev_natrange_list o2))
        → o1 <= i
        → i < o1 + o2
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

    Lemma Partial_index_out_of_range_is_none:
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
          (f: mvector i1 -> mvector o1)
          (g: mvector i2 -> mvector o2)
          `{hop1: !HOperator f}
          `{hop2: !HOperator g}
          (x: mvector (i1+i2)) (* input vector *)
      :
        HTDirectSum f g x =
        (HTSUMUnion
           ((ScatH 0 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_first_half o1 o2)
            ) ∘ f ∘ (GathH 0 1 (domain_bound := h_bound_first_half i1 i2)))
           ((ScatH o1 1 (snzord0:=ScatH_stride1_constr) (range_bound := h_bound_second_half o1 o2)
            ) ∘ g ∘ (GathH i1 1 (domain_bound := h_bound_second_half i1 i2))))
          x.
    Proof.
      unfold HTDirectSum, HCross, THCOLImpl.Cross, HCompose, compose,
      HTSUMUnion, pair2vector.
      break_let. break_let.
      rename t1 into x0, t2 into x1.
      tuple_inversion.
      symmetry.

      assert(LS: @ScatH o1 (o1 + o2) 0 1 (h_bound_first_half o1 o2)
                        (@ScatH_stride1_constr o1 2)
                        (f (@GathH (i1 + i2) i1 0 1 (h_bound_first_half i1 i2) x)) ≡ Vapp (f x0) (szero_mvector o2)).
      {
        replace (@GathH (i1 + i2) i1 0 1 (h_bound_first_half i1 i2) x) with x0.
        -
          unfold ScatH, Scatter.
          apply Veq_nth.
          intros.

          rewrite Vbuild_nth.
          generalize dependent (f x0). intros fx0.
          rewrite Vnth_app.
          break_match.
          + (* Second half of x, which is all zeros *)
            unfold szero_mvector.  rewrite Vnth_const.
            remember ((build_inverse_index_map (h_index_map 0 1))) as h'.
            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped.
            simpl.
            assert (HZI: partial_index_f i ≡ None).
            {
              apply is_None_def.
              apply Partial_index_out_of_range_is_none with (o1:=0) (o2:=o1).
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
              apply Partial_index_in_range with (o2:=o1) (o1:=O).
              assumption.
              omega.
              omega.
              f_equal; omega.
            }
            generalize (partial_index_f_spec i ip) as some_spec.
            rewrite HZI.
            intros.
            replace (some_spec i eq_refl) with g0 by apply proof_irrelevance.
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
                        (g (@GathH (i1 + i2) i2 i1 1 (h_bound_second_half i1 i2) x)) ≡ Vapp (szero_mvector o1) (g x1)).
      {
        replace (@GathH (i1 + i2) i2 i1 1 (h_bound_second_half i1 i2) x) with x1.
        -
          unfold ScatH, Scatter.
          apply Veq_nth.
          intros.
          rewrite Vbuild_nth.
          generalize dependent (g x1). intros gx0.
          rewrite Vnth_app.
          break_match.
          + (* Second half of x, which is gx0 *)
            remember (build_inverse_index_map (h_index_map o1 1)) as h'.
            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped; simpl.
            assert (HZI: partial_index_f i ≡ Some (i-o1))
              by (apply Partial_index_in_range with (o2:=o2); assumption).
            generalize (partial_index_f_spec i ip) as some_spec.
            rewrite HZI.
            intros.
            replace (some_spec (i-o1) eq_refl) with (Vnth_app_aux o2 ip l) by apply proof_irrelevance.
            reflexivity.
          + (* First half of x, which is all zeros *)
            unfold szero_mvector.  rewrite Vnth_const.
            remember ((build_inverse_index_map (h_index_map o1 1))) as h'.
            destruct h'.
            inversion Heqh'. rename H0 into H. clear Heqh'.
            unfold VnthInverseIndexMapped.
            simpl.
            assert (HZI: partial_index_f i ≡ None).
            {
              apply is_None_def.
              apply Partial_index_out_of_range_is_none with (o1:=o1) (o2:=o2).
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
          rewrite Vnth_app.
          break_match.
          generalize (Vnth_app_aux i2
                                   (h_index_map_obligation_1 i2 (i1 + i2) i1 1
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
      setoid_replace (Vmap2 (Union plus) (f x0) (szero_mvector o1)) with (f x0).
      setoid_replace (Vmap2 (Union plus) (szero_mvector o2) (g x1)) with (g x1).
      reflexivity.
      apply Vec2Union_szero_svector_l.
      apply Vec2Union_szero_svector_r.
    Qed.

  End Value_Correctness.

  Section Structural_Correctness.

    (* Strong condition: operator preserves vectors' density *)
    Class DensityPreserving {i o:nat} (op: svector i -> svector o) :=
      o_den_pres : forall x, svector_is_dense x -> svector_is_dense (op x).

    Instance HTDirectSum_DensityPreserving
             {i1 o1 i2 o2}
             (f: svector i1 -> svector o1)
             (g: svector i2 -> svector o2)
             `{hop1: !HOperator f}
             `{hop2: !HOperator g}
             `{DP1: !DensityPreserving f}
             `{DP2: !DensityPreserving g}
      : DensityPreserving (HTDirectSum f g).
    Proof.
      unfold DensityPreserving.
      intros x Dx.
      unfold svector_is_dense.
      unfold HTDirectSum, HCross, compose, THCOLImpl.Cross, pair2vector.
      break_let. break_let.
      tuple_inversion.
      apply Vbreak_dense_vector in Heqp0. destruct Heqp0.
      assert(svector_is_dense (f t1)) by apply DP1, H.
      assert(svector_is_dense (g t2)) by apply DP2, H0.
      apply Vforall_app.
      auto.
      apply Dx.
    Qed.

    (* Weaker condition: applied to dense vector does not produce strucural collisions *)
    Class DenseCauseNoCol {i o:nat} (op: svector i -> svector o) :=
      o_den_non_col : forall x, svector_is_dense x -> svector_is_non_col (op x).

    Instance HTDirectSum_DenseCauseNoCol
             {i1 o1 i2 o2}
             (f: svector i1 -> svector o1)
             (g: svector i2 -> svector o2)
             `{hop1: !HOperator f}
             `{hop2: !HOperator g}
             `{DP1: !DenseCauseNoCol f}
             `{DP2: !DenseCauseNoCol g}
      : DenseCauseNoCol (HTDirectSum f g).
    Proof.
      unfold DenseCauseNoCol.
      intros x Dx.
      unfold svector_is_dense.
      unfold HTDirectSum, HCross, compose, THCOLImpl.Cross, pair2vector.
      break_let. break_let.
      tuple_inversion.
      apply Vbreak_dense_vector in Heqp0. destruct Heqp0.
      assert(svector_is_non_col (f t1)) by apply DP1, H.
      assert(svector_is_non_col (g t2)) by apply DP2, H0.
      apply Vforall_app.
      auto.
      apply Dx.
    Qed.


    Instance HTDirectSumExpansion_DensityPreserving
             {i1 o1 i2 o2}
             (f: svector i1 -> svector o1)
             (g: svector i2 -> svector o2)
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
      unfold DenseCauseNoCol.
      intros x Dx.
      unfold svector_is_non_col, compose, Is_Collision, RthetaIsCollision.
      repeat unfold HCompose, compose.
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
      assert(svector_is_dense (f gx2)) by apply DP1, Dxg2.
      generalize dependent (f gx2). intros fgx2 Dfgx2.
      clear Dxg2 gx2 DP1 hop1 f.

      assert(svector_is_dense (g gx1)) by apply DP2, Dxg1.
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
               Is_Val
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

  End Structural_Correctness.


End SigmaHCOLRewriting.




