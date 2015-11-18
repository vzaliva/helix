
Require Import Spiral.
Require Import Rtheta.
Require Import SigmaHCOL.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program. 

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Section SigmaHCOLRewriting.
  Context

    `{Ae: Equiv A}
    `{Az: Zero A} `{A1: One A}
    `{Aplus: Plus A} `{Amult: Mult A} 
    `{Aneg: Negate A}
    `{Ale: Le A}
    `{Alt: Lt A}
    `{Ato: !@TotalOrder A Ae Ale}
    `{Aabs: !@Abs A Ae Ale Az Aneg}
    `{Asetoid: !@Setoid A Ae}
    `{Aledec: !∀ x y: A, Decision (x ≤ y)}
    `{Aeqdec: !∀ x y, Decision (x = y)}
    `{Altdec: !∀ x y: A, Decision (x < y)}
    `{Ar: !Ring A}
    `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
    `{ASSO: !@StrictSetoidOrder A Ae Alt}
  .
  
  Add Ring RingA: (stdlib_ring_theory A).
  
  Open Scope vector_scope.
  Global Open Scope nat_scope.

  Fact ScatH_1_to_n_domain_bound base o stride:
    base < o ->
    (base+(pred 1)*stride) < o.
  Proof.
    intros bo.
    omega.
  Qed.

  
  Fact GathH_j1_range_bound base i (bc:base<i):
    (base+(pred 1)*1) < i.
  Proof.
    lia.
  Qed.
    
  Lemma Vnth_cast_i_plus_0:
    ∀ (n : nat) (x : vector Rtheta n) (j : nat) (jn : j < n) 
      (ln : j + 0 < n), Vnth x ln ≡ Vnth x jn.
  Proof.
    intros n x j jn ln. 
    apply Vnth_cast_index.
    omega.
  Qed.

  Lemma VecUnion_cons:
    ∀ m x (xs : svector m),
      VecUnion (Vcons x xs) ≡ Union (VecUnion xs) x.
  Proof.
    intros m x xs.
    unfold VecUnion.
    rewrite Vfold_left_cons.
    reflexivity.
  Qed.

  Lemma SumUnion_cons m n (x: svector m) (xs: vector (svector m) n):
    SumUnion (Vcons x xs) ≡ Vec2Union (SumUnion xs) x.
  Proof.
    unfold SumUnion.
    apply Vfold_left_cons.
  Qed.

  Lemma AbsorbUnionIndexBinary:
    ∀ (m k : nat) (kc : k < m) (a b : svector m),
      Vnth (Vec2Union a b) kc ≡ Union (Vnth a kc) (Vnth b kc).
  Proof.
    intros m k kc a b.
    unfold Vec2Union.
    apply Vnth_map2.
  Qed.

  Lemma AbsorbUnionIndex:
    forall m n (x: vector (svector m) n) k (kc: k<m),
      Vnth (SumUnion x) kc ≡ VecUnion (Vmap (fun v => Vnth v kc) x).
  Proof.
    intros m n x k kc.
    induction n.
    + dep_destruct x.
      unfold VecUnion, SumUnion,szero_svector; simpl.
      apply Vnth_const.
    + dep_destruct x.
      rewrite Vmap_cons, SumUnion_cons, AbsorbUnionIndexBinary, IHn, VecUnion_cons, Union_comm.
      reflexivity.
  Qed.
  
  (* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbIUnionIndex:
    forall m n (x: vector (svector m) n) k (kc: k<m),
      Vnth
        (SumUnion
           (Vbuild 
              (fun (i : nat) (ic : i < n) =>
                 (Vnth x ic)
           ))
        ) kc ≡
        VecUnion
        (Vbuild 
           (fun (i : nat) (ic : i < n) =>
              Vnth (Vnth x ic) kc
        )).
  Proof.
    intros m n x k kc.
    
    induction n.
    + dep_destruct x.
      rewrite 2!Vbuild_0.
      unfold VecUnion; simpl.
      unfold SumUnion; simpl.
      unfold szero_svector; apply Vnth_const.

    +
      dep_destruct x.
      remember (λ (i : nat) (ic : i < (S n)), Vnth (Vcons h x0) ic) as geni.
      remember (λ (i : nat) (ic : i < (S n)), Vnth (geni i ic) kc) as genik.

      (* RHS massaging *)
      rewrite Vbuild_cons with (gen:=genik).
      replace (genik 0 (lt_0_Sn n)) with (Vnth h kc)
        by (subst genik geni; reflexivity).
      rewrite VecUnion_cons.

      replace (λ (i : nat) (ip : i < n), genik (S i) (lt_n_S ip)) with
      (λ (i : nat) (ic : i < n), Vnth (Vnth x0 ic) kc).
      
      rewrite <- IHn.
      remember (λ (i : nat) (ic : i < n), Vnth x0 ic) as genX.

      rewrite Vbuild_cons with (gen:=geni).
      replace (geni 0 (lt_0_Sn n)) with h
        by (subst geni; reflexivity).
      subst geni.
      replace (λ (i : nat) (ip : i < n), Vnth (Vcons h x0) (lt_n_S ip)) with genX.
      rewrite SumUnion_cons.
      rewrite AbsorbUnionIndexBinary.
      reflexivity.
      
      subst genX.
      extensionality i.
      extensionality ic.
      simpl.
      rewrite NatUtil.lt_Sn_nS.
      reflexivity.

      extensionality i.
      extensionality ic.
      subst genik geni.
      simpl.
      rewrite NatUtil.lt_Sn_nS.
      reflexivity.
  Qed.


  Lemma Union_Val_with_Struct:
    ∀ x s , Is_Val x -> Is_StructNonErr s -> Union x s ≡ x.
  Proof.
    intros x s V S.
    unfold Is_Val, Is_StructNonErr, Is_Struct, Is_SErr in *.
    destruct V, S.
    destruct_Rtheta x.
    destruct_Rtheta s.
    destruct x1, x2, s1, s2; crush.
  Qed.

  Lemma Union_Struct_with_Val:
    ∀ x s , Is_Val x -> Is_StructNonErr s -> Union s x ≡ x.
  Proof.
    intros x s V S.
    unfold Is_Val, Is_StructNonErr, Is_Struct, Is_SErr in *.
    destruct V, S.
    destruct_Rtheta x.
    destruct_Rtheta s.
    destruct x1, x2, s1, s2; crush.
  Qed.

  
  Lemma Is_Struct_Rtheta_szero:
    Is_Struct Rtheta_szero.
  Proof.
    unfold Rtheta_szero.
    unfold Is_Struct, RthetaIsStruct.
    simpl.
    trivial.
  Qed.


  Lemma Is_StructNonErr_Rtheta_szero:
    Is_StructNonErr Rtheta_szero.
  Proof.
    unfold Is_StructNonErr.
    split.
    apply Is_Struct_Rtheta_szero.
    crush.
  Qed.
  
  Lemma VecUnion_structs:
    ∀ (m : nat) (x : svector m),
      Vforall Is_StructNonErr x → VecUnion x ≡ Rtheta_szero.
  Proof.
    intros m x H.
    unfold VecUnion.
    induction x.
    crush.
    simpl.
    rewrite IHx.
    simpl in H. destruct H as [Hh Hx].
    unfold Is_Val, Is_StructNonErr, Is_Struct, Is_SErr in Hh.
    destruct Hh.
    
    destruct_Rtheta h.
    unfold Rtheta_szero.
    destruct h1, h2; crush.
    apply H.
  Qed.

  
  Lemma Vfold_OptionUnion_val_with_empty:
    ∀ (m : nat) (h : Rtheta) (x : svector m),
      Is_Val h -> Vforall Is_StructNonErr x → Vfold_left Union h x ≡ h.
  Proof.
    intros m h x V E.
    induction x.
    auto.
    simpl.
    simpl in E. destruct E as [Eh Ex].
    rewrite IHx; try assumption.
    rewrite Union_Val_with_Struct; try assumption.
    reflexivity.
  Qed.
    
  Lemma Lemma3 m j (x:svector m) (jc:j<m):
    (forall i (ic:i<m),
        (i ≡ j -> Is_Val (Vnth x ic)) /\ (i ≢ j -> Is_StructNonErr (Vnth x ic)))
    -> (VecUnion x ≡ Vnth x jc).
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

        assert(Vforall Is_StructNonErr x0).
        {
          apply Vforall_nth_intro.
          intros.
          assert(ipp:S i < S m) by lia.
          replace (Vnth x0 ip) with (Vnth (Vcons h x0) ipp) by apply Vnth_Sn.
          apply SZ; lia.
        }
        
        assert(Is_Val h).
        {
          specialize SZ with (i:=j) (ic:=jc).
          destruct SZ as [SZ0 SZ1].
          subst j.
          simpl in *.
          apply SZ0.
          reflexivity.
        }
        rewrite VecUnion_structs.
        apply Union_Struct_with_Val.
        assumption.
        apply Is_StructNonErr_Rtheta_szero.
        assumption.
      +
        Case ("j!=0").
        rewrite VecUnion_cons.
        assert(Zc: 0<(S m)) by lia.

        assert (HS: Is_StructNonErr h).
        {
          cut (Is_StructNonErr (Vnth (Vcons h x0) Zc)).
          rewrite Vnth_0.
          auto.
          apply SZ; auto.
        }

        destruct j; try congruence.
        simpl.
        generalize (lt_S_n jc).
        intros l.
        rewrite IHm with (jc:=l).

        assert(Is_Val (Vnth x0 l)).
        {
          assert(ics: S j < S m) by lia.
          specialize SZ with (i:=S j) (ic:=ics).
          destruct SZ as [SZ0 SZ1].
          simpl in *.
          replace (lt_S_n ics) with l in SZ0 by apply proof_irrelevance.
          apply SZ0.
          reflexivity.
        }
        rewrite Union_comm.
        apply Union_Struct_with_Val; assumption.

        intros i ic.
        assert(ics: S i < S m) by lia.
        rewrite <- Vnth_Sn with (v:=h) (ip:=ics).
        specialize SZ with (i:=S i) (ic:=ics).
        crush.
  Qed.


  Lemma InverseIndex_1_hit:
    ∀ (n k s : nat) (kp : k < n) (v : Rtheta) {snz:s ≢ 0},
      (@VnthInverseIndexMapped 1 n [v]
           (@IndexFunctions.build_inverse_index_map 1 n
                 (@IndexFunctions.h_index_map 1 n k s
                     (ScatH_1_to_n_domain_bound k n s kp) snz)) k kp) ≡ v.
  Proof.
    intros n k s kp v snz.
    destruct (@IndexFunctions.build_inverse_index_map 1 n
        (@IndexFunctions.h_index_map 1 n k s
           (ScatH_1_to_n_domain_bound k n s kp) snz)) as [h' h'_spec] eqn:P.
    unfold IndexFunctions.h_index_map in P.
    inversion P. rename H0 into HH. symmetry in HH. clear P.
    assert(PH': h' k ≡ Some 0).
    {
      subst h'.
      break_if; [reflexivity | omega].
    }
    unfold VnthInverseIndexMapped, IndexFunctions.partial_index_f, IndexFunctions.partial_index_f_spec.
    generalize (h'_spec k).
    destruct (h' k); crush.
  Qed.

  Lemma InverseIndex_1_miss:
    ∀ (n s i j : nat) (ip : i < n) (jp: j<n) (v : Rtheta) {snz: s ≢ 0},
      i ≢ j ->
      @VnthInverseIndexMapped 1 n [v]
                              (@IndexFunctions.build_inverse_index_map 1 n
                                                                       (@IndexFunctions.h_index_map 1 n j s
                                                                                                    (ScatH_1_to_n_domain_bound j n s jp)
                                                             snz
                             ))
                             i ip ≡ Rtheta_szero.
  Proof .
    intros n s i j ip jp v snz N.
    destruct (@IndexFunctions.build_inverse_index_map 1 n
                                                                       (@IndexFunctions.h_index_map 1 n j s
                                                                                                    (ScatH_1_to_n_domain_bound j n s jp)
                                                             snz
                             )) as [h' h'_spec] eqn:P.
    unfold IndexFunctions.h_index_map in P.
    inversion P. rename H0 into HH. symmetry in HH. 
    assert(PH': h' i ≡ None).
    {
      subst h'.
      break_if ; [omega | reflexivity ].
    }
    assert (N0: i ≢ j + 0) by omega.
    unfold VnthInverseIndexMapped, IndexFunctions.partial_index_f, IndexFunctions.partial_index_f_spec.
    generalize (h'_spec i).
    destruct (h' i); crush.
  Qed.

  Lemma U_SAG1:
    ∀ (n : nat) (x : vector Rtheta n) (f : ∀ i : nat, i < n → Rtheta → Rtheta)
      (i : nat) (ip : i < n),
      Vforall Is_Val x ->
      (forall i (ic: i<n) y, Is_Val y -> Is_Val (f i ic y)) ->
      Vnth
        (SumUnion
           (Vbuild
              (λ (i0 : nat) (id : i0 < n),
               ((ScatH i0 1
                       (snz:=One_ne_Zero)
                       (domain_bound:=ScatH_1_to_n_domain_bound i0 n 1 id))
                  ∘ Atomic (f i0 id)
                  ∘ (GathH i0 1
                           (snz:=One_ne_Zero)
                           (range_bound:=GathH_j1_range_bound i0 n id))
               ) x))) ip
      ≡
      Vnth (Pointwise f x) ip.
  Proof.
    intros n x f i ip V F.
    unfold compose.

    remember (λ (i0 : nat) (id : i0 < n),
              ScatH i0 1 (Atomic (f i0 id) (GathH i0 1 x))) as bf.
    assert(B1: bf ≡ (λ (i0 : nat) (id : i0 < n),
                  ScatH i0 1 (snz:=One_ne_Zero) (domain_bound:=ScatH_1_to_n_domain_bound i0 n 1 id) (Atomic (f i0 id) [Vnth x id]))
           ).
    
    {
      subst bf.
      extensionality j.
      extensionality jn.
      unfold GathH.
      unfold Gather.
      rewrite Vbuild_1.
      unfold VnthIndexMapped.
      simpl.
      generalize (IndexFunctions.h_index_map_obligation_1 1 n j 1
                                                          (GathH_j1_range_bound j n jn) One_ne_Zero 0 (lt_0_Sn 0)).
      intros ln.
      simpl in ln.
      rewrite Vnth_cast_i_plus_0 with (jn:=jn).
      reflexivity.
    }
    assert (B2: bf ≡ (λ (i0 : nat) (id : i0 < n),
                  ScatH i0 1 (snz:=One_ne_Zero) (domain_bound:=ScatH_1_to_n_domain_bound i0 n 1 id)  [f i0 id (Vnth x id)])).
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
    rewrite AbsorbUnionIndex.
    rewrite Vmap_Vbuild.

    (* Preparing to apply Lemma3. Prove some peoperties first. *)
    remember (Vbuild
                (λ (z : nat) (zi : z < n), Vnth (ScatH z 1 [f z zi (Vnth x zi)]) ip)) as b.

    assert
      (L3pre: forall ib (icb:ib<n),
          (ib ≡ i -> Is_Val (Vnth b icb)) /\ (ib ≢ i -> Is_StructNonErr (Vnth b icb))).
    {
      intros ib icb.

      subst.
      rewrite Vbuild_nth.
      unfold ScatH, Scatter.
      rewrite Vbuild_nth.
      split.

      intros H.
      subst ib.
      remember (f i icb (Vnth x icb)) as v eqn: W.
      replace ip with icb by apply proof_irrelevance.
      rewrite InverseIndex_1_hit.
      cut(Is_Val (Vnth x icb)); try crush.
      apply Vforall_nth with (i:=i) (ip:=icb) in V.
      apply V.

      intros H.
      rewrite InverseIndex_1_miss. 
      apply Is_StructNonErr_Rtheta_szero.
      auto.
    }
    rewrite Lemma3 with (j:=i) (jc:=ip).
    subst b.
    rewrite Vbuild_nth.
    unfold ScatH, Scatter.
    rewrite Vbuild_nth.
    apply InverseIndex_1_hit. 
    assumption.
  Qed.

  Theorem U_SAG1_PW:
    forall n (x:svector n) (f: forall i, i<n -> Rtheta -> Rtheta),
      Vforall Is_Val x ->
      (forall i (ic: i<n) y, Is_Val y -> Is_Val (f i ic y)) ->
      SumUnion
        (@Vbuild (svector n) n
                 (fun i id =>
                    (
                      (ScatH i 1
                             (snz:=One_ne_Zero)
                             (domain_bound:=ScatH_1_to_n_domain_bound i n 1 id)) 
                        ∘ (Atomic (f i id)) 
                        ∘ (GathH i 1
                                 (snz:=One_ne_Zero)
                                 (range_bound:=GathH_j1_range_bound i n id)
                          )
                    ) x
        ))
      ≡
      Pointwise f x.
  Proof.
    intros n x f V F.
    apply vec_eq_elementwise.
    apply Vforall2_intro_nth.
    intros i ip.
    apply U_SAG1; assumption.
  Qed.

  Fact GathH_jn_range_bound i n:
    i < n ->
    n ≢ 0 ->
    (i+(pred 2)*n) < (n+n).
  Proof.
    nia.
  Qed.
  
  Lemma Vnth_cast_i_plus_n0_lt_n_plus_nn:
    ∀ (n : nat) (x : vector Rtheta (n+n)) (j : nat) (nnz : n ≢ 0) (jn : j + n < n + n) 
      (ln : j + (n + 0) < n+n), Vnth x ln ≡ Vnth x jn.
  Proof.
    intros n x j nnz jn ln.
    apply Vnth_cast_index.
    omega.
  Qed.

  Lemma Pointwise2_nth:
    ∀ (n : nat) (x : vector Rtheta (n + n)) (f : Rtheta → Rtheta → Rtheta)
      (k : nat) (kp : k < n) (kn: k < n + n) (knn: k + n < n + n) (nnz : n ≢ 0),
      Vnth (Pointwise2 f x) kp ≡ f (Vnth x kn) (Vnth x knn).
  Proof.
    intros n x f k kp kn knn nnz.
    unfold Pointwise2.
    break_let.  rename t into a. rename t0 into b.
    rewrite Vnth_map2.
    assert(A: Vnth a kp ≡ Vnth x kn).
    {
      admit.
    }
    assert(B: Vnth b kp ≡ Vnth x knn). 
    {
      admit.
    }
    rewrite A, B.
    reflexivity.
  Qed.
  
  Lemma U_SAG2:
    ∀ (n : nat) (x : vector Rtheta (n + n)) (f : Rtheta → Rtheta → Rtheta)
      (nnz : n ≢ 0) (k : nat) (kp : k < n),
      Vforall Is_Val x
      → (∀ a b : Rtheta, Is_Val a → Is_Val b → Is_Val (f a b))
      → Vnth
          (SumUnion
             (Vbuild
                (λ (i : nat) (id : i < n),
                 ((ScatH i n
                         (snz:=nnz)
                         (domain_bound:=ScatH_1_to_n_domain_bound i n n id))
                    ∘ (Pointwise2 (n:=1) f)
                    ∘ (GathH i n
                             (range_bound:=GathH_jn_range_bound i n id nnz)
                             (snz:=nnz))
                 ) x))) kp
          ≡ Vnth (Pointwise2 f x) kp.
  Proof.
    intros n x f nnz k kp V F.
    unfold compose.

    remember (λ (i : nat) (id : i < n),
              ScatH (o:=n) i n
                    (domain_bound:=ScatH_1_to_n_domain_bound i n n id)
                    (snz:=nnz)
                    (Pointwise2 (n:=1) f (
                                  GathH i n x
                                        (range_bound:=GathH_jn_range_bound i n id nnz)
                                        (snz:=nnz)
             ))) as bf.

    assert(ILTNN: forall y:nat,  y<n -> y<(n+n)) by (intros; omega).
    assert(INLTNN: forall y:nat,  y<n -> y+n<(n+n)) by (intros; omega).

    assert(B1: bf ≡ (λ (i : nat) (id : i < n), ScatH (o:=n) i n
                                                     (domain_bound:=ScatH_1_to_n_domain_bound i n n id)
                                                     (snz:=nnz)
                                                     (Pointwise2 (n:=1) f
                                                                 [
                                                                   (Vnth x (ILTNN i id));
                                                                   (Vnth x (INLTNN i id))
          ]))).
    {
      subst bf.
      extensionality j.
      extensionality jn.
      unfold GathH.
      unfold Gather.
      rewrite Vbuild_2.
      unfold VnthIndexMapped.
      generalize
        (IndexFunctions.index_f_spec 2 (n + n) (@IndexFunctions.h_index_map 2 (n + n) j n (GathH_jn_range_bound j n jn nnz) nnz) 0  (lt_0_SSn 0)) as l0
                                                                                                                                                     , (IndexFunctions.index_f_spec 2 (n + n) (@IndexFunctions.h_index_map 2 (n + n) j n (GathH_jn_range_bound j n jn nnz) nnz) 1  (lt_1_SSn 0)) as l1,  (ILTNN j jn) as l00, (INLTNN j jn) as l01.
      intros.
      simpl in *.
      rewrite Vnth_cast_i_plus_0 with (jn:=l00) (ln:=l0).
      rewrite Vnth_cast_i_plus_n0_lt_n_plus_nn with (jn:=l01) (ln:=l1).
      reflexivity.
      assumption.
    }
    
    assert (B2: bf ≡ (λ (i : nat) (id : i < n), ScatH (o:=n) i n
                                                      (domain_bound:=ScatH_1_to_n_domain_bound i n n id)
                                                      (snz:=nnz)
                                                      [ f  (Vnth x (ILTNN i id))
                                                           (Vnth x (INLTNN i id)) ]
           )).
    {
      rewrite B1.
      extensionality j.
      extensionality jn.
      unfold Pointwise2.
      reflexivity.
    }
    rewrite B2.
    clear B1 B2 Heqbf bf.

    (* Lemma5 embedded below*)

    rewrite AbsorbUnionIndex.
    rewrite Vmap_Vbuild.

    (* Preparing to apply Lemma3. Prove some peoperties first. *)
    remember (Vbuild
        (λ (z : nat) (zi : z < n),
         Vnth (ScatH z n [f (Vnth x (ILTNN z zi)) (Vnth x (INLTNN z zi))]) kp)) as b.

    assert
      (L3pre: forall ib (icb:ib<n),
          (ib ≡ k -> Is_Val (Vnth b icb)) /\ (ib ≢ k -> Is_StructNonErr (Vnth b icb))).
    {
      intros ib icb.

      subst.
      rewrite Vbuild_nth.
      unfold ScatH, Scatter.
      rewrite Vbuild_nth.
      split.

      intros H.
      subst ib.
      replace icb with kp by apply proof_irrelevance.
      remember (f (Vnth x (ILTNN k kp)) (Vnth x (INLTNN k kp))) as v eqn: W.
      rewrite InverseIndex_1_hit.
      
      assert(Is_Val (Vnth x (ILTNN k kp))); try crush.
      apply Vforall_nth with (i:=k) (ip:=(ILTNN k kp)) in V.
      apply V.

      assert(Is_Val (Vnth x (INLTNN k kp))); try crush.
      apply Vforall_nth with (i:=k+n) (ip:=(INLTNN k kp)) in V.
      apply V.
      
      intros H.
      rewrite InverseIndex_1_miss.
      apply Is_StructNonErr_Rtheta_szero.
      auto.
    }
    rewrite Lemma3 with (j:=k) (jc:=kp).
    subst b.
    rewrite Vbuild_nth.
    unfold ScatH, Scatter.
    rewrite Vbuild_nth.
    rewrite InverseIndex_1_hit.
    symmetry; apply Pointwise2_nth.
    assumption.
    assumption.
  Qed.
  
  Theorem U_SAG_PW2:
    forall n (x:svector (n+n)) (f: Rtheta -> Rtheta -> Rtheta) (nnz: n ≢ 0),
      Vforall Is_Val x ->
      (forall a b, Is_Val a -> Is_Val b -> Is_Val (f a b)) ->
      SumUnion
        (@Vbuild (svector n) n
                 (fun i id =>
                    (
                      (ScatH i n (i:=1) (o:=n)
                             (domain_bound:=ScatH_1_to_n_domain_bound i n n id)
                             (snz:=nnz))
                        ∘ (Pointwise2 f (n:=1)) 
                        ∘ (GathH i n (o:=2)
                                 (range_bound:=GathH_jn_range_bound i n id nnz)
                                 (snz:=nnz))
                    ) x
        ))
        ≡
        Pointwise2 f x.
  Proof.
    intros n x f nnz V F.
    apply vec_eq_elementwise.

    apply Vforall2_intro_nth.
    intros i ip.
    apply U_SAG2; assumption.
  Qed.
  
  Section SigmaHCOLRewriting.
    