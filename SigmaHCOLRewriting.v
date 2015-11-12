
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

  Fact ScatH_j1_domain_bound base o (bc:base<o):
    (base+(pred 1)*1) < o.
  Proof.
    lia.
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
    dependent induction x.
    crush.
    destruct j.
    crush.
    assert(jn' :  j < n) by lia.
    simpl in ln.
    assert(ln' : j + 0 < n) by lia.
    rewrite Vnth_Sn with (ip':=ln').
    rewrite Vnth_Sn with (ip':=jn').
    apply IHx.
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


  Lemma InverseIndex_h_j1_not_j:
    ∀ (n i ib : nat) (ip : i < n) (ibd: ib<n) (v : Rtheta),
      VnthInverseIndexMapped [v]
                             (IndexFunctions.build_inverse_index_map
                                (IndexFunctions.h_index_map ib 1
                                                            (range_bound := ScatH_j1_domain_bound ib n ibd)
                                                            (snz := One_ne_Zero)
                             ))
                             i ip ≡ Rtheta_szero.
  Proof .
    admit.
  Qed.
  
  Lemma InverseIndex_h_j1_j:
    ∀ (n i : nat) (ip : i < n) (v : Rtheta),
      VnthInverseIndexMapped [v]
                             (IndexFunctions.build_inverse_index_map
                                (IndexFunctions.h_index_map i 1
                                                            (range_bound := ScatH_j1_domain_bound i n ip)
                                                            (snz := One_ne_Zero)
                             ))
                             i ip ≡ v.
  Proof.
    intros n i ip v.
    destruct (IndexFunctions.build_inverse_index_map (IndexFunctions.h_index_map i 1))
             as [h' h'_spec]
             eqn:P.
    unfold IndexFunctions.h_index_map in P.
    inversion P.

    assert(PH': h' i ≡ Some 0).
    {
      rewrite <- H0.
      simpl.
      destruct (eq_nat_dec i (i + 0)).
      reflexivity.
      omega.
    }
    unfold VnthInverseIndexMapped.
    simpl (IndexFunctions.partial_index_f n 1
       {|
       IndexFunctions.partial_index_f := h';
       IndexFunctions.partial_index_f_spec := h'_spec |}).
    admit.
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
                       (domain_bound:=ScatH_j1_domain_bound i0 n id))
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
                  ScatH i0 1 (snz:=One_ne_Zero) (domain_bound:=ScatH_j1_domain_bound i0 n id) (Atomic (f i0 id) [Vnth x id]))
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
                  ScatH i0 1 (snz:=One_ne_Zero) (domain_bound:=ScatH_j1_domain_bound i0 n id)  [f i0 id (Vnth x id)])).
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
      rewrite InverseIndex_h_j1_j with (n:=n) (i:=i) (ip:=ip).
      cut(Is_Val (Vnth x icb)); try crush.
      apply Vforall_nth with (i:=i) (ip:=icb) in V.
      apply V.

      intros H.
      rewrite InverseIndex_h_j1_not_j with (n:=n) (i:=i) (ip:=ip).
      apply Is_StructNonErr_Rtheta_szero.
    }
    rewrite Lemma3 with (j:=i) (jc:=ip).
    subst b.
    rewrite Vbuild_nth.
    unfold ScatH, Scatter.
    rewrite Vbuild_nth.
    generalize  (f i ip (Vnth x ip)) as v.
    intros v.
    apply InverseIndex_h_j1_j.
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
                             (domain_bound:=ScatH_j1_domain_bound i n id)) 
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
  



  

















  (* --------------- OLD STUFF BELOW ------------------ *)
  
  (* Inductive definition of sparse vector which has at most one non-empty element. It is called "VecOptUnionCompSvector compatible" *)
  Inductive VecOptUnionCompSvector {B}: forall {n} (v: svector B n), Prop :=
  | VecOptUnionCompSvector_nil: VecOptUnionCompSvector []
  | VecOptUnionCompSvector_none {n} (v: svector B n): VecOptUnionCompSvector v -> VecOptUnionCompSvector (None::v)
  | VecOptUnionCompSvector_some {x} {n} (v: svector B n): Vforall is_None v -> VecOptUnionCompSvector (Some x::v).

  Lemma VecOptUnionCompSvector_spec {B} {n} {x:svector B n}:
    VecOptUnionCompSvector x ->
    forall i j (ic:i< n) (jc:j<n), (Vnth x ic ≢ None) /\ (Vnth x jc ≢ None) -> i ≡ j.
  Proof.
    intros V i j ic jc U.
    destruct U as [Ui Uj].
    dependent induction V.
    destruct i, j; crush.

    destruct i, j.
    reflexivity.
    + rewrite Vnth_0 in Ui.
      simpl in Ui.
      none_some_elim.
    + rewrite Vnth_0 in Uj.
      simpl in Uj.
      none_some_elim.
    +
      assert (ic':i < n) by omega.
      assert (jc':j < n) by omega.
      f_equal.
      apply IHV with (ic:=ic') (jc:=jc').
      simpl in Ui.
      replace (lt_S_n ic) with ic' in Ui by apply proof_irrelevance.
      assumption.
      simpl in Uj.
      replace (lt_S_n jc) with jc' in Uj by apply proof_irrelevance.
      assumption.
    +
      destruct i, j.
      - reflexivity.
      - simpl in Uj.
        assert (jc':j < n) by omega.
        replace (lt_S_n jc) with jc' in Uj by apply proof_irrelevance.
        apply Vforall_nth with (ip:=jc') in H.
        rewrite is_None_def in H.
        congruence.
      - simpl in Ui.
        assert (ic':i < n) by omega.
        replace (lt_S_n ic) with ic' in Ui by apply proof_irrelevance.
        apply Vforall_nth with (ip:=ic') in H.
        rewrite is_None_def in H.
        congruence.
      - simpl in Uj.
        assert (jc':j < n) by omega.
        replace (lt_S_n jc) with jc' in Uj by apply proof_irrelevance.
        apply Vforall_nth with (ip:=jc') in H.
        rewrite is_None_def in H.
        congruence.
  Qed.


  Lemma VecOptionUnion_Cons_None:
    ∀ (m : nat) (x : vector (option A) (S m)),
      VecOptUnion (Vcons None x) ≡ VecOptUnion x.
  Proof.
    intros m x.
    rewrite VecOptionUnion_cons.
    simpl.
    destruct (VecOptUnion x); reflexivity.
  Qed.

  Lemma SparseUnion_Cons_None:
    ∀ (n : nat) (x : vector (option A) n), SparseUnion (Vconst None n) x ≡ x.
  Proof.
    intros n x.
    induction x.
    auto.
    destruct h;
    (simpl;
     rewrite IHx;
     reflexivity).
  Qed.

  
  (* Unary union of vector where all except exactly one element are "structural zero", and one is unknown, is the value of this element  *)
  Lemma Lemma3 m j (x:svector A (S m)) (jc:j<(S m)):
      (forall i (ic:i<(S m)) (inej: i ≢ j), is_None (Vnth x ic)) -> (VecOptUnion x ≡ Vnth x jc).
  Proof.
    intros SZ.

    dependent induction m.
    - dep_destruct x.
      dep_destruct x0.
      destruct j; crush.
      (* got IHm *)

    - dep_destruct x.
      destruct (eq_nat_dec j 0).
      +
        rewrite Vnth_cons_head; try assumption.
        unfold VecOptUnion.
        simpl.
        
        assert(Vforall is_None x0).
        {
          apply Vforall_nth_intro.
          intros.
          assert(ipp:S i < S (S m)) by lia.
          replace (Vnth x0 ip) with (Vnth (Vcons h x0) ipp) by apply Vnth_Sn.
          apply SZ; lia.
        }

        apply Vfold_OptionUnion_empty; assumption.
      +
        assert(Zc: 0<(S (S m))) by lia.
        assert (H0: is_None (Vnth (Vcons h x0) Zc))
          by (apply SZ; auto).
        rewrite Vnth_0 in H0. simpl in H0.
        rewrite is_None_def in H0.
        subst h.

        rewrite VecOptionUnion_Cons_None.
        
        destruct j as [j0|js]; try congruence.
        assert(jcp : js < S m) by lia.
        rewrite Vnth_Sn with (ip':=jcp).

        rewrite <-IHm.
        reflexivity.
        intros i ic inej.

        assert(ics: (S i) < S (S m)) by lia.
        rewrite <- Vnth_Sn with (v:=None) (ip:=ics).
        apply SZ.
        auto.
  Qed.

  Lemma SparseUnionWithEmpty:
    ∀ (m : nat) (x : vector (option A) m), SparseUnion (szero_svector m) x ≡ x.
  Proof.
    intros m x.
    induction x.
    auto.
    destruct h;
    (simpl;
    rewrite SparseUnion_Cons_None; reflexivity).
  Qed.

  Lemma AbsorbUnionIndexBinary:
    ∀ (m k : nat) (kc : k < m) (h t : vector (option A) m),
      Vnth (SparseUnion t h) kc ≡ OptionUnion (Vnth t kc) (Vnth h kc).
  Proof.
    intros m k kc h t.
    unfold SparseUnion.
    apply Vnth_map2.
  Qed.

  Lemma Lemma2:
    forall var st m n (x: vector (svector A m) n) k (kc: k<(m*n)), exists i (ic:i<n) j (jc:j<m),
        Vnth (Vnth x ic) jc ≡ Vnth
                                (Vfold_left SparseUnion (szero_svector (m * n))
                                            (Vbuild 
                                               (fun (i : nat) (ic : i < n) =>
                                                  evalScatH (update st var i)
                                                            (AMult (AValue var) (AConst m)) 
                                                            (AConst 1)
                                                            (Vnth x ic)
                                ))) kc.
  Proof.
    intros var st m n x k kc.
  Qed.
  
  Section SigmaHCOLRewriting.
    