
Require Import Spiral.
Require Import SVector.
Require Import AExp.
Require Import HCOL.
Require Import SigmaHCOL.
Import SigmaHCOL_Operators.
Require Import HCOLSyntax.

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

  Lemma Vfold_OptionUnion_empty:
    ∀ (m : nat) (h : option A) (x : vector (option A) m),
      Vforall is_None x → Vfold_left OptionUnion h x ≡ h.
  Proof.
    intros m h x E.
    induction x.
    auto.
    simpl.
    simpl in E. destruct E as [Eh Ex].
    rewrite IHx; try assumption.
    dep_destruct h0; none_some_elim.
    destruct h; auto.
  Qed.
  
  Lemma OptionUnionAssoc:
    forall B (a b c:option B),
      (a ≡ None /\ b ≡ None ) \/
      (a ≡ None  /\ c ≡ None ) \/
      (b ≡ None  /\ c ≡ None ) 
      ->
      OptionUnion (OptionUnion a b) c ≡ OptionUnion (OptionUnion a c) b.
  Proof.
    intros B a b c C.
    destruct a, b, c; crush.
  Qed.

  (* Inductive definition of sparse vector which has at most single non-empty element. It is called "VecOptUnionCompSvector compatible" *)
  Inductive VecOptUnionCompSvector {B}: forall {n} (v: svector B (S n)), Prop :=
  | SingleSome_none {n} (v: svector B (S n)): VecOptUnionCompSvector v -> VecOptUnionCompSvector (None::v)
  | SingleSome_some {x} {n} (v: svector B n): Vforall is_None v -> VecOptUnionCompSvector (Some x::v).

  Lemma VecOptUnionCompSvector_spec {B} {n} {x:svector B (S n)}:
    VecOptUnionCompSvector x ->
    forall i j (ic:i< S n) (jc:j<S n), (Vnth x ic ≢ None) /\ (Vnth x jc ≢ None) -> i ≡ j.
  Proof.
    intros V i j ic jc U.
    destruct U as [Ui Uj].
    dependent induction V.
    -
      destruct i, j.
      + reflexivity.
      + rewrite Vnth_0 in Ui.
        simpl in Ui.
        none_some_elim.
      + rewrite Vnth_0 in Uj.
        simpl in Uj.
        none_some_elim.
      +
        assert (ic':i < S n) by omega.
        assert (jc':j < S n) by omega.
        f_equal.
        apply IHV with (ic:=ic') (jc:=jc').
        simpl in Ui.
        replace (lt_S_n ic) with ic' in Ui by apply proof_irrelevance.
        assumption.
        simpl in Uj.
        replace (lt_S_n jc) with jc' in Uj by apply proof_irrelevance.
        assumption.
    -
      destruct i, j.
      + reflexivity.
      + simpl in Uj.
        assert (jc':j < n) by omega.
        replace (lt_S_n jc) with jc' in Uj by apply proof_irrelevance.
        apply Vforall_nth with (ip:=jc') in H.
        rewrite is_None_def in H.
        congruence.
      + simpl in Ui.
        assert (ic':i < n) by omega.
        replace (lt_S_n ic) with ic' in Ui by apply proof_irrelevance.
        apply Vforall_nth with (ip:=ic') in H.
        rewrite is_None_def in H.
        congruence.
      + simpl in Uj.
        assert (jc':j < n) by omega.
        replace (lt_S_n jc) with jc' in Uj by apply proof_irrelevance.
        apply Vforall_nth with (ip:=jc') in H.
        rewrite is_None_def in H.
        congruence.
  Qed.
  
  Lemma VecOptionUnion_cons:
    ∀ m x (xs : vector (option A) (S m)),
      VecOptUnion (Vcons x xs) ≡
                  OptionUnion
                  (VecOptUnion xs)
                  x.
  Proof.
    intros m x xs.
    unfold VecOptUnion.
    simpl.
    dep_destruct xs. simpl.
    induction x0.
    destruct x, h; auto.
    rewrite 2!Vfold_left_cons.

    rewrite OptionUnionAssoc.
    rewrite IHx0.
    rewrite OptionUnionAssoc.
    reflexivity.
    admit.
    exact (Vtail xs).
    admit.
  Qed.
  
  Lemma VecOptionUnion_Cons_None:
    ∀ (m : nat) (x : vector (option A) (S m)),
      VecOptUnion (Vcons None x) ≡ VecOptUnion x.
  Proof.
    intros m x.
    rewrite VecOptionUnion_cons.
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
    ∀ (m : nat) (x : vector (option A) m), SparseUnion (empty_svector m) x ≡ x.
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

  (* Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbUnionIndex:
    forall m n (x: vector (svector A m) (S n)) k (kc: k<m),
      Vnth
        (Vfold_left SparseUnion (empty_svector m)
                    (Vbuild 
                       (fun (i : nat) (ic : i < S n) =>
                          (Vnth x ic)
                    ))
        ) kc ≡
        VecOptUnion
        (Vbuild 
           (fun (i : nat) (ic : i < S n) =>
              Vnth (Vnth x ic) kc
        )).
  Proof.
    intros m n x k kc.
    
    induction n.
    + dep_destruct x.
      dep_destruct x0.
      remember (Vbuild (λ (i : nat) (ic : i < 1), Vnth (Vnth [h] ic) kc)) as b.
      unfold VecOptUnion.
      dep_destruct b.
      dep_destruct x0.
      simpl.
      apply hd_eq in Heqb.
      simpl in Heqb.
      subst h0.
      unfold SparseUnion.
      rewrite Vnth_map2.
      rewrite empty_svector_Vnth.
      dep_destruct x1.
      simpl.
      destruct (Vnth h kc); reflexivity.
    +
      dep_destruct x.
      remember (λ (i : nat) (ic : i < S (S n)), Vnth (Vcons h x0) ic) as geni.
      remember (λ (i : nat) (ic : i < S (S n)), Vnth (geni i ic) kc) as genik.

      (* RHS massaging *)
      rewrite Vbuild_cons with (gen:=genik).
      replace (genik 0 (lt_0_Sn (S n))) with (Vnth h kc)
        by (subst genik geni; reflexivity).
      rewrite VecOptionUnion_cons.

      replace (λ (i : nat) (ip : i < S n), genik (S i) (lt_n_S ip)) with
      (λ (i : nat) (ic : i < S n), Vnth (Vnth x0 ic) kc).
      
      rewrite <- IHn.
      remember (λ (i : nat) (ic : i < S n), Vnth x0 ic) as genX.

      rewrite Vbuild_cons with (gen:=geni).
      replace (geni 0 (lt_0_Sn (S n))) with h
        by (subst geni; reflexivity).
      subst geni.
      replace (λ (i : nat) (ip : i < S n), Vnth (Vcons h x0) (lt_n_S ip)) with genX.
      rewrite Vfold_left_cons.
      apply AbsorbUnionIndexBinary.

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
        
   
  Lemma Lemma2:
    forall var st m n (x: vector (svector A m) n) k (kc: k<(m*n)), exists i (ic:i<n) j (jc:j<m),
        Vnth (Vnth x ic) jc ≡ Vnth
                                (Vfold_left SparseUnion (empty_svector (m * n))
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
    