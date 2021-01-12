Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.
Require Import Helix.LLVMGen.Correctness_While.

From Vellvm Require Import Utils.Commutation.

Require Import Paco.paco.
From ITree Require Import HeterogeneousRelations.

Import ProofMode.

Set Implicit Arguments.
Set Strict Implicit.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Import Memory.NM.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Section DSHIMap_is_tfor.

  (* Iterative body of [IMap] *)
  Definition DSHIMap_body
             (σ : evalContext)
             (f : AExpr)
             (offset : nat)
             (init acc : mem_block) : itree Event mem_block :=
    v <-
       lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" offset init);;
    vn <- lift_Serr (MInt64asNT.from_nat offset);;
    v'<- denoteIUnCType σ f vn v;;
    ret (mem_add offset v' acc).

  (* [tfor] formulation of [DSHIMap].
     "Reverse/downward" indexing ([n - 1 .. 0]). *)
  Definition DSHIMap_tfor_down
             (σ : evalContext)
             (f : AExpr)
             (i n e: nat)
             (init acc : mem_block):
    itree Event mem_block :=
    (* IMap has "reverse indexing" on its body *)
    tfor (fun i acc => DSHIMap_body σ f (e - 1 - i) init acc) i n acc.

  (* "Right"-side-up indexing variant ([0 .. n - 1]). *)
  Definition DSHIMap_tfor_up
             (σ : evalContext)
             (f : AExpr)
             (i n : nat)
             (init acc : mem_block):
    itree Event mem_block :=
    tfor (fun i acc => DSHIMap_body σ f i init acc) i n acc.

  (* [denoteDSHIMap] is equivalent to [tfor] with "reverse indexing" on an
     [IMap] body. *)
  Lemma denoteDSHIMap_as_tfor:
    forall (σ : evalContext) n f x y,
      denoteDSHIMap n f σ x y ≈ DSHIMap_tfor_down σ f 0 n n x y.
  Proof.
    intros.
    unfold DSHIMap_tfor_down. revert y.
    induction n.
    - cbn. intros.
      setoid_rewrite tfor_0.
      reflexivity.
    - intros.
      rewrite tfor_unroll; [| lia].
      assert (S n - 1 - 0 ≡ n) by lia. rewrite H. cbn.
      repeat setoid_rewrite bind_bind.
      cbn.
      eapply eutt_clo_bind; [reflexivity|].
      intros u1 u2 H'.
      eapply eutt_clo_bind; [reflexivity|].
      intros u0 u3 H''. subst.
      eapply eutt_clo_bind; [reflexivity|].
      intros; subst. rewrite bind_ret_l.
      rewrite IHn.

      setoid_rewrite tfor_ss_dep. 3 : lia.
      reflexivity. intros.
      cbn. assert (n - 0 - S i ≡ n - 1 - i) by lia. rewrite H0. reflexivity.
  Qed.

  Definition pair_rel {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop) :=
    (fun '(a, b) '(a', b') => RA a a' /\ RB b b').

  (* < Desired Lemma > *)
  Lemma mem_block_equiv_is_order_independent :
    ∀ (n : nat) (init_vec : memoryH) x y σ f,
      eutt (E := void1) (Coqlib.option_rel (pair_rel (@eq memoryH) (@equiv mem_block _)))
        (interp_helix (DSHIMap_tfor_up σ f 0 n x y) init_vec)
        (interp_helix (DSHIMap_tfor_down σ f 0 n n x y) init_vec).
  Proof.
    intros *.
    unfold DSHIMap_tfor_up, DSHIMap_tfor_down.
  Admitted.

  Instance option_pair_rel_Equiv {A B} {R : A -> A -> Prop} {S : B -> B -> Prop}
           {EQR: Equivalence R} {EQS: Equivalence S}
    : Equivalence (Coqlib.option_rel (pair_rel R S)).
  Proof.
    split.
    - red; intros [ [] | ]; constructor; unfold pair_rel; split; reflexivity.
    - red; intros [ [] | ] [ [] | ] H; inv H ; constructor; unfold pair_rel in *.
      destruct H2 as []. split; symmetry; auto.
    - red; intros [ [] | ] [ [] | ] [ [] | ] H H'; inv H; inv H'; constructor;
        unfold pair_rel in *.
      destruct H2 as []; destruct H1 as []; split; etransitivity; eauto.
  Qed.

  Notation "⤉ ( R , S ) " := (Coqlib.option_rel (pair_rel R S)) (at level 10).

  Definition equiv_mem_block_frag (i n : nat) (m m' : mem_block) :=
    forall k, i <= k -> k < n -> find k m = find k m'.

  Definition equiv_mem_block (n : nat) (m m' : mem_block) :=
    equiv_mem_block_frag 0 n m m'.

  Notation "m ≡[ i , n  ] m'" := (equiv_mem_block_frag i n m m') (at level 10).
  Notation "m ≡[ n ] m'" := (equiv_mem_block n m m') (at level 10).


  Instance option_pair_Equivalence: (Equivalence (⤉ (@eq memoryH, @equiv mem_block _))).
  Proof.
    intros. apply (@option_pair_rel_Equiv memoryH mem_block eq equiv _ mem_block_Equiv_Equivalence).
  Qed.


  Lemma imap_body_post:
    forall E m1 m2 init σ f i,
      no_failure (interp_helix (E := E) (DSHIMap_body σ f i init m2) m1) ->
    forall m0 b t0 b1,
      MInt64asNT.from_nat i ≡ inr t0 ->
      mem_lookup_err "Error reading memory denoteDSHIMap" i init ≡ inr b ->
      Returns (E := E) (Some (m0, b1)) (interp_helix (denoteIUnCType σ f t0 b) m1) ->
      Returns (Some (m0, mem_add i b1 m2)) (interp_helix (E := E) (DSHIMap_body σ f i init m2) m1).
  Proof.
    intros. cbn in *.
    assert (H' := H).
    apply no_failure_helix_bind_prefix in H.
    rewrite interp_helix_bind.
    unfold lift_Derr in H.

    destruct (mem_lookup_err "Error reading memory denoteDSHIMap" i init) eqn: MEM.

    try_abs.
    cbn. rewrite interp_helix_ret. cbn. rewrite bind_ret_l.


    eapply no_failure_helix_bind_continuation in H'.
    2 : {
      cbn. rewrite interp_helix_ret. constructor. cbn. reflexivity.
    }

    clear H.
    assert (H := H').
    eapply no_failure_helix_bind_prefix in H'.
    unfold lift_Serr in H'. destruct (MInt64asNT.from_nat i) eqn: HM. cbn in *.
    try_abs. cbn.
    rewrite interp_helix_bind; cbn. rewrite interp_helix_ret. cbn.
    rewrite bind_ret_l.
    rewrite interp_helix_bind.

    eapply no_failure_helix_bind_continuation in H.
    2 : {
      cbn. rewrite interp_helix_ret. constructor. cbn. reflexivity.
    }


    inv H0. inv H1.
    eapply no_failure_helix_bind_prefix in H.
    red in H.
    eapply Returns_bind. apply H2. cbn. rewrite interp_helix_ret. cbn. constructor. reflexivity.
  Qed.

  (* < Generalized Lemma > Equivalent to Desired lemma when i = 0 *)
  Lemma swap_ind:
    ∀ n i : nat,
      (∀ (memH : memoryH) (σ : evalContext) (f : AExpr) (init : mem_block),
          eutt (E := void1) (⤉ (eq, equiv))
            (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 i init;;
              tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - i) vec) memH)
            (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S i - 1 - i0) init acc) 0 i init;;
              tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) (S i) n vec) memH))
      → ∀ (memH : memoryH) (σ : evalContext) (f : AExpr) (init : mem_block),
        0 < S i
        → S i < n
        -> no_failure (E := void1) (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 (S i) init;;
                                tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) vec) memH)
        → eutt (E := void1) (⤉ (eq, equiv))
          (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 (S i) init;;
          tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) vec) memH)
          (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S (S i) - 1 - i0) init acc) 0 (S i) init;;
            tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) (S (S i)) n vec) memH).
  Proof.
    intros n i IHi memH σ f init LO HI NOFAIL.
    Opaque DSHIMap_body.
    assert (EQ: S (S i) - 1 ≡ S i) by lia; rewrite EQ; clear EQ.

      setoid_rewrite tfor_split with (j := i) at 1; try lia.

      assert (
        SWAP_LHS:
          eutt (E := void1) (⤉ (eq, equiv))

            (interp_helix (vec <- (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 i init) ;;
                           vec <- (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) i (S i) vec) ;;
                            tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) vec) memH)

            (interp_helix (vec <- (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 i init) ;;
                           (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - i) vec)) memH)). {
        intros; setoid_rewrite interp_helix_bind.
        eapply eutt_clo_bind. reflexivity.

        intros [[] |] [[]|] EQ; inv EQ.
        2 : reflexivity.
        setoid_rewrite tfor_split with (j := n - S i) at 2; try lia.
        cbn.

        assert (
           H: tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) (n - S i) (n - i) m2 ≈
                 tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) i (S i) m2). {
          rewrite tfor_unroll. 2 : lia.
          assert (EQ : S (n - S i) ≡ n - i) by lia; rewrite EQ; clear EQ.
          assert (EQ : n - 1 - (n - S i) ≡ i) by lia; rewrite EQ; clear EQ.
          setoid_rewrite tfor_0. rewrite bind_ret_r. rewrite tfor_unroll; try lia.
          setoid_rewrite tfor_0. rewrite bind_ret_r.
          reflexivity.
        }

        setoid_rewrite <- H; clear H.

        rewrite interp_helix_bind.

        assert (forall m m2, eutt (E := void1) eq
              (interp_helix (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) (n - S i) (n - i) m2) m)
              (interp_helix (DSHIMap_body σ f i init m2) m)). {
          intros.
          rewrite tfor_unroll.
          assert (EQ : n - 1 - (n - S i) ≡ i) by lia; rewrite EQ; clear EQ.
          assert (EQ : S (n - S i) ≡ n - i) by lia; rewrite EQ; clear EQ.
          setoid_rewrite tfor_0. rewrite bind_ret_r. reflexivity. lia.
        }

        setoid_rewrite H.
        match goal with
        | [ |- _ ?R ] => remember R as RHS
        end.
        assert (RHS ≈
          interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) m2;;
                        (DSHIMap_body σ f i init vec)) m1). {
          subst. setoid_rewrite interp_helix_bind.
          eapply eutt_clo_bind. reflexivity.

          intros [[] |] [[] |] EQ; inv EQ. 2 : reflexivity.
          apply H.
        }
        rewrite H0. clear H0 HeqRHS H RHS.

        setoid_rewrite interp_helix_bind.

        (* match goal with *)
        (* | [ |- eutt _ (ITree.bind ?pre ?post) (ITree.bind ?pre' ?post') ] => *)
        (*     remember pre as PRE ; remember post as POST; *)
        (*     remember pre' as PRE' ; remember post' as POST' *)
        (* end. *)

        (* eapply commut_gen'.  *)
        (*     (Q1 := fun x => Returns x PRE) *)
        (*     (Q2 := fun x => Returns x PRE'). *)
        (* - admit. *)
        (* - admit. *)
        (* - rewrite has_post_post_strong. eapply eutt_Returns_. eauto. *)
        (* - rewrite has_post_post_strong. eapply eutt_Returns_. eauto. *)
        (* - intros. rewrite has_post_post_strong. eapply eutt_Returns_. *)
        (*   intros [[] |] EQ. subst. *)
        (*   destruct a as [[] |]. *)



        (*   intros. *)
        (* - admit. *)
        (* - admit. *)
        admit.
      }

      setoid_rewrite bind_bind.
      rewrite SWAP_LHS; clear SWAP_LHS.
      rewrite IHi; try lia. clear IHi.

      assert (EQ : S i - 1 ≡ i) by lia; rewrite EQ; clear EQ.
      setoid_rewrite tfor_unroll at 2.

      assert (EQ : S i - 0 ≡ S i) by lia; rewrite EQ; clear EQ.

      assert (
        SWAP_LHS:
          eutt (E := void1) eq
               (interp_helix
                  (vec <- DSHIMap_body σ f (S i) init init;;
                    tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S i - i0) init acc) 1 (S i) vec ) memH)
               (interp_helix
                    (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S i - i0) init acc) 1 (S i) init ;;
                     DSHIMap_body σ f (S i) init vec) memH)). {
        setoid_rewrite interp_helix_bind.
        eapply commut_gen; admit.
      }
      all : try lia.

      setoid_rewrite interp_helix_bind at 2.
      rewrite SWAP_LHS; clear SWAP_LHS.
      rewrite <- interp_helix_bind.
      rewrite tfor_ss_dep.
      all : try lia.
      2 : { Unshelve. 4 : exact (fun n mem_bl => DSHIMap_body σ f (i - n) init mem_bl). intros; reflexivity. shelve. shelve. }
      setoid_rewrite bind_bind.
      setoid_rewrite interp_helix_bind.
      eapply eutt_clo_bind. reflexivity.

      intros [[] |] [[] |] EQ; inv EQ. 2 : reflexivity.
      rewrite tfor_split with (j := (S (S i))); try lia.
      rewrite tfor_unroll. setoid_rewrite tfor_0.
      rewrite bind_ret_r. reflexivity. lia.
      Unshelve.

  Admitted.

End DSHIMap_is_tfor.
