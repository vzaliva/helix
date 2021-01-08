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
             (i n : nat)
             (init acc : mem_block):
    itree Event mem_block :=
    (* IMap has "reverse indexing" on its body *)
    tfor (fun i acc => DSHIMap_body σ f (n - 1 - i) init acc) i n acc.

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
      denoteDSHIMap n f σ x y ≈ DSHIMap_tfor_down σ f 0 n x y.
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
        (interp_helix (DSHIMap_tfor_down σ f 0 n x y) init_vec).
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
  Admitted.

  (* < Generalized Lemma > Equivalent to Desired lemma when i = 0 *)
  (*
      Rough proof sketch for inductive case:

      We want to show:
         (0 ... (S m)) (e ... (S m)) ≈ ((S m) ... i) ((S m) ... e)
      Where we have as IH:
         (i ... m) (e ... m) ≈ (m ... i) (m ... e)

      1) First manipulate the RHS...
      By [commut_gen] and [tfor_ss_dep], the RHS can be rewritten to the following:
         (0 ... m) (m) (e ... (S m)) ≈ (m ... i) (m) ((S m) ... e)
      By [eutt_clo_bind] and [tfor_unroll], this is equivalent to:
         (0 ... m) (m) (e ... (S m)) ≈ (m ... i) (m ... e)

      2) At this point, we can use the IH to rewrite on the RHS.

      3) Clean up the LHS.
        Since we know that (i ... (S m)) ≈ (i .. m) (m) (TODO: aux. lemma)
         (0 ... (S m)) (e ... (S m)) ≈ ((S m) ... i) ((S m) ... e) is equivalent to
         (0 ... m) (m) (e ... (S m)) ≈ ((S m) ... i) ((S m) ... e)

      Using [commut_gen] [tfor_unroll] again similarly on the LHS, we can show
      that both sides are equivalent to each other. *)
  Lemma mem_block_equiv_is_order_independent_gen :
    ∀ (i n : nat) (memH : memoryH) σ f init,
      0 <= i < n ->
      eutt (E := void1) (⤉ (eq, equiv))
           (interp_helix (vec <- DSHIMap_tfor_up σ f 0 (n - i) init init;;
                          DSHIMap_tfor_down σ f (n - i) n init vec) memH)
           (interp_helix (vec <- DSHIMap_tfor_down σ f 0 (n - i) init init;;
                          DSHIMap_tfor_up σ f (n - i) n init vec) memH).
  Proof.
    intros * [LO HI].
    assert (INEQ: n - i > 0) by lia.
    Opaque DSHIMap_body.
    revert n i INEQ memH σ f init LO HI.
    intros n i.
    induction (n - i); intros.
    - inv INEQ.
    - clear INEQ.
      unfold DSHIMap_tfor_up, DSHIMap_tfor_down in *.
      assert (EQ: S n0 - 1 ≡ n0) by lia; rewrite EQ; clear EQ.

      (* 1) RHS unrolling and swapping *)
      setoid_rewrite tfor_unroll at 2. 2 : shelve. (* TODO: bounds *)
      assert (EQ: n0 - 0 ≡ n0) by lia; rewrite EQ; clear EQ.

      assert (
        SWAP_RHS:
          eutt (E := void1) eq
              (interp_helix (a <- DSHIMap_body σ f n0 init init ;;
                tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n0 - i0) init acc) 1 (S n0) a) memH)
              (interp_helix (a <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n0 - i0) init acc) 1 (S n0) init ;;
                DSHIMap_body σ f n0 init a) memH)). {
        intros; setoid_rewrite interp_helix_bind.
        eapply commut_gen; admit.
      }

      setoid_rewrite interp_helix_bind.

      (* TODO: SWAP_RHS [eq] should be ⤉ (eq, equiv); another [eutt_clo_bind] is necessary... *)
      rewrite SWAP_RHS; clear SWAP_RHS.
      setoid_rewrite <- interp_helix_bind.
      setoid_rewrite bind_bind.
      rewrite tfor_ss_dep. Unshelve. 7 : { exact (fun i0 x => DSHIMap_body σ f (n0 - 1 - i0) init x). }

      assert (
        UNROLL: eutt (E := void1) (⤉ (eq, equiv))
             (interp_helix (vec <- tfor (λ (i0 : nat) (x : mem_block), DSHIMap_body σ f (n0 - 1 - i0) init x) 0 n0 init;;
                            (acc' <- DSHIMap_body σ f n0 init vec;;
                             tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) (S n0) n acc')) memH)
             (interp_helix (vec <- tfor (λ (i : nat) (acc : mem_block), DSHIMap_body σ f (n0 - 1 - i) init acc) 0 n0 init;;
                            tfor (λ (i : nat) (acc : mem_block), DSHIMap_body σ f i init acc) n0 n vec) memH)). {
        setoid_rewrite tfor_unroll.
        assert (EQ: n0 - 1 - 0 ≡ n0 - 1) by lia; rewrite EQ; clear EQ.
        setoid_rewrite interp_helix_bind.
        setoid_rewrite interp_helix_bind.
        rewrite 2 bind_bind.
        eapply eutt_clo_bind. reflexivity.
        intros [[] |] [[]|] EQ; inv EQ.
        eapply eutt_clo_bind. reflexivity.
        intros [[] |] [[]|] EQ; inv EQ.
        rewrite tfor_unroll. reflexivity. admit.
        reflexivity.
        eapply eutt_clo_bind. reflexivity.
        intros [[] |] [[]|] EQ; inv EQ.
        rewrite tfor_unroll. reflexivity. admit.
        reflexivity. admit. admit.
        (* TODO: admits are w.r.t bounds reasoning; should be trivial to dismiss *)
      }

      rewrite UNROLL; clear UNROLL.

      (* Proper... *)

      (* 2) Apply IH *)
      rewrite <- IHn0.

      (* LHS unrolling and swapping *)
      rewrite tfor_unroll.

  Admitted.

End DSHIMap_is_tfor.
