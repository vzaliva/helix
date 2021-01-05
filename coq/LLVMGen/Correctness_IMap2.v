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

  (* < Generalized Lemma > Equivalent to Desired lemma when i = 0 *)
  Lemma mem_block_equiv_is_order_independent_gen :
    ∀ (i n : nat) (memH : memoryH) σ f init,
      0 <= i < n ->
      eutt (E := void1) (⤉ (eq, equiv))
           (interp_helix (vec <- DSHIMap_tfor_up σ f i n init init;;
                          DSHIMap_tfor_down σ f (n - i) n init vec) memH)
           (interp_helix (vec <- DSHIMap_tfor_down σ f i n init init;;
                          DSHIMap_tfor_up σ f (n - i) n init vec) memH).
  Proof.
    intros * [LO HI].
    Opaque DSHIMap_body.
    revert i LO HI memH σ f init.
    induction n; intros.
    - inv HI.
    - unfold DSHIMap_tfor_up, DSHIMap_tfor_down.
      assert (EQ: S n - 1 ≡ n) by lia; rewrite EQ; clear EQ.
      rewrite tfor_unroll; [ | lia].
      rewrite tfor_unroll; [ | lia].

      setoid_rewrite interp_helix_bind.

      assert
        (forall memH,
            eutt (E := void1) (⤉ (eq, equiv))
        (interp_helix
          (ITree.bind'
            (fun a : mem_block =>
              tfor (fun (i0 : nat) (acc : mem_block) => DSHIMap_body σ f i0 init acc) (S i) (S n) a)
            (DSHIMap_body σ f i init init)) memH)

        (interp_helix
          (ITree.bind'
            (fun a : mem_block => DSHIMap_body σ f i init a)
            (tfor (fun (i0 : nat) (acc : mem_block) => DSHIMap_body σ f i0 init acc) (S i) (S n) init)) memH)).
      {
        intros.
        setoid_rewrite interp_helix_bind.
        pose proof @commut_gen as CG.
        admit.
      }
      specialize (H memH).
      assert (Equivalence (⤉ (@eq memoryH, @equiv mem_block _))). {
        intros. apply (@option_pair_rel_Equiv memoryH mem_block eq equiv _ mem_block_Equiv_Equivalence).
      }

      pose proof @trans_rcompose.
      (* TODO: Make rcompose_trans an [eq_rel] *)
      assert (@eq_rel
                (option (memoryH * mem_block)) _
                (rcompose (⤉ (eq, equiv)) (⤉ (eq, equiv))) (⤉ (eq, equiv))).
      {
        repeat intro. split; repeat intro. inv H2. etransitivity; eauto.
        econstructor; eauto. reflexivity.
      }

      rewrite <- H2.

      eapply eqit_trans.

      (* Bubbling up one step. *)
      {
        eapply eutt_clo_bind.
        apply H.
        intros.
        Unshelve.
        2 : {
          exact (fun x =>
            match x with
            | Some (mem', v) =>
              interp_helix
                (tfor (λ (i0 : nat) (acc : mem_block),
                        DSHIMap_body σ f (n - i0) init acc) (S n - i) (S n) v) mem'
            | None => Ret None
            end).
        }
        inv H3. reflexivity. unfold pair_rel in H4. destruct x; destruct y.
        destruct H4; subst.
        pose proof mem_block_Equiv_Equivalence.
        assert (forall E f i n, Proper (@equiv mem_block _ ==> eutt eq) (@tfor E mem_block f i n)). {
          repeat intro. admit.
        }
        rewrite H4.
        reflexivity.
      }

      (* One step bubbled on the LHS. *)
      clear H H0 H1 H2.
      unfold DSHIMap_tfor_down, DSHIMap_tfor_up in IHn.

  Admitted.

End DSHIMap_is_tfor.
