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

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.


Section DSHIMap_is_tfor.

  Definition DSHIMap_tfor_body
             (σ : evalContext)
             (f : AExpr)
             (offset : nat)
             (init acc : mem_block) :=
    ` v : binary64 <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" offset init);;
    ` vn : MInt64asNT.t <- lift_Serr (MInt64asNT.from_nat offset);;
    ` v' : binary64 <- denoteIUnCType σ f vn v;;
    ret (mem_add offset v' acc).

  Definition DSHIMap_tfor
             (σ : evalContext)
             (n : nat)
             (f : AExpr)
             (x y : mem_block):
    itree Event mem_block :=
    (* IMap has "reverse indexing" on its body *)
    tfor (fun i acc => DSHIMap_tfor_body σ f (n - i) x acc) 1 (S n) y.


  Lemma tfor_ss_dep : forall {E A} i j (body body' : nat -> A -> itree E A) a0,
      (forall x i, body' (S i) x ≈ body i x) ->
      i <= j ->
      tfor body' (S i) (S j) a0 ≈ tfor body i j a0.
  Proof.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply eutt_iter'' with (RI1:=fun '(a,x) '(b, y) => a = S b /\ x ≡ y) (RI2:=fun '(a,x) '(b, y) => a = S b /\ x ≡ y); auto.
    intros [j1 acc1] [j2 acc2] H1.
    destruct H1. subst.
    cbn.
    destruct (j <=? j2) eqn:J.
    - rewrite H1.
      rewrite J.
      apply eutt_Ret.
      constructor; auto.
    -
      rewrite H1. rewrite J.
      eapply eutt_clo_bind.
      rewrite H.
      reflexivity.
      intros; subst.
      apply eutt_Ret.
      constructor; auto.
  Qed.

  Lemma denoteDSHIMap_as_tfor:
    forall (σ : evalContext) n f x y,
      denoteDSHIMap n f σ x y ≈ DSHIMap_tfor σ n f x y.
  Proof.
    intros.
    unfold DSHIMap_tfor. revert y.
    induction n.
    - cbn. intros.
      setoid_rewrite tfor_0.
      reflexivity.
    - intros.
      assert (S n ≡ n + 1). lia. rewrite H. rewrite <- H at 1. rewrite <- H at 1. clear H.
      cbn. rewrite tfor_unroll; [| lia].
      assert (n + 1 - 1 ≡ n) by lia. rewrite H. clear H.
      repeat setoid_rewrite bind_bind.
      eapply eutt_clo_bind; [reflexivity|].
      intros u1 u2 H'.
      eapply eutt_clo_bind; [reflexivity|].
      intros u0 u3 H''. subst.
      eapply eutt_clo_bind; [reflexivity|].
      intros; subst. rewrite bind_ret_l.
      rewrite IHn.
      setoid_rewrite tfor_ss_dep at 2. 3 : lia.
      reflexivity. intros.
      cbn. assert (n + 1 - S i ≡ n - i) by lia. rewrite H. reflexivity.
  Qed.


End DSHIMap_is_tfor.
