Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.Correctness_AExpr.
Require Import Helix.LLVMGen.Correctness_While.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.


Require Import Helix.LLVMGen.Correctness_GenIR.
Set Nested Proofs Allowed.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.

Import ProofMode.

(* DSHIMap case for [compile_FSHCOL_correct]. *)
Lemma compile_DSHIMap_correct:
  ∀ (n : nat)
    (x_p y_p : PExpr)
    (f : AExpr)
    (s1 s2 : IRState)
    (σ : evalContext)
    (memH : memoryH)
    (nextblock bid_in bid_from : block_id)
    (bks : list (LLVMAst.block typ))
    (g : global_env)
    (ρ : local_env)
    (memV : memoryV)
    (NEXT : bid_bound s1 nextblock)
    (BISIM : GenIR_Rel σ s1 bid_in (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))))
    (NOFAIL : @no_failure E_cfg (memoryH * ())
                          (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH))
    (GEN : genIR (DSHIMap n x_p y_p f) nextblock s1 ≡ inr (s2, (bid_in, bks)))

    (* Added constraints related to bounds-checking / freshness*)
    (OVERFLOW : Z.of_nat n < Integers.Int64.modulus),

    (* *)
    eutt (succ_cfg (GenIR_Rel σ s2 nextblock))
         (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH)
         (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros.

  Opaque genWhileLoop.
  cbn* in *.
  simp.
  unfold denotePExpr in *; cbn* in *.
  simp; try now (exfalso; clear -NOFAIL; try apply no_failure_Ret in NOFAIL; try_abs).
  apply no_failure_Ret in NOFAIL; simp; cbn in *; try_abs.

  hide_strings'.
  inv_resolve_PVar Heqs0.
  inv_resolve_PVar Heqs1.
  cbn* in *.
  simp.

  eutt_hide_right.
  repeat apply no_failure_Ret in NOFAIL.
  repeat (edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; [];
          clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto).

  rauto:L.
  all:eauto.
  Ltac rewrite_nth_error :=
    match goal with
    | h: nth_error _ _ ≡ _ |- _ => rewrite h
    end.

  Ltac rewrite_memory_lookup :=
    match goal with
    | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
    end.

  subst; eutt_hide_left.
  cbn in *.
  rewrite add_comment_eutt. subst.

  destruct BISIM as (STATE & BRANCHES).

  match goal with
  | [ H : context [genWhileLoop msg _ _ _ _ _ ?body _ _ ?s] |-_] => remember body as body_blocks;
                                                                    remember s as s1'
  end.

  remember (fun x σ n' mem_bl =>
      ` H : binary64 <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" n' x);;
      ` H0 : MInt64asNT.t <- lift_Serr (MInt64asNT.from_nat n');;
      ` H1 : binary64 <- denoteIUnCType σ f H0 H;; Ret (mem_add n' H1 mem_bl)) as FN.

  pose proof @genWhileLoop_correct as GEN_W.
  assert (IN: In b0 (block_ids body_blocks)). {
    subst. unfold block_ids. rewrite map_cons. cbn. left. reflexivity.
  }
  assert (UNIQUE: blk_id_norepet l0). {
    subst.
    rename Heqs4 into GEN.
    Transparent genWhileLoop.
    unfold genWhileLoop in GEN.
    cbn* in GEN. simp.
    unfold blk_id_norepet.
    cbn. admit.
    (* Coqlib.list_norepet [bid_in; b2; b0; b] *)
    (* Well-formedness condition needed. *)
  }

  assert (FRESH: fresh_in_cfg l0 nextblock). {
    rename Heqs4 into GEN.
    Transparent genWhileLoop.
    unfold genWhileLoop in GEN.
    cbn* in GEN. simp. cbn. unfold fresh_in_cfg. cbn.
    (* Maybe we can get this from no_failure..? *)
    admit.
  }
  specialize (GEN_W _ _ _ _ _ _ _ _ s2 σ _ IN UNIQUE FRESH n Heqs4).

  (* Defining BODY_H *)
  (* IY: Defining this as a Definition here, because we want the opacity in the
     later parts of this proof. *)
  Definition FUNCTION σ x f :=
    let FN :=
    (λ (x : mem_block) (σ : evalContext) (n' : nat) (mem_bl : Memory.NM.t binary64),
          ` H : binary64 <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" n' x);;
          ` H0 : MInt64asNT.t <- lift_Serr (MInt64asNT.from_nat n');;
          ` H1 : binary64 <- denoteIUnCType σ f H0 H;; Ret (mem_add n' H1 mem_bl)) in
    (fun n mem_bl=> FN x σ n%nat mem_bl).
  Opaque FUNCTION.
  clear HeqFN.

  remember (fun m mem_bl => FUNCTION σ x f (n - m - 1)%nat mem_bl) as BODY.

  (* GEN_W gets a BODY *)
  specialize (GEN_W BODY OVERFLOW).

  (* Defining Indexed Invariant (I : nat -> mem_block -> Rel_cfg) and stable
      state invariant (R : Rel_cfg)*)
  (* TODO: Tweak to change with "mem_bl" and "m""*)
  remember (fun (m : nat) (mem_bl : mem_block) memH '(memV_, (l_, g_)) => state_invariant σ s1 memH (memV_, (l_, g_))) as INV.

  remember (fun memH '(memV_, (l_, g_)) => forall mem_bl, state_invariant σ s2 (memory_set memH a0 mem_bl)
                                                        (memV_, (l_, g_))) as R.


  (* GEN_W also gets an INV and R *)
  specialize (GEN_W INV R).

  match goal with
  | [ |- eutt _ _ ?RHS] => remember RHS
  end .

  assert (i ≈ ITree.bind' (fun x => Ret x) i). rewrite bind_ret_r. reflexivity.

  rewrite H1. clear H1.


  eapply eutt_post_bind_gen.
  eapply no_failure_helix_bind_prefix in NOFAIL.
  red in NOFAIL. apply NOFAIL. apply post_returns.

  rewrite Heqi.
  eapply eutt_Proper_R. 2, 3: reflexivity.
  eapply rcompose_eq_l.

  eapply eqit_trans.
  unfold denoteDSHIMap, build_vec. cbn. unfold build_vec_gen_aux.


  (* Apply genWhileLoop_correct top lemma *)
  2 : eapply GEN_W; clear GEN_W.

  (* Equate the rest of the continuation with each other *)
  (* TODO: Invariant 'I' and 'R' might need to be tweaked. *)
  8 : {
    intros. destruct u1. destruct p1.
    rewrite interp_helix_MemSet. apply eutt_Ret.
    cbn. cbn in H1. destruct u2. destruct p1. destruct p1.
    destruct H1.

    clear GEN_W.
    2 : {
      assert (forall A, (@None A ≡ None -> False) -> False). intros * F. apply F. reflexivity.
      apply H4 in H2. contradiction.
    }
    red. Unshelve.

    subst.
    split. red. apply H4. red. destruct H1. exists b; auto. exists bid_in; auto. auto. auto.
  }

  (* TODO: Is it necessary to assume this bound? *)
  2: auto.

  (* Equate denoteDSHIMap with build_vec *)
  {
    unfold build_vec, build_vec_gen, build_vec_gen_aux.
    assert (n ≡ n - 0)%nat by lia. rewrite <- H1. clear H1.
    clear GEN_W. clear Heqi i UNIQUE FRESH IN H0. clear Heqs4 Heqbody_blocks OVERFLOW NOFAIL H.
    rewrite HeqBODY.
    subst.
    clear Heqo0 Heqo.

    clear STATE BRANCHES.
    revert memH x x0 σ.

    induction n.
    - cbn. reflexivity.
    - setoid_rewrite <- bind_bind. setoid_rewrite <- bind_bind. 

      cbn. intros *.

      rewrite interp_helix_bind.
      setoid_rewrite  interp_helix_bind at 2.

      eapply eutt_clo_bind.
      Unshelve.
      3 : {
        intros.

        refine (
            match X, X0 with
            | Some (x_memH, x_memb), Some (x0_memH, x0_memb)=> x_memH ≡ x0_memH /\
                                                              mem_add n x_memb x0 ≡ x0_memb
            | None, None => True
            | _, _ => False
            end
          ).
      }
      cbn.

      {
        Transparent FUNCTION.
        subst. cbn.
        rewrite 2 interp_helix_bind.
        rewrite Nat.sub_0_r.
        eapply eutt_clo_bind.
        reflexivity.
        intros * H1. destruct u1, u2. destruct p1, p2. inversion H1. subst.
        (* inversion H1. inversion H1. subst. *)
        rewrite 2 interp_helix_bind.
        eapply eutt_clo_bind.
        reflexivity. intros.
        destruct u1, u2. destruct p1, p2. rewrite interp_helix_bind. inversion H1.
        subst. rewrite <- bind_ret_r at 1.
        eapply eutt_clo_bind. inversion H. reflexivity. intros. destruct u1, u2. destruct p2.
        rewrite interp_helix_ret. cbn. destruct p1. inversion H0.
        apply eutt_Ret. split; cbn; try rewrite <- H; try reflexivity.
        inversion H0; auto. inversion H0; auto.
        (* inversion H3. inversion H3. *)
        apply eutt_Ret; try inversion H. auto. inversion H. inversion H.
        apply eutt_Ret. auto. inversion H1. inversion H1. apply eutt_Ret. auto.
     }

    (* Bind continuation case of DSHIMap and build_vec equality *)
     {
       intros.

       destruct u1, u2. destruct p1, p2. 4 : reflexivity.
       3 : contradiction.
       2 : { destruct p1; contradiction. }
       destruct H. rewrite H, H0.
       rewrite IHn.
       Opaque FUNCTION.
       cbn.

       clear.

       remember 0%nat in * at 1.
       rewrite <- Heqn0 at 1.
       assert ( n ≡ n + n0 )%nat by lia.
       rewrite H. rewrite <- H at 1 2.
       clear Heqn0 H.

       revert n0 m0 m1 x σ f.
       induction n; [reflexivity | ].
       intros; rewrite 2 interp_helix_bind.

       eapply eutt_clo_bind_returns. reflexivity.
       intros [ [memH memBl] | ] [ [memH' memBl'] | ] A RetH RetH'; inversion A ; [ | reflexivity ].
       subst.

       assert (EQV': (S n + n0)%nat ≡ (n + (S n0))%nat) by lia.
       rewrite EQV'.
       specialize (IHn (S n0) memH' memBl' x σ f). apply IHn.
     }
  }

  (* Prove body hypothesis (body blocks is equal to one iteration of FUNCTION) *)
  {
    intros. Transparent FUNCTION. unfold FUNCTION.
    subst.
    match goal with
    | [ |- eutt ?R _ _ ] => remember R
    end.

    vjmp. hvred.

    unfold denote_phis.
    cbn. hvred. vred.

    rename Heqs4 into GEN.
    rename i1 into ptr.
    (* [vstep] does not handle gep currently *)

    (* Starting to reason about memory for GEP. *)
    cbn.

    hvred. vstep.

    (* Looking up memory *)
    edestruct denote_instr_gep_array as (? & READ & EQ); shelve.
    (* TODO: Indexed Invariant should reference mem *)

    hvred.
    eapply eutt_clo_bind_returns.
    vstep.
    edestruct denote_instr_gep_array as (? & READ & EQ); shelve.
    shelve. shelve.

    intros. destruct u1, u2. destruct p1, p2. destruct p1.
    hvred.

    shelve. shelve.
  }

  {
    intros. subst.
    destruct H6 as [ | [| [|] ]] ; subst; admit.
  }

  (* Imp_rel state invariant *)
  2 : {
    subst. repeat intro. destruct b1. destruct p1. admit.
  }

  (* Stability condition *)
  {
    intros. subst. intros.
    red in H1.
    pose proof @memory_invariant_ext_local.
    red in H3.
    admit.
  }

  {
    (* subst. intros. split. intros. split; eauto. red in STATE. *)
    shelve.
  }

  {
    subst. red in STATE. intros.
    (* TODO: The mem_block should be instantiated concretely. *)
    intros. shelve.
  }
Admitted.
