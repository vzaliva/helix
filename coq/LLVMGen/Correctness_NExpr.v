Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.StateInvariant.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.IdLemmas.

(* Import ProofNotations. *)
Import ListNotations.

Open Scope Z.
Open Scope list.

Set Implicit Arguments.
Set Strict Implicit.

(* YZ TODO: Check that this is global and factor it in prelude *)
Typeclasses Opaque equiv.

(** * Correctness of the compilation of numerical expressions

     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [ genNexpr].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     Compiler side:
     * s1 s2: IRState
     Vellvm side:
     * c : code
     * e : exp typ

 *)

Section NExpr.
  
  (** At the top level, the correctness of genNExpr is expressed as the denotation of the operator being equivalent
      to the bind of denoting the code followed by denoting the expression.
      However this is not inductively stable, we only want to plug the expression at the top level.
      We therefore instead carry the fact about the denotation of the expression in the invariant. (Is there another clever way?)
   *)
  Definition genNExpr_exp_correct_ind (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
            interp_cfg
              (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
              g l' memV ≈
              Ret (memV,(l',(g,UVALUE_I64 i))).

  (**
     We package the local specific invariants. Additionally to the evaluation of the resulting expression,
     we also state that evaluating the code preserves most of the state, except for the local state being
     allowed to be extended with fresh bindings.
   *)
  Record genNExpr_rel_ind
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct_ind e mf stf;
    monotone : ext_local mi sti mf stf
    }.

(** * Tactics
    
  - [cbn*] : unfolds a fixed list of definitions we want to go under, and reduces via [cbn]
  - [simp] : systematically destruct [match] in the context. Used in particular to systematically
             derive from the success of the compilation the success of the compilation of the sub-components.
  - [try_abs] : attempts to automatically discharge absurd cases. Relies essentially on two sources to this end:
             type constraints provided by [memory_invariant], and success of the computation provided by
             [no_failure].

  - [solve_lu] : attempts to discharge goal of the shape [Maps.lookup id l = Some ?]
  - [solve_state_invariant] : attempts to discharge goal of the shape [state_invariant _ _ _ _] 

  - [hvred] : stands for helix-vellvm-reduction. Uses rewriting to "reduce" both side of the simulation
             being proved to a bind whose first component is either the denotation of a parameter,
             or of a concrete operation to be processed. 
  - [vred] : stands for vellvm-reduction. Similar to [hvred], but performing only [vellvm]-based reduction
             on the right hand-side of the simulation.
             In the context of this development, is a synonymous for [vstep_r].
             To perform it on the left-hand-side of [eutt], use [vstep_l].
   - [tred] :alias for [autorewrite with itree]. Useful to fill in defaults in the current automation,
             hopefully will be made useless soon.
   - [vstep]: stands for vellvm-step. Performs a single atomic forward-reasoning principle, processing for
             instance a single instruction or expression.
             Cycles goals so that it exhibits first the generated side conditions.
  - [hstep]: stands helix-step. Processes a single trigger of a memory event.

 *)

  Import ProofMode.

  Lemma genNExpr_local_count :
    forall nexp s1 s2 e c,
      genNExpr nexp s1 ≡ inr (s2, (e, c)) ->
      (local_count s2 >= local_count s1)%nat.
  Proof.
    induction nexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
          | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            apply incLocal_local_count in H
          | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
              genNExpr ?n s1 ≡ inr (s2, (e, c)) → local_count s2 ≥ local_count s1,
      GEN: genNExpr ?n _ ≡ inr _ |- _ =>
    apply IH in GEN
    end;
      try lia.
  Qed.

  Ltac get_local_count_hyps ::=
    repeat
      match goal with
      | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
        apply incBlockNamed_local_count in H
      | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
        apply incVoid_local_count in H
      | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
        apply incLocal_local_count in H
      | H: genNExpr ?n ?s1 ≡ inr (?s2, _) |- _ =>
        apply genNExpr_local_count in H
      end.

  Create HintDb irs_lt.
  Hint Resolve incLocal_lt : irs_lt.
  
  Ltac solve_alist_fresh :=
    (eapply freshness_pre_alist_fresh; now eauto with irs_lt).
  
  Ltac solve_sub_alist :=
    (reflexivity
     || (apply sub_alist_add; solve_alist_fresh)
     || (etransitivity; try eassumption; []; solve_sub_alist)
    ).

Lemma alist_In_dec :
  forall {K V} `{RelDec K} `{RelDec v} (id : K) (l : alist K V) (v : V),
    {alist_In id l v} + {~(alist_In id l v)}.
Proof.
Admitted.

Require Import LidBound.

  (* Lemma freshness_chain: forall s1 s2 s3 g1 g2 l1 l2 memV1 memV2 , *)
  (*     freshness_pre s1 s3 (memV1,(l1,g1)) -> *)
  (*     freshness_post s1 s2 l1 (memV2,(l2,g2)) -> *)
  (*     freshness_pre s2 s3 (memV2,(l2,g2)). *)
  (* Proof. *)
  (*   intros * PRE POST. *)
  (*   cbn in *. *)
  (*   intros * IN. *)
  (*   destruct (alist_In_dec id l1 v) as [IN' | NIN]. *)
  (*   - apply PRE in IN'. *)

  (* Admitted. *)

  (** * Freshness
      We need to reason about the freshness of local variables generated through the IRState monad.
      To this end, we rely on the following pre and postcondition about local states (defined formally over a whole VIR state, ignoring the other arguments)
      when reasoning about a given computation c:
      - freshness_pre s1 s2 : fun l => dom(l) ∩ [s1,s2] = ∅
        i.e. we ensure that the provided interval over which we will generate variables is indeed fresh
      - freshness_post s1 s2 li : fun lf => dom(lf) \ dom(li) ⊆ [s1;s2]
        i.e. after the computation, the new local state has indeed only been extended with variables from the provided interval.

     Let us note FP (resp. FQ) for freshness_pre (resp. freshness_post). We have the following lemmas axiomatizing how these two predicates evolve.

     FP1. FP s s l             : if we give ourself an empty freshness window, the precondition is trivially true

     FP2. FP s1 s3 l ->
          s2 << s3 ->
          FP s1 s2 l

     2. FQ s1 s2 l l         : if we don't extend the state, the postcondition is trivially true

     3. incLocal s1 = (s2,r) ->
        FP s1 s2 l l[r:v]

     4. FP s1 s3 l1 ->
        FQ s1 s2 l1 l2 ->
        FP s2 s3 l2          : if we have the precondition for a long computation, and establish the postcondition at a mid point, we can recover the precondition at this point for the remaining of the computation.


   *)

  (* If we have not extended the local state, certainly we did not extend it out the required bound *)
  Lemma freshness_post_no_extension: forall s1 s2 l, freshness_post s1 s2 l l.
  Proof.
    intros; red; intros.
    intuition.
  Qed.

  Lemma freshness_post_inclocal : forall s1 s2 l x v,
      incLocal s1 ≡ inr (s2,x) ->
      freshness_post s1 s2 l (alist_add x v l).
  Proof.
    intros * INC.
    cbn in *.
    apply lid_bound_between_incLocal in INC.
    red; intros.
    destruct (id ?[ Logic.eq ] x) eqn:EQ.
    - rewrite rel_dec_correct in EQ; subst; auto.
    - apply neg_rel_dec_correct in EQ.
      apply In_add_In_ineq in H; auto.
      intuition.
  Qed.

  (* Weakens the freshness precondition: if we know that the range [|s1;s3|] is fresh in [l],
         we can always lower [s3].
         This is useful to derive the precondition of the first inductive hypotheses when dealing with nary operators.
   *)
  Lemma freshness_pre_shrink_upper_bound :
    forall s1 s2 s3 l,
      freshness_pre s1 s3 l ->
      s2 << s3 -> (* Also works with non-strict *)
      freshness_pre s1 s2 l.
  Proof.
    (* intros; eapply new_state_invariant_shrink; eauto. *)
  Admitted.

  Lemma freshness_chain: forall s1 s2 s3 l1 l2 ,
      freshness_pre s1 s3 l1 ->
      freshness_post s1 s2 l1 l2 ->
      freshness_pre s2 s3 l2.
  Proof.
  Admitted.

  Lemma freshness_post_transitive :
    forall s1 s2 s3 l1 l2 l3,
      freshness_post s1 s2 l1 l2 ->
      freshness_post s2 s3 l2 l3 ->
      freshness_post s1 s3 l1 l3.
  Admitted.

  Lemma freshness_pre_alist_fresh_specialized:
    forall s1 s2 l id,
      freshness_pre s1 s2 l ->
      incLocal s1 ≡ inr (s2,id) ->
      alist_fresh id l.
  Proof.
    intros * ? INCL.
    eapply freshness_pre_alist_fresh; eauto with irs_lt.
  Qed.

  Ltac forwardr H H' :=
    match type of H with
    | ?P -> _ => assert P as H'; [| specialize (H H')]
    end.
  Tactic Notation "forwardr" ident(H) ident(H') := forwardr H H'.
  
  Create HintDb fresh.
  Hint Resolve freshness_post_no_extension: fresh.
  Hint Resolve freshness_post_inclocal : fresh.

  Definition lift_fresh (P: local_env -> Prop) : Rel_cfg := fun _ '(_,(l,_)) => P l.

  Notation fresh_pre := (fun s1 s2 => lift_fresh (freshness_pre s1 s2)). 
  Notation fresh_post := (fun s1 s2 l => lift_fresh (freshness_post s1 s2 l)). 
  Ltac splits :=
    repeat match goal with
             | |- _ /\ _ => split
             | |- (_ ⩕ _) _ _ => split
           end.

  Arguments freshness_pre : simpl never.
  Arguments freshness_post : simpl never.
  Arguments lift_fresh /.

  Ltac solve_fresh :=
    eauto with fresh;
    match goal with
    | h: freshness_pre ?s ?s' ?l |- freshness_pre ?s _ ?l => apply freshness_pre_shrink_upper_bound with (1 := h); solve_local_count
    | h: freshness_pre _ ?s _ |- freshness_pre _ ?s _ => apply freshness_chain with (1 := h); solve_fresh
    | h: freshness_post _ ?s _ ?x |- freshness_pre ?s _ ?x => eapply freshness_chain with (2 := h); solve_fresh
    | |- freshness_post _ _ _ _ => first [eassumption | eapply freshness_post_inclocal; eassumption | eapply freshness_post_transitive; [eassumption |]]; solve_fresh
    end.

  Ltac solve_state_invariant :=
    cbn;
    match goal with
      |- state_invariant _ _ _ (_, (alist_add _ _ _, _)) =>
      eapply state_invariant_add_fresh; [now eauto | (eassumption || solve_state_invariant) | solve_fresh]
    end.

  Lemma genNExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      (state_invariant σ s1 ⩕ fresh_pre s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕
                     lift_Rel_cfg (fresh_post s1 s2 l) ⩕
                     genNExpr_rel_ind e memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE [PRE PREF] NOFAIL.

    - (* Variable case *)
      (* Reducing the successful compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs. 
        hvred.

        (* The identifier has to be a local one *)
        destruct i0; try_abs.

        (* We establish the postcondition *)
        apply eutt_Ret; cbn; splits; cbn; auto.
        solve_fresh.
        split; auto.
        intros l' MONO; cbn*.
        vstep.
        solve_lu.
        reflexivity.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs.
        break_inner_match_goal; try_abs.
        hvred.
        (* We need to be a bit careful: when stepping the [load], we will need to provide the memory address
           at which we load. This address needs to be in scope when introducing the evar, we are therefore
           forced to look a bit ahead and first use [memory_invariant_GLU].
         *)
        edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.
        rewrite typ_to_dtyp_equation in READ.
        vstep.
        vstep; eauto; reflexivity.

        apply eutt_Ret; cbn; splits; cbn; eauto with fresh.
        -- cbn.
           solve_state_invariant.
        -- split.
           intros l' MONO; cbn*.
           vstep; [solve_lu | reflexivity].
           repeat split.
           solve_sub_alist.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      hvred.

      apply eutt_Ret; cbn; splits; cbn; eauto with fresh.
      split; auto.
      intros l' MONO; cbn*.
      vstep; reflexivity.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      hvred.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { split; auto.
        solve_fresh.
      }
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
      hvred.
      cbn in *.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2.
      {
        split; auto.
        solve_fresh.
      }
      forward IHnexp2; eauto.

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
      cbn in *.

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXPR1 _ MONO2) .
      assert (l1 ⊑ l1) as L1L1 by reflexivity; specialize (EXPR2 _ L1L1). 
      cbn in *.
      hvred.
      vstep.
      {
        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        clear EXPR2 EXPR1.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; splits; cbn.
      {
        solve_state_invariant.
      }
      {
        solve_fresh.
      }
      { split; auto.
        intros ? MONO; cbn.
        vstep; solve_lu; reflexivity.
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        eapply freshness_pre_alist_fresh_specialized; eauto.
        solve_fresh.
      }
        
    - (* NMod *)
      cbn* in *; simp; try_abs.
      hvred.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { split; auto.
        solve_fresh.
      }
      forward IHnexp1; eauto.

      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
      hvred.
      cbn in *.

      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2.
      {
        split; auto.
        solve_fresh.
      }
      forward IHnexp2; eauto.
      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
      cbn; hvred.
      break_match_goal; try_abs...
      hvred.
      
      vstep.
      (* Operator evaluation *)
      {
        vstep; cbn; eauto; try reflexivity.
        eapply EXPR2; reflexivity.
        reflexivity.
        cbn; break_inner_match_goal; try reflexivity.

        (* Division by 0 *)
        exfalso.
        apply Z.eqb_eq in Heqb.
        exfalso. apply n.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }


      apply eutt_Ret; cbn; splits; cbn.
      {
        solve_state_invariant.
      }
      {
        solve_fresh.
      }
      { split; auto.
        intros ? MONO; cbn.
        vstep; solve_lu; reflexivity.
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        eapply freshness_pre_alist_fresh_specialized; eauto.
        solve_fresh.
      }
 
   - (* NAdd *)

     cbn* in *; simp; try_abs.
     hvred.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { split; auto.
       solve_fresh.
     }
     forward IHnexp1; eauto.

     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
     hvred.
     cbn in *.

     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     {
       split; auto.
       solve_fresh.
     }
     forward IHnexp2; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; reflexivity.

     apply eutt_Ret; cbn; splits; cbn.
     {
       solve_state_invariant.
     }
     {
       solve_fresh.
     }
     { split; auto.
       intros ? MONO; cbn.
       vstep; solve_lu; reflexivity.
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       eapply freshness_pre_alist_fresh_specialized; eauto.
       solve_fresh.
     }
     
   - (* NMinus *)

     cbn* in *; simp; try_abs.
     hvred.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { split; auto.
       solve_fresh.
     }
     forward IHnexp1; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
     hvred; cbn in *.

     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     { split; auto.
       solve_fresh.
     }
      forward IHnexp2; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; reflexivity.

     apply eutt_Ret; cbn; splits; cbn.
     {
       solve_state_invariant.
     }
     {
       solve_fresh.
     }
     { split; auto.
       intros ? MONO; cbn.
       vstep; solve_lu; reflexivity.
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       eapply freshness_pre_alist_fresh_specialized; eauto.
       solve_fresh.
     }
 
   - (* NMult *)
     
     cbn* in *; simp; try_abs.
     hvred.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { split; auto.
       solve_fresh.
     }
     forward IHnexp1; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
     hvred; cbn in *.

     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     { split; auto.
       solve_fresh.
     }
      forward IHnexp2; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     (* Operator evaluation *)
     {
        vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }

     apply eutt_Ret; cbn; splits; cbn.
     {
       solve_state_invariant.
     }
     {
       solve_fresh.
     }
     { split; auto.
       intros ? MONO; cbn.
       vstep; solve_lu; reflexivity.
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       eapply freshness_pre_alist_fresh_specialized; eauto.
       solve_fresh.
     }
 
   - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.

End NExpr.

Notation fresh_pre := (fun s1 s2 => lift_fresh (freshness_pre s1 s2)). 
Notation fresh_post := (fun s1 s2 l => lift_fresh (freshness_post s1 s2 l)). 
Definition genNExpr_exp_correct (σ : evalContext) (s : IRState) (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
  fun '(memH,i) '(memV,(l,(g,v))) => 
    eutt Logic.eq 
         (interp_cfg
            (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
            g l memV)
         (Ret (memV,(l,(g,UVALUE_I64 i)))).

Lemma genNExpr_correct :
  forall (* Compiler bits *) (s1 s2: IRState)
    (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
    (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

    genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
    (state_invariant σ s1 ⩕ fresh_pre s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
    no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
    eutt (succ_cfg
            (lift_Rel_cfg (state_invariant σ s2 ⩕ fresh_post s1 s2 l) ⩕ ext_local memH (memV,(l,g)))
         )
         (interp_helix (denoteNExpr σ nexp) memH)
         (interp_cfg (denote_code (convert_typ [] c)) g l memV).
Proof.
  intros.
  eapply eutt_mon; cycle -1.
  eapply genNExpr_correct_ind; eauto.
  intros [(? & ?) |] (? & ? & ? & []) INV; [destruct INV as (SI & ? & EXP & ?) | inv INV].
  cbn in *.
  specialize (EXP l0).
  forward EXP; [reflexivity |].
  split; auto.
  split; auto.
Qed.
