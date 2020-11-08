Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Freshness.
Require Import Helix.LLVMGen.Correctness_Invariants.
Import LidBound.

(* Import ProofNotations. *)
Import ListNotations.

Open Scope Z.
Open Scope list.

Set Implicit Arguments.
Set Strict Implicit.

(* The memory invariant *)
Variant state_invariant (σ : evalContext) (s : IRState): memoryH -> config_cfg -> Prop :=
| mk_state_invariant : forall mH mV l g
                          (MINV : memory_invariant σ s mH (mV, (l, g)))
                          (WF   : WF_IRState σ s),
    state_invariant σ s mH (mV,(l,g)).

(* Predicate stating that an (llvm) local variable is relevant to the memory invariant *)
Variant in_Gamma : evalContext -> IRState -> raw_id -> Prop :=
| mk_in_Gamma : forall σ s id τ n v,
    nth_error σ n ≡ Some v ->
    nth_error (Γ s) n ≡ Some (ID_Local id,τ) ->
    WF_IRState σ s ->
    in_Gamma σ s id.

(* Given a range defined by [s1;s2], ensures that the whole range is irrelevant to the memory invariant *)
Definition Gamma_safe σ (s1 s2 : IRState) : Prop :=
  forall id, lid_bound_between s1 s2 id ->
        ~ in_Gamma σ s1 id.

(* Given an initial local env [l1] that reduced to [l2], ensures that no variable relevant to the memory invariant has been modified *)
Definition Gamma_preserved σ s (l1 l2 : local_env) : Prop :=
  forall id, in_Gamma σ s id ->
        l1 @ id ≡ l2 @ id.

(* Given an initial local env [l1] that reduced to [l2], and a range given by [s1;s2], ensures
   that all modified variables came from this range *)
Definition local_scope_modif (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
  fun l2 =>
    forall id,
      alist_find id l2 <> alist_find id l1 ->
      lid_bound_between s1 s2 id.

(* Given an initial local env [l1] that reduced to [l2], and a range given by [s1;s2], ensures
   that this range has been left untouched *)
Definition local_scope_preserved (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
  fun l2 => forall id,
      lid_bound_between s1 s2 id ->
      l2 @ id ≡ l1 @ id.

(* Expresses that only the llvm local env has been modified *)
Definition almost_pure {R S} : config_helix -> config_cfg -> Rel_cfg_T R S :=
  fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) =>
    mh ≡ mh' /\ mi ≡ m /\ gi ≡ g.

(* The memory invariant is stable by evolution of IRStates that preserve Γ *)
Lemma state_invariant_same_Γ :
  ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV) 
    (l : local_env) (g : global_env) (v : uvalue),
    Γ s1 ≡ Γ s2 ->
    ~ in_Gamma σ s1 id →
    state_invariant σ s1 memH (memV, (l, g)) →
    state_invariant σ s2 memH (memV, (alist_add id v l, g)).
Proof.
  intros * EQ NIN INV; inv INV.
  constructor; auto.
  - cbn; rewrite <- EQ.
    intros * LUH LUV.
    generalize LUV; intros INLG;
      eapply MINV in INLG; eauto.
    destruct v0; cbn in *; auto.
    + destruct x; cbn in *; auto.
      break_match_goal.
      * rewrite rel_dec_correct in Heqb; subst.
        exfalso; eapply NIN.
        econstructor; eauto.
      * apply neg_rel_dec_correct in Heqb.
        rewrite remove_neq_alist; eauto.
        all: typeclasses eauto.
    + destruct x; cbn; auto.
      break_match_goal.
      * rewrite rel_dec_correct in Heqb; subst.
        exfalso; eapply NIN.
        econstructor; eauto.
      * apply neg_rel_dec_correct in Heqb.
        rewrite remove_neq_alist; eauto.
        all: typeclasses eauto.
    + destruct x; cbn in *; auto.
      destruct INLG as (? & ? & ? & ? &?).
      do 2 eexists; split; [| split]; eauto.
      break_match_goal.
      * rewrite rel_dec_correct in Heqb; subst.
        exfalso; eapply NIN.
        econstructor; eauto.
      * apply neg_rel_dec_correct in Heqb.
        rewrite remove_neq_alist; eauto.
        all: typeclasses eauto.
  - red; rewrite <- EQ; apply WF.
Qed.

Lemma state_invariant_memory_invariant' :
  forall σ s mH mV l g,
    state_invariant σ s mH (mV,(l,g)) ->
    memory_invariant σ s mH (mV,(l,g)).
Proof.
  intros * H; inv H; auto.
Qed.
Hint Resolve state_invariant_memory_invariant' : core.

(* The memory invariant is stable by extension of the local environment
   if the variable belongs to a Γ safe interval
 *)
Lemma state_invariant_add_fresh :
  ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV) 
    (l : local_env) (g : global_env) (v : uvalue),
    incLocal s1 ≡ inr (s2, id)
    -> Gamma_safe σ s1 s2
    → state_invariant σ s1 memH (memV, (l, g))
    → state_invariant σ s2 memH (memV, (alist_add id v l, g)).
Proof.
  intros * INC SAFE INV.
  eapply state_invariant_same_Γ; [| | eauto].
  symmetry; eapply incLocal_Γ; eauto.
  apply SAFE.
  auto using lid_bound_between_incLocal.
Qed.

(* If no change has been made, all changes are certainly in the interval *)
Lemma local_scope_modif_refl: forall s1 s2 l, local_scope_modif s1 s2 l l.
Proof.
  intros; red; intros * NEQ.
  contradiction NEQ; auto.
Qed.
Hint Resolve local_scope_modif_refl: core.

(* If a single change has been made, we just need to check that it was in the interval *)
Lemma local_scope_modif_add: forall s1 s2 l r v,
    lid_bound_between s1 s2 r ->   
    local_scope_modif s1 s2 l (alist_add r v l).
Proof.
  intros * BET.
  red; intros * NEQ.
  destruct (rel_dec_p r id).
  - subst; rewrite alist_find_add_eq in NEQ; auto.
  - rewrite alist_find_neq in NEQ; auto.
    contradiction NEQ; auto.
Qed.

(* If all changes made are in the empty interval, then no change has been made *)
Lemma local_scope_modif_empty_scope:
  forall (l1 l2 : local_env) id s,
    local_scope_modif s s l1 l2 ->
    l2 @ id ≡ l1 @ id.
Proof.
  intros * SCOPE.
  red in SCOPE.
  edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption|].
  exfalso; apply SCOPE in NEQ; clear SCOPE.
  destruct NEQ as (? & ? & ? & ? & ? & ? & ?).
  cbn in *; inv H2.
  lia.
Qed.

(* If I know that all changes came from [s2;s3] and that I consider a variable from another interval, then it hasn't changed *)
Lemma local_scope_modif_out:
  forall (l1 l2 : local_env) id s1 s2 s3,
    s1 << s2 ->
    lid_bound_between s1 s2 id ->
    local_scope_modif s2 s3 l1 l2 ->
    l2 @ id ≡ l1 @ id.
Proof.
  intros * LT BOUND SCOPE.
  red in SCOPE.
  edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
  exfalso; apply SCOPE in NEQ; clear SCOPE.
  destruct NEQ as (? & ? & ? & ? & ? & ? & ?).
  destruct BOUND as (? & ? & ? & ? & ? & ? & ?).
  cbn in *.
  inv H2; inv H6.
  unfold IRState_lt in *.
  exfalso; eapply IdLemmas.not_ends_with_nat_neq; [| | | eassumption]; auto.
  lia.
Qed.

(* If no change occurred, it left any interval untouched *)
Lemma local_scope_preserved_refl : forall s1 s2 l,
    local_scope_preserved s1 s2 l l.
Proof.
  intros; red; intros; reflexivity.
Qed.

(* If no change occurred, it left Gamma safe *)
Lemma Gamma_preserved_refl : forall s1 s2 l,
    Gamma_preserved s1 s2 l l.
Proof.
  intros; red; intros; reflexivity.
Qed.

(* If I know that an interval leaves Gamma safe, I can shrink it on either side and it still lives Gamma safe *)
Lemma Gamma_safe_shrink : forall σ s1 s2 s3 s4,
    Gamma_safe σ s1 s4 ->
    Γ s1 ≡ Γ s2 ->
    s1 <<= s2 ->
    s3 <<= s4 ->
    Gamma_safe σ s2 s3.
Proof.
  unfold Gamma_safe; intros * SAFE EQ LE1 LE2 * (? & s & s' & ? & ? & ? & ?) IN.
  apply SAFE with id.
  exists x, s, s'.
  repeat split; eauto.
  solve_local_count.
  solve_local_count.
  inv IN.
  econstructor.
  eauto.
  rewrite EQ; eauto.
  eapply WF_IRState_Γ; eauto.
Qed.

(* If I have modified an interval, other intervals are preserved *)
Lemma local_scope_preserve_modif:
  forall s1 s2 s3 l1 l2,
    s2 << s3 ->
    local_scope_modif s2 s3 l1 l2 ->
    local_scope_preserved s1 s2 l1 l2. 
Proof.
  intros * LE MOD.
  red. intros * BOUND.
  red in MOD.
  edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
  apply MOD in NEQ; clear MOD.
  destruct NEQ as (msg & s & s' & ? & ? & ? & ?).
  cbn in *; inv H2.
  destruct BOUND as (msg' & s' & s'' & ? & ? & ? & ?).
  cbn in *; inv H5.
  destruct s as [a s b]; cbn in *; clear a b.
  destruct s' as [a s' b]; cbn in *; clear a b.
  destruct s1 as [a s1 b]; cbn in *; clear a b.
  destruct s2 as [a s2 b], s3 as [a' s3 b']; cbn in *.
  red in LE; cbn in *.
  clear a b a' b'.
  exfalso; eapply IdLemmas.not_ends_with_nat_neq; [| | | eassumption]; auto.
  lia.
Qed.

Lemma in_Gamma_Gamma_eq:
  forall σ s1 s2 id,
    Γ s1 ≡ Γ s2 ->
    in_Gamma σ s1 id ->
    in_Gamma σ s2 id.
Proof.
  intros * EQ IN; inv IN; econstructor; eauto.
  rewrite <- EQ; eauto.
  eapply WF_IRState_Γ; eauto.
Qed.

Lemma Gamma_preserved_Gamma_eq:
  forall σ s1 s2 l1 l2,
    Γ s1 ≡ Γ s2 ->
    Gamma_preserved σ s1 l1 l2 ->
    Gamma_preserved σ s2 l1 l2.
Proof.
  unfold Gamma_preserved. intros * EQ PRE * IN.
  apply PRE.
  eauto using in_Gamma_Gamma_eq.
Qed.

(* If an interval is Gamma safe, and that all changes occurred in this interval, then the changes preserved Gamma. *)
Lemma Gamma_preserved_if_safe :
  forall σ s1 s2 l1 l2,
    Gamma_safe σ s1 s2 ->
    local_scope_modif s1 s2 l1 l2 ->
    Gamma_preserved σ s1 l1 l2.
Proof.
  intros * GS L.
  red.
  intros ? IN.
  red in GS.
  red in L.
  edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
  exfalso; eapply GS; eauto.
Qed.

(* Belonging to an interval can relaxed down *)
Lemma lid_bound_between_shrink_down :
  forall s1 s2 s3 id,
    s1 <<= s2 ->
    lid_bound_between s2 s3 id ->
    lid_bound_between s1 s3 id.
Proof.
  intros * LE (? & ? & ? & ? & ? & ? & ?).
  do 3 eexists.
  repeat split; eauto.
  solve_local_count.
Qed.

(* Belonging to an interval can relaxed up *)
Lemma lid_bound_between_shrink_up :
  forall s1 s2 s3 id,
    s2 <<= s3 ->
    lid_bound_between s1 s2 id ->
    lid_bound_between s1 s3 id.
Proof.
  intros * EQ (? & s & s' & ? & ? & ? & ?).
  do 3 eexists.
  repeat split; eauto.
  solve_local_count.
Qed.

(* Transitivity of the changes belonging to intervals *)
Lemma local_scope_modif_trans :
  forall s1 s2 s3 l1 l2 l3,
    s1 <<= s2 ->
    s2 <<= s3 ->
    local_scope_modif s1 s2 l1 l2 ->
    local_scope_modif s2 s3 l2 l3 ->
    local_scope_modif s1 s3 l1 l3.
Proof.
  unfold local_scope_modif; intros * LE1 LE2 MOD1 MOD2 * INEQ.
  destruct (alist_find_eq_dec_local_env id l1 l2) as [EQ | NEQ].
  - destruct (alist_find_eq_dec_local_env id l2 l3) as [EQ' | NEQ'].
    + contradiction INEQ; rewrite <- EQ; auto.
    + apply MOD2 in NEQ'.
      eauto using lid_bound_between_shrink_down.
  - apply MOD1 in NEQ.
    eauto using lid_bound_between_shrink_up.
Qed.

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
  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.

  Definition genNExpr_exp_correct σ s1 s2 (e: exp typ) 
    : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l',
        local_scope_preserved s1 s2 l l' ->
        Gamma_preserved σ s1 l l' ->
        interp_cfg
          (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
          g l' memV ≈
          Ret (memV,(l',(g,UVALUE_I64 i))).

  Record genNExpr_post
         (e : exp typ)
         σ s1 s2
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct σ s1 s2 e mf stf;
    is_almost_pure : almost_pure mi sti mf stf; 
    extends : local_scope_modif s1 s2 (fst (snd sti)) (fst (snd stf));
    exp_in_scope : forall id, e ≡ EXP_Ident (ID_Local id) -> ((exists v, alist_In id (fst (snd sti)) v) \/ (lid_bound_between s1 s2 id /\ s1 << s2));
    Gamma_cst : Γ s2 ≡ Γ s1;
    Mono_IRState : s1 << s2 \/ fst (snd sti) ≡ fst (snd stf)
    }.

  Lemma genNExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) ((* li *) l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      (state_invariant σ s1) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      Gamma_safe σ s1 s2 ->
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕
                     genNExpr_post e (* li *) σ s1 s2 memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE PRE SAFE NOFAIL.
    - (* Variable case *)
      (* Reducing the successful compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs. 
        hvred.

        (* The identifier has to be a local one *)
        destruct i0.
        inv PRE; try_abs.

        (* We establish the postcondition *)
        apply eutt_Ret; split; [| split]; cbn; eauto.
        * intros l' LOC GAM; cbn*.
          inv PRE.
          vstep.
          cbn.
          red in GAM.
          erewrite <- GAM.
          eapply memory_invariant_LLU; eauto.
          econstructor;eauto.
          reflexivity.
        * intros * EQ; inv EQ.
          left.
          eexists.
          eapply memory_invariant_LLU; eauto.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs.
        break_inner_match_goal; try_abs.
        2:inv PRE; try_abs.
 
        hvred.
        (* We need to be a bit careful: when stepping the [load], we will need to provide the memory address
           at which we load. This address needs to be in scope when introducing the evar, we are therefore
           forced to look a bit ahead and first use [memory_invariant_GLU].
         *)

        edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.

        rewrite typ_to_dtyp_equation in READ.
        vstep.
        vstep; eauto; reflexivity.
        apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
        * eapply state_invariant_add_fresh; eauto.
        * intros l' LOC GAM; cbn*.
          vstep; [ | reflexivity].
          cbn.
          red in LOC; rewrite LOC.
          rewrite alist_find_add_eq; reflexivity.
          eauto using lid_bound_between_incLocal.          
        * apply local_scope_modif_add.
          auto using lid_bound_between_incLocal.
        * intros * EQ; inv EQ; right.
          split; [auto using lid_bound_between_incLocal | solve_local_count].
        * eauto using incLocal_Γ.
        * left; solve_local_count.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      hvred.

      apply eutt_Ret; split; [| split]; cbn; eauto.
      intros l' MONO; cbn*.
      vstep; reflexivity.
      intros * EQ; inv EQ.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      hvred.
      rename i into s2, i0 into s3, s2 into s4.
      clean_goal.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { inv PRE; split; auto.
        (* solve_fresh. *)
      }
      forward IHnexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn* in *; inv_eqs.
      (* rename H into VAR1. *)
      hvred.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2.
      {
        inv PRE; inv PRE1.
        constructor; auto.
      }

      forward IHnexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp2; eauto. 

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn* in *; inv_eqs.
      (* rename H into VAR2. *)

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        clear EXP1 EXP2 VAR1 VAR2.
        clean_goal.
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      hvred.
      vstep.
      {
        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.

    - (* NMod *)
      cbn* in *; simp; try_abs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      clean_goal.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { inv PRE; split; auto.
        (* solve_fresh. *)
      }
      forward IHnexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn* in *; inv_eqs.
      (* rename H into VAR1. *)
      hvred.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2.
      {
        inv PRE; inv PRE1.
        constructor; auto.
      }

      forward IHnexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp2; eauto. 

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn* in *; inv_eqs.
      (* rename H into VAR2. *)

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        clear EXP1 EXP2 VAR1 VAR2.
        clean_goal.
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      hvred.
      vstep.
      {
        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.
 
   - (* NAdd *)

     cbn* in *; simp; try_abs.
     hvred.

     rename i into s2, i0 into s3, s2 into s4.
     clean_goal.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { inv PRE; split; auto.
       (* solve_fresh. *)
     }
     forward IHnexp1; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp1; eauto.
     
     (* e1 *)
     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
     cbn* in *; inv_eqs.
     (* rename H into VAR1. *)
     hvred.

     (* e2 *)
     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     {
       inv PRE; inv PRE1.
       constructor; auto.
     }

     forward IHnexp2; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp2; eauto. 

     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
     cbn* in *; inv_eqs.

     specialize (EXP1 l1) .
     specialize (EXP2 l1) .
     forward EXP2.
     auto using local_scope_preserved_refl.
     forward EXP2.
     auto using Gamma_preserved_refl.
     forward EXP1.
     {
       clear EXP1 EXP2 VAR1 VAR2.
       clean_goal.
       destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
       eapply local_scope_preserve_modif; eauto.
     }
     forward EXP1.
     {
       apply Gamma_preserved_Gamma_eq with s2; auto.
       eapply Gamma_preserved_if_safe; eauto.
       eapply Gamma_safe_shrink; eauto; solve_local_count.
     }

     hvred.
     vstep; cbn; eauto.
     vstep; cbn; eauto; reflexivity.

     apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
     + eapply state_invariant_add_fresh; eauto.
       eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
       solve_local_count.
       solve_local_count.
     + intros * SCO GAM.
       vstep; eauto.
       cbn.
       erewrite SCO,alist_find_add_eq.
       reflexivity.
       apply lid_bound_between_shrink_down with s3.
       solve_local_count.
       eapply lid_bound_between_incLocal; eauto.
       reflexivity.
     + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
       eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
       eauto using local_scope_modif_add, lid_bound_between_incLocal.
     + intros ? EQ; inv EQ.
       right; split; [| solve_local_count].
       apply lid_bound_between_shrink_down with s3; [solve_local_count |].
       eauto using lid_bound_between_incLocal.
     + rewrite <- GAM1, <- GAM2.
       eapply incLocal_Γ; eauto.
     + left; solve_local_count.
       
   - (* NMinus *)

     cbn* in *; simp; try_abs.
     hvred.

     rename i into s2, i0 into s3, s2 into s4.
     clean_goal.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { inv PRE; split; auto.
       (* solve_fresh. *)
     }
     forward IHnexp1; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp1; eauto.
     
     (* e1 *)
     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
     cbn* in *; inv_eqs.
     (* rename H into VAR1. *)
     hvred.

     (* e2 *)
     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     {
       inv PRE; inv PRE1.
       constructor; auto.
     }

     forward IHnexp2; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp2; eauto. 

     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
     cbn* in *; inv_eqs.

     specialize (EXP1 l1) .
     specialize (EXP2 l1) .
     forward EXP2.
     auto using local_scope_preserved_refl.
     forward EXP2.
     auto using Gamma_preserved_refl.
     forward EXP1.
     {
       clear EXP1 EXP2 VAR1 VAR2.
       clean_goal.
       destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
       eapply local_scope_preserve_modif; eauto.
     }
     forward EXP1.
     {
       apply Gamma_preserved_Gamma_eq with s2; auto.
       eapply Gamma_preserved_if_safe; eauto.
       eapply Gamma_safe_shrink; eauto; solve_local_count.
     }

     hvred.
     vstep; cbn; eauto.
     vstep; cbn; eauto; reflexivity.

     apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
     + eapply state_invariant_add_fresh; eauto.
       eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
       solve_local_count.
       solve_local_count.
     + intros * SCO GAM.
       vstep; eauto.
       cbn.
       erewrite SCO,alist_find_add_eq.
       reflexivity.
       apply lid_bound_between_shrink_down with s3.
       solve_local_count.
       eapply lid_bound_between_incLocal; eauto.
       reflexivity.
     + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
       eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
       eauto using local_scope_modif_add, lid_bound_between_incLocal.
     + intros ? EQ; inv EQ.
       right; split; [| solve_local_count].
       apply lid_bound_between_shrink_down with s3; [solve_local_count |].
       eauto using lid_bound_between_incLocal.
     + rewrite <- GAM1, <- GAM2.
       eapply incLocal_Γ; eauto.
     + left; solve_local_count.
 
   - (* NMult *)
     
     cbn* in *; simp; try_abs.
     hvred.

     rename i into s2, i0 into s3, s2 into s4.
     clean_goal.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { inv PRE; split; auto.
       (* solve_fresh. *)
     }
     forward IHnexp1; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp1; eauto.
     
     (* e1 *)
     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
     cbn* in *; inv_eqs.
     (* rename H into VAR1. *)
     hvred.

     (* e2 *)
     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     {
       inv PRE; inv PRE1.
       constructor; auto.
     }

     forward IHnexp2; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp2; eauto. 

     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
     cbn* in *; inv_eqs.

     specialize (EXP1 l1) .
     specialize (EXP2 l1) .
     forward EXP2.
     auto using local_scope_preserved_refl.
     forward EXP2.
     auto using Gamma_preserved_refl.
     forward EXP1.
     {
       clear EXP1 EXP2 VAR1 VAR2.
       clean_goal.
       destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
       eapply local_scope_preserve_modif; eauto.
     }
     forward EXP1.
     {
       apply Gamma_preserved_Gamma_eq with s2; auto.
       eapply Gamma_preserved_if_safe; eauto.
       eapply Gamma_safe_shrink; eauto; solve_local_count.
     }

     hvred.
     vstep; cbn; eauto.
     vstep; cbn; eauto; try reflexivity.
     cbn.
     break_inner_match; reflexivity.
     
     apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
     + eapply state_invariant_add_fresh; eauto.
       eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
       solve_local_count.
       solve_local_count.
     + intros * SCO GAM.
       vstep; eauto.
       cbn.
       erewrite SCO,alist_find_add_eq.
       reflexivity.
       apply lid_bound_between_shrink_down with s3.
       solve_local_count.
       eapply lid_bound_between_incLocal; eauto.
       reflexivity.
     + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
       eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
       eauto using local_scope_modif_add, lid_bound_between_incLocal.
     + intros ? EQ; inv EQ.
       right; split; [| solve_local_count].
       apply lid_bound_between_shrink_down with s3; [solve_local_count |].
       eauto using lid_bound_between_incLocal.
     + rewrite <- GAM1, <- GAM2.
       eapply incLocal_Γ; eauto.
     + left; solve_local_count.
 
   - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.

End NExpr.

(* Definition genNExpr_exp_correct (σ : evalContext) (s : IRState) (e: exp typ) *)
(*   : Rel_cfg_T DynamicValues.int64 unit := *)
(*   fun '(memH,i) '(memV,(l,(g,v))) =>  *)
(*     eutt Logic.eq  *)
(*          (interp_cfg *)
(*             (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e))) *)
(*             g l memV) *)
(*          (Ret (memV,(l,(g,UVALUE_I64 i)))). *)

(* Lemma genNExpr_correct : *)
(*   forall (* Compiler bits *) (s1 s2: IRState) *)
(*     (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH)  *)
(*     (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV), *)

(*     genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *) *)
(*     (state_invariant_pre σ s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *) *)
(*     no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *) *)
(*     eutt (succ_cfg *)
(*             (lift_Rel_cfg (state_invariant_post σ s1 s2 l) ⩕ *)
(*                           genNExpr_exp_correct σ s2 e ⩕ *)
(*                           ext_local memH (memV,(l,g))) *)
(*          ) *)
(*          (interp_helix (denoteNExpr σ nexp) memH) *)
(*          (interp_cfg (denote_code (convert_typ [] c)) g l memV). *)
(* Proof. *)
(*   intros. *)
(*   eapply eutt_mon; cycle -1. *)
(*   eapply genNExpr_correct_ind; eauto. *)
(*   intros [(? & ?) |] (? & ? & ? & []) INV; [destruct INV as ((SI & ?) & EXP & ?) | inv INV]. *)
(*   cbn in *. *)
(*   specialize (EXP l0). *)
(*   forward EXP; [reflexivity |]. *)
(*   split; auto. *)
(*   split; auto. *)
(*   split; auto. *)
(* Qed. *)

(* Opaque incBlockNamed. *)
(* Opaque incVoid. *)
(* Opaque incLocal. *)

(* Lemma state_invariant_genNExpr : *)
(*   ∀ (n : NExpr) (σ : evalContext) (s s' : IRState) (ec : exp typ * code typ) (memH : memoryH) (stV : config_cfg), *)
(*     genNExpr n s ≡ inr (s', ec) → state_invariant σ s memH stV → state_invariant σ s' memH stV. *)
(* Proof. *)
(*   induction n; *)
(*     intros σ s s' ec memH stV GEN SINV; *)
(*     cbn in GEN; simp; *)
(*       repeat *)
(*         match goal with *)
(*         | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ => *)
(*           destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst *)
(*         end; *)
(*       auto; try solve_state_invariant. *)
(* Qed. *)

(* Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_genNExpr; [eassumption | solve_state_invariant] : SolveStateInv. *)
