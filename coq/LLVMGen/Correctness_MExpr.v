Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Import ProofNotations.

Set Implicit Arguments.
Set Strict Implicit.

Typeclasses Opaque equiv.
Remove Hints
       equiv_default_relation
       abstract_algebra.sg_op_proper
       abstract_algebra.sm_proper
       abstract_algebra.comp_proper
       orders.po_preorder
       orders.total_order_po
       orders.le_total
       orders.join_sl_order
       orders.lattice_order_join
       orders.lattice_order_meet
       orders.strict_po_po
       orders.srorder_po
       strong_setoids.binary_strong_morphism_proper
       semirings.FullPseudoOrder_instance_0
       minmax.LatticeOrder_instance_0
       workarounds.equivalence_proper : typeclass_instances.

Section MExpr.

  Definition invariant_MExpr
             (σ : evalContext)
             (s : IRState) (mexp : MExpr) (e : exp typ) : Rel_cfg_T (mem_block * Int64.int) unit :=
    fun '(memH, (mb, mb_sz)) '(memV, (ρ, (g, _))) =>
      (exists ptr i (vid : nat) (mid : nat) (size : Int64.int) (sz : int), (* TODO: sz ≈ size? *)
        Ret (memV,(ρ,(g,UVALUE_Addr ptr))) ≈ interp_cfg (translate exp_E_to_instr_E (D.denote_exp (Some DTYPE_Pointer) (convert_typ [] e))) g ρ memV /\
        memory_lookup memH mid ≡ Some mb /\
        in_local_or_global_addr ρ g i ptr /\
        nth_error σ vid ≡ Some (DSHPtrVal mid size) /\
        nth_error (Γ s) vid ≡ Some (i, TYPE_Pointer (TYPE_Array sz TYPE_Double))) /\
      evalMExpr memH σ mexp ≡ inr (mb, mb_sz).

  (* TODO: like ext_local, but locals also don't change. Not sure what to call this... *)
  Definition preserves_states {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ≡ l.

  Lemma preserves_states_refl:
  forall {R S} memH memV l g n v,
    @preserves_states R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
  Proof.
    intros; repeat split; reflexivity.
  Qed.
  Hint Resolve preserves_states_refl: core.

  Record genMExpr_rel
         (σ : evalContext)
         (s : IRState)
         (mexp : MExpr)
         (e  : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * (mem_block * Int64.int)) (stf : config_cfg_T unit)
    : Prop :=
    {
    mexp_correct :invariant_MExpr σ s mexp e mf stf;
    m_preserves : preserves_states mi sti mf stf
    }.

 (* ;; ) *)

  Lemma memory_invariant_Ptr : forall vid σ s memH memV l g a size x sz,
      state_invariant σ s memH (memV, (l, g)) ->
      nth_error σ vid ≡ Some (DSHPtrVal a size) ->
      nth_error (Γ s) vid ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
      ∃ (bk_helix : mem_block) (ptr_llvm : Addr.addr),
        memory_lookup memH a ≡ Some bk_helix
        ∧ in_local_or_global_addr l g x ptr_llvm
        ∧ (∀ (i : Memory.NM.key) (v : binary64), mem_lookup i bk_helix ≡ Some v → get_array_cell memV ptr_llvm i DTYPE_Double ≡ inr (UVALUE_Double v)).
  Proof.
    intros * [MEM _ _] LU1 LU2; eapply MEM in LU1; eapply LU1 in LU2; eauto.
  Qed.

  Lemma failure_throw : forall E Y X s (k : Y -> _) m,
      ~ no_failure (interp_helix (X := X) (E := E) (ITree.bind (Exception.throw s) k) m).
  Proof.
  Admitted.


  (** ** Compilation of MExpr
  *)
  Lemma genMExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (mexp: MExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (exp: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV) (τ: typ),
      genMExpr mexp s1 ≡ inr (s2, (exp, c, τ)) -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) ->
      no_failure (interp_helix (E := E_cfg) (denoteMExpr σ mexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg
              (lift_Rel_cfg (state_invariant σ s2) ⩕ genMExpr_rel σ s2 mexp exp memH (mk_config_cfg memV l g)))
           (interp_helix (denoteMExpr σ mexp) memH)
           (interp_cfg (D.denote_code (convert_typ [] c)) g l memV).
  Proof with rauto.
    intros * Hgen Hmeminv NOFAIL.
    generalize Hmeminv; intros WF; apply IRState_is_WF in WF.

    unfold denoteMExpr in *; cbn* in *.

    destruct mexp as [[vid] | mblock]; [| cbn in Hgen; inv Hgen].

    cbn* in Hgen; simp.
    unfold denotePExpr in *; cbn* in *.
    simp; try (abs_by_WF || abs_by failure_throw).

    edestruct memory_invariant_Ptr as (bkH & ptrV & Mem_LU & LUV & EQ); eauto.

    cbn*... 2:eauto.
    apply eutt_Ret.
    
    split; auto.
    split; auto.
    split.
    { do 6 eexists.
      splits; eauto.

      destruct i0;
        cbn in *; cbn...

        cbn... 2 : eauto. 3 : eauto. 2 : cbn... 2 : reflexivity. 
        reflexivity.
      }
    { 
      cbn*.
      do 2 match_rewrite; reflexivity.
    }
  Qed.

  (* TODO: move these, and use them more. *)

  Lemma genMExpr_memH : forall σ s mexp e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s mexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memH ≡ memH'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_memV : forall σ s mexp e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s mexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memV ≡ memV'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_g : forall σ s mexp e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s mexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      g ≡ g'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_l : forall σ s mexp e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s mexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      l ≡ l'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_preserves_WF:
    forall mexp s s' σ x,
      WF_IRState σ s ->
      genMExpr mexp s ≡ inr (s',x) ->
      WF_IRState σ s'.
  Proof.
    induction mexp; intros * WF GEN; cbn* in GEN; simp; auto.
  Qed.

  Lemma genMExpr_array : forall {s1 s2 m e c t},
      genMExpr m s1 ≡ inr (s2, (e, c, t)) ->
      exists sz, t ≡ TYPE_Array sz TYPE_Double.
  Proof.
    intros s1 s2 m e c t H.
    destruct m; cbn in H; inv H.
    simp.
    exists sz.
    reflexivity.
  Qed.

End MExpr.

Ltac genMExpr_rel_subst :=
  match goal with
  | MEXP : genMExpr_rel ?σ ?s ?mexp ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?mb) (?memV', (?l', (?g', ?uv))) |- _ =>
    let H := fresh in
    pose proof genMExpr_memH MEXP as H; subst memH';
    pose proof genMExpr_memV MEXP as H; subst memV';
    pose proof genMExpr_g MEXP as H; subst g';
    pose proof genMExpr_l MEXP as H; subst l'
  end.
