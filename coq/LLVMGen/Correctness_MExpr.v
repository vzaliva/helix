Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Typeclasses Opaque equiv.

Section MExpr.

  Definition invariant_MExpr
             (e : exp typ) : Rel_cfg_T (mem_block * Int64.int) unit :=
    fun '(memH, (mb, mb_sz)) '(memV, (ρ, (g, _))) => 
      exists (ptr : Addr.addr), 
        interp_cfg (translate exp_E_to_instr_E (D.denote_exp (Some DTYPE_Pointer) (convert_typ [] e))) g ρ memV ≈
                   Ret (memV,(ρ,(g,UVALUE_Addr ptr))) /\ 
        (forall i v, mem_lookup i mb ≡ Some v -> get_array_cell memV ptr i DTYPE_Double ≡ inr (UVALUE_Double v)).
  
  Definition preserves_states {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ≡ l.

  Lemma preserves_states_refl:
  forall {R S} memH memV l g n v,
    @preserves_states R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
  Proof.
    intros; repeat split; reflexivity.
  Qed.
  Hint Resolve preserves_states_refl: core.

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

  Lemma genMExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (mexp: MExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (exp: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV) (τ: typ),
      genMExpr mexp s1 ≡ inr (s2, (exp, c, τ)) -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) ->
      no_failure (interp_helix (E := E_cfg) (denoteMExpr σ mexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg
              (
                lift_Rel_cfg (state_invariant σ s2) ⩕
                             preserves_states memH (memV,(l,g)) ⩕
                             invariant_MExpr exp 
           ))
           (interp_helix (denoteMExpr σ mexp) memH)
           (interp_cfg (D.denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros * Hgen Hmeminv NOFAIL.
    destruct mexp as [[vid] | mblock]; cbn* in Hgen; simp.
    cbn.
    unfold denoteMExpr, denotePExpr in *; cbn* in *.
    simp; try_abs.
    hvred.
    edestruct memory_invariant_Ptr as (bkH & ptrV & Mem_LU & LUV & EQ); eauto.
    hstep.
    solve_lu.
    hvred.
    apply eutt_Ret; split; [| split]; cbn; auto.
    eexists; split; eauto.
    break_match_goal; cbn.
    all:vstep; eauto; reflexivity.
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

