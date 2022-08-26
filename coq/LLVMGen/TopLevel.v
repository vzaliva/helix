Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.EvalDenoteEquiv.
Require Import Helix.DynWin.DynWinProofs.
Require Import Helix.DynWin.DynWinTopLevel.
Require Import Helix.LLVMGen.Correctness_GenIR.
Require Import Helix.LLVMGen.Init.
Require Import Helix.LLVMGen.Correctness_Invariants.

Import ReifyRHCOL.
Import RHCOLtoFHCOL.
Import RSigmaHCOL.
Import RHCOL.
Import DynWin.
Import RHCOLtoFHCOL.
Import RHCOLEval.
Import FHCOLEval.
Import CarrierType.
Import SemNotations.
Import BidBound.

Lemma top_to_FHCOL :
  forall (a : Vector.t CarrierA 3) (* parameter *)
    (x : Vector.t CarrierA dynwin_i)  (* input *)
    (y : Vector.t CarrierA dynwin_o), (* output *)

      (* Evaluation of the source program.
         The program is fixed and hard-coded: the result is not generic,
         we provide a "framework". *)
      dynwin_orig a x = y →

      (* We cannot hide away the [R] level as we axiomatize the real to float
       approximation performed *)
      ∀ (dynwin_F_memory : memoryH)
        (dynwin_F_σ : evalContext)
        (dynwin_fhcol : FHCOL.DSHOperator),

        RHCOLtoFHCOL.translate DynWin_RHCOL = inr dynwin_fhcol →

        heq_memory () RF_CHE (dynwin_R_memory a x) dynwin_F_memory →
        heq_evalContext () RF_NHE RF_CHE dynwin_R_σ dynwin_F_σ ->

        ∀ a_rmem x_rmem : RHCOLEval.mem_block,
          RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_a_addr = Some a_rmem →
          RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_x_addr = Some x_rmem →

          DynWinInConstr a_rmem x_rmem →

          (* At the R-level, there are a memory and a memory block st... *)
          ∃ (r_omemory : RHCOLEval.memory) (y_rmem : RHCOLEval.mem_block),

            (* Evaluation succeeds and returns this memory *)
            RHCOLEval.evalDSHOperator dynwin_R_σ DynWin_RHCOL (dynwin_R_memory a x) (RHCOLEval.estimateFuel DynWin_RHCOL) = Some (inr r_omemory) ∧

            (* At the expected [y] address is found the memory block *)
              RHCOLEval.memory_lookup r_omemory dynwin_y_addr = Some y_rmem ∧


              MSigmaHCOL.MHCOL.ctvector_to_mem_block y = y_rmem ∧

              (* At the F-level, there are a memory and a memory block st... *)
              (∃ (f_omemory : memoryH) (y_fmem : mem_block),

                  (* Evaluation succeeds and returns this memory *)
                  evalDSHOperator dynwin_F_σ dynwin_fhcol dynwin_F_memory (estimateFuel dynwin_fhcol) = Some (inr f_omemory) ∧

                    (* At the expected [y] address is found the memory block *)
                    memory_lookup f_omemory dynwin_y_addr = Some y_fmem ∧

                    (* And this memory block is related to the R version *)
                    DynWinOutRel a_rmem x_rmem y_rmem y_fmem)
.
Proof.
  intros.
  eapply HCOL_to_FHCOL_Correctness; eauto.
Qed.

(* TODO *)
Section Program.

  Local Obligation Tactic := cbv;auto.
  Program Definition dynwin_i' : Int64.int := Int64.mkint (Z.of_nat dynwin_i) _.
  Program Definition dynwin_o' : Int64.int := Int64.mkint (Z.of_nat dynwin_o) _.
  Program Definition three : Int64.int := Int64.mkint 3 _.
  (* TODO pull and recompile?? *)
  (* TODO convert R global type signature to F global type signature? *)
  (* IZ : Construct the globals here *)
  Definition dynwin_globals' : list (string * FHCOL.DSHType)
    := cons ("a",DSHPtr three) nil.

  (* Here I should be able to compute the operator instead of quantifying over it in the statement *)
  Definition dynwin_fhcolp : FHCOL.DSHOperator -> FSHCOLProgram :=
    mkFSHCOLProgram dynwin_i' dynwin_o' "dyn_win" dynwin_globals'.

  (* Where do I build my data to pass to compile_w_main? *)
  (* Lookup in fmem yaddr xaddr and aaddr and flatten *)
  Definition dynwin_data (a_fmem x_fmem : FHCOLEval.mem_block): list binary64.
  Admitted.

End Program.

(* (* with init step  *) *)
(* Lemma compiler_correct_aux: *)
(*   forall (p:FSHCOLProgram) *)
(*     (data:list binary64) *)
(*     (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))), *)
(*     forall s, compile_w_main p data newState ≡ inr (s,pll) -> *)
(*     eutt (succ_mcfg (bisim_full nil s)) (semantics_FSHCOL p data) (semantics_llvm pll). *)
(* Proof. *)
(*   intros * COMP. *)
(*   unshelve epose proof memory_invariant_after_init _ _ (conj _ COMP) as INIT_MEM. *)
(*   helix_initial_memory *)
(*   unfold compile_w_main,compile in COMP. *)
(*   cbn* in COMP. *)
(*   simp. *)
(*   unshelve epose proof @compile_FSHCOL_correct _ _ _ (* dynwin_F_σ dynwin_F_memory *) _ _ _ _ _ _ _ _ _ Heqs _ _ _ _. *)

Set Nested Proofs Allowed.
Import MonadNotation.
Local Open Scope monad_scope.
Import ListNotations.

(* Definition helix_initializer (p:FSHCOLProgram) (data:list binary64) *)
(*   : itree Event (nat*nat) := *)
(*   '(data, σ) <- denote_initFSHGlobals data p.(Data.globals) ;; *)
(*   xindex <- trigger (MemAlloc p.(i));; *)
(*   yindex <- trigger (MemAlloc p.(o));; *)
(*   let '(data, x) := constMemBlock (MInt64asNT.to_nat p.(i)) data in *)
(*   trigger (MemSet xindex x);; *)
(*   Ret (xindex,yindex). *)

Definition helix_finalizer (p:FSHCOLProgram) (yindex : nat)
  : itree Event _ :=
  bk <- trigger (MemLU "denote_FSHCOL" yindex);;
  lift_Derr (mem_to_list "Invalid output memory block" (MInt64asNT.to_nat p.(o)) bk).

(* Replacement for [denote_FSHCOL] where the memory is shallowy initialized using [helix_initial_memory].
   In this setup, the address at which [x] and [y] are allocated in memory is explicitly hard-coded rather than relying on the exact behavior of [Alloc].

 *)
Definition denote_FSHCOL' (p:FSHCOLProgram) (data:list binary64) σ
  : itree Event (list binary64) :=
  let xindex := List.length p.(globals) - 1 in
  let yindex := S xindex in
  let σ := List.app σ
                    [(DSHPtrVal yindex p.(o),false);
                     (DSHPtrVal xindex p.(i),false)]
  in
  denoteDSHOperator σ (p.(Data.op) : DSHOperator);;
  helix_finalizer p yindex.

Definition semantics_FSHCOL' (p: FSHCOLProgram) (data : list binary64) σ mem
  : failT (itree E_mcfg) (memoryH * list binary64) :=
  interp_helix (denote_FSHCOL' p data σ) mem.

(* TODO
   We want to express that the computed value is the right one
   Confused: compile with main returns the content of the [y] global.
   Is that the data or the address of the data in memory?
   The former makes little sense to me, but the latter even less as we are looking for a vector.
 *)
(* This is similar to [DynWinOutRel], see that for details.

   Looking at the definition of [DynWinOutRel],
   <<
    hopt_r (flip CType_impl)
      (RHCOLEval.mem_lookup dynwin_y_offset y_r)
      (FHCOLEval.mem_lookup dynwin_y_offset y_64).
   >>

   [FHCOLEval.mem_lookup dynwin_y_offset y_64]
   is the FHCOL output and needs to be proven equivalent to [llvm_out] here.

   [RHCOLEval.mem_lookup dynwin_y_offset y_r]
   is the RHCOL output and is already known to be equivalent to HCOL ([hcol_out] here).
 *)
Definition final_rel_val : Vector.t CarrierA dynwin_o -> uvalue -> Prop :=
  fun hcol_out llvm_out =>
    exists b64,
      llvm_out ≡ UVALUE_Array [UVALUE_Double b64]
      /\ CType_impl
          b64 (HCOLImpl.Scalarize hcol_out).

Definition final_rel : Rel_mcfg_OT (Vector.t CarrierA dynwin_o) uvalue :=
  succ_mcfg (fun '(_,vh) '(_,(_,(_,vv))) => final_rel_val vh vv).

Definition fhcol_to_llvm_rel_val : list binary64 -> uvalue -> Prop :=
  fun fhcol_out llvm_out =>
      llvm_out ≡ UVALUE_Array (List.map UVALUE_Double fhcol_out).

Definition fhcol_to_llvm_rel : Rel_mcfg_OT (list binary64) uvalue :=
  succ_mcfg (fun '(_,vh) '(_,(_,(_,vv))) => fhcol_to_llvm_rel_val vh vv).


Require Import LibHyps.LibHyps.

Lemma compiler_correct_aux:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))),
  forall s hmem hdata σ,
    compile_w_main p data newState ≡ inr (s,pll) ->
    helix_initial_memory p data ≡ inr (hmem, hdata, σ) ->
    eutt fhcol_to_llvm_rel (semantics_FSHCOL' p data σ hmem) (semantics_llvm pll).
Proof.
  intros * COMP INIT.
  generalize COMP; intros COMP'.
  unfold compile_w_main,compile in COMP.
  cbn* in COMP.
  simp/g.
  epose proof @compile_FSHCOL_correct _ _ _ (* dynwin_F_σ dynwin_F_memory *) _ _ _ _ _ _ _ _ _ Heqs _ _ _ _.
  pose proof memory_invariant_after_init _ _ (conj INIT COMP') as INIT_MEM.
  match goal with
    |- context [semantics_llvm ?foo] => remember foo
  end.
  unfold semantics_llvm, semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm.
  simpl bind.
  rewrite interp3_bind.
  ret_bind_l_left ((hmem, tt)).
  eapply eutt_clo_bind.
  apply INIT_MEM.
  intros [? []] (? & ? & ? & []) INV.

  clear - Heqs1.

  unfold initIRGlobals,initIRGlobals_rev, init_with_data in Heqs1.

  rewrite interp3_bind.

  (* Need to get all the initialization stuff concrete I think? *)
  unfold initIRGlobals,initIRGlobals_rev, init_with_data in Heqs1.
  cbn in Heqs1.

Admitted.

(* Lemma compiler_correct_aux': *)
(*   forall (p:FSHCOLProgram) *)
(*     (data:list binary64) *)
(*     (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))), *)
(*   forall s (* hmem hdata σ *), *)
(*     (* helix_initial_memory p data ≡ inr (hmem, hdata, σ) -> *) *)
(*     compile_w_main p data newState ≡ inr (s,pll) -> *)
(*     eutt fhcol_to_llvm_rel (semantics_FSHCOL p data) (semantics_llvm pll). *)
(* Proof. *)
(* Admitted. *)


(*
  STATIC: what are the arguments to compile_w_main
1. What is the data
(to_float (to_list y) ++ to_float (to_list x) ++ to_float (to_list a))
 and how do I build it? --> Would be some kind of propositional relation that IZ will write matching a quantifier against (to_list y ++ to_list x ++ to_list a) ?
2. How to build the globals to build the program?

3. Is helix_initial_memory p data === dynwin_F_memory ???
4. Same for dynwin_F_σ??
   dyn_F_σ


1. I know that I compile safely operators: gen_IR is correct, i.e. some initial invariant between mems on FHCOL and LLVM entails the right bisimilarity
2. What I'm intersted is compile_w_main: that creates two functions, a main and the operator. The main does some initialization.
   Ilia proved: the main that is produced by compiled with main is a LLVM computation that produces an LLVM memory that satisfies the right invariant AGAINST WHAT FHCOL memory? The one produced by helix_initial_memory

3. Use the fact that by top_to_FHCOL, the semantics of the operator is also the same as the source one, STARTING FROM dynwin_F_memory


run op a memory satisfying some predicate = some result = source result

run op helix_initial_memory = some result = if I run my llvm code

TODO: assume the hypotheses to instantiate top_to_FHCOL with helix_initial_memory
heq_memory () RF_CHE (dynwin_R_memory a x) mem →
heq_evalContext () RF_NHE RF_CHE dynwin_R_σ σ ->


helix_initial_memory _ data = (mem,_,σ) ->
heq_memory () RF_CHE (dynwin_R_memory a x) mem →
heq_evalContext () RF_NHE RF_CHE dynwin_R_σ σ ->

INITIAL MEMORY: what is the link between dynwin_F_memory and dynwin_F_sigma that are inherited from the top, with the result of helix_initial_memory = (hmem,hdata,σ): hmem == dynwin_F_memory and σ == dynwin_F_sigma?

 *)

Lemma helix_inital_memory_denote_initFSHGlobals :
  forall p data        (* FSHCOL static data  *)
    hmem hdata σ  (* FSHCOL dynamic data *),
    helix_initial_memory p data ≡ inr (hmem,hdata,σ) -> (* shallow memory initialization *)
    interp_helix (denote_initFSHGlobals data (globals p)) FHCOLITree.memory_empty ≈ (Ret (Some (hmem,(hdata,σ))) : itree E_mcfg _).
Admitted.

Definition heq_list : list CarrierA → list binary64 → Prop
  := Forall2 (RHCOLtoFHCOL.heq_CType' RF_CHE ()).

(* IZ TODO: This could be stated more cleanly, and proven equivalent *)
(* DynWinInConstr, only expressed on HCOL input directly *)
Definition input_inConstr
  (a : Vector.t CarrierA 3)
  (x : Vector.t CarrierA dynwin_i)
  : Prop :=
  DynWinInConstr
    (MSigmaHCOL.MHCOL.ctvector_to_mem_block a)
    (MSigmaHCOL.MHCOL.ctvector_to_mem_block x).

(* IZ TODO: generalize beyond just DynWin? *)
Lemma initial_memory_from_data :
  forall (a : Vector.t CarrierA 3)
    (x : Vector.t CarrierA dynwin_i)
    (y : Vector.t CarrierA dynwin_o)
    data,
    heq_list (Vector.to_list y ++ Vector.to_list x ++ Vector.to_list a) data ->
    exists dynwin_F_memory data_garbage dynwin_F_σ,
      helix_initial_memory (dynwin_fhcolp DynWin_FHCOL_hard) data
      ≡ inr (dynwin_F_memory, data_garbage, dynwin_F_σ)
      /\ RHCOLtoFHCOL.heq_memory () RF_CHE (dynwin_R_memory a x) dynwin_F_memory
      /\ RHCOLtoFHCOL.heq_evalContext () RF_NHE RF_CHE dynwin_R_σ dynwin_F_σ.
Admitted.

Lemma interp_mem_interp_helix_ret : forall E σ op hmem fmem v,
    interp_Mem (denoteDSHOperator σ op) hmem ≈ Ret (fmem,v) ->
    interp_helix (E := E) (denoteDSHOperator σ op) hmem ≈ Ret (Some (fmem,v)).
Proof.
  intros * HI.
  unfold interp_helix.
  rewrite HI.
  rewrite interp_fail_ret.
  cbn.
  rewrite translate_ret.
  reflexivity.
Qed.


(* Notation mcfg_ctx fundefs := *)
(*   (λ (T : Type) (call : CallE T), *)
(*     match call in (CallE T0) return (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T0) with *)
(*     | LLVMEvents.Call dt0 fv args0 => *)
(*         dfv <- concretize_or_pick fv True;; *)
(*         match lookup_defn dfv fundefs with *)
(*         | Some f_den => f_den args0 *)
(*         | None => dargs <- map_monad (λ uv : uvalue, pickUnique uv) args0;; Functor.fmap dvalue_to_uvalue (trigger (ExternalCall dt0 fv dargs)) *)
(*         end *)
(*     end). *)

#[local] Definition mcfg_ctx fundefs :
  ∀ T : Type,
    CallE T
    → itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T :=

  (λ (T : Type) (call : CallE T),
    match call in (CallE T0) return (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T0) with
    | LLVMEvents.Call dt0 fv args0 =>
        dfv <- concretize_or_pick fv True;;
        match lookup_defn dfv fundefs with
        | Some f_den => f_den args0
        | None =>
            dargs <- map_monad (λ uv : uvalue, pickUnique uv) args0;;
            Functor.fmap dvalue_to_uvalue (trigger (ExternalCall dt0 fv dargs))
        end
    end).

Import RecursionFacts.
Lemma denote_mcfg_unfold_in : forall G τ addr args f,
    lookup_defn (DVALUE_Addr addr) G ≡ Some f ->
    denote_mcfg G τ (UVALUE_Addr addr) args ≈
      interp_mrec (mcfg_ctx G) (f args).
Proof.
  intros * LU.
  unfold denote_mcfg at 1.
  rewrite RecursionFacts.mrec_as_interp.
  simpl bind. rewrite interp_bind.
  cbn.
  rewrite interp_ret, bind_ret_l.
  rewrite LU.
  rewrite <- RecursionFacts.interp_mrec_as_interp.
  reflexivity.
Qed.


Lemma interp3_MemPush: forall g l m,
    ℑs3 (trigger MemPush) g l m ≈ Ret3 g l (push_fresh_frame m) ().
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  rewrite interp_memory_trigger.
  cbn.
  MCFGTactics.go.
  reflexivity.
Qed.


Lemma interp3_StackPush: forall g a sbot m s,
    ℑs3 (trigger (StackPush s)) g (a,sbot) m ≈
      Ret3 g (fold_right (λ '(x, dv), alist_add x dv) [] s, a :: sbot) m ().
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  reflexivity.
Qed.

Import TranslateFacts.

Global Instance Proper_interp_mrec_foo {D E}
  (ctx : D ~> itree (D +' E)) T :
  Proper (eutt eq ==> eutt eq) (interp_mrec ctx (T := T)).
Proof.
  repeat intro.
  eapply Proper_interp_mrec; auto.
  intros ??.
  reflexivity.
Qed.

Lemma interp_mrec_ret :
  ∀ (D E : Type → Type) (ctx : ∀ T : Type, D T → itree (D +' E) T) (U : Type) (u : U),
    interp_mrec ctx (Ret u) ≅ (Ret u).
Proof.
  intros.
  rewrite unfold_interp_mrec; reflexivity.
Qed.

Lemma interp3_call_void : forall G n τ f fdfn args g s m addr,
    prefix "llvm." f = false ->
    Maps.lookup (Name f) g ≡ Some (DVALUE_Addr addr) ->
    lookup_defn (DVALUE_Addr addr) G ≡ Some fdfn ->

    ℑs3 (interp_mrec (mcfg_ctx G)
           (Interp.translate instr_to_L0'
              ⟦(IVoid n, INSTR_Call (τ, EXP_Ident (ID_Global (Name f))) args) ⟧i)) g s m
      ≈
      '(m,(s,(g,vs))) <- ℑs3 (interp_mrec (mcfg_ctx G)
                               (Interp.translate instr_to_L0'
                                  (map_monad (λ '(t, op), Interp.translate exp_to_instr ⟦ op at t ⟧e) args))) g s m
    ;;

    '(m,(s,(g,v))) <- ℑs3 (interp_mrec (mcfg_ctx G) (fdfn vs)) g s m;;
    Ret (m,(s,(g,tt))).
Proof.
  intros * PRE LU LUD.
  Transparent denote_instr.
  cbn.
  rewrite translate_bind, interp_mrec_bind, interp3_bind.
  (* Expressions are pure, lifted by induction over map_monad *)
  apply eutt_clo_bind with
    (UU := fun '(m1,(s1,(g1,v))) m2 =>
             (m1,(s1,(g1,v))) ≡ m2 /\ m1 ≡ m /\ s1 ≡ s /\ g1 ≡ g).
  admit.
  intros (m1,(s1,(g1,v1))) (m2,(s2,(g2,v2))) (EQ & -> & -> & ->).
  symmetry in EQ; inv EQ.
  rewrite PRE.
  (* repeat break_and. *)
  rewrite bind_bind.
  rewrite translate_bind, interp_mrec_bind, interp3_bind.
  Transparent denote_exp.
  unfold denote_exp.
  cbn.
  rewrite bind_trigger.
  rewrite translate_vis.
  rewrite translate_vis.
  rewrite translate_vis.
  cbn.
  rewrite <- bind_trigger.
  rewrite interp_mrec_bind.
  rewrite interp_mrec_trigger.
  cbn.
  rewrite interp3_bind.
  match goal with
    |- context[ℑs3 ?e] =>
      let eqn := fresh in
      assert (eqn:e ≡ trigger (@GlobalRead raw_id dvalue (Name f))) by reflexivity;
      rewrite eqn; clear eqn
  end.
  rewrite interp3_GR; [| apply LU].
  rewrite bind_ret_l.
  rewrite 3translate_ret.

  rewrite interp_mrec_ret, interp3_ret, bind_ret_l.

  rewrite !translate_bind, interp_mrec_bind, interp3_bind.
  rewrite translate_trigger, interp_mrec_trigger.
  cbn.
  rewrite mrec_as_interp.
  cbn.
  rewrite bind_ret_l.
  rewrite LUD.
  cbn.
  rewrite <- RecursionFacts.interp_mrec_as_interp.

  apply eutt_eq_bind.
  intros (? & ? & ? & ?).
  rewrite translate_ret, interp_mrec_ret, interp3_ret.
  reflexivity.
  Opaque denote_instr.
  Opaque denote_exp.

Admitted.

From Paco Require Import paco.
Lemma eutt_ret_inv_strong {E X Y} (R : X -> Y -> Prop) (x : X) (t : itree E Y) :
  eutt R (Ret x) t ->
  exists y, t ≈ Ret y /\ R x y.
Proof.
  intros EQ; punfold EQ.
  red in EQ.
  dependent induction EQ.
  - exists r2; split; auto.
    rewrite itree_eta, <-x; reflexivity.
  - edestruct IHEQ as (y & EQ1 & HR); auto.
    exists y; split; auto.
    now rewrite itree_eta, <- x, tau_eutt.
Qed.

Lemma denote_mcfg_ID_Global :
  ∀ ctx (g : global_env) s (m : memoryV) id (τ : dtyp) (ptr : Addr.addr),
    alist_find id g ≡ Some (DVALUE_Addr ptr) ->

    ℑs3 (interp_mrec ctx
           (Interp.translate instr_to_L0'
              (Interp.translate exp_to_instr (denote_exp (Some τ) (EXP_Ident (ID_Global id)))))) g s m
      ≈
      Ret3 g s m (UVALUE_Addr ptr)
.
Proof.
  intros * LU.
  Transparent denote_exp.
  unfold denote_exp.
  cbn.
  rewrite 3translate_bind, interp_mrec_bind, interp3_bind.
  rewrite !translate_trigger.
  cbn.
  rewrite interp_mrec_trigger.
  cbn.

  match goal with
    |- context[ℑs3 ?e] =>
      let eqn := fresh in
      assert (eqn:e ≡ trigger (@GlobalRead raw_id dvalue id)) by reflexivity;
      rewrite eqn; clear eqn
  end.

  rewrite interp3_GR; [| apply LU].
  rewrite bind_ret_l.
  rewrite !translate_ret,interp_mrec_ret,interp3_ret.
  reflexivity.
Qed.

Import Interp.

From Vellvm Require Import Utils.PostConditions.

Import AlistNotations.
Definition global_ptr_exists fnname : Pred_mcfg :=
  fun '(mem_llvm, (ρ,g)) => exists mf, g @ fnname ≡ Some (DVALUE_Addr mf).

Definition global_ptr_existsT {T} fnname : Pred_mcfg_T T :=
  fun '(mem_llvm, (ρ,(g,_))) => exists mf, g @ fnname ≡ Some (DVALUE_Addr mf).

Lemma allocate_global_spec : forall (glob : global dtyp) g s m,
    non_void (g_typ glob) ->
    ℑs3 (allocate_global glob) g s m ⤳
      (global_ptr_existsT (g_ident glob)).
Proof.
  intros.
  unfold allocate_global.
  cbn.
  rewrite interp3_bind.
  edestruct interp3_alloca as (? & mf & ? & EQ); [eauto |].
  rewrite EQ; clear EQ.
  cbn; rewrite bind_ret_l.
  rewrite interp3_GW.
  apply eutt_Ret.
  cbn.
  exists mf.
  now rewrite alist_find_add_eq.
Qed.

Lemma interp3_map_monad {A B} g l m (xs : list A) (ts : A -> itree _ B) :
  ℑs3 (map_monad ts xs) g l m ≈
    map_monad (m := Monads.stateT _ (Monads.stateT _ (Monads.stateT _ (itree _))))
    (fun a => ℑs3 (ts a)) xs g l m.
Proof.
  intros; revert g l m; induction xs as [| a xs IH]; simpl; intros.
  - rewrite interp3_ret; reflexivity.
  - rewrite interp3_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp3_bind, IH.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp3_ret; reflexivity.
Qed.

Lemma exp_eq_dec: ∀ e1 e2 : exp dtyp, {e1 ≡ e2} + {e1 ≢ e2}.
Admitted.

Lemma allocate_globals_cons :
  forall g gs,
    allocate_globals (g :: gs) ≈ allocate_global g;; allocate_globals gs.
Proof.
  intros; cbn.
  rewrite !bind_bind.
  apply eutt_eq_bind; intros ?.
  apply eutt_eq_bind; intros ?.
  rewrite !bind_bind.
  apply eutt_eq_bind; intros ?.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma global_eq_dec: ∀ g1 g2 : global dtyp, {g1 ≡ g2} + {g1 ≢ g2}.
Proof.
  repeat decide equality.
  apply exp_eq_dec.
  apply dtyp_eq_dec.
Qed.

Lemma allocate_globals_spec : forall (gs:list (global dtyp)) glob (g : global_env) s m,
    In glob gs ->
    NoDup (List.map g_ident gs) ->
    Forall (fun x => non_void (g_typ x)) gs ->
    ℑs3 (allocate_globals gs) g s m ⤳ (global_ptr_existsT (g_ident glob)).
Proof.
  intros * IN NOD NV.
  unfold allocate_globals.
  unfold map_monad_; cbn; rewrite interp3_bind.
  apply has_post_bind_strong with (S := global_ptr_existsT (g_ident glob)).
  - cut (forall gs g s m
           (NV : Forall (fun x => non_void (g_typ x)) gs)
           (IN : (NoDup (List.map g_ident gs) /\ In glob gs) \/ (~ (In (g_ident glob) (List.map g_ident gs)) /\ global_ptr_exists (g_ident glob) (m,(s,g)))),
            ℑs3 (map_monad allocate_global gs) g s m ⤳ global_ptr_existsT (g_ident glob)).
    {
      intros H.
      apply H; auto.
    }
    clear.
    induction gs as [| g' gs IH].
    + intros.
      destruct IN as [[? []] | [NIN INV]].
      cbn; rewrite interp3_ret; apply eutt_Ret.
      apply INV.
    + intros.
      cbn.
      rewrite bind_bind.
      rewrite interp3_bind.
      edestruct interp3_alloca as (? & mf & ? & EQ); [| rewrite EQ].
      now inv NV.
      cbn.
      rewrite bind_ret_l.
      rewrite interp3_bind.
      rewrite interp3_GW.
      rewrite bind_ret_l.
      rewrite interp3_bind.
      eapply has_post_bind_strong.
      apply IH.
      * now inv NV.
      * destruct IN as [IN | [NIN HI]].
        {
          destruct (global_eq_dec glob g').
          { right.
            destruct IN as [NOD IN].
            subst g'.
            split.
            now inv NOD.
            cbn.
            setoid_rewrite alist_find_add_eq.
            eauto.
          }
          left.
          destruct IN as [NOD []]; [subst; exfalso; now apply n| split;auto].
          now inv NOD.
        }
        right.
        apply not_in_cons in NIN as [NEQ NIN]; split; [apply NIN |].
        cbn.
        destruct HI.
        exists x0.
        rewrite alist_find_neq; auto.

      * intros (?,(?,(?,?))) HI.
        rewrite interp3_ret. apply eutt_Ret.
        apply HI.
  - intros (?,(?,(?,?))) HI.
    rewrite interp3_ret; apply eutt_Ret.
    apply HI.
Qed.

(* We would want something stronger like the following.
   But unfortunately it cannot be derived from the weaker
   spec directly by induction as the weaker spec does not
   specify that we preserve the other [global_ptr_existsT]
   predicates.
 *)
Lemma allocate_globals_spec' :
  forall (gs:list (global dtyp)) (g : global_env) s m,
    NoDup (List.map g_ident gs) ->
    Forall (fun x => non_void (g_typ x)) gs ->
    ℑs3 (allocate_globals gs) g s m ⤳
      (fun s => forall glob, In glob gs -> global_ptr_existsT (g_ident glob) s).
Proof.
  induction gs as [| glob gs IH]; intros * NOD NV.
  - cbn; rewrite bind_ret_l, interp3_ret.
    apply eutt_Ret.
    intros ? [].
  - rewrite allocate_globals_cons.
    cbn. rewrite interp3_bind.
    eapply has_post_bind_strong.
    apply allocate_global_spec. now inv NV.
    intros ? IH'; repeat break_and.
Abort.

#[local] Definition GFUNC dyn_addr b0 l4 main_addr :=
  [(DVALUE_Addr dyn_addr,
        ⟦ TFunctor_definition typ dtyp (typ_to_dtyp [])
            {|
              df_prototype :=
                {|
                  dc_name := Name "dyn_win";
                  dc_type :=
                    TYPE_Function TYPE_Void
                      [TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double);
                      TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double)];
                  dc_param_attrs := ([], [PARAMATTR_Readonly :: ArrayPtrParamAttrs; ArrayPtrParamAttrs]);
                  dc_linkage := None;
                  dc_visibility := None;
                  dc_dll_storage := None;
                  dc_cconv := None;
                  dc_attrs := [];
                  dc_section := None;
                  dc_align := None;
                  dc_gc := None
                |};
              df_args := [Name "X"; Name "Y"];
              df_instrs :=
                cfg_of_definition typ
                  {|
                    df_prototype :=
                      {|
                        dc_name := Name "dyn_win";
                        dc_type :=
                          TYPE_Function TYPE_Void
                            [TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double);
                            TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double)];
                        dc_param_attrs :=
                          ([], [PARAMATTR_Readonly :: ArrayPtrParamAttrs; ArrayPtrParamAttrs]);
                        dc_linkage := None;
                        dc_visibility := None;
                        dc_dll_storage := None;
                        dc_cconv := None;
                        dc_attrs := [];
                        dc_section := None;
                        dc_align := None;
                        dc_gc := None
                      |};
                    df_args := [Name "X"; Name "Y"];
                    df_instrs := (b0, l4)
                  |}
            |} ⟧f);
       (DVALUE_Addr main_addr,
       ⟦ TFunctor_definition typ dtyp (typ_to_dtyp [])
           {|
             df_prototype :=
               {|
                 dc_name := Name "main";
                 dc_type := TYPE_Function (TYPE_Array (Npos 1) TYPE_Double) [];
                 dc_param_attrs := ([], []);
                 dc_linkage := None;
                 dc_visibility := None;
                 dc_dll_storage := None;
                 dc_cconv := None;
                 dc_attrs := [];
                 dc_section := None;
                 dc_align := None;
                 dc_gc := None
               |};
             df_args := [];
             df_instrs :=
               cfg_of_definition typ
                 {|
                   df_prototype :=
                     {|
                       dc_name := Name "main";
                       dc_type := TYPE_Function (TYPE_Array (Npos 1) TYPE_Double) [];
                       dc_param_attrs := ([], []);
                       dc_linkage := None;
                       dc_visibility := None;
                       dc_dll_storage := None;
                       dc_cconv := None;
                       dc_attrs := [];
                       dc_section := None;
                       dc_align := None;
                       dc_gc := None
                     |};
                   df_args := [];
                   df_instrs :=
                     ({|
                        blk_id := Name "main_block";
                        blk_phis := [];
                        blk_code :=
                          [(IVoid 0%Z,
                           INSTR_Call (TYPE_Void, EXP_Ident (ID_Global (Name "dyn_win")))
                             [(TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double),
                              EXP_Ident (ID_Global (Anon 0%Z)));
                             (TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double),
                             EXP_Ident (ID_Global (Anon 1%Z)))]);
                          (IId (Name "z"),
                          INSTR_Load false (TYPE_Array (Npos 1) TYPE_Double)
                            (TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double),
                            EXP_Ident (ID_Global (Anon 1%Z))) None)];
                        blk_term :=
                          TERM_Ret (TYPE_Array (Npos 1) TYPE_Double, EXP_Ident (ID_Local (Name "z")));
                        blk_comments := None
                      |}, [])
                 |}
           |} ⟧f)].

#[local] Definition Γi :=
  {|
    block_count := 1;
    local_count := 0;
    void_count := 0;
    Γ :=
      [(ID_Global (Name "a"), TYPE_Pointer (TYPE_Array (Npos 3) TYPE_Double));
       (ID_Local (Name "Y"), TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double));
       (ID_Local (Name "X"), TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double));
       (ID_Global (Anon 1%Z), TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double));
       (ID_Global (Anon 0%Z), TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double))]
  |}.

#[local] Definition MCFG l6 l3 l5 b0 l4 :=
  (TLE_Global {|
                               g_ident := Name "a";
                               g_typ := TYPE_Array (Npos 3) TYPE_Double;
                               g_constant := true;
                               g_exp := Some (EXP_Array l6);
                               g_linkage := Some LINKAGE_Internal;
                               g_visibility := None;
                               g_dll_storage := None;
                               g_thread_local := None;
                               g_unnamed_addr := true;
                               g_addrspace := None;
                               g_externally_initialized := false;
                               g_section := None;
                               g_align := Some 16%Z
                             |}
                           :: TLE_Global
                                {|
                                  g_ident := Anon 1%Z;
                                  g_typ := TYPE_Array (Npos 1) TYPE_Double;
                                  g_constant := true;
                                  g_exp := Some (EXP_Array l3);
                                  g_linkage := None;
                                  g_visibility := None;
                                  g_dll_storage := None;
                                  g_thread_local := None;
                                  g_unnamed_addr := false;
                                  g_addrspace := None;
                                  g_externally_initialized := false;
                                  g_section := None;
                                  g_align := None
                                |}
                              :: TLE_Global
                                   {|
                                     g_ident := Anon 0%Z;
                                     g_typ := TYPE_Array (Npos 5) TYPE_Double;
                                     g_constant := true;
                                     g_exp := Some (EXP_Array l5);
                                     g_linkage := None;
                                     g_visibility := None;
                                     g_dll_storage := None;
                                     g_thread_local := None;
                                     g_unnamed_addr := false;
                                     g_addrspace := None;
                                     g_externally_initialized := false;
                                     g_section := None;
                                     g_align := None
                                   |}
                                 :: TLE_Comment "Prototypes for intrinsics we use"
                                    :: TLE_Declaration IntrinsicsDefinitions.fabs_32_decl
                                       :: TLE_Declaration IntrinsicsDefinitions.fabs_64_decl
                                          :: TLE_Declaration IntrinsicsDefinitions.maxnum_32_decl
                                             :: TLE_Declaration IntrinsicsDefinitions.maxnum_64_decl
                                                :: TLE_Declaration IntrinsicsDefinitions.minimum_32_decl
                                                   :: TLE_Declaration IntrinsicsDefinitions.minimum_64_decl
                                                      :: TLE_Declaration
                                                           IntrinsicsDefinitions.memcpy_8_decl
                                                         :: TLE_Comment "Top-level operator definition"
                                                            :: TLE_Definition
                                                                 {|
                                                                   df_prototype :=
                                                                     {|
                                                                       dc_name := Name "dyn_win";
                                                                       dc_type :=
                                                                         TYPE_Function TYPE_Void
                                                                           [TYPE_Pointer
                                                                              (TYPE_Array
                                                                              (Npos 5) TYPE_Double);
                                                                           TYPE_Pointer
                                                                             (TYPE_Array
                                                                              (Npos 1) TYPE_Double)];
                                                                       dc_param_attrs :=
                                                                         ([],
                                                                         [PARAMATTR_Readonly
                                                                          :: ArrayPtrParamAttrs;
                                                                         ArrayPtrParamAttrs]);
                                                                       dc_linkage := None;
                                                                       dc_visibility := None;
                                                                       dc_dll_storage := None;
                                                                       dc_cconv := None;
                                                                       dc_attrs := [];
                                                                       dc_section := None;
                                                                       dc_align := None;
                                                                       dc_gc := None
                                                                     |};
                                                                   df_args := [Name "X"; Name "Y"];
                                                                   df_instrs := (b0, l4)
                                                                 |}
                                                               :: genMain "dyn_win"
                                                                    (Anon 0%Z)
                                                                    (TYPE_Pointer
                                                                       (TYPE_Array (Npos 5) TYPE_Double))
                                                                    (Anon 1%Z)
                                                                    (TYPE_Array (Npos 1) TYPE_Double)
                                                                    (TYPE_Pointer
                                                                       (TYPE_Array (Npos 1) TYPE_Double))).

Definition MAIN :=
  {|
    df_prototype :=
      {|
        dc_name := Name "main";
        dc_type := TYPE_Function (TYPE_Array (Npos 1) TYPE_Double) [];
        dc_param_attrs := ([], []);
        dc_linkage := None;
        dc_visibility := None;
        dc_dll_storage := None;
        dc_cconv := None;
        dc_attrs := [];
        dc_section := None;
        dc_align := None;
        dc_gc := None
      |};
    df_args := [];
    df_instrs :=
      cfg_of_definition typ
                        {|
                          df_prototype :=
                            {|
                              dc_name := Name "main";
                              dc_type := TYPE_Function (TYPE_Array (Npos 1) TYPE_Double) [];
                              dc_param_attrs := ([], []);
                              dc_linkage := None;
                              dc_visibility := None;
                              dc_dll_storage := None;
                              dc_cconv := None;
                              dc_attrs := [];
                              dc_section := None;
                              dc_align := None;
                              dc_gc := None
                            |};
                          df_args := [];
                          df_instrs :=
                            ({|
                                blk_id := Name "main_block";
                                blk_phis := [];
                                blk_code :=
                                  [(IVoid 0%Z,
                                     INSTR_Call (TYPE_Void, EXP_Ident (ID_Global (Name "dyn_win")))
                                       [(TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double),
                                          EXP_Ident (ID_Global (Anon 0%Z)));
                                        (TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double),
                                          EXP_Ident (ID_Global (Anon 1%Z)))]);
                                   (IId (Name "z"),
                                     INSTR_Load false (TYPE_Array (Npos 1) TYPE_Double)
                                       (TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double),
                                         EXP_Ident (ID_Global (Anon 1%Z))) None)];
                                blk_term :=
                                  TERM_Ret (TYPE_Array (Npos 1) TYPE_Double, EXP_Ident (ID_Local (Name "z")));
                                blk_comments := None
                              |}, [])
                        |}
  |}.

Definition DYNWIN b0 l4 :=
{|
                        df_prototype :=
                          {|
                            dc_name := Name "dyn_win";
                            dc_type :=
                              TYPE_Function TYPE_Void
                                [TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double);
                                TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double)];
                            dc_param_attrs :=
                              ([], [PARAMATTR_Readonly :: ArrayPtrParamAttrs; ArrayPtrParamAttrs]);
                            dc_linkage := None;
                            dc_visibility := None;
                            dc_dll_storage := None;
                            dc_cconv := None;
                            dc_attrs := [];
                            dc_section := None;
                            dc_align := None;
                            dc_gc := None
                          |};
                        df_args := [Name "X"; Name "Y"];
                        df_instrs :=
                          cfg_of_definition typ
                            {|
                              df_prototype :=
                                {|
                                  dc_name := Name "dyn_win";
                                  dc_type :=
                                    TYPE_Function TYPE_Void
                                      [TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double);
                                      TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double)];
                                  dc_param_attrs :=
                                    ([], [PARAMATTR_Readonly :: ArrayPtrParamAttrs; ArrayPtrParamAttrs]);
                                  dc_linkage := None;
                                  dc_visibility := None;
                                  dc_dll_storage := None;
                                  dc_cconv := None;
                                  dc_attrs := [];
                                  dc_section := None;
                                  dc_align := None;
                                  dc_gc := None
                                |};
                              df_args := [Name "X"; Name "Y"];
                              df_instrs := (b0, l4)
                            |}
|}.

Definition MAINCFG := [{|
      blk_id := Name "main_block";
      blk_phis := [];
      blk_code :=
        [(IVoid 0%Z,
           INSTR_Call (typ_to_dtyp [] TYPE_Void, EXP_Ident (ID_Global (Name "dyn_win")))
             [(typ_to_dtyp [] (TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double)), EXP_Ident (ID_Global (Anon 0%Z))); (typ_to_dtyp [] (TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double)), EXP_Ident (ID_Global (Anon 1%Z)))]);
         (IId (Name "z"), INSTR_Load false (typ_to_dtyp [] (TYPE_Array (Npos 1) TYPE_Double)) (typ_to_dtyp [] (TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double)), EXP_Ident (ID_Global (Anon 1%Z))) None)];
      blk_term := TERM_Ret (typ_to_dtyp [] (TYPE_Array (Npos 1) TYPE_Double), EXP_Ident (ID_Local (Name "z")));
      blk_comments := None
    |}].

Opaque MCFG MAIN MAINCFG DYNWIN GFUNC Γi mcfg_ctx.

Ltac hide_MCFG l6 l3 l5 b0 l4 :=
  match goal with
  | h : context[mcfg_of_tle ?x] |- _ =>
      progress change x with (MCFG l6 l3 l5 b0 l4) in h
  | |- context[semantics_llvm ?x] => progress change x with (MCFG l6 l3 l5 b0 l4)
  end.

Ltac hide_Γi :=
  match goal with
  | h : context [genIR _ _ ?x] |- _ => progress change x with Γi in h
  end.

Ltac hide_GFUNC dyn_addr b0 l4 main_addr :=
  match goal with
    |- context [denote_mcfg ?x] =>
      progress change x with (GFUNC dyn_addr b0 l4 main_addr)
  end.

Ltac hide_MAIN :=
  match goal with
    |- context [TFunctor_definition _ _ _ ?x] =>
      progress change x with MAIN
  end.

Ltac hide_DYNWIN b0 l4 :=
  match goal with
    |- context [TFunctor_definition _ _ _ ?x] =>
      progress change x with (DYNWIN b0 l4)
  end.

Ltac hide_mcfg_ctx dyn_addr b0 l4 main_addr :=
  match goal with
    |- context[interp_mrec ?x ] =>
      replace x with (mcfg_ctx (GFUNC dyn_addr b0 l4 main_addr)) by reflexivity
  end.

Ltac hide_MAINCFG :=
  match goal with
    |- context [[mk_block (Name "main_block") ?phi ?c ?t ?comm]] =>
      change [mk_block (Name "main_block") ?phi ?c ?t ?comm] with MAINCFG
  end.

Ltac HIDE l6 l3 l5 b0 l4 dyn_addr main_addr
  := repeat (hide_MCFG l6 l3 l5 b0 l4 || hide_GFUNC dyn_addr b0 l4 main_addr || hide_Γi || hide_MAIN || hide_DYNWIN b0 l4 || hide_mcfg_ctx dyn_addr b0 l4 main_addr || hide_MAINCFG).

Import ProofMode.

Lemma heq_list_nil : heq_list [] [].
Proof.
  constructor.
Qed.

Lemma heq_list_app : forall l1 l2 l,
    heq_list (l1 ++ l2) l ->
    exists l1' l2', l ≡ l1' ++ l2' /\ heq_list l1 l1' /\ heq_list l2 l2'.
Proof.
  induction l1; intros.
  - exists [], l; repeat split. apply heq_list_nil. apply H.
  - destruct l as [| a' l]; inv H.
    edestruct IHl1 as (l1' & l2' & ? & ? & ?); eauto.
    exists (a' :: l1'), l2'; repeat split; subst; eauto.
    constructor; auto.
Qed.

Set Printing Compact Contexts.

Lemma top_to_LLVM :
  forall (a : Vector.t CarrierA 3) (* parameter *)
    (x : Vector.t CarrierA dynwin_i) (* input *)
    (y : Vector.t CarrierA dynwin_o), (* output *)

      (* Evaluation of the source program.
         The program is fixed and hard-coded: the result is not generic,
         we provide a "framework". *)
      dynwin_orig a x = y →

      (* We cannot hide away the [R] level as we axiomatize the real to float
         approximation performed *)
      ∀
        (data : list binary64)
        (PRE : heq_list
                 (Vector.to_list y ++ Vector.to_list x ++ Vector.to_list a)
                 data),

        (* the input data must be within bounds for numerical stability *)
        input_inConstr a x ->

        forall s pll
          (COMP : compile_w_main (dynwin_fhcolp DynWin_FHCOL_hard) data newState ≡ inr (s,pll)),
        exists g l m r, semantics_llvm pll ≈ Ret (m,(l,(g, r))) /\
                     final_rel_val y r.
Proof.
  intros/g.

  (* Specification of the initial memory on the helix side *)
  edestruct initial_memory_from_data
    as (dynwin_F_memory & data_garbage & dynwin_F_σ & HINIT & RFM & RFΣ);
    try eassumption/g.

  (* The current statement gives us essentially FHCOL-level inputs and outputs,
     and relate them to the source *)
  edestruct top_to_FHCOL
    with (dynwin_F_σ := dynwin_F_σ) (dynwin_F_memory := dynwin_F_memory)
    as (r_omemory & y_rmem' & EVR & LUR & TRR & f_omemory & y_fmem & EVF & LUF & TRF);
    eauto/g.

  instantiate (1:=DynWin_FHCOL_hard).
  rewrite DynWin_FHCOL_hard_OK.

  1,2,3: now repeat constructor.

  (* TODO : evaluation in terms of equiv and not eq, contrary to what' assumed in EvalDenoteEquiv.
     Is it an easy fix to Denote_Eval_Equiv?
   *)
  match type of EVF with
  | ?x = ?y => clear EVF; assert (EVF:x ≡ y) by admit
  end.
  (* We know that we can see the evaluation of the FHCOL operator under an itree-lense  *)
  pose proof (Denote_Eval_Equiv _ _ _ _ _ EVF) as EQ.

  (* Breaking down the compilation process *)
  Opaque genIR.
  generalize COMP; intros COMP'.
  unfold compile_w_main,compile in COMP.
  simpl in COMP.
  simp.

  unfold initXYplaceholders in Heqs0; cbn in Heqs0.
  break_let; cbn in Heqs0.
  break_let; cbn in Heqs0.
  inv_sum/g.
  cbn in Heqs1.
  unfold initIRGlobals in Heqs1; cbn in Heqs1.
  break_let; cbn in Heqs1.
  cbv in Heqs1.
  inv_sum/g.

  unfold LLVMGen in Heqs2.
  Opaque genIR.
  cbn in Heqs2.
  break_match; [inv_sum |]/g.
  break_and; cbn in Heqs2/g.
  destruct s0/g.
  break_match; [inv_sum |]/g.
  break_and; cbn in Heqs2/g.
  inv_sum/g.
  cbn.

  (* Processing the construction of the LLVM global environment:
     We know that the two functions of interest have been allocated,
     and that the memories on each side satisfy the major relational
     invariant.
   *)
  pose proof memory_invariant_after_init _ _ (conj HINIT COMP') as INIT_MEM; clear COMP' HINIT.
  destruct u.

  (* The context gets... quite big. We try to prevent it as much as possible early on *)

  rename l1 into bks1, l4 into bks2.
  rename b0 into bk.
  rename l3 into exps1, l5 into exps2, l6 into exps3.
  rename s into s1, i into s2, i1 into s3.

  Tactic Notation "tmp" ident(exps3)
    ident(exps1)
    ident(exps2)
    ident(bk)
    ident(bks2)
    ident(dyn_addr)
    ident(main_addr)
    := HIDE exps3 exps1 exps2 bk bks2 dyn_addr main_addr.
  Ltac hide := tmp exps3 exps1 exps2 bk bks2 dyn_addr main_addr.
  hide.

  apply heq_list_app in PRE as (Y & tmp & -> & EQY & EQtmp).
  apply heq_list_app in EQtmp as (X & A & -> & EQX & EQA).


  (* match type of INIT_MEM with *)
  (* | context[mcfg_of_tle ?x] => remember x as tmp; cbn in Heqtmp; subst tmp *)
  (* end. *)

  (* match goal with *)
  (*   |- context [semantics_llvm ?x] => remember x as G eqn:VG; apply boxh_cfg in VG *)
  (* end. *)
  onAllHyps move_up_types.

  edestruct @eutt_ret_inv_strong as (RESLLVM & EQLLVMINIT & INVINIT); [apply INIT_MEM |].
  destruct RESLLVM as (memI & [ρI sI] & gI & []).
  inv INVINIT.
  destruct decl_inv as [(main_addr & EQmain) (dyn_addr & EQdyn)].
  cbn in EQdyn.

  (* We are getting closer to business: instantiating the lemma
     stating the correctness of the compilation of operators *)
  unshelve epose proof @compile_FSHCOL_correct _ _ _ dynwin_F_σ dynwin_F_memory _ _ (blk_id bk) _ gI ρI memI Heqs0 _ _ _ _ as RES; clear Heqs0; cycle -1.

  - (* Assuming we can discharge all the preconditions,
       we prove here that it is sufficient for establishing
       our toplevel correctness statement.
     *)
    eapply interp_mem_interp_helix_ret in EQ.
    rewrite EQ in RES.
    clear EQ.
    edestruct @eutt_ret_inv_strong as (RESLLVM2 & EQLLVM2 & INV2); [apply RES |].
    destruct RESLLVM2 as (mem2 & ρ2 & g2 & v2).
    onAllHyps move_up_types.


    (* We need to reason about [semantics_llvm].
       Hopefully we now have all the pieces into our
       context, we try to go through it via some kind of
       symbolic execution to figure out what statement
       we need precisely.
     *)
    assert (forall x, semantics_llvm (MCFG exps3 exps1 exps2 bk bks2) ≈ x).
    { intros ?.

      unfold semantics_llvm, semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm.


      simpl bind.
      rewrite interp3_bind.
      (* We know that building the global environment is pure,
         and satisfy a certain spec.
       *)
      rewrite EQLLVMINIT.
      rewrite bind_ret_l.

      rewrite interp3_bind.
      focus_single_step_l.

      (* We build the open denotations of the functions, i.e.
         of "main" and "dyn_win".
        [memory_invariant_after_init] has guaranteed us that
        they are allocated in memory (via [EQdyn] and [EQmain])
       *)
      (* Hmm, amusing hack, [unfold] respects Opaque but not [unfold at i] *)
      unfold MCFG at 1 2; cbn.
      hide.

      rewrite !interp3_bind.
      rewrite !bind_bind.
      rewrite interp3_GR; [| apply EQdyn].

      rewrite bind_ret_l.
      rewrite interp3_ret.
      rewrite bind_ret_l.
      rewrite !interp3_bind.
      rewrite !bind_bind.
      rewrite interp3_GR; [| apply EQmain].
      repeat (rewrite bind_ret_l || rewrite interp3_ret).
      subst.
      cbn.
      rewrite interp3_bind.
      hide.

      (* We now specifically get the pointer to the main as the entry point *)
      rewrite interp3_GR; [| apply EQmain].
      repeat (rewrite bind_ret_l || rewrite interp3_ret).
      cbn/g.

      (* We are done with the initialization of the runtime, we can
         now begin the evaluation of the program per se. *)

      (* We hence first do a one step unfolding of the mutually
         recursive fixpoint in order to jump into the body of the main.
       *)
      rewrite denote_mcfg_unfold_in; cycle -1.

      {
        unfold GFUNC at 1.
        unfold lookup_defn.
        rewrite assoc_tl.
        apply assoc_hd.
        (* Need to keep track of the fact that [main_addr] and [dyn_addr]
           are distinct. Might be hidden somewhere in the context.
         *)
        admit. (* addresses are distincts *)
      }

      cbn.
      rewrite bind_ret_l.
      rewrite interp_mrec_bind.
      rewrite interp_mrec_trigger.
      cbn.
      rewrite interp3_bind.

      (* Function call, we first create a new memory frame *)
      rewrite interp3_MemPush.
      rewrite bind_ret_l.
      rewrite interp_mrec_bind.
      rewrite interp_mrec_trigger.
      cbn.
      rewrite interp3_bind.
      rewrite interp3_StackPush.

      rewrite bind_ret_l.
      rewrite interp_mrec_bind.
      rewrite interp3_bind.
      rewrite translate_bind.
      rewrite interp_mrec_bind.
      rewrite interp3_bind.
      rewrite bind_bind.
      cbn.

      hide.
      onAllHyps move_up_types.

      (* TODO FIX surface syntax *)
      (* TODO : should really wrap the either monad when jumping from blocks into a named abstraction to lighten goals
         TODO : can we somehow avoid the continuations being systematically
         let (m',p) := r in
         let (l',p0) := p in
         let (g',_)  := p0 in ...
       *)
      Lemma typ_to_dtyp_void s : typ_to_dtyp s TYPE_Void ≡ DTYPE_Void.
      Proof.
        intros; rewrite typ_to_dtyp_equation; reflexivity.
      Qed.

      Notation "'call' x args" := ((IVoid _, INSTR_Call x args)) (at level 30, only printing).

      (* We are now evaluating the main.
         We hence first need to need to jump into the right block
       *)
      rewrite denote_ocfg_unfold_in; cycle -1.
      unfold MAINCFG at 1; rewrite find_block_eq; reflexivity.

      rewrite typ_to_dtyp_void.
      rewrite denote_block_unfold.
      (* No phi node in this block *)
      rewrite denote_no_phis.
      rewrite bind_ret_l.
      rewrite bind_bind.

      (* We hence evaluate the code: it starts with a function call to "dyn_win"! *)

      rewrite denote_code_cons.
      rewrite bind_bind,translate_bind.
      rewrite interp_mrec_bind, interp3_bind.
      rewrite bind_bind.
      cbn.
      focus_single_step_l.

      hide.
      rewrite interp3_call_void; cycle 1.
      reflexivity.
      eauto.
      {
        unfold GFUNC at 1.
        unfold lookup_defn.
        apply assoc_hd.
      }
      hide.
      cbn.
      rewrite bind_bind.
      hide.
      rewrite translate_bind, interp_mrec_bind,interp3_bind, bind_bind.
      focus_single_step_l.

      (* This function call has arguments: we need to evaluate those.
         These arguments are globals that have been allocated during
         the initialization phase, but I'm afraid we lost this fact
         at this moment.
         In particular right now, we need to lookup in the global
         environment the address to an array stored at [Anon 0].

         Do I need to reinforce [memory_invariant_after_init] or is
         what I need a consequence of [genIR_post]?
       *)

      assert (exists add0, gI @ Anon 0%Z ≡ Some (DVALUE_Addr add0)) as [add0 ?] by admit.
      rewrite denote_mcfg_ID_Global; cycle 1.
      eassumption.

      rewrite bind_ret_l.
      subst.
      cbn.
      focus_single_step_l.

      match goal with
        |- context [interp_mrec ?x] => remember x as ctx
      end.
      rewrite !translate_bind, !interp_mrec_bind,!interp3_bind, !bind_bind.
      assert (exists add1, gI @ Anon 1%Z ≡ Some (DVALUE_Addr add1)) as [add1 ?] by admit.
      rewrite denote_mcfg_ID_Global; cycle 1.
      eassumption.
      rewrite bind_ret_l.
      rewrite bind_ret_l.
      rewrite translate_ret.
      rewrite interp_mrec_ret, interp3_ret, bind_ret_l.
      rewrite translate_ret, interp_mrec_ret, interp3_ret, bind_ret_l.

      subst.
      rewrite !bind_bind.
      cbn.
      focus_single_step_l.
      unfold DYNWIN at 1; cbn.

      rewrite bind_ret_l.

      cbn.
      rewrite interp_mrec_bind.
      rewrite interp_mrec_trigger.
      cbn.
      rewrite interp3_bind.

      (* Function call, we first create a new memory frame *)
      rewrite interp3_MemPush.
      rewrite bind_ret_l.
      rewrite interp_mrec_bind.
      rewrite interp_mrec_trigger.
      cbn.
      rewrite interp3_bind.
      rewrite interp3_StackPush.

      rewrite bind_ret_l.

      rewrite !translate_bind,!interp_mrec_bind,!interp3_bind.
      rewrite !bind_bind.
      subst; focus_single_step_l.

      Notation "'foo' t" := (ℑs3 (interp_mrec (mcfg_ctx (GFUNC _ _ _ _)) t)) (at level 0, only printing).


      unfold DYNWIN at 2 3; cbn.

      unfold init_of_definition.
      cbn.

      unfold DYNWIN at 1.
      cbn[df_instrs blks cfg_of_definition fst snd].

      match type of Heqs1 with
      | body_non_empty_cast ?x _ ≡ inr (_, (?bk, ?bks)) => assert (EQbks: bk :: bks2 ≡ x)
      end.
      {
        clear - Heqs1.
        destruct bks1; cbn in *; inv Heqs1; reflexivity.
      }


      (* Shouldn't we be facing EQLLVM2 right now? *)
      (* rewrite denote_ocfg_unfold_in; cycle -1. *)
      (* apply find_block_eq; reflexivity. *)
      (* cbn. *)
      (* rewrite denote_block_unfold. *)

      (* Who's b0? *)
      (* Ah ok: we have extended the operator's cfg with a return block to terminate, and our [genIR_post]
         tells us we are about to jump to this ret block, so we need a lemma to piece this together *)

      (*

  assert (forall x g s m, ℑs3 (build_global_environment (convert_types (mcfg_of_tle [TLE_Global {|
                 g_ident := Anon 0%Z;
                 g_typ := TYPE_Array (Npos 5) TYPE_Double;
                 g_constant := true;
                 g_exp := Some (EXP_Array l5);
                 g_linkage := None;
                 g_visibility := None;
                 g_dll_storage := None;
                 g_thread_local := None;
                 g_unnamed_addr := false;
                 g_addrspace := None;
                 g_externally_initialized := false;
                 g_section := None;
                 g_align := None
               |}
                 ]))) g s m ⤳ x).
  {
    clear.
    intros.
    unfold build_global_environment.
    simpl bind. rewrite interp3_bind.
    match goal with
      |- has_post (ITree.bind _ ?x) _ => remember x
    end.
    cbn; rewrite bind_ret_l, interp3_ret, bind_ret_l.
    subst.
    rewrite interp3_bind.
    eapply has_post_bind_strong.
    apply allocate_globals_spec.
    left; reflexivity.
    cbn; constructor; [intros [] | constructor].
    constructor; [cbn; rewrite typ_to_dtyp_D_array; intros abs; inv abs
                 | apply Forall_nil].
    intros ? IH; repeat break_and.
    cbn in IH.
    destruct IH as (? & EQ).
    cbn.
    rewrite ?bind_bind, ?bind_ret_l.
    rewrite translate_bind, translate_trigger,interp3_bind.
    rewrite exp_to_L0_Global.
    rewrite subevent_subevent.
    rewrite interp3_GR; [| apply EQ].
    rewrite bind_ret_l.
    rewrite ?bind_bind, ?bind_ret_l.
    unfold denote_exp.
    cbn.
    rewrite translate_bind, translate_trigger,interp3_bind.

    cbn.
    rewrite interp3_GR.

    eapply has_post_bind_strong.


  Record post_init_invariant_enriched
    (fnname:string) (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
      state_inv: state_invariant σ s memH configV;
      decl_inv:  declarations_invariant fnname configV;
      globs_inv : globals_invariant
    }.


(post_init_invariant_mcfg_enriched p.(name) σ s)

Lemma memory_invariant_after_init_enriched
      (p: FSHCOLProgram)
      (data: list binary64) :
  forall hmem σ s hdata pll,
    helix_initial_memory p data ≡ inr (hmem,hdata,σ) /\
    compile_w_main p data newState ≡ inr (s,pll) ->
    eutt
      (post_init_invariant_mcfg p.(name) σ s)
      (Ret (hmem, ()))
      (interp_mcfg3 (build_global_environment (convert_types (mcfg_of_tle pll)))
                    [] ([],[]) empty_memory_stack).

*)

      (* Need a stronger invariant than [declarations_invariant] given by [memory_invariant_after_init] in order to get the addresses of the other globals *)


(*
        rewrite denote_exp_ID.
        rewrite denote_code_singleton.

        cbn.
        cbn.
        rewrite interp3_bind.


      rewrite bind_trigger.
      rewrite interp3_vis.

      Unset Printing Notations.
ℑs3
      rewrite interp3

    }


    do 4 eexists.
    split.

    destruct VG. as [EQ].
    subst.
    cbn.
    ret_bind_l_left ((hmem, tt)).
    eapply eutt_clo_bind.
    apply INIT_MEM.
    intros [? []] (? & ? & ? & []) INV.



    cbn in INV2.
    destruct INV2 as (INV21 & INV22 & INV23).
    cbn in INV21,INV22,INV23.


    exists g2, (ρ2, sI), mem2.

  unfold semantics_llvm, semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm.
  simpl bind.
  rewrite interp3_bind.
  ret_bind_l_left ((hmem, tt)).
  eapply eutt_clo_bind.
  apply INIT_MEM.
  intros [? []] (? & ? & ? & []) INV.

  clear - Heqs1.

  unfold initIRGlobals,initIRGlobals_rev, init_with_data in Heqs1.

  rewrite interp3_bind.

  (* Need to get all the initialization stuff concrete I think? *)
  unfold initIRGlobals,initIRGlobals_rev, init_with_data in Heqs1.
  cbn in Heqs1.




  eapply compiler_correct_aux in COMP; try eassumption.
  unfold semantics_FSHCOL', denote_FSHCOL' in COMP.
  Opaque denoteDSHOperator.
  cbn in COMP.
  rewrite interp_helix_bind in COMP.
  match type of COMP with
  | eutt _ (ITree.bind _ ?k) _ => remember k
  end.
  unfold interp_helix in COMP.

  (* No idea what this mismatch is *)
  match type of COMP with
  | context[denoteDSHOperator ?x _] =>
      assert (TMP : dynwin_F_σ ≡ x)
(* by admit *)
  end.
  rewrite <- TMP in COMP; clear TMP.
  rewrite EQ in COMP.
  rewrite interp_fail_ret in COMP.
  cbn in COMP.
  rewrite translate_ret in COMP.
  rewrite bind_ret_l in COMP.
  subst i.

  rewrite interp_helix_bind in COMP.
  clear LUF.
  assert (LUF: memory_lookup f_omemory dynwin_y_addr ≡ Some y_fmem) by admit.
  eapply interp_helix_MemLU in LUF.
  rewrite LUF in COMP.
  rewrite bind_ret_l in COMP.

  assert (exists foo, (ListSetoid.monadic_Lbuild (Pos.to_nat 1)
                    (λ (j : nat) (_ : (j < Pos.to_nat 1)%mc),
                      trywith "Invalid output memory block" (FHCOL.mem_lookup j y_fmem))) ≡ inr foo) as [foo EQ'] by admit.
  rewrite EQ' in COMP; cbn in COMP.

  rewrite interp_helix_ret in COMP.
  cbn in COMP.

  (* Ret x ~R~ t -> exists y, t ~~ Ret y /\ R x y ?? *)
*)
Admitted.
