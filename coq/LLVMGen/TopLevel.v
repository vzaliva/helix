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


Notation mcfg_ctx fundefs :=
  (λ (T : Type) (call : CallE T),
    match call in (CallE T0) return (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T0) with
    | LLVMEvents.Call dt0 fv args0 =>
        dfv <- concretize_or_pick fv True;;
        match lookup_defn dfv fundefs with
        | Some f_den => f_den args0
        | None => dargs <- map_monad (λ uv : uvalue, pickUnique uv) args0;; Functor.fmap dvalue_to_uvalue (trigger (ExternalCall dt0 fv dargs))
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
  (* cbn* in COMP. *)
  (* simp/g. *)
  pose proof memory_invariant_after_init _ _ (conj HINIT COMP') as INIT_MEM; clear COMP' HINIT.
  match type of INIT_MEM with
  | context[mcfg_of_tle ?x] => remember x as tmp; cbn in Heqtmp; subst tmp
  end.
  match goal with
    |- context [semantics_llvm ?x] => remember x as G eqn:VG; apply boxh_cfg in VG
  end.
  destruct u.

  edestruct @eutt_ret_inv_strong as (RESLLVM & EQLLVMINIT & INVINIT); [apply INIT_MEM |].
  destruct RESLLVM as (memI & [ρI sI] & gI & []).

  inv INVINIT.
  destruct decl_inv as [(main_addr & EQmain) (dyn_addr & EQdyn)].
  cbn in EQdyn.

  unshelve epose proof @compile_FSHCOL_correct _ _ _ dynwin_F_σ dynwin_F_memory _ _ (Name "main_block") _ gI ρI memI Heqs0 _ _ _ _ as RES; clear Heqs0; cycle -1.

  -
    eapply interp_mem_interp_helix_ret in EQ.
    rewrite EQ in RES.
    clear EQ.
    edestruct @eutt_ret_inv_strong as (RESLLVM2 & EQLLVM2 & INV2); [apply RES |].
    destruct RESLLVM2 as (mem2 & ρ2 & g2 & v2).

    assert (forall x, semantics_llvm G ≈ x).
    { intros ?.

      unfold semantics_llvm, semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm.
      simpl bind.
      rewrite interp3_bind.
      rewrite EQLLVMINIT.
      rewrite bind_ret_l.
      rewrite interp3_bind.
      match goal with
        |- context[ITree.bind _ ?k] => remember k end.
      destruct VG. subst.
      cbn.
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
      cbn.
      rewrite interp3_bind.
      rewrite interp3_GR; [| apply EQmain].
      repeat (rewrite bind_ret_l || rewrite interp3_ret).
      cbn.
      match goal with
        |- context [denote_mcfg ?x] => remember x as G eqn:VG; apply boxh_cfg in VG
      end.

      rewrite denote_mcfg_unfold_in; cycle -1.

      {
      destruct VG; subst.
      unfold lookup_defn.
      rewrite assoc_tl.
      apply assoc_hd.
      admit. (* addresses are distincts *)
      }
      cbn.
      match goal with
        |- context [interp_mrec ?x] => remember x as ctx
      end.
      rewrite bind_ret_l.
      rewrite interp_mrec_bind.
      rewrite interp_mrec_trigger.
      cbn.
      rewrite interp3_bind.


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

      rewrite denote_ocfg_unfold_in; cycle -1.
      rewrite find_block_eq; reflexivity.
      rewrite denote_block_unfold.
      rewrite denote_no_phis.
      rewrite bind_ret_l.
      rewrite bind_bind.
      rewrite denote_code_cons.
      rewrite bind_bind,translate_bind.
      rewrite interp_mrec_bind, interp3_bind.
      rewrite bind_bind.
      cbn.
      focus_single_step_l.
      subst ctx.

      match goal with
        |- context[interp_mrec ?x ] =>
          replace x with (mcfg_ctx G) by reflexivity
      end.
      rewrite interp3_call_void; cycle 1.
      reflexivity.
      eauto.
      {
        destruct VG; subst.
        unfold lookup_defn.
        apply assoc_hd.
      }

      cbn.
      rewrite bind_bind.
      match goal with
        |- context [interp_mrec ?x] => remember x as ctx
      end.
      rewrite translate_bind, interp_mrec_bind,interp3_bind, bind_bind.

      Lemma foo :

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

      idtac.
      Import Interp.

      rewrite foo; cycle 1.
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
