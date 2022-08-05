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

TOFIX: stupid nonsense, mixing up memory-level computation where I shouldn't
 *)
Definition denote_FSHCOL' (p:FSHCOLProgram) (data:list binary64) σ
  : itree Event (list binary64) :=
  let xindex := List.length p.(globals) in
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

(* Lemma helix_initial_ *)

(* TODO:
   Why does [helix_initial_memory p data] succeeds?
 *)
(* helix_initial_memory is actually pure!! *)
Lemma compiler_correct_aux:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))),
  forall s hmem hdata σ,
    compile_w_main p data newState ≡ inr (s,pll) ->
    helix_initial_memory p data ≡ inr (hmem, hdata, σ) ->
    eutt fhcol_to_llvm_rel (semantics_FSHCOL' p data σ hmem) (semantics_llvm pll).
Proof.
  intros * COMP.
  unfold compile_w_main,compile in COMP.
  cbn* in COMP.
  simp/g.
  unshelve epose proof @compile_FSHCOL_correct _ _ _ (* dynwin_F_σ dynwin_F_memory *) _ _ _ _ _ _ _ _ _ Heqs _ _ _ _.
  (* pose proof memory_invariant_after_init _ _ (conj INIT COMP) as INIT_MEM. *)
Admitted.

Lemma compiler_correct_aux':
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))),
  forall s (* hmem hdata σ *),
    (* helix_initial_memory p data ≡ inr (hmem, hdata, σ) -> *)
    compile_w_main p data newState ≡ inr (s,pll) ->
    eutt fhcol_to_llvm_rel (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
Admitted.


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
        exists g l m r, semantics_llvm pll ≡ Ret (m,(l,(g, r))) /\
                     final_rel_val y r.
Proof.
  intros.

  edestruct initial_memory_from_data
    as (dynwin_F_memory & data_garbage & dynwin_F_σ & HINIT & RFM & RFΣ);
    try eassumption.

  (* The current statement gives us essentially FHCOL-level inputs and outputs,
     and relate them to the source *)
  edestruct top_to_FHCOL
    with (dynwin_F_σ := dynwin_F_σ) (dynwin_F_memory := dynwin_F_memory)
    as (r_omemory & y_rmem' & EVR & LUR & TRR & f_omemory & y_fmem & EVF & LUF & TRF);
    eauto/g.

  instantiate (1:=DynWin_FHCOL_hard).
  rewrite DynWin_FHCOL_hard_OK.
  repeat constructor.

  1,2: now repeat constructor.

  (* TODO : evaluation in terms of equiv and not eq, contrary to what' assumed in EvalDenoteEquiv.
     Is it an easy fix to Denote_Eval_Equiv?
   *)
  match type of EVF with
  | ?x = ?y => clear EVF; assert (EVF:x ≡ y) by admit
  end.
  (* We know that we can see the evaluation of the FHCOL operator under an itree-lense  *)
  pose proof (Denote_Eval_Equiv _ _ _ _ _ EVF) as EQ.

  eapply compiler_correct_aux' in COMP; try eassumption.
  clear -EQ COMP HINIT.
  unfold semantics_FSHCOL, denote_FSHCOL in COMP.
  Opaque denote_initFSHGlobals.
  cbn in COMP. rewrite interp_helix_bind in COMP.
  pose proof helix_inital_memory_denote_initFSHGlobals _ _ _ _ _ HINIT.
  (* This broke after the removal of [translate RHCOL = inr FHCOL] assumption,
     replacing with DynWin_FHCOL_hard *)
  (*
  rewrite H, bind_ret_l in COMP.
  clear H.
  rewrite interp_helix_bind, interp_helix_MemAlloc, bind_ret_l in COMP.
  rewrite interp_helix_bind, interp_helix_MemAlloc, bind_ret_l in COMP.
  destruct (constMemBlock (Pos.to_nat 5) data_garbage) eqn:EQ'.
  rewrite interp_helix_bind, interp_helix_MemSet, bind_ret_l in COMP.
  rewrite interp_helix_bind in COMP.
  unfold interp_helix at 1 in COMP.
   *)

  (* No idea what this mismatch is *)
  assert (dynwin_F_σ ++
                           [(FHCOLITree.DSHPtrVal (FHCOLITree.memory_next_key dynwin_F_memory) dynwin_o',
                            false);
                           (FHCOLITree.DSHPtrVal (FHCOLITree.memory_next_key dynwin_F_memory) dynwin_i',
                           false)] ≡ dynwin_F_σ) by admit.
  rewrite H in COMP; clear H.

  (* (FHCOLITree.memory_set dynwin_F_memory (FHCOLITree.memory_next_key dynwin_F_memory) m) *)




  (* rewrite HINIT in COMP. *)
  (* cbn in COMP. *)
  (* rewrite bind_ret_l in COMP. *)
  (* rewrite interp_helix_bind in COMP. *)
  (* unfold interp_helix at 1 in COMP. *)

  (* clear - EQ EVF COMP HINIT. *)
  (* rewrite HINIT in COMP. *)
  (* pose proof compile_FSHCOL_correct *)

  (* Now we know that the compilation of operators is correct *)
Admitted.
