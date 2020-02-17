Require Import Coq.Arith.Arith.
Require Import Psatz.

Require Import Coq.Strings.String.

Notation "x @@ y" := (String.append x y) (right associativity, at level 60) : string_scope.

  Lemma string_cons_app :
    forall x y,
      String x y = ((String x "") @@ y)%string.
  Proof.
    reflexivity.
  Qed.

  Lemma string_app_assoc :
    forall (a b c : string),
      eq (a @@ (b @@ c))%string ((a @@ b) @@ c)%string.
  Proof.
    intros a b c.
    induction a.
    - reflexivity.
    - simpl. rewrite IHa.
      reflexivity.
  Qed.

Import Coq.Strings.String Strings.Ascii.
Open Scope string_scope.
Open Scope char_scope.

Require Import Coq.Lists.List.

  (* Lemma blah : *)
  (*   forall (b : bool), *)
  (*   (String "y" (String "a" (String "a" (if b then "!" else "?")))) = "yay"%string. *)
  (* Proof. *)
  (*   intros b. *)
  (*   replace (String "y" (String "a" (String "a" (if b then "!"%string else "?"%string)))) with ("yaa" @@ (if b then "!"%string else "?"%string)). *)
  (*   Focus 2. *)

  (*   Ltac rewrite_str acc s := *)
  (*     match s with *)
  (*     | (String ?x EmptyString) => idtac acc; idtac x *)
  (*     | (String ?x ?y) => rewrite_str (acc ++ )%list y *)
  (*     end. *)

  (*   match goal with *)
  (*   | [ |- context [String ?x ?y] ] => rewrite_str (@nil ascii) (String x y) *)
  (*   end. *)


  (* Qed. *)

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.LLVMGen.Data.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Tactics.HelixTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Map.FMapAList.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.TopLevelRefinements.
Require Import Vellvm.LLVMEvents.

Require Import Ceres.Ceres.

Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Basics.Basics.
Require Import ITree.Interp.InterpFacts.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.

Definition model_llvm' := model_to_L3 helix_intrinsics.

Definition E_mcfg: Type -> Type := (IO.ExternalCallE +' IO.PickE +' UBE +' DebugE +' FailureE) +' (StaticFailE +' DynamicFailE).
Definition E_cfg: Type -> Type := (IO.CallE +' IO.PickE +' UBE +' DebugE +' FailureE) +' (StaticFailE +' DynamicFailE).

Definition semantics_llvm_mcfg p: itree E_mcfg _ := translate inl_ (model_llvm' p).

Definition semantics_llvm (prog: list (toplevel_entity typ (list (LLVMAst.block typ)))) :=
  TopLevelEnv.lift_sem_to_mcfg semantics_llvm_mcfg prog.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Fixpoint denote_initFSHGlobals
         (data: list binary64)
         (globals: list (string * FSHValType))
  : itree Event (list binary64 * evalContext) :=
    match globals with
    | [] => ret (data, [])
    | (_,gt)::gs =>
      match gt with
      | FSHnatValType => Sfail "Unsupported global type: nat"
      | FSHFloatValType =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
         let '(x, data) := rotate Float64Zero data in
         ret (data, (DSHCTypeVal x)::σ)
      | FSHvecValType n =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
         let (data,mb) := constMemBlock n data in
         k <- trigger (MemAlloc n);;
         trigger (MemSet k mb);;
         let p := DSHPtrVal k n in
         ret (data, (p::σ))
      end
    end.

Definition denote_FSHCOL (p:FSHCOLProgram) (data:list binary64)
  : itree Event (list binary64) :=
  '(data, σ) <- denote_initFSHGlobals data p.(globals) ;;
  xindex <- trigger (MemAlloc p.(i));;
  yindex <- trigger (MemAlloc p.(o));;
  let '(data, x) := constMemBlock p.(i) data in
  trigger (MemSet xindex x);;

  let σ := List.app σ [DSHPtrVal yindex p.(o); DSHPtrVal xindex p.(i)] in
  denoteDSHOperator σ p.(op);;
  bk <- trigger (MemLU "denote_FSHCOL" yindex);;
  lift_Derr (mem_to_list "Invalid output memory block" p.(o) bk).

Definition semantics_FSHCOL p data: itree E_mcfg (memory * list binary64) :=
  translate (@subevent _ E_mcfg _) (interp_Mem (denote_FSHCOL p data) memory_empty).

(* MOVE TO VELLVM *)
Definition normalize_types_blocks (env: list _) (bks: list (LLVMAst.block typ))
  : list (LLVMAst.block DynamicTypes.dtyp) :=
  List.map
    (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env)) bks.
Import IO TopLevelEnv Global Local.

Definition interp_cfg_to_L3:
  forall (R: Type),
    IS.intrinsic_definitions ->
    itree instr_E R ->
    global_env ->
    local_env ->
    memory ->
    itree (CallE +' PickE +' UBE +' DebugE +' FailureE)
          (memory * (local_env * (global_env * R))) :=
  fun R defs t g l m =>
    let L0_trace := INT.interpret_intrinsics defs t in
    let L1_trace       := Util.runState (interp_global L0_trace) g in
    let L2_trace       := Util.runState (interp_local  L1_trace) l in
    let L3_trace       := Util.runState (M.interp_memory L2_trace) m in
    L3_trace.

Section StateTypes.

  Local Open Scope type_scope.

  Definition LLVM_memory_state_partial
    := memory *
       (local_env * (global_env)).

  Definition LLVM_memory_state_full
    := memory *
       (local_env * @Stack.stack (local_env) * (global_env)).

  Definition LLVM_state_partial
    := memory * (local_env * (global_env * (block_id + uvalue))) .

  Definition LLVM_state_full
    := memory * ((local_env) * @Stack.stack (local_env) * (global_env * (block_id + uvalue))).

  Definition LLVM_sub_state_partial (T:Type): Type
    := memory * (local_env * (global_env * T)).

  Definition LLVM_sub_state_full (T:Type): Type
    := memory * (local_env * @Stack.stack (local_env) * (global_env * T)).

  Definition LLVM_state_final :=
    LLVM_sub_state_full (uvalue).

  (* -- Injections -- *)

  Definition mk_LLVM_sub_state_partial_from_mem (T:Type) (v:T): LLVM_memory_state_partial -> (LLVM_sub_state_partial T)
    := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

  Definition mk_LLVM_sub_state_full_from_mem (T:Type) (v:T): LLVM_memory_state_full -> (LLVM_sub_state_full T)
    := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

End StateTypes.

Section RelationTypes.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Type_R_memory: Type
    := evalContext ->
       MDSHCOLOnFloat64.memory → LLVM_memory_state_partial → Prop.

  (** Type of bisimilation relation between between DSHCOL and LLVM states.
    This relation could be used for fragments of CFG [cfg].
   *)
  Definition Type_R_partial: Type
    := evalContext ->
       MDSHCOLOnFloat64.memory * () → LLVM_state_partial → Prop.

  (** Type of bisimilation relation between between DSHCOL and LLVM states.
      This relation could be used for "closed" CFG [mcfg].
   *)
  Definition Type_R_full: Type
    := evalContext ->
       MDSHCOLOnFloat64.memory * (list binary64) → LLVM_state_final → Prop.

End RelationTypes.

Definition get_logical_block (mem: M.memory) (ptr: A.addr): option M.logical_block :=
  let '(b,a) := ptr in
  M.lookup_logical b mem.

Import DynamicTypes.

Definition mem_lookup_llvm_at_i (bk_llvm: M.logical_block) i ptr_size_helix v_llvm :=
  exists offset,
    match bk_llvm with
    | M.LBlock _ bk_llvm _ =>
      M.handle_gep_h (DTYPE_Array (Z.of_nat ptr_size_helix) DTYPE_Double)
                     0
                     [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))] ≡ inr offset /\
      M.deserialize_sbytes
        (M.lookup_all_index offset (M.sizeof_dtyp DTYPE_Double) bk_llvm M.SUndef)
        DTYPE_Double ≡ v_llvm
    end.

(** Injective function from finite naturals [i<domain] to
   arbitrary type.
*)
Record injection_Fin (A:Type) (domain : nat) :=
  mk_injection_Fin
    {
      inj_f : nat -> A;
      inj_f_spec :
        forall x y,
          x < domain /\ y < domain ->
          inj_f x ≡ inj_f y ->
          x ≡ y
    }.

Definition memory_invariant : Type_R_memory :=
  fun σ mem_helix '(mem_llvm, x) =>
    let σ_len := List.length σ in
    σ_len ≡ 0 \/ (* empty env immediately allowed, as injection could not exists *)
    let '(ρ, g) := x in
    exists (ι: injection_Fin raw_id σ_len),
      forall (x: nat) v,
        nth_error σ x ≡ Some v ->
        match v with
        | DSHnatVal v   =>
          (* check local env first *)
          alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat v))) \/
          (* if not found, check global *)
          (alist_find _ (inj_f ι x) ρ ≡ None /\ alist_find _ (inj_f ι x) g ≡ Some (DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat v))))
        | DSHCTypeVal v =>
          (* check local env first *)
          alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Double v) \/
          (* if not found, check global *)
          (alist_find _ (inj_f ι x) ρ ≡ None /\
           alist_find _ (inj_f ι x) g ≡ Some (DVALUE_Double v))
        | DSHPtrVal ptr_helix ptr_size_helix =>
          forall bk_helix,
            memory_lookup mem_helix ptr_helix ≡ Some bk_helix ->
            exists ptr_llvm bk_llvm,
              alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
              get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm /\
              (fun bk_helix bk_llvm =>
                 forall i, i < ptr_size_helix ->
                      exists v_helix v_llvm,
                        mem_lookup i bk_helix ≡ Some v_helix /\
                        mem_lookup_llvm_at_i bk_llvm i ptr_size_helix v_llvm /\
                        v_llvm ≡ UVALUE_Double v_helix
              ) bk_helix bk_llvm
        end.

Require Import ITree.Interp.TranslateFacts.
Require Import ITree.Basics.CategoryFacts.
Require Import StateFacts.

Import Coq.Strings.String Strings.Ascii.
Open Scope string_scope.
Open Scope char_scope.

Import CatNotations.

(* TODO: This is a redefinition from [DSigmaHCOLITree]. To remove after proper reorganization into two files *)
(* TODO: Actually even more so there should be a clean part of the tactics that do the generic structural
   rewriting, and a wrapper around it doing stuff specific to this denotation. We should only need the former
   here I believe *)

Ltac inv_option :=
  match goal with
  | h: Some _ ≡ Some _ |-  _ => inv h
  | h: None   ≡ Some _ |-  _ => inv h
  | h: Some _ ≡ None   |-  _ => inv h
  | h: None   ≡ None   |-  _ => inv h
  end.

Ltac inv_sum :=
  match goal with
  | h: inl _ ≡ inl _ |-  _ => inv h
  | h: inr _ ≡ inr _ |-  _ => inv h
  | h: inl _ ≡ inr _ |-  _ => inv h
  | h: inr _ ≡ inl _ |-  _ => inv h
  end.

Ltac inv_mem_lookup_err :=
  unfold mem_lookup_err, trywith in *;
  break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

Ltac inv_memory_lookup_err :=
  unfold memory_lookup_err, trywith in *;
  break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).


Ltac state_steps :=
  cbn;
  repeat (
      ((match goal with
        | |- ITree.bind (lift_Derr _) _ ≈ _ => break_match_goal; inv_memory_lookup_err; inv_option
        | |- ITree.bind (lift_Serr _) _ ≈ _ => break_match_goal; inv_memory_lookup_err; inv_option
        | |- ITree.bind (State.interp_state _ (lift_Derr _) _) _ ≈ _ => break_match_goal; inv_option
        | |- ITree.bind (State.interp_state _ (lift_Serr _) _) _ ≈ _ => break_match_goal; inv_option
        end) || state_step); cbn).


Lemma denote_bks_nil: forall s, D.denote_bks [] s ≈ ret (inl s).
Proof.
  intros s; unfold D.denote_bks.
  unfold loop.
  cbn. rewrite bind_ret_l.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  state_steps.
  reflexivity.
Qed.

(* TODO: Currently this relation just preserves memory invariant.
   Maybe it needs to do something more?
 *)
Definition bisim_partial: Type_R_partial
  :=
    fun σ '(mem_helix, _) '(mem_llvm, x) =>
      let '(ρ, (g, bid_or_v)) := x in
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)).

(* Definition interp_cfg'_to_L3: *)
(*   forall (R: Type), *)
(*     IS.intrinsic_definitions -> *)
(*     itree (instr_E +' (StaticFailE +' DynamicFailE)) R -> *)
(*     global_env -> *)
(*     local_env -> *)
(*     memory -> *)
(*     itree E_cfg *)
(*           (memory * (local_env * (global_env * R))).  *)
(*   fun R defs t g l m => *)
(*     let L0_trace := INT.interpret_intrinsics defs t in *)
(*     let L1_trace       := Util.runState (interp_global L0_trace) g in *)
(*     let L2_trace       := Util.runState (interp_local  L1_trace) l in *)
(*     let L3_trace       := Util.runState (M.interp_memory L2_trace) m in *)
(*     L3_trace. *)


(* Changed my mind, I think we don't need this if we work under the translation rather than try to commute it first *)
  Section PARAMS.
    Variable (E F G : Type -> Type).
    Context `{FailureE -< F} `{UBE -< F} `{PickE -< F}.
    Notation Effin := ((E +' IntrinsicE +' MemoryE +' F) +' G).
    Notation Effout := ((E +' F) +' G).

    Definition E_trigger {M} : forall R, E R -> (Monads.stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (Monads.stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R, G R -> (Monads.stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_memory'' :
      itree Effin ~> Monads.stateT M.memory_stack (itree Effout)  :=
      State.interp_state (case_ (case_ E_trigger (case_ M.handle_intrinsic (case_ M.handle_memory F_trigger))) G_trigger).

    (* Lemma interp_memory_bind : *)
    (*   forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) m, *)
    (*     runState (interp_memory (ITree.bind t k)) m ≅ *)
    (*      ITree.bind (runState (interp_memory t) m) (fun '(m',r) => runState (interp_memory (k r)) m'). *)
    (* Proof. *)
    (*   intros. *)
    (*   unfold interp_memory. *)
    (*   setoid_rewrite interp_state_bind. *)
    (*   apply eq_itree_clo_bind with (UU := Logic.eq). *)
    (*   reflexivity. *)
    (*   intros [] [] EQ; inv EQ; reflexivity. *)
    (* Qed. *)

    (* Lemma interp_memory_ret : *)
    (*   forall (R : Type) g (x: R), *)
    (*     runState (interp_memory (Ret x: itree Effin R)) g ≅ Ret (g,x). *)
    (* Proof. *)
    (*   intros; apply interp_state_ret. *)
    (* Qed. *)

  End PARAMS.

  Instance eutt_interp_cfg_to_L3 (defs: IS.intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L3 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L3, Util.runState.
    subst; rewrite H.
    (* Show Proof. *)
    reflexivity.
  Qed.

  From Vellvm Require Import Util.
  Require Import State.

  (* Move to vellvm *)
  (* ************************************************** *)
  Lemma normalize_types_block_bid :
    forall (env : list (ident * typ)) (b: LLVMAst.block typ),
      blk_id (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env) b) ≡ blk_id b.
  Proof.
    intros env b.
    destruct b. reflexivity.
  Qed.

  Lemma normalize_types_block_term :
    forall (env : list (ident * typ)) (b: LLVMAst.block typ) (nextblock : block_id),
      snd (blk_term b) ≡ TERM_Br_1 nextblock ->
      snd (blk_term (TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b)) ≡ TERM_Br_1 nextblock.
  Proof.
    intros env b nextblock Hterm.
    destruct b. cbn in *. rewrite Hterm.
    reflexivity.
  Qed.
  (* ************************************************** *)

  Lemma interp_cfg_to_L3_ret (defs: IS.intrinsic_definitions):
    forall {T} (x: T) g l m,
      interp_cfg_to_L3 defs (Ret x) g l m ≅ Ret (m,(l,(g,x))).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    (* setoid_rewrite INT.interp_intrinsics_ret. *)
    (* interp_global_ret. *)
  Admitted. (* YZ: Likely a missing instance for runState, easy to fix *)

  Lemma interp_cfg_to_L3_bind (defs: IS.intrinsic_definitions):
      forall (R S : Type) (t : itree _ R) (k : R -> itree _ S) g l m,
        interp_cfg_to_L3 defs (ITree.bind t k) g l m ≅
        ITree.bind (interp_cfg_to_L3 defs t g l m) (fun '(m', (l', (g',r))) => interp_cfg_to_L3 defs (k r) g' l' m').
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    (* setoid_rewrite INT.interp_intrinsics_ret. *)
    (* interp_global_ret. *)
  Admitted. (* YZ: Likely a missing instance for runState, easy to fix *)

  Ltac eutt_hide_left :=
    match goal with
      |- eutt _ ?t _ => remember t
    end.

  Ltac eutt_hide_right :=
    match goal with
      |- eutt _ _ ?t => remember t
    end.

  (* TODO: Move this to Vellvm *)
  Definition TT {A} : relation A := fun _ _ => True.

  Lemma denote_bks_singleton :
    forall (b : LLVMAst.block dtyp) (bid : block_id) (nextblock : block_id),
      (blk_id b) ≡ bid ->
      (snd (blk_term b)) ≡ (TERM_Br_1 nextblock) ->
      (blk_id b) <> nextblock ->
      eutt (Logic.eq) (D.denote_bks [b] bid) (D.denote_block b).
  Proof.
    intros b bid nextblock Heqid Heqterm Hneq.
    cbn.
    rewrite bind_ret_l.
    rewrite KTreeFacts.unfold_iter_ktree.
    cbn.
    destruct (Eqv.eqv_dec_p (blk_id b) bid) eqn:Heq'; try contradiction.
    repeat rewrite bind_bind.
    rewrite Heqterm.
    cbn.
    setoid_rewrite translate_ret.
    setoid_rewrite bind_ret_l. 
    destruct (Eqv.eqv_dec_p (blk_id b) nextblock); try contradiction.
    repeat setoid_rewrite bind_ret_l. unfold Datatypes.id.
    reflexivity.
  Qed.

  (* Should probably be in itrees? *)
(*
    for an opeartor, in initialized state
    TODO: We could probably fix [env] to be [nil]
 *)

  Lemma DSHAssign_singleton :
    forall (nextblock : block_id) (src dst : MemVarRef) (st st' : IRState) (bid_in : block_id) 
      (bks : list (LLVMAst.block typ)),
      genIR (DSHAssign src dst) nextblock st ≡ inr (st', (bid_in, bks)) ->
      exists b,
        genIR (DSHAssign src dst) nextblock st ≡ inr (st', (bid_in, [b])) /\ snd (blk_term b) ≡ TERM_Br_1 nextblock /\ blk_id b ≡ bid_in /\ bks ≡ [b].
  Proof.
    intros nextblock src dst st st' bid_in bks HCompile.
    simpl in HCompile. destruct src, dst.
    simpl in HCompile.
    repeat break_match_hyp; try inl_inr.
    inv Heqs; inv HCompile.
    unfold genFSHAssign in Heqs2.
    cbn in Heqs2.
  Admitted.

Lemma compile_FSHCOL_correct
      (op: DSHOperator): forall (nextblock bid_in : block_id) (st st' : IRState) (bks : list (LLVMAst.block typ)) (σ : evalContext) (env : list (ident * typ)) (mem : MDSHCOLOnFloat64.memory) (g : global_env) (ρ : local_env) (mem_llvm : memory),
  nextblock ≢ bid_in ->    
  bisim_partial σ (mem,tt) (mem_llvm, (ρ, (g, (inl bid_in)))) ->
  genIR op nextblock st ≡ inr (st',(bid_in,bks)) ->
  eutt (bisim_partial σ)
       (translate inr_
                  (interp_Mem (denoteDSHOperator σ op) mem))
       (translate inl_
                  (interp_cfg_to_L3 helix_intrinsics
                                    (D.denote_bks (normalize_types_blocks env bks) bid_in)
                                    g ρ mem_llvm)).
Proof.
  induction op; intros; rename H1 into HCompile.
  - inv HCompile.
    eutt_hide_right; cbn.
    unfold interp_Mem; simpl denoteDSHOperator.
    rewrite interp_state_ret, translate_ret.
    subst i.
    simpl normalize_types_blocks.
    rewrite denote_bks_nil.
    cbn. rewrite interp_cfg_to_L3_ret, translate_ret.
    apply eqit_Ret; auto.
  - (*
      Assign case.
       Need some reasoning about
       - resolve_PVar
       - genFSHAssign
       - D.denote_bks over singletons
     *)
    apply DSHAssign_singleton in HCompile.
    destruct HCompile as (b & HCompile & Hterm & Hbid & Hbksbk).
    subst. unfold normalize_types_blocks.
    eutt_hide_left.
    simpl.

    pose proof (denote_bks_singleton (TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b)) (blk_id b) nextblock.
    assert (eutt (Logic.eq) (D.denote_bks [TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b] (blk_id b)) (D.denote_block (TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b))).
    {
      rewrite (@denote_bks_singleton (TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b) (blk_id b) nextblock (normalize_types_block_bid env b)).
      reflexivity.
      apply normalize_types_block_term; auto.
      rewrite (normalize_types_block_bid env b); auto.
    }
    rewrite H2.
    subst i.
    eutt_hide_right.
    subst i.
    unfold interp_Mem; cbn.
    destruct src, dst.
    simpl in HCompile.
    repeat break_match_hyp; try inl_inr.
    inv Heqs; inv HCompile.
    unfold denotePexp, evalPexp, lift_Serr.
    subst.
    unfold interp_Mem. (* cbn *)
    (* match goal with *)
    (* | |- context[add_comment _ ?ss] => generalize ss; intros ls *)
    (* end. *)
    (* match goal with *)
    (* | |- context[add_comment _ ?ss] => generalize ss; intros ls1 *)
    (* end. *)

    (* subst. eutt_hide_right. *)
    (* cbn. *)
    (* unfold interp_Mem. *)
    (* rewrite interp_state_bind. *)
    (* unfold denotePexp, evalPexp. *)
    (* cbn. *)
    (* repeat setoid_rewrite interp_state_bind. *)
    (* rewrite denote_bks_singleton. *)
    (* destruct src, dst. *)
    (* simpl in HCompile. *)
    (* repeat break_match_hyp; try inl_inr. *)
    (* inv Heqs; inv HCompile. *)
    (* match goal with *)
    (* | |- context[add_comment _ ?ss] => generalize ss; intros ls *)
    (* end. *)
    (* unfold interp_Mem. *)
    (* simpl denoteDSHOperator. *)
    (* rewrite interp_state_bind, translate_bind. *)
    (* match goal with *)
    (*   |- eutt _ ?t _ => remember t *)
    (* end. *)

    (* Need a lemma to invert Heqs2.
       Should allow us to know that the list of blocks is a singleton in this case.
       Need then probably a lemma to reduce proofs about `D.denote_bks [x]` to something like the denotation of x,
       avoiding having to worry about iter.
     *)
    (* cbn; rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_ret, bind_ret_l. *)
    
    admit.

  - (*
      Map case.
      Need some reasoning about
      - denotePexp
      - nat_eq_or_cerr
      - genIMapBody
      - 
     *)
    simpl genIR in HCompile.

    (* repeat rewrite string_cons_app in HCompile. *)

    repeat break_match_hyp; try inl_inr.
    repeat inv_sum.
    cbn.
    (* Need to solve the issue with the display of strings, it's just absurd *)
    eutt_hide_right.
    unfold interp_Mem.
    rewrite interp_state_bind.
    admit.

  - admit.

  - admit.

  - admit.

  - eutt_hide_right.
    cbn. unfold interp_Mem.

    (*
    Check interp_state_bind.
    Check interp_bind.

interp_state_bind
     : ∀ (f : ∀ T : Type, ?E T → ?S → itree ?F (?S * T)) (t : itree ?E ?A) (k : ?A → itree ?E ?B) (s : ?S),
         interp_state f (ITree.bind t k) s
         ≅ ITree.bind (interp_state f t s) (λ st0 : ?S * ?A, interp_state f (k (snd st0)) (fst st0))

interp_bind
     : ∀ (f : ∀ T : Type, ?E T → itree ?F T) (t : itree ?E ?R) (k : ?R → itree ?E ?S),
         interp f (ITree.bind t k) ≅ ITree.bind (interp f t) (λ r : ?R, interp f (k r))

    rewrite interp_state_bind.
    rewrite interp_iter.
*)
    admit.

  - eutt_hide_right.
    cbn.
    unfold interp_Mem.
    rewrite interp_state_bind.
    (* rewrite bind_trigger.
    
    Locate ITree.bind.
    rewrite *)
    admit.
  - admit.

  - admit.

  - (* Sequence case.

     *)

    cbn in HCompile.
    break_match_hyp; try inv_sum.
    break_match_hyp; try inv_sum.
    destruct p, s.
    break_match_hyp; try inv_sum.
    destruct p, s; try inv_sum.
    eapply IHop1 with (env := env) (σ := σ) in Heqs1; eauto.
    eapply IHop2 with (env := env) (σ := σ) in Heqs0; eauto.
    clear IHop2 IHop1.
    eutt_hide_right.
    cbn; unfold interp_Mem in *.
    rewrite interp_state_bind.

    rewrite translate_bind.
    (* Opaque D.denote_bks. *)

    (* Set Nested Proofs Allowed. *)

    (* Lemma add_comment_app: forall bs1 bs2 s, *)
    (*     add_comment (bs1 ++ bs2)%list s ≡ (add_comment bs1 s ++ add_comment bs2 s)%list. *)
    (* Proof. *)
    (*   induction bs1 as [| b bs1 IH]; cbn; auto; intros bs2 s. *)
    (*   f_equal. rewrite IH; auto. *)

    (*   subst i0. *)
    (*   eutt_hide_left. *)
    (*   cbn. rewrite bind_ret_l. *)


(* Definition respectful_eutt {E F : Type -> Type} *)
(*   : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop *)
(*   := i_respectful (fun _ => eutt eq) (fun _ => eutt eq). *)


(* Instance eutt_translate {E F R} *)
(*   : @Proper (IFun E F -> (itree E ~> itree F)) *)
(*             (eq2 ==> eutt RR ==> eutt RR) *)
(*             translate. *)
(* Proof. *)
(*   repeat red. *)
(*   intros until T. *)
(*   ginit. gcofix CIH. intros. *)
(*   rewrite !unfold_translate. punfold H1. red in H1. *)
(*   induction H1; intros; subst; simpl. *)
(*   - gstep. econstructor. eauto. *)
(*   - gstep. econstructor. pclearbot. eauto with paco. *)
(*   - gstep. rewrite H. econstructor. pclearbot. red. eauto 7 with paco. *)
(*   - rewrite tau_euttge, unfold_translate. eauto. *)
(*   - rewrite tau_euttge, unfold_translate. eauto. *)
(* Qed. *)

(* Instance eutt_translate' {E F : Type -> Type} {R : Type} (f : E ~> F) : *)
(*   Proper (eutt eq ==> eutt eq) *)
(*          (@translate E F f R). *)
(* Proof. *)
(*   repeat red. *)
(*   apply eutt_translate. *)
(*   reflexivity. *)
(* Qed. *)

(*     rewrite Heqs1. *)
(* eutt_translate' *)

Admitted.

Definition llvm_empty_memory_state_partial: LLVM_memory_state_partial
  := (M.empty_memory_stack, ([], [])).

Definition bisim_full: Type_R_full  :=
  fun σ  '(mem_helix, v_helix) mem_llvm =>
    let '(m, ((ρ,_), (g, v))) := mem_llvm in
    bisim_partial σ (mem_helix, tt) (mk_LLVM_sub_state_partial_from_mem (inr v) (m, (ρ, g))).


(* This code attempts to mimic global variable initialization from
   [Vellvm.Toplevel] and heavily depends on internal memory
   organization of Vellvm, as in [Vellvm.Handlers.Memory] *)
Section LLVM_Memory_Init.

  (* mimics [Alloca] handler *)
  Definition alloc_global (c_name:string) (c_typ:typ) (m:M.memory) (ms:M.mem_stack) (genv:global_env) :=
    (* TODO: not sure about this [typ] to [dtyp] conversion *)
    let d_typ := TypeUtil.normalize_type_dtyp [] c_typ in
    let new_block := M.make_empty_block d_typ in
    let key := M.next_logical_key m in
    let new_mem := M.add_logical key new_block m in
    match ms with
    | [] => inl "No stack frame for alloca."%string
    | frame :: stack_rest =>
      let new_stack := (key :: frame) :: stack_rest in
      (*  global_env = alist raw_id dvalue *)
      let a := DVALUE_Addr (key, 0%Z) in
      ret (new_mem, new_stack, (Name c_name, a) :: genv, a)
    end.

  (* mimics [Store] handler *)
  Definition init_global (m:M.memory) (ms:M.mem_stack) (a: dvalue) (v:dvalue)
    : err (M.memory * M.mem_stack)
    :=
      match a with
      | DVALUE_Addr (key, i) =>
        match M.lookup_logical key m with
        | Some (M.LBlock sz bytes cid) =>
          let bytes' := M.add_all_index (M.serialize_dvalue v) i bytes in
          let block' := M.LBlock sz bytes' cid in
          ret (M.add_logical key block' m, ms)
        | None => inl "stored to unallocated address"%string
        end
      | _ => inl ("Store got non-address dvalue: " ++ (to_string a))
      end.

End LLVM_Memory_Init.

(* Scalar *)
Definition eval_const_double_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Double, EXP_Double v) => ret (DVALUE_Double v)
  | (_, c_typ) => inl ("Type double expected: " ++ (to_string c_typ))
  end.

(* Array *)
Definition eval_const_arr_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Array _ TYPE_Double, EXP_Array a) =>
    da <- ListSetoid.monadic_fold_left
           (fun ds d => dd <- eval_const_double_exp d ;; ret (dd::ds))
           [] a ;;
    ret (DVALUE_Array da)
  | (_, c_typ) => inl ("Array of doubles expected: " ++ (to_string c_typ))
  end.

Definition eval_const_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Array _ TYPE_Double, EXP_Array a) => eval_const_arr_exp typed_expr
  | (TYPE_Double, EXP_Double v) =>  eval_const_double_exp typed_expr
  | (_, c_typ) => inl ("Unsupported constant expression type: " ++ (to_string c_typ))
  end.

Definition init_one_global (mem_state:LLVM_memory_state_partial) (g:toplevel_entity typ (list (LLVMAst.block typ)))
  : err LLVM_memory_state_partial
  := match g with
     | TLE_Global (mk_global (Name c_name) c_typ
                             true
                             (Some c_initiaizer)
                             (Some LINKAGE_Internal)
                             None None None true None
                             false None None) =>
       let '((m,ms), (lenv, genv)) := mem_state in
       '(m,ms,genv,a) <- alloc_global c_name c_typ m ms genv ;;
       mms <- (eval_const_exp >=> init_global m ms a) (c_typ, c_initiaizer)
       ;;
       ret (mms,(lenv, genv))
     | _ => inl "Usupported global initialization"%string
     end.

Definition init_llvm_memory
           (p: FSHCOLProgram)
           (data: list binary64) : err LLVM_memory_state_partial
  :=
    '(data,ginit) <- initIRGlobals data p.(globals) ;;

    let y := Anon 1%Z in
    let ytyp := getIRType (FSHvecValType p.(o)) in
    let x := Anon 0%Z in
    let xtyp := getIRType (FSHvecValType p.(i)) in

    let xyinit := global_YX p.(i) p.(o) data x xtyp y ytyp in

    (* Will return in order [globals ++ xy] *)
    ListSetoid.monadic_fold_left init_one_global llvm_empty_memory_state_partial
                                 (ginit ++ xyinit)%list.


(** Empty memories and environments should satisfy [memory_invariant] *)
Lemma memory_invariant_empty: memory_invariant [] helix_empty_memory llvm_empty_memory_state_partial.
Proof.
  unfold memory_invariant.
  break_let.
  left.
  auto.
Qed.

Fact initFSHGlobals_globals_sigma_len_eq
     {mem mem' data data'} globals σ:
  initFSHGlobals data mem globals ≡ inr (mem', data', σ) ->
  List.length globals ≡ List.length σ.
Proof.
  unfold initFSHGlobals.

  remember [] as pz.
  replace (Datatypes.length globals) with (List.length pz + List.length globals)%nat
    by (subst pz; reflexivity).
  clear Heqpz. (* poor man generalize *)
  revert mem mem' data data' σ pz.
  induction globals; intros.
  -
    cbv in H.
    inv H.
    cbn.
    rewrite Nat.add_0_r.
    reflexivity.
  -
    cbn in H.
    break_match;[inl_inr|].
    rename Heqe into H1.
    unfold initOneFSHGlobal in H1.
    break_let; subst.
    break_match_hyp.
    +
      inl_inr.
    +
      break_let;subst.
      inv H1.
      eapply IHglobals in H.
      rewrite <- H.
      cbn.
      rewrite Snoc_length.
      lia.
    +
      break_let;subst.
      inv H1.
      eapply IHglobals in H.
      rewrite <- H.
      cbn.
      rewrite Snoc_length.
      lia.
Qed.


(* Maps indices from [σ] to [raw_id].
   Currently [σ := [globals;Y;X]]
   Where globals mapped by name, while [X-> Anon 0] and [Y->Anon 1]
*)
Definition memory_invariant_map (globals : list (string * FSHValType)): nat -> raw_id
  := fun j =>
       let l := List.length globals in
       if Nat.eqb j l then Anon 0%Z (* X *)
       else if Nat.eqb j (S l) then Anon 1%Z (* Y *)
            else
              match nth_error globals j with
              | None => Anon 0%Z (* default value *)
              | Some (name,_) => Name name
              end.

Lemma memory_invariant_map_injectivity (globals : list (string * FSHValType)):
  list_uniq fst globals ->
  forall (x y : nat),
    x < (Datatypes.length globals + 2)%nat ∧ y < (Datatypes.length globals + 2)%nat
    → memory_invariant_map globals x ≡ memory_invariant_map globals y → x ≡ y.
Proof.
  intros U x y [Hx Hy] E.
  unfold lt, peano_naturals.nat_lt in *.
  unfold memory_invariant_map in E.
  repeat break_if; repeat break_match; bool_to_nat; subst; try inv E; auto.
  - apply nth_error_None in Heqo; lia.
  - apply nth_error_None in Heqo; lia.
  -
    unfold list_uniq in U.
    eapply U; eauto.
  - apply nth_error_None in Heqo; lia.
Qed.

Fact initIRGlobals_cons_head_uniq:
  ∀ (a : string * FSHValType) (globals : list (string * FSHValType))
    (data : list binary64) (res : list binary64 *
                                  list (toplevel_entity typ (list (LLVMAst.block typ)))),
    initIRGlobals data (a :: globals) ≡ inr res ->
    forall (j : nat) (n : string) (v : FSHValType),
      (nth_error globals j ≡ Some (n, v) /\ n ≡ fst a) → False.
Proof.
  intros a globals data res H j n v C.
  cbn in H.
  break_let;subst.
  assert(globals_name_present s globals ≡ true).
  {
    clear -C.
    apply nth_to_globals_name_present.
    exists (n,v).
    exists j.
    apply C.
  }
  rewrite H0 in H.
  inl_inr.
Qed.

(* If [initIRGlobals] suceeds, the names of variables in [globals] were unique *)
Lemma initIRGlobals_names_unique globals data res:
  initIRGlobals data globals ≡ inr res → list_uniq fst globals.
Proof.
  revert res data.
  induction globals; intros.
  -
    cbn in H.
    inv H.
    apply list_uniq_nil.
  -
    apply list_uniq_cons.
    split.
    +
      cbn in H.
      break_let; subst.
      break_match_hyp;[inl_inr|].
      break_match_hyp;[inl_inr|].
      break_let; subst.
      break_match_hyp;[inl_inr|].
      break_let; subst.
      inv H.
      eapply IHglobals.
      eauto.
    +
      (* [a] must not be present in [globals] *)
      unfold not.
      intros C.
      destruct C as (j & [n v] & C); cbn in C.
      eapply initIRGlobals_cons_head_uniq; eauto.
Qed.

Fact fold_init_one_global_app
     (lm0 lm1 : memory)
     (g0 g : global_env)
     (d: list (toplevel_entity typ (list (LLVMAst.block typ))))
     (m1 m0 : local_env)
     (H1: ListSetoid.monadic_fold_left init_one_global (lm0, (m0, g0)) d ≡ inr (lm1, (m1, g)))
  : ∃ g', g ≡ app g' g0.
Proof.
  revert H1.
  revert lm1 lm0 g g0 m0 m1.
  induction d; intros.
  -
    cbn in H1.
    inv H1.
    exists [].
    symmetry.
    apply app_nil_l.
  -
    cbn in H1.
    break_match_hyp; [inl_inr|].
    destruct l as [lm' [m' g']].
    unfold init_one_global in Heqe.
    repeat (break_match_hyp; try inl_inr).
    subst.
    cbn in Heqe.
    repeat (break_match_hyp; try inl_inr); subst.
    +
      repeat inl_inr_inv.
      subst.
      unfold alloc_global in Heqs0.
      break_match_hyp; try inl_inr.
      inv Heqs0.
      apply IHd in H1.
      destruct H1.
      exists (app x [(Name s, DVALUE_Addr (M.next_logical_key m, 0%Z))]).
      subst. clear.
      symmetry.
      apply ListUtil.list_app_first_last.
    +
      repeat inl_inr_inv.
      subst.
      unfold alloc_global in Heqs0.
      break_match_hyp; try inl_inr.
      inv Heqs0.
      apply IHd in H1.
      destruct H1.
      exists (app x [(Name s, DVALUE_Addr (M.next_logical_key m, 0%Z))]).
      subst. clear.
      symmetry.
      apply ListUtil.list_app_first_last.
Qed.

Lemma monadic_fold_left_err_app
         {A B : Type}
         (f : A -> B -> err A)
         (s0 s2 : A)
         (l0 l1 : list B):
  ListSetoid.monadic_fold_left f s0 (l0++l1) ≡ inr s2
  ->
  ∃ s1,
  ListSetoid.monadic_fold_left f s0 l0 ≡ inr s1 /\
  ListSetoid.monadic_fold_left f s1 l1 ≡ inr s2.
Proof.
  revert l0 l1 s0 s2 f.
  induction l0; intros.
  -
    cbn in *.
    eexists; auto.
  -
    cbn in H.
    break_match_hyp; [inl_inr|].
    eapply IHl0 in H.
    destruct H as [s1 [H1 H2]].
    eexists.
    split; [|eauto].
    cbn.
    rewrite Heqe.
    apply H1.
Qed.

(* TODO: This is general-purpose. Move elsewhere? *)
Lemma mapsto_alist_app_1st
      {K V: Type}
      (R : K → K → Prop)
      `{RD: RelDec.RelDec _ R}
      `{RDC: @RelDec.RelDec_Correct K R RD}
      (g g' : alist K V)
      (v : V)
      (n : K):
  mapsto_alist RD g n v ->
  mapsto_alist RD (g ++ g')%list n v.
Proof.
  revert v n.
  induction g; intros.
  -
    inversion H.
  -
    cbn.
    destruct a as [k0 v0].
    apply mapsto_alist_cons; [apply RDC|].
    destruct (RelDec.rel_dec n k0) eqn:K0.
    +
      right.
      split.
      *
        rewrite RelDec.rel_dec_correct in K0.
        apply K0.
      *
        apply mapsto_alist_cons in H ; [| auto].
        destruct H.
        destruct H.
        rewrite RelDec.rel_dec_correct in K0.
        congruence.
        apply H.
    +
      left.
      split.
      *
        apply IHg.
        apply mapsto_alist_cons in H ; [| auto].
        destruct H.
        apply H.
        destruct H.
        apply RelDec.rel_dec_correct in H.
        congruence.
      *
        apply RelDec.neg_rel_dec_correct in K0.
        apply K0.
Qed.

(*
Fact init_one_global_fold_in_1st
     (lm0 lm1 : memory)
     (g0 g : global_env)
     (d0 d1 : list (toplevel_entity typ (list (LLVMAst.block typ))))
     (m0 : local_env)
     (H0: ListSetoid.monadic_fold_left init_one_global llvm_empty_memory_state_partial d0 ≡ inr (lm0, (m0, g0)))
     (H1: ListSetoid.monadic_fold_left init_one_global (lm0, (m0, g0)) d1 ≡ inr (lm1, ([ ], g)))
     (v: dvalue)
     (n: raw_id)
  :
    mapsto_alist AstLib.eq_dec_raw_id g0 n v ->
    mapsto_alist AstLib.eq_dec_raw_id g n v.
Proof.
  intros H.
  pose proof (fold_init_one_global_app _ _ _ _ H1) as [g' G].
  clear - G H.
  subst g.
  apply mapsto_alist_app_1st.
  typeclasses eauto.
  apply H.
Qed.
 *)

Fact fold_init_one_global_empty_local
     (gdecls : list (toplevel_entity typ (list (LLVMAst.block typ))))
     (m m1 : memory)
     (l1 : local_env)
     (g g1 : global_env)
  :
    ListSetoid.monadic_fold_left init_one_global (m, ([], g)) gdecls ≡ inr (m1, (l1, g1))
    → l1 ≡ [].
Proof.
  revert g g1 l1 m m1.
  induction gdecls; intros.
  -
    cbn in H.
    inv H.
    reflexivity.
  -
    cbn in H.
    break_match_hyp; [inl_inr|].
    unfold init_one_global in Heqe.
    repeat break_match_hyp; subst; try inl_inr.
    cbn in Heqe.
    repeat break_match_hyp; subst; try inl_inr.
    repeat inl_inr_inv.
    destruct l as [m' [l' g']].
    tuple_inversion.
    eapply IHgdecls; clear IHgdecls.
    repeat inl_inr_inv.
    eauto.
    destruct l as [m' [l' g']].
    inv Heqe.
    eauto.
Qed.

(** [memory_invariant] relation must holds after initialization of global variables *)
Lemma memory_invariant_after_init
      (p: FSHCOLProgram)
      (data: list binary64) :
  forall hmem σ lmem hdata,
                helix_intial_memory p data ≡ inr (hmem,hdata,σ) /\
                init_llvm_memory p data ≡ inr lmem ->
                memory_invariant σ hmem lmem.
Proof.
  intros hmem σ lmem hdata [HI LI].
  unfold memory_invariant.
  repeat break_let; subst.
  unfold helix_intial_memory, init_llvm_memory in *.
  cbn in *.
  repeat break_match_hyp ; try inl_inr.
  subst.
  inv HI.
  cbn in *.
  repeat break_let; subst.

  right. (* as [σ] is never empty after init *)
  rename Heqp0 into HCY, m1 into ydata.
  rename Heqp4 into HCX, m2 into xdata.
  rename Heqe0 into HFSHG, l2 into fdata', e into σ.
  rename Heqe into HIRG, l0 into ldata', l1 into gdecls.
  remember (global_YX i o ldata' (Anon 0%Z) (TYPE_Array (Z.of_nat i) TYPE_Double)
                      (Anon 1%Z) (TYPE_Array (Z.of_nat o) TYPE_Double)) as xydecls eqn:HXY.
  rename l3 into fdata''.

  pose proof (monadic_fold_left_err_app _ _ _ _ LI) as [s1 [HG HFXY]].
  destruct s1 as [m1 [l1 g1]].

  (* No local variables initialize in init stage *)
  assert(L1: l1 ≡ []) by eapply fold_init_one_global_empty_local, HG; subst l1.
  assert(L: l ≡ []) by eapply fold_init_one_global_empty_local, HFXY; subst l.

  cbn in *.

  unshelve eexists.
  exists (memory_invariant_map globals).

  (* Injectivity proof *)
  {
    rewrite app_length.
    erewrite <- initFSHGlobals_globals_sigma_len_eq with (globals0:=globals).
    2: eauto.
    simpl.
    apply memory_invariant_map_injectivity.
    eapply initIRGlobals_names_unique.
    eauto.
  }

  intros x v Hn.
  break_match.
  -
    (* [DSHnatVal] must end up in globals *)
    right.
    split; [trivial|].
    (* but currently nat constants are not implemented so we
       shortcut this branch *)
    exfalso.
    clear - Hn HFSHG.
    rename HFSHG into F.

    apply ListUtil.nth_app in Hn.
    destruct Hn as [[Hn Hx] | [Hn Hx]].
    2:{
      remember (x - Datatypes.length σ)%nat as k.
      destruct k; inv Hn.
      destruct k; inv H0.
      rewrite Util.nth_error_nil in H1.
      inv H1.
    }
    clear i o.
    clear Hx.
    revert F Hn.
    revert data fdata' m0 σ x.
    generalize helix_empty_memory as mem.

    intros mem data fdata' m0 σ x F Hn.
    contradict Hn.
    revert x n.
    revert F.
    revert σ m0 data fdata' mem.
    induction globals; intros.
    +
      cbn in F.
      inv F.
      rewrite Util.nth_error_nil.
      intros N.
      inversion N.
    +
      cbn in F.
      break_match_hyp; [inl_inr|].
      destruct a; destruct f; cbn in *.
      *
        inl_inr.
      *
        break_let; subst.
        symmetry in Heqe.
        inl_inr_inv.
        subst p.
        revert x n.
        (* TODO: from [F] split [\sigma] *)
        admit.
      *
    admit.
  -
    (* [DSHCTypeVal] must end up in globals *)
    right.
    split; [trivial|cbn].
    apply ListUtil.nth_app in Hn.
    rename HFSHG into F.
    destruct Hn as [[Hn Hx] | [Hn Hx]].
    2:{
      remember (x - Datatypes.length σ)%nat as k.
      destruct k; inv Hn.
      destruct k; inv H0.
      rewrite Util.nth_error_nil in H1.
      inv H1.
    }
    clear v Heqd.

    (* Deal with X,Y first *)
    pose proof (initFSHGlobals_globals_sigma_len_eq globals F) as GSL.
    unfold memory_invariant_map.
    repeat break_if; bool_to_nat; try lia.

    (* X,Y eliminated, [x] somewhere in globals *)
    break_match.
    2:{
      (* impossible case *)
      apply ListNth.nth_error_length_lt in Hn.
      apply ListUtil.nth_beyond_idx in Heqo0.
      lia.
    }
    destruct p as (gname, gval).

    (* unify lengths *)
    remember (Datatypes.length σ) as l eqn:SL; symmetry in SL.
    clear Heqb Heqb0.

    rename m0 into fm0.

    (* we know, [gname] is in [gdecls] and not in [xydecls] *)
    (* eapply init_one_global_fold_in_1st;eauto. *)
    clear LI HXY xydecls HFXY HCX HCY xdata ydata hdata.
    admit.
  -
    (* [DSHPtrVal] must end up in memory *)
    intros bk_helix HMH.
    eexists.
    eexists.
    admit.
Admitted.

(* with init step  *)
Lemma compiler_correct_aux:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (list (LLVMAst.block typ))),
    compile_w_main p data ≡ inr pll ->
    eutt (bisim_full []) (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
Admitted.

(** Relation bewteen the final states of evaluation and execution
    of DHCOL program.

    At this stage we do not care about memory or environemnts, and
    just compare return value of [main] function in LLVM with
    evaulation results of DSHCOL.
 *)
Definition bisim_final: Type_R_full :=
  fun σ '(_, h_result) '(_,(_,(_,llvm_result))) =>
    match llvm_result with
    | UVALUE_Array arr => @List.Forall2 _ _
                                       (fun ve de =>
                                          match de with
                                          | UVALUE_Double d =>
                                            Floats.Float.cmp Integers.Ceq d ve
                                          | _ => False
                                          end)
                                       h_result arr
    | _ => False
    end.

Lemma bisim_partial_memory_subrelation: forall σ helix_state llvm_state,
    let '(mem_helix, _) := helix_state in
    let '(mem_llvm, (ρ, (g, _))) := llvm_state in
    bisim_partial σ helix_state llvm_state -> memory_invariant σ mem_helix (mem_llvm, (ρ, g)).
Proof.
  intros σ helix_state llvm_state.
  repeat break_let.
  subst.
  intros H.
  auto.
Qed.

Lemma bisim_full_partial_subrelation: forall σ helix_state llvm_state,
    let '(mem_helix, v_helix) := helix_state in
    let '(m, ((ρ,_), (g, v))) := llvm_state in
    bisim_full σ helix_state llvm_state -> bisim_partial σ (mem_helix, tt) (mk_LLVM_sub_state_partial_from_mem (inr v) (m, (ρ, g))).
Proof.
  intros σ helix_state llvm_state.
  repeat break_let.
  subst.
  intros H.
  unfold mk_LLVM_sub_state_partial_from_mem.
  auto.
Qed.

(* Top-level compiler correctness lemma  *)
Theorem compiler_correct:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (list (LLVMAst.block typ))),
    compile_w_main p data ≡ inr pll ->
    eutt (bisim_final []) (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
  intros p data pll H.
  (* This no longer follows from [compiler_correct_aux]. It will
     at pen-ultimate step when the [main] does [return] on a memory
     block.

       eapply eqit_mon.
       3:apply bisim_full_final_subrelation.
       3:eapply compiler_correct_aux.
       tauto.
       tauto.
       tauto.
   *)
Admitted.
