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

    Ltac rev_str_helper acc s :=
      match s with
      | EmptyString => acc
      | (String ?x ?y) =>
        rev_str_helper (String x acc) y
      end.

    Ltac rev_str s := rev_str_helper EmptyString s.
    
    Ltac rewrite_str acc s :=
      match s with
      | (String ?x EmptyString) =>
        let r := rev_str acc in
        constr:(r)
      | (String ?x ?y) => rewrite_str (String x acc) y
      end.

    Ltac last_str s :=
      match s with
      | (String ?x EmptyString) => constr:(String x EmptyString)
      | (String ?x ?y) => last_str y
      end.

    Ltac make_append_str s :=
      match s with
      | (String ?x ?y) =>
        let rs := rewrite_str EmptyString (String x y) in
        let ls := last_str y in
        replace (String x y) with (rs @@ ls)%string by reflexivity
      end.

Import Coq.Strings.String Strings.Ascii.
Open Scope string_scope.
Open Scope char_scope.

Require Import Coq.Lists.List.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.LLVMGen.Data.
Require Import Helix.Util.OptionSetoid.
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
         (globals: list (string * DSHType))
  : itree Event (list binary64 * evalContext) :=
    match globals with
    | [] => ret (data, [])
    | (_,gt)::gs =>
      match gt with
      | DSHnat => Sfail "Unsupported global type: nat"
      | DSHCType =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
         let '(x, data) := rotate Float64Zero data in
         ret (data, (DSHCTypeVal x)::σ)
      | DSHPtr n =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
         let (data,mb) := constMemBlock (MInt64asNT.to_nat n) data in
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
  let '(data, x) := constMemBlock (MInt64asNT.to_nat p.(i)) data in
  trigger (MemSet xindex x);;

  let σ := List.app σ [DSHPtrVal yindex p.(o); DSHPtrVal xindex p.(i)] in
  denoteDSHOperator σ p.(op);;
  bk <- trigger (MemLU "denote_FSHCOL" yindex);;
  lift_Derr (mem_to_list "Invalid output memory block" (MInt64asNT.to_nat p.(o)) bk).

Definition semantics_FSHCOL p data: itree E_mcfg (memory * list binary64) :=
  translate (@subevent _ E_mcfg _) (interp_Mem (denote_FSHCOL p data) memory_empty).

(* MOVE TO VELLVM *)
(* Definition normalize_types_blocks (env: list _) (bks: list (LLVMAst.block typ)) *)
  (* : list (LLVMAst.block DynamicTypes.dtyp) := *)
  (* List.map *)
    (* (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env)) bks. *)
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
    let L0_trace := INT.interp_intrinsics defs t in
    let L1_trace       := interp_global L0_trace g in
    let L2_trace       := interp_local  L1_trace l in
    let L3_trace       := M.interp_memory L2_trace m in
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
  fun (σ : evalContext) (mem_helix : MDSHCOLOnFloat64.memory) '(mem_llvm, x) =>
    let σ_len := List.length σ in
    σ_len ≡ 0 \/ (* empty env immediately allowed, as injection could not exists *)
    let '(ρ, g) := x in
    exists (ι: injection_Fin raw_id σ_len),
    forall (x: nat) v,
      nth_error σ x ≡ Some v ->
      match v with
      | DSHnatVal v   =>
        exists ptr_llvm,
        ( (* variable in local environment *)
          (alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
           alist_find _ (inj_f ι x) g ≡ None) \/
          (* variable in global environment *)
          (alist_find _ (inj_f ι x) ρ ≡ None /\
           alist_find _ (inj_f ι x) g ≡ Some (DVALUE_Addr ptr_llvm))) /\
        (* the block must exists *)
        (exists  bk_llvm,
            (get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm) /\
            (* And value at this pointer must match *)
            (exists v_llvm,  mem_lookup_llvm_at_i bk_llvm 0 1 v_llvm /\ v_llvm ≡ UVALUE_I64 (DynamicValues.Int64.repr (Int64.intval v))))
      | DSHCTypeVal v =>
        exists ptr_llvm,
        ( (* variable in local environment *)
          (alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
           alist_find _ (inj_f ι x) g ≡ None) \/
          (* variable in global environment *)
          (alist_find _ (inj_f ι x) ρ ≡ None /\
           alist_find _ (inj_f ι x) g ≡ Some (DVALUE_Addr ptr_llvm))) /\
        (* the block must exists *)
        (exists  bk_llvm,
            (get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm) /\
            (* And value at this pointer must match *)
            (exists v_llvm,  mem_lookup_llvm_at_i bk_llvm 0 1 v_llvm /\ v_llvm ≡ UVALUE_Double v))
      | DSHPtrVal ptr_helix ptr_size_helix =>
        forall bk_helix,
          memory_lookup mem_helix ptr_helix ≡ Some bk_helix ->
          exists ptr_llvm bk_llvm,
            alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
            get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm /\
            (fun bk_helix bk_llvm =>
               forall i, Int64.lt i ptr_size_helix ->
                    exists v_helix v_llvm,
                      mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v_helix /\
                      mem_lookup_llvm_at_i bk_llvm (MInt64asNT.to_nat i)
                                           (MInt64asNT.to_nat ptr_size_helix) v_llvm /\
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
(*     let L0_trace := INT.interp_intrinsics defs t in *)
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
    unfold interp_cfg_to_L3.
    subst; rewrite H.
    (* Show Proof. *)
    reflexivity.
  Qed.

  From Vellvm Require Import Util TypToDtyp Transformations.Traversal.
  Require Import State.

  (* Move to vellvm *)
  (* ************************************************** *)
  Lemma normalize_types_block_bid :
    forall (env : list (ident * typ)) (b: LLVMAst.block typ),
      blk_id (fmap (typ_to_dtyp env) b) ≡ blk_id b.
  Proof.
    intros env b.
    destruct b. reflexivity.
  Qed.

  Lemma normalize_types_block_term :
    forall (env : list (ident * typ)) (b: LLVMAst.block typ) (nextblock : block_id),
      snd (blk_term b) ≡ TERM_Br_1 nextblock ->
      snd (blk_term (fmap (typ_to_dtyp env) b)) ≡ TERM_Br_1 nextblock.
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

  Ltac hide_string :=
    match goal with
    | |- context [String ?x ?y] => remember (String x y)
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

  Lemma add_comment_preserves_num_blocks :
    forall l comments blocks,
      add_comment l comments ≡ blocks ->
      List.length l ≡ List.length blocks.
  Proof.
    induction l; intros comments blocks H.
    - inversion H; reflexivity.
    - simpl. inversion H. simpl.
      reflexivity.
  Qed.

  Lemma add_comment_singleton :
    forall l comments block,
      add_comment l comments ≡ [block] ->
      exists b, l ≡ [b].
  Proof.
    intros l comments block H.
    destruct l.
    - inv H.
    - destruct l.
      + exists b. reflexivity.
      + inv H.
  Qed.
  
  Lemma genIR_DSHAssign_to_genFSHAssign :
    forall src dst nextblock st st' b,
      genIR (DSHAssign src dst) nextblock st ≡ inr (st', (blk_id b, [b])) ->
      exists psrc nsrc pdst ndst b_orig comments i i0 i1 i2 i3 n n0,
        src ≡ (psrc, nsrc) /\
        dst ≡ (pdst, ndst) /\
        [b] ≡ add_comment [b_orig] comments /\
        resolve_PVar psrc st ≡ inr (i, (i0, n)) /\
        resolve_PVar pdst i  ≡ inr (i1, (i2, n0)) /\
        genFSHAssign n n0 i0 i2 nsrc ndst nextblock i1 ≡ inr (i3, (blk_id b, [b_orig])).
  Proof.
    intros src dst nextblock st st' b H.
    destruct src as (psrc, nsrc). exists psrc. exists nsrc.
    destruct dst as (pdst, ndst). exists pdst. exists ndst.

    inv H.
    destruct (resolve_PVar psrc st) eqn:Hr. inversion H1.
    destruct p. destruct p.
    destruct (resolve_PVar pdst i) eqn:Hr1. inversion H1.
    destruct p. destruct p.
    destruct (genFSHAssign i1 i4 i0 i3 nsrc ndst nextblock i2) eqn:Hassign. inversion H1.
    destruct p. destruct s.
    match goal with
    | H: context[add_comment _ ?ss] |- _ => remember ss
    end.

    inversion H1.
    apply add_comment_singleton in H3. destruct H3 as (b_orig & Hl).
    exists b_orig. exists l0.
    exists i. exists i0. exists i2. exists i3. exists i5. exists i1. exists i4.
    subst; intuition.
  Qed.

(*   Lemma compile_NExpr_correct : *)
(*     forall (nexp : NExpr) (e : exp typ) (c : code typ) (σ : evalContext) env (mem : MDSHCOLOnFloat64.memory) s s' mem_llvm ρ g, *)
(*       genNExpr nexp s ≡ inr (s', (e, c)) -> *)
(*       eutt _ *)
(*            (translate inr_ (interp_Mem (denoteNexp σ nexp) mem)) *)
(*            (translate inl_ (interp_cfg_to_L3 helix_intrinsics *)
(*                                              (D.denote_code ((map (λ '(id, i), (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i)) *)
(*                                                                   c))) *)
(*                                              g ρ mem_llvm)). *)

(* (map (λ '(id, i), (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i)) *)
(*                    src_nexpcode) *)

  (* TODO: Move to Vellvm *)
  Lemma denote_code_app :
    forall a b,
      eutt Logic.eq (D.denote_code (a ++ b)%list) (ITree.bind (D.denote_code a) (fun _ => D.denote_code b)).
  Proof.
    induction a; intros b.
    - cbn. rewrite bind_ret_l.
      reflexivity.
    - cbn. rewrite bind_bind. setoid_rewrite IHa.
      reflexivity.
  Qed.

  Lemma denote_code_cons :
        forall a l,
      eutt Logic.eq (D.denote_code (a::l)%list) (ITree.bind (D.denote_instr a) (fun _ => D.denote_code l)).
  Proof.
    cbn; reflexivity.
  Qed.

  (* Relations for expressions *)

  Definition int64_dvalue_rel (n : Int64.int) (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I64 i => Z.eq (Int64.intval n) (unsigned i)
    | _ => False
    end.


  Definition nat_dvalue_rel (n : nat) (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I64 i => Z.eq (Z.of_nat n) (unsigned i)
    | _ => False
    end.

  Definition int64_concrete_uvalue_rel (n : Int64.int) (uv : uvalue) : Prop :=
    match uvalue_to_dvalue uv with
    | inr dv => int64_dvalue_rel n dv
    | _ => False
    end.

  Definition nat_concrete_uvalue_rel (n : nat) (uv : uvalue) : Prop :=
    match uvalue_to_dvalue uv with
    | inr dv => nat_dvalue_rel n dv
    | _ => False
    end.

  (* top might be able to just be Some (DTYPE_I 64) *)
  Definition nexp_relation (env : list (ident * typ)) (e : exp typ) (n : Int64.int) (r : (memory * (local_env * (global_env * ())))) :=
    let '(mem_llvm, (ρ, (g, _))) := r in
    eutt (fun n '(_, (_, (_, uv))) => int64_concrete_uvalue_rel n uv)
         (ret n)
         (interp_cfg_to_L3 helix_intrinsics (translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64)) (fmap (typ_to_dtyp env) e))) g ρ mem_llvm).

  (* TODO: Need something about denoteNexp not failing *)
  Lemma denote_nexp_div :
    forall (σ : evalContext) (nexp1 nexp2 : NExpr),
      eutt Logic.eq (denoteNexp σ (NDiv nexp1 nexp2))
           (ITree.bind (denoteNexp σ nexp1)
                       (fun (n1 : Int64.int) => ITree.bind (denoteNexp σ nexp2)
                                                (fun (n2 : Int64.int) => denoteNexp σ (NDiv (NConst n1) (NConst n2))))).
  Proof.
  Admitted.

  Lemma denote_exp_nexp:
    forall nexp st i e c mem_llvm σ g ρ env,
      genNExpr nexp st ≡ inr (i, (e, c)) ->
      (* TODO: factor out this relation *)
      eutt (fun n '(m, (l, (g, uv))) => int64_concrete_uvalue_rel n uv)
           (translate inr_ (denoteNexp σ nexp))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics (translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64)) (fmap (typ_to_dtyp env) e))) g ρ mem_llvm)).
  Proof.
    induction nexp; intros st i e c mem_llvm σ g ρ env H.
    - cbn in H; repeat break_match_hyp; try solve [inversion H].
      + (* Int case *)
        cbn.
        unfold denoteNexp. cbn.
        break_match.
        * cbn.
          (* exception *) admit.
        * break_match.
          -- inversion H. cbn.
             (* Need something linking id to global_env / local_env *)
             destruct i1.
             ++ cbn. rewrite bind_trigger.
                repeat rewrite translate_vis.
                admit.
             ++ admit.
          -- cbn. (* exception *) admit.
          -- cbn. (* exception *) admit.
      + (* Pointer case *)
        admit.
    - cbn in H; repeat break_match_hyp; inversion H; cbn.
      admit.
  Admitted.
    

  (* Probably need to know something about σ and mem_llvm,
     like memory_invariant... *)
  Lemma denoteNexp_genNExpr :
    forall (nexp : NExpr) (st st' : IRState) (nexp_r : exp typ) (nexp_code : code typ) (env : list (ident * typ)) (σ : evalContext) g ρ mem_llvm,
      genNExpr nexp st  ≡ inr (st', (nexp_r, nexp_code)) ->
      eutt (nexp_relation env nexp_r)
           (translate inr_ (denoteNexp σ nexp))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics
                             (D.denote_code (map
                                               (λ '(id, i),
                                                (id, convert_typ env i))
                                               nexp_code)) g ρ mem_llvm)).
  Proof.
    induction nexp; intros st st' nexp_r nexp_code env σ g ρ mem_llvm H.
    - (* NVar *)
      cbn in H.
      repeat break_match_hyp; subst; inversion H; simpl.
      cbn in Heqs.
      admit.
      admit.

      (*
        destruct t.
        destruct (Z.eq_dec sz 64).
        inversion H. reflexivity.
        inversion H.
        destruct t.
        *
      + inversion H.
       *)
    - (* NConst *)
      cbn in H; inversion H; cbn.
      rewrite interp_cfg_to_L3_ret.
      repeat rewrite translate_ret.
      apply eqit_Ret.
      cbn.
      rewrite translate_ret.
      rewrite interp_cfg_to_L3_ret.
      apply eqit_Ret.
      cbn.
      rewrite DynamicValues.Int64.unsigned_repr.
      apply Z.eq_refl.
      admit. (* overflow *)
    - cbn in H.
      repeat break_match_hyp; inversion H.

      repeat rewrite map_app.
      repeat setoid_rewrite denote_code_app.

      rewrite denote_nexp_div.
      pose proof IHnexp1 _ _ _ _ env σ g ρ mem_llvm Heqs.
      rewrite interp_cfg_to_L3_bind.
      repeat setoid_rewrite translate_bind.
      eapply eutt_clo_bind; eauto.

      intros u1 u2 H4.
      repeat break_match.
      rewrite interp_cfg_to_L3_bind; rewrite translate_bind.
      eapply eutt_clo_bind; eauto.

      intros u0 u3 H5.
      repeat break_match.

      (* We executed code that generated the values for the
      expressions for the binary operations... Now we need to denote
      the expressions themselves. *)
      (* simplify left side to ret *)
      cbn.

      repeat rewrite translate_bind.      
      repeat rewrite interp_cfg_to_L3_bind.
      repeat rewrite bind_bind.

      (* genNExpr nexp1 st ≡ inr (i, (e, c)) *)
      (* I need something relating `denote_exp e` and `denoteNexp nexp1`... *)
  Admitted.

  (* TODO: awful AWFUL name. Need to figure out which of these we need *)
  Definition nexp_relation_mem (σ : evalContext) (helix_res : MDSHCOLOnFloat64.memory * Int64.int) (llvm_res : TopLevelEnv.memory * (local_env * (global_env * ()))) : Prop
    :=
      let '(mem_helix, n) := helix_res in
      let '(mem_llvm, (ρ, (g, _))) := llvm_res in
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)).

  Lemma interp_denoteNexp_genNExpr :
    forall (nexp : NExpr) (st st' : IRState) (nexp_r : exp typ) (nexp_code : code typ) (env : list (ident * typ)) (σ : evalContext) g ρ mem_llvm memory,
      genNExpr nexp st  ≡ inr (st', (nexp_r, nexp_code)) ->
      eutt (nexp_relation_mem σ)
           (translate inr_ (interp_state (case_ Mem_handler MDSHCOLOnFloat64.pure_state) (denoteNexp σ nexp) memory))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics
                                             (D.denote_code (map
                                                               (λ '(id, i),
                                                                (id, convert_typ env i))
                                                               nexp_code)) g ρ mem_llvm)).
  Proof.
  Admitted.

(* TODO: only handle cases where there are no exceptions? *)
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
                                    (D.denote_bks (fmap (typ_to_dtyp env) bks) bid_in)
                                    g ρ mem_llvm)).
Proof.
  induction op; intros; rename H1 into HCompile.
  - inv HCompile.
    eutt_hide_right; cbn.
    unfold interp_Mem; simpl denoteDSHOperator.
    rewrite interp_state_ret, translate_ret.
    subst i. 
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
    subst.
    eutt_hide_left.
    unfold fmap; simpl Fmap_list'.
    (* Rewrite denote_bks to denote_block *)
    rewrite denote_bks_singleton; eauto using normalize_types_block_term.

    (* Work with denote_block *)
    (* I need to know something about b... *)
    pose proof genIR_DSHAssign_to_genFSHAssign src dst nextblock st HCompile.
    destruct H1 as (psrc & nsrc & pdst & ndst & b_orig & comments & ist & i0 & ist1 & i1 & ist2 & n & n0 & Hsrc & Hdst & Hb & Hr & Hr' & Hfsh).

    cbn in Hb. inversion Hb.
    cbn.

    (* Now I need to know something about b_orig... *)
    (* I know it's generated from genFSHassign, though... *)
    cbn in Hfsh.

    (* Checkpoint *)
    inversion Hfsh.
    destruct (genNExpr nsrc
                       {|
                         block_count := S (block_count ist1);
                         local_count := S (S (S (local_count ist1)));
                         void_count := S (S (void_count ist1));
                         vars := vars ist1 |}) as [|(s', (src_nexpr, src_nexpcode))] eqn:Hnexp_src. inversion H3.
    destruct (genNExpr ndst s') as [|(s'', (dst_nexpr, dst_nexpcode))] eqn:Hnexp_dst. inversion H3.
    inversion H3.
    cbn.
    (*
    match goal with
    | |- context[D.denote_code (map _ (src_nexpcode ++ dst_nexpcode ++ ?x))] => remember x as assigncode
    end.

    (* start working on right side again *)
    subst i. cbn.
    subst src dst.

    unfold denotePexp, evalPExpr. cbn.
    destruct psrc, pdst.
    destruct (nth_error σ v) eqn:Herr.
    + destruct d.
      * (* exceptions *) admit.
      (* Might be able to do this with the bisimulation relation,
         which might need to be strengthened *)
      * (* exceptions *) admit.
      * cbn. rewrite bind_ret_l.
        destruct (nth_error σ v0) eqn:Herr'.
        -- destruct d.
           ++ (* exceptions *) admit.
           ++ (* exceptions *) admit.
           ++ cbn. rewrite bind_ret_l.
              repeat setoid_rewrite bind_trigger.
              unfold interp_Mem.
              rewrite interp_state_vis; cbn.
              destruct (memory_lookup_err "Error looking up 'x' in DSHAssign" mem a) eqn:Hmem_x.
              (* exceptions *) admit.

              cbn. rewrite bind_ret_l.

              rewrite interp_state_vis; cbn.
              destruct (memory_lookup_err "Error looking up 'y' in DSHAssign" mem a0) eqn:Hmem_y.
              (* exceptions *) admit.

              cbn; rewrite bind_ret_l; cbn.
              repeat rewrite tau_eutt.

              (* Unfold denote_code and break it apart. *)
              do 2 rewrite map_app.
              do 2 setoid_rewrite denote_code_app.
              do 2 setoid_rewrite bind_bind.

              (* Need to relate denoteNexp and denote_code of genNexpr *)
              repeat setoid_rewrite interp_cfg_to_L3_bind.
              repeat setoid_rewrite interp_state_bind.
              repeat setoid_rewrite translate_bind.

              eapply eutt_clo_bind.
              eapply interp_denoteNexp_genNExpr; eauto.

              intros u1 u2 H1.
              destruct u1, u2, p, p; cbn.
              rewrite interp_cfg_to_L3_bind.
              rewrite translate_bind.

              eapply eutt_clo_bind.
              eapply interp_denoteNexp_genNExpr; eauto.

              intros u1 u2 H7.
              destruct u1, u2, p, p; cbn.

              destruct (mem_lookup_err "Error looking up 'v' in DSHAssign" (MInt64asNT.to_nat i) m) eqn:Hmemlookup.
              (* exception *) admit.

              cbn.
              rewrite interp_state_ret.
              rewrite translate_ret.
              rewrite bind_ret_l.

              rewrite interp_state_trigger.
              cbn.
              rewrite bind_ret_l.
              rewrite translate_tau.
              rewrite tau_eutt.
              rewrite translate_ret.

              rewrite interp_cfg_to_L3_bind.
              rewrite translate_bind.
              cbn.

              subst assigncode.
              cbn.

              repeat setoid_rewrite translate_bind.
              repeat setoid_rewrite interp_cfg_to_L3_bind.
              repeat setoid_rewrite bind_bind.

              unfold D.lookup_id.
              destruct i0 eqn:Hi0.
              ** (* Global id *)
                cbn.
                repeat setoid_rewrite translate_bind.
                rewrite interp_cfg_to_L3_bind.
                repeat setoid_rewrite translate_vis.
                repeat setoid_rewrite bind_bind.
                repeat setoid_rewrite translate_ret.
                admit.
              ** (* Local id *)
                admit.
        -- (* exceptions *) admit. 
    + (* Need to handle exceptions *)
      admit.
     *)
    (* Focus 3. *)
    (* cbn. *)
    (* rewrite bind_ret_l. *)
    (* destruct (nth_error σ v0) eqn:Herr'. *)
    (* destruct d. *)

    (* Focus 3. *)
    
    (* (* Lookup failure *) *)
    (* Focus 2. cbn. *)
    (* unfold interp_Mem. *)
    (* setoid_rewrite interp_state_bind. *)
    (* unfold Exception.throw. *)
    (* rewrite interp_state_vis. cbn. *)
    (* unfold MDSHCOLOnFloat64.pure_state. *)
    (* rewrite bind_vis. rewrite bind_vis. *)
    (* unfold resum. unfold ReSum_inl. *)
    (* unfold resum. unfold ReSum_id. *)
    (* unfold id_. unfold inl_. *)

    (* rewrite translate_vis. *)
    (* unfold resum. unfold inr_. *)
    (* Check VisF. *)
    (* simpl. *)
    (* unfold interp_state. unfold interp. *)
    (* interp. *)
    (* unfold Exception.Throw. cb *)

    (* inversion H3. cbn. *)
    (* simpl. *)
    (* cbn. *)

    (* subst i. *)
    (* unfold interp_Mem; cbn. *)
    (* destruct src, dst. *)
    (* simpl in HCompile. *)
    (* repeat break_match_hyp; try inl_inr. *)
    (* inv Heqs; inv HCompile. *)
    (* unfold denotePexp, evalPExpr, lift_Serr. *)
    (* subst. *)
    (* unfold interp_Mem. (* cbn *) *)
    (* (* match goal with *) *)
    (* (* | |- context[add_comment _ ?ss] => generalize ss; intros ls *) *)
    (* (* end. *) *)
    (* (* match goal with *) *)
    (* (* | |- context[add_comment _ ?ss] => generalize ss; intros ls1 *) *)
    (* (* end. *) *)

    (* (* subst. eutt_hide_right. *) *)
    (* (* cbn. *) *)
    (* (* unfold interp_Mem. *) *)
    (* (* rewrite interp_state_bind. *) *)
    (* (* unfold denotePexp, evalPExpr. *) *)
    (* (* cbn. *) *)
    (* (* repeat setoid_rewrite interp_state_bind. *) *)
    (* (* rewrite denote_bks_singleton. *) *)
    (* (* destruct src, dst. *) *)
    (* (* simpl in HCompile. *) *)
    (* (* repeat break_match_hyp; try inl_inr. *) *)
    (* (* inv Heqs; inv HCompile. *) *)
    (* (* match goal with *) *)
    (* (* | |- context[add_comment _ ?ss] => generalize ss; intros ls *) *)
    (* (* end. *) *)
    (* (* unfold interp_Mem. *) *)
    (* (* simpl denoteDSHOperator. *) *)
    (* (* rewrite interp_state_bind, translate_bind. *) *)
    (* (* match goal with *) *)
    (* (*   |- eutt _ ?t _ => remember t *) *)
    (* (* end. *) *)

    (* (* Need a lemma to invert Heqs2. *)
    (*    Should allow us to know that the list of blocks is a singleton in this case. *)
    (*    Need then probably a lemma to reduce proofs about `D.denote_bks [x]` to something like the denotation of x, *)
    (*    avoiding having to worry about iter. *)
    (*  *) *)
    (* (* cbn; rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_ret, bind_ret_l. *) *)

    (* repeat match goal with *)
    (* | |- context [ String ?x ?y ] => remember (String x y) *)
    (* end. *)

    (* make_append_str in H6. *)
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
  Definition alloc_global (c_name:string) (c_typ:typ) (m:M.memory) (ms:M.mem_stack) :=
    (* TODO: not sure about this [typ] to [dtyp] conversion *)
    let d_typ := typ_to_dtyp [] c_typ in
    let new_block := M.make_empty_block d_typ in
    let key := M.next_logical_key m in
    let new_mem := M.add_logical key new_block m in
    match ms with
    | [] => inl "No stack frame for alloca."%string
    | frame :: stack_rest =>
      let new_stack := (key :: frame) :: stack_rest in
      (*  global_env = alist raw_id dvalue *)
      let a := DVALUE_Addr (key, 0%Z) in
      ret (new_mem, new_stack, (Name c_name, a), a)
    end.

  (* mimics [Store] handler *)
  Definition init_global (m:M.memory) (ms:M.mem_stack) (a: dvalue) (v:dvalue)
    : err (M.memory * M.mem_stack) :=
    match a with
    | DVALUE_Addr (key, i) =>
      match M.lookup_logical key m with
      | Some (M.LBlock sz bytes cid) =>
        let bytes' := M.add_all_index (M.serialize_dvalue v) i bytes in
        let block' := M.LBlock sz bytes' cid in
        ret (M.add_logical key block' m, ms)
      | None => inl "stored to unallocated address"%string
      end
    | _ => inl ("Store got non-address dvalue: " ++ (to_string a))%string
    end.

End LLVM_Memory_Init.

(* Scalar *)
Definition eval_const_double_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Double, EXP_Double v) => ret (DVALUE_Double v)
  | (_, c_typ) => inl ("Type double expected: " ++ (to_string c_typ))%string
  end.

(* Array *)
Definition eval_const_arr_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Array _ TYPE_Double, EXP_Array a) =>
    da <- ListSetoid.monadic_fold_left
           (fun ds d => dd <- eval_const_double_exp d ;; ret (dd::ds))
           [] a ;;
    ret (DVALUE_Array da)
  | (_, c_typ) => inl ("Array of doubles expected: " ++ (to_string c_typ))%string
  end.

Definition eval_const_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Array _ TYPE_Double, EXP_Array a) => eval_const_arr_exp typed_expr
  | (TYPE_Double, EXP_Double v) =>  eval_const_double_exp typed_expr
  | (_, c_typ) => inl ("Unsupported constant expression type: " ++ (to_string c_typ))%string
  end.

Definition init_one_global
           (mem_state: (memory * local_env)%type)
           (g:toplevel_entity typ (list (LLVMAst.block typ)))
  := match g with
     | TLE_Global (mk_global (Name c_name) c_typ
                             true
                             (Some c_initiaizer)
                             (Some LINKAGE_Internal)
                             None None None true None
                             false None None) =>
       let '((m,ms), lenv) := mem_state in
       '(m,ms,g,a) <- alloc_global c_name c_typ m ms ;;
       mms <- (eval_const_exp >=> init_global m ms a) (c_typ, c_initiaizer)
       ;;
       ret ((mms,lenv), g)
     | _ => inl "Usupported global initialization"%string
     end.

(* TODO: move to Util *)
Definition assoc_right_to_left {A B C:Type}: (A*(B*C)) -> ((A*B)*C)
  := fun x => let '(a,(b,c)):=x in ((a,b),c).

(* TODO: move to Util *)
Definition assoc_left_to_right {A B C:Type}: ((A*B)*C) -> (A*(B*C))
  := fun x => let '((a,b),c) := x in (a,(b,c)).

Definition init_llvm_memory
           (p: FSHCOLProgram)
           (data: list binary64) : err LLVM_memory_state_partial
  :=
    '(data,ginit) <- initIRGlobals data p.(globals) ;;

    let y := Anon 1%Z in
    let ytyp := getIRType (DSHPtr p.(o)) in
    let x := Anon 0%Z in
    let xtyp := getIRType (DSHPtr p.(i)) in

    let xyinit := global_YX p.(i) p.(o) data x xtyp y ytyp in

    (* Will return in order [globals ++ xy] *)
    let '(ms,(le,ge)) := llvm_empty_memory_state_partial in
    res <- init_with_data init_one_global no_chk (ms,le) (ginit ++ xyinit)%list ;;
    ret (assoc_left_to_right res).

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
  apply init_with_data_len.
Qed.

(* Maps indices from [σ] to [raw_id].
   Currently [σ := [globals;Y;X]]
   Where globals mapped by name, while [X-> Anon 0] and [Y->Anon 1]
*)
Definition memory_invariant_map (globals : list (string * DSHType)): nat -> raw_id
  := fun j =>
       let l := List.length globals in
       if Nat.eqb j l then Anon 0%Z (* X *)
       else if Nat.eqb j (S l) then Anon 1%Z (* Y *)
            else
              match nth_error globals j with
              | None => Anon 0%Z (* default value *)
              | Some (name,_) => Name name
              end.

Lemma memory_invariant_map_injectivity (globals : list (string * DSHType)):
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
  ∀ (a : string * DSHType) (globals : list (string * DSHType))
    (data : list binary64) (res : list binary64 *
                                  list (toplevel_entity typ (list (LLVMAst.block typ)))),
    initIRGlobals data (a :: globals) ≡ inr res ->
    forall (j : nat) (n : string) (v : DSHType),
      (nth_error globals j ≡ Some (n, v) /\ n ≡ fst a) → False.
Proof.
  intros a globals data res H j n v C.
  unfold initIRGlobals, global_uniq_chk in H.
  cbn in H.
  repeat break_match_hyp; try inl_inr.
  unfold assert_false_to_err in Heqs.
  repeat break_match_hyp; try inl_inr.
  inl_inr_inv.
  subst.
  assert(globals_name_present (fst a) globals ≡ true).
  {
    clear -C.
    apply nth_to_globals_name_present.
    exists (n,v).
    exists j.
    apply C.
  }
  congruence.
Qed.

(* If [initIRGlobals] suceeds, the names of variables in [globals] were unique *)
Lemma initIRGlobals_names_unique {globals data res}:
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

(* Note: this could not be proben for arbitrary [chk] function,
   so we prove this only for [no_chk] *)
Lemma init_with_data_app
      {A: Type} (* input values *)
      {B: Type} (* output values we collect *)
      {C: Type} (* data *)
      (f: C -> A -> err (C*B))
      (c c': C) (* initial data *)
      (l0 l1: list A)
      (b: list B)
  :
    init_with_data f no_chk c (l0++l1) ≡ inr (c',b) ->
    ∃ c1 b1 b2,
      (init_with_data f no_chk c l0 ≡ inr (c1,b1) /\
       init_with_data f no_chk c1 l1 ≡ inr (c',b2) /\
       b ≡ (b1 ++ b2)%list).
Proof.
  revert l0 l1 c c' b.
  induction l0; intros.
  -
    cbn in H.
    repeat eexists.
    eauto.
  -
    cbn in H.
    repeat break_match_hyp; try inl_inr.
    inl_inr_inv.
    subst.
    apply IHl0 in Heqs0; clear IHl0.
    destruct Heqs0 as (c1 & b1 & b2 & H1 & H2 & E).
    repeat eexists; cbn.
    +
      rewrite Heqs.
      rewrite H1.
      eauto.
    +
      eauto.
    +
      cbn.
      f_equiv.
      auto.
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
    rewrite Heqs.
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


(* TODO: brute-force proof is slow. Could be optimized *)
Fact init_one_global_empty_local
      (a0 : toplevel_entity typ (list (LLVMAst.block typ)))
      (m0 : M.memory_stack)
      (p : M.memory * M.mem_stack)
      (l0 : local_env)
      (p1 : raw_id * dvalue):
  init_one_global (m0, [ ]) a0 ≡ inr (p, l0, p1) → l0 ≡ [ ].
Proof.
  intros H.
  unfold init_one_global in H.
  repeat (break_match_hyp; try inl_inr).
  cbn in *.
  subst.
  repeat (break_match_hyp; try inl_inr).
  inl_inr_inv.
  reflexivity.
  inl_inr_inv.
  reflexivity.
Qed.

Fact init_with_data_init_one_global_empty_local
     m g m' l g':
  init_with_data init_one_global no_chk (m, [ ]) g ≡ inr (m', l, g') -> l ≡ [].
Proof.
  revert g' l m m'.
  induction g; intros.
  -
    cbn in H.
    inv H.
    reflexivity.
  -
    cbn in H.
    break_match_hyp; try inl_inr.
    break_let; subst.
    break_match_hyp; try inl_inr.
    break_let; subst.
    inl_inr_inv.
    destruct p2.
    tuple_inversion.
    destruct p0.
    destruct p.

    unfold init_one_global in Heqs.
    repeat break_match_hyp; try inl_inr.
    subst.
    inv Heqs.
    break_match_hyp; try inl_inr.
    repeat break_let; subst.
    repeat break_match_hyp; try inl_inr.
    +
      repeat inl_inr_inv.
      subst.
      eapply IHg.
      eauto.
    +
      repeat inl_inr_inv.
      subst.
      eapply IHg.
      eauto.
Qed.

Lemma alist_find_nth_error_list_uniq
      (g : global_env)
      (x : nat)
      (n: raw_id)
      (v : dvalue)
      (U: list_uniq fst g):
  nth_error g x ≡ Some (n, v) →
  alist_find AstLib.eq_dec_raw_id n g ≡ Some v.
Proof.
  revert U.
  revert x v n.
  induction g; intros.
  -
    rewrite nth_error_nil in H.
    some_none.
  -
    cbn.
    break_let.
    break_if.
    +
      unfold RelDec.rel_dec, AstLib.eq_dec_raw_id in Heqb.
      cbn in Heqb.
      break_match; [| inversion Heqb].
      subst.
      destruct x.
      *
        cbn in H.
        some_inv.
        reflexivity.
      *
        cbn in H.
        clear - U H.
        exfalso.
        apply list_uniq_cons in U.
        destruct U.
        contradict H1.
        eexists.
        eexists.
        eauto.
    +
      destruct x.
      *
        clear IHg.
        cbn in *.
        some_inv.
        subst.
        clear - Heqb.
        unfold RelDec.rel_dec, AstLib.eq_dec_raw_id in Heqb.
        cbn in Heqb.
        break_if.
        inversion Heqb.
        contradict n0.
        reflexivity.
      *
        cbn in H.
        eapply IHg.
        eapply list_uniq_de_cons; eauto.
        eapply H.
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
  (*

  This partial proof was further broken after
  eliminating [FSHValType] and replacing it with [DSHType].
  It needs to be repaired


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
  rename Heqp2 into HCX, m2 into xdata.
  rename Heqs0 into HFSHG, l2 into fdata', e into σ.
  rename Heqs into HIRG, l0 into ldata', l1 into gdecls.
  remember (global_YX i o ldata' (Anon 0%Z) (TYPE_Array (Int64.intval i) TYPE_Double)
                      (Anon 1%Z) (TYPE_Array (Int64.intval o) TYPE_Double)) as xydecls eqn:HXY.
  rename l3 into fdata''.

  inv LI.
  unfold assoc_left_to_right in H0.
  destruct p1.
  destruct p.
  tuple_inversion.

  pose proof (init_with_data_app _ _ _ _ HFSHG)
    as ([m1 l1] & g1 & g2 & HG & HFXY & E).

  (* No local variables initialize in init stage *)
  assert(L1: l1 ≡ []) by eapply init_with_data_init_one_global_empty_local, HG; subst l1.
  assert(L2: l ≡ []) by eapply init_with_data_init_one_global_empty_local, HFXY; subst l.

  cbn in *.

  assert(∀ x y : nat,
            x < Datatypes.length
                  (σ ++
                     [DSHPtrVal (S (Datatypes.length globals)) o;
                      DSHPtrVal (Datatypes.length globals) i])
            ∧ y <
              Datatypes.length
                (σ ++
                   [DSHPtrVal (S (Datatypes.length globals)) o;
                    DSHPtrVal (Datatypes.length globals) i])
            → memory_invariant_map globals x ≡ memory_invariant_map globals y → x ≡ y) as INJ.
  {
    (* Injectivity proof *)
    rewrite app_length.
    erewrite <- initFSHGlobals_globals_sigma_len_eq with (globals0:=globals).
    2: eauto.
    simpl.
    apply memory_invariant_map_injectivity.
    eapply initIRGlobals_names_unique.
    eauto.
  }
  unshelve eexists.
  exists (memory_invariant_map globals).
  apply INJ.

  intros x v Hn.
  break_match.
  -
    (* [DSHnatVal] must end up in globals *)
    (* but currently nat constants are not implemented so we
       shortcut this branch *)
    exfalso.
    clear - Hn Heqs1.
    rename Heqs1 into F.

    apply ListUtil.nth_app in Hn.
    destruct Hn as [[Hn Hx] | [Hn Hx]].
    2:{
      remember (x - Datatypes.length σ)%nat as k.
      destruct k; inv Hn.
      destruct k; inv H0.
      rewrite Util.nth_error_nil in H1.
      inv H1.
    }
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
      break_let; subst.
      break_match_hyp; [inl_inr|].
      break_let; subst.
      inv F.
      destruct a.
      destruct f; cbn in *.
      *
        inl_inr.
      *
        repeat break_let; subst.
        symmetry in Heqs.
        inl_inr_inv.
        subst.
        destruct x.
        cbn.
        intros C. inv C.
        cbn.
        eapply IHglobals, Heqs0.
      *
        repeat break_let; subst.
        symmetry in Heqs.
        inl_inr_inv.
        subst.
        destruct x.
        cbn.
        intros C. inv C.
        cbn.
        eapply IHglobals, Heqs0.
  -
    (* [DSHCTypeVal] must end up in globals as  a pointer *)

    apply ListUtil.nth_app in Hn.
    destruct Hn as [[Hn Hx] | [Hn Hx]].
    2:{
      (* X,Y are pointers, not CType, so [Hn] is [False] *)
      remember (x - Datatypes.length σ)%nat as k.
      destruct k; inv Hn.
      destruct k; inv H0.
      rewrite Util.nth_error_nil in H1.
      inv H1.
    }
    subst v.
    clear HFXY.

    assert(List.length gdecls ≡ List.length g1) as GL
        by eapply init_with_data_len, HG.

    assert(List.length globals ≡ List.length gdecls) as GG
        by eapply init_with_data_len, HIRG.

    rename Heqs1 into F.
    pose proof (initFSHGlobals_globals_sigma_len_eq globals F) as GSL.

    assert(exists gname gtype, nth_error globals x ≡ Some (gname, gtype)).
    {
      assert(L: x < Datatypes.length globals).
      {
        rewrite GSL.
        apply Hx.
      }
      pose proof (nth_error_succeeds globals L) as H.
      destruct H as ([gname gtype] & H).
      exists gname.
      exists gtype.
      apply H.
    }
    destruct H as (gname & gtype & NG).

    assert(exists gd,
              nth_error gdecls x ≡ Some (TLE_Global gd) /\
              g_exp gd ≡ Some (EXP_Double a) /\
              g_ident gd ≡ Name gname
          ) as (gd & XGD & VGD & NGD).
    {
      rewrite <- GSL, GG in Hx.
      clear - F HIRG Hn Hx NG F.
      unfold initFSHGlobals in *.
      pose proof (nth_error_succeeds gdecls Hx) as H.
      destruct H as (te & H).

      (* now prove [te] is [TLE_Global gd] *)
      revert F HIRG Hn NG Hx H.
      revert m0 fdata' σ data ldata' gdecls x.
      generalize helix_empty_memory as m0.
      induction globals; intros.
      -
        rewrite nth_error_nil in NG.
        some_none.
      -
        cbn in F.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.
        destruct p0.

        destruct gdecls; [rewrite nth_error_nil in H; inversion H|].

        cbn in HIRG.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.

        unfold initOneIRGlobal in Heqs2.
        repeat break_match_hyp; try inl_inr.
        +
          inl_inr_inv.
          subst.
          cbn in *.
          destruct x.
          *
            cbn in *.
            repeat some_inv.
            subst.
            break_let.
            tuple_inversion.
            inl_inr_inv.
            subst.
            eexists.
            eauto.
          *
            cbn in *.
            repeat some_inv.
            subst.
            break_let.
            tuple_inversion.
            inl_inr_inv.
            subst.
            eapply IHglobals; eauto.
            lia.
        +
          (* Array *)
          inl_inr_inv.
          subst.
          cbn in *.
          destruct x.
          *
            cbn in *.
            repeat some_inv.
            subst.
            break_let.
            inl_inr_inv.
          *
            cbn in *.
            break_let.
            inv Heqs.
            subst.
            eapply IHglobals; eauto.
            assert (LL: l0≡l1).
            {
              clear - Heqp Heqp0.
              unfold constMemBlock in Heqp.
              unfold constArray in Heqp0.
              break_let.
              tuple_inversion.
              tuple_inversion.
              reflexivity.
            }
            rewrite LL.
            eapply Heqs3.
            lia.
    }

    assert(exists ptr_llvm, nth_error g x ≡ Some (Name gname, (DVALUE_Addr ptr_llvm))).
    {
      assert (x < Datatypes.length g1) as L.
      {
        rewrite <- GL, <- GG, GSL.
        apply Hx.
      }
      subst g.
      rewrite app_nth_error1 in * by apply L.
      pose proof (nth_error_succeeds g1 L) as H.
      destruct H as ([did dv] & H).
      clear - HG H NGD XGD.
      revert x HG H XGD.
      generalize M.empty_memory_stack as m0.
      revert g1 did dv.
      induction gdecls; intros.
      -
        cbn in *.
        inv HG.
        rewrite nth_error_nil in H.
        some_none.
      -
        cbn in HG.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.
        unfold init_one_global in Heqs.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        cbn in *.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.
        +
          (* Double *)
          destruct x.
          *
            clear IHgdecls.
            cbn in *.
            some_inv.
            destruct p1.
            some_inv.
            unfold alloc_global in Heqs1.
            repeat break_match_hyp; try inl_inr.
            repeat inl_inr_inv.
            exists (M.next_logical_key m, 0%Z).
            subst.
            f_equiv.
            f_equiv.
            apply NGD.
          *
            cbn.
            eapply IHgdecls; eauto.
        +
          (* Array *)
          destruct x.
          *
            clear IHgdecls.
            cbn in *.
            some_inv.
            destruct p1.
            some_inv.
            unfold alloc_global in Heqs1.
            repeat break_match_hyp; try inl_inr.
            repeat inl_inr_inv.
            exists (M.next_logical_key m, 0%Z).
            subst.
            f_equiv.
            f_equiv.
            cbn in *.
            tuple_inversion.
            apply NGD.
            tuple_inversion.
            eauto.
          *
            cbn.
            destruct p0.
            inl_inr_inv.
            subst.
            eapply IHgdecls; eauto.
    }

    destruct H as (ptr_llvm & NGDECL).
    exists ptr_llvm.

    split.
    right.
    split; [trivial|cbn].
    +
      (* Deal with X,Y first *)
      unfold memory_invariant_map.
      repeat break_if; bool_to_nat; try lia.

      (* X,Y eliminated, [x] somewhere in globals *)
      break_match_goal; try some_none.
      some_inv. subst p.

      (* unify lengths *)
      remember (Datatypes.length σ) as l eqn:SL; symmetry in SL.
      clear Heqb Heqb0.
      rename m0 into fm0.

      (* we know, [gname] is in [gdecls] and not in [xydecls] *)
      clear HCX HCY xdata ydata hdata.

      assert(list_uniq fst g) as GU.
      {
        pose proof (initIRGlobals_names_unique HIRG) as GLU.
        admit.
      }

      eapply alist_find_nth_error_list_uniq; eauto.
    +
      eexists.
      split.
      *
        admit.
      *
        eexists.
        clear - NGDECL HFSHG Hn.
        admit.
  -
    (* [DSHPtrVal] must end up in memory *)
    intros bk_helix HMH.
    eexists.
    eexists.
    admit.
   *)
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
