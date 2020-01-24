Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.LLVMGen.Data.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Tactics.StructTactics.

Require Import ExtLib.Structures.Monads.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.TopLevelRefinements.
Require Import Vellvm.LLVMEvents.

Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Basics.Basics.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.

Definition model_llvm' := model_to_L3 helix_intrinsics.

Definition E: Type -> Type := (StaticFailE +' DynamicFailE) +' (IO.CallE +' IO.ExternalCallE +' IO.PickE +' UBE +' DebugE +' FailureE).

Definition semantics_llvm_mcfg p: itree E _ := translate (@subevent _ E _) (model_llvm' p).

(* MOVE TO VELLVM *)
Definition lift_sem_to_mcfg {E X} `{FailureE -< E}
           (sem: (CFG.mcfg DynamicTypes.dtyp) -> itree E X):
  list (toplevel_entity typ (list (LLVMAst.block typ))) -> itree E X :=
  fun prog =>
    let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in

    match CFG.mcfg_of_modul _ scfg with
    | Some ucfg =>
      let mcfg := TopLevelEnv.normalize_types ucfg in

      sem mcfg

    | None => raise "Ill-formed program: mcfg_of_modul failed."
    end.

Definition semantics_llvm (prog: list (toplevel_entity typ (list (LLVMAst.block typ)))) :=
  lift_sem_to_mcfg semantics_llvm_mcfg prog.

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

Definition mem_to_list (msg:string) (n:nat) (mb:mem_block) : err (list binary64) :=
  ListSetoid.monadic_Lbuild n (fun j _ => trywith msg (mem_lookup j mb)).

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

Definition semantics_FSHCOL p data: itree E (memory * list binary64) :=
  translate (@subevent _ E _) (interp_Mem (denote_FSHCOL p data) memory_empty).

(* MOVE TO VELLVM *)
Definition normalize_types_blocks (env: list _) (bks: list (LLVMAst.block typ))
  : list (LLVMAst.block DynamicTypes.dtyp) :=
  List.map
    (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env)) bks.
Import IO TopLevelEnv Global Local.

(* TO FIX *)
Definition interp_to_L3': forall (R: Type), IS.intrinsic_definitions -> itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) R ->
                        (FMapAList.alist raw_id dvalue) ->
                        (FMapAList.alist raw_id res_L0) ->
                        M.memory_stack ->
itree (CallE +' PickE +' UBE +' DebugE +' FailureE)
              (M.memory_stack * (FMapAList.alist raw_id res_L0 * (FMapAList.alist raw_id dvalue * R))) :=
  fun R _ _ a b c => raise "".

(* memory and block or value *)
Open Scope type_scope.

Definition LLVM_state_cfg := M.memory_stack * (FMapAList.alist raw_id res_L0 * (FMapAList.alist raw_id dvalue * (block_id + res_L0))) .

Definition LLVM_state_mcfg := M.memory_stack * ((FMapAList.alist raw_id res_L0) * @Stack.stack (FMapAList.alist raw_id res_L0) * (FMapAList.alist raw_id dvalue * (block_id + res_L0))).

(** Type of bisimilation relation between between DSHCOL and LLVM states.
    This relation could be used for fragments of CFG [cfg].
 *)
Definition Type_R_partial: Type := evalContext
           → MDSHCOLOnFloat64.memory * ()
             → LLVM_state_cfg → Prop.

Definition injection_Fin {A} (ι: nat -> A) k: Prop :=
  forall x y,
    x < k /\ y < k ->
    ι x ≡ ι y ->
    x ≡ y.

Definition get_logical_block (mem: M.memory) (ptr: A.addr): option M.logical_block :=
  let '(b,a) := ptr in
  M.lookup_logical b mem.

Import DynamicTypes.

Definition bisim_mem_lookup_llvm_at_i (bk_llvm: M.logical_block) i ptr_size_helix v_llvm :=
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

Definition bisim_partial: Type_R_partial :=
  fun σ '(mem_helix, _) '(mem_llvm, x) =>
    let '(ρ, (g, bid_or_v)) := x in
    exists (ι: nat -> raw_id),
      injection_Fin ι (length σ) /\
      forall (x: nat) v,
        nth_error σ x ≡ Some v ->
        match v with
        | DSHnatVal v   =>
          FMapAList.alist_find _ (ι x) ρ ≡ Some (UVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat v)))
        | DSHCTypeVal v =>
          FMapAList.alist_find _ (ι x) ρ ≡ Some (UVALUE_Double v)
        | DSHPtrVal ptr_helix ptr_size_helix =>
          forall bk_helix,
            memory_lookup mem_helix ptr_helix ≡ Some bk_helix ->
            exists ptr_llvm bk_llvm,
              FMapAList.alist_find _ (ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
              get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm /\
              (fun bk_helix bk_llvm =>
                 forall i, i < ptr_size_helix ->
                      exists v_helix v_llvm,
                        mem_lookup i bk_helix ≡ Some v_helix /\
                        bisim_mem_lookup_llvm_at_i bk_llvm i ptr_size_helix v_llvm /\
                        v_llvm ≡ UVALUE_Double v_helix
              ) bk_helix bk_llvm
        end
.

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
  | |- KTree.iter ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  state_steps.
  reflexivity.
Qed.

(*
    for an opeartor, in initized state
    TODO: We could probably fix [env] to be [nil]
*)
Lemma compile_FSHCOL_correct:
  forall (op: DSHOperator) st bid_out st' bid_in bks σ env mem g ρ mem_llvm,
    genIR op st bid_out ≡ inr (st',(bid_in,bks)) ->
    eutt (bisim_partial σ)
         (translate (@subevent _ E _) (interp_Mem (denoteDSHOperator σ op) mem))
         (translate (@subevent _ E _)
                    (interp_to_L3' helix_intrinsics
                                   (D.denote_bks (normalize_types_blocks env bks) bid_in)
                                   g ρ mem_llvm)).
Proof.
  induction op; intros; rename H into HCompile.
  - inv HCompile.
    unfold interp_Mem. simpl denoteDSHOperator.
    rewrite interp_state_ret, translate_ret.
    simpl normalize_types_blocks.
    admit.
  - destruct src, dst.
    simpl in HCompile.
    repeat break_match_hyp; try inl_inr.
    inv Heqs; inv HCompile.
    match goal with
    | |- context[add_comment _ ?ss] => generalize ss; intros ls
    end.
    unfold interp_Mem. simpl denoteDSHOperator.

Admitted.

Definition LLVM_memory_state_cfg
  := M.memory_stack *
     (FMapAList.alist raw_id res_L0 * (FMapAList.alist raw_id dvalue)).

Definition LLVM_memory_state_mcfg
  := M.memory_stack *
     (FMapAList.alist raw_id res_L0 * @Stack.stack (FMapAList.alist raw_id res_L0) * (FMapAList.alist raw_id dvalue)).

(* Definition LLVM_state_cfg_from_mem: (block_id + res_L0) -> LLVM_memory_state -> LLVM_state_cfg *)
(*   := λ (r : block_id + res_L0) '(m, (ρ, g)), (m, (ρ, (g, r))). *)

(* Definition LLVM_state_mcfg_from_mem: (block_id + res_L0) -> LLVM_memory_state -> LLVM_state_mcfg *)
(*   := λ (r : block_id + res_L0) '(m, (ρ, g)), (m, ((ρ,[ρ]), (g, r))). *)

Definition LLVM_sub_state_cfg (T:Type): Type
  := M.memory_stack * (FMapAList.alist raw_id res_L0 * (FMapAList.alist raw_id dvalue * T)).

Definition LLVM_sub_state_mcfg (T:Type): Type
  := M.memory_stack * (FMapAList.alist raw_id res_L0 * @Stack.stack (FMapAList.alist raw_id res_L0) * (FMapAList.alist raw_id dvalue * T)).

Definition LLVM_sub_state_cfg_from_mem (T:Type) (v:T): LLVM_memory_state_cfg -> (LLVM_sub_state_cfg T)
  := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

Definition LLVM_sub_state_mcfg_from_mem (T:Type) (v:T): LLVM_memory_state_mcfg -> (LLVM_sub_state_mcfg T)
  := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

Definition llvm_empty_memory_state_cfg: LLVM_memory_state_cfg
  := (M.empty, M.empty, [], ([], [])).

Definition llvm_empty_memory_state_mcfg: LLVM_memory_state_mcfg
  := (M.empty, M.empty, [], (([],[]), [])).

(** Type of bisimilation relation between between DSHCOL and LLVM states.
    This relation could be used for "closed" CFG [mcfg].
 *)
Definition Type_R_full: Type := evalContext
           → MDSHCOLOnFloat64.memory * (list binary64)
             → LLVM_sub_state_mcfg (res_L0) → Prop.

Definition bisim_full: Type_R_full  :=
  fun σ  '(mem_helix, v_helix) mem_llvm =>
    let '(m, ((ρ,_), (g, v))) := mem_llvm in
    bisim_partial σ (mem_helix, tt) (LLVM_sub_state_cfg_from_mem (inr v) (m, (ρ, g))).

Definition init_one_global (m:LLVM_memory_state_cfg) (g:toplevel_entity typ (list (LLVMAst.block typ)))
  : err LLVM_memory_state_cfg
  := match g with
     | TLE_Global (mk_global (Name c_name) c_typ
                             true
                             (Some c_initiaizer)
                             (Some LINKAGE_Internal)
                             None None None true None
                             false None None) =>
       inl "TODO: implement me"%string
     | _ => inl "Usupported global initialization"%string
     end.

Definition init_llvm_memory
           (p: FSHCOLProgram)
           (data: list binary64) : err LLVM_memory_state_cfg
  :=
    '(data,ginit) <- initIRGlobals data p.(globals) ;;
    (* At this point `ginit` is list of TLE_Global definitions
       which could be applied sequentually to empty memory to
       get the state with initialized globals *)
    ListSetoid.monadic_fold_left init_one_global llvm_empty_memory_state_cfg ginit.

(* Relation holds between two empty memory states *)
Definition empty_R hm (lm:LLVM_sub_state_mcfg unit) : Prop :=
  hm ≡ (helix_empty_memory,tt) /\ lm ≡ (LLVM_sub_state_mcfg_from_mem tt llvm_empty_memory_state_mcfg).

(* Bisimulation relation holds between two memory states after
   initalization of global variables *)
Lemma initialization_memory_bisim_OK
      (p: FSHCOLProgram)
      (data: list binary64) :
  match helix_intial_memory p data, init_llvm_memory p data with
  | inl _, inl _ => False (* not sure if both erroring should be [True] *)
  | inr (hmem,data,σ), inr lmem =>
    bisim_partial σ (hmem,tt) (LLVM_sub_state_cfg_from_mem (inl (Name "main")) lmem)
  | _, _ => False
  end.
Proof.
Admitted.

(* with init step  *)
Lemma compiler_correct_aux:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (list (LLVMAst.block typ))),
    compile p data ≡ inr pll ->
    eutt (bisim_full []) (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
Admitted.

(* top-level  *)
Theorem compiler_correct:
  exists RR,
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (list (LLVMAst.block typ))),
    compile p data ≡ inr pll ->
    eutt RR (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
  eexists; eapply compiler_correct_aux.
Qed.
