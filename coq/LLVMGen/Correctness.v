Require Import Coq.Arith.Arith.
Require Import Psatz.

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
Require Import Helix.Util.ListUtil.
Require Import Helix.Tactics.HelixTactics.

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

Require Import Ceres.Ceres.

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
                        (global_env) ->
                        (local_env) ->
                        memory ->
itree (CallE +' PickE +' UBE +' DebugE +' FailureE)
              (memory * (local_env * (global_env * R))) :=
  fun R _ _ a b c => raise "".

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
          FMapAList.alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat v))) \/
          (* if not found, check global *)
          (FMapAList.alist_find _ (inj_f ι x) ρ ≡ None /\ FMapAList.alist_find _ (inj_f ι x) g ≡ Some (DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat v))))
        | DSHCTypeVal v =>
          (* check local env first *)
          FMapAList.alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Double v) \/
          (* if not found, check global *)
          (FMapAList.alist_find _ (inj_f ι x) ρ ≡ None /\
           FMapAList.alist_find _ (inj_f ι x) g ≡ Some (DVALUE_Double v))
        | DSHPtrVal ptr_helix ptr_size_helix =>
          forall bk_helix,
            memory_lookup mem_helix ptr_helix ≡ Some bk_helix ->
            exists ptr_llvm bk_llvm,
              FMapAList.alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
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

(*
    for an opeartor, in initized state
    TODO: We could probably fix [env] to be [nil]
*)
Lemma compile_FSHCOL_correct (op: DSHOperator) st bid_out st' bid_in bks σ env mem g ρ mem_llvm:
  bisim_partial σ (mem,tt) (mem_llvm, (ρ, (g, (inl bid_in)))) ->
  genIR op st bid_out ≡ inr (st',(bid_in,bks)) ->
  eutt (bisim_partial σ)
       (translate (@subevent _ E _) (interp_Mem (denoteDSHOperator σ op) mem))
       (translate (@subevent _ E _)
                  (interp_to_L3' helix_intrinsics
                                 (D.denote_bks (normalize_types_blocks env bks) bid_in)
                                 g ρ mem_llvm)).
  intros P.
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
      (*  global_env = FMapAList.alist raw_id dvalue *)
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
  | (TYPE_Array _ TYPE_Double, EXP_Array a) => eval_const_double_exp typed_expr
  | (TYPE_Double, EXP_Double v) =>  eval_const_arr_exp typed_expr
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

    let x := Anon 0%Z in
    let xtyp := getIRType (FSHvecValType p.(i)) in
    let y := Anon 1%Z in
    let ytyp := getIRType (FSHvecValType p.(o)) in

    let xyinit := global_XY p.(i) p.(o) data x xtyp y ytyp in

    post_xy <- ListSetoid.monadic_fold_left init_one_global llvm_empty_memory_state_partial xyinit ;;
    ListSetoid.monadic_fold_left init_one_global post_xy ginit.


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
  revert mem mem' data data' σ.
  induction globals; intros.
  -
    cbn in *.
    inv H.
    reflexivity.
  -
    cbn in H.
    break_let; subst.
    break_match;[inl_inr|].
    repeat break_let; subst.
    break_match;[inl_inr|].
    repeat break_let; subst.
    inv H.
    cbn.
    erewrite IHglobals; eauto.
Qed.

(* Maps indices from [σ] to [raw_id].
   Currently [σ := [globals;Y;X]]
   Where globals mapped by name, while [X-> Anon 0] and [Y->Anon 1]
*)
Definition memory_invariant_map (globals : list (string * FSHValType)): nat -> raw_id
  := fun j =>
       let n := List.length globals in
       if Nat.eqb j n then Anon 0%Z (* X *)
       else if Nat.eqb j (S n) then Anon 1%Z (* Y *)
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

(* If [initIRGlobals] suceeds, the names of variables in [globals] were unique *)
Lemma initIRGlobals_names_unique globals data res:
  initIRGlobals data globals ≡ inr res → list_uniq fst globals.
Proof.
Admitted.

(** [memory_invariant] relation must holds after initalization of global variables *)
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
  break_match_hyp ; [inl_inr|].
  break_let.
  destruct p.
  break_match_hyp; inv LI.
  repeat break_let; subst.
  break_match_hyp; inv HI.
  cbn in *.
  repeat break_let; subst.
  inv H1.
  right. (* as [σ] is never empty after init *)

  rename Heqp3 into HCY, m2 into ydata.
  rename Heqp2 into HCX, m1 into xdata.
  rename Heqe1 into HFSHG, l3 into fdata', e into σ.
  rename Heqe into HIRG, l0 into ldata', l1 into gdecls.
  remember (global_XY i o ldata' (Anon 0%Z) (TYPE_Array (Z.of_nat i) TYPE_Double)
                      (Anon 1%Z) (TYPE_Array (Z.of_nat o) TYPE_Double)) as xydecls eqn:HXY.
  rename Heqe0 into HFXY, l2 into lm0.
  rename H0 into HG.
  rename m into lm1, l4 into fdata'', data into fdata'''.

  (* No local variables initialize in init stage *)
  assert(L: l ≡ []).
  {
    pose proof (monadic_fold_left_err_app HFXY HG) as HFGXY.
    unfold llvm_empty_memory_state_partial in HFGXY.
    generalize dependent (app xydecls gdecls).
    generalize dependent M.empty_memory_stack.
    intros m x.
    generalize (@nil (prod raw_id dvalue)).
    intros g0 H.
    clear - H.

    unfold llvm_empty_memory_state_partial in H.
    revert g0 m g l H.
    induction x; intros; cbn in H.
    -
      inv H; reflexivity.
    -
      break_match_hyp; [inl_inr|].
      destruct l0 as [m' [l' g']].
      destruct l'.
      + eapply IHx, H.
      +
        unfold init_one_global in Heqe.
        repeat break_match_hyp; subst; try inl_inr.
        inv Heqe.
        repeat break_match_hyp; subst; try inl_inr.
  }
  subst l; cbn in *.

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
    (* but currently natval constants not implemented so we
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
    clear Hx.
    revert F Hn.
    revert fdata''' m0 fdata' σ x.
    generalize helix_empty_memory as mem.
    induction globals; intros.
    +
      cbn in F.
      inv F.
      rewrite Util.nth_error_nil in Hn.
      inv Hn.
    +
      cbn in F.
      destruct a; destruct f; cbn in F.
      *
        break_match_hyp.
        inl_inr.
        repeat break_let; subst. inl_inr.
      *
        break_match_hyp; [inl_inr|].
        repeat break_let; subst.
        destruct σ as [| σ0 σs]; inv F.
        destruct x; [inv Hn|].
        rewrite ListUtil.nth_error_Sn in Hn.
        eapply IHglobals; eauto.
      *
        break_match_hyp; [inl_inr|].
        repeat break_let; subst.
        destruct σ as [| σ0 σs]; inv F.
        destruct x; [inv Hn|].
        rewrite ListUtil.nth_error_Sn in Hn.
        eapply IHglobals; eauto.
  -
    (* [DSHCTypeVal] must end up in globals *)
    right.
    split; [trivial|].
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
    compile p data ≡ inr pll ->
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
    compile p data ≡ inr pll ->
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
