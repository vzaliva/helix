Require Import Helix.LLVMGen.Correctness_Prelude.

Set Implicit Arguments.
Set Strict Implicit.

Section WF_IRState.

  (**
     The compiler maintains a sort of typing context named [IRState].
     This typing context should soundly reflect the content of the [evalContext],
     injecting the types from [DSHCOL] to [VIR].
   *)

  Definition getWFType (id : ident) (t: DSHType): typ :=
    match id, t with
    | ID_Local _  , DSHnat   => IntType
    | ID_Global _ , DSHnat   => TYPE_Pointer IntType
    | ID_Local _  , DSHCType => TYPE_Double
    | ID_Global _ , DSHCType => TYPE_Pointer TYPE_Double
    | _           , DSHPtr n => TYPE_Pointer (TYPE_Array (Int64.intval n) TYPE_Double)
    end.

  (* True if σ typechecks in Γ *)
  Definition evalContext_typechecks (σ : evalContext) (Γ : list (ident * typ)) : Prop :=
    forall v n, nth_error σ n ≡ Some v ->
           exists id, (nth_error Γ n ≡ Some (id, getWFType id (DSHType_of_DSHVal v))).

  Definition WF_IRState (σ : evalContext) (s : IRState) : Prop :=
    evalContext_typechecks σ (Γ s).

  Lemma WF_IRState_lookups :
    forall σ s n v id τ,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (id, τ) ->
      nth_error σ n ≡ Some v ->
      τ ≡ getWFType id (DSHType_of_DSHVal v).
  Proof.
    intros * WF LU_IR LU_SIGMA.
    apply WF in LU_SIGMA; destruct LU_SIGMA as (id' & LU); rewrite LU in LU_IR; inv LU_IR.
    reflexivity.
  Qed.

  Lemma WF_IRState_one_of_local_type:
    forall σ x τ s n v,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (ID_Local x,τ) ->
      nth_error σ n ≡ Some v ->
      τ ≡ IntType \/
      τ ≡ TYPE_Double \/
      exists k, τ ≡ TYPE_Pointer (TYPE_Array (Int64.intval k) TYPE_Double).
  Proof.
    intros * WF LU LU'.
    eapply WF in LU'; destruct LU' as (id & LU''); rewrite LU in LU''; inv LU''.
    cbn; break_match_goal; eauto.
  Qed.

  Lemma WF_IRState_one_of_global_type:
    forall σ x τ s n v,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (ID_Global x,τ) ->
      nth_error σ n ≡ Some v ->
      τ ≡ TYPE_Pointer IntType \/
      τ ≡ TYPE_Pointer TYPE_Double \/
      exists k, τ ≡ TYPE_Pointer (TYPE_Array (Int64.intval k) TYPE_Double).
  Proof.
    intros * WF LU LU'.
    edestruct WF as (id & LU''); eauto.
    rewrite LU in LU''; inv LU''.
    cbn in *.
    break_match_goal; eauto.
  Qed.

End WF_IRState.

Ltac abs_by_WF :=
  match goal with
  | h  : nth_error (Γ ?s) _ ≡ ?rhs,
    h': @nth_error DSHVal ?σ _ ≡ ?rhs'
    |- _ =>
    match rhs with
    | Some (?id,?τ) =>
      match rhs' with
      | None => fail
                 (*
        let LUP    := fresh "LUP" in
        let val    := fresh "val" in
        let CONTRA := fresh "CONTRA" in
        epose proof (context_lookup_succeeds _ _ _ h) as (val & LUP & CONTRA);
        rewrite h' in CONTRA;
        discriminate CONTRA *)
      | Some ?val =>
        let WF := fresh "WF" in
        assert (WF : WF_IRState σ s) by eauto;
        let H := fresh in pose proof (WF_IRState_lookups _ WF h h') as H; now (destruct id; inv H)
      end
    | None =>
      match rhs' with
      | None => fail
        (* exfalso; eapply WF_IRState_lookup_cannot_fail_st; now eauto *)
      | Some ?val => fail
      end
    end
  | h : nth_error (Γ ?s) _ ≡ Some (?id,?τ) |- _ =>
    match id with
    | ID_Local _ =>
      eapply WF_IRState_one_of_local_type in h; eauto;
      now (let EQ := fresh in destruct h as [EQ | [EQ | [? EQ]]]; inv EQ)
    | ID_Global _ =>
      eapply WF_IRState_one_of_global_type in h; eauto;
      now (let EQ := fresh in destruct h as [EQ | [EQ | [? EQ]]]; inv EQ)
    end
   end.

Section SimulationRelations.

  (**
     We define in this section the principal simulation relations used:
     - At the top-level to relate full [FSHCOLProgram]s to the full Vellvm
     program resulting from their compilation: see [compiler_correct]
     - At the top-level to relate these same program after initialization of
     the runtime. (TODOYZ: Do we need one such?)
     - When relating operators to the sub-cfg resulting from their compilation:
     see [compile_FSHCOL_correct]

    These relations also get refined when related sub-structures of the operators,
    we define these refinements in the corresponding sections.
   *)

  (**
     Relation used to relate memories after the initialization phase.
     Recall: [Type_R_memory ≜ memoryH -> LLVM_memory_state_cfg -> Prop]
  *)

  (* Conversion from Helix values to VIR values *)
  Definition dvalue_of_int (v : Int64.int) : dvalue := DVALUE_I64 (DynamicValues.Int64.repr (Int64.intval v)).
  Definition dvalue_of_bin (v: binary64)   : dvalue := DVALUE_Double v.

  (* Check that a pair of [ident] and [dvalue] can be found in the
     appropriate environment. This to be used only for scalar values,
     like [int] or [double] *)
  Definition in_local_or_global_scalar
             (ρ : local_env) (g : global_env) (m : memoryV)
             (x : ident) (dv : dvalue) (τ : typ) : Prop
    := match x with
       | ID_Local  x => ρ @ x ≡ Some (dvalue_to_uvalue dv)
       | ID_Global x =>
         exists ptr τ',
         τ ≡ TYPE_Pointer τ' /\
         g @ x ≡ Some (DVALUE_Addr ptr) /\
         read m ptr (typ_to_dtyp [] τ') ≡ inr (dvalue_to_uvalue dv)
       end.

  (* Check that a pair of [ident] and [dvalue] can be found in the
     appropriate environment. *)
  Definition in_local_or_global_addr
             (ρ : local_env) (g : global_env)
             (x : ident) (a : Addr.addr): Prop
    := match x with
       | ID_Local  x => ρ @ x ≡ Some (UVALUE_Addr a)
       | ID_Global x => g @ x ≡ Some (DVALUE_Addr a)
       end.

  (* Main memory invariant. Relies on Helix's evaluation context and the [IRState] built by the compiler.
     At any indices, the value and ident/types respectively found are related in that:
     - integers and floats have their translation in the appropriate VIR environment;
     - pointers have a corresponding pointer in the appropriate VIR environment such that they map on identical arrays
   *)
  Definition memory_invariant (σ : evalContext) (s : IRState) : Rel_cfg :=
    fun (mem_helix : MDSHCOLOnFloat64.memory) '(mem_llvm, (ρ,g)) =>
      forall (n: nat) v τ x,
        nth_error σ n ≡ Some v ->
        nth_error (Γ s) n ≡ Some (x,τ) ->
        match v with
        | DSHnatVal v   => in_local_or_global_scalar ρ g mem_llvm x (dvalue_of_int v) τ
        | DSHCTypeVal v => in_local_or_global_scalar ρ g mem_llvm x (dvalue_of_bin v) τ
        | DSHPtrVal ptr_helix ptr_size_helix =>
          exists bk_helix ptr_llvm,
          memory_lookup mem_helix ptr_helix ≡ Some bk_helix /\
          in_local_or_global_addr ρ g x ptr_llvm /\
          (forall i v, mem_lookup i bk_helix ≡ Some v ->
                  get_array_cell mem_llvm ptr_llvm i DTYPE_Double ≡ inr (UVALUE_Double v))
        end.

  (* Lookups in [genv] are fully determined by lookups in [Γ] and [σ] *)
  Lemma memory_invariant_GLU : forall σ s v id memH memV t l g n,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Global id, TYPE_Pointer t) ->
      nth_error σ v ≡ Some (DSHnatVal n) ->
      exists ptr, Maps.lookup id g ≡ Some (DVALUE_Addr ptr) /\
             read memV ptr (typ_to_dtyp [] t) ≡ inr (dvalue_to_uvalue (DVALUE_I64 n)).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    destruct LU as (ptr & τ & EQ & LU & READ); inv EQ.
    exists ptr; split; auto.
    cbn in *.
    rewrite repr_intval in READ; auto.
  Qed.

  (* Lookups in [local_env] are fully determined by lookups in [Γ] and [σ] *)
  Lemma memory_invariant_LLU : forall σ s v id memH memV t l g n,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHnatVal n) ->
      Maps.lookup id l ≡ Some (UVALUE_I64 n).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    unfold in_local_or_global_scalar, dvalue_of_int in LU.
    rewrite repr_intval in LU; auto.
  Qed.

  Hint Resolve memory_invariant_GLU memory_invariant_LLU : core.

  (* Lookups in [local_env] are fully determined by lookups in [vars] and [σ] *)
  Lemma memory_invariant_LLU_AExpr : forall σ s v id memH memV t l g f,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHCTypeVal f) ->
      Maps.lookup id l ≡ Some (UVALUE_Double f).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    unfold in_local_or_global_scalar, dvalue_of_int in LU.
    cbn in LU; auto.
  Qed.

  (* Lookups in [genv] are fully determined by lookups in [vars] and [σ] *)
  Lemma memory_invariant_GLU_AExpr : forall σ s v id memH memV t l g f,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Global id, TYPE_Pointer t) ->
      nth_error σ v ≡ Some (DSHCTypeVal f) ->
      exists ptr, Maps.lookup id g ≡ Some (DVALUE_Addr ptr) /\
             read memV ptr (typ_to_dtyp [] t) ≡ inr (dvalue_to_uvalue (DVALUE_Double f)).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    destruct LU as (ptr & τ & EQ & LU & READ); inv EQ.
    exists ptr; split; auto.
  Qed.

  Hint Resolve memory_invariant_GLU memory_invariant_LLU memory_invariant_LLU_AExpr memory_invariant_GLU_AExpr : core.

  Lemma memory_invariant_LLU_Ptr : forall σ s v id memH memV t l g m size,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHPtrVal m size) ->
      exists (bk_h : mem_block) (ptr_v : Addr.addr),
        memory_lookup memH m ≡ Some bk_h
        /\ in_local_or_global_addr l g (ID_Local id) ptr_v
        /\ (forall (i : Memory.NM.key) (v : binary64),
              mem_lookup i bk_h ≡ Some v -> get_array_cell memV ptr_v i DTYPE_Double ≡ inr (UVALUE_Double v)).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    auto.
  Qed.

  (** ** Fresh identifier generator invariant
      Low and high level invariants ensuring that calls to [incLocal] indeed generate fresh variables.
   *)
  Definition incLocal_fresh (l : local_env) (s : IRState) : Prop :=
    forall s' id, incLocal s ≡ inr (s',id) ->
             alist_fresh id l.

  Definition concrete_fresh_inv (s : IRState) : config_cfg -> Prop :=
    fun '(_, (l,g)) =>
      forall id v n, alist_In id l v -> n >= local_count s -> id <> Name ("l" @@ string_of_nat n).

  (* We need to preserve the concrete invariant, but it is sufficient to get the abstract one of interest *)
  Lemma concrete_fresh_fresh: forall s memV l g,
      concrete_fresh_inv s (memV,(l,g)) ->
      incLocal_fresh l s.
  Proof.
    intros * FRESH ? ? LU.
    unfold incLocal, incLocalNamed in LU; cbn in *; inv LU.
    unfold alist_fresh.
    match goal with
    | |- ?x ≡ None => destruct x eqn:EQ; auto; exfalso
    end.
    eapply FRESH; eauto.
  Qed.

  (** ** General state invariant
      The main invariant carried around combine the three properties defined:
      1. the memories satisfy the invariant;
      2. the [IRState] is well formed;
      3. the fresh ident generator is working properly.
   *)
  Record state_invariant (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
    mem_is_inv : memory_invariant σ s memH configV ;
    IRState_is_WF : WF_IRState σ s ;
    incLocal_is_fresh : concrete_fresh_inv s configV
    }.

  (* Named function pointer exists in global environemnts *)
  Definition global_named_ptr_exists (fnname:string) : Pred_cfg :=
    fun '(mem_llvm, (ρ,g)) => exists mf, g @ (Name fnname) ≡ Some (DVALUE_Addr mf).

  (* For compiled FHCOL programs we need to ensure we have 2 declarations:
     1. "main" function
     2. function, implementing compiled expression.
   *)
  Definition declarations_invariant (fnname:string) : Pred_cfg :=
    fun c =>
      global_named_ptr_exists "main" c /\
      global_named_ptr_exists fnname c.

  (** An invariant which must hold after initialization stage *)
  Record post_init_invariant (fnname:string) (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
    state_inv:  state_invariant σ s memH configV;
    decl_inv: declarations_invariant fnname configV
    }.

  (**
   Lifting of [memory_invariant] to include return values in the relation.
   This relation is used to prove the correctness of the compilation of operators.
   The value on the Helix side is trivially [unit]. The value on the Vellvm-side however
   is non trivial, we will most likely have to mention it.
   *)
  (* TODO: Currently this relation just preserves memory invariant.
   Maybe it needs to do something more?
   *)
  Definition bisim_partial (σ : evalContext) (s : IRState) : Type_R_partial
    :=
      fun '(mem_helix, _) '(mem_llvm, x) =>
        let '(ρ, (g, _)) := x in
        memory_invariant σ s mem_helix (mem_llvm, (ρ, g)).

  (**
   Relation over memory and invariant for a full [cfg], i.e. to relate states at
   the top-level. lift_R_memory_mcfg
   Currently a simple lifting of [bisim_partial].
   *)
  Definition bisim_full (σ : evalContext) (s : IRState) : Type_R_full  :=
    fun '(mem_helix, _) mem_llvm =>
      let '(m, ((ρ,_), (g, v))) := mem_llvm in
      bisim_partial σ s (mem_helix, tt) (mk_config_cfg_T (inr v) (m, (ρ, g))).

  (** Relation bewteen the final states of evaluation and execution
    of DHCOL program.

    At this stage we do not care about memory or environemnts, and
    just compare return value of [main] function in LLVM with
    evaulation results of DSHCOL.
   *)
  Definition bisim_final (σ : evalContext) : Type_R_full :=
    fun '(_, h_result) '(_,(_,(_,llvm_result))) =>
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

End SimulationRelations.

Section Ext_Local.

  (** When compiling expressions, we need to carry on the invariant that
      the meaning of the generated expression will be stable by execution of the
      intermediate code corresponding to the evaluation of the second operand.
      To this end, we rely on the fact that this code does not alter the configuration
      except to extend it with fresh bindings.
   *)
  Definition ext_local {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ⊑ l.

 Lemma in_local_or_global_scalar_ext_local :
    forall ρ1 ρ2 g m x dv τ,
      in_local_or_global_scalar ρ1 g m x dv τ ->
      ρ1 ⊑ ρ2 ->
      in_local_or_global_scalar ρ2 g m x dv τ.
  Proof.
    unfold in_local_or_global_scalar; intros ? ? ? ? [] ? ? IN MONO; auto.
    apply MONO; auto.
  Qed.

 Lemma in_local_or_global_addr_ext_local :
    forall ρ1 ρ2 g x ptr,
      in_local_or_global_addr ρ1 g x ptr ->
      ρ1 ⊑ ρ2 ->
      in_local_or_global_addr ρ2 g x ptr.
  Proof.
    unfold in_local_or_global_addr; intros ρ1 ρ2 g [] ptr IN MONO; auto.
    apply MONO; auto.
  Qed.

  Lemma memory_invariant_ext_local :
    forall σ s memH memV ρ1 ρ2 g,
      memory_invariant σ s memH (memV, (ρ1, g)) ->
      ρ1 ⊑ ρ2 ->
      memory_invariant σ s memH (memV, (ρ2, g)).
  Proof.
    intros * INV MONO.
    red; intros * NTH NTH'.
    specialize (INV _ _ _ _ NTH NTH').
    destruct v; eauto.
    eapply in_local_or_global_scalar_ext_local; eauto.
    eapply in_local_or_global_scalar_ext_local; eauto.
    repeat destruct INV as (? & INV).
    do 3 eexists; splits; eauto.
    eapply in_local_or_global_addr_ext_local; eauto.
  Qed.

End Ext_Local.

Lemma state_invariant_WF_IRState :
  forall σ s memH st, state_invariant σ s memH st -> WF_IRState σ s.
Proof.
  intros ? ? ? (? & ? & ?) [_ WF _]; auto.
Qed.

Lemma state_invariant_memory_invariant :
  forall σ s memH st, state_invariant σ s memH st -> memory_invariant σ s memH st.
Proof.
  intros ? ? ? (? & ? & ?) [INV _ _]; auto.
Qed.

Lemma ext_local_refl:
  forall {R S} memH memV l g n v,
    @ext_local R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
Proof.
  intros; repeat split; reflexivity.
Qed.
Hint Resolve state_invariant_memory_invariant state_invariant_WF_IRState ext_local_refl: core.

Lemma in_local_or_global_scalar_same_global : forall l g l' m id dv τ,
    in_local_or_global_scalar l g m (ID_Global id) dv τ ->
    in_local_or_global_scalar l' g m (ID_Global id) dv τ.
Proof.
  cbn; intros; auto.
Qed.

Lemma in_local_or_global_addr_same_global : forall l g l' id ptr,
    in_local_or_global_addr l g (ID_Global id) ptr ->
    in_local_or_global_addr l' g (ID_Global id) ptr.
Proof.
  cbn; intros; auto.
Qed.

Lemma incLocal_Γ:
  forall s s' id,
    incLocal s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma in_local_or_global_scalar_add_fresh_old :
  forall (id : raw_id) (l : local_env) (g : global_env) m (x : ident) dv dv' τ,
    x <> ID_Local id ->
    in_local_or_global_scalar l g m x dv τ ->
    in_local_or_global_scalar (alist_add id dv' l) g m x dv τ.
Proof.
  intros * INEQ LUV'.
  destruct x; cbn in *; auto.
  rewrite rel_dec_neq_false; try typeclasses eauto; [| intros ->; auto].
  rewrite remove_neq_alist; auto; try typeclasses eauto; intros ->; auto.
Qed.

Lemma in_local_or_global_addr_add_fresh_old :
  forall (id : raw_id) (l : local_env) (g : global_env) (x : ident) ptr dv',
    x <> ID_Local id ->
    in_local_or_global_addr l g x ptr ->
    in_local_or_global_addr (alist_add id dv' l) g x ptr.
Proof.
  intros * INEQ LUV'.
  destruct x; cbn in *; auto.
  rewrite rel_dec_neq_false; try typeclasses eauto; [| intros ->; auto].
  rewrite remove_neq_alist; auto; try typeclasses eauto; intros ->; auto.
Qed.

Lemma fresh_no_lu :
  forall s s' id l g m x dv τ,
    incLocal s ≡ inr (s', id) ->
    incLocal_fresh l s ->
    in_local_or_global_scalar l g m x dv τ ->
    x <> ID_Local id.
Proof.
  intros * INC FRESH IN abs; subst.
  apply FRESH in INC.
  unfold alist_fresh in *.
  cbn in *; rewrite INC in IN; inv IN.
Qed.

Lemma fresh_no_lu_addr :
  forall s s' id l g x ptr,
    incLocal s ≡ inr (s', id) ->
    incLocal_fresh l s ->
    in_local_or_global_addr l g x ptr ->
    x <> ID_Local id.
Proof.
  intros * INC FRESH IN abs; subst.
  apply FRESH in INC.
  unfold alist_fresh in *.
  cbn in *; rewrite INC in IN; inv IN.
Qed.

(* Inversion messes up my goal a bit too much, simpler to use this *)
Lemma Name_inj : forall s1 s2,
    Name s1 ≡ Name s2 ->
    s1 ≡ s2.
Proof.
  intros * EQ; inv EQ; auto.
Qed.

Lemma append_factor_left : forall s s1 s2,
    s @@ s1 ≡ s @@ s2 ->
    s1 ≡ s2.
Proof.
  induction s as [| c s IH]; cbn; intros * EQ; auto.
  apply IH.
  inv EQ; auto.
Qed.

Global Opaque append.
(**
     [memory_invariant] is stable by fresh extension of the local environment.
 *)
Lemma state_invariant_add_fresh :
  forall σ s s' id memH memV l g v,
    incLocal s ≡ inr (s', id) ->
    state_invariant σ s memH (memV, (l, g)) ->
    state_invariant σ s' memH (memV, (alist_add id v l, g)).
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; intros * LUH LUV.
    erewrite incLocal_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
    break_match.
    + subst.
      eapply in_local_or_global_scalar_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply concrete_fresh_fresh; eauto.
    + subst.
      eapply in_local_or_global_scalar_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply concrete_fresh_fresh; eauto.
    + subst.
      repeat destruct INLG as [? INLG].
      do 3 eexists; splits; eauto.
      eapply in_local_or_global_addr_add_fresh_old; eauto.
      eapply fresh_no_lu_addr; eauto.
      eapply concrete_fresh_fresh; eauto.
  - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
  - intros ? ? ? LU INEQ.
    clear MEM WF.
    destruct (rel_dec_p id0 id); [subst |];
      destruct s; cbn in INC; inv_sum; cbn in *.
    + intros abs.
      clear - INEQ abs.
      apply Name_inj, append_factor_left,string_of_nat_inj in abs; lia.
    + apply In_add_In_ineq in LU; eauto.
      eapply FRESH; eauto with arith.
Qed.

Lemma ext_local_subalist : forall {R S} memH memV l1 g vH vV l2,
    l1 ⊑ l2 ->
    @ext_local R S memH (mk_config_cfg memV l1 g) (memH, vH) (memV, (l2, (g, vV))).
Proof.
  intros * SUB; cbn; splits; auto.
Qed.

Lemma incVoid_Γ:
  forall s s' id,
    incVoid s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incVoid_local_count:
  forall s s' id,
    incVoid s ≡ inr (s', id) ->
    local_count s' ≡ local_count s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma state_invariant_incVoid :
  forall σ s s' k memH stV,
    incVoid s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; repeat break_let; intros * LUH LUV.
    erewrite incVoid_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
  - unfold WF_IRState; erewrite incVoid_Γ; eauto; apply WF.
  - red; repeat break_let; erewrite incVoid_local_count; eauto.
Qed.

Lemma incLocal_local_count: forall s s' x,
    incLocal s ≡ inr (s',x) ->
    local_count s' ≡ S (local_count s).
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma state_invariant_incLocal :
  forall σ s s' k memH stV,
    incLocal s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; repeat break_let; intros * LUH LUV.
    erewrite incLocal_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
  - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
  - red; repeat break_let; intros ? ? ? LU INEQ.
    clear MEM WF.
    erewrite incLocal_local_count in INEQ; eauto.
    eapply FRESH; eauto with arith.
Qed.

Lemma incBlockNamed_Γ:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incBlockNamed_local_count:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    local_count s' ≡ local_count s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma state_invariant_incBlockNamed :
  forall σ s s' k msg memH stV,
    incBlockNamed msg s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; repeat break_let; intros * LUH LUV.
    erewrite incBlockNamed_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
  - unfold WF_IRState; erewrite incBlockNamed_Γ; eauto; apply WF.
  - red; repeat break_let; erewrite incBlockNamed_local_count; eauto.
Qed.

Global Opaque incBlockNamed.
Global Opaque incVoid.
Global Opaque incLocal.

Lemma unsigned_is_zero: forall a, Int64.unsigned a ≡ Int64.unsigned Int64.zero ->
                             a = Int64.zero.
Proof.
  intros a H.
  unfold Int64.unsigned, Int64.intval in H.
  repeat break_let; subst.
  destruct Int64.zero.
  inv Heqi0.
  unfold equiv, MInt64asNT.NTypeEquiv, Int64.eq, Int64.unsigned, Int64.intval.
  (* apply Coqlib.zeq_true. *)
(* Qed. *)
Admitted.

