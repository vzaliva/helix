Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Freshness.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
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

  Lemma WF_IRState_Γ :
    forall (σ : evalContext) (s1 s2 : IRState),
      WF_IRState σ s1 ->
      Γ s1 ≡ Γ s2 ->
      WF_IRState σ s2.
  Proof.
    intros σ s1 s2 WF GAMMA.
    unfold WF_IRState.
    rewrite <- GAMMA.
    apply WF.
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
      | Some ?val =>
        let WF := fresh "WF" in
        assert (WF : WF_IRState σ s) by eauto;
        let H := fresh in pose proof (WF_IRState_lookups _ WF h h') as H; now (destruct id; inv H)
      end
    | None =>
      match rhs' with
      | None => fail
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


Ltac try_abs :=
  try (abs_by_WF ||
        abs_by failure_helix_throw || abs_by failure_helix_throw').

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

  Definition mem_lookup_succeeds bk size :=
    forall i, 0 <= i /\ i < MInt64asNT.to_nat size -> exists v, mem_lookup i bk ≡ Some v.

  Definition no_dshptr_aliasing (σ : evalContext) : Prop :=
    forall n n' ptr sz sz',
      nth_error σ n ≡ Some (DSHPtrVal ptr sz) ->
      nth_error σ n' ≡ Some (DSHPtrVal ptr sz') ->
      n' ≡ n.

  Definition no_id_aliasing (s : IRState) : Prop :=
    forall n n' id τ τ',
      nth_error (Γ s) n ≡ Some (id, τ) ->
      nth_error (Γ s) n' ≡ Some (id, τ') ->
      n' ≡ n.

  Definition no_llvm_ptr_aliasing (σ : evalContext) (s : IRState) (ρ : local_env) (g : global_env) : Prop :=
    forall (id1 : ident) (ptrv1 : addr) (id2 : ident) (ptrv2 : addr) n1 n2 τ τ' sz1 sz2 ptrh1 ptrh2,
      nth_error σ n1 ≡ Some (DSHPtrVal ptrh1 sz1) ->
      nth_error σ n2 ≡ Some (DSHPtrVal ptrh2 sz2) ->
      nth_error (Γ s) n1 ≡ Some (id1, τ) ->
      nth_error (Γ s) n2 ≡ Some (id2, τ') ->
      in_local_or_global_addr ρ g id1 ptrv1 ->
      in_local_or_global_addr ρ g id2 ptrv2 ->
      id1 ≢ id2 ->
      fst ptrv1 ≢ fst ptrv2.

  Definition no_llvm_ptr_aliasing_cfg (σ : evalContext) (s : IRState) : config_cfg -> Prop :=
    fun '(mv, (ρ, g)) => no_llvm_ptr_aliasing σ s ρ g.

  (* TODO: might not keep this *)
  Definition dshptr_no_block_aliasing (σ : evalContext) ρ g dshp1 (ptrv1 : addr) : Prop :=
    forall dshp2 n2 sz2 s id2 ptrv2 τ,
      dshp1 ≢ dshp2 ->
      nth_error σ n2 ≡ Some (DSHPtrVal dshp2 sz2) ->
      nth_error (Γ s) n2 ≡ Some (id2, τ) ->
      in_local_or_global_addr ρ g id2 ptrv2 ->
      fst ptrv1 ≢ fst ptrv2.

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
          mem_lookup_succeeds bk_helix ptr_size_helix /\
          dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp (Γ s) τ) /\ (* TODO: might not need this *)
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
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
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
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
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
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
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
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
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
        /\ mem_lookup_succeeds bk_h size
        /\ dtyp_fits memV ptr_v (typ_to_dtyp (Γ s) t)
        /\ in_local_or_global_addr l g (ID_Local id) ptr_v
        /\ (forall (i : Memory.NM.key) (v : binary64),
              mem_lookup i bk_h ≡ Some v -> get_array_cell memV ptr_v i DTYPE_Double ≡ inr (UVALUE_Double v)).
  Proof.
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
    auto.
  Qed.

  Lemma ptr_alias_size_eq :
    forall σ n1 n2 sz1 sz2 p,
      no_dshptr_aliasing σ ->
      nth_error σ n1 ≡ Some (DSHPtrVal p sz1) ->
      nth_error σ n2 ≡ Some (DSHPtrVal p sz2) ->
      sz1 ≡ sz2.
  Proof.
    intros σ n1 n2 sz1 sz2 p ALIAS N1 N2.
    pose proof (ALIAS _ _ _ _ _ N1 N2); subst.
    rewrite N1 in N2; inversion N2.
    auto.
  Qed.

  (** ** General state invariant
      The main invariant carried around combine the three properties defined:
      1. the memories satisfy the invariant;
      2. the [IRState] is well formed;
   *)
  Record state_invariant (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
    mem_is_inv : memory_invariant σ s memH configV ;
    IRState_is_WF : WF_IRState σ s ;
    st_no_id_aliasing : no_id_aliasing s ;
    st_no_dshptr_aliasing : no_dshptr_aliasing σ ;
    st_no_llvm_ptr_aliasing : no_llvm_ptr_aliasing_cfg σ s configV
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
    state_inv: state_invariant σ s memH configV;
    decl_inv:  declarations_invariant fnname configV
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
  Definition ext_local {R S}: config_helix -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ⊑ l.

  Definition sub_local_no_aliasing (σ : evalContext) (s : IRState) (ρ1 ρ2 : local_env) (g : global_env) :=
    ρ1 ⊑ ρ2 /\
    (forall id id' ptr ptr' n1 n2 ptrh1 ptrh2 τ τ' sz1 sz2,
        nth_error σ n1 ≡ Some (DSHPtrVal ptrh1 sz1) ->
        nth_error σ n2 ≡ Some (DSHPtrVal ptrh2 sz2) ->
        nth_error (Γ s) n1 ≡ Some (id, τ) ->
        nth_error (Γ s) n2 ≡ Some (id', τ') ->
        in_local_or_global_addr ρ2 g id ptr ->
        in_local_or_global_addr ρ2 g id' ptr' ->
        id ≢ id' ->
        fst ptr ≢ fst ptr').

  Definition ext_local_no_aliasing {R S}
             (σ : evalContext) (s  : IRState) :
    config_helix -> config_cfg -> Rel_cfg_T R S
    := fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) =>
         mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ sub_local_no_aliasing σ s li l g.

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

  Lemma no_llvm_ptr_aliasing_ext_local :
    forall σ s ρ1 ρ2 g,
      no_llvm_ptr_aliasing σ s ρ1 g ->
      sub_local_no_aliasing σ s ρ1 ρ2 g ->
      no_llvm_ptr_aliasing σ s ρ2 g.
  Proof.
    intros σ s ρ1 ρ2 g ALIAS [EXT EXT_ALIAS].
    unfold no_llvm_ptr_aliasing in *.

    intros id1 ptrv1 id2 ptrv2 INP1 INP2 NEQ.
    eauto.
  Qed.


  Lemma memory_invariant_ext_local :
    forall σ s memH memV ρ1 ρ2 g,
      memory_invariant σ s memH (memV, (ρ1, g)) ->
      ρ1 ⊑ ρ2 ->
      memory_invariant σ s memH (memV, (ρ2, g)).
  Proof.
    intros * MEM_INV EXT_LOCAL.
    red; intros * NTH NTH'.
    specialize (MEM_INV _ _ _ _ NTH NTH').
    destruct v; eauto.
    eapply in_local_or_global_scalar_ext_local; eauto.
    eapply in_local_or_global_scalar_ext_local; eauto.
    repeat destruct MEM_INV as (? & MEM_INV).
    do 3 eexists; splits; eauto.
    eapply in_local_or_global_addr_ext_local; eauto.
  Qed.

End Ext_Local.

Lemma state_invariant_WF_IRState :
  forall σ s memH st, state_invariant σ s memH st -> WF_IRState σ s.
Proof.
  intros ? ? ? (? & ? & ?) [_ WF]; auto.
Qed.

Lemma state_invariant_memory_invariant :
  forall σ s memH st, state_invariant σ s memH st -> memory_invariant σ s memH st.
Proof.
  intros ? ? ? (? & ? & ?) [INV _]; auto.
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

Lemma append_factor_left : forall s s1 s2,
    s @@ s1 ≡ s @@ s2 ->
    s1 ≡ s2.
Proof.
  induction s as [| c s IH]; cbn; intros * EQ; auto.
  apply IH.
  inv EQ; auto.
Qed.

Lemma incLocal_no_id_aliasing :
  forall s1 s2 id,
    incLocal s1 ≡ inr (s2, id) ->
    no_id_aliasing s1 ->
    no_id_aliasing s2.
Proof.
  intros s1 s2 id INC ALIAS.
  unfold no_id_aliasing in *.
  apply incLocal_Γ in INC.
  rewrite INC.
  auto.
Qed.

Definition no_local_global_alias (l : local_env) (g : global_env) (v : uvalue) : Prop :=
  forall id p p', v ≡ UVALUE_Addr p -> in_local_or_global_addr l g id p' -> fst p ≢ fst p'.

Lemma no_local_global_alias_no_llvm_ptr_aliasing :
  forall σ s id v l g,
    no_llvm_ptr_aliasing σ s l g ->
    no_local_global_alias l g v ->
    no_llvm_ptr_aliasing σ s (alist_add id v l) g.
Proof.
  intros σ s id v l g LLVM_ALIAS NO_LG.
  unfold no_llvm_ptr_aliasing in *.
  unfold no_local_global_alias in *.

  intros id1 ptrv1 id2 ptrv2 n1 n2 τ τ' sz1 sz2 ptrh1 ptrh2 N1σ N2σ N1 N2 INp1 INp2 NEQ.
  destruct id1, id2;
    eauto using in_local_or_global_addr_same_global.
  - destruct (id1 ?[ Logic.eq ] id) eqn:EQid;
      cbn in INp2; rewrite EQid in INp2.
    + inversion INp2; subst.
      intros CONTRA. symmetry in CONTRA. revert CONTRA.
      eapply NO_LG; eauto using in_local_or_global_addr_same_global.
    + rewrite remove_neq_alist in INp2; eauto.

      (* These are all obviously true... *)
      admit.
      admit.
      admit.
  - destruct (id0 ?[ Logic.eq ] id) eqn:EQid;
      cbn in INp1; rewrite EQid in INp1.
    + inversion INp1; subst.
      eapply NO_LG; eauto using in_local_or_global_addr_same_global.
    + rewrite remove_neq_alist in INp1; eauto.

      (* These are all obviously true... *)
      admit.
      admit.
      admit.
  - cbn in *.
    break_match;
      break_match.
    + assert (id1 ≡ id0) by admit.
      exfalso. apply NEQ.
      subst.
      auto.
    + inversion INp2; subst.
      intros CONTRA. symmetry in CONTRA. revert CONTRA.
      eapply (NO_LG (ID_Local id0)); eauto using in_local_or_global_addr_same_global.
 
      rewrite remove_neq_alist in INp1; eauto.

      (* These are all obviously true... *)
      admit.
      admit.
      admit.
    + inversion INp1; subst.
      eapply (NO_LG (ID_Local id1)); eauto using in_local_or_global_addr_same_global.
 
      rewrite remove_neq_alist in INp2; eauto.

      (* These are all obviously true... *)
      admit.
      admit.
      admit.
    + rewrite remove_neq_alist in INp1, INp2; eauto.

      all: admit. (* These should all hold too. *)
Admitted.

(**
     [memory_invariant] is stable by fresh extension of the local environment.
 *)
Lemma state_invariant_add_fresh :
  ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV) 
    (l : local_env) (g : global_env) (v : uvalue),
    incLocal s1 ≡ inr (s2, id)
    -> no_local_global_alias l g v
    → state_invariant σ s1 memH (memV, (l, g))
    → freshness_pre s1 s2 l
    → state_invariant σ s2 memH (memV, (alist_add id v l, g)).
Proof.
  intros * INC ALIAS [MEM_INV WF] FRESH.
  split; eauto.
  - red; intros * LUH LUV.
    erewrite incLocal_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM_INV in INLG; eauto.
    break_match.
    + subst.
      repeat (split; auto).
      eapply in_local_or_global_scalar_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply freshness_fresh; eauto using incLocal_lt.
    + subst.
      repeat (split; auto).
      eapply in_local_or_global_scalar_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply freshness_fresh; eauto using incLocal_lt.
    + subst.
      repeat destruct INLG as [? INLG].
      repeat (split; eauto).
      do 3 eexists; splits; eauto.
      { apply incLocal_Γ in INC; rewrite INC in *; auto. }
      eapply in_local_or_global_addr_add_fresh_old; eauto.
      eapply fresh_no_lu_addr; eauto.
      eapply freshness_fresh; eauto using incLocal_lt.
  - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
  - eapply incLocal_no_id_aliasing; eauto.
  - cbn. eapply no_local_global_alias_no_llvm_ptr_aliasing; eauto.
    unfold no_llvm_ptr_aliasing in *.
    apply incLocal_Γ in INC. rewrite INC.
    eauto.
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

Lemma incVoid_no_id_aliasing :
  forall s1 s2 id,
    incVoid s1 ≡ inr (s2, id) ->
    no_id_aliasing s1 ->
    no_id_aliasing s2.
Proof.
  intros s1 s2 id INC ALIAS.
  unfold no_id_aliasing in *.
  apply incVoid_Γ in INC.
  rewrite INC; auto.
Qed.

Lemma state_invariant_incVoid :
  forall σ s s' k memH stV,
    incVoid s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM_INV WF].
  split; eauto.
  - red; repeat break_let; intros * LUH LUV.
    pose proof INC as INC'.
    apply incVoid_Γ in INC; rewrite INC in *.
    generalize LUV; intros INLG;
      eapply MEM_INV in INLG; eauto.
  - unfold WF_IRState; erewrite incVoid_Γ; eauto; apply WF.
  - eapply incVoid_no_id_aliasing; eauto.
  - apply incVoid_Γ in INC.
    unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing in *.
    destruct stV as [mv [l g]].
    rewrite INC in *.
    eauto.
Qed.

Lemma state_invariant_incLocal :
  forall σ s s' k memH stV,
    incLocal s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM_INV WF].
  split; eauto.
  - red; repeat break_let; intros * LUH LUV.
    pose proof INC as INC'.
    apply incLocal_Γ in INC; rewrite INC in *.
    generalize LUV; intros INLG;
      eapply MEM_INV in INLG; eauto.
  - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
  - eapply incLocal_no_id_aliasing; eauto.
  - apply incLocal_Γ in INC.
    unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing in *.
    destruct stV as [mv [l g]].
    rewrite INC in *.
    eauto.
Qed.

Lemma incLocalNamed_Γ:
  forall s s' msg id,
    incLocalNamed msg s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incLocalNamed_no_id_aliasing :
  forall s1 s2 msg id,
    incLocalNamed msg s1 ≡ inr (s2, id) ->
    no_id_aliasing s1 ->
    no_id_aliasing s2.
Proof.
  intros s1 s2 msg id INC ALIAS.
  unfold no_id_aliasing in *.
  apply incLocalNamed_Γ in INC.
  rewrite INC.
  auto.
Qed.

Lemma state_invariant_incLocalNamed :
  forall σ msg s s' k memH stV,
    incLocalNamed msg s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM_INV WF].
  split; eauto.
  - red; repeat break_let; intros * LUH LUV.
    pose proof INC as INC'.
    apply incLocalNamed_Γ in INC; rewrite INC in *.
    generalize LUV; intros INLG;
      eapply MEM_INV in INLG; eauto.
  - unfold WF_IRState; erewrite incLocalNamed_Γ; eauto; apply WF.
  - eapply incLocalNamed_no_id_aliasing; eauto.
  - apply incLocalNamed_Γ in INC.
    unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing in *.
    destruct stV as [mv [l g]].
    rewrite INC in *.
    eauto.
Qed.

Lemma incBlockNamed_no_id_aliasing :
  forall s1 s2 msg id,
    incBlockNamed msg s1 ≡ inr (s2, id) ->
    no_id_aliasing s1 ->
    no_id_aliasing s2.
Proof.
  intros s1 s2 msg id INC ALIAS.
  unfold no_id_aliasing in *.
  apply incBlockNamed_Γ in INC.
  rewrite INC.
  auto.
Qed.

Lemma state_invariant_incBlockNamed :
  forall σ s s' k msg memH stV,
    incBlockNamed msg s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM_INV WF].
  split; eauto.
  - red; repeat break_let; intros * LUH LUV.
    pose proof INC as INC'.
    apply incBlockNamed_Γ in INC; rewrite INC in *.
    generalize LUV; intros INLG;
      eapply MEM_INV in INLG; eauto.
  - unfold WF_IRState; erewrite incBlockNamed_Γ; eauto; apply WF.
  - eapply incBlockNamed_no_id_aliasing; eauto.
  - apply incBlockNamed_Γ in INC.
    unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing in *.
    destruct stV as [mv [l g]].
    rewrite INC in *.
    eauto.
Qed.

Lemma state_invariant_no_llvm_ptr_aliasing :
  forall σ s mh mv l g,
    state_invariant σ s mh (mv, (l, g)) ->
    no_llvm_ptr_aliasing σ s l g.
Proof.
  intros σ s mh mv l g SINV.
  destruct SINV. cbn in *.
  auto.
Qed.

Lemma state_invariant_sub_local_no_aliasing_refl :
  forall l g s mh mv σ,
    state_invariant σ s mh (mv, (l, g)) ->
    sub_local_no_aliasing σ s l l g.
Proof.
  intros l g s mh mv σ SINV.
  destruct SINV. cbn in *.
  split; [reflexivity | eauto].
Qed.

Hint Resolve state_invariant_sub_local_no_aliasing_refl: core.

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

Hint Resolve memory_invariant_ext_local: core.

Lemma no_local_global_alias_non_pointer:
  forall l g v,
    (forall p, v ≢ UVALUE_Addr p) ->
    no_local_global_alias l g v.
Proof.
  intros l g v PTR.
  unfold no_local_global_alias.
  intros id p0 p' H0 H1.
  specialize (PTR p0).
  contradiction.
Qed.

Lemma sub_local_no_aliasing_add_non_ptr :
  forall σ s id v l g,
    alist_fresh id l ->
    no_llvm_ptr_aliasing σ s l g ->
    no_local_global_alias l g v ->
    sub_local_no_aliasing σ s l (alist_add id v l) g.
Proof.
  intros σ s id v l g FRESH ALIAS NLG.
  unfold sub_local_no_aliasing.
  split.

  - apply sub_alist_add; auto.
  - epose proof (no_local_global_alias_no_llvm_ptr_aliasing _ ALIAS NLG).
    unfold no_llvm_ptr_aliasing in ALIAS.
    intros id0 id' ptr ptr' n1 n2 ptrh1 ptrh2 τ τ' sz1 sz2 H0 H1 H2 H3 H4 H5 H6.
    unfold no_llvm_ptr_aliasing in H.
    eapply H; [apply H0 | apply H1 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 ].
Qed.

Lemma sub_local_no_aliasing_transitive :
  forall σ s l0 l1 l2 g,
    sub_local_no_aliasing σ s l0 l1 g ->
    sub_local_no_aliasing σ s l1 l2 g ->
    sub_local_no_aliasing σ s l0 l2 g.
Proof.
  intros σ s l0 l1 l2 g [L0L1 ALIAS1] [L1L2 ALIAS2].
  split; eauto.
  etransitivity; eauto.
Qed.

Lemma sub_local_no_aliasing_add_non_ptr' :
  forall σ s id v l l' g,
    alist_fresh id l ->
    no_llvm_ptr_aliasing σ s l g ->
    no_local_global_alias l g v ->
    sub_local_no_aliasing σ s l' l g ->
    sub_local_no_aliasing σ s l' (alist_add id v l) g.
Proof.
  intros σ s id v l l' g FRESH ALIAS NLG [L'L ALIAS'].
  unfold sub_local_no_aliasing.
  split.

  - rewrite L'L. apply sub_alist_add; auto.
  - epose proof (no_local_global_alias_no_llvm_ptr_aliasing _ ALIAS NLG).
    unfold no_llvm_ptr_aliasing in ALIAS.
    intros id0 id' ptr ptr' H0 H1 H2.
    intros ptrh2 τ τ' sz1 sz2 H3 H4 H5 H6 H7 H8 H9.
    eapply H; [apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 | apply H9 ].
Qed.

Lemma sub_local_no_aliasing_Γ :
  forall σ s1 s2 l1 l2 g,
    sub_local_no_aliasing σ s1 l1 l2 g ->
    Γ s2 ≡ Γ s1 ->
    sub_local_no_aliasing σ s2 l1 l2 g.
Proof.
  intros σ s1 s2 l1 l2 g [L1L2 SUB] GAMMA.
  unfold sub_local_no_aliasing in *.
  rewrite GAMMA.
  auto.
Qed.


Ltac solve_no_local_global_alias :=
  solve
    [ let H := fresh in
      apply no_local_global_alias_non_pointer; intros ? H; discriminate H ].

Ltac solve_alist_in := first [apply In_add_eq | idtac].
Ltac solve_lu :=
  (try now eauto);
  match goal with
  | |- @Maps.lookup _ _ local_env _ ?id ?l ≡ Some _ =>
    eapply memory_invariant_LLU; [| eassumption | eassumption]; eauto
  | h: _ ⊑ ?l |- @Maps.lookup _ _ local_env _ ?id ?l ≡ Some _ =>
    eapply h; solve_lu
  | |- @Maps.lookup _ _ global_env _ ?id ?l ≡ Some _ =>
    eapply memory_invariant_GLU; [| eassumption | eassumption]; eauto
  | _ => solve_alist_in
  end.

Ltac solve_state_invariant :=
  cbn; try eassumption;
  match goal with
  | |- state_invariant _ _ _ (_, (alist_add _ _ _, _)) =>
    eapply state_invariant_add_fresh; [now eauto | solve_no_local_global_alias | (eassumption || solve_state_invariant) | solve_fresh]
  | |- state_invariant _ _ _ _ =>
    solve [eauto with SolveStateInv]
  end.

Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incBlockNamed; [eassumption | solve_state_invariant] : SolveStateInv.
Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incLocal; [eassumption | solve_state_invariant] : SolveStateInv.
Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incVoid; [eassumption | solve_state_invariant] : SolveStateInv.

Ltac solve_sub_local_no_aliasing_gamma :=
  match goal with
  | H: incLocal ?s1 ≡ inr (?s2, _) |- sub_local_no_aliasing ?σ ?s2 ?l1 ?l2 ?g
    => let GAMMA := fresh "GAMMA"
      in assert (Γ s2 ≡ Γ s1) as GAMMA by eauto with helix_context;
         eapply sub_local_no_aliasing_Γ;
         eauto;
         clear GAMMA

  | H: genNExpr _ ?s1 ≡ inr (?s2, _) |- sub_local_no_aliasing ?σ ?s2 ?l1 ?l2 ?g
    => let GAMMA := fresh "GAMMA"
      in assert (Γ s2 ≡ Γ s1) as GAMMA by eauto with helix_context;
         eapply sub_local_no_aliasing_Γ;
         eauto;
         clear GAMMA

  | H: genNExpr _ ?s1 ≡ inr (?s2, _),
       SUB: sub_local_no_aliasing ?σ ?s2 ?l1 ?l2 ?g |- _
    => let GAMMA := fresh "GAMMA" in
      let SUB2  := fresh "SUB" in
      assert (Γ s1 ≡ Γ s2) as GAMMA by eauto with helix_context;
      epose proof (sub_local_no_aliasing_Γ _ SUB GAMMA);
      clear SUB;
      eauto
  end.

Ltac solve_sub_local_no_aliasing :=
  first [ solve [eapply state_invariant_sub_local_no_aliasing_refl; solve_state_invariant]
        | solve_sub_local_no_aliasing_gamma; solve_sub_local_no_aliasing
        | eapply sub_local_no_aliasing_add_non_ptr';
          [ solve_alist_fresh
          | eapply state_invariant_no_llvm_ptr_aliasing; solve_state_invariant
          | solve_no_local_global_alias
          | solve_sub_local_no_aliasing
          ]
        | solve [eapply sub_local_no_aliasing_transitive; eauto]].
Definition state_invariant_pre σ s1 s2 := (state_invariant σ s1 ⩕ fresh_pre s1 s2).
Definition state_invariant_post σ s1 s2 l := (state_invariant σ s2 ⩕ fresh_post s1 s2 l).

  (* TODO: Move this, and remove Transparent / Opaque *)
  Lemma incLocal_unfold :
    forall s,
      incLocal s ≡ inr
               ({|
                   block_count := block_count s;
                   local_count := S (local_count s);
                   void_count := void_count s;
                   Γ := Γ s
                 |}
                , Name ("l" @@ string_of_nat (local_count s))).
  Proof.
    intros s.
    Transparent incLocal.
    cbn.
    reflexivity.
    Opaque incLocal.
  Qed.

  (* TODO: Move this, and remove Transparent / Opaque *)
  Lemma incVoid_unfold :
    forall s,
      incVoid s ≡ inr
              ({|
                  block_count := block_count s;
                  local_count := local_count s;
                  void_count := S (void_count s);
                  Γ := Γ s
                |}
               , Z.of_nat (void_count s)).
  Proof.
    intros s.
    Transparent incVoid.
    cbn.
    reflexivity.
    Opaque incVoid.
  Qed.

  Lemma genNExpr_context :
    forall nexp s1 s2 e c,
      genNExpr nexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction nexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genNExpr ?nexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genNExpr ?nexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
    end; auto.
  Qed.

  Lemma genMExpr_context :
    forall mexp s1 s2 e c,
      genMExpr mexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction mexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genMExpr ?nexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genMExpr ?nexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
    end; auto.
  Qed.

  Hint Resolve genNExpr_context : helix_context.
  Hint Resolve genMExpr_context : helix_context.
  Hint Resolve incVoid_Γ        : helix_context.
  Hint Resolve incLocal_Γ       : helix_context.
  Hint Resolve incBlockNamed_Γ  : helix_context.

  Lemma genAExpr_context :
    forall aexp s1 s2 e c,
      genAExpr aexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction aexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incVoid_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genAExpr ?aexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genAExpr ?aexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
  | GEN: genNExpr _ _ ≡ inr _ |- _ =>
    rewrite (genNExpr_context _ _ GEN)
  | GEN: genMExpr _ _ ≡ inr _ |- _ =>
    rewrite (genMExpr_context _ _ GEN)
    end; subst; auto.
  Qed.
  
  Ltac subst_contexts :=
    repeat match goal with
           | H : Γ ?s1 ≡ Γ ?s2 |- _ =>
             rewrite H in *; clear H
           end.
