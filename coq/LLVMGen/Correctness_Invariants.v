Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.

From Coq Require Import ZArith.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Import AlistNotations.

Definition gamma_bound (s : IRState) : Prop :=
  forall n id τ,
    nth_error (Γ s) n ≡ Some (ID_Local id, τ) ->
    lid_bound s id.

Lemma gamma_bound_mono :
  forall s1 s2,
    gamma_bound s1 ->
    s1 <<= s2 ->
    Γ s1 ≡ Γ s2 ->
    gamma_bound s2.
Proof.
  intros s1 s2 GAM LT GAMEQ.
  unfold gamma_bound in *.
  intros n id τ NTH.
  eapply state_bound_mono.
  eapply GAM.
  2: solve_local_count.
  rewrite GAMEQ.
  eauto.
Qed.

Lemma gamma_bound_uncons :
  forall s1 s2 x ,
    gamma_bound s1 ->
    s1 <<= s2 ->
    Γ s1 ≡ x :: Γ s2 ->
    gamma_bound s2.
Proof.
  intros s1 s2 x BOUND LT GAM.
  unfold gamma_bound in *.
  intros n id τ NTH.
  eapply state_bound_mono.
  eapply BOUND.
  2: solve_local_count.
  rewrite GAM.
  rewrite nth_error_Sn.
  eauto.
Qed.

Lemma gamma_bound_cons :
  forall s1 s2 x τ,
    gamma_bound s1 ->
    s1 <<= s2 ->
    (ID_Local x, τ) :: Γ s1 ≡ Γ s2 ->
    lid_bound s2 x ->
    gamma_bound s2.
Proof.
  intros s1 s2 x τ BOUND LT GAM LID_BOUND.
  unfold gamma_bound in *.
  intros [|n] id τ' NTH.
  - rewrite <- GAM in NTH.
    cbn in NTH. inv NTH.
    eauto.
  - eapply state_bound_mono.
    eapply BOUND.
    2: solve_local_count.
    rewrite <- GAM in NTH.
    rewrite nth_error_Sn in NTH.
    eauto.
Qed.

Lemma gamma_bound_nil :
  forall s,
    Γ s ≡ [] ->
    gamma_bound s.
Proof.
  intros s H.
  unfold gamma_bound.
  intros n id τ NTH.
  rewrite H in NTH.
  rewrite ListNth.nth_error_nil in NTH.
  inv NTH.
Qed.

Ltac solve_gamma_bound :=
  solve [ eauto
        | apply gamma_bound_nil; solve_gamma
        | eapply gamma_bound_mono; [solve_gamma_bound | solve_local_count | solve_gamma]
        | eapply gamma_bound_uncons; [solve_gamma_bound | solve_local_count | eauto]
        | eapply gamma_bound_cons; [solve_gamma_bound | solve_local_count | cbn; eauto | solve_lid_bound]
        ].

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
    | _           , DSHPtr n => TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval n)) TYPE_Double)
    end.

  (* True if σ typechecks in Γ *)
  Definition evalContext_typechecks (σ : evalContext) (Γ : list (ident * typ)) : Prop :=
    forall v n b, nth_error σ n ≡ Some (v, b) ->
           exists id, (nth_error Γ n ≡ Some (id, getWFType id (DSHType_of_DSHVal v))).

  Definition WF_IRState (σ : evalContext) (s : IRState) : Prop :=
    evalContext_typechecks σ (Γ s).

  Lemma evalContext_typechecks_extend:
    ∀ (σ : evalContext) (s1 s1' : IRState) (x : ident * typ) (v : DSHVal * bool),
      Γ s1' ≡ x :: Γ s1 →
      evalContext_typechecks (v :: σ) (Γ s1') →
      evalContext_typechecks σ (Γ s1).
  Proof.
    intros σ s1 s1' x v H2 H9.
    red. red in H9. intros.
    rewrite H2 in H9. specialize (H9 _ (S n) _ H). cbn in *.
    apply H9.
  Qed.

  Lemma WF_IRState_lookups :
    forall σ s n v id τ b,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (id, τ) ->
      nth_error σ n ≡ Some (v, b) ->
      τ ≡ getWFType id (DSHType_of_DSHVal v).
  Proof.
    intros * WF LU_IR LU_SIGMA.
    apply WF in LU_SIGMA; destruct LU_SIGMA as (id' & LU); rewrite LU in LU_IR; inv LU_IR; eauto.
  Qed.

  Lemma WF_IRState_one_of_local_type:
    forall σ x τ s n v b,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (ID_Local x,τ) ->
      nth_error σ n ≡ Some (v, b) ->
      τ ≡ IntType \/
      τ ≡ TYPE_Double \/
      exists k, τ ≡ TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval k)) TYPE_Double).
  Proof.
    intros * WF LU LU'.
    eapply WF in LU'; destruct LU' as (id & LU''); rewrite LU in LU''; inv LU''.
    cbn; break_match_goal; eauto.
  Qed.

  Lemma WF_IRState_one_of_global_type:
    forall σ x τ s n v b,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (ID_Global x,τ) ->
      nth_error σ n ≡ Some (v, b) ->
      τ ≡ TYPE_Pointer IntType \/
      τ ≡ TYPE_Pointer TYPE_Double \/
      exists k, τ ≡ TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval k)) TYPE_Double).
  Proof.
    intros * WF LU LU'.
    unfold WF_IRState, evalContext_typechecks in WF.
    specialize (WF _ _ _ LU'). cbn in WF.
    edestruct WF as (id & LU''); eauto.
    rewrite LU in LU''; inv LU''.
    cbn in *; eauto.
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
  | h  : nth_error (Γ ?s) _ ≡ Some (?id,?τ),
         h': @nth_error DSHVal ?σ _ ≡ Some ?val
    |- _ =>
    let WF := fresh "WF" in
    assert (WF : WF_IRState σ s) by eauto;
    let H := fresh in pose proof (WF_IRState_lookups _ WF h h') as H; now (destruct id; inv H)
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

Ltac abs_failure :=
  exfalso;
  unfold Dfail, Sfail, lift_Serr in *; cbn in *;
  match goal with
  | h: no_failure (interp_helix (throw _) _) |- _ =>
    exact (failure_helix_throw _ _ h)
  | h: no_failure (interp_helix (ITree.bind (throw _) _) _) |- _ =>
    exact (failure_helix_throw' _ _ _ h)
  | h: no_failure (interp_helix (ITree.bind (Ret _) _)  _) |- _ =>
    eapply no_failure_Ret in h; abs_failure
  end.
Ltac try_abs :=
  try (abs_by_WF || abs_failure).


(* Ltac try_abs := *)
(*   try (abs_by_WF || *)
(*        abs_by failure_helix_throw || abs_by failure_helix_throw'). *)

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

  Definition no_dshptr_aliasing (σ : evalContext) : Prop :=
    forall n n' ptr sz sz' b b',
      nth_error σ n ≡ Some (DSHPtrVal ptr sz, b) ->
      nth_error σ n' ≡ Some (DSHPtrVal ptr sz', b') ->
      n' ≡ n.

  Definition id_allocated (σ : evalContext) (m : memoryH) : Prop :=
    forall n addr val b,
      nth_error σ n ≡ Some (DSHPtrVal addr val, b) ->
      mem_block_exists addr m.

  Definition no_id_aliasing (σ : evalContext) (s : IRState) : Prop :=
    forall n1 n2 id τ τ' v1 v2,
      nth_error σ n1 ≡ Some v1 ->
      nth_error σ n2 ≡ Some v2 ->
      nth_error (Γ s) n1 ≡ Some (id, τ) ->
      nth_error (Γ s) n2 ≡ Some (id, τ') ->
      n2 ≡ n1.

  Definition no_llvm_ptr_aliasing (σ : evalContext) (s : IRState) (ρ : local_env) (g : global_env) : Prop :=
    forall (id1 : ident) (ptrv1 : addr) (id2 : ident) (ptrv2 : addr) n1 n2 τ τ' v1 v2 b b',
      nth_error σ n1 ≡ Some (v1, b) ->
      nth_error σ n2 ≡ Some (v2, b') ->
      nth_error (Γ s) n1 ≡ Some (id1, τ) ->
      nth_error (Γ s) n2 ≡ Some (id2, τ') ->
      id1 ≢ id2 ->
      in_local_or_global_addr ρ g id1 ptrv1 ->
      in_local_or_global_addr ρ g id2 ptrv2 ->
      fst ptrv1 ≢ fst ptrv2.

  Definition no_llvm_ptr_aliasing_cfg (σ : evalContext) (s : IRState) : config_cfg -> Prop :=
    fun '(mv, (ρ, g)) => no_llvm_ptr_aliasing σ s ρ g.

  (* TODO: might not keep this *)
  Definition dshptr_no_block_aliasing (σ : evalContext) ρ g dshp1 (ptrv1 : addr) : Prop :=
    forall dshp2 n2 sz2 s id2 ptrv2 τ b,
      dshp1 ≢ dshp2 ->
      nth_error σ n2 ≡ Some (DSHPtrVal dshp2 sz2, b) ->
      nth_error (Γ s) n2 ≡ Some (id2, τ) ->
      in_local_or_global_addr ρ g id2 ptrv2 ->
      fst ptrv1 ≢ fst ptrv2.

  Lemma incLocal_no_id_aliasing :
    forall s1 s2 id σ,
      incLocal s1 ≡ inr (s2, id) ->
      no_id_aliasing σ s1 ->
      no_id_aliasing σ s2.
  Proof.
    intros s1 s2 id * INC ALIAS.
    unfold no_id_aliasing in *.
    apply incLocal_Γ in INC.
    rewrite INC.
    auto.
  Qed.

  Lemma no_id_aliasing_n_eq :
    forall s σ n n' id τ τ' v v',
      no_id_aliasing σ s ->
      nth_error σ n ≡ Some v ->
      nth_error σ n' ≡ Some v' ->
      nth_error (Γ s) n ≡ Some (id, τ) ->
      nth_error (Γ s) n' ≡ Some (id, τ') ->
      n' ≡ n.
  Proof.
    intros s σ n n' id τ τ' ALIAS N1 N2.
    edestruct ALIAS; eauto.
  Qed.

  Definition no_local_global_alias (l : local_env) (g : global_env) (v : uvalue) : Prop :=
    forall id p p', v ≡ UVALUE_Addr p -> in_local_or_global_addr l g id p' -> fst p ≢ fst p'.

  (* TODO: Move this *)
  Lemma in_local_or_global_addr_neq :
    forall l g id id' v ptr,
      in_local_or_global_addr l g (ID_Local id) ptr ->
      id ≢ id' ->
      in_local_or_global_addr (alist_add id' v l) g (ID_Local id) ptr.
  Proof.
    intros l g id id' v ptr H H0.
    unfold in_local_or_global_addr.
    rewrite alist_find_neq; eauto.
  Qed.

  (* Main memory invariant. Relies on Helix's evaluation context and the [IRState] built by the compiler.
     At any indices, the value and ident/types respectively found are related in that:
     - integers and floats have their translation in the appropriate VIR environment;
     - pointers have a corresponding pointer in the appropriate VIR environment such that they map on identical arrays


SOURCE     result is v
  |
  v
RSHCOL
  | C
  v
FSHCOL   ~ exists y, final mem y == v

forall error, exists p, C(p) is error off from p

SOURCE     result is v
  |
  v

(* FSHCOL   ~ exists y, final mem y == v *)
  |
  v
VELLVM   ~ exists y', final mem' y' == v
final mem y == final mem' y' == v

L1 -C1-> L2 -C2-> L3

forall p1, C1(p1) === p1
forall p2, C2(p2) === p2

C2(C1(p1)) == p1


   *)
  Definition memory_invariant (σ : evalContext) (s : IRState) : Rel_cfg :=
    fun (mem_helix : FHCOL.memory) '(mem_llvm, (ρ,g)) =>
      forall (n: nat) v b τ x,
        nth_error σ n ≡ Some (v, b) ->
        nth_error (Γ s) n ≡ Some (x,τ) ->
        match v with
        | DSHnatVal v   => in_local_or_global_scalar ρ g mem_llvm x (dvalue_of_int v) τ
        | DSHCTypeVal v => in_local_or_global_scalar ρ g mem_llvm x (dvalue_of_bin v) τ
        | DSHPtrVal ptr_helix ptr_size_helix =>
          exists ptr_llvm τ',
          τ ≡ TYPE_Pointer τ' /\
          dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] τ') /\
          in_local_or_global_addr ρ g x ptr_llvm /\
          (b ≡ false ->
          exists bk_helix ,
          memory_lookup mem_helix ptr_helix ≡ Some bk_helix /\
          (forall (i : Int64.int) v, mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v ->
                       get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v)))
        end.

  Definition memory_invariant_partial_write (configV : config_cfg) (index : nat) (ptr_llvm : addr)
             (bk_helix : mem_block) (x : ident) sz : Prop :=
      let '(mem_llvm, (ρ, g)) := configV in
          dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] (TYPE_Array sz TYPE_Double))
              ∧ in_local_or_global_addr ρ g x ptr_llvm
              ∧ (∀ (i : Int64.int) (v0 : binary64),
                  ((MInt64asNT.to_nat i) < N.to_nat sz -> (MInt64asNT.to_nat i) < index) ->
                  mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0
                  → get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0)).

  (* TODO: might be able to simplify this *)
  Definition memory_invariant_partial_single_write (configV : config_cfg) (index : nat) (ptr_llvm : addr) (bk_helix : mem_block) (x : ident) sz : Prop :=
      let '(mem_llvm, (ρ, g)) := configV in
          dtyp_fits mem_llvm ptr_llvm (DTYPE_Array sz DTYPE_Double)
              ∧ in_local_or_global_addr ρ g x ptr_llvm
              ∧ (∀ (v0 : binary64),
                  mem_lookup index bk_helix ≡ Some v0
                  → get_array_cell mem_llvm ptr_llvm index DTYPE_Double ≡ inr (UVALUE_Double v0)).

  (* TODO Prove lemma *)
  (* lookup y (protect σ) ≡ true..? *)

  (* Lookups in [genv] are fully determined by lookups in [Γ] and [σ] *)
  Lemma memory_invariant_GLU : forall σ s v id memH memV t l g n b,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Global id, TYPE_Pointer t) ->
      nth_error σ v ≡ Some (DSHnatVal n, b) ->
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
  Lemma memory_invariant_LLU : forall σ s v id memH memV t l g n b,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHnatVal n, b) ->
      Maps.lookup id l ≡ Some (UVALUE_I64 n).
  Proof.
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
    unfold in_local_or_global_scalar, dvalue_of_int in LU.
    rewrite repr_intval in LU; auto.
  Qed.

  (* Lookups in [local_env] are fully determined by lookups in [vars] and [σ] *)
  Lemma memory_invariant_LLU_AExpr : forall σ s v id memH memV t l g f b,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHCTypeVal f, b) ->
      Maps.lookup id l ≡ Some (UVALUE_Double f).
  Proof.
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
    unfold in_local_or_global_scalar, dvalue_of_int in LU.
    cbn in LU; auto.
  Qed.

  (* Lookups in [genv] are fully determined by lookups in [vars] and [σ] *)
  Lemma memory_invariant_GLU_AExpr : forall σ s v id memH memV t l g f b,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Global id, TYPE_Pointer t) ->
      nth_error σ v ≡ Some (DSHCTypeVal f, b) ->
      exists ptr, Maps.lookup id g ≡ Some (DVALUE_Addr ptr) /\
                  read memV ptr (typ_to_dtyp [] t) ≡ inr (dvalue_to_uvalue (DVALUE_Double f)).
  Proof.
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
    destruct LU as (ptr & τ & EQ & LU & READ); inv EQ.
    exists ptr; split; auto.
  Qed.

  Lemma memory_invariant_LLU_Ptr : forall σ s v id memH memV t l g m size b,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHPtrVal m size, b) ->
      exists ptr_llvm τ',
      t ≡ TYPE_Pointer τ' /\
      dtyp_fits memV ptr_llvm (typ_to_dtyp [] τ') /\
      in_local_or_global_addr l g (ID_Local id) ptr_llvm /\
      (b ≡ false ->
      exists bk_helix ,
      memory_lookup memH m ≡ Some bk_helix /\
      (forall (i : Int64.int) v, mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v ->
                    get_array_cell memV ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v))).
  Proof.
    intros * MEM_INV NTH LU; cbn* in *.
    eapply MEM_INV in LU; clear MEM_INV; eauto.
    auto.
  Qed.

  Lemma ptr_alias_size_eq :
    forall σ n1 n2 sz1 sz2 p b,
      no_dshptr_aliasing σ ->
      nth_error σ n1 ≡ Some (DSHPtrVal p sz1, b) ->
      nth_error σ n2 ≡ Some (DSHPtrVal p sz2, b) ->
      sz1 ≡ sz2.
  Proof.
    intros σ n1 n2 sz1 sz2 p b ALIAS N1 N2.
    pose proof (ALIAS _ _ _ _ _ _ _ N1 N2); subst.
    rewrite N1 in N2; inversion N2.
    auto.
  Qed.

  (** ** General state invariant
      The main invariant carried around combine the two properties defined:
      1. the memories satisfy the invariant;
      2. the [IRState] is well formed;
      3.
   *)
  Record state_invariant (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
    mem_is_inv : memory_invariant σ s memH configV ;
    IRState_is_WF : WF_IRState σ s ;
    st_no_id_aliasing : no_id_aliasing σ s ;
    st_no_dshptr_aliasing : no_dshptr_aliasing σ ;
    st_no_llvm_ptr_aliasing : no_llvm_ptr_aliasing_cfg σ s configV ;
    st_id_allocated : id_allocated σ memH ;
    st_gamma_bound : gamma_bound s
    }.

  (* Predicate stating that an (llvm) local variable is relevant to the memory invariant *)
  Variant in_Gamma : evalContext -> IRState -> raw_id -> Prop :=
  | mk_in_Gamma : forall σ s id τ n v,
      nth_error σ n ≡ Some v ->
      nth_error (Γ s) n ≡ Some (ID_Local id,τ) ->
      WF_IRState σ s ->
      in_Gamma σ s id.

  (* Given a range defined by [s1;s2], ensures that the whole range is irrelevant to the memory invariant *)
  Definition Gamma_safe σ (s1 s2 : IRState) : Prop :=
    forall id, lid_bound_between s1 s2 id ->
               ~ in_Gamma σ s1 id.

  (* Given an initial local env [l1] that reduced to [l2], ensures that no variable relevant to the memory invariant has been modified *)
  Definition Gamma_preserved σ s (l1 l2 : local_env) : Prop :=
    forall id, in_Gamma σ s id ->
               l1 @ id ≡ l2 @ id.

  (* Given an initial local env [l1] that reduced to [l2], and a range given by [s1;s2], ensures
   that all modified variables came from this range *)
  Definition local_scope_modif (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
    fun l2 =>
      forall id,
        alist_find id l2 <> alist_find id l1 ->
        lid_bound_between s1 s2 id.

  (* Given an initial local env [l1] that reduced to [l2], and a range given by [s1;s2], ensures
   that this range has been left untouched *)
  Definition local_scope_preserved (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
    fun l2 => forall id,
        lid_bound_between s1 s2 id ->
        l2 @ id ≡ l1 @ id.

  (* Expresses that only the llvm local env has been modified *)
  Definition almost_pure {R S} : config_helix -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) =>
      mh ≡ mh' /\ mi ≡ m /\ gi ≡ g.

  Definition is_pure {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ≡ l.

  Lemma is_pure_refl:
    forall {R S} memH memV l g n v,
      @is_pure R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
  Proof.
    intros; repeat split; reflexivity.
  Qed.

  Lemma no_llvm_ptr_aliasing_not_in_gamma :
    forall σ s id v l g,
      no_llvm_ptr_aliasing σ s l g ->
      WF_IRState σ s ->
      ~ in_Gamma σ s id ->
      no_llvm_ptr_aliasing σ s (alist_add id v l) g.
  Proof.
    intros σ s id v l g ALIAS WF FRESH.
    unfold no_llvm_ptr_aliasing in *.
    intros id1 ptrv1 id2 ptrv2 n1 n2 τ0 τ' v1 v2 b b' H H0 H1 H2 H3 H4 H5.
    destruct id1, id2.
    - epose proof (ALIAS _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5).
      eauto.
    - epose proof (ALIAS _ _ _ ptrv2 _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4).
      destruct (rel_dec_p id1 id) as [EQ | NEQ]; unfold Eqv.eqv, eqv_raw_id in *.
      + subst.
        assert (in_Gamma σ s id).
        econstructor; eauto.
        exfalso; apply FRESH; auto.
      + eapply H6.
        cbn in *.
        pose proof NEQ.
        rewrite alist_find_neq in H5; auto.
    - epose proof (ALIAS _ ptrv1 _ ptrv2 _ _ _ _ _ _ _ _ H H0 H1 H2 H3).
      destruct (rel_dec_p id0 id).
      + subst.
        assert (in_Gamma σ s id).
        { econstructor.
          2: eapply H1.
          all:eauto.
        }
        exfalso; apply FRESH; auto.
      + cbn in *.
        apply In_add_ineq_iff in H4; eauto.
    - unfold alist_fresh in *.
      destruct (rel_dec_p id0 id).
      + subst.
        destruct (rel_dec_p id1 id).
        * subst.
          contradiction.
        * epose proof (ALIAS _ ptrv1 _ ptrv2 _ _ _ _ _ _ _ _ H H0 H1 H2 H3).
          assert (in_Gamma σ s id).
          { econstructor.
            2: eapply H1.
            all:eauto.
          }
          exfalso; apply FRESH; auto.
      + destruct (rel_dec_p id1 id).
        * subst.
          epose proof (ALIAS _ ptrv1 _ ptrv2 _ _ _ _ _ _ _ _ H H0 H1 H2 H3).
          assert (in_Gamma σ s id).
          econstructor; eauto.
          exfalso; apply FRESH; auto.
        * cbn in *.
          apply In_add_ineq_iff in H4; eauto.
          apply In_add_ineq_iff in H5; eauto.
  Qed.

  Lemma state_invariant_cons :
    forall a x s' s σ mH mV l g,
      s <<= s' ->
      x :: Γ s' ≡ Γ s ->
      state_invariant (a :: σ) s mH (mV, (l, g)) ->
      state_invariant σ s' mH (mV, (l, g)).
  Proof.
    intros * LT GAM INV.
    destruct INV.
    unfold memory_invariant, WF_IRState, no_id_aliasing, no_dshptr_aliasing, no_llvm_ptr_aliasing, id_allocated in *.
    rewrite <- GAM in *.
    cbn in *.
    split; eauto; red; repeat intro.
    - intros. specialize (mem_is_inv0 (S n)).
      cbn in *.
      specialize (mem_is_inv0 _ _ _ _ H H0). destruct v; eauto.
    - red in IRState_is_WF0. specialize (IRState_is_WF0 v (S n)).
      cbn in *. eauto.
    - assert ((S n2) ≡ (S n1) -> n2 ≡ n1) by lia. apply H3.
      eapply st_no_id_aliasing0; eauto.
    - assert ((S n') ≡ (S n) -> n' ≡ n) by lia. apply H1.
      eapply st_no_dshptr_aliasing0; eauto.
    - red in st_no_llvm_ptr_aliasing0.
      specialize (st_no_llvm_ptr_aliasing0 id1 ptrv1 id2 ptrv2 (S n1) (S n2)).
      cbn in *. rewrite <- GAM in *. revert H6. eapply st_no_llvm_ptr_aliasing0; eauto.
    - specialize (st_id_allocated0 (S n)). cbn in *. eauto.
    - unfold gamma_bound in st_gamma_bound0.
      eapply state_bound_mono.
      eapply st_gamma_bound0.
      2: solve_local_count.
      rewrite <- GAM.
      rewrite nth_error_Sn.
      eauto.
  Qed.

  Lemma state_invariant_cons2 :
    forall a b x y s' s σ mH mV l g,
      s <<= s' ->
      x :: y  :: Γ s' ≡ Γ s ->
      state_invariant (a :: b :: σ) s mH (mV, (l, g)) ->
      state_invariant σ s' mH (mV, (l, g)).
  Proof.
    intros * LT GAM INV.
    destruct INV.
    unfold memory_invariant, WF_IRState, no_id_aliasing, no_dshptr_aliasing, no_llvm_ptr_aliasing, id_allocated in *.
    rewrite <- GAM in *.
    cbn in *.
    split; eauto; red; repeat intro.
    - intros. specialize (mem_is_inv0 (S (S n))).
      cbn in *.
      specialize (mem_is_inv0 _ _ _ _ H H0). destruct v; eauto.
    - red in IRState_is_WF0. specialize (IRState_is_WF0 v (S (S n))).
      cbn in *. eauto.
    - assert (S (S n2) ≡ S (S n1) -> n2 ≡ n1) by lia. apply H3.
      eapply st_no_id_aliasing0; eauto.
    - assert (S (S n') ≡ S (S n) -> n' ≡ n) by lia. apply H1.
      eapply st_no_dshptr_aliasing0; eauto.
    - red in st_no_llvm_ptr_aliasing0.
      specialize (st_no_llvm_ptr_aliasing0 id1 ptrv1 id2 ptrv2 (S (S n1)) (S (S n2))).
      cbn in *. rewrite <- GAM in *. revert H6. eapply st_no_llvm_ptr_aliasing0;eauto.
    - specialize (st_id_allocated0 (S (S n))). cbn in *. eauto.
    - unfold gamma_bound in st_gamma_bound0.
      eapply state_bound_mono.
      eapply st_gamma_bound0.
      2: solve_local_count.
      rewrite <- GAM.
      do 2 rewrite nth_error_Sn.
      eauto.
  Qed.

  Lemma state_invariant_cons3 :
    forall a b c x y z s' s σ mH mV l g,
      s <<= s' ->
      x :: y :: z :: Γ s' ≡ Γ s ->
      state_invariant (a :: b :: c :: σ) s mH (mV, (l, g)) ->
      state_invariant σ s' mH (mV, (l, g)).
  Proof.
    intros * LT GAM INV.
    destruct INV.
    unfold memory_invariant, WF_IRState, no_id_aliasing, no_dshptr_aliasing, no_llvm_ptr_aliasing, id_allocated in *.
    rewrite <- GAM in *.
    cbn in *.
    split; eauto; red; repeat intro.
    - intros. specialize (mem_is_inv0 (S (S (S n)))).
      cbn in *.
      specialize (mem_is_inv0 _ _ _ _ H H0). destruct v; eauto.
    - red in IRState_is_WF0. specialize (IRState_is_WF0 v (S (S (S n)))).
      cbn in *. eauto.
    - assert (S (S (S n2)) ≡ S (S (S n1)) -> n2 ≡ n1) by lia. apply H3.
      eapply st_no_id_aliasing0; eauto.
    - assert (S (S (S n')) ≡ S (S (S n)) -> n' ≡ n) by lia. apply H1.
      eapply st_no_dshptr_aliasing0; eauto.
    - red in st_no_llvm_ptr_aliasing0.
      specialize (st_no_llvm_ptr_aliasing0 id1 ptrv1 id2 ptrv2 (S (S (S n1))) (S (S (S n2)))).
      cbn in *. rewrite <- GAM in *. revert H6. eapply st_no_llvm_ptr_aliasing0;eauto.
    - specialize (st_id_allocated0 (S (S (S n)))). cbn in *. eauto.
    - unfold gamma_bound in st_gamma_bound0.
      eapply state_bound_mono.
      eapply st_gamma_bound0.
      2: solve_local_count.
      rewrite <- GAM.
      do 3 rewrite nth_error_Sn.
      eauto.
  Qed.

  (* The memory invariant is stable by evolution of IRStates that preserve Γ *)
  Lemma state_invariant_same_Γ :
    ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV)
      (l : local_env) (g : global_env) (v : uvalue),
      Γ s1 ≡ Γ s2 ->
      s1 <<= s2 ->
      ~ in_Gamma σ s1 id →
      state_invariant σ s1 memH (memV, (l, g)) →
      state_invariant σ s2 memH (memV, (alist_add id v l, g)).
  Proof.
    intros * EQ LT NIN INV; inv INV.
    assert (WF_IRState σ s2) as WF.
    { red; rewrite <- EQ; auto. }
    constructor; auto.
    - cbn; rewrite <- EQ.
      intros * LUH LUV.
      generalize LUV; intros INLG;
        eapply mem_is_inv0 in INLG; eauto.
      destruct v0; cbn in *; auto.
      + destruct x; cbn in *; auto.
        unfold alist_add; cbn.
        break_match_goal.
        * subst.
          rewrite rel_dec_correct in Heqb0; subst.
          exfalso; eapply NIN.
          econstructor; eauto.
        * apply neg_rel_dec_correct in Heqb0.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.
      + destruct x; cbn; auto.
        unfold alist_add; cbn.
        break_match_goal.
        * rewrite rel_dec_correct in Heqb0; subst.
          exfalso; eapply NIN.
          econstructor; eauto.
        * apply neg_rel_dec_correct in Heqb0.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.
      + intros; destruct INLG as (? & ? & ? & ? & ? & ?); eauto.
        destruct x.
        do 2 eexists; split; [eauto | split]; eauto.
        unfold alist_add; cbn.
        break_match_goal.
        * rewrite rel_dec_correct in Heqb0; subst.
          exfalso; eapply NIN.
          econstructor; eauto.
        * apply neg_rel_dec_correct in Heqb0.
          rewrite remove_neq_alist; eauto.
          do 2 eexists; split; [eauto | split]; eauto.

          all: typeclasses eauto.
    - red; rewrite <- EQ; auto.
    - apply no_llvm_ptr_aliasing_not_in_gamma; eauto.
      red; rewrite <- EQ; auto.

      intros INGAMMA.
      destruct INGAMMA.
      apply NIN.
      rewrite <- EQ in H0.
      econstructor; eauto.
    - solve_gamma_bound.
  Qed.

  Lemma state_invariant_same_Γ' :
    ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV)
      (l : local_env) (g : global_env) (v : uvalue),
      Γ s1 ≡ Γ s2 ->
      gamma_bound s2 ->
      ~ in_Gamma σ s1 id →
      state_invariant σ s1 memH (memV, (l, g)) →
      state_invariant σ s2 memH (memV, (alist_add id v l, g)).
  Proof.
    intros * EQ LT NIN INV; inv INV.
    assert (WF_IRState σ s2) as WF.
    { red; rewrite <- EQ; auto. }
    constructor; auto.
    - cbn; rewrite <- EQ.
      intros * LUH LUV.
      generalize LUV; intros INLG;
        eapply mem_is_inv0 in INLG; eauto.
      destruct v0; cbn in *; auto.
      + destruct x; cbn in *; auto.
        unfold alist_add; cbn.
        break_match_goal.
        * subst.
          rewrite rel_dec_correct in Heqb0; subst.
          exfalso; eapply NIN.
          econstructor; eauto.
        * apply neg_rel_dec_correct in Heqb0.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.
      + destruct x; cbn; auto.
        unfold alist_add; cbn.
        break_match_goal.
        * rewrite rel_dec_correct in Heqb0; subst.
          exfalso; eapply NIN.
          econstructor; eauto.
        * apply neg_rel_dec_correct in Heqb0.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.
      + intros; destruct INLG as (? & ? & ? & ? & ? & ?); eauto.
        destruct x.
        do 2 eexists; split; [eauto | split]; eauto.
        unfold alist_add; cbn.
        break_match_goal.
        * rewrite rel_dec_correct in Heqb0; subst.
          exfalso; eapply NIN.
          econstructor; eauto.
        * apply neg_rel_dec_correct in Heqb0.
          rewrite remove_neq_alist; eauto.
          do 2 eexists; split; [eauto | split]; eauto.

          all: typeclasses eauto.
    - red; rewrite <- EQ; auto.
    - apply no_llvm_ptr_aliasing_not_in_gamma; eauto.
      red; rewrite <- EQ; auto.

      intros INGAMMA.
      destruct INGAMMA.
      apply NIN.
      rewrite <- EQ in H0.
      econstructor; eauto.
  Qed.

  Lemma evalContext_typechecks_cons :
    forall σ Γ v id τ b,
      evalContext_typechecks σ Γ ->
      getWFType id (DSHType_of_DSHVal v) ≡ τ ->
      evalContext_typechecks ((v, b) :: σ) ((id, τ) :: Γ).
  Proof.
    intros σ Γ v id τ b TC TYP.
    unfold evalContext_typechecks.
    intros v0 [|n] b0 LUP.
    - cbn in LUP. inv LUP.
      exists id. reflexivity.
    - rewrite nth_error_Sn in LUP.
      rewrite nth_error_Sn.
      apply TC in LUP.
      auto.
  Qed.

  Lemma no_llvm_ptr_aliasing_cons :
    forall s1 s2 l g x σ v,
      no_llvm_ptr_aliasing (v :: σ) s1 l g ->
      Γ s1 ≡ x :: Γ s2 ->
      no_llvm_ptr_aliasing σ s2 l g.
  Proof.
    intros s1 s2 l g x σ v ALIAS EQ.
    red in ALIAS.
    red.
    intros id1 ptrv1 id2 ptrv2 n1 n2 τ τ' v1 v2 b1 b2 NTH_σ1 NTH_σ2 NTH_Γ1 NTH_Γ2 NEQ INLG1 INLG2.

    assert (nth_error (v :: σ) (S n1) ≡ Some (v1, b1)) as NTH_σ1' by auto.
    assert (nth_error (v :: σ) (S n2) ≡ Some (v2, b2)) as NTH_σ2' by auto.

    assert (nth_error (Γ s1) (S n1) ≡ Some (id1, τ)) as NTH_Γ1' by (rewrite EQ; auto).
    assert (nth_error (Γ s1) (S n2) ≡ Some (id2, τ')) as NTH_Γ2' by (rewrite EQ; auto).

    eauto.
  Qed.

  Lemma no_llvm_ptr_aliasing_cons2 :
    forall s1 s2 l g x1 x2 σ hv1 hv2,
      no_llvm_ptr_aliasing (hv1 :: hv2 :: σ) s1 l g ->
      Γ s1 ≡ x1 :: x2 :: Γ s2 ->
      no_llvm_ptr_aliasing σ s2 l g.
  Proof.
    intros s1 s2 l g x1 x2 σ hv1 hv2 ALIAS EQ.
    red in ALIAS.
    red.
    intros id1 ptrv1 id2 ptrv2 n1 n2 τ τ' v1 v2 b1 b2 NTH_σ1 NTH_σ2 NTH_Γ1 NTH_Γ2 NEQ INLG1 INLG2.

    assert (nth_error (hv1 :: hv2 :: σ) (S (S n1)) ≡ Some (v1, b1)) as NTH_σ1' by auto.
    assert (nth_error (hv1 :: hv2 :: σ) (S (S n2)) ≡ Some (v2, b2)) as NTH_σ2' by auto.

    assert (nth_error (Γ s1) (S (S n1)) ≡ Some (id1, τ)) as NTH_Γ1' by (rewrite EQ; auto).
    assert (nth_error (Γ s1) (S (S n2)) ≡ Some (id2, τ')) as NTH_Γ2' by (rewrite EQ; auto).

    eauto.
  Qed.

  Lemma no_llvm_ptr_aliasing_same_block :
    forall {σ s l g n1 n2 v1 v2 id1 id2 τ1 τ2 ptrv1 ptrv2},
      no_llvm_ptr_aliasing σ s l g ->
      nth_error (Γ s) n1 ≡ Some (id1, τ1) ->
      nth_error σ n1 ≡ Some v1 ->
      nth_error (Γ s) n2 ≡ Some (id2, τ2) ->
      nth_error σ n2 ≡ Some v2 ->
      in_local_or_global_addr l g id1 ptrv1 ->
      in_local_or_global_addr l g id2 ptrv2 ->
      fst ptrv1 ≡ fst ptrv2 ->
      id1 ≡ id2.
  Proof.
    intros σ s l g n1 n2 [v1 b1] [v2 b2] id1 id2 τ1 τ2 ptrv1 ptrv2 ALIAS NTH_Γ1 NTH_σ1 NTH_Γ2 NTH_σ2 INLG1 INLG2 BLOCK.
    pose proof (ALIAS id1 ptrv1 id2 ptrv2 n1 n2 τ1 τ2 v1 v2 b1 b2 NTH_σ1 NTH_σ2 NTH_Γ1 NTH_Γ2) as CONTRA.
    destruct id1, id2.
    - (* global + global *)
      pose proof (rel_dec_p id id0) as [EQ | NEQ]; subst; auto.
      assert (ID_Global id ≢ ID_Global id0) as NEQ' by (intros H; inv H; contradiction).
      specialize (CONTRA NEQ' INLG1 INLG2).
      contradiction.
    - (* global + local *)
      assert (ID_Global id ≢ ID_Local id0) as NEQ' by (intros H; inv H; contradiction).
      specialize (CONTRA NEQ' INLG1 INLG2).
      contradiction.
    - (* local + global *)
      assert (ID_Local id ≢ ID_Global id0) as NEQ' by (intros H; inv H; contradiction).
      specialize (CONTRA NEQ' INLG1 INLG2).
      contradiction.
    - (* local + local *)
      pose proof (rel_dec_p id id0) as [EQ | NEQ]; subst; auto.
      assert (ID_Local id ≢ ID_Local id0) as NEQ' by (intros H; inv H; contradiction).
      specialize (CONTRA NEQ' INLG1 INLG2).
      contradiction.
  Qed.


  Lemma state_invariant_memory_invariant :
    forall σ s mH mV l g,
      state_invariant σ s mH (mV,(l,g)) ->
      memory_invariant σ s mH (mV,(l,g)).
  Proof.
    intros * H; inv H; auto.
  Qed.

  (* The memory invariant is stable by extension of the local environment
   if the variable belongs to a Γ safe interval
   *)
  Lemma state_invariant_add_fresh :
    ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV)
      (l : local_env) (g : global_env) (v : uvalue),
      incLocal s1 ≡ inr (s2, id)
      -> WF_IRState σ s2
      -> Gamma_safe σ s1 s2
      -> s1 <<= s2
      → state_invariant σ s1 memH (memV, (l, g))
      → state_invariant σ s2 memH (memV, (alist_add id v l, g)).
  Proof.
    intros * INC SAFE LT INV.
    eapply state_invariant_same_Γ; eauto using lid_bound_between_incLocal.
    symmetry; eapply incLocal_Γ; eauto.
  Qed.

  Lemma incVoid_no_id_aliasing :
    forall s1 s2 id σ,
      incVoid s1 ≡ inr (s2, id) ->
      no_id_aliasing σ s1 ->
      no_id_aliasing σ s2.
  Proof.
    intros s1 s2 id SIG INC ALIAS.
    unfold no_id_aliasing in *.
    apply incVoid_Γ in INC.
    rewrite INC.
    auto.
  Qed.

  Lemma incVoid_no_llvm_ptr_aliasing :
    forall σ s1 s2 id l g,
      incVoid s1 ≡ inr (s2, id) ->
      no_llvm_ptr_aliasing σ s1 l g ->
      no_llvm_ptr_aliasing σ s2 l g.
  Proof.
    intros σ s1 s2 id l g INC ALIAS.
    unfold no_llvm_ptr_aliasing in *.
    apply incVoid_Γ in INC.
    rewrite INC.
    auto.
  Qed.

  Lemma state_invariant_incVoid :
    forall σ s s' k memH stV,
      incVoid s ≡ inr (s', k) ->
      state_invariant σ s memH stV ->
      state_invariant σ s' memH stV.
  Proof.
    intros * INC INV; inv INV.
    split; eauto.
    - red; repeat break_let; intros * LUH LUV.
      assert (Γ s' ≡ Γ s) as GAMMA by (eapply incVoid_Γ; eauto).
      rewrite GAMMA in *.
      generalize LUV; intros INLG;
        eapply mem_is_inv0 in INLG; eauto.
    - unfold WF_IRState; erewrite incVoid_Γ; eauto; apply WF.
    - eapply incVoid_no_id_aliasing; eauto.
    - destruct stV as [m [l g]].
      eapply incVoid_no_llvm_ptr_aliasing; eauto.
    - solve_gamma_bound.
  Qed.

  (* If no change has been made, all changes are certainly in the interval *)
  Lemma local_scope_modif_refl: forall s1 s2 l, local_scope_modif s1 s2 l l.
  Proof.
    intros; red; intros * NEQ.
    contradiction NEQ; auto.
  Qed.

  (* If a single change has been made, we just need to check that it was in the interval *)
  Lemma local_scope_modif_add: forall s1 s2 l r v,
      lid_bound_between s1 s2 r ->
      local_scope_modif s1 s2 l (alist_add r v l).
  Proof.
    intros * BET.
    red; intros * NEQ.
    destruct (rel_dec_p r id).
    - subst; rewrite alist_find_add_eq in NEQ; auto.
    - rewrite alist_find_neq in NEQ; auto.
      contradiction NEQ; auto.
  Qed.

  (* Gives a way to work with multiple changes made to locals *)
  Lemma local_scope_modif_add': forall s1 s2 l l' r v,
      lid_bound_between s1 s2 r ->
      local_scope_modif s1 s2 l l' ->
      local_scope_modif s1 s2 l (alist_add r v l').
  Proof.
    intros * BET MODIF.
    red; intros * NEQ.
    destruct (rel_dec_p r id).
    - subst; rewrite alist_find_add_eq in NEQ; auto.
    - rewrite alist_find_neq in NEQ; auto.
  Qed.

  Lemma local_scope_modif_sub':
    ∀ (s1 s2 : IRState) (l l' : local_env) (r : local_id) (v : uvalue),
      lid_bound_between s1 s2 r → local_scope_modif s1 s2 l (alist_add r v l') → local_scope_modif s1 s2 l l'.
  Proof.
    intros s1 s2 l l' r v BOUND MODIF.

    unfold local_scope_modif in *.
    intros id H.
    pose proof (rel_dec_p id r) as [EQ | NEQ].
    - subst; auto.
    - specialize (MODIF id).
      rewrite alist_find_neq in MODIF; auto.
  Qed.

  Lemma local_scope_modif_sub'_l :
    ∀ (s1 s2 : IRState) (l l' : local_env) (r : local_id) (v : uvalue),
      lid_bound_between s1 s2 r → local_scope_modif s1 s2 (alist_add r v l) l' → local_scope_modif s1 s2 l l'.
  Proof.
    intros s1 s2 l l' r v BOUND MODIF.

    unfold local_scope_modif in *.
    intros id H.
    pose proof (rel_dec_p id r) as [EQ | NEQ].
    - subst; auto.
    - specialize (MODIF id).
      rewrite alist_find_neq in MODIF; auto.
  Qed.

  (* If all changes made are in the empty interval, then no change has been made *)
  Lemma local_scope_modif_empty_scope:
    forall (l1 l2 : local_env) id s,
      local_scope_modif s s l1 l2 ->
      l2 @ id ≡ l1 @ id.
  Proof.
    intros * SCOPE.
    red in SCOPE.
    edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption|].
    exfalso; apply SCOPE in NEQ; clear SCOPE.
    destruct NEQ as (? & ? & ? & ? & ? & ? & ?).
    cbn in *; inv H2.
    lia.
  Qed.

  (* If I know that all changes came from [s2;s3] and that I consider a variable from another interval, then it hasn't changed *)
  Lemma local_scope_modif_out:
    forall (l1 l2 : local_env) id s1 s2 s3,
      s1 << s2 ->
      lid_bound_between s1 s2 id ->
      local_scope_modif s2 s3 l1 l2 ->
      l2 @ id ≡ l1 @ id.
  Proof.
    intros * LT BOUND SCOPE.
    red in SCOPE.
    edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
    exfalso; apply SCOPE in NEQ; clear SCOPE.
    destruct NEQ as (? & ? & ? & ? & ? & ? & ?).
    destruct BOUND as (? & ? & ? & ? & ? & ? & ?).
    cbn in *.
    inv H2; inv H6.
    exfalso; eapply IdLemmas.valid_prefix_neq_differ; [| | | eassumption]; auto.
    lia.
  Qed.

  Lemma local_scope_modif_external :
    forall l1 l2 id s1 s2,
      local_scope_modif s1 s2 l1 l2 ->
      ~ lid_bound_between s1 s2 id ->
      l1 @ id ≡ l2 @ id.
  Proof.
    intros l1 l2 id s1 s2 MODIF NBOUND.
    edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
    exfalso; apply NBOUND; apply MODIF; eauto.
  Qed.

  (* If no change occurred, it left any interval untouched *)
  Lemma local_scope_preserved_refl : forall s1 s2 l,
      local_scope_preserved s1 s2 l l.
  Proof.
    intros; red; intros; reflexivity.
  Qed.

  (* If no change occurred, it left Gamma safe *)
  Lemma Gamma_preserved_refl : forall s1 s2 l,
      Gamma_preserved s1 s2 l l.
  Proof.
    intros; red; intros; reflexivity.
  Qed.

  (* TODO: move this? *)
  Lemma maps_add_neq :
    forall {K} {V} {eqk : K -> K -> Prop} {RD : RelDec eqk} `{RelDec_Correct _ eqk} `{Symmetric _ eqk} `{Transitive _ eqk} (x id : K) (v : V) m,
      ~ eqk id x ->
      Maps.add x v m @ id ≡ m @ id.
  Proof.
    intros K V eqk RD RDC SYM TRANS H x id v m H0.
    cbn. unfold alist_add; cbn.
    rewrite rel_dec_neq_false; eauto.
    eapply remove_neq_alist; eauto.
  Qed.

  Lemma Gamma_preserved_add_not_in_Gamma:
    forall σ s l l' r v,
      Gamma_preserved σ s l l' ->
      ~ in_Gamma σ s r ->
      Gamma_preserved σ s l (Maps.add r v l').
  Proof.
    intros σ s l l' r v PRES NGAM.
    unfold Gamma_preserved in *.
    intros id H.
    assert (id ≢ r) by (intros CONTRA; subst; contradiction).
    setoid_rewrite maps_add_neq; eauto.
  Qed.

  Lemma not_in_gamma_cons :
    forall σ s1 s2 id id' τ v,
      Γ s2 ≡ (ID_Local id', τ) :: Γ s1 ->
      ~ in_Gamma σ s1 id ->
      id ≢ id' ->
      ~ in_Gamma (v :: σ) s2 id.
  Proof.
    intros σ s1 s2 id id' τ v GAM NIN NEQ.
    intros CONTRA.
    inv CONTRA.
    apply NIN.
    rewrite GAM in *.
    destruct n.
    - cbn in *; inv H; inv H0.
      contradiction.
    - esplit; eauto.
      eapply evalContext_typechecks_extend; eauto.
  Qed.

  Lemma not_in_gamma_cons2 :
    ∀ σ s1 s2 id id' id'' τ v1 v2,
      Γ s2 ≡ (ID_Local id', τ) :: (ID_Local id'', τ) :: Γ s1 →
      ~ in_Gamma σ s1 id →
      id ≢ id' →
      id ≢ id'' →
      ~ in_Gamma (v1 :: v2 :: σ) s2 id.
  Proof.
    intros.
    set (s' :=
           {| block_count := block_count s1;
             local_count := local_count s1;
             void_count := void_count s1;
             Γ := (ID_Local id'', τ) :: Γ s1 |}).
    eapply not_in_gamma_cons with (s1 := s').
    rewrite H; reflexivity.
    eapply not_in_gamma_cons.
    reflexivity.
    all: auto.
  Qed.

  (* If I know that an interval leaves Gamma safe, I can shrink it on either side and it still lives Gamma safe *)
  Lemma Gamma_safe_shrink : forall σ s1 s2 s3 s4,
      Gamma_safe σ s1 s4 ->
      Γ s1 ≡ Γ s2 ->
      s1 <<= s2 ->
      s3 <<= s4 ->
      Gamma_safe σ s2 s3.
  Proof.
    unfold Gamma_safe; intros * SAFE EQ LE1 LE2 * (? & s & s' & ? & ? & ? & ?) IN.
    apply SAFE with id.
    exists x, s, s'.
    repeat split; eauto.
    solve_local_count.
    solve_local_count.
    inv IN.
    econstructor.
    eauto.
    rewrite EQ; eauto.
    eapply WF_IRState_Γ; eauto.
  Qed.

  Lemma Gamma_safe_Context_extend :
    forall σ s1 s2,
      Gamma_safe σ s1 s2 ->
      forall s1' s2' x v xτ,
        (local_count s1 <= local_count s1')%nat ->
        (local_count s2 >= local_count s2')%nat ->
        Γ s1' ≡ (ID_Local x, v) :: Γ s1 ->
        Γ s2' ≡ (ID_Local x, v) :: Γ s2 ->
        (∀ id : local_id, lid_bound_between s1' s2' id → x ≢ id) ->
        Gamma_safe (xτ :: σ) s1' s2'.
  Proof.
    intros. do 2 red. intros.
    unfold Gamma_safe in H. red in H.
    inversion H3; subst.
    unfold lid_bound_between, state_bound_between in *.
    eapply H.
    - destruct H5 as (? & ? & ? & ? & ? & ? & ?).
      cbn* in *. inversion e; subst. clear e.
      exists x0, x1. eexists. split; auto.
      split. clear H.
      lia. split; auto. lia.
    - inversion H6; subst.
      econstructor.
      3 : {
        unfold WF_IRState in *.
        clear -H10 H2 H4.

        eapply evalContext_typechecks_extend; eauto.
      }

      rewrite H2 in H9.
      destruct n eqn: n' .
      + cbn in *. inversion H9. subst. specialize (H4 id H5).
        contradiction.
      + cbn in *. Unshelve.
        3 : exact (n - 1)%nat. cbn.
        rewrite Nat.sub_0_r. apply H7. eauto.
      + rewrite H2 in H9. cbn in *. inversion H9. subst.
        destruct n. cbn in *.
        specialize (H4 id H5). inversion H9. subst. contradiction.
        cbn. rewrite Nat.sub_0_r. cbn in *. auto.
  Qed.

  (* If I have modified an interval, other intervals are preserved *)
  Lemma local_scope_preserve_modif:
    forall s1 s2 s3 l1 l2,
      local_scope_modif s2 s3 l1 l2 ->
      local_scope_preserved s1 s2 l1 l2.
  Proof.
    intros * MOD.
    red. intros * BOUND.
    red in MOD.
    edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
    apply MOD in NEQ; clear MOD.
    destruct NEQ as (msg & s & s' & ? & ? & ? & ?).
    cbn in *; inv H2.
    destruct BOUND as (msg' & s' & s'' & ? & ? & ? & ?).
    cbn in *; inv H5.
    destruct s as [a s b]; cbn in *; clear a b.
    destruct s' as [a s' b]; cbn in *; clear a b.
    destruct s1 as [a s1 b]; cbn in *; clear a b.
    destruct s2 as [a s2 b], s3 as [a' s3 b']; cbn in *.
    clear a b a' b'.
    exfalso; eapply IdLemmas.valid_prefix_neq_differ; [| | | eassumption]; auto.
    lia.
  Qed.

  Lemma local_scope_preserve_modif_up :
    forall s1 s2 s3 l1 l2,
      local_scope_modif s1 s2 l1 l2 ->
      local_scope_preserved s2 s3 l1 l2.
  Proof.
    intros * MOD.
    red. intros * BOUND.
    red in MOD.
    edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
    apply MOD in NEQ; clear MOD.
    destruct NEQ as (msg & s & s' & ? & ? & ? & ?).
    cbn in *; inv H2.
    destruct BOUND as (msg' & s' & s'' & ? & ? & ? & ?).
    cbn in *; inv H5.
    destruct s as [a s b]; cbn in *; clear a b.
    destruct s' as [a s' b]; cbn in *; clear a b.
    destruct s1 as [a s1 b]; cbn in *; clear a b.
    destruct s2 as [a s2 b], s3 as [a' s3 b']; cbn in *.
    clear a b a' b'.
    exfalso; eapply IdLemmas.valid_prefix_neq_differ; [| | | eassumption]; auto.
    lia.
  Qed.

  Lemma in_Gamma_Gamma_eq:
    forall σ s1 s2 id,
      Γ s1 ≡ Γ s2 ->
      in_Gamma σ s1 id ->
      in_Gamma σ s2 id.
  Proof.
    intros * EQ IN; inv IN; econstructor; eauto.
    rewrite <- EQ; eauto.
    eapply WF_IRState_Γ; eauto.
  Qed.

  Lemma not_in_Gamma_Gamma_eq:
    forall σ s1 s2 id,
      Γ s1 ≡ Γ s2 ->
      ~ in_Gamma σ s1 id ->
      ~ in_Gamma σ s2 id.
  Proof.
    intros σ s1 s2 id EQ NGAM.
    intros GAM.
    apply NGAM.
    inversion GAM; subst.
    econstructor; eauto.
    rewrite EQ. eauto.
    eapply WF_IRState_Γ; eauto.
  Qed.

  Lemma Gamma_preserved_Gamma_eq:
    forall σ s1 s2 l1 l2,
      Γ s1 ≡ Γ s2 ->
      Gamma_preserved σ s1 l1 l2 ->
      Gamma_preserved σ s2 l1 l2.
  Proof.
    unfold Gamma_preserved. intros * EQ PRE * IN.
    apply PRE.
    eauto using in_Gamma_Gamma_eq.
  Qed.

  (* If an interval is Gamma safe, and that all changes occurred in this interval, then the changes preserved Gamma. *)
  Lemma Gamma_preserved_if_safe :
    forall σ s1 s2 l1 l2,
      Gamma_safe σ s1 s2 ->
      local_scope_modif s1 s2 l1 l2 ->
      Gamma_preserved σ s1 l1 l2.
  Proof.
    intros * GS L.
    red.
    intros ? IN.
    red in GS.
    red in L.
    edestruct @alist_find_eq_dec_local_env as [EQ | NEQ]; [eassumption |].
    exfalso; eapply GS; eauto.
  Qed.

  (* Belonging to an interval can relaxed down *)
  Lemma lid_bound_between_shrink_down :
    forall s1 s2 s3 id,
      s1 <<= s2 ->
      lid_bound_between s2 s3 id ->
      lid_bound_between s1 s3 id.
  Proof.
    intros * LE (? & ? & ? & ? & ? & ? & ?).
    do 3 eexists.
    repeat split; eauto.
    solve_local_count.
  Qed.

  (* Belonging to an interval can relaxed up *)
  Lemma lid_bound_between_shrink_up :
    forall s1 s2 s3 id,
      s2 <<= s3 ->
      lid_bound_between s1 s2 id ->
      lid_bound_between s1 s3 id.
  Proof.
    intros * EQ (? & s & s' & ? & ? & ? & ?).
    do 3 eexists.
    repeat split; eauto.
    solve_local_count.
  Qed.

  Lemma lid_bound_between_shrink :
    ∀ (s1 s2 s3 s4 : IRState) (id : local_id),
      lid_bound_between s2 s3 id →
      s1 <<= s2 →
      s3 <<= s4 ->
      lid_bound_between s1 s4 id.
  Proof.
    intros s1 s2 s3 s4 id H H0 H1.
    eapply lid_bound_between_shrink_down; [|eapply lid_bound_between_shrink_up];
      eauto.
  Qed.

  (* Convenience wrapper over [Gamma_safe_Context_extend]: two var case *)
  Lemma Gamma_safe_Context_extend2 :
    forall σ s1 s2,
      Gamma_safe σ s1 s2 ->
      forall s1' s2' x y v xτ yτ,
        (local_count s1 <= local_count s1')%nat ->
        (local_count s2 >= local_count s2')%nat ->
        Γ s1' ≡ (ID_Local x, v) :: (ID_Local y, v) :: Γ s1 ->
        Γ s2' ≡ (ID_Local x, v) :: (ID_Local y, v) :: Γ s2 ->
        (∀ id : local_id, lid_bound_between s1' s2' id → x ≢ id) ->
        (∀ id : local_id, lid_bound_between s1' s2' id → y ≢ id) ->
        Gamma_safe (xτ :: yτ :: σ) s1' s2'.
  Proof.
    intros * SAFE * LC1 LC2 G1 G2 UNIQ_X UNIQ_Y.
    set (s1'' :=
           {| block_count := block_count s1';
             local_count := local_count s1';
             void_count := void_count s1';
             Γ := (ID_Local y, v) :: Γ s1 |}).
    set (s2'' :=
           {| block_count := block_count s2';
             local_count := local_count s2';
             void_count := void_count s2';
             Γ := (ID_Local y, v) :: Γ s2 |}).

    eapply Gamma_safe_Context_extend with (s1:=s1'') (s2:=s2''); cycle 1.
    solve_local_count.
    solve_local_count.
    now rewrite G1.
    now rewrite G2.
    auto.

    eapply Gamma_safe_Context_extend.
    eapply SAFE.
    solve_local_count.
    solve_local_count.
    reflexivity.
    reflexivity.
    auto.
  Qed.

  (* Transitivity of the changes belonging to intervals *)
  Lemma local_scope_modif_trans :
    forall s1 s2 s3 l1 l2 l3,
      s1 <<= s2 ->
      s2 <<= s3 ->
      local_scope_modif s1 s2 l1 l2 ->
      local_scope_modif s2 s3 l2 l3 ->
      local_scope_modif s1 s3 l1 l3.
  Proof.
    unfold local_scope_modif; intros * LE1 LE2 MOD1 MOD2 * INEQ.
    destruct (alist_find_eq_dec_local_env id l1 l2) as [EQ | NEQ].
    - destruct (alist_find_eq_dec_local_env id l2 l3) as [EQ' | NEQ'].
      + contradiction INEQ; rewrite <- EQ; auto.
      + apply MOD2 in NEQ'.
        eauto using lid_bound_between_shrink_down.
    - apply MOD1 in NEQ.
      eauto using lid_bound_between_shrink_up.
  Qed.

  (* Alternate notion of transitivity, with respect to a fix interval *)
  Lemma local_scope_modif_trans' :
    forall s1 s2 l1 l2 l3,
      local_scope_modif s1 s2 l1 l2 ->
      local_scope_modif s1 s2 l2 l3 ->
      local_scope_modif s1 s2 l1 l3.
  Proof.
    unfold local_scope_modif; intros * MOD1 MOD2 * INEQ.
    destruct (alist_find_eq_dec_local_env id l1 l2) as [EQ | NEQ].
    - destruct (alist_find_eq_dec_local_env id l2 l3) as [EQ' | NEQ'].
      + contradiction INEQ; rewrite <- EQ; auto.
      + apply MOD2 in NEQ'.
        eauto using lid_bound_between_shrink_down.
    - apply MOD1 in NEQ.
      eauto using lid_bound_between_shrink_up.
  Qed.

  Lemma local_scope_modif_trans''' :
    forall s1 s2 s3 l1 l2 l3,
      s1 <<= s2 ->
      s2 <<= s3 ->
      local_scope_modif s2 s3 l1 l2 ->
      local_scope_modif s1 s2 l2 l3 ->
      local_scope_modif s1 s3 l1 l3.
  Proof.
    unfold local_scope_modif; intros * LE1 LE2 MOD1 MOD2 * INEQ.
    destruct (alist_find_eq_dec_local_env id l1 l2) as [EQ | NEQ].
    - destruct (alist_find_eq_dec_local_env id l2 l3) as [EQ' | NEQ'].
      + contradiction INEQ; rewrite <- EQ; auto.
      + apply MOD2 in NEQ'.
        eauto using lid_bound_between_shrink_up.
    - apply MOD1 in NEQ.
      eauto using lid_bound_between_shrink_down.
  Qed.

  Lemma local_scope_modif_shrink :
    forall (s1 s2 s3 s4 : IRState) l1 l2,
      local_scope_modif s2 s3 l1 l2 ->
      s1 <<= s2 ->
      s3 <<= s4 ->
      local_scope_modif s1 s4 l1 l2.
  Proof.
    intros s1 s2 s3 s4 l1 l2 MODIF LT1 LT2.
    unfold local_scope_modif in *.
    intros id NEQ.
    eapply lid_bound_between_shrink; eauto.
  Qed.

  Lemma local_scope_modif_bound_before:
    forall s s1 s2 l1 l2 id,
      local_scope_modif s1 s2 l1 l2 ->
      s <<= s1 ->
      lid_bound s id ->
      alist_find id l1 ≡ alist_find id l2.
  Proof.
    intros s s1 s2 l1 l2 id MODIF LE BOUND.
    unfold local_scope_modif in MODIF.
    eapply state_bound_before_not_bound_between in BOUND.
    2: eapply incLocalNamed_count_gen_injective.
    2: eauto.

    destruct (l1 @ id) as [u1|] eqn:EQ1;
    destruct (l2 @ id) as [u2|] eqn:EQ2.

    - destruct (rel_dec_p u1 u2) as [EQ | NEQ]; subst; auto.
      assert (l2 @ id ≢ l1 @ id).
      { intros CONTRA. rewrite EQ1, EQ2 in CONTRA.
        inv CONTRA. contradiction.
      }

      pose proof (MODIF id H) as BETWEEN.
      instantiate (1 := s2) in BOUND.
      contradiction.
    - assert (l2 @ id ≢ l1 @ id).
      { intros CONTRA. rewrite EQ1, EQ2 in CONTRA.
        inv CONTRA.
      }

      pose proof (MODIF id H) as BETWEEN.
      contradiction.
    - assert (l2 @ id ≢ l1 @ id).
      { intros CONTRA. rewrite EQ1, EQ2 in CONTRA.
        inv CONTRA.
      }

      pose proof (MODIF id H) as BETWEEN.
      contradiction.
    - reflexivity.
  Qed.

  Lemma local_scope_modif_trans'' :
    forall s1 s2 s3 s4 l1 l2 l3,
      local_scope_modif s1 s2 l1 l2 →
      local_scope_modif s3 s4 l2 l3 →
      s1 <<= s2 ->
      s1 <<= s3 ->
      s2 <<= s4 ->
      s3 <<= s4 ->
      local_scope_modif s1 s4 l1 l3.
  Proof.
    unfold local_scope_modif; intros * MOD1 MOD2 LE1 LE2 LE3 LE4 * INEQ.
    destruct (alist_find_eq_dec_local_env id l1 l2) as [EQ | NEQ].
    - destruct (alist_find_eq_dec_local_env id l2 l3) as [EQ' | NEQ'].
      + contradiction INEQ; rewrite <- EQ; auto.
      + apply MOD2 in NEQ'.
        eauto using lid_bound_between_shrink_down.
    - apply MOD1 in NEQ.
      eauto using lid_bound_between_shrink_up.
  Qed.


  Lemma memory_invariant_Ptr : forall vid σ s memH memV l g a size x sz b,
      state_invariant σ s memH (memV, (l, g)) ->
      nth_error σ vid ≡ Some (DSHPtrVal a size, b) ->
      nth_error (Γ s) vid ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
      ∃ (ptr_llvm : Addr.addr),
        dtyp_fits memV ptr_llvm
                    (typ_to_dtyp [] (TYPE_Array sz TYPE_Double))
        ∧ in_local_or_global_addr l g x ptr_llvm /\

        (b ≡ false ->
      exists bk_helix,
        memory_lookup memH a ≡ Some bk_helix
        ∧ (∀ (i : Int64.int) (v : binary64), mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v → get_array_cell memV ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v))).
  Proof.
    intros * MEM LU1 LU2; inv MEM; eapply mem_is_inv0 in LU1; eapply LU1 in LU2; eauto.
    destruct LU2 as (bk & ptr & τ' & ? & ? & ?).
    exists bk. split; eauto. inv τ'. eauto.
  Qed.


  (* Named function pointer exists in global environemnts *)
  Definition global_named_ptr_exists (fnname:string) : Pred_cfg :=
    fun '(mem_llvm, (ρ,g)) => exists mf, g @ (Name fnname) ≡ Some (DVALUE_Addr mf).

  (* Anon pointer exists in global environemnts *)
  Definition global_anon_ptr_exists (id:int) : Pred_cfg :=
    fun '(mem_llvm, (ρ,g)) => exists mf, g @ (Anon id) ≡ Some (DVALUE_Addr mf).

  (* For compiled FHCOL programs we need to ensure we have 2 global function declarations:
     1. "main" function
     2. function, implementing compiled expression.

     We do not state here that their addresses are distinct
     but we have this in [state_invariant].
   *)
  Definition fun_declarations_invariant (fnname:string) : Pred_cfg :=
    fun c => global_named_ptr_exists "main" c /\ global_named_ptr_exists fnname c.

  (* For compiled FHCOL programs we need to ensure we have 2 global anonymous variables exist:
     1. Placeholder for X (Anon 0)
     2. Placeholder for Y (Anon 1)

     We do not state here that their addresses are distinct
     but we have this in [state_invariant].
   *)
  Definition anon_declarations_invariant : Pred_cfg :=
    fun c => global_anon_ptr_exists 0%Z c /\ global_anon_ptr_exists 1%Z c.

  Definition in_global_addr (g : global_env) (x : raw_id) (a : Addr.addr) :=
    g @ x ≡ Some (DVALUE_Addr a).

  Definition genv_ptr_uniq (g : global_env) :=
    ∀ (id id' : raw_id) (ptr ptr' : addr),
      in_global_addr g id ptr →
      in_global_addr g id' ptr' →
      fst ptr ≡ fst ptr' ->
      id ≡ id'.

  Definition genv_mem_bounded (g : global_env) (m : memoryV) :=
    forall id a,
      g @ id ≡ Some (DVALUE_Addr a) ->
      (fst a < next_logical_key m)%Z.

  Definition genv_mem_wf (g : global_env) (m : memoryV) :=
    genv_ptr_uniq g /\ genv_mem_bounded g m.

  Definition genv_mem_wf_cfg : config_cfg -> Prop :=
    fun '(memV, (_, genv)) => genv_mem_wf genv memV.

  (** An invariant which must hold after initialization stage *)
  Record post_init_invariant (fnname:string) (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
      state_inv: state_invariant σ s memH configV;
      fun_decl_inv:  fun_declarations_invariant fnname configV;
      anon_decl_inv: anon_declarations_invariant configV;
      genv_mem_wf_inv: genv_mem_wf_cfg configV
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
      bisim_partial σ s (mem_helix, tt) (mk_config_cfg_T _ (inr v) (m, (ρ, g))).

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

  (* The result is a branch *)
  Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
    match c with
    | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
    end.

  Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env) (gi : global_env)
    : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ s2) ⩕
      branches to ⩕
      (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf)) /\
                       (* global environment remains unchanged (gi - env at start of execution)*)
                       gi ≡ (fst (snd (snd stvf)))).

End SimulationRelations.

Lemma state_invariant_WF_IRState :
  forall σ s memH st, state_invariant σ s memH st -> WF_IRState σ s.
Proof.
  intros ? ? ? (? & ? & ?) INV; inv INV; auto.
Qed.

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

Lemma in_local_or_global_scalar_add_fresh_old :
  forall (id : raw_id) (l : local_env) (g : global_env) m (x : ident) dv dv' τ,
    x <> ID_Local id ->
    in_local_or_global_scalar l g m x dv τ ->
    in_local_or_global_scalar (alist_add id dv' l) g m x dv τ.
Proof.
  intros * INEQ LUV'.
  destruct x; cbn in *; auto.
  unfold alist_add; cbn.
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
  unfold alist_add; cbn.
  rewrite rel_dec_neq_false; try typeclasses eauto; [| intros ->; auto].
  rewrite remove_neq_alist; auto; try typeclasses eauto; intros ->; auto.
Qed.

Lemma append_factor_left : forall s s1 s2,
    s @@ s1 ≡ s @@ s2 ->
    s1 ≡ s2.
Proof.
  induction s as [| c s IH]; cbn; intros * EQ; auto.
  apply IH.
  inv EQ; auto.
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
  - solve_gamma_bound.
Qed.

Lemma incLocalNamed_no_id_aliasing :
  forall s1 s2 msg id σ,
    incLocalNamed msg s1 ≡ inr (s2, id) ->
    no_id_aliasing σ s1 ->
    no_id_aliasing σ s2.
Proof.
  intros s1 s2 msg id * INC ALIAS.
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
  - solve_gamma_bound.
Qed.

Lemma incBlockNamed_no_id_aliasing :
  forall s1 s2 msg id σ,
    incBlockNamed msg s1 ≡ inr (s2, id) ->
    no_id_aliasing σ s1 ->
    no_id_aliasing σ s2.
Proof.
  intros s1 s2 msg id * INC ALIAS.
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
  - solve_gamma_bound.
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

Lemma no_id_aliasing_gamma :
  forall s1 s2 σ,
    no_id_aliasing σ s1 ->
    Γ s1 ≡ Γ s2 ->
    no_id_aliasing σ s2.
Proof.
  intros s1 s2 σ ALIAS GAMMA.
  unfold no_id_aliasing.
  rewrite <- GAMMA.
  auto.
Qed.

Lemma no_llvm_ptr_aliasing_gamma :
  forall σ s1 s2 l g,
    no_llvm_ptr_aliasing σ s1 l g ->
    Γ s1 ≡ Γ s2 ->
    no_llvm_ptr_aliasing σ s2 l g.
Proof.
  intros σ s1 s2 l g ALIAS GAMMA.
  unfold no_llvm_ptr_aliasing.
  rewrite <- GAMMA.
  auto.
Qed.

Lemma state_invariant_Γ :
  forall σ s1 s2 memH stV,
    state_invariant σ s1 memH stV ->
    Γ s2 ≡ Γ s1 ->
    s1 <<= s2 ->
    state_invariant σ s2 memH stV.
Proof.
  intros * INV EQ LT; inv INV.
  split; cbn; eauto.
  - red; rewrite EQ; apply mem_is_inv0.
  - red. rewrite EQ; apply IRState_is_WF0.
  - eapply no_id_aliasing_gamma; eauto.
  - destruct stV as (? & ? & ?); cbn in *; eapply no_llvm_ptr_aliasing_gamma; eauto.
  - solve_gamma_bound.
Qed.

Lemma state_invariant_Γ' :
  forall σ s1 s2 memH stV,
    state_invariant σ s1 memH stV ->
    Γ s2 ≡ Γ s1 ->
    gamma_bound s2 ->
    state_invariant σ s2 memH stV.
Proof.
  intros * INV EQ LT; inv INV.
  split; cbn; eauto.
  - red; rewrite EQ; apply mem_is_inv0.
  - red. rewrite EQ; apply IRState_is_WF0.
  - eapply no_id_aliasing_gamma; eauto.
  - destruct stV as (? & ? & ?); cbn in *; eapply no_llvm_ptr_aliasing_gamma; eauto.
Qed.

Lemma state_invariant_add_fresh' :
  ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV)
    (l : local_env) (g : global_env) (v : uvalue),
    Gamma_safe σ s1 s2
    -> lid_bound_between s1 s2 id
    → state_invariant σ s1 memH (memV, (l, g))
    → state_invariant σ s1 memH (memV, (alist_add id v l, g)).
Proof.
  intros * GAM BOUND INV.
  apply GAM in BOUND.
  eapply state_invariant_same_Γ; eauto.
Qed.

Lemma state_invariant_escape_scope : forall σ v x s1 s2 stH stV,
    Γ s1 ≡ x :: Γ s2 ->
    gamma_bound s2 ->
    state_invariant (v::σ) s1 stH stV ->
    state_invariant σ s2 stH stV.
Proof.
  intros * EQ BOUND [MEM WF ALIAS1 ALIAS2 ALIAS3].
  destruct stV as (? & ? & ?).
  split.
  - red; intros * LU1 LU2.
    red in MEM.
    specialize (MEM (S n)).
    rewrite EQ, 2nth_error_Sn in MEM.
    specialize (MEM _ _ _ _ LU1 LU2).
    destruct v0; cbn; auto.
  - repeat intro.
    do 2 red in WF.
    specialize (WF v0 (S n)).
    cbn in WF.
    specialize (WF _ H).
    edestruct WF as (?id & LU).
    clear WF.
    (* rewrite nth_error_Sn ; eauto. *)
    exists id.
    rewrite EQ in LU. eauto.
    (* rewrite nth_error_Sn in LU;eauto. *)

  - red; intros * LU1 LU2 LU3 LU4.
    specialize (ALIAS1 (S n1) (S n2)).
    rewrite EQ, 2nth_error_Sn in ALIAS1.
    eapply ALIAS1 in LU1; eauto.
  - red; intros * LU1 LU2.
    specialize (ALIAS2 (S n) (S n')).
    rewrite 2nth_error_Sn in ALIAS2.
    eapply ALIAS2 in LU1; eauto.

  - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
    do 2 red in ALIAS3.
    specialize (ALIAS3 id1 ptrv1 id2 ptrv2 (S n1) (S n2)).
    rewrite !EQ, !nth_error_Sn in ALIAS3.
    eapply ALIAS3 in LU1; eauto.

  - red.
    intros * LU.
    eapply (st_id_allocated0 (S n)); eauto.
  - eauto.
Qed.

(* TO MOVE *)
Definition uvalue_of_nat k := UVALUE_I64 (Int64.repr (Z.of_nat k)).

Lemma state_invariant_enter_scope_DSHnat :
  forall σ v prefix x s1 s2 stH mV l g b,
    newLocalVar IntType prefix s1 ≡ inr (s2, x) ->
    is_correct_prefix prefix ->
    ~ in_Gamma σ s1 x ->
    l @ x ≡ Some (uvalue_of_nat v) ->
    state_invariant σ s1 stH (mV,(l,g)) ->
    state_invariant ((DSHnatVal (Int64.repr (Z.of_nat v)), b)::σ) s2 stH (mV,(l,g)).
Proof.
  intros * EQ PREF GAM LU [MEM WF ALIAS1 ALIAS2 ALIAS3]; inv EQ; cbn in *.
  split.
  - red; intros * LU1 LU2.
    destruct n as [| n].
    + cbn in *; inv LU1; inv LU2; auto.
      cbn; rewrite repr_intval; auto.
    + rewrite nth_error_Sn in LU1.
      cbn in *.
      eapply MEM in LU2; eauto.
  -  do 2 red.
     cbn.
     intros ? [| n] * LU'.
     + cbn in LU'.
       inv LU'.
       cbn.
       exists (ID_Local (Name (prefix @@ string_of_nat (local_count s1)))); reflexivity.
     + rewrite nth_error_Sn in LU'.
       rewrite nth_error_Sn.
       apply WF in LU'; auto.

  - red; intros * LU1 LU2 LU3 LU4.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + exfalso. cbn in *.
      apply GAM.
      inv LU3; eapply mk_in_Gamma; eauto.
    + exfalso.
      apply GAM; inv LU4; eapply mk_in_Gamma; eauto.
    + inv LU3; inv LU4; eapply ALIAS1 in LU1; apply LU1 in LU2; eauto.

  - red; intros * LU1 LU2.
    destruct n as [| n], n' as [| n']; auto.
    + inv LU1.
    + inv LU2.
    + rewrite nth_error_Sn in LU1.
      rewrite nth_error_Sn in LU2.
      eapply ALIAS2 in LU1; apply LU1 in LU2; eauto.

  - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
    cbn in *.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + cbn in *. inv LU1; inv LU2; inv LU3; inv LU4; auto.
    + cbn in *; inv LU1; inv LU3; eauto.
      cbn in *.
      rewrite LU in IN1; inv IN1.
    + cbn in *; inv LU2; inv LU4.
      cbn in *; rewrite LU in IN2; inv IN2.
    + cbn in *.
      eapply ALIAS3; [exact LU1 | exact LU2 |..]; eauto.
  - intros [| n] * LUn; [inv LUn |].
    eapply st_id_allocated0; eauto.
  - solve_gamma_bound.
Qed.

Lemma state_invariant_enter_scope_DSHCType :
  forall σ v prefix x s1 s2 stH mV l g b,
    newLocalVar TYPE_Double prefix s1 ≡ inr (s2, x) ->
    is_correct_prefix prefix ->
    ~ in_Gamma σ s1 x ->
    l @ x ≡ Some (UVALUE_Double v) ->
    state_invariant σ s1 stH (mV,(l,g)) ->
    state_invariant ((DSHCTypeVal v, b)::σ) s2 stH (mV,(l,g)).
Proof.
  intros * EQ PREF GAM LU [MEM WF ALIAS1 ALIAS2 ALIAS3]; inv EQ; cbn in *.
  split.
  - red; intros * LU1 LU2.
    destruct n as [| n].
    + cbn in *; inv LU1; inv LU2; auto.
    + rewrite nth_error_Sn in LU1.
      cbn in *.
      eapply MEM in LU2; eauto.
  -  do 2 red.
     cbn.
     intros ? [| n] * LU'.
     + cbn in LU'.
       inv LU'.
       cbn.
       exists (ID_Local (Name (prefix @@ string_of_nat (local_count s1)))); reflexivity.
     + rewrite nth_error_Sn in LU'.
       rewrite nth_error_Sn.
       apply WF in LU'; auto.

  - red; intros * LU1 LU2 LU3 LU4.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + exfalso. cbn in *.
      apply GAM.
      inv LU3; eapply mk_in_Gamma; eauto.
    + exfalso.
      apply GAM; inv LU4; eapply mk_in_Gamma; eauto.
    + inv LU3; inv LU4; eapply ALIAS1 in LU1; apply LU1 in LU2; eauto.

  - red; intros * LU1 LU2.
    destruct n as [| n], n' as [| n']; auto.
    + inv LU1.
    + inv LU2.
    + rewrite nth_error_Sn in LU1.
      rewrite nth_error_Sn in LU2.
      eapply ALIAS2 in LU1; apply LU1 in LU2; eauto.

  - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
    cbn in *.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + cbn in *. inv LU1; inv LU2; inv LU3; inv LU4; auto.
    + cbn in *; inv LU1; inv LU3; eauto.
      cbn in *.
      rewrite LU in IN1; inv IN1.
    + cbn in *; inv LU2; inv LU4.
      cbn in *; rewrite LU in IN2; inv IN2.
    + cbn in *.
      eapply ALIAS3; [exact LU1 | exact LU2 |..]; eauto.
  - intros [| n] * LUn; [inv LUn |].
    eapply st_id_allocated0; eauto.
  - solve_gamma_bound.
Qed.

Lemma state_invariant_enter_scope_DSHCType' :
  forall σ v b x s1 s2 stH mV l g τ,
    τ ≡ getWFType (ID_Local x) DSHCType ->
    Γ s2 ≡ (ID_Local x,τ) :: Γ s1 ->
    lid_bound s2 x ->

    (* Freshness *)
    ~ in_Gamma σ s1 x ->
    s1 <<= s2 ->

    l @ x ≡ Some (UVALUE_Double v) ->
    state_invariant σ s1 stH (mV,(l,g)) ->
    state_invariant ((DSHCTypeVal v, b)::σ) s2 stH (mV,(l,g)).
Proof.
  intros * TYP EQ LID_BOUND GAM LT LU [MEM WF ALIAS1 ALIAS2 ALIAS3]; cbn in TYP; inv TYP.
  split.
  - red; intros * LU1 LU2.
    rewrite EQ in *.
    destruct n as [| n].
    + inv LU1; inv LU2; auto.
    + rewrite nth_error_Sn in LU1.
      cbn in *.
      eapply MEM in LU2; eauto.
  -  do 2 red.
     rewrite EQ.
     cbn.
     intros ? [| n] * LU'.
     + cbn in LU'.
       inv LU'.
       cbn.
       exists (ID_Local x); reflexivity.
     + rewrite nth_error_Sn in LU'.
       rewrite nth_error_Sn.
       apply WF in LU'; auto.

  - red; intros * LU1 LU2 LU3 LU4.
    rewrite EQ in *.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + exfalso. cbn in *.
      apply GAM.
      inv LU3; eapply mk_in_Gamma; eauto.
    + exfalso.
      apply GAM; inv LU4; eapply mk_in_Gamma; eauto.
    + inv LU3; inv LU4; eapply ALIAS1 in LU1; apply LU1 in LU2; eauto.

  - red; intros * LU1 LU2.
    destruct n as [| n], n' as [| n']; auto.
    + inv LU1.
    + inv LU2.
    + rewrite nth_error_Sn in LU1.
      rewrite nth_error_Sn in LU2.
      eapply ALIAS2 in LU1; apply LU1 in LU2; eauto.

  - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
    rewrite EQ in *.
    cbn in *.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + cbn in *. inv LU1; inv LU2; inv LU3; inv LU4; auto.
    + cbn in *; inv LU1; inv LU3; eauto.
      cbn in *.
      rewrite LU in IN1; inv IN1.
    + cbn in *; inv LU2; inv LU4.
      cbn in *; rewrite LU in IN2; inv IN2.
    + cbn in *.
      eapply ALIAS3; [exact LU1 | exact LU2 |..]; eauto.
  - intros [| n] * LUn; [inv LUn |].
    eapply st_id_allocated0; eauto.
  - solve_gamma_bound.
Qed.

Lemma state_invariant_enter_scope_DSHCType'2 :
  forall σ vx vy b x y s1 s2 stH mV l g τx τy,
    x ≢ y ->
    τx ≡ getWFType (ID_Local x) DSHCType ->
    τy ≡ getWFType (ID_Local y) DSHCType ->
    Γ s2 ≡ (ID_Local x,τx) :: (ID_Local y,τy) :: Γ s1 ->
    lid_bound s2 x ->
    lid_bound s2 y ->

    (* Freshness *)
    ~ in_Gamma σ s1 x ->
    ~ in_Gamma σ s1 y ->
    s1 <<= s2 ->

    l @ x ≡ Some (UVALUE_Double vx) ->
    l @ y ≡ Some (UVALUE_Double vy) ->
    state_invariant σ s1 stH (mV,(l,g)) ->
    state_invariant ((DSHCTypeVal vx, b)::(DSHCTypeVal vy, b)::σ) s2 stH (mV,(l,g)).
Proof.
  intros * NEQ TYP_X TYP_Y EQ LID_BOUND_X LID_BOUND_Y
             GAM_X GAM_Y LT LU_X LU_Y [MEM WF ALIAS1 ALIAS2 ALIAS3].
    cbn in TYP_X, TYP_Y; subst.
  split.
  - red; intros * LU1 LU2.
    rewrite EQ in *.
    destruct n as [| [| n]].
    + inv LU1; inv LU2; auto.
    + inv LU1; inv LU2; auto.
    + rewrite !nth_error_Sn in LU1.
      cbn in *.
      eapply MEM in LU2; eauto.
  -  do 2 red.
     rewrite EQ.
     cbn.
     intros ? [| [| n]] * LU'.
     + cbn in LU'.
       inv LU'.
       cbn.
       exists (ID_Local x); reflexivity.
     + cbn in LU'.
       inv LU'.
       cbn.
       exists (ID_Local y); reflexivity.
     + rewrite !nth_error_Sn in LU'.
       rewrite nth_error_Sn.
       apply WF in LU'; auto.

  - red; intros * LU1 LU2 LU3 LU4.
    clear MEM.
    rewrite EQ in *.
    destruct n1 as [| [| n1]], n2 as [| [| n2]]; auto.
    all: cbn in *; repeat find_inversion.
    all: try now contradict NEQ.
    all: try solve [exfalso; eapply GAM_X; eapply mk_in_Gamma; eauto].
    all: try solve [exfalso; eapply GAM_Y; eapply mk_in_Gamma; eauto].
    do 2 f_equal.
    eauto.
  - red; intros * LU1 LU2.
    destruct n as [| [| n]], n' as [| [| n']]; auto.
    all: cbn in *; repeat find_inversion.
    do 2 f_equal.
    eauto.
  - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
    rewrite EQ in *.
    cbn in *.
    destruct n1 as [| [| n1]], n2 as [| [| n2]]; auto.
    all: cbn in *; repeat find_inversion; cbn in *.
    all: try first [rewrite LU_X in IN1 | rewrite LU_Y in IN1].
    all: try first [rewrite LU_X in IN2 | rewrite LU_Y in IN2].
    all: repeat find_inversion.
    eauto.
  - intros [| [| n]] * LUn; inv LUn.
    eapply st_id_allocated0; eauto.
  -
    unfold gamma_bound.
    rewrite EQ.
    intros [| [| n]] * LUn; inv LUn.
    all: solve_lid_bound.
Qed.

Lemma state_invariant_enter_scope_DSHPtr :
  forall σ ptrh sizeh ptrv x τ s1 s2 stH mV mV_a l g b,
    τ ≡ getWFType (ID_Local x) (DSHPtr sizeh) ->
    Γ s2 ≡ (ID_Local x,τ) :: Γ s1 ->
    lid_bound s2 x ->

    (* Freshness *)
    ~ in_Gamma σ s1 x ->
    s1 <<= s2 ->

    (* ~ In (ID_Local x) (map fst (Γ s2)) ->          (* The new ident is fresh *) *)
    (forall sz b, ~ In ((DSHPtrVal ptrh sz), b) σ) -> (* The new Helix address is fresh *)

    (* We know that a certain ptr has been allocated *)
    allocate mV (DTYPE_Array (Z.to_N (Int64.intval sizeh)) DTYPE_Double) ≡ inr (mV_a, ptrv) ->

    state_invariant σ s1 stH (mV,(l,g)) ->

    state_invariant ((DSHPtrVal ptrh sizeh, b) :: σ) s2
                    (memory_set stH ptrh mem_empty)
                    (mV_a, (alist_add x (UVALUE_Addr ptrv) l,g)).
Proof.
  Opaque add_logical_block. Opaque next_logical_key.
  intros * -> EQ LID_BOUND GAM LT fresh alloc [MEM WF ALIAS1 ALIAS2 ALIAS3 ALLOC].
  split.
  - red; intros * LU1 LU2.
    destruct n as [| n].
    + rewrite EQ in LU2; cbn in *.
      inv LU1; inv LU2; eauto.
      eexists ptrv. eexists.
      split; auto.
      split. red.
      inv alloc.
      rewrite get_logical_block_of_add_to_frame. cbn.
      rewrite get_logical_block_of_add_logical_block.

      auto. eexists. eexists. eexists. split; auto.
      reflexivity. cbn. rewrite typ_to_dtyp_D_array. cbn. lia.
      split; auto. inv alloc.
      red.
      rewrite alist_find_add_eq. reflexivity.
      inv alloc.
      intros. inversion H.
      exists mem_empty.

      split; auto.
      apply memory_lookup_memory_set_eq.
      intros. inv H1.

    + pose proof LU1 as LU1'.
      pose proof LU2 as LU2'.
      rewrite nth_error_Sn in LU1.
      rewrite EQ, nth_error_Sn in LU2.
      eapply MEM in LU2; eauto.

      (* There is some reasoning on the memory (on [alloc] in particular) to be done here *)
      (* I've allocated a new pointer, and added it to the local environment.
       *)
      pose proof (allocate_correct alloc) as (ALLOC_FRESH & ALLOC_NEW & ALLOC_OLD).
      { destruct v.
        - destruct x0.
          + (* The only complication here is read mV_a *)
            destruct LU2 as (ptr & τ' & TEQ & G & READ).
            exists ptr. exists τ'.
            repeat (split; auto).
            erewrite ALLOC_OLD; eauto.

            eapply can_read_allocated; eauto.
            eapply freshly_allocated_no_overlap_dtyp; eauto.
            eapply can_read_allocated; eauto.
          + cbn. cbn in LU2.
            destruct (Eqv.eqv_dec_p x id) as [EQid | NEQid].
            * do 2 red in EQid; subst.
              (* Need a contradiction *)
              exfalso. apply GAM.
              rewrite EQ, nth_error_Sn in LU2'.
              econstructor; eauto.
            * unfold Eqv.eqv, eqv_raw_id in NEQid.
              rewrite alist_find_neq; eauto.
        - destruct x0.
          + (* The only complication here is read mV_a *)
            destruct LU2 as (ptr & τ' & TEQ & G & READ).
            exists ptr. exists τ'.
            repeat (split; auto).
            erewrite ALLOC_OLD; eauto.

            eapply can_read_allocated; eauto.
            eapply freshly_allocated_no_overlap_dtyp; eauto.
            eapply can_read_allocated; eauto.
          + cbn. cbn in LU2.
            destruct (Eqv.eqv_dec_p x id) as [EQid | NEQid].
            * do 2 red in EQid; subst.
              (* Need a contradiction *)
              exfalso. apply GAM.
              rewrite EQ, nth_error_Sn in LU2'.
              econstructor; eauto.
            * unfold Eqv.eqv, eqv_raw_id in NEQid.
              rewrite alist_find_neq; eauto.
        - intros; destruct LU2 as (ptr_llvm & τ' & MLUP & TEQ & FITS & GET); auto.
          (* & INLG & GET); auto. *)
          (* exists bkh. *)
          exists ptr_llvm. exists τ'.
          assert (ptrh ≢ a) as NEQa.
          { intros CONTRA.
            subst.
            apply nth_error_In in LU1.
            apply (fresh size b0). auto.
          }
          repeat (split; eauto).
          (* + rewrite memory_lookup_memory_set_neq; auto. *)
          + eapply dtyp_fits_after_allocated; eauto.
          + destruct x0; auto.
            destruct (Eqv.eqv_dec_p x id) as [EQid | NEQid].
            * do 2 red in EQid; subst.
              exfalso. apply GAM.
              rewrite EQ, nth_error_Sn in LU2'.
              econstructor; eauto.
            * unfold Eqv.eqv, eqv_raw_id in NEQid.
              cbn.
              rewrite alist_find_neq; eauto.
          + intros. destruct (GET H) as ( ? & ? & ?).
            exists x1. split.
            rewrite memory_lookup_memory_set_neq; auto.
            intros i v H'.
            unfold get_array_cell in *.

            (* TODO: is there a better way to do this...? *)
            assert ((let
                       '(b, o) := ptr_llvm in
                     match get_logical_block mV_a b with
                     | Some (LBlock _ bk _) => get_array_cell_mem_block bk o (MInt64asNT.to_nat i) 0 DTYPE_Double
                     | None => failwith "Memory function [get_array_cell] called at a non-allocated address"
                     end) ≡
                     (
                         match get_logical_block mV_a (fst ptr_llvm) with
                         | Some (LBlock _ bk _) => get_array_cell_mem_block bk (snd ptr_llvm) (MInt64asNT.to_nat i) 0 DTYPE_Double
                         | None => failwith "Memory function [get_array_cell] called at a non-allocated address"
                         end)).
            { destruct ptr_llvm. cbn. reflexivity. }

            assert ((let
                       '(b, o) := ptr_llvm in
                     match get_logical_block mV b with
                     | Some (LBlock _ bk _) => get_array_cell_mem_block bk o (MInt64asNT.to_nat i) 0 DTYPE_Double
                     | None => failwith "Memory function [get_array_cell] called at a non-allocated address"
                     end) ≡
                     (
                         match get_logical_block mV (fst ptr_llvm) with
                         | Some (LBlock _ bk _) => get_array_cell_mem_block bk (snd ptr_llvm) (MInt64asNT.to_nat i) 0 DTYPE_Double
                         | None => failwith "Memory function [get_array_cell] called at a non-allocated address"
                         end)).
            { destruct ptr_llvm. cbn. reflexivity. }

            rewrite H2.
            erewrite get_logical_block_allocated.
            rewrite <- H3.
            eauto.
            eauto.
            eapply dtyp_fits_allocated; eauto.
      }

  - do 2 red.
    intros ? [| n] * LU.
    + cbn in LU.
      inv LU.
      rewrite EQ; cbn; eauto.
      exists (ID_Local x). cbn. reflexivity.
    + rewrite nth_error_Sn in LU.
      rewrite EQ,nth_error_Sn.
      apply WF in LU; auto.

  - red; intros * LU1 LU2 LU3 LU4.
    destruct n1 as [| n1], n2 as [| n2]; auto.

    + exfalso.
      inv LU1; rewrite EQ in LU3; inv LU3.
      rewrite EQ in LU4.
      cbn in LU2.
      cbn in LU4.
      apply GAM; eapply mk_in_Gamma; eauto.

    + exfalso.
      inv LU2; rewrite EQ in LU4; inv LU4.
      rewrite EQ in LU3.
      apply GAM; eapply mk_in_Gamma; eauto.

    + rewrite EQ in LU3,LU4; cbn in *.
      f_equal. eapply ALIAS1; eauto.

  - red; intros * LU1 LU2.
    destruct n as [| n], n' as [| n']; auto.
    + cbn in *. inv LU1. exfalso.
      inv alloc.
      eapply fresh.
      apply nth_error_In in LU2. eauto.
    + cbn in *. inv LU2. exfalso.
      eapply fresh.
      apply nth_error_In in LU1. eauto.
    + cbn in *.
      f_equal; eapply ALIAS2; eauto.

  - cbn in ALIAS3.
    do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.

    rewrite EQ in *.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + (* Both pointers are the same *)
      inv LU1; inv LU2; inv LU3; inv LU4.
      contradiction.
    + (* One pointer from Γ s2, one from Γ s1 *)
      inv LU3.
      unfold WF_IRState, evalContext_typechecks in WF.
      pose proof LU2.
      cbn in H.
      apply WF in H.
      destruct H. cbn in LU4. rewrite LU4 in H.
      cbn in H.
      inv H.

      apply alist_In_add_eq in IN1.
      inv IN1.
      epose proof (MEM _ _ _ _ _ LU2 LU4).
      destruct v2.
      * destruct x0.
        -- destruct H as (ptr & τ' & TEQ & G & READ).
           inv TEQ.
           rewrite typ_to_dtyp_I in READ.
           rewrite IN2 in G. inv G.
           apply can_read_allocated in READ.
           eapply freshly_allocated_different_blocks in alloc; eauto.
        -- assert (x ≢ id) as NEQ by (intros CONTRA; subst; contradiction).
           apply In_add_ineq_iff in IN2; auto.
           unfold alist_In in IN2.
           cbn in H.
           rewrite IN2 in H.
           inv H.
      * destruct x0.
        -- destruct H as (ptr & τ' & TEQ & G & READ).
           inv TEQ.
           rewrite typ_to_dtyp_D in READ.
           rewrite IN2 in G. inv G.
           apply can_read_allocated in READ.
           eapply freshly_allocated_different_blocks in alloc; eauto.
        -- assert (x ≢ id) as NEQ by (intros CONTRA; subst; contradiction).
           apply In_add_ineq_iff in IN2; auto.
           unfold alist_In in IN2.
           cbn in H.
           rewrite IN2 in H.
           inv H.
      * cbn in LU1. inv LU1.
        cbn in LU2.
        destruct H as (τ' & MLUP & WFT & FITS & INLG & GETARRAY).
        (* reflexivity. *)
        destruct x0.
        -- cbn in INLG. rewrite IN2 in INLG. inv INLG.
           apply dtyp_fits_allocated in FITS.
           eapply freshly_allocated_different_blocks in alloc; eauto.
        -- assert (x ≢ id) as NEQ by (intros CONTRA; subst; contradiction).
           apply In_add_ineq_iff in IN2; auto.
           unfold alist_In in IN2.
           cbn in INLG.
           rewrite IN2 in INLG.
           inv INLG.
           apply dtyp_fits_allocated in FITS.
           eapply freshly_allocated_different_blocks in alloc; eauto.
    + (* One pointer from Γ s2, one from Γ s1 *)
      inv LU4.
      unfold WF_IRState, evalContext_typechecks in WF.
      pose proof LU1.
      apply WF in H.
      destruct H. cbn in LU3. rewrite LU3 in H.
      cbn in H.
      inv H.

      apply alist_In_add_eq in IN2.
      inv IN2.
      epose proof (MEM _ _ _ _ _ LU1 LU3).
      destruct v1.
      * destruct x0.
        -- destruct H as (ptr & τ' & TEQ & G & READ).
           inv TEQ.
           rewrite typ_to_dtyp_I in READ.
           rewrite IN1 in G. inv G.
           apply can_read_allocated in READ.
           eapply freshly_allocated_different_blocks in alloc; eauto.
        -- assert (x ≢ id) as NEQ by (intros CONTRA; subst; contradiction).
           apply In_add_ineq_iff in IN1; auto.
           unfold alist_In in IN1.
           cbn in H.
           rewrite IN1 in H.
           inv H.
      * destruct x0.
        -- destruct H as (ptr & τ' & TEQ & G & READ).
           inv TEQ.
           rewrite typ_to_dtyp_D in READ.
           rewrite IN1 in G. inv G.
           apply can_read_allocated in READ.
           eapply freshly_allocated_different_blocks in alloc; eauto.
        -- assert (x ≢ id) as NEQ by (intros CONTRA; subst; contradiction).
           apply In_add_ineq_iff in IN1; auto.
           unfold alist_In in IN1.
           cbn in H.
           rewrite IN1 in H.
           inv H.
      * destruct H as (ptr & τ' & WFT & FITS & INLG & GET).
        destruct x0.
        -- cbn in INLG. rewrite IN1 in INLG. inv INLG.
           apply dtyp_fits_allocated in FITS.
           eapply freshly_allocated_different_blocks in alloc; eauto.
        -- assert (x ≢ id) as NEQ by (intros CONTRA; subst; contradiction).
           apply In_add_ineq_iff in IN1; auto.
           unfold alist_In in IN1.
           cbn in INLG.
           rewrite IN1 in INLG.
           inv INLG.
           apply dtyp_fits_allocated in FITS.
           eapply freshly_allocated_different_blocks in alloc; eauto.
    + (* Both pointers from Γ s1, can fall back to assumption (ALIAS3) *)
      rewrite nth_error_Sn in LU1, LU2.
      rewrite nth_error_Sn in LU3, LU4.
      assert (id2 ≢ id1) as INEQ' by auto.

      eapply (no_llvm_ptr_aliasing_not_in_gamma (UVALUE_Addr ptrv) ALIAS3 WF GAM).

      eapply LU1.
      eapply LU2.
      all: eauto.
  - unfold id_allocated.
    intros n addr0 val ba H.
    destruct n.
    + cbn in H. inv H.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    + cbn in H.
      pose proof (nth_error_In _ _ H).
      assert (addr0 ≢ ptrh) as NEQ.
      { intros CONTRA; subst.
        apply fresh in H0.
        contradiction.
      }

      apply (@mem_block_exists_memory_set_neq _ _ stH mem_empty NEQ).
      eauto.
  - solve_gamma_bound.
Qed.

Lemma protect_nil :
  forall n,
    protect [] n ≡ [].
Proof.
  destruct n; auto.
Qed.

Lemma protect_cons_S :
  forall p σ n,
    protect (p :: σ) (S n) ≡ p :: protect σ n.
Proof.
  intros p σ n.
  unfold protect.
  rewrite nth_error_Sn.
  break_match; auto.
  destruct p0; auto.
Qed.

Lemma nth_error_protect_neq :
  forall n1 n2 σ,
    n1 ≢ n2 ->
    nth_error (protect σ n2) n1 ≡ nth_error σ n1.
Proof.
  induction n1; intros n2 σ NEQ.
  - cbn. destruct n2; try contradiction.
    unfold protect. cbn.
    destruct σ; auto.
    cbn.
    destruct (nth_error σ n2); auto.
    destruct p0; reflexivity.
  - destruct σ.
    + rewrite protect_nil.
      reflexivity.
    + cbn. destruct n2; cbn.
      * destruct p. reflexivity.
      * rewrite protect_cons_S.
        auto.
Qed.

Lemma nth_error_protect_eq :
  forall n σ v b',
    nth_error (protect σ n) n ≡ Some (v, b') ->
    exists b, nth_error σ n ≡ Some (v, b).
Proof.
  induction n;
    intros σ v b' NTH.
  - destruct σ; cbn in *; inv NTH.
    destruct p. inv H0.
    eexists. reflexivity.
  - destruct σ.
    + inv NTH.
    + rewrite protect_cons_S in NTH.
      rewrite nth_error_Sn in NTH.
      apply IHn in NTH.
      destruct NTH as [b NTH].
      eexists; eauto.
Qed.

Lemma nth_error_protect_eq' :
  forall n σ v b,
    nth_error σ n ≡ Some (v, b) ->
    nth_error (protect σ n) n ≡ Some (v, true).
Proof.
  induction n;
    intros σ v b NTH.
  - destruct σ; cbn in *; inv NTH.
    reflexivity.
  - destruct σ.
    + inv NTH.
    + rewrite protect_cons_S.
      rewrite nth_error_Sn in NTH.
      rewrite nth_error_Sn.
      eauto.
Qed.


Lemma nth_error_protect_ineq :
  forall n n' σ v b,
    n' <> n ->
    nth_error σ n ≡ Some (v, b) ->
    nth_error (protect σ n') n ≡ Some (v, b).
Proof.
  intros. rewrite <- H0. clear H0.
  revert n' H σ. induction n.
  - intros. cbn. destruct σ eqn: Hσ. unfold protect. cbn.
    destruct (nth_error [] n') eqn: Hn. destruct p. reflexivity. auto.
    unfold protect. cbn.
    destruct (nth_error (p :: l) n') eqn: Hn. destruct p0.
    destruct n'. lia. reflexivity. reflexivity.
  - intros. destruct σ eqn: Hσ. unfold protect. cbn.
    destruct (nth_error [] n') eqn: Hn. destruct p. reflexivity. reflexivity.
    destruct n'. cbn. destruct p. reflexivity.
    rewrite protect_cons_S.
    rewrite nth_error_Sn.
    rewrite nth_error_Sn. eapply IHn. lia.
Qed.

Lemma WF_IRState_protect :
  forall n σ s,
    WF_IRState (protect σ n) s <->
    WF_IRState σ s.
Proof.
  unfold WF_IRState, evalContext_typechecks.
  intros n σ s.
  split; intros.
  - destruct (Nat.eq_dec n n0); subst.
    + apply nth_error_protect_eq' in H0.
      eauto.
    + erewrite <- nth_error_protect_neq in H0; eauto.
  - destruct (Nat.eq_dec n n0); subst.
    + apply nth_error_protect_eq in H0 as [b' NTH].
      eauto.
    + rewrite nth_error_protect_neq in H0; eauto.
Qed.

Lemma not_in_gamma_protect :
  forall σ s id n,
    ~ in_Gamma σ s id ->
    ~ in_Gamma (protect σ n) s id.
Proof.
  intros σ s id n NIN.
  intros CONTRA; inv CONTRA.
  apply NIN.

  destruct (Nat.eq_dec n n0); subst.
  - destruct v.
    pose proof (nth_error_protect_eq n0 σ H) as [b' NTH].
    econstructor; eauto.
    eapply WF_IRState_protect; eauto.
  - rewrite nth_error_protect_neq in H; eauto.
    econstructor; eauto.
    eapply WF_IRState_protect; eauto.
Qed.

Lemma Gamma_safe_protect :
  forall σ s1 s2 n,
    Gamma_safe σ s1 s2 ->
    Gamma_safe (protect σ n) s1 s2.
Proof.
  unfold Gamma_safe.
  intros σ s1 s2 n H id H0.
  apply not_in_gamma_protect.
  eauto.
Qed.

Lemma protect_eq_true :
  forall n σ v b,
    nth_error (protect σ n) n ≡ Some (v, b) ->
    b ≡ true.
Proof.
  induction n;
    intros σ v b NTH; cbn in NTH.
  - destruct σ; cbn in NTH; inv NTH.
    destruct p. inv H0.
    reflexivity.
  - destruct σ; cbn in NTH; inv NTH.
    rewrite protect_cons_S in H0.
    eauto.
Qed.

Lemma memory_invariant_protect :
  forall σ s mH mV l g hid,
    memory_invariant σ s mH (mV, (l, g)) ->
    memory_invariant (protect σ hid) s mH (mV, (l, g)).
Proof.
  intros σ s mH mV l g hid MINV.
  unfold memory_invariant in *.
  intros n v b τ x NTH_σ NTH_Γ.

  destruct (Nat.eq_dec hid n); subst.
  - pose proof (protect_eq_true _ _ NTH_σ); subst.
    eapply nth_error_protect_eq in NTH_σ as [b' NTH_σ].
    pose proof (MINV n v b' τ x NTH_σ NTH_Γ).
    destruct v; eauto.

    destruct H as (ptrll & τ' & TEQ & FITS & INLG & LUP).
    inv TEQ.
    exists ptrll. exists τ'.
    repeat split; auto.
    intros CONTRA. inv CONTRA.
  - erewrite nth_error_protect_neq in NTH_σ; eauto.
    pose proof (MINV n v b τ x NTH_σ NTH_Γ).
    eauto.
Qed.

Lemma no_id_aliasing_protect :
  forall σ s hid,
    no_id_aliasing σ s <->
    no_id_aliasing (protect σ hid) s.
Proof.
  intros σ s hid;
    split; intros H.
  {
    unfold no_id_aliasing in *.
    intros n1 n2 id τ τ' v1 v2 NTH_σ1 NTH_σ2 NTH_Γ1 NTH_Γ2.

    destruct (Nat.eq_dec hid n1), (Nat.eq_dec hid n2); subst; auto.
    - (* hid = n1 *)
      erewrite nth_error_protect_neq in NTH_σ2; [|eauto].
      destruct v1.
      eapply nth_error_protect_eq in NTH_σ1 as [b' NTH_σ1].
      eauto.
    - (* hid = n2 *)
      erewrite nth_error_protect_neq in NTH_σ1; [|eauto].
      destruct v2.
      eapply nth_error_protect_eq in NTH_σ2 as [b' NTH_σ2].
      eauto.
    - (* hid = neither *)
      erewrite nth_error_protect_neq in NTH_σ1; [|eauto].
      erewrite nth_error_protect_neq in NTH_σ2; [|eauto].
      eauto.
  }
  {
    unfold no_id_aliasing in *.
    intros n1 n2 id τ τ' v1 v2 NTH_σ1 NTH_σ2 NTH_Γ1 NTH_Γ2.

    destruct (Nat.eq_dec hid n1), (Nat.eq_dec hid n2); subst; auto.
    - (* hid = n1 *)
      erewrite <- nth_error_protect_neq with (n2 := n1) in NTH_σ2; [|eauto].
      destruct v1.
      eapply nth_error_protect_eq' in NTH_σ1.
      eauto.
    - (* hid = n2 *)
      erewrite <- nth_error_protect_neq with (n2 := n2) in NTH_σ1; [|eauto].
      destruct v2.
      eapply nth_error_protect_eq' in NTH_σ2.
      eauto.
    - (* hid = neither *)
      erewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ1; [|eauto].
      erewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ2; [|eauto].
      eauto.
  }
Qed.

Lemma no_dshptr_aliasing_protect :
  forall σ hid,
    no_dshptr_aliasing σ <->
    no_dshptr_aliasing (protect σ hid).
Proof.
  intros σ hid;
    split; intros H.
  {
    unfold no_dshptr_aliasing in *.
    intros n1 n2 ptr sz sz' b b' NTH_σ1 NTH_σ2.
    destruct (Nat.eq_dec hid n1), (Nat.eq_dec hid n2); subst; auto.
    - (* hid = n1 *)
      erewrite nth_error_protect_neq in NTH_σ2; [|eauto].
      eapply nth_error_protect_eq in NTH_σ1 as [? NTH_σ1].
      eauto.
    - (* hid = n2 *)
      erewrite nth_error_protect_neq in NTH_σ1; [|eauto].
      eapply nth_error_protect_eq in NTH_σ2 as [? NTH_σ2].
      eauto.
    - (* hid = neither *)
      erewrite nth_error_protect_neq in NTH_σ1; [|eauto].
      erewrite nth_error_protect_neq in NTH_σ2; [|eauto].
      eauto.
  }
  {
    unfold no_dshptr_aliasing in *.
    intros n1 n2 ptr sz sz' b b' NTH_σ1 NTH_σ2.

    destruct (Nat.eq_dec hid n1), (Nat.eq_dec hid n2); subst; auto.
    - (* hid = n1 *)
      erewrite <- nth_error_protect_neq with (n2 := n1) in NTH_σ2; [|eauto].
      eapply nth_error_protect_eq' in NTH_σ1.
      eauto.
    - (* hid = n2 *)
      erewrite <- nth_error_protect_neq with (n2 := n2) in NTH_σ1; [|eauto].
      eapply nth_error_protect_eq' in NTH_σ2.
      eauto.
    - (* hid = neither *)
      erewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ1; [|eauto].
      erewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ2; [|eauto].
      eauto.
  }
Qed.

Lemma no_llvm_ptr_aliasing_protect :
  forall σ hid s l g,
    no_llvm_ptr_aliasing σ s l g <->
    no_llvm_ptr_aliasing (protect σ hid) s l g.
Proof.
  intros σ hid; split; intros H.
  {
    unfold no_llvm_ptr_aliasing in *.
    intros id1 ptrv1 id2 ptrv2 n1 n2 τ τ' v1 v2 b b' NTH_σ1 NTH_σ2 H3 H4 H5 H6 H7.

    destruct (Nat.eq_dec hid n1), (Nat.eq_dec hid n2); subst.
    - (* hid = n1 = n2 *)
      eapply nth_error_protect_eq in NTH_σ1 as [? NTH_σ1].
      eapply nth_error_protect_eq in NTH_σ2 as [? NTH_σ2].
      eauto.
    - (* hid = n1 *)
      erewrite nth_error_protect_neq in NTH_σ2; [|eauto].
      eapply nth_error_protect_eq in NTH_σ1 as [? NTH_σ1].
      eauto.
    - (* hid = n2 *)
      erewrite nth_error_protect_neq in NTH_σ1; [|eauto].
      eapply nth_error_protect_eq in NTH_σ2 as [? NTH_σ2].
      eauto.
    - (* hid = neither *)
      erewrite nth_error_protect_neq in NTH_σ1; [|eauto].
      erewrite nth_error_protect_neq in NTH_σ2; [|eauto].
      eauto.
  }
  {
    unfold no_llvm_ptr_aliasing in *.
    intros id1 ptrv1 id2 ptrv2 n1 n2 τ τ' v1 v2 b b' NTH_σ1 NTH_σ2 H3 H4 H5 H6 H7.

    destruct (Nat.eq_dec hid n1), (Nat.eq_dec hid n2); subst; auto.
    - (* hid = n1 = n2 *)
      eapply nth_error_protect_eq' in NTH_σ1.
      eapply nth_error_protect_eq' in NTH_σ2.
      eauto.
    - (* hid = n1 *)
      erewrite <- nth_error_protect_neq with (n2 := n1) in NTH_σ2; [|eauto].
      eapply nth_error_protect_eq' in NTH_σ1.
      eauto.
    - (* hid = n2 *)
      erewrite <- nth_error_protect_neq with (n2 := n2) in NTH_σ1; [|eauto].
      eapply nth_error_protect_eq' in NTH_σ2.
      eauto.
    - (* hid = neither *)
      erewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ1; [|eauto].
      erewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ2; [|eauto].
      eauto.
  }
Qed.

Lemma id_allocated_protect :
  forall σ hid mh,
    id_allocated σ mh <->
    id_allocated (protect σ hid) mh.
Proof.
  intros σ hid mh; split; intros H.
  {
    unfold id_allocated in *.
    intros n addr0 val b NTH.
    destruct (Nat.eq_dec hid n); subst.
    - eapply nth_error_protect_eq in NTH as [b' NTH].
      eauto.
    - erewrite nth_error_protect_neq in NTH; eauto.
  }
  {
    unfold id_allocated in *.
    intros n addr0 val b NTH.
    destruct (Nat.eq_dec hid n); subst.
    - eapply nth_error_protect_eq' in NTH.
      eauto.
    - erewrite <- nth_error_protect_neq in NTH; eauto.
  }
Qed.

Lemma state_invariant_protect :
  forall σ hid s mh cv,
    state_invariant σ s mh cv ->
    state_invariant (protect σ hid) s mh cv.
Proof.
  intros σ hid s mh cv H.
  destruct H, cv, p.
  split.
  - eapply memory_invariant_protect; eauto.
  - eapply WF_IRState_protect; eauto.
  - apply no_id_aliasing_protect; eauto.
  - apply no_dshptr_aliasing_protect; eauto.
  - apply no_llvm_ptr_aliasing_protect; eauto.
  - apply id_allocated_protect; eauto.
  - eauto.
Qed.


Lemma write_state_invariant_protected :
  forall σ s mH mV1 mV2 l g dst_addr (id_addr : ident) sz v ptrll n addr_h sz_h,
    state_invariant (protect σ n) s mH (mV1, (l, g)) ->
    nth_error (Γ s) n ≡ Some (id_addr, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
    nth_error (protect σ n) n ≡ Some (DSHPtrVal addr_h sz_h, true) ->
    in_local_or_global_addr l g id_addr ptrll ->
    fst ptrll ≡ fst dst_addr ->
    write mV1 dst_addr v ≡ inr mV2 ->
    dvalue_has_dtyp v DTYPE_Double ->
    state_invariant (protect σ n) s mH (mV2, (l, g)).
Proof.
  intros σ s mH mV1 mV2 l g dst_addr id_addr sz v ptrll n addr_h sz_h SINV NTH_Γ NTH_σ INLG BLOCK WRITE DTYP.
  destruct SINV.
  split.

  unfold memory_invariant in *.

  intros n0 v0 b0 τ0 x NTH_σ0 NTH_Γ0.
  { (* Memory invariant *)
    destruct (Nat.eq_dec n0 n); subst.
    - (* n = n0 *)
      pose proof (mem_is_inv0 _ _ _ (TYPE_Pointer (TYPE_Array sz TYPE_Double)) id_addr NTH_σ NTH_Γ).
      rewrite NTH_σ in NTH_σ0; inv NTH_σ0.
      destruct H as (ptr & τ' & TEQ & FIND & INLG' & LUP).
      exists ptr. eexists.
      rewrite NTH_Γ0 in NTH_Γ. inv NTH_Γ.
      repeat split; auto. inv TEQ. eauto.
      eapply dtyp_fits_after_write; eauto.
      intros CONTRA; inv CONTRA.
    - pose proof (mem_is_inv0 _ _ _ _ x NTH_σ0 NTH_Γ0).
      eauto.
      destruct x, v0; cbn in *; eauto.
      + destruct H as (ptr & τ' & TEQ & FIND & READ).
        exists ptr. exists τ'.
        repeat split; eauto.
        eauto.

        (* id can not be id_addr because of the different
                     type, and thus must be in a different block *)

        (* Find τ' *)
        pose proof (IRState_is_WF0 _ _ _ NTH_σ0) as (id' & NTH_Γ0').
        rewrite NTH_Γ0 in NTH_Γ0'; inv NTH_Γ0'.
        cbn in H1. inv H1.

        eapply write_different_blocks; eauto.
        2: reflexivity.
        2: { typ_to_dtyp_simplify. constructor. }

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ.
        eapply NTH_σ0.
        eapply NTH_Γ.
        eapply NTH_Γ0.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
      + destruct H as (ptr & τ' & TEQ & FIND & READ).
        exists ptr. exists τ'.
        repeat split; eauto.

        (* id can not be id_addr because of the different
                     type, and thus must be in a different block *)

        (* Find τ' *)
        pose proof (IRState_is_WF0 _ _ _ NTH_σ0) as (id' & NTH_Γ0').
        rewrite NTH_Γ0 in NTH_Γ0'; inv NTH_Γ0'.
        cbn in H1. inv H1.

        eapply write_different_blocks; eauto.
        2: reflexivity.
        2: { typ_to_dtyp_simplify. constructor. }

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ.
        eapply NTH_σ0.
        eapply NTH_Γ.
        eapply NTH_Γ0.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
      + (* Global vector *)
        destruct H as (ptr & τ' & TEQ & FITS & INLG' & LUP).
        inv TEQ.
        exists ptr. exists τ'.
        repeat split; eauto.
        eapply dtyp_fits_after_write; eauto.
        intros H; destruct b0; inv H.
        specialize (LUP eq_refl).
        destruct LUP as (bkh & MLUP_bk & GETARRAYCELL).
        exists bkh.
        split; eauto.
        intros i v0 H.
        specialize (GETARRAYCELL _ _ H).

        erewrite write_untouched_ptr_block_get_array_cell; eauto.

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ0.
        eapply NTH_σ.
        eapply NTH_Γ0.
        eapply NTH_Γ.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
      + (* Local vector *)
        destruct H as (ptr & τ' & TEQ & FITS & INLG' & LUP).
        inv TEQ.
        exists ptr. exists τ'.
        repeat split; eauto.
        eapply dtyp_fits_after_write; eauto.
        intros H; destruct b0; inv H.
        specialize (LUP eq_refl).
        destruct LUP as (bkh & MLUP_bk & GETARRAYCELL).
        exists bkh.
        split; eauto.
        intros i v0 H.
        specialize (GETARRAYCELL _ _ H).

        erewrite write_untouched_ptr_block_get_array_cell; eauto.

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ0.
        eapply NTH_σ.
        eapply NTH_Γ0.
        eapply NTH_Γ.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
  }

  all : try eauto.
Qed.

Lemma st_no_dshptr_aliasing_neq :
  forall σ,
    no_dshptr_aliasing σ ->
      ∀ (n n' ptr1 ptr2 : nat) (sz sz' : Int64.int) (b b' : bool),
        nth_error σ n ≡ Some (DSHPtrVal ptr1 sz, b)
        → nth_error σ n' ≡ Some (DSHPtrVal ptr2 sz', b') →
        ptr1 ≢ ptr2 ->
        n' ≢ n.
Proof.
  intros σ H n n' ptr1 ptr2 sz sz' b b' H0 H1 H2.
  unfold no_dshptr_aliasing in *.
  intros N.
  subst.
  rewrite H0 in H1.
  inv H1.
  contradiction.
Qed.

Lemma write_state_invariant :
  forall σ s mH mV1 mV2 l g dst_addr (id_addr : ident) sz v ptrll n b addr_h sz_h,
    state_invariant σ s mH (mV1, (l, g)) ->
    nth_error (Γ s) n ≡ Some (id_addr, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
    nth_error σ n ≡ Some (DSHPtrVal addr_h sz_h, b) ->
    in_local_or_global_addr l g id_addr ptrll ->
    fst ptrll ≡ fst dst_addr ->
    write mV1 dst_addr v ≡ inr mV2 ->
    dvalue_has_dtyp v DTYPE_Double ->
    state_invariant (protect σ n) s mH (mV2, (l, g)).
Proof.
  intros σ s mH mV1 mV2 l g dst_addr id_addr sz v ptrll n b addr_h sz_h SINV NTH_Γ NTH_σ INLG BLOCK WRITE DTYP.
  destruct SINV.
  split.

  unfold memory_invariant in *.

  intros n0 v0 b0 τ0 x NTH_σ0 NTH_Γ0.
  { (* Memory invariant *)
    destruct (Nat.eq_dec n n0); subst.
    - (* n = n0 *)
      pose proof (protect_eq_true _ _ NTH_σ0); subst.
      eapply nth_error_protect_eq in NTH_σ0 as [b' NTH_σ0].
      rewrite NTH_Γ in NTH_Γ0; inv NTH_Γ0.
      pose proof (mem_is_inv0 n0 v0 b' (TYPE_Pointer (TYPE_Array sz TYPE_Double)) x NTH_σ0 NTH_Γ).
      rewrite NTH_σ in NTH_σ0; inv NTH_σ0.
      destruct H as (ptr & τ' & TEQ & FIND & INLG' & LUP); inv TEQ.
      exists ptr. eexists.
      repeat split; auto.
      eapply dtyp_fits_after_write; eauto.
      intros CONTRA; inv CONTRA.
    - rewrite nth_error_protect_neq in NTH_σ0; auto.
      pose proof (mem_is_inv0 n0 v0 b0 τ0 x NTH_σ0 NTH_Γ0).
      eauto.
      destruct x, v0; cbn in *; eauto.
      + destruct H as (ptr & τ' & TEQ & FIND & READ).
        exists ptr. exists τ'.
        repeat split; eauto.

        (* id can not be id_addr because of the different
                     type, and thus must be in a different block *)

        (* Find τ' *)
        pose proof (IRState_is_WF0 _ _ _ NTH_σ0) as (id' & NTH_Γ0').
        rewrite NTH_Γ0 in NTH_Γ0'; inv NTH_Γ0'.
        cbn in H1. inv H1.

        eapply write_different_blocks; eauto.
        2: reflexivity.
        2: { typ_to_dtyp_simplify. constructor. }

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ.
        eapply NTH_σ0.
        eapply NTH_Γ.
        eapply NTH_Γ0.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
      + destruct H as (ptr & τ' & TEQ & FIND & READ).
        exists ptr. exists τ'.
        repeat split; eauto.

        (* id can not be id_addr because of the different
                     type, and thus must be in a different block *)

        (* Find τ' *)
        pose proof (IRState_is_WF0 _ _ _ NTH_σ0) as (id' & NTH_Γ0').
        rewrite NTH_Γ0 in NTH_Γ0'; inv NTH_Γ0'.
        cbn in H1. inv H1.

        eapply write_different_blocks; eauto.
        2: reflexivity.
        2: { typ_to_dtyp_simplify. constructor. }

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ.
        eapply NTH_σ0.
        eapply NTH_Γ.
        eapply NTH_Γ0.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
      + (* Global vector *)
        destruct H as (ptr & τ' & TEQ & FITS & INLG' & LUP).
        inv TEQ.
        exists ptr. exists τ'.
        repeat split; eauto.
        eapply dtyp_fits_after_write; eauto.
        intros H; destruct b0; inv H.
        specialize (LUP eq_refl).
        destruct LUP as (bkh & MLUP_bk & GETARRAYCELL).
        exists bkh.
        split; eauto.
        intros i v0 H.
        specialize (GETARRAYCELL _ _ H).

        erewrite write_untouched_ptr_block_get_array_cell; eauto.

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ0.
        eapply NTH_σ.
        eapply NTH_Γ0.
        eapply NTH_Γ.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
      + (* Local vector *)
        destruct H as (ptr & τ' & TEQ & FITS & INLG' & LUP).
        inv TEQ.
        exists ptr. exists τ'.
        repeat split; eauto.
        eapply dtyp_fits_after_write; eauto.
        intros H; destruct b0; inv H.
        specialize (LUP eq_refl).
        destruct LUP as (bkh & MLUP_bk & GETARRAYCELL).
        exists bkh.
        split; eauto.
        intros i v0 H.
        specialize (GETARRAYCELL _ _ H).

        erewrite write_untouched_ptr_block_get_array_cell; eauto.

        rewrite <- BLOCK.
        eapply st_no_llvm_ptr_aliasing0.
        eapply NTH_σ0.
        eapply NTH_σ.
        eapply NTH_Γ0.
        eapply NTH_Γ.
        2-3: eauto.
        intros CONTRA; inv CONTRA.
        assert (n ≡ n0).
        { eapply st_no_id_aliasing0; eauto. }
        subst.
        contradiction.
  }

  - eapply WF_IRState_protect; eauto.
  - apply no_id_aliasing_protect; eauto.
  - apply no_dshptr_aliasing_protect; eauto.
  - apply no_llvm_ptr_aliasing_protect; eauto.
  - apply id_allocated_protect; eauto.
  - solve_gamma_bound.
Qed.

Lemma id_allocated_memory_set :
  forall σ mH addr mb,
    id_allocated σ mH ->
    id_allocated σ (memory_set mH addr mb).
Proof.
  intros σ mH addr0 mb H.
  unfold id_allocated in *.
  intros n addr1 val b H0.
  apply mem_block_exists_memory_set.
  eauto.
Qed.

(* TODO: tactics? *)
Ltac solve_allocated :=
  solve [ eauto
        | eapply dtyp_fits_allocated; eauto
        | eapply handle_gep_addr_allocated; cycle 1; [solve [eauto] | solve_allocated]
        | eapply write_preserves_allocated; cycle 1; [solve [eauto] | solve_allocated]
        | eapply id_allocated_memory_set; eauto
        ].

Ltac solve_read :=
  solve [ eauto
        (* This is largely for cases where sizeof_dtyp t <> 0 -> read ... *)
        | match goal with
          | H: _ |- _ => apply H
          end; cbn; lia
        | (* read from an array *)
        erewrite read_array; cycle 2; [solve [eauto] | | solve_allocated]; eauto
        ].

Lemma state_invariant_write_double_result :
  forall σ s hid mH mV mV_init l g v mb mb_old dst_addr_h ptrll (dst_addr : addr) dst_size_h b_hid y id_addr sz sz',
    state_invariant (protect σ hid) s mH (mV, (l, g)) ->
    nth_error (Γ s) hid ≡ Some (id_addr, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
    nth_error σ hid ≡ Some (DSHPtrVal dst_addr_h dst_size_h, b_hid) ->
    in_local_or_global_addr l g id_addr ptrll ->
    ext_memory mV_init dst_addr DTYPE_Double (UVALUE_Double v) mV ->
    handle_gep_addr (DTYPE_Array sz' DTYPE_Double) ptrll
                    [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat (MInt64asNT.to_nat y)))] ≡
                    inr dst_addr ->
    (∀ x : nat, x ≢ MInt64asNT.to_nat y → mem_lookup x mb ≡ mem_lookup x mb_old) ->
    mem_lookup (MInt64asNT.to_nat y) mb ≡ Some v ->
    (* TODO: update this *)
    (∀ (i : MInt64asNT.t) (v : binary64),
        (MInt64asNT.to_nat i ≢ MInt64asNT.to_nat y)
        → mem_lookup (MInt64asNT.to_nat i) mb_old ≡ Some v
        → get_array_cell mV ptrll (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v)) ->
    state_invariant σ s (memory_set mH dst_addr_h mb) (mV, (l, g)).
Proof.
  intros σ s hid mH mV mV_init l g v mb mb_old dst_addr_h ptrll_dst dst_addr dst_size_h b_hid y id_addr sz sz' SINV NTH_Γ_hid NTH_σ_hid INLG [MEXT_NEW MEXT_OLD] GEP MLUP_OLD MLUP_NEW MGAC.
  destruct SINV.
  split.
  { unfold memory_invariant in *.
    intros n v0 b τ x NTH_σ NTH_Γ.
    destruct (Nat.eq_dec hid n); subst.
    - (* hid = n *)
      apply nth_error_protect_eq' in NTH_σ.
      apply nth_error_protect_eq' in NTH_σ_hid.
      pose proof (mem_is_inv0 _ _ _ _ _ NTH_σ NTH_Γ).
      destruct v0; eauto.
      destruct H as (ptrll & τ' & TEQ & FITS & INLG' & LUP); inv TEQ.
      exists ptrll. exists τ'.
      repeat split; eauto.
      intros H; destruct b; inv H.

      (* Because n = hid I want to conclude that a = dst_addr_h *)
      rewrite NTH_σ_hid in NTH_σ; inv NTH_σ.
      rewrite NTH_Γ_hid in NTH_Γ; inv NTH_Γ.
      assert (ptrll_dst ≡ ptrll) as PTREQ.
      { destruct x; cbn in INLG, INLG';
          rewrite INLG in INLG'; inv INLG'; auto.
      }
      subst.

      rename a into dst_addr_h.
      exists mb.
      split.
      + apply memory_lookup_memory_set_eq.
      + intros i v0 H.
        destruct (Nat.eq_dec (MInt64asNT.to_nat i) (MInt64asNT.to_nat y)) as [EQ | NEQ].
        * rewrite EQ in H; rewrite MLUP_NEW in H; inv H.
          erewrite <- read_array.
          solve_read.
          solve_allocated.
          eauto.
          eauto.
          rewrite EQ. eauto.
        * clear LUP.
          eapply MGAC; eauto.
          rewrite <- MLUP_OLD; eauto.
    - rewrite <- nth_error_protect_neq with (n2 := hid) in NTH_σ; eauto.
      apply nth_error_protect_eq' in NTH_σ_hid.
      pose proof (mem_is_inv0 _ _ _ _ _ NTH_σ NTH_Γ).
      destruct v0; eauto.
      destruct H as (ptrll & τ' & TEQ & FITS & INLG' & LUP); inv TEQ.
      exists ptrll. exists τ'.
      repeat split; eauto.
      intros H; destruct b; inv H.
      specialize (LUP eq_refl).
      destruct LUP as (bkh & MEMLUP & GETARRAYCELL).
      exists bkh.
      split; eauto.

      rewrite memory_lookup_memory_set_neq; eauto.

      intros CONTRA; subst.
      assert (hid ≡ n).
      { eapply st_no_dshptr_aliasing0; eauto.
      }
      contradiction.
  }

  (* In theory all should hold, but different direction *)
  - eapply WF_IRState_protect; eauto.
  - eapply no_id_aliasing_protect; eauto.
  - eapply no_dshptr_aliasing_protect; eauto.
  - eapply no_llvm_ptr_aliasing_protect; eauto.
  - eapply id_allocated_protect;
      eapply id_allocated_memory_set; eauto.
  - solve_gamma_bound.
Qed.

(* TODO: is there a better spot for this? *)
Lemma get_array_cell_mlup_ext :
  forall bkh ptrll dst_addr sz ix mV mV' v',
    (∀ (i : Int64.int) (v : binary64),
        mem_lookup (MInt64asNT.to_nat i) bkh ≡ Some v
        → get_array_cell mV ptrll (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v)) ->
    handle_gep_addr (DTYPE_Array sz DTYPE_Double) ptrll [DVALUE_I64 (repr 0); DVALUE_I64 ix] ≡ inr dst_addr ->
    ext_memory mV dst_addr DTYPE_Double (dvalue_to_uvalue (DVALUE_Double v')) mV' ->
    allocated ptrll mV' ->
    (∀ (i : Int64.int) (v : binary64),
        MInt64asNT.to_nat ix ≢ MInt64asNT.to_nat i ->
        mem_lookup (MInt64asNT.to_nat i) bkh ≡ Some v ->
        get_array_cell mV' ptrll (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v)).
Proof.
  intros bkh ptrll dst_addr sz ix mV mV' v' GAC GEP_INIT [EXT_NEW EXT_OLD] ALLOC' i v NEQ MLUP.

  pose proof (GAC _ _ MLUP) as G.
  pose proof (get_array_succeeds_allocated _ _ _ _ G) as ALLOC.

  epose proof (read_array_exists mV _ _ _ ptrll ALLOC) as (elem_addr & GEP & READ).

  erewrite <- read_array; eauto.
  rewrite EXT_OLD; eauto.
  rewrite READ; eauto.
  solve_allocated.

  rewrite repr_of_nat_to_nat in GEP.
  eapply no_overlap_dtyp_array_different_indices; eauto.
  apply to_nat_unsigned'; eauto.
Qed.

(* TODO: is there a better spot for this? *)
Lemma get_array_cell_mlup_ext' :
  forall bkh ptrll dst_addr sz ix mV mV' v',
    (∀ (i : Int64.int) (v : binary64),
        MInt64asNT.to_nat ix ≢ MInt64asNT.to_nat i ->
        mem_lookup (MInt64asNT.to_nat i) bkh ≡ Some v
        → get_array_cell mV ptrll (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v)) ->
    handle_gep_addr (DTYPE_Array sz DTYPE_Double) ptrll [DVALUE_I64 (repr 0); DVALUE_I64 ix] ≡ inr dst_addr ->
    ext_memory mV dst_addr DTYPE_Double (dvalue_to_uvalue (DVALUE_Double v')) mV' ->
    allocated ptrll mV' ->
    (∀ (i : Int64.int) (v : binary64),
        MInt64asNT.to_nat ix ≢ MInt64asNT.to_nat i ->
        mem_lookup (MInt64asNT.to_nat i) bkh ≡ Some v ->
        get_array_cell mV' ptrll (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v)).
Proof.
  intros bkh ptrll dst_addr sz ix mV mV' v' GAC GEP_INIT [EXT_NEW EXT_OLD] ALLOC' i v NEQ MLUP.

  pose proof (GAC _ _ NEQ MLUP) as G.
  pose proof (get_array_succeeds_allocated _ _ _ _ G) as ALLOC.

  epose proof (read_array_exists mV _ _ _ ptrll ALLOC) as (elem_addr & GEP & READ).

  erewrite <- read_array; eauto.
  rewrite EXT_OLD; eauto.
  rewrite READ; eauto.
  solve_allocated.

  rewrite repr_of_nat_to_nat in GEP.
  eapply no_overlap_dtyp_array_different_indices; eauto.
  apply to_nat_unsigned'; eauto.
Qed.

Lemma vellvm_helix_ptr_size:
  forall σ s memH memV ρ g n id (sz : N) dsh_ptr (dsh_sz : Int64.int) b,
    nth_error (Γ s) n ≡ Some (id, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
    nth_error σ n ≡ Some (DSHPtrVal dsh_ptr dsh_sz, b) ->
    state_invariant σ s memH (memV, (ρ, g)) ->
    sz ≡ Z.to_N (Int64.intval dsh_sz).
Proof.
  intros σ s memH memV ρ g n id sz dsh_ptr dsh_sz b GAM SIG SINV.
  apply IRState_is_WF in SINV.
  unfold WF_IRState in SINV.
  unfold evalContext_typechecks in SINV.
  pose proof (SINV (DSHPtrVal dsh_ptr dsh_sz) n  b SIG) as H.
  destruct H as (id' & NTH).
  cbn in NTH.
  rewrite GAM in NTH.
  inv NTH.
  destruct id'; inv H1; reflexivity.
Qed.

Definition pointers_untouched (σ : evalContext) (s : IRState) (l1 l2 : local_env) :=
  forall id ptr ptr_h sz n τ,
    nth_error σ n ≡ Some (DSHPtrVal ptr_h sz, true) ->
    nth_error (Γ s) n ≡ Some (ID_Local id, TYPE_Pointer τ) ->
    alist_find id l1 ≡ Some (UVALUE_Addr ptr) ->
    alist_find id l2 ≡ Some (UVALUE_Addr ptr).

Lemma pointers_untouched_refl :
  forall σ s l,
    pointers_untouched σ s l l.
Proof.
  intros l.
  unfold pointers_untouched.
  auto.
Qed.

Lemma unsigned_is_zero: forall a, Int64.unsigned a ≡ Int64.unsigned Int64.zero ->
                                  a = Int64.zero.
Proof.
  intros a H.
  unfold Int64.unsigned, Int64.intval in H.
  repeat break_let; subst.
  destruct Int64.zero.
  inv Heqi0.
  unfold equiv, MInt64asNT.NTypeEquiv, Int64.eq, Int64.unsigned, Int64.intval.
  apply Coqlib.zeq_true.
Qed.

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

Ltac solve_in_gamma :=
  match goal with
  | GAM : nth_error (Γ ?s) ?n ≡ Some (ID_Local ?id, _),
          SIG : nth_error ?σ ?n ≡ Some _ |-
    in_Gamma _ _ ?id
    => econstructor; [eapply SIG | eapply GAM | eauto]
  end.

(* TODO: expand this *)
Ltac solve_lid_bound_between :=
  solve [ eauto
        | eapply lid_bound_between_count; [solve_prefix | solve_local_count | solve_local_count]
        | eapply lid_bound_between_shrink; [eapply lid_bound_between_incLocal | | ]; eauto; solve_local_count
        | eapply lid_bound_between_shrink; [eapply lid_bound_between_incLocalNamed; cycle 1; [eauto | solve_prefix]| solve_local_count | solve_local_count]
        ].

Ltac solve_not_in_gamma :=
  first [ now eauto
        |
      match goal with
      | GAM : Gamma_safe ?σ ?si ?sf |-
        ~ in_Gamma ?σ ?si ?id =>
        eapply GAM; solve_lid_bound_between
      end
    | solve [eapply not_in_Gamma_Gamma_eq; [eassumption | solve_not_in_gamma]]
    | solve [eapply not_in_gamma_protect; solve_not_in_gamma]
    | solve [eapply not_in_gamma_cons; [cbn; eauto; try solve_gamma | solve_not_in_gamma |]]
    ].

#[export] Hint Resolve state_invariant_memory_invariant : core.
#[export] Hint Resolve memory_invariant_GLU memory_invariant_LLU memory_invariant_LLU_AExpr memory_invariant_GLU_AExpr : core.

#[export] Hint Resolve is_pure_refl: core.
#[export] Hint Resolve local_scope_modif_refl: core.

#[export] Hint Resolve genNExpr_Γ : helix_context.
#[export] Hint Resolve genMExpr_Γ : helix_context.
#[export] Hint Resolve incVoid_Γ        : helix_context.
#[export] Hint Resolve incLocal_Γ       : helix_context.
#[export] Hint Resolve incBlockNamed_Γ  : helix_context.
#[export] Hint Resolve genAExpr_Γ : helix_context.
#[export] Hint Resolve genIR_Γ  : helix_context.

(* TODO: expand this *)
Ltac solve_gamma_safe :=
  eapply Gamma_safe_shrink; eauto; try solve_gamma; cbn; solve_local_count.

(* TODO: expand this *)
Ltac solve_local_scope_modif :=
  cbn; eauto with LSM.

#[export] Hint Immediate local_scope_modif_refl : LSM.
#[export] Hint Extern 1 (lid_bound_between _ _ _) => solve_lid_bound_between : LSM.
#[export] Hint Extern 1 (lid_bound _ _) => solve_lid_bound : LSM.
#[export] Hint Resolve local_scope_modif_add' : LSM.
#[export] Hint Resolve local_scope_modif_shrink : LSM.
#[export] Hint Extern 1 (_ <<= _) => solve_local_count : LSM.
#[export] Hint Extern 2 (local_scope_modif _ _ _ _) => eapply local_scope_modif_trans; cycle 2; eauto; solve_local_count : LSM.

(* Slightly more aggressive with transitivity... May get stuck *)
Ltac solve_local_scope_modif_trans :=
  eauto;
  first
    [ eapply local_scope_modif_refl
    | solve [eapply local_scope_modif_shrink; [eassumption | solve_local_count | solve_local_count]]
    | solve [eapply local_scope_modif_add'; [solve_lid_bound_between | solve_local_scope_modif]]
    | eapply local_scope_modif_trans; cycle 3; [solve_local_scope_modif_trans | solve_local_count | solve_local_count | solve_local_scope_modif_trans]
    ].

#[export] Hint Immediate Gamma_preserved_refl : SolveGammaPreserved.
#[export] Hint Extern 1 (~ (in_Gamma _ _ _)) => solve_not_in_gamma : SolveGammaPreserved.
#[export] Hint Resolve Gamma_preserved_add_not_in_Gamma : SolveGammaPreserved.
#[export] Hint Resolve Gamma_preserved_if_safe : SolveGammaPreserved.
#[export] Hint Extern 1 (local_scope_modif _ _ _ _) => solve_local_scope_modif : SolveGammaPreserved.
#[export] Hint Extern 1 (Gamma_safe _ _ _) => solve_gamma_safe : SolveGammaPreserved.

Ltac solve_gamma_preserved :=
  solve [eauto with SolveGammaPreserved].

Opaque alist_add.

(* TODO: move these *)
Lemma in_local_or_global_scalar_not_in_gamma :
  forall r v ρ g m id v_id τ σ s,
    in_Gamma σ s id ->
    ~ in_Gamma σ s r ->
    in_local_or_global_scalar ρ g m (ID_Local id) v_id τ ->
    in_local_or_global_scalar (alist_add r v ρ) g m (ID_Local id) v_id τ.
Proof.
  intros r v ρ g m id v_id τ σ s GAM NGAM INLG.
  destruct (Eqv.eqv_dec_p r id) as [EQ | NEQ].
  - do 2 red in EQ.
    subst.
    contradiction.
  - unfold Eqv.eqv, eqv_raw_id in NEQ.
    cbn in *.
    erewrite alist_find_neq; eauto.
Qed.

(* TODO: move this? *)
Lemma incLocal_id_neq :
  forall s1 s2 s3 s4 id1 id2,
    incLocal s1 ≡ inr (s2, id1) ->
    incLocal s3 ≡ inr (s4, id2) ->
    local_count s1 ≢ local_count s3 ->
    id1 ≢ id2.
Proof.
  intros s1 s2 s3 s4 id1 id2 GEN1 GEN2 COUNT.
  eapply incLocalNamed_count_gen_injective.
  symmetry; eapply GEN1.
  symmetry; eapply GEN2.
  solve_local_count.
  solve_prefix.
  solve_prefix.
Qed.

Lemma incLocal_id_neq_flipped :
  forall s1 s2 s3 s4 id1 id2,
    incLocal s1 ≡ inr (s2, id1) ->
    incLocal s3 ≡ inr (s4, id2) ->
    local_count s1 ≢ local_count s3 ->
    id2 ≢ id1.
Proof.
  intros s1 s2 s3 s4 id1 id2 GEN1 GEN2 COUNT.
  intros EQ. symmetry in EQ. revert EQ.
  eapply incLocal_id_neq; eauto.
Qed.

Lemma incBlockNamed_id_neq :
  forall s1 s2 s3 s4 id1 id2 n1 n2,
    incBlockNamed n1 s1 ≡ inr (s2, id1) ->
    incBlockNamed n2 s3 ≡ inr (s4, id2) ->
    is_correct_prefix n1 ->
    is_correct_prefix n2 ->
    block_count s1 ≢ block_count s3 ->
    id1 ≢ id2.
Proof.
  intros s1 s2 s3 s4 id1 id2 n1 n2 GEN1 GEN2 PRE1 PRE2 COUNT.
  eapply incBlockNamed_count_gen_injective; eauto.
Qed.

Lemma in_gamma_not_in_neq :
  forall σ s id r,
    in_Gamma σ s id ->
    ~ in_Gamma σ s r ->
    id ≢ r.
Proof.
  intros σ s id r GAM NGAM.
  destruct (Eqv.eqv_dec_p r id) as [EQ | NEQ].
  - do 2 red in EQ.
    subst.
    contradiction.
  - unfold Eqv.eqv, eqv_raw_id in NEQ.
    eauto.
Qed.

Ltac solve_id_neq :=
  first [ solve [eapply incLocal_id_neq; eauto; solve_local_count]
        | solve [eapply incBlockNamed_id_neq; eauto; solve_block_count]
        | solve [eapply in_gamma_not_in_neq; [solve_in_gamma | solve_not_in_gamma]]
        | solve [eapply lid_bound_earlier; [ solve_lid_bound | solve_lid_bound_between  | solve_local_count ]]
        | solve [eapply state_bound_between_separate; [eapply incLocalNamed_count_gen_injective
                                                      | solve_lid_bound_between
                                                      | solve_lid_bound_between
                                                      | cbn; solve_local_count]]
        | solve [let CONTRA := fresh "CONTRA" in intros CONTRA; symmetry in CONTRA; revert CONTRA; solve_id_neq]
        ].

Ltac solve_alist_in :=
  solve [cbn;
         first [ apply In_add_eq
               | solve [eauto]
               | solve [rewrite alist_find_neq; [solve_alist_in | solve_id_neq]]
               | solve [erewrite local_scope_preserve_modif; [|solve_local_scope_modif|solve_lid_bound_between]; solve_alist_in]
               | solve [erewrite local_scope_preserve_modif_up; [|solve_local_scope_modif|solve_lid_bound_between]; solve_alist_in]
               ]
        ].

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


Ltac solve_local_lookup :=
  first
    [ now eauto
    | solve [erewrite alist_find_add_eq; eauto]
    | solve [erewrite alist_find_neq; [solve_local_lookup|solve_id_neq]]
    ].

Ltac solve_in_local_or_global_scalar :=
  first
    [ now eauto
    | solve [eapply in_local_or_global_scalar_not_in_gamma; [solve_in_gamma | solve_not_in_gamma | solve_in_local_or_global_scalar]]
    ].

#[export] Hint Resolve state_invariant_memory_invariant state_invariant_WF_IRState : core.

Lemma local_scope_preserved_bound_earlier :
  forall s1 s2 s3 x v l l',
    lid_bound s1 x ->
    s1 <<= s2 ->
    local_scope_preserved s2 s3 l l' ->
    local_scope_preserved s2 s3 l (Maps.add x v l').
Proof.
  intros s1 s2 s3 x v l l' BOUND LT PRES.
  unfold local_scope_preserved.
  intros id BETWEEN.

  epose proof (lid_bound_earlier BOUND BETWEEN LT) as NEQ.
  unfold local_scope_preserved in PRES.
  setoid_rewrite maps_add_neq; eauto.
Qed.

Lemma local_scope_preserved_add_bound_earlier :
  forall s1 s2 s3 s4 l1 l2 id v,
    local_scope_preserved s1 s2 l1 l2 ->
    lid_bound_between s3 s4 id ->
    s4 <<= s1 ->
    local_scope_preserved s1 s2 l1 (alist_add id v l2).
Proof.
  intros s1 s2 s3 s4 l1 l2 id v LSP BOUND LT.
  unfold local_scope_preserved in *.
  intros id0 H.

  rewrite alist_find_neq.
  eauto.
  intros CONTRA; symmetry in CONTRA; revert CONTRA.
  solve_id_neq.
Qed.

Lemma local_scope_preserved_add_bound_later :
  forall s1 s2 s3 s4 l1 l2 id v,
    local_scope_preserved s1 s2 l1 l2 ->
    lid_bound_between s3 s4 id ->
    s2 <<= s3 ->
    local_scope_preserved s1 s2 l1 (alist_add id v l2).
Proof.
  intros s1 s2 s3 s4 l1 l2 id v LSP BOUND LT.
  unfold local_scope_preserved in *.
  intros id0 H.

  rewrite alist_find_neq.
  eauto.
  solve_id_neq.
Qed.

#[export] Hint Extern 1 (local_scope_modif _ _ _ _) => solve_local_scope_modif : LocalScopePreserved.
#[export] Hint Extern 1 (Gamma_safe _ _ _) => solve_gamma_safe : LocalScopePreserved.
#[export] Hint Extern 1 (_ <<= _) => solve_local_count : LocalScopePreserved.
#[export] Hint Extern 1 (lid_bound _ _) => solve_lid_bound : LocalScopePreserved.
#[export] Hint Extern 1 (lid_bound_between _ _ _) => solve_lid_bound : LocalScopePreserved.
#[export] Hint Immediate local_scope_preserve_modif : LocalScopePreserved.
#[export] Hint Resolve local_scope_preserved_refl local_scope_preserved_bound_earlier : LocalScopePreserved.
#[export] Hint Resolve local_scope_preserved_add_bound_later local_scope_preserved_add_bound_earlier : LocalScopePreserved.
#[export] Hint Extern 1 (lid_bound_between _ _ _) => solve_lid_bound_between : LocalScopePreserved.

Ltac solve_local_scope_preserved :=
  solve [eauto with LocalScopePreserved].

Ltac solve_state_invariant := eauto with SolveStateInv.
#[export] Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incBlockNamed; [eassumption | solve_state_invariant] : SolveStateInv.
#[export] Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incLocal; [eassumption | solve_state_invariant] : SolveStateInv.
#[export] Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incLocalNamed; [eassumption | solve_state_invariant] : SolveStateInv.
#[export] Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incVoid; [eassumption | solve_state_invariant] : SolveStateInv.
#[export] Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_incLocalNamed; [eassumption | solve_state_invariant] : SolveStateInv.

Ltac get_gamma_bounds :=
  repeat match goal with
         | SINV : state_invariant _ _ _ _ |- _
           => apply st_gamma_bound in SINV
         end.
