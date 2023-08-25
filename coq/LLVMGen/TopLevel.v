Require Import Helix.LLVMGen.Vellvm_Utils.
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
Import AlistNotations.

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

Section Program.

  Local Obligation Tactic := cbv;auto.
  Program Definition dynwin_i' : Int64.int := Int64.mkint (Z.of_nat dynwin_i) _.
  Program Definition dynwin_o' : Int64.int := Int64.mkint (Z.of_nat dynwin_o) _.
  Program Definition three : Int64.int := Int64.mkint 3 _.
  Definition dynwin_globals' : list (string * FHCOL.DSHType)
    := cons ("a",DSHPtr three) nil.

  (* Here I should be able to compute the operator instead of quantifying over it in the statement *)
  Definition dynwin_fhcolp : FHCOL.DSHOperator -> FSHCOLProgram :=
    mkFSHCOLProgram dynwin_i' dynwin_o' "dyn_win" dynwin_globals'.

End Program.

Set Nested Proofs Allowed.
Import MonadNotation.
Local Open Scope monad_scope.
Import ListNotations.

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

Lemma vector_to_list_length :
  forall A n (xs : Vector.t A n),
    Datatypes.length (Vector.to_list xs) ≡ n.
Proof.
  intros.
  induction n.
  - dep_destruct xs.
    reflexivity.
  - dep_destruct xs.
    specialize IHn with x.
    apply f_equal with (f := S) in IHn.
    rewrite <- IHn.
    reflexivity.
Qed.

Definition dynwin_F_σ :=
  [ (FHCOL.DSHPtrVal 0 three    , false) ;
    (FHCOL.DSHPtrVal 1 dynwin_o', false) ;
    (FHCOL.DSHPtrVal 2 dynwin_i', false) ].

Definition dynwin_F_memory a x :=
  memory_set
    (memory_set
      (memory_set
        memory_empty
          dynwin_a_addr (mem_block_of_list a))
      dynwin_y_addr mem_empty)
    dynwin_x_addr (mem_block_of_list x).


Lemma constList_app :
  forall n data rest data' data'' l1 l2,
    n <= Datatypes.length data ->
    constList n (data ++ rest) ≡ (data', l1) ->
    constList n data ≡ (data'', l2) ->
    l1 ≡ l2.
Proof.
  induction n; intros * Hn H1 H2.
  - cbn in *.
    inv H1; inv H2.
    reflexivity.
  - cbn in *.
    repeat break_let.
    repeat find_inversion.
    destruct data; [inv Heqp; inv Hn |].
    cbn in Hn.
    cbn in Heqp; inv Heqp.
    cbn in Heqp1; inv Heqp1.
    f_equal.
    apply le_S_n in Hn.
    destruct (constList n data) eqn:E.
    replace l0 with l3 in * by (eapply IHn; revgoals; eassumption).
    eapply IHn.
    + eassumption.
    + rewrite <- app_assoc in Heqp2.
      apply Heqp2.
    + eassumption.
Qed.

Lemma constList_firstn :
  forall n data data' l,
    constList n data ≡ (data', l) ->
    n <= Datatypes.length data ->
    l ≡ firstn n data.
Proof.
  induction n; intros * H Hn.
  - cbn in H.
    inv H.
    reflexivity.
  - cbn in H.
    do 2 break_let.
    find_inversion.
    destruct data; [inv Hn |].
    cbn in Heqp.
    inv Heqp.
    cbn.
    f_equal.
    cbn in Hn; apply le_S_n in Hn.
    destruct (constList n data) eqn:E.
    replace l0 with l2 in *
      by (eapply constList_app; revgoals; eassumption).
    eapply IHn; eassumption.
Qed.

Lemma rotateN_nil A n : @rotateN A n [] ≡ [].
Proof.
  induction n; auto.
  simpl; rewrite IHn; auto.
Qed.

Lemma rotateN_sing A n (x : A) : rotateN n [x] ≡ [x].
Proof.
  induction n; auto.
  simpl; rewrite IHn; auto.
Qed.

Lemma rotateN_cons A n (x : A) xs :
  rotateN (S n) (x :: xs) ≡ rotateN n (xs ++ [x]).
Proof.
  induction n; auto.
  simpl in *; rewrite IHn; auto.
Qed.

Lemma rotateN_firstn_reverse :
  forall A n (xs : list A),
    n <= Datatypes.length xs ->
    rotateN n xs ≡ skipn n xs ++ firstn n xs.
Proof.
  induction n; intros; [cbn; rewrite app_nil_r; auto |].
  destruct xs; [inv H |].
  cbn in H; apply le_S_n in H.
  cbn - [rotateN].
  unfold rotateN in *.
  rewrite nat_iter_S.
  rewrite IHn by (cbn; lia); clear IHn.
  destruct n; cbn; [rewrite app_nil_r; auto |].
  break_match; [destruct skipn; discriminate |].
  destruct (skipn n xs) eqn:E.
  + cbn in *. inv Heql.
    assert (Datatypes.length (skipn n xs) ≡ 0) by (rewrite E; auto).
    pose proof skipn_length n xs.
    find_rewrite; lia.
  + cbn in Heql.
    inv Heql.
    replace (S n) with (1 + n) by auto.
    rewrite <- skipn_skipn, E, <- app_assoc; cbn.
    repeat f_equal.
    replace (S n) with (n + 1) by lia.
    rewrite MCList.firstn_add.
    rewrite E.
    reflexivity.
Qed.

(* MARK Vadim ? IZ TODO: generalize beyond just DynWin? *)
Lemma initial_memory_from_data :
  forall
    (a : Vector.t CarrierA 3)
    (x : Vector.t CarrierA dynwin_i)
    data,
    heq_list (Vector.to_list a ++ Vector.to_list x) data ->
    exists dynwin_F_memory data_garbage,
      helix_initial_memory (dynwin_fhcolp DynWin_FHCOL_hard) data
      ≡ inr (dynwin_F_memory, data_garbage, dynwin_F_σ)
      /\ RHCOLtoFHCOL.heq_memory () RF_CHE (dynwin_R_memory a x) dynwin_F_memory
      /\ RHCOLtoFHCOL.heq_evalContext () RF_NHE RF_CHE dynwin_R_σ dynwin_F_σ.
Proof.
  intros.
  unfold helix_initial_memory; cbn.
  repeat break_let; cbn.
  apply heq_list_app in H as (la & lx & Hdata & Hla & Hlx); subst.
  eexists (dynwin_F_memory la lx), _; break_and_goal.
  - repeat f_equal.
    unfold dynwin_F_memory.
    unfold dynwin_a_addr; cbn.
    unfold constMemBlock in *.
    repeat (break_let; find_inversion).
    enough (l3 ≡ la /\ l2 ≡ lx) as (? & ?) by (subst; reflexivity).
    apply Forall2_length in Hla, Hlx.
    rewrite vector_to_list_length in Hla, Hlx.
    copy_apply constList_firstn Heqp0; [| rewrite app_length; lia].
    rewrite firstn_app_exact in H by assumption; subst.
    apply constList_data in Heqp0; subst.
    rewrite rotateN_firstn_reverse in Heqp1 by (rewrite app_length; lia).
    rewrite skipn_app_exact, firstn_app_exact in Heqp1 by assumption.
    unfold dynwin_i in *.
    apply constList_firstn in Heqp1; [| rewrite app_length; lia].
    rewrite firstn_app_exact in Heqp1 by assumption.
    subst; split; auto.
  - clear - Hla Hlx.
    unfold heq_memory; intro.
    repeat (destruct k; [apply hopt_r_Some |]).
    + apply Forall2_length in Hla as Hla'.
      rewrite vector_to_list_length in Hla'.
      repeat (destruct la; try discriminate).
      clear - Hla.
      repeat dependent destruction a.
      unfold heq_list in Hla.
      repeat inv_prop Forall2.
      intro k.
      repeat (destruct k; [apply hopt_r_Some; assumption |]).
      apply hopt_r_None.
    + intro k.
      apply hopt_r_None.
    + apply Forall2_length in Hlx as Hlx'.
      rewrite vector_to_list_length in Hlx'.
      repeat (destruct lx; try discriminate).
      clear - Hlx.
      repeat dependent destruction x.
      unfold heq_list in Hlx.
      repeat inv_prop Forall2.
      intro k.
      repeat (destruct k; [apply hopt_r_Some; assumption |]).
      apply hopt_r_None.
    + apply hopt_r_None.
  - unfold heq_evalContext.
    repeat (apply Forall2_cons; [split; auto |]).
    4: apply Forall2_nil.
    all: apply heq_DSHPtrVal; reflexivity.
Qed.

Lemma interp_mem_interp_helix_ret_eq : forall E σ op hmem fmem v,
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

Lemma option_rel_opt_r : forall {A} (R : A -> A -> Prop),
    HeterogeneousRelations.eq_rel (option_rel R) (RelUtil.opt_r R).
Proof.
  split; repeat intro.
  - cbv in H.
    repeat break_match; intuition.
    now constructor.
    now constructor.
  - inv H; now cbn.
Qed.

(* MARK *)
Lemma interp_mem_interp_helix_ret : forall E σ op hmem fmem,
    eutt equiv (interp_Mem (denoteDSHOperator σ op) hmem) (Ret (fmem,tt)) ->
    eutt equiv (interp_helix (E := E) (denoteDSHOperator σ op) hmem) (Ret (Some (fmem,tt))).
Proof.
  intros * HI.
  unfold interp_helix.
  assert (Transitive (eutt (E := E) (option_rel equiv))).
  - apply eutt_trans, option_rel_trans.
    intros x y z.
    unfold equiv, FHCOLtoSFHCOL.SFHCOLEval.evalNatClosure_Equiv.
    apply oprod_equiv_Equivalence.
  - unfold equiv, option_Equiv.
    rewrite <- option_rel_opt_r.
    unfold equiv, FHCOLtoSFHCOL.SFHCOLEval.evalNatClosure_Equiv in H.
Admitted.

Import RecursionFacts.

Import TranslateFacts.

From Paco Require Import paco.
Import Interp.

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
              df_args := [Name "X0"; Name "Y1"];
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
                    df_args := [Name "X0"; Name "Y1"];
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
    local_count := 2;
    void_count := 0;
    Γ :=
      [(ID_Global (Name "a"), TYPE_Pointer (TYPE_Array (Npos 3) TYPE_Double));
       (ID_Local (Name "Y1"), TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double));
       (ID_Local (Name "X0"), TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double))]
  |}.

#[local] Definition Γi' :=
  {|
    block_count := 1;
    local_count := 2;
    void_count := 0;
    Γ :=
      [(ID_Global (Name "a"), TYPE_Pointer (TYPE_Array (Npos 3) TYPE_Double));
       (ID_Global (Anon 1%Z), TYPE_Pointer (TYPE_Array (Npos 1) TYPE_Double));
       (ID_Global (Anon 0%Z), TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double))]
  |}.

Local Lemma Γi_bound : gamma_bound Γi.
Proof.
  unfold gamma_bound.
  intros.
  unfold LidBound.lid_bound.
  unfold VariableBinding.state_bound.
  apply nth_error_In in H.
  repeat invc_prop In; find_inversion.
  - exists "Y", {|
        block_count := 1;
        local_count := 1;
        void_count  := 0;
        Γ := [(ID_Global (Name "a"), TYPE_Pointer (TYPE_Array (Npos 3) TYPE_Double));
              (ID_Local (Name "X0"), TYPE_Pointer (TYPE_Array (Npos 5) TYPE_Double))]
      |}; eexists; break_and_goal.
    + reflexivity.
    + constructor.
    + reflexivity.
  - exists "X", {|
        block_count := 1;
        local_count := 0;
        void_count  := 0;
        Γ := [(ID_Global (Name "a"), TYPE_Pointer (TYPE_Array (Npos 3) TYPE_Double))]
      |}; eexists; break_and_goal.
    + reflexivity.
    + repeat constructor.
    + reflexivity.
Qed.

Local Lemma Γi'_bound : gamma_bound Γi'.
Proof.
  unfold gamma_bound.
  intros.
  unfold LidBound.lid_bound.
  unfold VariableBinding.state_bound.
  apply nth_error_In in H.
  repeat invc_prop In; find_inversion.
Qed.

#[local] Definition MCFG l6 l5 b0 l4 :=
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
                                  g_exp := Some (EXP_Array [(TYPE_Double, EXP_Double MFloat64asCT.CTypeZero)]);
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
                                                                   df_args := [Name "X0"; Name "Y1"];
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
                        df_args := [Name "X0"; Name "Y1"];
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
                              df_args := [Name "X0"; Name "Y1"];
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

Require Import Helix.LLVMGen.Vellvm_Utils.
Definition mcfg_ctx := Vellvm_Utils.mcfg_ctx.
Opaque MCFG MAIN MAINCFG DYNWIN GFUNC mcfg_ctx.

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

Set Printing Compact Contexts.

Local Lemma numeric_suffix_must_exist:
  forall ls rs n,
    CeresString.string_forall IdLemmas.is_alpha ls ->
    ls ≡ rs @@ string_of_nat n -> False.
Proof.
  intros ls rs n H C.
  rewrite C in H.
  apply IdLemmas.string_append_forall in H as [H1 H2].
  eapply IdLemmas.string_of_nat_not_empty.
  eapply IdLemmas.string_forall_contradiction.
  - eapply H2.
  - eapply IdLemmas.string_of_nat_not_alpha.
Qed.

Local Lemma dropLocalVars_Gamma_eq :
  forall s1 s1' s2 s2',
    dropLocalVars s1 ≡ inr (s1', ()) ->
    dropLocalVars s2 ≡ inr (s2', ()) ->
    Γ s1  ≡ Γ s2 ->
    Γ s1' ≡ Γ s2'.
Proof.
  intros.
  destruct s1; destruct s1'.
  destruct s2; destruct s2'.
  unfold dropLocalVars in *.
  simpl in *.
  unfold ErrorWithState.option2errS in *.
  repeat (break_if; try discriminate).
  repeat (break_match; try discriminate).
  unfold ret in *; simpl in *.
  repeat find_inversion.
  reflexivity.
Qed.

#[local]
Definition coe_Γi_Γi' (id : ident) : ident :=
  match id with
  | ID_Local "X0" => ID_Global (Anon 0%Z)
  | ID_Local "Y1" => ID_Global (Anon 1%Z)
  | _ => id
  end.

(*
  Γ only contains variables we care about [existing compile time].
  Others might exist at runtime, but Γ defines a subset of them.

  Γi' is the state after allocation, but before the operator is called.
  It has globals, but no local variables.
  Γi is the state during operator evalution: it does contain local variables.
*)
Local Lemma state_invariant_Γi :
  forall σ mem memI ρI ρI' gI a0 a1,
    (* global environment must contain addresses for input and output *)
    gI @ (Anon 0%Z) ≡ Some (DVALUE_Addr a0) ->
    gI @ (Anon 1%Z) ≡ Some (DVALUE_Addr a1) ->

    (* after we get inside the function, local environment will containan
       two new local vars with addresses for input and output *)
    ρI' @ (Name "X0") ≡ Some (UVALUE_Addr a0) ->
    ρI' @ (Name "Y1") ≡ Some (UVALUE_Addr a1) ->

    (* then the state invariant is preserved *)
    state_invariant σ Γi' mem (memI, (ρI , gI)) ->
    state_invariant σ Γi  mem (memI, (ρI', gI)).
Proof.
  intros * Hg0 Hg1 Hρ0 Hρ1 SINV.
  destruct SINV.
  constructor; try assumption.
  - unfold memory_invariant in *.
    intros.
    specialize mem_is_inv with n v b τ (coe_Γi_Γi' x).
    repeat (destruct n; try discriminate).
    all: inv H0.
    1: apply mem_is_inv; auto.
    all: conclude mem_is_inv assumption.
    all: conclude mem_is_inv auto.
    all: apply IRState_is_WF in H as [id H].
    all: destruct v; try (inv H; discriminate).
    all: destruct mem_is_inv as (ptr & τ & ? & ? & ? & ?).
    all: exists ptr, τ; break_and_goal; try assumption.
    all: cbn in H2.
    all: find_rewrite; find_inversion.
    all: cbn.
    all: assumption.
  - unfold WF_IRState, evalContext_typechecks in *.
    intros.
    specialize IRState_is_WF with v n b.
    apply IRState_is_WF in H.
    destruct H.
    repeat (destruct n; try discriminate).
    all: cbn in H.
    all: eexists.
    all: cbn.
    all: do 2 f_equal.
    all: inv H.
    all: destruct FHCOLITree.DSHType_of_DSHVal eqn:E in H2.
    all: try discriminate.
    all: try rewrite E.
    all: rewrite H2.
    all: reflexivity.
  - unfold no_id_aliasing.
    intros.
    all: repeat (destruct n1; try discriminate).
    all: repeat (destruct n2; try discriminate).
    all: try reflexivity.
    all: eapply st_no_id_aliasing; try eassumption.
    all: unshelve (inv H1; inv H2); assumption.
  - unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing in *.
    intros.
    specialize st_no_llvm_ptr_aliasing with
      (coe_Γi_Γi' id1) ptrv1
      (coe_Γi_Γi' id2) ptrv2
      n1 n2 τ τ' v1 v2 b b'.
    all: repeat (destruct n1; try discriminate).
    all: repeat (destruct n2; try discriminate).
    all: inv H1; inv H2.
    all: try contradiction.
    all: apply st_no_llvm_ptr_aliasing; assumption || auto.
    all: try (intro; discriminate).
    all: cbn.
    all: cbn in H4, H5.
    all: repeat (find_rewrite; find_inversion).
    all: assumption.
  - apply Γi_bound.
Qed.

Local Lemma state_invariant_frames :
  forall σ s mH m f f' ρ g,
    state_invariant σ s mH (m, f , (ρ, g)) ->
    state_invariant σ s mH (m, f', (ρ, g)).
Proof.
  intros * SINV.
  split; apply SINV.
Qed.

Local Lemma state_invariant_frames' :
  forall σ s mH mV mV' ρ g,
    fst mV ≡ fst mV' ->
    state_invariant σ s mH (mV , (ρ, g)) ->
    state_invariant σ s mH (mV', (ρ, g)).
Proof.
  intros * EQmV SINV.
  destruct mV; destruct mV'.
  cbn in EQmV; subst.
  eapply state_invariant_frames, SINV.
Qed.

(* TODO: move the following 2 tactics and 2 lemmas *)
#[local] Ltac find_b0_id :=
  match goal with
  | [H : _ ≡ ?b0 :: ?blocks |- _] => invc H
  end.
#[local] Ltac matchify :=
  cbv [ret raise catch bind
         ErrorWithState.Monad_errS ErrorWithState.Exception_errS]
    in *.
Lemma genIR_nonempty_blocks :
  forall op nextblock s s' b0_id blocks,
    genIR op nextblock s ≡ inr (s', (b0_id, blocks)) ->
    exists b0 blocks', blocks ≡ b0 :: blocks'.
Proof.
  induction op;
    intros * GENIR.
  (* induction hypothesis only necessary for [DSHSeq], and slows others down *)
  1-9: try clear IHop.
  1-9: unfold
         genIR, genNop, genFSHAssign, genIMapBody,
      genBinOpBody, genMemMap2Body,
      genPower, genMemInit, genWhileLoop in *.
  1-9: matchify; simp; now repeat eexists.

  cbn [genIR] in GENIR.
  matchify; simp.
  eapply IHop1 in Heqs3.
  eapply IHop2 in Heqs1.
  clear - Heqs1 Heqs3.
  destruct Heqs3 as [b1 [blocks1 B1]].
  destruct Heqs1 as [b2 [blocks2 B2]].
  rewrite B1, B2.
  repeat eexists.
Qed.

Lemma genIR_entry_blk_id :
  forall op nextblock s s' b0_id b0 blocks,
  genIR op nextblock s ≡ inr (s', (b0_id, b0::blocks)) ->
  blk_id b0 ≡ b0_id.
Proof.
  induction op;
    intros * GENIR.

  1-9: try clear IHop.
  all: cbn [genIR] in *.
  1-9: unfold
         genNop, genFSHAssign, genIMapBody,
      genBinOpBody, genMemMap2Body,
      genPower, genMemInit, genWhileLoop
      in *.
  1-9: (matchify; simp; try congruence; try now find_b0_id).

  -
    cbn in Heqs4; now invc Heqs4.
  -
    matchify; simp.
    congruence.
    all: find_b0_id; cbn.
    all: copy_apply genIR_nonempty_blocks Heqs3;
      destruct H as [b0 [blocks' B]]; subst l0.
    all: eapply IHop1; rewrite Heqs3; repeat f_equal.
    all: now rewrite <-app_comm_cons in Heql1.
Qed.

Transparent denote_terminator.
Lemma denote3_term_ret :
  ∀ (g : ρ) l (m : memoryV) d e ctx x,
interp_mcfg3 (interp_mrec ctx (translate instr_to_L0' (translate exp_to_instr (denote_exp (Some d) e)))) g l m ≈ Ret3 g l m x ->
interp_mcfg3 (interp_mrec ctx (translate instr_to_L0' (translate exp_to_instr
    ⟦ TERM_Ret (d,e)⟧t))) g l m ≈ Ret3 g l m (inr x).
Proof.
  unfold denote_terminator.
  intros * EQ; cbn.
  rewrite 2 translate_bind, interp_mrec_bind, interp3_bind.
  rewrite EQ, bind_ret_l.
  rewrite 2 translate_ret, interp_mrec_ret, interp3_ret.
  reflexivity.
Qed.
Opaque denote_terminator.

(* denote_exp_LR *)
Lemma denote3_exp_LR :
  forall ctx (id : raw_id) τ g l m v s,
    Maps.lookup id l ≡ Some v ->
    interp_mcfg3 (interp_mrec ctx (translate instr_to_L0'
                                     (translate exp_to_instr (denote_exp (Some τ) (EXP_Ident (ID_Local id)))))) g (l,s) m ≈ Ret3 g (l,s) m v.
Proof.
  intros.
  eapply interp_cfg3_to_mcfg3.
  rewrite denote_exp_LR; [reflexivity |]; eauto.
Qed.


Lemma interp_cfg3_StackPop: forall g a f s m,
    ℑs3 (trigger StackPop) g (a,f :: s) m ≈
      Ret3 g (f,s) m tt.
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  reflexivity.
Qed.

Lemma interp3_StackPop: forall foo g a f s m,
    interp_mcfg3 (interp_mrec (mcfg_ctx foo) (trigger (@StackPop raw_id uvalue))) g (a,f :: s) m ≈
      Ret3 g (f,s) m tt.
Proof.
  intros.
  rewrite interp_mrec_trigger.
  cbn.
  match goal with
  |- context[ITree.trigger ?e] => assert (EQ: e ≡ (subevent _ (inr1 (inr1 (inr1 (inl1 (inr1 (@StackPop raw_id uvalue)))))))) by reflexivity; rewrite EQ; clear EQ
  end.
  rewrite (interp_mcfg3_trigger_is_handler3_strong).
  cbn.
  rewrite bind_ret_l.
  rewrite 3 tau_eutt; reflexivity.
Qed.

Lemma denote3_instr_load :
  forall ctx (i : raw_id) volatile τ τp ptr align g l l' m a uv s,
    ⟦ ptr at τp ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_Addr a) ->
    read m a τ ≡ inr uv ->
    interp_mcfg3 (interp_mrec ctx (translate instr_to_L0' ⟦ (IId i, INSTR_Load volatile τ (τp, ptr) align) ⟧i)) g (l,s) m ≈ Ret3 g ((Maps.add i uv l'),s) m tt.
Proof.
  intros.
  eapply interp_cfg3_to_mcfg3.
  rewrite denote_instr_load; [reflexivity | |]; eauto.
Qed.

(* Notation "'with' 'ℑs3' 'and' 'context' ctx 'computing' t 'from' g l m" *)
(*   := (ℑs3 (mrecursive ctx _ t) g l m) *)
(*        (only printing, at level 0, *)
(*        format "'with'  'ℑs3'  'and'  'context'  ctx  'computing' '//' t '//' 'from' '//' g '//' l '//' m '//'"). *)
  
Lemma get_array_cell_signleton 
  (mem : μ) (addr : Addr.addr) (i : nat) (y : uvalue) (b64 : DynamicValues.ll_double) :
  get_array_cell mem addr i DTYPE_Double ≡ inr (UVALUE_Double b64) →
  get_array_cell mem addr i (DTYPE_Array (Npos 1) DTYPE_Double) ≡ inr y ->
  y ≡ UVALUE_Array [UVALUE_Double b64].
Proof.
  intros * Y Y'.
  destruct addr as (addr, off).
  cbn in *.
  repeat break_match; try inl_inr.
  invc Y; invc Y'.
  unfold read_in_mem_block.
  generalize dependent (off +
                          DynamicValues.Int64.unsigned
                            (DynamicValues.Int64.repr (Z.of_nat i)) * 8)%Z;
    intros z READ.
  unfold read_in_mem_block in READ.
  cbv [sizeof_dtyp BinNat.N.mul] in *.
  replace (1 * 8)%positive with 8%positive by reflexivity.
  remember (lookup_all_index z (Npos 8) bytes SUndef) as bt.
  rewrite <-app_nil_r with (l:=bt).
  replace (Npos 1) with (BinNat.N.succ N0) by reflexivity.
  erewrite deserialize_array_element.
  6: reflexivity.
  instantiate (1:=[]).
  now rewrite app_nil_r.
  constructor.
  constructor.
  subst.
  {
    eapply deserialize_sbytes_dvalue_all_not_sundef.
    rewrite READ.
    instantiate (1:=DVALUE_Double b64).
    reflexivity.
  }
  reflexivity.
  subst; now rewrite lookup_all_index_length.
  reflexivity.
Qed.

Lemma top_to_LLVM :
  forall (a : Vector.t CarrierA 3) (* parameter *)
    (x : Vector.t CarrierA dynwin_i) (* input *)
    (y : Vector.t CarrierA dynwin_o), (* y - output *)

      (* Evaluation of the source program.
         The program is fixed and hard-coded: the result is not generic,
         we provide a "framework". *)
      dynwin_orig a x = y →

      (* We cannot hide away the [R] level as we axiomatize the real to float
         approximation performed *)
      ∀
        (data : list binary64)
        (PRE : heq_list
                 (Vector.to_list a ++ Vector.to_list x)
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
    as (dynwin_F_memory & data_garbage & HINIT & RFM & RFΣ);
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

  (* We know that we can see the evaluation of the FHCOL operator under an itree-lense  *)
  pose proof (Denote_Eval_Equiv _ _ _ _ _ EVF) as EQ.

  (* Breaking down the compilation process *)
  Opaque genIR.
  generalize COMP; intros COMP'.
  unfold compile_w_main,compile in COMP.
  simpl in COMP.
  simp.

  unfold initIRGlobals in Heqs0; cbn in Heqs0.
  break_let; cbn in Heqs0.
  inv_sum/g.

  unfold initXYplaceholders in Heqs3; cbn in Heqs3.
  break_let; cbn in Heqs3.
  inv_sum/g.

  unfold LLVMGen in Heqs1.
  Opaque genIR.
  cbn in Heqs1.
  break_match; [inv_sum |]/g. (* genIR DynWin_FHCOL_hard ("b" @@ "0" @@ "") Γi *)
  break_and; cbn in Heqs1/g.
  destruct s/g.
  copy_apply genIR_nonempty_blocks Heqs;
    destruct H1 as (b' & blocks & L0); subst l0.
  copy_apply genIR_entry_blk_id Heqs;
    subst b; rename b' into b.
  break_match; [inv_sum |]/g.
  break_and; cbn in Heqs0 /g. rename l0 into bks2.
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

  remember (b :: blocks) as bks1.
  rename b0 into bk.
  rename l2 into exps1, l3 into exps3.
  rename i into s3, i0 into s2, i1 into s1.

  assert (HgenIR : genIR DynWin_FHCOL_hard "b0" Γi ≡ inr (s3, (blk_id b, bks1)))
    by apply Heqs; clear Heqs.
  rename Heqs2 into Hdrop.

  replace s3 with s2 in *; revgoals.
  { clear - Heqs0.
    now invc Heqs0.
  }

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

  apply heq_list_app in PRE as (A & X & -> & EQA & EQX).

  onAllHyps move_up_types.
  edestruct @eutt_ret_inv_strong as (RESLLVM & EQLLVMINIT & INVINIT); [apply INIT_MEM |].
  destruct RESLLVM as (memI & [ρI sI] & gI & []).
  inv INVINIT.
  destruct fun_decl_inv as [(main_addr & EQmain) (dyn_addr & EQdyn)].
  cbn in EQdyn.

  destruct anon_decl_inv as [(a0_addr & EQa0) (a1_addr & EQa1)].
  destruct genv_mem_wf_inv as [genv_ptr_uniq_inv genv_mem_bounded_inv].

  assert (Γ s1 ≡ [(ID_Global "a", TYPE_Pointer (TYPE_Array (Npos 3) TYPE_Double))])
  as HΓs1.
  {
    erewrite dropLocalVars_Gamma_eq with (s1 := s2) (s2 := Γi); revgoals.
    - symmetry.
      eapply Context.genIR_Γ.
      eassumption.
    - cbn.
      reflexivity.
    - assumption.
    - reflexivity.
  }

  set (ρI' := (alist_add (Name "Y1") (UVALUE_Addr a1_addr)
              (alist_add (Name "X0") (UVALUE_Addr a0_addr) ρI))).

  eassert (state_inv' : state_invariant _ Γi _ (memI, (ρI', gI))).
  {
    eapply state_invariant_Γi with (ρI := ρI); eassumption || auto.
    eapply state_invariant_Γ'.
    - eassumption.
    - cbn.
      rewrite HΓs1.
      reflexivity.
    - apply Γi'_bound.
  }

  onAllHyps move_up_types.

  match goal with
    |- context [semantics_llvm ?x] => change x with (MCFG exps3 exps1 bk bks2)
  end.

  (* We process the initialization phase first *)
  set (fundefs :=
    [(DVALUE_Addr dyn_addr, ⟦ TFunctor_definition typ dtyp (typ_to_dtyp []) (DYNWIN bk bks2) ⟧f);
     (DVALUE_Addr main_addr, ⟦ TFunctor_definition typ dtyp (typ_to_dtyp []) MAIN ⟧f)]).

  set (left_computation := ℑs3 (x1 <- trigger (@GlobalRead raw_id _ "main");;
             denote_mcfg fundefs DTYPE_Void (dvalue_to_uvalue x1) main_args
        ) gI (ρI, sI) memI).
  assert (semantics_llvm (MCFG exps3 exps1 bk bks2) ≈ left_computation).
  {
    subst left_computation; cbn.
    match goal with
    |- _ ≈ ?x => remember x
    end.

    unfold semantics_llvm, semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm.

    simpl bind.
    rewrite interp3_bind.
    (* We know that building the global environment is pure,
         and satisfy a certain spec.
     *)
    rewrite EQLLVMINIT.
    rewrite bind_ret_l.

    rewrite interp3_bind.

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
    reflexivity.
  }
  setoid_rewrite H1; clear H1.

  Definition cont_ocfg : _ -> itree instr_E _ :=
    (λ r : block_id * block_id + uvalue,
        match r with
        | inl bid => LLVMEvents.raise ("Can't find block in denote_cfg " @@ CeresSerialize.to_string (snd bid))
        | inr uv => Ret uv
        end).
  Definition calling_pop : uvalue -> itree L0' _ :=
    fun rv => trigger StackPop;;
           trigger MemPop;;
           Ret rv.
  Notation Ti := (translate instr_to_L0').
  Arguments calling_pop : simpl never.
  Arguments cont_ocfg : simpl never.
  Definition catch_and_pop : _ -> itree L0' _ :=
    fun v => Ti (cont_ocfg v) >>= calling_pop.
  Arguments catch_and_pop : simpl never.

  set (left_computation' :=
         ℑs3 (interp_mrec (Vellvm_Utils.mcfg_ctx (GFUNC dyn_addr bk bks2 main_addr))
                (Ti (⟦ MAINCFG ⟧bs (Name "main_block", Name "main_block")) >>=
                      catch_and_pop))
           gI
           ([], ρI :: sI)
           (push_fresh_frame memI)).

  assert (left_computation ≈ left_computation').
  {
    subst left_computation.
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
      clear - genv_ptr_uniq_inv EQmain EQdyn.
      intro H; inv H.
      enough (Name "main" ≡ Name "dyn_win") by discriminate.
      eapply genv_ptr_uniq_inv; eassumption || auto.
    }


    cbn.
(* Notation "'with' 'ℑs3' 'and' 'context' ctx 'computing' t 'from' g l m" *)
(*   := (ℑs3 (interp_mrec ctx t) g l m) *)
(*        (only printing, at level 0, *)
(*        format "'with'  'ℑs3'  'and'  'context'  ctx  'computing' '//' t '//' 'from' '//' g '//' l '//' m '//'"). *)


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
    subst left_computation'.
    simpl.
    rewrite translate_bind. rewrite ? interp_mrec_bind.
    rewrite ? interp3_bind.
    rewrite bind_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?).
    destruct s.
    - unfold catch_and_pop.
      simpl; rewrite ? interp_mrec_bind, ?interp3_bind.
      reflexivity.
    - unfold catch_and_pop.
      simpl; rewrite ? interp_mrec_bind, ?interp3_bind.
      reflexivity.
  }
  setoid_rewrite H1; clear H1; clear left_computation.

  Infix ">>=" := (ITree.bind).
  Notation "f >>> g" := (fun x => f x >>= g) (at level 10).
  Notation "'M' E X" := (itree E X) (at level 0).

  Definition cont_ocfg' : _ -> itree L0' _ :=
    (λ r : block_id  + uvalue,
        Ti match r with
        | inl bid => ⟦ MAINCFG ⟧bs (Name "main_block", bid)
        | inr uv => Ret (inr uv)
        end).

  set (left_computation :=
         ℑs3 (interp_mrec (Vellvm_Utils.mcfg_ctx (GFUNC dyn_addr bk bks2 main_addr))

                (Ti (⟦ TFunctor_list' typ dtyp (typ_to_dtyp nil) (blks (df_instrs (DYNWIN bk bks2)) )⟧bs (init (df_instrs (DYNWIN bk bks2)), init (df_instrs (DYNWIN bk bks2))))
                   >>= catch_and_pop
                 ;;
                 Ti
                   (denote_instr
                      (IId "z",
                        INSTR_Load false (DTYPE_Array (Npos 1) DTYPE_Double)
                          (DTYPE_Pointer, EXP_Ident (ID_Global (Anon 1%Z)))
                          None);;
                    (translate exp_to_instr (denote_terminator (TERM_Ret
                                                                  (DTYPE_Array (Npos 1) DTYPE_Double,
                                                                    (EXP_Ident (ID_Local (Name "z"))))))))
                   >>= cont_ocfg' >>> catch_and_pop)
           )
           gI
           ([(Name "X0", UVALUE_Addr a0_addr) ; (Name "Y1", UVALUE_Addr a1_addr)], [] :: ρI :: sI)
           (push_fresh_frame (push_fresh_frame memI))).

  assert (left_computation' ≈ left_computation).

  {
    subst left_computation'.
    cbn.
    rewrite interp_mrec_bind.
    rewrite interp3_bind.
    cbn.
    hide.
    onAllHyps move_up_types.
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

    Notation t2d := (typ_to_dtyp _).
    Notation double := (TYPE_Double).
    Notation arr := (TYPE_Array).
    Notation void := (DTYPE_Void).
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

    (* Evaluating the arguments *)
    Import AlistNotations.
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
    rewrite denote_mcfg_ID_Global; cycle 1.
    eassumption.
    rewrite !bind_ret_l, translate_ret, interp_mrec_ret, interp3_ret, bind_ret_l.
    rewrite translate_ret, interp_mrec_ret, interp3_ret, bind_ret_l.

    (* Calling convention: pushing fresh frames *)
    subst.
    rewrite !bind_bind; cbn; focus_single_step_l; unfold DYNWIN at 1; cbn; rewrite bind_ret_l.
    cbn; rewrite interp_mrec_bind, interp_mrec_trigger, interp3_bind.

    onAllHyps move_up_types.

    (* Function call, we first create a new memory frame *)
    rewrite interp3_MemPush, bind_ret_l, interp_mrec_bind, interp_mrec_trigger.
    cbn; rewrite interp3_bind, interp3_StackPush, bind_ret_l.
    subst i.

    rewrite translate_bind, interp_mrec_bind,interp3_bind, bind_bind.
    rewrite interp_mrec_bind, interp3_bind.
    cbn.
    rewrite bind_bind.

    Notation "'with' 'ℑs3' 'and' 'context' ctx 'computing' t 'from' g l m"
      := (ℑs3 (interp_mrec ctx t) g l m)
           (only printing, at level 0,
             format "'with'  'ℑs3'  'and'  'context'  ctx  'computing' '//' '//' t '//' '//' 'from' '//' g '//' l '//' m '//'").

    unfold left_computation.
    cbn; rewrite ? interp_mrec_bind, ?interp3_bind, ?bind_bind.
    apply eutt_eq_bind.
    intros (? & ? & ? & ?).
    cbn.
    unfold catch_and_pop at 2, cont_ocfg; cbn.
    destruct s.
    {
      setoid_rewrite interp_mrec_bind; setoid_rewrite interp3_bind.
      rewrite bind_bind. idtac.
      unfold LLVMEvents.raise.
      rewrite translate_bind.
      setoid_rewrite interp_mrec_bind; setoid_rewrite interp3_bind.
      rewrite ?bind_bind.
      apply eutt_eq_bind; intros [? [? [? []]]].
    }
    rewrite ?translate_ret, ?bind_ret_l.
    rewrite interp_mrec_ret, interp3_ret, bind_ret_l.
    apply eutt_eq_bind.
    intros (? & ? & ? & ?).
    rewrite bind_ret_l.
    cbn; rewrite ?translate_bind, ?interp_mrec_bind, ?interp3_bind, ?bind_bind.
    symmetry; rewrite ?translate_bind, ?interp_mrec_bind, ?interp3_bind, ?bind_bind.
    symmetry.
    rewrite denote_code_singleton.
    rewrite ? typ_to_dtyp_D_array, Utils.typ_to_dtyp_P.
    apply eutt_eq_bind.
    intros (? & ? & ? & ?).
    cbn; rewrite ?translate_bind, ?interp_mrec_bind, ?interp3_bind, ?bind_bind.
    symmetry; rewrite ?translate_bind, ?interp_mrec_bind, ?interp3_bind, ?bind_bind.
    symmetry.
    eapply eutt_eq_bind.
    intros (? & ? & ? & ?).
    symmetry; rewrite ?translate_bind, ?interp_mrec_bind, ?interp3_bind, ?bind_bind.
    symmetry.
    apply eutt_eq_bind.
    intros (? & ? & ? & ?).
    reflexivity.
  }
  setoid_rewrite H1; clear H1; clear left_computation'.

  (* We are getting closer to business: instantiating the lemma
     stating the correctness of the compilation of operators *)
   set (ρI'' := (alist_add (Name "X0") (UVALUE_Addr a0_addr)
                  (alist_add (Name "Y1") (UVALUE_Addr a1_addr) []))).

  eassert (state_inv'' : state_invariant _ Γi _ (push_fresh_frame (push_fresh_frame memI), (ρI'', gI))).
  {
    apply state_invariant_frames' with (mV := memI).
    destruct memI; auto.
    unfold push_fresh_frame.
    eapply state_invariant_Γi; eauto.
    eapply state_invariant_Γ'; [eapply state_inv | | apply Γi'_bound].
    unfold Γi'; cbn.
    rewrite HΓs1; auto.
  }

  unshelve epose proof
    @compile_FSHCOL_correct _ _ _ dynwin_F_σ dynwin_F_memory _ _
    (blk_id b)
    _ gI ρI'' (push_fresh_frame (push_fresh_frame memI)) HgenIR _ _ _ _
    as RES.
  { clear - EQ.
    unfold no_failure, has_post.
    apply eutt_EQ_REL_Reflexive_.
    intros * [H1 H2] H; subst.
    apply eutt_ret_inv_strong' in EQ as [[m ()] [EQ _]].
    rewrite interp_mem_interp_helix_ret_eq in H2.
    + apply Returns_Ret in H2; inv H2.
    + rewrite EQ; apply eutt_Ret; auto.
  }
  { unfold bid_bound, VariableBinding.state_bound.
    exists "b",
      {| block_count := 0; local_count := 0; void_count := 0; Γ := Γ Γi |},
      {| block_count := 1; local_count := 0; void_count := 0; Γ := Γ Γi |}.
    cbn; auto.
  }
  { apply state_inv''.
  }
  { unfold Gamma_safe.
    intros id B NB.
    clear - B NB.
    dep_destruct NB.
    clear NB w e v.
    rename e0 into H0.
    destruct B as [name [s' [s'' [P [C1 [C2 B]]]]]].
    cbn in *.
    inv B.
    clear C1.
    cbn in *.
    repeat (destruct n; try discriminate).
    + cbn in H0.
      invc H0.
      replace "Y1" with ("Y" @@ string_of_nat 1) in H1 by auto.
      destruct name.
      { unfold append in H1 at 2.
        pose proof IdLemmas.string_of_nat_not_alpha (local_count s').
        rewrite <- H1 in H.
        apply IdLemmas.string_append_forall in H as [H _].
        cbn in H.
        discriminate. }
      destruct name.
      { invc H1.
        eapply string_of_nat_inj; [| eassumption].
        intro H.
        rewrite <- H in C2.
        invc C2.
        invc H1. }
      invc H1.
      fold append in H3.
      destruct name.
      { unfold append in H3.
        eapply IdLemmas.string_of_nat_not_empty.
        symmetry.
        eassumption. }
      invc H3.
    + cbn in H0.
      invc H0.
      replace "X0" with ("X" @@ string_of_nat 0) in H1 by auto.
      destruct name.
      { unfold append in H1 at 2.
        pose proof IdLemmas.string_of_nat_not_alpha (local_count s').
        rewrite <- H1 in H.
        apply IdLemmas.string_append_forall in H as [H _].
        cbn in H.
        discriminate. }
      destruct name.
      { invc H1.
        eapply string_of_nat_inj; [| eassumption].
        intro H.
        rewrite <- H in C2.
        invc C2. }
      invc H1.
      fold append in H3.
      destruct name.
      { unfold append in H3.
        eapply IdLemmas.string_of_nat_not_empty.
        symmetry.
        eassumption. }
      invc H3.
  }

  eapply interp_mem_interp_helix_ret in EQ.
  eapply eutt_ret_inv_strong' in EQ.
  destruct EQ as ([? |] & EQ & TMP); inv TMP.
  rewrite EQ in RES.
  clear EQ.
  match type of RES with
  | eutt _ _ (interp_cfg3 (denote_ocfg ?ocfg ?b) ?g ?ρ (push_fresh_frame ?m)) =>
      let H := fresh in
      let H' := fresh in
      pose proof memory_scoping ocfg b g ρ m as H;
      pose proof has_post_enrich_eutt_r _ _ RES H as H';
      clear H RES; rename H' into RES
  end.

  destruct p as [? []].
  inv H3; cbn in H1; clear H2.
  edestruct @eutt_ret_inv_strong as (RESLLVM2 & EQLLVM2 & INV2); [apply RES | clear RES].
  destruct RESLLVM2 as (mem2 & ρ2 & g2 & v2).
  match type of Heqs0 with
  | inr (_, (_, ?x)) ≡ inr _ =>
      assert (EQbks: bk :: bks2 ≡ b :: x)
      by now invc Heqs0
  end.
  destruct INV2 as [[INV2 [[from EQ] INV3]] FREE_INV].
  subst v2.
  destruct FREE_INV as (mem2' & EQ_mem2 & ALLOC_INV & READ_INV).

  set (left_computation' :=
         ℑs3 (interp_mrec (Vellvm_Utils.mcfg_ctx (GFUNC dyn_addr bk bks2 main_addr))
                (calling_pop UVALUE_None;; Ti
                                             (denote_instr
                                                (IId "z",
                                                  INSTR_Load false (DTYPE_Array (Npos 1) DTYPE_Double)
                                                    (DTYPE_Pointer, EXP_Ident (ID_Global (Anon 1%Z)))
                                                    None);;
                                              (translate exp_to_instr (denote_terminator (TERM_Ret
                                                                                            (DTYPE_Array (Npos 1) DTYPE_Double,
                                                                                              (EXP_Ident (ID_Local (Name "z")))))))) >>= cont_ocfg' >>> catch_and_pop
                )
           )
           g2
           (ρ2, [] :: ρI :: sI)
           mem2).

  assert (left_computation ≈ left_computation').
  {
    subst left_computation.

    unfold DYNWIN at 2 3; cbn.

    unfold init_of_definition.
    cbn.

    unfold DYNWIN at 1.
    cbn[df_instrs blks cfg_of_definition fst snd].
    assert (EQbk: bk ≡ b) by (now invc Heqs0).
    rewrite EQbk in *.
    assert (EQbk': Some bk ≡ Some b) by (subst; reflexivity).
    clear EQbk.
    rewrite EQbks.
    rewrite app_comm_cons.
    remember (b :: blocks) as bks1.
    unfold TFunctor_list'; rewrite map_app.
    rewrite denote_ocfg_app; [| apply list_disjoint_nil_l].
    rewrite translate_bind,interp_mrec_bind.
    rewrite interp3_bind, bind_bind.
    subst; focus_single_step_l.

    (* replace bk with b in * by now invc Heqs0. *)
    (* clear Heqs0. *)

    (* eapply interp_mem_interp_helix_ret in EQ. *)
    (* eapply eutt_ret_inv_strong' in EQ. *)
    (* destruct EQ as ([? |] & EQ & TMP); inv TMP. *)
    (* rewrite EQ in RES. *)
    (* clear EQ. *)

    (* match type of RES with *)
    (* | eutt _ _ (interp_cfg3 (denote_ocfg ?ocfg ?b) ?g ?ρ (push_fresh_frame ?m)) => *)
    (*     let H := fresh in *)
    (*     let H' := fresh in *)
    (*     pose proof memory_scoping ocfg b g ρ m as H; *)
    (*     pose proof has_post_enrich_eutt_r _ _ RES H as H'; *)
    (*     clear H RES; rename H' into RES *)
    (* end. *)

    (* destruct p as [? []]. *)
    (* inv H3; cbn in H1; clear H2. *)
    (* edestruct @eutt_ret_inv_strong as (RESLLVM2 & EQLLVM2 & INV2); [apply RES | clear RES]. *)
    (* destruct RESLLVM2 as (mem2 & ρ2 & g2 & v2). *)

    subst ρI''.
    match goal with
      |- context[interp_mrec ?X] =>
        eapply interp_cfg3_to_mcfg3 with (ctx := X) (s := [] :: ρI :: sI) in EQLLVM2
    end.
    match goal with
      |- context[denote_ocfg ?a] => change a with (convert_typ [] (b :: blocks))
    end.
    rewrite interp_mrec_bind, interp3_bind.
    rewrite EQLLVM2.
    rewrite bind_ret_l.
    onAllHyps move_up_types.
    (* subst v2. *)
    rewrite interp_mrec_bind, interp3_bind.
    focus_single_step_l.
    rewrite denote_ocfg_unfold_in; cycle -1.
    cbn; rewrite find_block_eq; reflexivity.
    cbn.
    rewrite denote_block_unfold.
    rewrite denote_no_phis.
    rewrite bind_ret_l.
    rewrite bind_bind.
    rewrite denote_code_nil.
    rewrite bind_ret_l.
    Transparent denote_terminator.
    unfold denote_terminator.
    Opaque denote_terminator.
    cbn.
    rewrite translate_ret.
    rewrite bind_ret_l.
    rewrite translate_ret, interp_mrec_ret, interp3_ret, bind_ret_l.
    subst i.
    unfold catch_and_pop, cont_ocfg.
    cbn.
    rewrite translate_ret, bind_ret_l.
    unfold left_computation'.
    cbn.
    rewrite interp_mrec_bind, interp3_bind.
    assert (bk ≡ b) by (now inv EQbk').
    subst.
    eapply eutt_eq_bind.
    intros (? & ? & ? & ?).
    reflexivity.

  }
  setoid_rewrite H2; clear H2; clear left_computation.

  (* instantiatiate read before introducing existential *)
  assert (T: allocated a1_addr mem2').
  {
    apply ALLOC_INV.
    apply st_id_allocated in state_inv''.
    move state_inv' at bottom.

    apply mem_is_inv in state_inv'.
    cbn in state_inv'.
    specialize (state_inv' 1).
    cbn in state_inv'.
    specialize (state_inv' (FHCOL.DSHPtrVal 1 dynwin_o') (false)).
    specialize (state_inv' (TYPE_Pointer (TYPE_Array (Npos xH) TYPE_Double)) (ID_Local "Y1")).
    autospecialize state_inv'; [reflexivity |].
    autospecialize state_inv'; [reflexivity |].
    cbn in state_inv'.
    destruct state_inv' as (a1_addr' & ? & ? & A1_MEMI & ρI'Y1 & ?).
    subst ρI'.
    replace a1_addr' with a1_addr in * by now cbv in ρI'Y1.
    invc H2.
    clear - A1_MEMI.
    apply dtyp_fits_allocated in A1_MEMI.
    destruct memI.
    cbn in *.
    assumption.
  }

  pose proof allocated_can_read _ _ DTYPE_Double T as [y_ival' YIV'].
  pose proof allocated_can_read _ _ (typ_to_dtyp nil (TYPE_Array (Npos xH) TYPE_Double)) T as [y_ival YIV].

  clear INIT_MEM EQLLVMINIT.

  Lemma i3_bind :
    ∀ (R S : Type) (t : itree L0' R) (k : R → itree _ S) (g : alist raw_id dvalue)
      (l : alist raw_id uvalue * stack) (m : μ) ctx,
      ℑs3 (interp_mrec ctx (t >>= k)) g l m
        ≈ ℑs3 (interp_mrec ctx t) g l m >>=
        (λ x_ : μ * (alist raw_id uvalue * stack * (alist raw_id dvalue * R)),
            let (m', p) := x_ in
            let (l', p0) := p in let (g', x) := p0 in ℑs3 (interp_mrec ctx (k x)) g' l' m').
  Proof.
    intros.
    rewrite interp_mrec_bind,interp3_bind.
    reflexivity.
  Qed.

  set (left_computation :=
         ℑs3 (interp_mrec (Vellvm_Utils.mcfg_ctx (GFUNC dyn_addr bk bks2 main_addr))
                (catch_and_pop (inr y_ival)))
           gI
           (Maps.add (Name "z") y_ival [], ρI :: sI)
           mem2').

  assert (left_computation' ≈ left_computation).
  {
    subst left_computation'.
    unfold calling_pop.
    cbn; rewrite ?interp_mrec_bind, ?interp3_bind.
    simpl.
    pose proof interp_mcfg3_trigger_is_handler3 unit (subevent _ (inr1 StackPop)) g2 (ρ2, [] :: ρI :: sI) mem2 as EQ; cbn in EQ.

    rewrite interp_mrec_trigger.

    rewrite EQ; clear EQ.
    rewrite 2 bind_ret_l.
    rewrite interp_mrec_bind,interp_mrec_trigger.
    rewrite interp3_bind, bind_bind.
    simpl.
    pose proof interp_mcfg3_trigger_is_handler3 unit (subevent _ MemPop) g2 ([], ρI :: sI) mem2 as EQ; cbn in EQ.
    rewrite EQ; clear EQ.
    cbn in INV3.
    cbn in INV2.

    rewrite bind_bind.
    rewrite EQ_mem2.
    cbn. rewrite ?bind_ret_l.
    cbn.
    rewrite interp_mrec_ret, interp3_ret, bind_ret_l.
    subst.
    (* rewrite bind_ret_l. *)
    rewrite translate_bind.
    (* rewrite denote_code_singleton. *)
    rewrite interp_mrec_bind,interp3_bind.
    focus_single_step_l.

    rewrite i3_bind.
    rewrite typ_to_dtyp_D_array in YIV.

    rewrite denote3_instr_load; cycle 1.
    rewrite denote_exp_GR.

    all: replace g2 with gI in * by tauto.

    2,3: eassumption.
    reflexivity.
    rewrite bind_ret_l.
    subst.
    focus_single_step_l.

    rewrite denote3_term_ret; cycle -1.
    apply denote3_exp_LR.
    eapply Maps.mapsto_lookup. apply Maps.mapsto_add_eq.
    rewrite bind_ret_l; subst i.
    unfold cont_ocfg'.
    rewrite translate_ret, bind_ret_l.
    reflexivity.
  }
  setoid_rewrite H2; clear H2; clear left_computation'.

  (* TOFIX *)
  destruct mem2' as [mem2' fs].
  assert (exists f, fs ≡ Mem.Snoc (Mem.Singleton f) nil) as [f ?] by admit.

  set (final_computation := Ret3 gI (ρI, sI) (free_frame_memory [] mem2', Mem.Singleton f) y_ival : itree E_mcfg _).

  assert (left_computation ≈ final_computation).
  {
    unfold left_computation.
    unfold catch_and_pop, cont_ocfg.
    cbn; rewrite i3_bind.
    rewrite translate_ret, interp_mrec_ret, interp3_ret.
    rewrite bind_ret_l.
    unfold calling_pop.
    cbn; rewrite i3_bind.
    rewrite interp3_StackPop.
    rewrite bind_ret_l.
    rewrite i3_bind.
    rewrite interp_mrec_trigger.
    pose proof interp_mcfg3_trigger_is_handler3 unit (subevent _ MemPop) gI (ρI , sI) (mem2',fs) as EQ; cbn in EQ.
    rewrite EQ; clear EQ.
    rewrite H2.
    cbn.
    rewrite ? bind_ret_l.
    rewrite interp_mrec_ret, interp3_ret.
    reflexivity.
  }
  setoid_rewrite H3; clear H3; clear left_computation.

  unfold final_computation.
  exists gI, (ρI, sI), (free_frame_memory [] mem2', Mem.Singleton f), y_ival.
  split; [reflexivity |].

  (** * zoickx checkpoint *)

  apply READ_INV in YIV.
  destruct INV3 as [RHO2 _]; cbn in RHO2.
  clear - INV2 H1 LUF TRF HgenIR H TRR YIV RHO2.
  destruct INV2 as [MINV _ _ _ _ _ _].
  specialize (MINV 1).
  specialize (MINV (FHCOL.DSHPtrVal 1 dynwin_o') false).
  specialize (MINV (TYPE_Pointer (TYPE_Array (Npos xH) TYPE_Double)) (ID_Local "Y1")).

  
  apply Context.genIR_Γ in HgenIR; rewrite <-HgenIR in *.
  cbn in MINV.
  do 2 (autospecialize MINV; [reflexivity |]).
  
  destruct MINV as (ptry & t & TE & TF & PTRY & MY).
  invc TE.
  replace ptry with a1_addr in *.
  2: {
    clear - RHO2 PTRY.
    eapply local_scope_preserve_modif in RHO2.
    unfold local_scope_preserved in RHO2.
    specialize (RHO2 "Y1").
    autospecialize RHO2.
    {
      Require Import LidBound.
      eapply lid_bound_between_shrink_up.
      instantiate (1:= {|
                        block_count := 1;
                        local_count := 2;
                        void_count := 0;
                        Γ :=
                          [(ID_Global "a", TYPE_Pointer (TYPE_Array (Npos 3) double));
                           (ID_Local "Y1", TYPE_Pointer (TYPE_Array (Npos 1) double))]
                      |}).
      cbv; lia.
      
      eapply lid_bound_between_incLocalNamed.
      instantiate (1:="Y"); reflexivity.
      instantiate (1:= {|
                        block_count := 1;
                        local_count := 1;
                        void_count := 0;
                        Γ :=
                          [(ID_Global "a", TYPE_Pointer (TYPE_Array (Npos 3) double));
                           (ID_Local "Y1", TYPE_Pointer (TYPE_Array (Npos 1) double))]
                      |}).
      cbv.
      reflexivity.
    }
    subst ρI''.
    rewrite alist_find_neq in RHO2 by discriminate.
    rewrite alist_find_add_eq in RHO2 by reflexivity.
    cbv [local_id] in *.
    rewrite PTRY in RHO2.
    now invc RHO2.
  }
  
  autospecialize MY; [reflexivity |].
  destruct MY as (y_rmem'' & FMY & IMY).
  replace dynwin_y_addr with 1 in * by reflexivity.
  
  (* rewrite <-H1 in LUF. *)
  replace f_omemory with m in LUF by admit.
  rewrite FMY in LUF.
  some_inv.
  
  specialize (TRR dynwin_y_offset).
  unshelve erewrite MSigmaHCOL.MHCOL.mem_lookup_ctvector_to_mem_block in TRR.
  constructor.
  unfold final_rel_val, HCOLImpl.Scalarize.
  rewrite VecUtil.Vhead_nth.
  
  (* poor man's generalize dependent *)
  remember (@VecUtil.Vnth (@CarrierA RasCarrierA.CarrierDefs_R) 
              (S O) y O (Nat.lt_0_succ O)) as yr.
  replace (@VecUtil.Vnth (@CarrierA RasCarrierA.CarrierDefs_R) dynwin_o y
             dynwin_y_offset (le_n dynwin_o))
    with yr
    in *
      by (subst yr; f_equal; apply proof_irrelevance).
  clear Heqyr.
  
  inv TRF.
  {
    exfalso.
    clear - H2 TRR.
    unfold RHCOLEval.mem_lookup in *.
    rewrite <-H2 in TRR.
    some_none.
  }
  
  unfold RHCOLEval.mem_lookup in *.
  rewrite <-H0 in TRR.
  some_inv.
  symmetry in TRR; invc TRR.
  
  rename b0 into yf.
  
  specialize (IMY Int64.zero yf).
  (* rewrite LUF in IMY. *) replace y_rmem'' with y_fmem in IMY by admit.
  setoid_rewrite H2 in IMY.
  autospecialize IMY; [reflexivity |].
  rewrite typ_to_dtyp_D_array in *.

  erewrite read_array in YIV.
  2: eapply can_read_allocated; eassumption.
  2: {
    instantiate (1:=(MInt64asNT.to_nat Int64.zero)).
    instantiate (1:=Npos 1).
    cbn.
    replace (Z.of_nat (MInt64asNT.to_nat Int64.zero)) with 0%Z by reflexivity.
    clear.
    destruct a1_addr as [a off].
    unfold handle_gep_addr.
    cbn.
    replace (DynamicValues.Int64.unsigned (DynamicValues.Int64.repr 0))
      with 0%Z
      by reflexivity.
    repeat f_equal.
    lia.
  }

  assert (y_ival ≡ UVALUE_Array [UVALUE_Double yf])
    by (eapply get_array_cell_signleton; eassumption).

  subst.
  now exists yf.
Admitted.
