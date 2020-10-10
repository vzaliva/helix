Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.

(* Import ProofNotations. *)
Import ListNotations.

Open Scope Z.
Open Scope list.

Set Implicit Arguments.
Set Strict Implicit.

(* YZ TODO: Check that this is global and factor it in prelude *)
Typeclasses Opaque equiv.

(** * Correctness of the compilation of numerical expressions

     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [ genNexpr].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     Compiler side:
     * s1 s2: IRState
     Vellvm side:
     * c : code
     * e : exp typ

 *)

  Lemma state_invariant_alist_fresh:
    forall σ s s' memH memV l g id,
      state_invariant σ s memH (memV, (l,g)) ->
      incLocal s ≡ inr (s',id) ->
      alist_fresh id l.
  Proof.
    intros * [] LOC.
    apply concrete_fresh_fresh in incLocal_is_fresh.
    eapply incLocal_is_fresh; eauto.
  Qed.

  Hint Resolve memory_invariant_ext_local: core.
  Ltac solve_lu :=
    match goal with
    | |- @Maps.lookup _ _ local_env _ ?id ?l ≡ Some _ =>
      eapply memory_invariant_LLU; [| eassumption | eassumption]; eauto
    | |- @Maps.lookup _ _ global_env _ ?id ?l ≡ Some _ =>
      eapply memory_invariant_GLU; [| eassumption | eassumption]; eauto
     end.

  Ltac check_state_invariant :=
    match goal with
      |- state_invariant _ _ _ (_, (alist_add _ _ _, _)) =>
      eapply state_invariant_add_fresh; [now eauto | (eassumption || check_state_invariant)]
    end.

  Ltac solve_alist_fresh :=
    (reflexivity ||
     eapply state_invariant_alist_fresh; now eauto).

  Ltac solve_sub_alist :=
    (reflexivity ||
     apply sub_alist_add; solve_alist_fresh).


Section NExpr.
  
  (** At the top level, the correctness of genNExpr is expressed as the denotation of the operator being equivalent
      to the bind of denoting the code followed by denoting the expression.
      However this is not inductively stable, we only want to plug the expression at the top level.
      We therefore instead carry the fact about the denotation of the expression in the invariant. (Is there another clever way?)
   *)
  Definition genNExpr_exp_correct_ind (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
            interp_cfg
              (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
              g l' memV ≈
              Ret (memV,(l',(g,UVALUE_I64 i))).

  (**
     We package the local specific invariants. Additionally to the evaluation of the resulting expression,
     we also state that evaluating the code preserves most of the state, except for the local state being
     allowed to be extended with fresh bindings.
   *)
  Record genNExpr_rel_ind
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct_ind e mf stf;
    monotone : ext_local mi sti mf stf
    }.

End NExpr.

Module VIR_Notations.
  (* We define print-only surface syntax for VIR *)

  (* Identifiers *)
  Notation "'%'" := ID_Local (only printing).
  Notation "'@'" := ID_Global (only printing).

  (* Expressions *)
  Notation "e" := (EXP_Integer e) (at level 10,only printing). 
  Notation "i" := (EXP_Ident i) (at level 10,only printing). 
  Notation "'add' e f"  := (OP_IBinop (Add _ _) _ e f) (at level 10, only printing).
  Notation "'sub' e f"  := (OP_IBinop (Sub _ _) _ e f) (at level 10, only printing).
  Notation "'mul' e f"  := (OP_IBinop (Mul _ _) _ e f) (at level 10, only printing).
  Notation "'shl' e f"  := (OP_IBinop (Shl _ _) _ e f) (at level 10, only printing).
  Notation "'udiv' e f" := (OP_IBinop (UDiv _) _ e f)  (at level 10, only printing).
  Notation "'sdiv' e f" := (OP_IBinop (SDiv _) _ e f)  (at level 10, only printing).
  Notation "'lshr' e f" := (OP_IBinop (LShr _) _ e f)  (at level 10, only printing).
  Notation "'ashr' e f" := (OP_IBinop (AShr _) _ e f)  (at level 10, only printing).
  Notation "'urem' e f" := (OP_IBinop URem _ e f)      (at level 10, only printing).
  Notation "'srem' e f" := (OP_IBinop SRem _ e f)      (at level 10, only printing).
  Notation "'and' e f"  := (OP_IBinop And _ e f)       (at level 10, only printing).
  Notation "'or' e f"   := (OP_IBinop Or _ e f)        (at level 10, only printing).
  Notation "'xor' e f"  := (OP_IBinop Xor _ e f)       (at level 10, only printing).

  (* Instructions *)
  Notation "r '←' 'op' x" := ((IId r, INSTR_Op x)) (at level 10, only printing).
  Notation "r '←' 'call' x args" := ((IId r, INSTR_Call x args)) (at level 10, only printing).
  Notation "'call' x args" := ((IVoid, INSTR_Call x args)) (at level 10, only printing).
  Notation "r '←' 'alloca' t" := ((IId r, INSTR_Alloca t _ _)) (at level 10, only printing).
  Notation "r '←' 'load' t ',' e" := ((IId r, INSTR_Load _ t e _)) (at level 10, only printing).
  Notation "r '←' 'store' e ',' f" := ((IId r, INSTR_Store _ e f _)) (at level 10, only printing).

  (* Terminators *)
  Notation "'ret' τ e" := (TERM_Ret (τ, e)) (at level 10, only printing).
  Notation "'ret' 'void'" := (TERM_Ret_void) (at level 10, only printing).
  Notation "'br' c ',' 'label' e ',' 'label' f" := (TERM_Br c e f) (at level 10, only printing).
  Notation "'br' 'label' e" := (TERM_Br_1 e) (at level 10, only printing).

  (* Phi-nodes *)
  Notation "x ← 'Φ' xs" := (x,Phi _ xs) (at level 10,only printing).

  (* Types *)
  Notation "'ι' x" := (DTYPE_I x) (at level 10,only printing).
  Notation "⋆" := (DTYPE_Pointer) (at level 10,only printing).
  Notation "x" := (convert_typ _ x) (at level 10, only printing).
  Notation "x" := (typ_to_dtyp _ x) (at level 10, only printing).
  Notation "x" := (fmap (typ_to_dtyp _) x) (at level 10, only printing).
  Notation "'ι' x" := (TYPE_I x) (at level 10,only printing).
  Notation "⋆" := (TYPE_Pointer) (at level 10,only printing).
 
End VIR_Notations.

Module VIR_denotation_Notations.
  Notation "'ℐ' '(' t ')' g l m" := (interp_cfg t g l m) (only printing, at level 10).
  Notation "⟦ c ⟧" := (denote_code c) (only printing, at level 10).
  Notation "⟦ i ⟧" := (denote_instr i) (only printing, at level 10).

End VIR_denotation_Notations.

Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).

End eutt_Notations.


Module A.

  Include ITreeNotations.
  Include VIR_Notations.
  Include VIR_denotation_Notations.
  Include eutt_Notations.

  (* Notation "⟦ b , p , c , t ⟧" := (fmap _ (mk_block b p c t _)) (only printing).  *)
  (* Notation "'denote_blocks' '...' id " := (denote_bks _ id) (at level 10,only printing).  *)
  (* Notation "'IRS' ctx" := (mkIRState _ _ _ ctx) (only printing, at level 10).  *)
  (* Notation "x" := (with_cfg x) (only printing, at level 10).  *)
  (* Notation "x" := (with_mcfg x) (only printing, at level 10).  *)
  (* (* Notation "'CODE' c" := (denote_code c) (only printing, at level 10, format "'CODE' '//' c"). *) *)
  (* Notation "c" := (denote_code c) (only printing, at level 10). *)
  (* (* Notation "'INSTR' i" := (denote_instr i) (only printing, at level 10, format "'INSTR' '//' i"). *) *)
  (* Notation "i" := (denote_instr i) (only printing, at level 10). *)
  (* Notation "x" := (translate exp_E_to_instr_E (denote_exp _ x)) (only printing, at level 10).  *)
  (* Notation "⟦ t ⟧ m" := (interp_helix t m) (only printing, at level 10). *)
  
End A.

(* Definition bool_in_nat (b:bool) := if b then 0 else 1. *)
(* Coercion bool_in_nat : bool >-> nat. *)
(* Check (true = 0). *)


(* Section coercion. *)
(* Open Scope nat. *)

(*   Parameter F : Set -> Set. *)
(*   Parameter A B : Set. *)
(*   Parameter c : F A -> F B. *)

(*   Parameter g : F B -> nat. *)

(*   (* I would like to be able to use [g] over a [F A] and have a coercion introduced *) *)
(*   (* I cannot write: *)
(*   Coercion c : F A >-> F B. *)
(*   Because it wants classes on both sides. *)
(*    *) *)

(*   Section FOO. *)
(*     (* I can do: *) *)
(*     Notation FA := (F A). *)
(*     Notation FB := (F B). *)
(*     Coercion c : FA >-> FB. *)
(*     (* But that doesn't work *) *)
(*     Fail Goal forall (x : F A), 0 = g x. *)
(*   End FOO. *)

(*   Section BAR. *)
(*     (* I can try to use definitions instead: *) *)
(*     Definition FA := (F A). *)
(*     Definition FB := (F B). *)
(*     (* But then I cannot use c, I need to explicitly have FA and FB *) *)
(*     Parameter c' : FA -> FB. *)
(*     Coercion c' : FA >-> FB. *)
(*     (* But not only that, I also need explicitly the argument typed as [FA] *) *)
(*     Fail Goal forall (x : F A), 0 = g x. *)
(*     (* And even worst, so does of course [g] *) *)
(*     Fail Goal forall (x : FA), 0 = g x. *)
(*     Parameter g' : FB -> nat. *)
(*     (* So this one works, but that's too much side effects for my use case *) *)
(*     Goal forall (x : FA), 0 = g' x. *)
(*   End FOO. *)

(*   (* Is there better? *) *)

(* End coerction. *)

(* Notation codes := (code typ). *)
(* Notation coded := (code dtyp). *)
(* Definition trivial_convert_typ_code (c : codes): coded := convert_typ [] c. *)
(* Coercion trivial_convert_typ_code : codes >-> coded. *)
(* Goal forall (c' : codes), denote_code c' ≡  denote_code c'. *)
(* Goal forall (c : coded) (c' : codes), c ≡ c'. *)

Ltac vred :=
  rewrite ?typ_to_dtyp_equation;
  rewrite ?bind_ret_l;
  rewrite ?bind_bind;
  first [rewrite translate_trigger; (rewrite lookup_E_to_exp_E_Local || rewrite lookup_E_to_exp_E_Global);
         rewrite subevent_subevent, translate_trigger;
         (rewrite exp_E_to_instr_E_Local || rewrite exp_E_to_instr_E_Global); rewrite subevent_subevent |
         idtac];
  first [rewrite denote_code_nil | rewrite denote_code_singleton | rewrite denote_code_cons | rewrite convert_typ_app, denote_code_app | idtac];
  first [rewrite interp_cfg_to_L3_ret | rewrite  interp_cfg_to_L3_bind | idtac].

Ltac hred :=
  repeat (rewrite ?interp_helix_bind, ?interp_helix_Ret, ?bind_ret_l).

Ltac hstep := first [rewrite interp_helix_MemSet | rewrite interp_helix_MemLU; cycle -1 | idtac].

Ltac hvred :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred; subst X;
        let X := fresh
        in eutt_hide_right_named X; hred; subst X;
           subst R.

Ltac expstep :=
first [rewrite denote_exp_LR; cycle 1 |
         rewrite denote_exp_GR; cycle 1 |
         rewrite denote_exp_i64 |
         rewrite denote_exp_double |
         rewrite denote_ibinop_concrete; cycle 1; try reflexivity |
         rewrite denote_fbinop_concrete; cycle 1; try reflexivity |
         rewrite denote_fcmp_concrete; cycle 1; try reflexivity |
         idtac].

Ltac instrstep :=
  first [rewrite denote_instr_load; eauto; cycle 1 |
         rewrite denote_instr_intrinsic; cycle 1; try reflexivity |
         rewrite denote_instr_op; cycle 1 |
         idtac
        ].

Ltac vstep :=
  first [progress expstep | instrstep].


Arguments denote_exp : simpl never.

  Lemma genNExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕
                      genNExpr_rel_ind e memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.

    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE PRE NOFAIL.
    - (* Variable case *)
      (* Reducing the compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        hvred.
        unfold denoteNExpr in *; cbn* in *.
        simp; try_abs.
        hvred.

        (* The identifier has to be a local one *)
        destruct i0; try_abs.

        (* We establish the postcondition *)
        apply eutt_Ret; split; [| split]; eauto.
        intros l' MONO; cbn*.
        vstep.
        solve_lu.
        reflexivity.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr in *; cbn* in *.
        simp; try_abs.
        break_inner_match_goal; try_abs.
        hvred.

        edestruct memory_invariant_GLU as (ptr & LU & READ); eauto; rewrite typ_to_dtyp_equation in READ.
        vstep.

        {
          vstep.
          eauto.
          reflexivity.
        }

        apply eutt_Ret; split; [| split].
        -- cbn; check_state_invariant.

        -- intros l' MONO; cbn*.
           (* TODO *)
           vstep.
           eapply MONO, In_add_eq.
           reflexivity.
        -- repeat (split; auto); solve_sub_alist.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      hvred.

      apply eutt_Ret; split; [| split]; try now eauto.
      intros l' MONO; cbn*.
      vstep.
      reflexivity.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      hvred.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
      forward IHnexp1; eauto.
      (* onAllHyps move_up_types. *)

      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)).

      (* e2 *)
      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI).
      forward IHnexp2; eauto. 
      (* onAllHyps move_up_types. *)
      hvred.
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)).

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXPRI _ MONOF) .
      assert (l1 ⊑ l1) as L1L1 by reflexivity; specialize (EXPRF _ L1L1). 
      cbn in *.
      hvred.
      vstep.
      {
        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        clear EXPRF EXPRI.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }
      apply eutt_Ret; split; [| split].
      { cbn. eapply state_invariant_add_fresh; eauto; reflexivity. }
      {
        intros ? MONO.
        cbn.
        vstep.
        apply MONO, In_add_eq.
        reflexivity.
      }
      {
        (* TODO solver for ext_local *)
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }

    - (* NMod *)
      cbn* in *; simp; try_abs.
      hvred.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
      forward IHnexp1; eauto.
      (* onAllHyps move_up_types. *)

      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)).

      hvred.
      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI).
      forward IHnexp2; eauto. 
      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)).
      cbn; hvred.
      break_match_goal; try_abs...
      hvred.
      
      vstep.
      (* Operator evaluation *)
      {
        cbn in EXPRF.
        vstep; cbn; eauto; try reflexivity.
        eapply EXPRF; reflexivity.
        reflexivity.
        cbn; break_inner_match_goal; try reflexivity.

        (* Division by 0 *)
        exfalso.
        apply Z.eqb_eq in Heqb.
        exfalso. apply n.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }
 
      apply eutt_Ret; split; [| split]; try now eauto.
      -- cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
      -- cbn; intros ? MONO.
         vstep.
         apply MONO, In_add_eq.
         reflexivity.
      -- apply ext_local_subalist.
         etransitivity; eauto.
         etransitivity; eauto.
         apply sub_alist_add.
         apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
         eapply PREF.
         eauto.

   - (* NAdd *)

     cbn* in *; simp; try_abs.
     hvred.

     (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
     specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
     forward IHnexp1; eauto. 
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)). 

     hvred.
     specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI). 
     forward IHnexp2; eauto. 
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 

     cbn; hvred.
     vstep.
     vstep; cbn; try (eapply EXPRF || eapply EXPRI); eauto; reflexivity.
     cbn.

     apply eutt_Ret; split; [| split].
     cbn; eapply state_invariant_add_fresh; eauto.
     {
       cbn; intros ? MONO.
       vstep.
       apply MONO, In_add_eq.
       reflexivity.
     }
     {
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
       eapply PREF.
       eauto.
     }
     
   - (* NMinus *)

     cbn* in *; simp; try_abs.
     hvred.

     (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
     specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
     forward IHnexp1; eauto. 
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)). 

     hvred.
     specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI). 
     forward IHnexp2; eauto. 
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 

     cbn; hvred.
     vstep.
     vstep; cbn; try (eapply EXPRF || eapply EXPRI); eauto; reflexivity.

     apply eutt_Ret; split; [| split].
     cbn; eapply state_invariant_add_fresh; eauto.
     {
       cbn; intros ? MONO.
       vstep.
       apply MONO, In_add_eq.
       reflexivity.
     }
     {
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
       eapply PREF.
       eauto.
     }

    - (* NMult *)
     
     cbn* in *; simp; try_abs.
     hvred.

     (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
     specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
     forward IHnexp1; eauto. 
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)). 

     hvred.
     specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI). 
     forward IHnexp2; eauto. 
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 

     cbn; hvred.
     vstep.
      (* Operator evaluation *)
     {
        vstep; cbn; try (eapply EXPRF || eapply EXPRI); eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }

      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      {
        cbn; intros ? MONO.
        vstep.
        apply MONO, In_add_eq.
        reflexivity.
      }
      {
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }

    - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.


Definition genNExpr_exp_correct (σ : evalContext) (s : IRState) (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
  fun '(memH,i) '(memV,(l,(g,v))) => 
    eutt Logic.eq 
         (interp_cfg
            (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
            g l memV)
         (Ret (memV,(l,(g,UVALUE_I64 i)))).

Lemma genNExpr_correct :
  forall (* Compiler bits *) (s1 s2: IRState)
    (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
    (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

    genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
    state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
    no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
    eutt (succ_cfg
            (lift_Rel_cfg (state_invariant σ s2) ⩕
                          genNExpr_exp_correct σ s2 e ⩕
                          ext_local memH (memV,(l,g))
         ))
         (interp_helix (denoteNExpr σ nexp) memH)
         (interp_cfg (denote_code (convert_typ [] c)) g l memV).
Proof.
  intros.
  eapply eutt_mon; cycle -1.
  eapply genNExpr_correct_ind; eauto.
  intros [(? & ?) |] (? & ? & ? & []) INV; [destruct INV as (SI & EXP & ?) | inv INV].
  cbn in *.
  cbn in *.
  specialize (EXP l0).
  forward EXP; [reflexivity |].
  split; auto.
  split; auto.
Qed.

