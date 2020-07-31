Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Ltac rewrite_nth_error :=
  match goal with
  | h: nth_error _ _ ≡ _ |- _ => rewrite h
  end.

Ltac rewrite_memory_lookup :=
  match goal with
  | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
  end.

Ltac rewrite_mem_lookup :=
  match goal with
  | h: mem_lookup _ _ ≡ _ |- _ => rewrite h
  end.
 
Fixpoint build_vec {E} (n: nat) (body: nat -> mem_block -> itree E mem_block):
  mem_block -> itree E mem_block :=
  fun memy =>
    match n with
    | O => ret memy
    | S n => memy' <- body n memy;;
            build_vec n body memy'
    end.

Definition bodyIMap (f : AExpr) (σ : evalContext) (x: mem_block) (n: nat) (y: mem_block) : itree Event (mem_block) :=
        v <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" n x) ;;
        vn <- lift_Serr (MInt64asNT.from_nat n) ;;
        v' <- denoteIUnCType σ f vn v ;;
        ret (mem_add n v' y).

Definition  IMap_Rel σ Γ : Rel_cfg_T mem_block (block_id * block_id + uvalue) :=
  lift_Rel_cfg (state_invariant σ Γ).

Definition uvalue_of_nat k := UVALUE_I64 (Int64.repr (Z.of_nat k)).

Lemma bodyIMapCorrect : forall i o vx vy f loopvar loopcontblock s1 s2 bid_from bid_src bodyV
                          memx memy
                          (σ : evalContext) (memH : memoryH) (memV : memoryV) l g
                          (* nx memx mx ix ny my iy *)
                          nx ny szx szy 
                          mbkx mbky szx' szy'
  ,
    genIMapBody i o vx vy f loopvar loopcontblock s1 ≡ inr (s2, (bid_src,bodyV)) ->

    state_invariant σ s1 memH (memV,(l,g)) ->

    nth_error (Γ s1) nx ≡ Some (vx, TYPE_Pointer (TYPE_Array szx TYPE_Double)) ->
    nth_error (Γ s1) ny ≡ Some (vy, TYPE_Pointer (TYPE_Array szy TYPE_Double)) ->
    MInt64asNT.from_Z szx ≡ inr i ->
    MInt64asNT.from_Z szy ≡ inr o ->

    nth_error σ nx ≡ Some (DSHPtrVal mbkx szx') ->
    nth_error σ ny ≡ Some (DSHPtrVal mbky szy') ->

    (* Should rather be something like? *)
    (*
      I am handling the cell k
      l @ loopvar ≡ Some (uvalue_of_nat k) ->

      memory_lookup memH mbkx ≡ Some bk_helix ->
      mem_lookup i bk_helix ≡ Some val ->

    l @ idx ≡ Some (UVALUE_Addr ptr_x) ->
    get_array_cell memV (DVALUE_Addr ptr_x) k TYPE_Double ≡ inr (UVALUE_Double val) ->

What should be exactly the post?
     *)


    forall k,
      eutt (IMap_Rel σ s1)
           (with_err_RB (interp_Mem (bodyIMap f σ memx k memy) memH))
           (with_err_LB (interp_cfg (D.denote_bks (convert_typ [] bodyV) (bid_from, bid_src)) g l memV)).
Proof.
  intros * GEN PRE; intros.

  cbn* in *.
  simp; cbn* in *; simp.

     
      (* Require Import LibHyps.LibHyps. *)
      (* onAllHyps move_up_types. *)

      destruct vx; [admit |].
      destruct vy; [admit |].
      break_match_goal; [admit|].
      break_match_goal; [|admit].
      cbn.
      cbn*; norm_h.
      unfold denoteIUnCType.

      rewrite denote_bks_unfold_in.
      Opaque find_block.
      2: rewrite find_block_eq; reflexivity.
      cbn.
      norm_v.
      focus_single_step.
      (*
      rewrite denote_code_cons.
      simpl.
      unfold denote_op.
      simpl.
      repeat rewrite bind_bind.
      focus_single_step_v.
      cbn*.
      edestruct memory_invariant_LLU_Ptr as (bk_x & ptr_x & LUx & INLGx & VEC_LUx); [| exact H | exact H3 |]; eauto.
      norm_v.
      2:eassumption. 
      cbn; norm_v.
      unfold IntType; rewrite typ_to_dtyp_I.
      cbn; repeat (norm_v; []).
      cbn.
      subst; focus_single_step.
      assert (l @ loopvar ≡ Some (UVALUE_I64 (Int64.repr (Z.of_nat k)))) by admit.
      norm_v.
      2:eassumption.
      cbn; norm_v.
      simpl.
      unfold ITree.map.
      cbn; norm_v.
      rewrite exp_E_to_instr_E_Memory,subevent_subevent.
      cbn in *. 
       *)
Admitted.

(*       apply VEC_LUx in Heqo0. *)
(*       edestruct (@interp_cfg_to_L3_GEP_array defs t a  g l) as (add & ?EQ & READ); eauto. *)
(*       erewrite interp_cfg_to_L3_GEP_array. *)

(*         | DSHIMap n (PVar ix) (PVar iy) f => *)
          
(*           (* Helix *) *)
(*           nth_error σ ix = Some (DSHPtrVal vx sizex) *)
(*           nth_error σ iy = Some (DSHPtrVal vy sizey) *)
(*           memH[vx] = x *)
(*           memH[vy] = y *)
(*   LUn : nth_error (Γ s1) n0 ≡ Some (i0, TYPE_Pointer (TYPE_Array sz TYPE_Double)) *)
(*           (* Vellvm *) *)
          


(*           '(x,i) <- resolve_PVar x_p ;; *)
(*           '(y,o) <- resolve_PVar y_p ;; *)
(*           loopcontblock <- incBlockNamed "IMap_lcont" ;; *)
(*           loopvar <- incLocalNamed "IMap_i" ;; *)
(*           '(body_entry, body_blocks) <- genIMapBody i o x y f loopvar loopcontblock ;; *)
(*           add_comment *)
(*             (genWhileLoop "IMap" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock) *)

(*         | DSHIMap n x_p y_p f => *)
(*           '(x_i,x_size) <- denotePExpr σ x_p ;; *)
(*           '(y_i,y_sixe) <- denotePExpr σ y_p ;; *)
(*           x <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i) ;; *)
(*           y <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i) ;; *)
(*           y' <- denoteDSHIMap n f σ x y ;; *)
(*           trigger (MemSet y_i y') *)


(* Definition genIMapBody *)
(*            (i o: Int64.int) *)
(*            (x y: ident) *)
(*            (f: AExpr) *)
(*            (loopvar: raw_id) *)
(*            (nextblock: block_id) *)
(*   : cerr segment *)
(*   := *)
(*     pwblock <- incBlockNamed "IMapLoopBody" ;; *)
(*     pwret <- incVoid ;; *)
(*     storeid <- incVoid ;; *)
(*     px <- incLocal ;; *)
(*     py <- incLocal ;; *)
(*     v <- incLocal ;; *)
(*     let xtyp := getIRType (DSHPtr i) in *)
(*     let ytyp := getIRType (DSHPtr o) in *)
(*     let xptyp := TYPE_Pointer xtyp in *)
(*     let yptyp := TYPE_Pointer ytyp in *)
(*     let loopvarid := ID_Local loopvar in *)
(*     addVars [(ID_Local v, TYPE_Double); (loopvarid, IntType)] ;; *)
(*     '(fexpr, fexpcode) <- genAExpr f ;; *)
(*     dropVars 2 ;; *)
(*     ret (pwblock, *)
(*          [ *)
(*            {| *)
(*              blk_id    := pwblock ; *)
(*              blk_phis  := []; *)
(*              blk_code  := [ *)
(*                            (IId px,  INSTR_Op (OP_GetElementPtr *)
(*                                                  xtyp (xptyp, (EXP_Ident x)) *)
(*                                                  [(IntType, EXP_Integer 0%Z); *)
(*                                                     (IntType,(EXP_Ident loopvarid))] *)

(*                            )); *)

(*                              (IId v, INSTR_Load false TYPE_Double *)
(*                                                 (TYPE_Pointer TYPE_Double, *)
(*                                                  (EXP_Ident (ID_Local px))) *)
(*                                                 (ret 8%Z)) *)
(*                          ] *)

(*                             ++ fexpcode ++ *)

(*                             [ (IId py,  INSTR_Op (OP_GetElementPtr *)
(*                                                     ytyp (yptyp, (EXP_Ident y)) *)
(*                                                     [(IntType, EXP_Integer 0%Z); *)
(*                                                        (IntType,(EXP_Ident loopvarid))] *)

(*                               )); *)

(*                                 (IVoid storeid, INSTR_Store false *)
(*                                                             (TYPE_Double, fexpr) *)
(*                                                             (TYPE_Pointer TYPE_Double, *)
(*                                                              (EXP_Ident (ID_Local py))) *)
(*                                                             (ret 8%Z)) *)


(*                             ]; *)
(*              blk_term  := (IVoid pwret, TERM_Br_1 nextblock); *)
(*              blk_comments := None *)
(*            |} *)
(*         ]). *)


Section FSHAssign.
  (** ** Compilation of FSHAssign TODO
      Unclear how to state this at the moment
      What is on the Helix side? What do the arguments correspond to?
   *)
  Lemma genFSHAssign_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (σ: evalContext)
      (* Vellvm bits *)   (i o: Int64.int) (x y: ident) (src dst: NExpr) (nextblock bid: block_id) (bks : list (LLVMAst.block typ)),
      genFSHAssign i o x y src dst nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End FSHAssign.

Fixpoint build_vec' {E} (n: nat) (body: nat -> mem_block -> itree E mem_block):
  mem_block -> itree E mem_block :=
  fun memy =>
    match n with
    | O => ret memy
    | S n => memy' <- build_vec' n body memy;;
            body n memy'
    end.
 
(**
   General lemma for iteration over vectors.
 *)

(* Bodies invariant:
   * Helix: pure computation returning a mem_block having updated the cell k with some value
   * Vellvm: impure computation having _only_ updated the same cell with the same value.
             The local state may have been extended
 *)

Definition body_pre loopvar (k: nat) : Rel_cfg :=
  fun memH '(memV,(l,g)) => l @ loopvar ≡ Some (uvalue_of_nat k).

Definition body_post
           (a: addr) (bk_i: mem_block) (k : nat) (post: block_id)
           (memHi : memoryH) (memVi : memoryV) (li : local_env) (gi : global_env)
           (τ: dtyp) (* This type should be fixed ? *)
  : Rel_cfg_T mem_block (block_id * block_id + uvalue) :=
  fun '(memH,bk) '(memV,(l,(g,v))) =>
    (exists l, v ≡ inl (l, post)) /\
    memH ≡ memHi /\
    g ≡ gi /\
    li ⊑ l /\
    exists v,
      bk ≡ mem_add k v bk_i /\
      inr memV ≡ write_array_cell memVi a k τ (dvalue_of_bin v).

From Vellvm Require Import Traversal.

(* Definition loop_post *)
(*            (a: addr) (bk_i: mem_block) (k : nat) (post: block_id) *)
(*            (memHi : memoryH) (memVi : memoryV) (li : local_env) (gi : global_env) *)
(*            (τ: dtyp) (* This type should be fixed ? *) *)
(*   : Rel_cfg_T mem_block (block_id * block_id + uvalue) := *)
(*   fun '(memH,bk) '(memV,(l,(g,v))) => *)
(*     (exists l, v ≡ inl (l, post)) /\ *)
(*     memH ≡ memHi /\ *)
(*     g ≡ gi /\ *)
(*     li ⊑ l /\ *)
(*     exists v, *)
(*       bk ≡ mem_add k v bk_i /\ *)
(*       inr memV ≡ write_array_cell memVi a k τ (dvalue_of_bin v). *)


Lemma genWhileLoop_ind:
  forall (msg : string)
    (lvar : raw_id)            (* lvar storing the loop index *)
    (body_entry_id : block_id) (* entry point of the body *)
    (wrap_loop_id : block_id)  (* reentry point from the body back to the loop *)
    (bodyV : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (exit_id : block_id)       (* exit point of the overall loop *)
    (entry_id : block_id)      (* entry point of the overall loop *)
    (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ)) (* (llvm) code defining the whole loop *)
    (from_id: block_id)       (* point from which we enter the overall loop *)
    (n : nat)                    (* Number of iterations *)

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    (GEN: genWhileLoop msg (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       lvar wrap_loop_id body_entry_id bodyV [] exit_id s1
                       ≡ inr (s2,(entry_id,bks)))

    (* Computation on the Helix side performed at each cell of the vector,
       the counterpart to bodyV *)
    (bodyH: nat -> mem_block -> itree _ mem_block) 

    (* Main relation preserved by iteration *)
    (R : Rel_cfg),

    (* Inductive proof: Assuming R, reestablish R by going through both bodies *)
    (forall g l mV mH ymem,
        (* ((R ⩕ Invk n) (mH,ymem) (mV, (l, (g, (inl body))))) -> *)
        (R mH (mV,(l,g))) ->
        eutt
          (lift_Rel_cfg R)
          (* (R ⩕ Invk (n +1) /\ lvar = n /\ retlabel = post ) *)
          (with_err_RB (interp_Mem (bodyH n ymem) mH))
          (with_err_LB (interp_cfg
                          (denote_bks (convert_typ [] bodyV) (from_id,body_entry_id)) g l mV))
    ) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH ymem,
      R mH (mV,(l,g)) ->
      eutt (lift_Rel_cfg R)
           (with_err_RB (interp_Mem (build_vec n bodyH ymem) mH))
           (with_err_LB (interp_cfg (denote_bks (convert_typ [] bks) (from_id,entry_id)) g l mV)).
Proof.
  intros * GEN * IND * PRE.
  cbn* in GEN; simp.
Admitted.

Definition stable_exp_local (R: Rel_cfg) : Prop :=
    forall memH memV ρ1 ρ2 g,
      R memH (memV, (ρ1, g)) ->
      ρ1 ⊑ ρ2 ->
      R memH (memV, (ρ2, g)).

Definition imp_rel {A B : Type} (R S: A -> B -> Prop): Prop :=
  forall a b, R a b -> S a b.

Lemma genWhileLoop_correct:
  forall (msg : string)
    (lvar : raw_id)            (* lvar storing the loop index *)
    (body_entry_id : block_id) (* entry point of the body *)
    (wrap_loop_id : block_id)  (* reentry point from the body back to the loop *)
    (bodyV : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (exit_id : block_id)       (* exit point of the overall loop *)
    (entry_id : block_id)      (* entry point of the overall loop *)
    σ (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ)) (* (llvm) code defining the whole loop *)
    (from_id: block_id)        (* point from which we enter the overall loop *)
    (n : nat)                    (* Number of iterations *)

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    (GEN: genWhileLoop msg (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       lvar wrap_loop_id body_entry_id bodyV [] exit_id s1
                       ≡ inr (s2,(entry_id,bks)))

    (* Computation on the Helix side performed at each cell of the vector,
       the counterpart to bodyV *)
    (bodyH: nat -> mem_block -> itree _ mem_block) 

    (* Main relation preserved by iteration *)
    (R : Rel_cfg),

    (* Inductive proof: Assuming R, reestablish R by going through both bodies *)
    (forall g l mV mH ymem,
        (* ((R ⩕ Invk n) (mH,ymem) (mV, (l, (g, (inl body))))) -> *)
        (R mH (mV,(l,g))) ->
        eutt
          (lift_Rel_cfg R)
          (* (R ⩕ Invk (n +1) /\ lvar = n /\ retlabel = post ) *)
          (with_err_RB (interp_Mem (bodyH n ymem) mH))
          (with_err_LB (interp_cfg
                          (denote_bks (convert_typ [] bodyV) (from_id,body_entry_id)) g l mV))
    ) ->

    (* R must be stable by extension of the local env *)
    stable_exp_local R ->

    (* R must entail the state invariant *)
    imp_rel R (state_invariant σ s1) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH ymem,
      R mH (mV,(l,g)) ->
      eutt (lift_Rel_cfg R)
           (with_err_RB (interp_Mem (build_vec n bodyH ymem) mH))
           (with_err_LB (interp_cfg (denote_bks (convert_typ [] bks) (from_id,entry_id)) g l mV)).
Proof.
  intros * GEN * IND STABLE IMPSTATE * PRE.
  cbn* in GEN; simp. 
  destruct n as [|[|n]].
  - (* n = 0: we never enter the loop *)

    cbn.
    norm_h.

    jump_in.
       
    cbn.
    norm_v.
    cbn; norm_v.

    rewrite denote_code_singleton.
    rewrite denote_instr_op.
    2:{
      cbn.
      rewrite !bind_ret_l.
      cbn.
      rewrite translate_ret, interp_cfg_to_L3_ret.
      reflexivity.
    }

    norm_v.
    focus_single_step_v.
    rewrite denote_term_br_r.
    2:{
      cbn.
      rewrite translate_trigger, lookup_E_to_exp_E_Local, subevent_subevent.
      rewrite translate_trigger, exp_E_to_instr_E_Local, subevent_subevent.
      rewrite interp_cfg_to_L3_LR.
      2: unfold local_env; rewrite lookup_alist_add_eq; reflexivity.
      cbn.
      reflexivity.
    }

    norm_v.
    subst.

    rewrite denote_bks_unfold_not_in.
    2: admit.

    norm_v.
    apply eutt_Ret.

    cbn; eapply STABLE; eauto.
    eapply sub_alist_add.
    eapply concrete_fresh_fresh; eauto.
    eapply incLocal_is_fresh.
    eapply state_invariant_incBlockNamed; eauto.
    eapply state_invariant_incBlockNamed; eauto.

  - (* n > 0 *)
    cbn.
    eutt_hide_left.

    jump_in.

    cbn.
    norm_v.
    cbn; norm_v.

    focus_single_step_v.
    rewrite denote_code_singleton.
    rewrite denote_instr_op.
    2:{
      simpl.
      rewrite !bind_ret_l.
      cbn.
      rewrite translate_ret, interp_cfg_to_L3_ret.
      reflexivity.
    }

    norm_v.
    subst; cbn; norm_v; focus_single_step_v.
    rewrite denote_term_br_l.
    2:{
      cbn.
      rewrite translate_trigger, lookup_E_to_exp_E_Local, subevent_subevent.
      rewrite translate_trigger, exp_E_to_instr_E_Local, subevent_subevent.
      rewrite interp_cfg_to_L3_LR.
      2: unfold local_env; rewrite lookup_alist_add_eq; reflexivity.
      cbn.
      reflexivity.
    }

    norm_v.
    subst; cbn; norm_v.

    jump_in.
    2:admit.

    cbn.
    norm_v.

    find_phi.

    cbn; norm_v.
    focus_single_step_v.

    cbn.
    norm_v.
    subst; norm_v.
    rewrite interp_cfg_to_L3_LW.
    cbn; norm_v.
    rewrite denote_code_nil.
    cbn; norm_v.


Admitted.


Section IMapBody.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genIMapBody_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (f: AExpr)
      (* Vellvm bits *) (i o: Int64.int) (x y: ident) (loopvar: raw_id) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genIMapBody i o x y f loopvar nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End IMapBody.

Section BinOpBody.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genBinOpBody_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (f: AExpr)
      (* Vellvm bits *) (i o: Int64.int) (n: nat) (x y: ident) (loopvar: raw_id) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genBinOpBody i o n x y f loopvar nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End BinOpBody.

Section MemMap2Body.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genMemMap2Body_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (f: AExpr)
      (* Vellvm bits *) (i0 i1 o: Int64.int) (n: nat) (x x0 y: ident) (loopvar: raw_id) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genMemMap2Body i0 i1 o x x0 y f loopvar nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End MemMap2Body.

Section MemInit.
  (** ** Compilation of IMapBody TODO
      Hmm this one even refuses to get admitted!
   *)

(*
  Lemma genMemInit_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (initial: binary64)
      (* Vellvm bits *) (size: Int64.int) (y: ident) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genMemInit size y initial nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.
  *)

End MemInit.

Section Power.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genPower_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (src dst: NExpr) (n: NExpr) (f: AExpr)
      (* Vellvm bits *) (i o: Int64.int) (x y: ident) (initial: binary64) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genPower i o x y src dst n f initial nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
  (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
   *)
  Proof.
  Admitted.

End Power.

Section LLVMGen.
  (** YZ TODO
      This is initialized over the empty memory. That is incorrect. Run it over the initialze memory, and add the top level statement about compile
     global_extern == false?
   *)
  Lemma LLVMGen_correct: forall R,
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix bits *)    (i o: Int64.int) (globals: list (string*DSHType)) (globals_extern: bool) (fshcol: DSHOperator) (funname: string) (σ: evalContext)
      (* Vellvm bits *)   tle,
      LLVMGen i o fshcol funname s1 ≡ inr (s2, tle) ->
      eutt (* (bisim_final σ) *) R
           (with_err_RT (interp_Mem (denoteDSHOperator σ fshcol) memory_empty))
           (semantics_llvm tle).
  Proof.
    (* intros p data pll H. *)
    (*   unfold compile_w_main, compile in H. *)
    (*   destruct p as [i o name globals op]. *)
    (*   destruct (initIRGlobals data globals) as [? | [data' ginit]] eqn:EQGlob; [inv H |]. *)
    (*   simpl in H. *)
    (*   destruct (ErrorWithState.evalErrS (LLVMGen i o globals false op name) newState) eqn: EQEVALERR; [inv H | inv H]. *)
    (*   unfold semantics_llvm. *)
    (*   unfold semantics_llvm_mcfg. *)
    (*   unfold lift_sem_to_mcfg. *)
    (*   match goal with *)
    (*     |- context[match ?p with | _ => _ end] => destruct p eqn:EQ *)
    (*   end. { *)
    (*     unfold ErrorWithState.evalErrS in EQEVALERR. *)
    (*     destruct (LLVMGen i o globals false op name newState) eqn:EQGEN; inv EQEVALERR. *)
  Admitted.

End LLVMGen.

(**
   Initialization of the memory
 **)

Definition llvm_empty_memory_state_partial: config_cfg
  := (empty_memory_stack, ([], [])).

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

(* TODO: move to Util *)
Definition assoc_right_to_left {A B C:Type}: (A*(B*C)) -> ((A*B)*C)
  := fun x => let '(a,(b,c)):=x in ((a,b),c).

(* TODO: move to Util *)
Definition assoc_left_to_right {A B C:Type}: ((A*B)*C) -> (A*(B*C))
  := fun x => let '((a,b),c) := x in (a,(b,c)).

(** Empty memories and environments should satisfy [memory_invariant] *)
Lemma memory_invariant_empty: memory_invariant [] newState helix_empty_memory llvm_empty_memory_state_partial.
Proof.
  unfold memory_invariant.
  intros n v τ x Hcontra Hst.
  rewrite nth_error_nil in Hcontra.
  inversion Hcontra.
Qed.

Lemma WF_IRState_empty : WF_IRState [ ] newState.
Proof.
(*   cbn; apply Forall2_nil. *)
(* Qed. *)
Admitted.

Lemma inc_local_fresh_empty : concrete_fresh_inv newState llvm_empty_memory_state_partial.
Proof.
  intros ? ? ? LU; inv LU.
Qed.

Lemma state_invariant_empty: state_invariant [] newState helix_empty_memory llvm_empty_memory_state_partial.
Proof.
  split; auto using memory_invariant_empty, WF_IRState_empty, inc_local_fresh_empty.
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
