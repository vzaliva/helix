(* Some of this code may be useful. I store it in there for now *)


Lemma eval_denoteNexp :
  forall σ nexp val,
    evalNexp σ nexp ≡ inr val ->
    denoteNexp σ nexp ≅ Ret val.
Proof.
  intros σ nexp val H.
  unfold denoteNexp. rewrite H.
  reflexivity.
Qed.

  (* Relations for expressions *)
  (* top might be able to just be Some (DTYPE_I 64) *)
  (* NOTEYZ: I am completely confused by this definition. *)
  Definition nexp_relation
             (env : list (ident * typ))
             (e : exp typ)
             (n : Int64.int)
             (r : (memory * (local_env * (global_env * ())))): Prop :=
    let '(mem_llvm, (ρ, (g, _))) := r in
    eutt (fun n '(_, (_, (_, uv))) => int64_concrete_uvalue_rel n uv)
         (ret n)
         (interp_cfg_to_L3 helix_intrinsics (translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64)) (TransformTypes.fmap_exp _ _ (TypeUtil.normalize_type_dtyp env) e))) g ρ mem_llvm).

  (**
     Division case. Division by zero is ruled out by assuming that no failure can happen.
     TODOYZ: Do we:
      - rule out failure from the source program (usual assumption, sensible). If so, how to we express it?
      - prove preservation of failure. Unusual, stronger, require a change in our current non-interpretation of errors.
   *)
  (* TODO: Need something about denoteNexp not failing *)
  Lemma denote_nexp_div :
    forall (σ : evalContext) (nexp1 nexp2 : NExpr),
      eutt Logic.eq (denoteNexp σ (NDiv nexp1 nexp2))
           (ITree.bind (denoteNexp σ nexp1)
                       (fun (n1 : Int64.int) => ITree.bind (denoteNexp σ nexp2)
                                                        (fun (n2 : Int64.int) => denoteNexp σ (NDiv (NConst n1) (NConst n2))))).
  Proof.
  Admitted.





  

  Lemma denoteNexp_genNExpr :
    forall (* Helix bits  *) (nexp : NExpr) (σ : evalContext) (st st' : IRState) mem_helix
      (* Vellvm bits *) (nexp_r : exp typ) (nexp_code : code typ) (env : list (ident * typ))  g ρ mem_llvm,
      (* TODOCB: Do I need mem_helix?
         YZ: I suspect it depends on whether you run the interpreter [interp_Mem] or not here
       *)
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
      genNExpr nexp st  ≡ inr (st', (nexp_r, nexp_code)) ->
      eutt (nexp_relation env nexp_r)
           (translate inr_ (denoteNexp σ nexp))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics
                             (D.denote_code (map
                                               (λ '(id, i),
                                                (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i))
                                               nexp_code)) g ρ mem_llvm)).
  Proof.
    (*
    induction nexp; intros σ st st' mem_helix nexp_r nexp_code env g ρ mem_llvm Hmem H.
    - (* NVar *)
      cbn in H.
      repeat break_match_hyp; subst; inversion H; simpl.
      + cbn in Heqs.
        subst.
        rewrite interp_cfg_to_L3_ret.
        destruct (nth_error (vars st) v) eqn:Hnth; inversion Heqs; subst.
        unfold denoteNexp. cbn.
        unfold context_lookup.
        destruct (nth_error σ v) eqn:Hnthsigma.
        cbn. destruct d.
        cbn.
        do 2 rewrite translate_ret.
        apply eqit_Ret.
        cbn.
        * destruct i0; cbn.
          rewrite bind_trigger.
          repeat rewrite translate_vis.
          cbn.

          unfold interp_cfg_to_L3.
          unfold INT.interp_intrinsics.
          rewrite interp_vis.
          cbn.
          rewrite interp_global_bind.
          unfold INT.F_trigger.
          unfold interp_global at 2.
          setoid_rewrite interp_state_trigger.
          rewrite bind_bind.
          cbn.
          break_match.
          2: admit. (* exception *)
          rewrite bind_ret_l.
          rewrite bind_tau.
          rewrite tau_eutt.
          rewrite bind_ret_l.
          rewrite tau_eutt.
          rewrite interp_translate.
          cbn.
          rewrite translate_ret.
          rewrite interp_ret.
          rewrite interp_global_ret.
          rewrite interp_local_ret.
          rewrite M.interp_memory_ret.

          apply eqit_Ret.

          unfold int64_concrete_uvalue_rel.
          rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
          unfold int64_dvalue_rel.
          inversion Hmem.
          apply ListUtil.length_0 in H0; subst.
          rewrite ListNth.nth_error_nil in Hnthsigma. inversion Hnthsigma.
          destruct H0.
          pose proof (H0 v (DSHnatVal n) Hnthsigma).
          cbn in H1.
          destruct H1 as (? & ? & ? & ? & ? & ? & ?).
          subst.
          destruct H1. admit.
          cbn.

          admit.
          admit.
        * admit.
        * admit.
        * admit.
      +
      (* exception *) admit.

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
      pose proof (DynamicValues.Int64.intrange t).
      unfold DynamicValues.Int64.max_unsigned.
      omega.
    - cbn in H.
      repeat break_match_hyp; inversion H.

      repeat rewrite map_app.
      repeat setoid_rewrite denote_code_app.

      rewrite denote_nexp_div.
      pose proof IHnexp1 σ _ _ mem_helix _ _ env g ρ mem_llvm Hmem Heqs.
      rewrite interp_cfg_to_L3_bind.
      repeat setoid_rewrite translate_bind.
      eapply eutt_clo_bind; eauto.

      intros u1 u2 H4.
      repeat break_match.
      rewrite interp_cfg_to_L3_bind; rewrite translate_bind.
      eapply eutt_clo_bind; eauto.
      (* eapply H0. *)

      (* intros u0 u3 H5. *)
      (* repeat break_match. *)

      (* (* We executed code that generated the values for the *)
      (* expressions for the binary operations... Now we need to denote *)
      (* the expressions themselves. *) *)
      (* (* simplify left side to ret *) *)
      (* cbn. *)

      (* repeat rewrite translate_bind.       *)
      (* repeat rewrite interp_cfg_to_L3_bind. *)
      (* repeat rewrite bind_bind. *)

      (* genNExpr nexp1 st ≡ inr (i, (e, c)) *)
      (* I need something relating `denote_exp e` and `denoteNexp nexp1`... *)
     *)
  Admitted.

  Lemma denote_exp_nexp:
    forall nexp st i e c mem_llvm σ g ρ env,
      genNExpr nexp st ≡ inr (i, (e, c)) ->
      (* TODO: factor out this relation *)
      eutt (fun n '(m, (l, (g, uv))) => int64_concrete_uvalue_rel n uv)
           (translate inr_ (denoteNexp σ nexp))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics (translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64)) (TransformTypes.fmap_exp _ _ (TypeUtil.normalize_type_dtyp env) e))) g ρ mem_llvm)).
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
                                                                (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i))
                                                               nexp_code)) g ρ mem_llvm)).
  Proof.
  Admitted.

  Lemma interp_cfg_to_L3_denote_exp :
    forall nexp s s' ll_exp ll_code n m l g env σ,
      genNExpr nexp s ≡ inr (s', (ll_exp, ll_code)) ->
      denoteNexp σ nexp ≈ Ret n ->
      (interp_cfg_to_L3 helix_intrinsics
                        (translate exp_E_to_instr_E
                                   (D.denote_exp (Some (DTYPE_I 64))
                                                 (TransformTypes.fmap_exp typ dtyp (TypeUtil.normalize_type_dtyp env) ll_exp))) g l m) ≈ Ret (m, (l, (g, UVALUE_I64 n))).
  Proof.
    induction nexp;
      intros s s' ll_exp ll_code n m l g env σ H H0;
      cbn in H; inversion H.
    - (* NVar *)
      admit.
    (* Exceptions due to lookup and type mismatches! *)
    - (* NConst *)
      cbn. rewrite repr_intval.
      rewrite translate_ret, interp_cfg_to_L3_ret.
      apply eqit_inv_ret in H0; subst; auto.
      reflexivity.
    - (* NDiv *)
      rewrite denote_nexp_div in H0.
      cbn in *.
  Admitted.

  (* Unprovable, this should come from some well typedness assumption *)
  Lemma nvar_is_i64 :
    forall {v s s' s'' ll_exp ll_code str i t},
      genNExpr (NVar v) s ≡ inr (s', (ll_exp, ll_code)) ->
      getStateVar str v s ≡ inr (s'', (i, t)) ->
      t ≡ TYPE_I 64%Z.
  Proof.
  Admitted.

  (* TODO: This is WRONG

      Each instruction evaluated in the code that nexp produces can
      add a local variable.
   *)
  Lemma denote_code_of_nexp :
    forall nexp s s' ll_exp ll_code env mem_llvm g ρ,
      genNExpr nexp s ≡ inr (s', (ll_exp, ll_code)) ->
      exists ρ',
        interp_cfg_to_L3 helix_intrinsics
                         (D.denote_code
                            (map (λ '(id, i), (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i))
                                 ll_code)) g ρ mem_llvm ≈ Ret (mem_llvm, (ρ', (g, ()))).
  Proof.
    induction nexp;
      intros s s' ll_exp ll_code env mem_llvm g ρ H;
      remember H as Hgen eqn:Heqgen; clear Heqgen;
        inversion H; subst; cbn.
    -  cbn in H.
       break_match_hyp; inversion H1.
       destruct p, p.
       pose proof (nvar_is_i64 Hgen Heqs0); subst.
       break_match_hyp; try contradiction.
       exists ρ.
       inversion H1; subst.
       cbn.
       rewrite interp_cfg_to_L3_ret.
       reflexivity.
    - exists ρ. rewrite interp_cfg_to_L3_ret.
      reflexivity.
    - exists ρ. (* TODO: This will need to change *)

        break_match_hyp.
        inversion H1.
        repeat break_match_hyp.
        inversion H1.
        inversion H1.
        cbn in *.
        do 2 rewrite map_app.
        do 2 setoid_rewrite denote_code_app.
        setoid_rewrite bind_bind.

        rewrite interp_cfg_to_L3_bind.
        pose proof IHnexp1 s i e c env mem_llvm g ρ Heqs0 as [ρ' Hnexp1].
        rewrite Hnexp1.
        rewrite bind_ret_l.

        rewrite interp_cfg_to_L3_bind.
        pose proof IHnexp2 i i0 e0 c0 env mem_llvm g ρ' Heqs1 as [ρ'' Hnexp2].
        rewrite Hnexp2.
        rewrite bind_ret_l.

        cbn.
        repeat setoid_rewrite translate_bind.
        rewrite bind_bind.

        rewrite interp_cfg_to_L3_bind.

  Admitted.

  (* TODO: I think I might want to know that ρ comes from denoting ll_code, actually *)
  Lemma denote_exp_of_nexp :
    forall nexp ll_exp ll_code s s' env g ρ mem_llvm mem_helix σ i,
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
      genNExpr nexp s ≡ inr (s', (ll_exp, ll_code)) ->
      evalNexp σ nexp ≡ inr i ->
      (interp_cfg_to_L3 helix_intrinsics
                        (translate exp_E_to_instr_E
                                   (D.denote_exp (Some (TypeUtil.normalize_type_dtyp env Utils.IntType))
                                                 (TransformTypes.fmap_exp typ dtyp (TypeUtil.normalize_type_dtyp env) ll_exp))) g ρ mem_llvm) ≈ Ret (mem_llvm, (ρ, (g, UVALUE_I64 i))).
  Proof.
    setoid_rewrite normalize_IntType.
    induction nexp;
      intros ll_exp ll_code s s' env g ρ mem_llvm mem_helix σ i Hmem H H0;
      inversion H; inversion H0; subst; cbn.
    - repeat break_match_hyp; inversion H3; inversion H2;
        cbn.
      destruct i1; cbn.
      rewrite bind_trigger.
      repeat setoid_rewrite translate_vis.
      repeat setoid_rewrite translate_ret.


      unfold interp_cfg_to_L3.
      {
        Set Nested Proofs Allowed.

        
      setoid_rewrite interp_intrinsics_vis; cbn.
      unfold INT.F_trigger.
      rewrite bind_trigger.
      setoid_rewrite interp_global_vis; cbn.

      unfold memory_invariant in Hmem.
      unfold context_lookup in Heqs0. destruct (nth_error σ v) eqn:Hlookup; inversion Heqs0.
      destruct Hmem as [Hmem | Hmem].
      { (* Case where sigma is nil *)
        assert (σ ≡ []) by (apply ListUtil.length_0; auto).
        subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
        inversion Hlookup.
      }

      destruct Hmem as [iota Hmem].
      (* TODO: need to be able to relate

            alist_find AstLib.eq_dec_raw_id id g

            and ι somehow.
       *)

            Lemma gen_var_irstate_rel :
              forall v s s' ll_exp ll_code mem_helix σ mem_llvm ρ g i id sz,
                genNExpr (NVar v) s ≡ inr (s', (ll_exp, ll_code)) ->
                memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
                evalNexp σ (NVar v) ≡ inr i ->
                getStateVar "NVar out of range" v s ≡ inr (s', (ID_Global id, TYPE_I sz)) ->
                alist_find AstLib.eq_dec_raw_id id g ≡ Some (DVALUE_I64 i).
            Proof.
              intros v s s' ll_exp ll_code mem_helix σ mem_llvm ρ g i id sz H H0 H1 H2.
              cbn in H1. break_match_hyp; inversion H1.
              break_match_hyp; inversion H1; subst.
              unfold context_lookup in *.
              destruct (nth_error σ v) eqn:Hlookup.
              2: { inversion Heqs0. }
              cbn in H2.
              destruct (nth_error (vars s) v) eqn:Hlookupst.
              2: { inversion H2. }
              cbn in H2.
              inversion H2. subst.
              inversion Heqs0.
              subst.
              unfold memory_invariant in H0.
              rename H0 into Hmem.
              destruct Hmem as [Hmem | Hmem].
              { (* Case where sigma is nil *)
                assert (σ ≡ []) by (apply ListUtil.length_0; auto).
                subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
                inversion Hlookup.
              }

              destruct Hmem as (Hinj & ?).
              specialize (H0 _ _ Hlookup).

              destruct H0 as [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.

              admit. (* locals *)

              cbn.

              cbn in *; subst.

            Qed.



            (** Those are remnants from the compile_FSHCOL_correct first sketch **)

      destruct (nth_error (vars s1) v) eqn:?; try inv_sum.
       destruct p,t; try inv_sum.
       destruct t; try inv_sum.
       destruct t; try inv_sum.
       cbn* GEN.

       destruct (ErrorWithState.err2errS (MInt64asNT.from_Z sz) s1); try inv_sum.
       destruct p,p0.
       destruct (nth_error (vars i0) v0) eqn:?; try inv_sum.
       destruct p,t; try inv_sum.
       destruct t0; try inv_sum.
       destruct t0; try inv_sum.
       destruct t0; try inv_sum.
       (* YZ TODO: simp_comp should break matches from the inside first *)
       destuct p.

      repeat hide_strings GEN.


      apply DSHAssign_singleton in HCompile.
      destruct HCompile as (b & HCompile & Hterm & Hbid & Hbksbk).
      subst.

    (* Start by working on the left hand side *)



    unfold normalize_types_blocks.
    eutt_hide_left.
    unfold fmap; simpl Fmap_list'.
    (* Rewrite denote_bks to denote_block *)
    rewrite denote_bks_singleton; eauto using normalize_types_block_term.

    (* Work with denote_block *)
    (* I need to know something about b... *)
    pose proof genIR_DSHAssign_to_genFSHAssign src dst nextblock st HCompile as H1.
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

    destruct psrc as [src_v] eqn:Hpsrc, pdst as [dst_v] eqn:Hpdst.

    destruct (nth_error σ dst_v) as [d|] eqn:Hdst_v. 2: admit. (* Exception *)
    destruct d as [n_dst | v_dst | a_dst size_dst]. admit. admit. (* should only be able to be pointer *)

    destruct (nth_error σ src_v) as [d|] eqn:Hsrc_v. 2: admit. (* Exception *)
    destruct d as [n_src | v_src | a_src size_src]. admit. admit. (* should only be able to be pointer *)

    setoid_rewrite denotePexp_eutt_ret; eauto.

    repeat rewrite bind_ret_l.
    repeat setoid_rewrite bind_trigger.

    (* Should be able to handle MemLU's in a lemma as well *)
    destruct (memory_lookup_err "Error looking up 'x' in DSHAssign" mem a_src) eqn:Hmem_src.
    admit. (* Exception *)

    destruct (memory_lookup_err "Error looking up 'y' in DSHAssign" mem a_dst) eqn:Hmem_dst.
    admit. (* Exception *)
    cbn.

    repeat (rewrite interp_Mem_MemLU; eauto).

    destruct (evalNexp σ nsrc) as [|eval_src] eqn:Heval_src.
    admit. (* Exception *)

    destruct (evalNexp σ ndst) as [|eval_dst] eqn:Heval_dst.
    admit. (* Exception *)

    setoid_rewrite eval_denoteNexp; eauto.
    repeat setoid_rewrite bind_ret_l.
    cbn.

    destruct (mem_lookup_err "Error looking up 'v' in DSHAssign" (MInt64asNT.to_nat eval_src) m) eqn:Hmemlookup.
    admit. (* Exception *)
    cbn.
    rewrite bind_ret_l.

    rewrite interp_Mem_MemSet.

    (* Work on the right hand side again *)
    (* Unfold denote_code and break it apart. *)
    do 2 rewrite map_app.
    do 2 setoid_rewrite denote_code_app.
    do 2 setoid_rewrite bind_bind.

    repeat setoid_rewrite interp_cfg_to_L3_bind.
    repeat setoid_rewrite translate_bind.

    (* Need to relate denoteNexp and denote_code of genNexpr *)
    match goal with
    | |- context[ ITree.bind ?x ?y ] => remember y as BLAH
    end.

     *)

  Lemma irstate_rel (op: DSHOperator) :
    forall (nextblock bid_in : block_id) (st st' : IRState) (bks : list (LLVMAst.block typ)) (σ : evalContext) (env : list (ident * typ)) (mem : MDSHCOLOnFloat64.memory) (g : global_env) (ρ : local_env) (mem_llvm : memory),
      nextblock ≢ bid_in -> (* Do I need this? *)
      bisim_partial σ (mem,tt) (mem_llvm, (ρ, (g, (inl bid_in)))) ->
      genIR op nextblock st ≡ inr (st',(bid_in,bks)) ->


      Lemma lookup_global:
        forall σ mem_helix mem_llvm ρ g v i id s s' sz,
          memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
          getStateVar "NVar out of range" v s ≡ inr (s', (ID_Global id, TYPE_I sz)) ->
          evalNexp σ (NVar v) ≡ inr i ->
          exists a, alist_find AstLib.eq_dec_raw_id id g ≡ Some (DVALUE_Addr a).
  Proof.
    intros σ mem_helix mem_llvm ρ g v i id s s' sz Hmem Hst Heval.
    cbn in Heval.
    unfold context_lookup in *.
    destruct (nth_error σ v) eqn:Hlookup; cbn in Heval; try solve [inversion Heval].
    unfold memory_invariant in Hmem.
    destruct Hmem as [Hmem | Hmem].
    { (* Case where sigma is nil *)
      assert (σ ≡ []) by (apply ListUtil.length_0; auto).
      subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
      inversion Hlookup.
    }

    destruct Hmem as (Hinj & ?).
    specialize (H _ _ Hlookup).

    (* Determine that d = DSHnatVal i *)
    destruct d eqn:Hd; cbn in Heval; inversion Heval as [Hni]; rewrite Hni in *.

    destruct H as [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                               [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.

              (* Variable is in the local environment *)
              admit.

              (* Variable is in the global environment *)
              exists ptr_llvm. unfold inj_f in Hglobal.
              destruct Hinj.
              cbn in Hglobal.

              (* Need something relating id and v *)
              destruct (inj_f0 v).

              - (* d = DSHnatVal i *)
                destruct H as
                    [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.
                admit.

                exists ptr_llvm.
                unfold inj_f in Hglobal.
                destruct Hinj.
                destruct inj_f0.


                unfold Hinj in

                 destruct Hsearch.

            Qed.
            .
              inversio


            destruct (alist_find AstLib.eq_dec_raw_id id g) eqn:Hg.
            Focus 2. admit. (* Exception *)

            rewrite bind_ret_l.
            repeat rewrite tau_eutt.
            cbn.
            rewrite interp_ret.
            rewrite interp_global_ret.
            cbn.

            setoid_rewrite interp_local_ret.
            unfold M.interp_memory.
            rewrite interp_state_ret.

            (* Need something relating g... memory_invariant ? *)

            setoid_rewrite interp_memory_ret.
            rewrite
            inversion Heqs1; subst.
            rewrite interp_cfg_to_L3_vis.
            setoid_rewrite tau_eutt.
            cbn.
            setoid_rewrite translate_vis.
            repeat rewrite translate_vis.
            do 2 setoid_rewrite interp_cfg_to_L3_vis; cbn.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            repeat setoid_rewrite translate_ret.
            setoid_rewrite interp_intrinsics_vis.
            cbn;
            rewrite interp_cfg_to_L3_vis.
          - rewrite translate_ret, interp_cfg_to_L3_ret, repr_intval.
            reflexivity.
          -
        Qed.

        cbn.
        subst.
        rewrite IHnexp1.

        destruct (genNExpr nexp1 s) eqn:Hnexp1.
        inversion H1.
        destruct p, p.

        destruct (genNExpr nexp1 s) eqn:Hnexp1.
    Qed.


  Lemma DSHAssign_singleton :
    forall (nextblock : block_id) (src dst : MemVarRef) (st st' : IRState) (bid_in : block_id)
      (bks : list (LLVMAst.block typ)),
      genIR (DSHAssign src dst) nextblock st ≡ inr (st', (bid_in, bks)) ->
      exists b,
        genIR (DSHAssign src dst) nextblock st ≡ inr (st', (bid_in, [b]))
        /\ snd (blk_term b) ≡ TERM_Br_1 nextblock
        /\ blk_id b ≡ bid_in /\ bks ≡ [b].
  Proof.
    intros nextblock src dst st st' bid_in bks HCompile.
    simpl in HCompile. destruct src, dst.
    simpl in HCompile.
    repeat break_match_hyp; try inl_inr.
    inv Heqs; inv HCompile.
    unfold genFSHAssign in Heqs2.
    cbn in Heqs2.
  Admitted.

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

    Lemma denotePexp_eutt_ret :
    forall (σ : evalContext) (v : var_id) a size,
      nth_error σ v ≡ Some (DSHPtrVal a size) ->
      denotePexp σ (PVar v) ≈ Ret a.
  Proof.
    intros σ v a size H.
    unfold denotePexp; cbn.
    rewrite H.
    reflexivity.
  Qed.

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

    (* Start by working on the left hand side *)



    unfold normalize_types_blocks.
    eutt_hide_left.
    unfold fmap; simpl Fmap_list'.
    (* Rewrite denote_bks to denote_block *)
    rewrite denote_bks_singleton; eauto using normalize_types_block_term.

    (* Work with denote_block *)
    (* I need to know something about b... *)
    pose proof genIR_DSHAssign_to_genFSHAssign src dst nextblock st HCompile as H1.
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

    destruct psrc as [src_v] eqn:Hpsrc, pdst as [dst_v] eqn:Hpdst.

    destruct (nth_error σ dst_v) as [d|] eqn:Hdst_v. 2: admit. (* Exception *)
    destruct d as [n_dst | v_dst | a_dst size_dst]. admit. admit. (* should only be able to be pointer *)

    destruct (nth_error σ src_v) as [d|] eqn:Hsrc_v. 2: admit. (* Exception *)
    destruct d as [n_src | v_src | a_src size_src]. admit. admit. (* should only be able to be pointer *)

    setoid_rewrite denotePexp_eutt_ret; eauto.

    repeat rewrite bind_ret_l.
    repeat setoid_rewrite bind_trigger.

    (* Should be able to handle MemLU's in a lemma as well *)
    destruct (memory_lookup_err "Error looking up 'x' in DSHAssign" mem a_src) eqn:Hmem_src.
    admit. (* Exception *)

    destruct (memory_lookup_err "Error looking up 'y' in DSHAssign" mem a_dst) eqn:Hmem_dst.
    admit. (* Exception *)
    cbn.

    repeat (rewrite interp_Mem_MemLU; eauto).

    destruct (evalNexp σ nsrc) as [|eval_src] eqn:Heval_src.
    admit. (* Exception *)

    destruct (evalNexp σ ndst) as [|eval_dst] eqn:Heval_dst.
    admit. (* Exception *)

    setoid_rewrite eval_denoteNexp; eauto.
    repeat setoid_rewrite bind_ret_l.
    cbn.

    destruct (mem_lookup_err "Error looking up 'v' in DSHAssign" (MInt64asNT.to_nat eval_src) m) eqn:Hmemlookup.
    admit. (* Exception *)
    cbn.
    rewrite bind_ret_l.

    rewrite interp_Mem_MemSet.

    (* Work on the right hand side again *)
    (* Unfold denote_code and break it apart. *)
    do 2 rewrite map_app.
    do 2 setoid_rewrite denote_code_app.
    do 2 setoid_rewrite bind_bind.

    repeat setoid_rewrite interp_cfg_to_L3_bind.
    repeat setoid_rewrite translate_bind.

    (* Need to relate denoteNexp and denote_code of genNexpr *)
    match goal with
    | |- context[ ITree.bind ?x ?y ] => remember y as BLAH
    end.

    Set Nested Proofs Allowed.

            Lemma irstate_rel (op: DSHOperator) :
              forall (nextblock bid_in : block_id) (st st' : IRState) (bks : list (LLVMAst.block typ)) (σ : evalContext) (env : list (ident * typ)) (mem : MDSHCOLOnFloat64.memory) (g : global_env) (ρ : local_env) (mem_llvm : memory),
                nextblock ≢ bid_in -> (* Do I need this? *)
                bisim_partial σ (mem,tt) (mem_llvm, (ρ, (g, (inl bid_in)))) ->
                genIR op nextblock st ≡ inr (st',(bid_in,bks)) ->


            Lemma lookup_global:
              forall σ mem_helix mem_llvm ρ g v i id s s' sz,
                memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
                getStateVar "NVar out of range" v s ≡ inr (s', (ID_Global id, TYPE_I sz)) ->
                evalNexp σ (NVar v) ≡ inr i ->
                exists a, alist_find AstLib.eq_dec_raw_id id g ≡ Some (DVALUE_Addr a).
            Proof.
              intros σ mem_helix mem_llvm ρ g v i id s s' sz Hmem Hst Heval.
              cbn in Heval.
              unfold context_lookup in *.
              destruct (nth_error σ v) eqn:Hlookup; cbn in Heval; try solve [inversion Heval].
              unfold memory_invariant in Hmem.
              destruct Hmem as [Hmem | Hmem].
              { (* Case where sigma is nil *)
                assert (σ ≡ []) by (apply ListUtil.length_0; auto).
                subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
                inversion Hlookup.
              }

              destruct Hmem as (Hinj & ?).
              specialize (H _ _ Hlookup).

              (* Determine that d = DSHnatVal i *)
              destruct d eqn:Hd; cbn in Heval; inversion Heval as [Hni]; rewrite Hni in *.

              destruct H as [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.

              (* Variable is in the local environment *)
              admit.

              (* Variable is in the global environment *)
              exists ptr_llvm. unfold inj_f in Hglobal.
              destruct Hinj.
              cbn in Hglobal.

              (* Need something relating id and v *)
              destruct (inj_f0 v).

              - (* d = DSHnatVal i *)
                destruct H as
                    [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.
                admit.

                exists ptr_llvm.
                unfold inj_f in Hglobal.
                destruct Hinj.
                destruct inj_f0.


                unfold Hinj in

                 destruct Hsearch.

            Qed.
            .
              inversio


            destruct (alist_find AstLib.eq_dec_raw_id id g) eqn:Hg.
            Focus 2. admit. (* Exception *)

            rewrite bind_ret_l.
            repeat rewrite tau_eutt.
            cbn.
            rewrite interp_ret.
            rewrite interp_global_ret.
            cbn.

            setoid_rewrite interp_local_ret.
            unfold M.interp_memory.
            rewrite interp_state_ret.

            (* Need something relating g... memory_invariant ? *)

            setoid_rewrite interp_memory_ret.
            rewrite
            inversion Heqs1; subst.
            rewrite interp_cfg_to_L3_vis.
            setoid_rewrite tau_eutt.
            cbn.
            setoid_rewrite translate_vis.
            repeat rewrite translate_vis.
            do 2 setoid_rewrite interp_cfg_to_L3_vis; cbn.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            repeat setoid_rewrite translate_ret.
            setoid_rewrite interp_intrinsics_vis.
            cbn;
            rewrite interp_cfg_to_L3_vis.
          - rewrite translate_ret, interp_cfg_to_L3_ret, repr_intval.
            reflexivity.
          -
        Qed.

        cbn.
        subst.
        rewrite IHnexp1.

        destruct (genNExpr nexp1 s) eqn:Hnexp1.
        inversion H1.
        destruct p, p.

        destruct (genNExpr nexp1 s) eqn:Hnexp1.
    Qed.



      memory * (local_env * (global_env * ()))memory * (local_env * (global_env * ()))
    Lemma interp_nex
    subst assigncode.
              cbn.

              repeat setoid_rewrite translate_bind.
              repeat setoid_rewrite interp_cfg_to_L3_bind.
              repeat setoid_rewrite bind_bind.

              destruct i0 eqn:Hi0.
              ** (* Global id *)
                repeat setoid_rewrite translate_bind.
                rewrite interp_cfg_to_L3_bind.
                repeat setoid_rewrite translate_vis.
                repeat setoid_rewrite bind_bind.
                repeat setoid_rewrite translate_ret.

                destruct (alist_find AstLib.eq_dec_raw_id id g1) eqn:Hlookup.
                Focus 2. admit. (* Exception *)

                cbn.

                match goal with
                | |- context [ ITree.bind ?x ?y ] => remember y
                end.

                setoid_rewrite interp_cfg_to_L3_globalread; eauto.

                rewrite translate_bind.
                rewrite bind_bind.
                repeat rewrite translate_ret.
                rewrite bind_ret_l.
                repeat rewrite translate_ret.
                rewrite interp_cfg_to_L3_ret.
                rewrite translate_ret.
                rewrite bind_ret_l.

                subst i3; cbn.

                match goal with
                | |- context [ ITree.bind ?x ?y ] => remember y
                end.

                repeat setoid_rewrite bind_bind.
                setoid_rewrite translate_ret.
                setoid_rewrite bind_ret_l.

                rewrite interp_cfg_to_L3_bind.
                rewrite translate_bind.
                rewrite bind_bind.

                rewrite normalize_IntType.
                progress cbn.
                rewrite translate_ret.
                rewrite interp_cfg_to_L3_ret.
                rewrite translate_ret, bind_ret_l.
                cbn.

                rewrite interp_cfg_to_L3_bind.
                rewrite interp_cfg_to_L3_denote_exp; eauto.

                (* This feels very stupid, surely this should all just evaluate? *)
                rewrite translate_bind.
                rewrite translate_ret.
                rewrite bind_ret_l.
                rewrite interp_cfg_to_L3_bind.
                rewrite translate_bind.
                rewrite interp_cfg_to_L3_ret.
                rewrite translate_ret, bind_ret_l.
                repeat rewrite interp_cfg_to_L3_bind.
                rewrite interp_cfg_to_L3_ret.
                rewrite bind_ret_l.
                cbn.

                rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
                unfold ITree.map.
                rewrite bind_trigger.
                rewrite translate_vis.
                cbn.
                setoid_rewrite translate_ret.

                subst i3.
                cbn.

                all: eauto.
                Focus 2. apply Hnexp_src.
                reflexivity.

                setoid_rewrite bind_ret_l.
                setoid_rewrite <- denote_exp_nexp.
                apply eutt_clo_bind.

                rewrite interp
                rewrite bind_trigger.
                rewrite translate_vis.
                rewrite translate_vis.
                setoid_rewrite translate_ret.
                setoid_rewrite translate_ret.
                cbn.
                repeat setoid_rewrite translate_bind.
                rewrite interp_cfg_to_L3_bind.
                repeat setoid_rewrite translate_vis.
                repeat setoid_rewrite bind_bind.
                repeat setoid_rewrite translate_ret.

                rewrite interp_cfg_to_L3_vis; cbn.
                repeat setoid_rewrite bind_bind.
                cbn.
                rewrite translate_bind.
                rewrite bind_bind.
                cbn.

                match goal with
                | |- context[ITree.bind ?ma ?b] => remember b as blah
                end.

                unfold interp_cfg_to_L3; cbn.
                unfold trigger.
                rewrite interp_intrinsics_vis.
                cbn.
                setoid_rewrite tau_eutt.
                setoid_rewrite interp_ret.
                setoid_rewrite bind_ret_r.
                unfold interp_global.
                cbn.
                unfold M.interp_memory.
                unfold interp_local.
                cbn.

                unfold INT.F_trigger.
                setoid_rewrite interp_state_trigger.
                cbn.
                destruct (alist_find AstLib.eq_dec_raw_id id g1) eqn:Hg1.
                Focus 2.
                (* exception *) admit.
                rewrite bind_ret_l.
                repeat rewrite interp_state_tau.
                rewrite tau_eutt.
                repeat rewrite interp_state_ret.
                rewrite translate_ret.
                rewrite bind_ret_l.

                subst blah.
                match goal with
                | |- context[ITree.bind ?ma ?b] => remember b as blah
                end.

                rewrite interp_cfg_to_L3_ret.
                rewrite tau_eutt.
                rewrite bind_ret_l, translate_ret.
                repeat rewrite translate_ret, interp_cfg_to_L3_ret.
                rewrite translate_ret, bind_ret_l.

                subst blah.
                match goal with
                | |- context[ITree.bind ?ma ?b] => remember b as blah
                end.

                repeat rewrite interp_cfg_to_L3_bind.
                setoid_rewrite translate_ret.
                rewrite interp_cfg_to_L3_ret.
                rewrite bind_ret_l.
                repeat rewrite interp_cfg_to_L3_bind.
                repeat rewrite bind_bind.
                rewrite translate_bind.
                rewrite bind_bind.

                epose proof (@denote_exp_nexp _ _ _ _ _ _ _ _ _ _ Hnexp_src).
                Check eutt_clo_bind.
                eapply eutt_clo_bind.

                rewrite interp_intrinsics_vis.

                destruct id eqn:Hid.
                --- (* Name *)


                  setoid_rewrite interp_interp.

                --- (* Local id *)
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
    (* unfold denotePexp, evalPexp, lift_Serr. *)
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
    (* (* unfold denotePexp, evalPexp. *) *)
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
