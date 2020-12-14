Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.


(* The result is a branch *)
Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
  match c with
  | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
  end.

Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
  : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
  lift_Rel_cfg (state_invariant σ s2) ⩕
               branches to ⩕
               (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

(* ** DSHAssign (x_p, src_e) (y_p, dst_e):
         Helix side:
         1. x_i <- evalPExpr σ x_p ;;
         2. y_i <- evalPExpr σ y_p ;;
         3. x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
         4. y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
         5. src <- evalNExpr σ src_e ;;
         6. dst <- evalNExpr σ dst_e ;;
         7. v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
         8. ret (memory_set mem y_i (mem_add (to_nat dst) v y))

         Vellm side:
         src_nexpcode ++
         dst_nexpcode ++
         px <- gep "src_p"[src_nexpr] ;;
         v  <- load px ;;
         py <- gep "dst_p"[dst_nexpr] ;;
         store v py
       *)

Lemma DSHAssign_correct :
  forall (** Compiler bits *) (s1 s2: IRState)
    (** Helix bits    *) src dst (σ : evalContext) (memH : memoryH)
    (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : ocfg typ)
    (g : global_env) (ρ : local_env) (memV : memoryV),
    genIR (DSHAssign src dst) nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
    bid_bound s1 nextblock ->
    state_invariant σ s1 memH (memV, (ρ, g)) ->
    Gamma_safe σ s1 s2 ->
    no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHAssign src dst)) memH) -> (* Evaluation succeeds *)
    eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
         (interp_helix (denoteDSHOperator σ (DSHAssign src dst)) memH)
         (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from,bid_in))
                     g ρ memV).
Proof. 
  intros * GEN NEXT PRE GAM NOFAIL.

  cbn* in *; simp.
  hide_cfg.
  inv_resolve_PVar Heqs0.
  inv_resolve_PVar Heqs1.
  unfold denotePExpr in *; cbn* in *.
  simp; try_abs.

  clean_goal.
  repeat apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  rename s1 into si, s2 into sf,
  i5 into s1, i6 into s2,
  i8 into s3, i9 into s4,
  i10 into s5, i11 into s6.
  rename n1 into x_p, n2 into y_p.
  rename n4 into x_i, n3 into y_i.
  rename x0 into y.
  clean_goal.

  hred.
  hstep; [eauto |].
  hred; hstep; [eauto |].
  hred.

  subst; eutt_hide_left.
  vjmp.
  unfold fmap, Fmap_block; cbn.
  vred.
  vred.
  vred.

  (* Step 5. *)
  subst. eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.

  solve_state_invariant.
  solve_gamma_safe.

  introR; destruct_unit.
  intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
  destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
  cbn in *; inv_eqs.
  hvred.

  (* Step 6. *)
  eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.
  solve_gamma_safe.

  introR; destruct_unit.
  intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
  destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
  cbn in *; inv_eqs.

  hvred.
  break_inner_match_hyp; break_inner_match_hyp; try_abs.
  destruct_unit.

  rename vH into src, vH0 into dst, b into v.
  clean_goal.
  (* Step 7. *)
  hvred.
  hstep.
  unfold assert_NT_lt,assert_true_to_err in *; simp.
  hide_cont.
  clear NOFAIL.
  rename i1 into vsz.
  rename i0 into vx_p, i3 into vy_p.
  rename e into esrc.
  clean_goal.

  (* Question 1: is [vx_p] global, local, or can be either? *)
  (* We access in memory vx_p[e] *)
  edestruct memory_invariant_Ptr as (membk & ptr & LU & FITS & INLG & GETCELL); [| eauto | eauto |]; eauto.
  clear FITS.

  rewrite LU in H; symmetry in H; inv H.
  specialize (GETCELL _ _ Heqo1).
  clean_goal.
  (* I find some pointer either in the local or global environment *)
  destruct vx_p as [vx_p | vx_p]; cbn in INLG.
  { (* vx_p is in global environment *)
    edestruct denote_instr_gep_array as (ptr' & READ & EQ); cycle -1; [rewrite EQ; clear EQ | ..]; cycle 1.
    3: apply GETCELL.
    { vstep; solve_lu; reflexivity. }
    {
      destruct MONO2 as [| <-].
      - rewrite EXP1; auto.
        rewrite repr_of_nat_to_nat.
        cbn; reflexivity.
        eapply local_scope_preserve_modif; eauto.
        clear EXP1 EXP2 VAR1 VAR2.
        clean_goal.
        eapply Gamma_preserved_Gamma_eq; [exact GAM1 |].
        eapply Gamma_preserved_if_safe; [| exact SCOPE2].
        solve_gamma_safe.
      - rewrite EXP1.
        rewrite repr_of_nat_to_nat.
        reflexivity.
        eauto using local_scope_preserved_refl.
        eauto using Gamma_preserved_refl.
    }

    clear EXP1.
    clean_goal.

    subst_cont; vred.
    vred.
    (* load *)
    vstep.
    { vstep; solve_lu. }
    vred.
    hide_cont.

    destruct vy_p as [vy_p | vy_p].
    { (* vy_p in global *)
      assert (Γ si ≡ Γ sf) as CONT by solve_gamma.
      rewrite CONT in LUn0, LUn.
      edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

      clean_goal.
      rewrite yLU in H0; symmetry in H0; inv H0.

      edestruct denote_instr_gep_array_no_read as (yptr' & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
      { vstep; solve_lu.
        cbn; reflexivity.
      }
      { rewrite EXP2.
        - rewrite repr_of_nat_to_nat.
          cbn; reflexivity.
        - clear EXP2.
          clean_goal.
          solve_local_scope_preserved.
        - destruct PRE2.
          (* TODO: can we automate this better? *)
          assert (Γ si ≡ Γ s6) as GAMsisf by solve_gamma.
          eapply Gamma_preserved_Gamma_eq. eapply GAMsisf.
          eapply Gamma_preserved_if_safe with (s2:=sf); eauto.
          solve_local_scope_modif.
      }

      { rewrite typ_to_dtyp_D_array in yFITS.
        assert (sz0 ≡ Z.to_N (Int64.intval i4)) by
            (apply from_N_intval; eauto).
        subst.
        eauto.
      }

      vstep.
      subst_cont.
      vred.

      (* MOVE *)
      (* Notation "'store' e ',' f" := ((IVoid _, INSTR_Store _ e f _)) (at level 30, only printing). *)

      edestruct write_succeeds as [m2 WRITE_SUCCEEDS]; cycle 2.
      
      (* Store *)
      erewrite denote_instr_store; eauto.
      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }
      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }
      2: reflexivity.
      2: constructor.
      2:{
        eapply dtyp_fits_array_elem.
        rewrite typ_to_dtyp_D_array in yFITS.
        eapply yFITS.
        epose proof (@from_N_intval _ _ EQsz0).
        subst.
        eapply yGEP.

        (* Need to relate sz0 with i *)
        assert (sz0 ≡ Z.to_N (Int64.intval i)) as SZI. eapply vellvm_helix_ptr_size; eauto.
        subst.

        pose proof (DynamicValues.Int64.intrange dst).
        pose proof (Int64.intrange i4).
        pose proof (Int64.intrange i).

        (* Maybe Heqb *)
        unfold MInt64asNT.from_N in EQsz0.
        rewrite Znat.Z2N.id in EQsz0; [|lia].

        pose proof EQsz0 as EQsz0'.
        apply from_Z_intval in EQsz0'.

        rewrite EQsz0'.

        rewrite repr_of_nat_to_nat.
        apply Znat.Z2Nat.inj_lt; [lia|lia|].

        apply NPeano.Nat.ltb_lt in Heqb.
        rewrite Znat.Z2N.id; [|lia].
        rewrite <- EQsz0'.
        auto.
      }

      { vstep.
        rewrite denote_term_br_1.
        vstep.
        rewrite denote_ocfg_unfold_not_in.
        2: {
          (* TODO: Add a subst_cfg *)
          destruct VG; subst.
          cbn.

          unfold find_block.
          cbn.
          assert (bid_in ≢ nextblock).
          { (* Should hold from NEXT and Heqs *)
            eapply incBlockNamed_bound_between in Heqs.
            intros CONTRA; symmetry in CONTRA; revert CONTRA.
            eapply bid_bound_fresh; eauto.
            solve_prefix.
          }
          assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false) as BID_NEQ.
          {
            unfold Eqv.eqv_dec_p.
            break_match_goal; [contradiction | reflexivity].
          }
          rewrite BID_NEQ.
          reflexivity.
        }

        vstep.

        apply eutt_Ret.
        cbn.
        split; [| split]; cbn.
        - (* State invariant *)
          cbn.
          split; eauto.
          destruct PRE2.
          unfold memory_invariant.
          intros n1 v0 τ x0 H4 H5.
          cbn in mem_is_inv.
          pose proof (mem_is_inv n1 v0 τ x0 H4 H5).

          (* TODO: can probably turn this into a lemma *)
          (* All depends on whether x0 == r, r1, or r0 *)
          destruct x0.
          { (* x0 is a global *)
            destruct v0.
            cbn. cbn in H4.
            { cbn in H. destruct H as (ptr_l & τ' & TYPE & INLG' & READ').
              do 2 eexists.
              repeat split; eauto.

              destruct (Z.eq_dec (fst ptr_l) (fst yptr)) as [EQ | NEQ].
              - destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
                + do 2 red in EQid.
                  subst. cbn in yINLG.
                  assert (n1 ≡ y_p).
                  eapply st_no_id_aliasing; eauto.
                  subst.
                  rewrite Heqo0 in H4.
                  discriminate H4.
                + unfold Eqv.eqv, eqv_raw_id in NEQid.
                  assert (fst ptr_l ≢ fst yptr).
                  { assert (ID_Global id ≢ ID_Global vy_p).
                    injection. apply NEQid.

                    eapply st_no_llvm_ptr_aliasing.
                    eapply H4.
                    eapply Heqo0.
                    3: eapply  H.
                    all: eauto.
                  }
                  contradiction.
                  
              - epose proof (IRState_is_WF _ _ H4) as [idT NT].
                rewrite H5 in NT. cbn in NT. inv NT.
                inv H1.

                erewrite write_untouched; eauto.
                constructor.
                rewrite typ_to_dtyp_I.

                pose proof (handle_gep_addr_array_same_block _ _ _ _ yGEP) as YPTRBLOCK.
                rewrite YPTRBLOCK in NEQ.
                do 2 red. auto.
            }

            { cbn in H. destruct H as (ptr_l & τ' & TYPE & INLG' & READ').
              do 2 eexists.
              repeat split; eauto.

              destruct (Z.eq_dec (fst ptr_l) (fst yptr)) as [EQ | NEQ].
              - destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
                + do 2 red in EQid.
                  subst. cbn in yINLG.
                  assert (n1 ≡ y_p).
                  eapply st_no_id_aliasing; eauto.
                  subst.
                  rewrite Heqo0 in H4.
                  discriminate H4.
                + unfold Eqv.eqv, eqv_raw_id in NEQid.
                  assert (fst ptr_l ≢ fst yptr).
                  { assert (ID_Global id ≢ ID_Global vy_p).
                    injection. apply NEQid.

                    eapply st_no_llvm_ptr_aliasing.
                    eapply H4.
                    eapply Heqo0.
                    3: eapply  H.
                    all: eauto.
                  }
                  contradiction.
              - epose proof (IRState_is_WF _ _ H4) as [idT NT].
                rewrite H5 in NT. cbn in NT. inv NT.
                inv H1.

                erewrite write_untouched; eauto.
                constructor.

                cbn.
                rewrite typ_to_dtyp_D. 

                pose proof (handle_gep_addr_array_same_block _ _ _ _ yGEP) as YPTRBLOCK.
                rewrite YPTRBLOCK in NEQ.
                do 2 red. auto.
            }
            destruct H as (bk_h & ptr_l & τ' & MINV).
            destruct MINV as (MLUP & MTYP & FITS & INLG' & GET).
            destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].

            - (* DSHPtrVals alias *)
              subst.
              rewrite yLU in MLUP.
              inv MLUP.

              epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
              pose proof H5 as IDS.
              rewrite LUn0 in IDS.
              inv IDS.

              (* Since y_i = a, we know this matches the block that was written to *)
              exists (mem_add (MInt64asNT.to_nat dst) v bk_h).

              (* *)
              exists yptr. exists (TYPE_Array sz0 TYPE_Double).

              split.
              { rewrite memory_lookup_memory_set_eq. reflexivity. }
              split; auto.
              split.
              eapply dtyp_fits_after_write; eauto.
              split.
              { cbn.
                rewrite Heqo0 in H4.
                rewrite LUn0 in H5.
                inversion H5; subst; auto.
              }
              { (* Need to show that every lookup matches *)
                intros idx v0 H3.

                pose proof (dtyp_fits_allocated yFITS) as yALLOC.


                epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
                erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

                destruct (Nat.eq_dec (MInt64asNT.to_nat idx) (MInt64asNT.to_nat dst)) as [EQdst | NEQdst].
                {
                  (* In the case where i = DST *)

                  (*                I know v0 = v (which is the value from the source (GETCELL) *)

                  (*                I should be able to show that yptr' is GEP of yptr in this case... *)

                  (*                May be able to use write array lemmas...? *)
                  (*              *)

                  rewrite EQdst in *.
                  rewrite mem_lookup_mem_add_eq in H3; inv H3.

                  change (UVALUE_Double v0) with (dvalue_to_uvalue (DVALUE_Double v0)).
                  eapply write_array_cell_get_array_cell; eauto.
                  constructor.
                }
                {
                  (* In the case where i <> dst *)

                  (*                I should be able to use yGETCELL along with H4 (getting rid of mem_add) *)
                  (*              *)
                  rewrite mem_lookup_mem_add_neq in H3; auto.
                  erewrite write_array_cell_untouched; eauto.
                  constructor.

                  apply to_nat_unsigned; auto.
                }
              }

            - (* DSHPtrVals do not alias *)

              (* This must be the case because if y_i <> a, then *)
              (*           we're looking at a different helix block. *)
              exists bk_h.

              (* MOVE *)
              Opaque memory_lookup.
              cbn.
              (* Need the pointer that matches up with @id *)
              exists ptr_l. exists τ'.

              rewrite memory_lookup_memory_set_neq; auto.
              repeat split; auto.

              eapply dtyp_fits_after_write; eauto.

              assert (fst (ptr_l) ≢ fst yptr) as DIFF_BLOCKS.
              {
                (* yINLG and INLG' *)
                eapply st_no_llvm_ptr_aliasing.
                6: eapply INLG'.
                6:{ (* This is local now... *)
                  eapply in_local_or_global_addr_same_global. eapply yINLG.
                }
                3: eapply H5.
                3: eapply LUn0.
                all: eauto.
                intros CONTRA; inv CONTRA.
                (* H5 and LUN5, means that n1 = y_p, which means a = y_i *)
                assert (a ≡ y_i).
                { assert (n1 ≡ y_p).
                  eapply st_no_id_aliasing; eauto.
                  subst.
                  rewrite Heqo0 in H4.
                  inv H4.
                  contradiction.
                }
                contradiction.
              }

              pose proof (dtyp_fits_allocated yFITS) as yALLOC.
              epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
              rewrite WRITE_ARRAY in WRITE_SUCCEEDS.

              intros idx v0 H3.
              erewrite write_array_cell_untouched_ptr_block; eauto.
              constructor.
          }

          { (* x0 is a local *)
            pose proof (dtyp_fits_allocated yFITS) as yALLOC.
            epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
            pose proof WRITE_SUCCEEDS as WRITE'.
            erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

            destruct v0. (* Probably need to use WF_IRState to make sure we only consider valid types *)
            solve_in_local_or_global_scalar.
            solve_in_local_or_global_scalar.

            destruct H as (bk_h & ptr_l & τ' & MINV). (* Do I need this? *)
            destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
            - (* PTR aliases, local case should be bogus... *)
              subst.

              epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
              rewrite LUn0 in H5.
              inversion H5.
            - (* This is the branch where a and y_i don't *)
              (*              alias. These are the DSHPtrVal pointers... *)

              (*              DSHPtrVal a size1 corresponds to %id, which must be a local id. *)

              (*              I need to show the memory invariant holds. *)

              (*              - y_i points to ymembk *)
              (*              - a points to bk_h *)

              (*              no_pointer_aliasing is a given. *)

              (*              We should say that there exists bk_h and ptr_l. *)

              (*              The memory_lookup case should hold because we *)
              (*              don't care about the memory_set operation because *)
              (*              a <> y_i *)

              (*              mem_lookup_succeeds is as before. *)

              (*              dtyp_fits should hold because the write shouldn't *)
              (*              change the block for ptr_l at all (no aliasing). *)

              (*              I need in_local_or_global_addr to hold, meaning I can find *)

              (*              l1 @ id = Some ptr_l *)

              (*              If id is in l0 then this follows from freshness and the old MINV. *)

              (*              Otherwise, there's actually a contradiction with *)
              (*              MINV's in_local_or_global_addr... Because id *)
              (*              would not be in l0. *)
              (*            *)

              destruct MINV as (MLUP & MSUC & FITS & INLG' & GET).
              subst.
              cbn.
              exists bk_h. exists ptr_l. exists τ'.

              rewrite memory_lookup_memory_set_neq; auto.
              repeat (split; auto).
              + eapply dtyp_fits_after_write; eauto.
              + solve_local_lookup.
              + intros idx v0 H6.
                pose proof (GET idx v0 H6).
                assert (ID_Local id ≢ ID_Global vy_p) as IDNEQ by discriminate.
                assert (fst ptr_l ≢ fst yptr).
                { eapply st_no_llvm_ptr_aliasing.
                  5: eapply IDNEQ.
                  eapply H4.
                  eapply Heqo0.
                  all: eauto.
                }

                assert (fst yptr ≡ fst yptr') by (eapply handle_gep_addr_array_same_block; eauto).
                erewrite write_array_cell_untouched_ptr_block; eauto.
                constructor.
          }

          + destruct PRE2. eapply st_no_id_aliasing; eauto.
          + eapply st_no_dshptr_aliasing; eauto.
          + (* TODO: turn this into a tactic? *)
            do 3 (eapply no_llvm_ptr_aliasing_not_in_gamma; [ | eauto | solve_not_in_gamma]).
            eapply state_invariant_no_llvm_ptr_aliasing; eauto.
          + unfold id_allocated in *.
            intros.
            destruct PRE2.

            specialize (st_id_allocated n1). cbn in *.
            specialize (st_id_allocated _ _ H).
            eapply mem_block_exists_memory_set; eauto.
        - exists bid_in. reflexivity.

        - (* The only local variables modified are in [si;sf] *)
          assert (local_scope_modif s5 sf ρ l0); solve_local_scope_modif.
      }
    }

    { (* vy_p in local *)
      assert (Γ si ≡ Γ sf) as CONT by solve_gamma.
      rewrite CONT in LUn0, LUn.
      edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant|].

      clean_goal.
      rewrite yLU in H0; symmetry in H0; inv H0.
      cbn in yINLG.

      edestruct denote_instr_gep_array_no_read as (yptr' & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
      { vstep.
        do 3 (setoid_rewrite lookup_alist_add_ineq; [eauto | solve_id_neq ]).
        reflexivity.
      }
      { rewrite EXP2.
        - rewrite repr_of_nat_to_nat.
          cbn; reflexivity.
        - clear EXP2.
          clean_goal.
          solve_local_scope_preserved.
        - solve_gamma_preserved.
      }

      { rewrite typ_to_dtyp_D_array in yFITS.
        assert (sz0 ≡ Z.to_N (Int64.intval i4)) by
            (apply from_N_intval; eauto).
        subst.
        eauto.
      }

      vstep.
      subst_cont.
      vred.

      edestruct write_succeeds as [m2 WRITE_SUCCEEDS]; cycle 2.

      (* Store *)
      erewrite denote_instr_store; eauto.
      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }

      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }

      2: reflexivity.
      2: constructor.
      2:{
        eapply dtyp_fits_array_elem.
        rewrite typ_to_dtyp_D_array in yFITS.
        eapply yFITS.
        epose proof (@from_N_intval _ _ EQsz0).
        subst.
        eapply yGEP.

        (* Need to relate sz0 with i *)
        assert (sz0 ≡ Z.to_N (Int64.intval i)) as SZI. eapply vellvm_helix_ptr_size; eauto.
        subst.

        pose proof (DynamicValues.Int64.intrange dst).
        pose proof (Int64.intrange i4).
        pose proof (Int64.intrange i).

        (* Maybe Heqb *)
        unfold MInt64asNT.from_N in EQsz0.
        rewrite Znat.Z2N.id in EQsz0; [|lia].

        pose proof EQsz0 as EQsz0'.
        apply from_Z_intval in EQsz0'.

        rewrite EQsz0'.

        rewrite repr_of_nat_to_nat.
        apply Znat.Z2Nat.inj_lt; [lia|lia|].

        apply NPeano.Nat.ltb_lt in Heqb.
        rewrite Znat.Z2N.id; [|lia].
        rewrite <- EQsz0'.
        auto.
      }

      vstep.
      rewrite denote_term_br_1.
      vstep.
      rewrite denote_ocfg_unfold_not_in.
      2: {
        (* TODO: Add a subst_cfg *)
        destruct VG; subst.
        cbn.

        unfold find_block.
        cbn.
        assert (bid_in ≢ nextblock).
        { (* Should hold from NEXT and Heqs *)
          eapply incBlockNamed_bound_between in Heqs.
          intros CONTRA; symmetry in CONTRA; revert CONTRA.
          eapply bid_bound_fresh; eauto.
          solve_prefix.
        }
        assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false).
        {
          unfold Eqv.eqv_dec_p.
          break_match_goal; [contradiction | reflexivity].
        }
        rewrite H0.
        reflexivity.
      }
      vstep.

      apply eutt_Ret; split; [| split]; cbn.
      - (* TODO: add to solve_state_invariant *)
        do 3 (eapply state_invariant_same_Γ; [reflexivity | solve_not_in_gamma | ]).
        destruct PRE2.
        split; eauto.

        (* Solve memory invariant... *)
        cbn. cbn in mem_is_inv.
        intros n1 v0 τ x H H0.
        destruct x.
        { (* Global *)
          pose proof (dtyp_fits_allocated yFITS) as yALLOC.
          epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
          pose proof WRITE_SUCCEEDS as WRITE'.
          erewrite WRITE_ARRAY in WRITE_SUCCEEDS.


          assert (ID_Global id ≢ ID_Local vy_p) as IDNEQ by discriminate.
          destruct v0.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            cbn.
            destruct INV as (ptr_l & τ' & TYP & INLG' & READ').
            exists ptr_l. exists τ'.

            (* TODO: automate *)
            assert (fst ptr_l ≢ fst yptr).
            { eapply st_no_llvm_ptr_aliasing.
              5: eapply IDNEQ.
              eapply H.
              eapply Heqo0.
              all: eauto.
            }

            repeat (split; eauto).

            assert (fst yptr ≡ fst yptr') by (eapply handle_gep_addr_array_same_block; eauto).
            rewrite H2 in H1.
            eapply write_different_blocks; eauto.
            cbn. reflexivity.
            2:constructor.

            epose proof (IRState_is_WF _ n1 H) as (id' & N).
            rewrite H0 in N. inv N.
            cbn in H5. inversion H5.
            subst.
            eapply read_type in READ'.
            rewrite typ_to_dtyp_I.
            constructor.

          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            cbn.
            destruct INV as (ptr_l & τ' & TYP & INLG' & READ').
            exists ptr_l. exists τ'.

            (* TODO: automate *)
            assert (fst ptr_l ≢ fst yptr).
            { eapply st_no_llvm_ptr_aliasing.
              5: eapply IDNEQ.
              eapply H.
              eapply Heqo0.
              all: eauto.
            }

            repeat (split; eauto).

            assert (fst yptr ≡ fst yptr') by (eapply handle_gep_addr_array_same_block; eauto).
            rewrite H2 in H1.
            eapply write_different_blocks; eauto.
            reflexivity.
            2: constructor.

            epose proof (IRState_is_WF _ n1 H) as (id' & N).
            rewrite H0 in N. inv N.
            cbn in H5. inversion H5.
            subst.
            eapply read_type in READ'.
            rewrite typ_to_dtyp_D.
            constructor.
            
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            destruct INV as (bk & ptr_l & τ' & MLUP & TYP & FITS & LOOKUP & GETCELL_ptr_l).

            destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
            { exists (mem_add (MInt64asNT.to_nat dst) v ymembk). exists ptr_l. exists τ'.

              subst.
              assert (n1 ≡ y_p) by eauto.
              rewrite yLU in MLUP.
              inv MLUP.

              repeat (split; eauto).
              - eapply memory_lookup_memory_set_eq.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.
                rewrite LUn0 in H0.
                inversion H0; subst.
            }
            { exists bk. exists ptr_l. exists τ'.
              repeat (split; eauto).
              - erewrite memory_lookup_memory_set_neq; eauto.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.

                assert (fst ptr_l ≢ fst yptr).
                { eapply st_no_llvm_ptr_aliasing.
                  5: eapply IDNEQ.
                  eapply H.
                  eapply Heqo0.
                  all: eauto.
                }

                erewrite write_array_cell_untouched_ptr_block; eauto.
                constructor.
            }
        }

        { (* Local *)
          destruct v0.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            eauto.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            eauto.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            destruct INV as (bk & ptr_l & τ' & MLUP & TYP & FITS & LOCALS & GETCELL_ptr_l).

            pose proof (dtyp_fits_allocated yFITS) as yALLOC.
            epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
            pose proof WRITE_SUCCEEDS as WRITE'.
            erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

            destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
            { exists (mem_add (MInt64asNT.to_nat dst) v ymembk). exists ptr_l. exists τ'.

              subst.
              assert (n1 ≡ y_p) by eauto.
              rewrite yLU in MLUP.
              inv MLUP.

              repeat (split; eauto).
              - eapply memory_lookup_memory_set_eq.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.
                rewrite LUn0 in H0.
                inversion H0; subst.

                rewrite yINLG in LOCALS.
                inversion LOCALS; subst.

                destruct (Nat.eq_dec (MInt64asNT.to_nat idx) (MInt64asNT.to_nat dst)) as [EQdst | NEQdst].
                + rewrite EQdst in *.
                  rewrite mem_lookup_mem_add_eq in H1; inv H1.

                  change (UVALUE_Double v0) with (dvalue_to_uvalue (DVALUE_Double v0)).
                  eapply write_array_cell_get_array_cell; eauto.
                  constructor.
                + rewrite mem_lookup_mem_add_neq in H1; inv H1; eauto.
                  erewrite write_array_cell_untouched; eauto.
                  constructor.
                  apply to_nat_unsigned; auto.
            }
            { exists bk. exists ptr_l. exists τ'.
              repeat (split; eauto).
              - erewrite memory_lookup_memory_set_neq; eauto.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.
                destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
                + unfold Eqv.eqv, eqv_raw_id in EQid.
                  subst.

                  assert (n1 ≡ y_p) by (eapply no_id_aliasing_n_eq; eauto).
                  subst.
                  rewrite Heqo0 in H.
                  inversion H; subst; contradiction.
                + unfold Eqv.eqv, eqv_raw_id in NEQid.
                  assert (fst ptr_l ≢ fst yptr).
                  { assert (ID_Local id ≢ ID_Local vy_p) as NEQl.
                    { intros CONTRA. inv CONTRA. contradiction. }

                    (* May have to recover some things I rewrote / cbn'd *)
                    eapply st_no_llvm_ptr_aliasing.
                    5: eapply NEQl.
                    eapply H.
                    eapply Heqo0.
                    all:eauto.
                  }
                  erewrite write_array_cell_untouched_ptr_block; eauto.
                  constructor.
            }
        }

        { (* id_allocated *)
          unfold id_allocated in *.
          intros n1 addr0 val H.
          specialize (st_id_allocated n1). cbn in *.
          specialize (st_id_allocated _ _ H).
          eapply mem_block_exists_memory_set; eauto.
        }
      - exists bid_in. reflexivity.
      - assert (local_scope_modif s5 sf ρ l0); solve_local_scope_modif.
    }
  }


  { (* vx_p is in local environment *)
    edestruct denote_instr_gep_array as (ptr' & READ & EQ); cycle -1; [rewrite EQ; clear EQ | ..]; cycle 1.
    3: apply GETCELL.
    { vstep; cbn; try reflexivity.
      assert (local_scope_modif s5 sf ρ l0) by solve_local_scope_modif.
      assert (in_Gamma σ si vx_p) by solve_in_gamma.
      rewrite <- INLG.
      destruct PRE2.

      assert (~ lid_bound_between si sf vx_p).
      { intros BETWEEN.
        eapply GAM; eauto.
      }

      symmetry.
      eapply local_scope_modif_external; eauto.
      intros BETWEEN.
      eapply H2.
      eapply lid_bound_between_shrink; eauto; solve_local_count.
    }

    {
      destruct MONO2 as [| <-].
      - rewrite EXP1; auto.
        rewrite repr_of_nat_to_nat.
        cbn; reflexivity.
        eapply local_scope_preserve_modif; eauto.
        clear EXP1 EXP2 VAR1 VAR2.
        clean_goal.
        eapply Gamma_preserved_Gamma_eq; [exact GAM1 |].
        eapply Gamma_preserved_if_safe; [| exact SCOPE2].
        solve_gamma_safe.
      - rewrite EXP1.
        rewrite repr_of_nat_to_nat.
        reflexivity.
        eauto using local_scope_preserved_refl.
        eauto using Gamma_preserved_refl.
    }

    clear EXP1.
    clean_goal.

    subst_cont; vred.
    vred.
    (* load *)
    vstep.
    { vstep; solve_lu. }
    vred.
    hide_cont.

    destruct vy_p as [vy_p | vy_p].
    { (* vy_p in global *)
      assert (Γ si ≡ Γ sf) as CONT by solve_gamma.
      rewrite CONT in LUn0, LUn.
      edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

      clean_goal.
      rewrite yLU in H0; symmetry in H0; inv H0.

      edestruct denote_instr_gep_array_no_read as (yptr' & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
      { vstep; solve_lu.
        cbn; reflexivity.
      }
      { rewrite EXP2.
        - rewrite repr_of_nat_to_nat.
          cbn; reflexivity.
        - clear EXP2.
          clean_goal.
          solve_local_scope_preserved.
        - destruct PRE2.
          (* TODO: can we automate this better? *)
          assert (Γ si ≡ Γ s6) as GAMsisf by solve_gamma.
          eapply Gamma_preserved_Gamma_eq. eapply GAMsisf.
          eapply Gamma_preserved_if_safe with (s2:=sf); eauto.
          solve_local_scope_modif.
      }

      { rewrite typ_to_dtyp_D_array in yFITS.
        assert (sz0 ≡ Z.to_N (Int64.intval i4)) by
            (apply from_N_intval; eauto).
        subst.
        eauto.
      }

      vstep.
      subst_cont.
      vred.

      edestruct write_succeeds as [m2 WRITE_SUCCEEDS]; cycle 2.

      (* Store *)
      erewrite denote_instr_store; eauto.
      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }

      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }

      2: reflexivity.
      2: constructor.
      2:{
        eapply dtyp_fits_array_elem.
        rewrite typ_to_dtyp_D_array in yFITS.
        eapply yFITS.
        epose proof (@from_N_intval _ _ EQsz0).
        subst.
        eapply yGEP.

        (* Need to relate sz0 with i *)
        assert (sz0 ≡ Z.to_N (Int64.intval i)) as SZI. eapply vellvm_helix_ptr_size; eauto.
        subst.

        pose proof (DynamicValues.Int64.intrange dst).
        pose proof (Int64.intrange i4).
        pose proof (Int64.intrange i).

        (* Maybe Heqb *)
        unfold MInt64asNT.from_N in EQsz0.
        rewrite Znat.Z2N.id in EQsz0; [|lia].

        pose proof EQsz0 as EQsz0'.
        apply from_Z_intval in EQsz0'.

        rewrite EQsz0'.

        rewrite repr_of_nat_to_nat.
        apply Znat.Z2Nat.inj_lt; [lia|lia|].

        apply NPeano.Nat.ltb_lt in Heqb.
        rewrite Znat.Z2N.id; [|lia].
        rewrite <- EQsz0'.
        auto.
      }

      vstep.
      rewrite denote_term_br_1.
      vstep.
      rewrite denote_ocfg_unfold_not_in.
      2: {
        (* TODO: Add a subst_cfg *)
        destruct VG; subst.
        cbn.

        unfold find_block.
        cbn.
        assert (bid_in ≢ nextblock).
        { (* Should hold from NEXT and Heqs *)
          eapply incBlockNamed_bound_between in Heqs.
          intros CONTRA; symmetry in CONTRA; revert CONTRA.
          eapply bid_bound_fresh; eauto.
          solve_prefix.
        }
        assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false) as BID_NEQ.
        {
          unfold Eqv.eqv_dec_p.
          break_match_goal; [contradiction | reflexivity].
        }
        rewrite BID_NEQ.
        reflexivity.
      }

      vstep.

      apply eutt_Ret.
      cbn.
      split; [| split]; cbn.
      - (* State invariant *)
        cbn.
        split; eauto.
        destruct PRE2.
        unfold memory_invariant.
        intros n1 v0 τ x0 H4 H5.
        cbn in mem_is_inv.
        pose proof (mem_is_inv n1 v0 τ x0 H4 H5).

        (* TODO: can probably turn this into a lemma *)
        (* All depends on whether x0 == r, r1, or r0 *)
        destruct x0.
        { (* x0 is a global *)
          destruct v0.
          cbn. cbn in H4.
          { cbn in H. destruct H as (ptr_l & τ' & TYPE & INLG' & READ').
            do 2 eexists.
            repeat split; eauto.

            destruct (Z.eq_dec (fst ptr_l) (fst yptr)) as [EQ | NEQ].
            - destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
              + do 2 red in EQid.
                subst. cbn in yINLG.
                assert (n1 ≡ y_p).
                eapply st_no_id_aliasing; eauto.
                subst.
                rewrite Heqo0 in H4.
                discriminate H4.
              + unfold Eqv.eqv, eqv_raw_id in NEQid.
                assert (fst ptr_l ≢ fst yptr).
                { assert (ID_Global id ≢ ID_Global vy_p).
                  injection. apply NEQid.

                  eapply st_no_llvm_ptr_aliasing.
                  eapply H4.
                  eapply Heqo0.
                  3: eapply  H.
                  all: eauto.
                }
                contradiction.
            - epose proof (IRState_is_WF _ _ H4) as [idT NT].
              rewrite H5 in NT. cbn in NT. inv NT.
              inv H1.

              erewrite write_untouched; eauto.
              constructor.

              rewrite typ_to_dtyp_I.

              pose proof (handle_gep_addr_array_same_block _ _ _ _ yGEP) as YPTRBLOCK.
              rewrite YPTRBLOCK in NEQ.
              do 2 red. auto.
          }

          { cbn in H. destruct H as (ptr_l & τ' & TYPE & INLG' & READ').
            do 2 eexists.
            repeat split; eauto.

            destruct (Z.eq_dec (fst ptr_l) (fst yptr)) as [EQ | NEQ].
            - destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
              + do 2 red in EQid.
                subst. cbn in yINLG.
                assert (n1 ≡ y_p).
                eapply st_no_id_aliasing; eauto.
                subst.
                rewrite Heqo0 in H4.
                discriminate H4.
              + unfold Eqv.eqv, eqv_raw_id in NEQid.
                assert (fst ptr_l ≢ fst yptr).
                { assert (ID_Global id ≢ ID_Global vy_p).
                  injection. apply NEQid.

                  eapply st_no_llvm_ptr_aliasing.
                  eapply H4.
                  eapply Heqo0.
                  3: eapply  H.
                  all: eauto.
                }
                contradiction.
            - epose proof (IRState_is_WF _ _ H4) as [idT NT].
              rewrite H5 in NT. cbn in NT. inv NT.
              inv H1.

              erewrite write_untouched; eauto.
              constructor.

              cbn.
              rewrite typ_to_dtyp_D.

              pose proof (handle_gep_addr_array_same_block _ _ _ _ yGEP) as YPTRBLOCK.
              rewrite YPTRBLOCK in NEQ.
              do 2 red. auto.
          }
          destruct H as (bk_h & ptr_l & τ' & MINV).
          destruct MINV as (MLUP & MTYP & FITS & INLG' & GET).
          destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
          - (* DSHPtrVals alias *)
            subst.
            rewrite yLU in MLUP.
            inv MLUP.

            epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
            pose proof H5 as IDS.
            rewrite LUn0 in IDS.
            inv IDS.

            (* Since y_i = a, we know this matches the block that was written to *)
            exists (mem_add (MInt64asNT.to_nat dst) v bk_h).

            (* *)
            exists yptr. exists (TYPE_Array sz0 TYPE_Double).

            split.
            { rewrite memory_lookup_memory_set_eq. reflexivity. }
            split; auto.
            split.
            eapply dtyp_fits_after_write; eauto.
            split.
            { cbn.
              rewrite Heqo0 in H4.
              rewrite LUn0 in H5.
              inversion H5; subst; auto.
            }
            { (* Need to show that every lookup matches *)
              intros idx v0 H3.

              pose proof (dtyp_fits_allocated yFITS) as yALLOC.
              epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
              erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

              destruct (Nat.eq_dec (MInt64asNT.to_nat idx) (MInt64asNT.to_nat dst)) as [EQdst | NEQdst].
              {
                (* In the case where i = DST *)

                (*                I know v0 = v (which is the value from the source (GETCELL) *)

                (*                I should be able to show that yptr' is GEP of yptr in this case... *)

                (*                May be able to use write array lemmas...? *)
                (*              *)

                rewrite EQdst in *.
                rewrite mem_lookup_mem_add_eq in H3; inv H3.

                change (UVALUE_Double v0) with (dvalue_to_uvalue (DVALUE_Double v0)).
                eapply write_array_cell_get_array_cell; eauto.
                constructor.
              }
              {
                (* In the case where i <> dst *)

                (*                I should be able to use yGETCELL along with H4 (getting rid of mem_add) *)
                (*              *)
                rewrite mem_lookup_mem_add_neq in H3; auto.
                erewrite write_array_cell_untouched; eauto.
                constructor.
                apply to_nat_unsigned; auto.
              }
            }
          - (* DSHPtrVals do not alias *)

            (* This must be the case because if y_i <> a, then *)
            (*           we're looking at a different helix block. *)
            exists bk_h.

            cbn.
            (* Need the pointer that matches up with @id *)
            exists ptr_l. exists τ'.

            rewrite memory_lookup_memory_set_neq; auto.
            repeat split; auto.

            eapply dtyp_fits_after_write; eauto.

            assert (fst (ptr_l) ≢ fst yptr) as DIFF_BLOCKS.
            { (* yINLG and INLG' *)
              eapply st_no_llvm_ptr_aliasing.
              6: eapply INLG'.
              6:{ (* This is local now... *)
                eapply in_local_or_global_addr_same_global. eapply yINLG. }
              3: eapply H5.
              3: eapply LUn0.
              all: eauto.
              intros CONTRA; inv CONTRA.
              (* H5 and LUN5, means that n1 = y_p, which means a = y_i *)
              assert (a ≡ y_i).
              { assert (n1 ≡ y_p).
                eapply st_no_id_aliasing; eauto.
                subst.
                rewrite Heqo0 in H4.
                inv H4.
                contradiction.
              }
              contradiction.
            }

            pose proof (dtyp_fits_allocated yFITS) as yALLOC.
            epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
            rewrite WRITE_ARRAY in WRITE_SUCCEEDS.

            intros idx v0 H3.
            erewrite write_array_cell_untouched_ptr_block; eauto.
            constructor.
        }

        { (* x0 is a local *)
          pose proof (dtyp_fits_allocated yFITS) as yALLOC.
          epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
          pose proof WRITE_SUCCEEDS as WRITE'.
          erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

          destruct v0. (* Probably need to use WF_IRState to make sure we only consider valid types *)
          solve_in_local_or_global_scalar.
          solve_in_local_or_global_scalar.

          destruct H as (bk_h & ptr_l & τ' & MINV). (* Do I need this? *)
          destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
          - (* PTR aliases, local case should be bogus... *)
            subst.

            epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
            rewrite LUn0 in H5.
            inversion H5.
          - (* This is the branch where a and y_i don't *)
            (*              alias. These are the DSHPtrVal pointers... *)

            (*              DSHPtrVal a size1 corresponds to %id, which must be a local id. *)

            (*              I need to show the memory invariant holds. *)

            (*              - y_i points to ymembk *)
            (*              - a points to bk_h *)

            (*              no_pointer_aliasing is a given. *)

            (*              We should say that there exists bk_h and ptr_l. *)

            (*              The memory_lookup case should hold because we *)
            (*              don't care about the memory_set operation because *)
            (*              a <> y_i *)

            (*              mem_lookup_succeeds is as before. *)

            (*              dtyp_fits should hold because the write shouldn't *)
            (*              change the block for ptr_l at all (no aliasing). *)

            (*              I need in_local_or_global_addr to hold, meaning I can find *)

            (*              l1 @ id = Some ptr_l *)

            (*              If id is in l0 then this follows from freshness and the old MINV. *)

            (*              Otherwise, there's actually a contradiction with *)
            (*              MINV's in_local_or_global_addr... Because id *)
            (*              would not be in l0. *)
            (*            *)

            destruct MINV as (MLUP & MSUC & FITS & INLG' & GET).
            subst.
            cbn.
            exists bk_h. exists ptr_l. exists τ'.

            rewrite memory_lookup_memory_set_neq; auto.
            repeat (split; auto).
            + eapply dtyp_fits_after_write; eauto.
            + solve_local_lookup.
            + intros idx v0 H6.
              pose proof (GET idx v0 H6).
              assert (ID_Local id ≢ ID_Global vy_p) as IDNEQ by discriminate.
              assert (fst ptr_l ≢ fst yptr).
              { eapply st_no_llvm_ptr_aliasing.
                5: eapply IDNEQ.
                eapply H4.
                eapply Heqo0.
                all: eauto.
              }

              assert (fst yptr ≡ fst yptr') by (eapply handle_gep_addr_array_same_block; eauto).
              erewrite write_array_cell_untouched_ptr_block; eauto.
              constructor.
        }

        + destruct PRE2. eapply st_no_id_aliasing; eauto.
        + eapply st_no_dshptr_aliasing; eauto.
        + (* TODO: turn this into a tactic? *)
          do 3 (eapply no_llvm_ptr_aliasing_not_in_gamma; [ | eauto | solve_not_in_gamma]).
          eapply state_invariant_no_llvm_ptr_aliasing; eauto.
        + unfold id_allocated in *.
          intros.
          destruct PRE2.

          specialize (st_id_allocated n1). cbn in *.
          specialize (st_id_allocated _ _ H).
          eapply mem_block_exists_memory_set; eauto.
      - exists bid_in. reflexivity.

      - (* The only local variables modified are in [si;sf] *)
        assert (local_scope_modif s5 sf ρ l0); solve_local_scope_modif.

    }

    { (* vy_p in local *)
      assert (Γ si ≡ Γ sf) as CONT by solve_gamma.
      rewrite CONT in LUn0, LUn.
      edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant|].

      clean_goal.
      rewrite yLU in H0; symmetry in H0; inv H0.
      cbn in yINLG.

      edestruct denote_instr_gep_array_no_read as (yptr' & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
      { vstep.
        do 3 (setoid_rewrite lookup_alist_add_ineq; [eauto | solve_id_neq ]).
        reflexivity.
      }
      { rewrite EXP2.
        - rewrite repr_of_nat_to_nat.
          cbn; reflexivity.
        - clear EXP2.
          clean_goal.
          solve_local_scope_preserved.
        - solve_gamma_preserved.
      }

      { rewrite typ_to_dtyp_D_array in yFITS.
        assert (sz0 ≡ Z.to_N (Int64.intval i4)) by
            (apply from_N_intval; eauto).
        subst.
        eauto.
      }

      vstep.
      subst_cont.
      vred.

      edestruct write_succeeds as [m2 WRITE_SUCCEEDS]; cycle 2.

      (* Store *)
      erewrite denote_instr_store; eauto.
      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }

      2: {
        vstep.
        - cbn.
          solve_local_lookup.
        - cbn.
          apply eqit_Ret.
          cbn.
          reflexivity.
      }

      2: reflexivity.
      2: constructor.
      2:{
        eapply dtyp_fits_array_elem.
        rewrite typ_to_dtyp_D_array in yFITS.
        eapply yFITS.
        epose proof (@from_N_intval _ _ EQsz0).
        subst.
        eapply yGEP.

        (* Need to relate sz0 with i *)
        assert (sz0 ≡ Z.to_N (Int64.intval i)) as SZI. eapply vellvm_helix_ptr_size; eauto.
        subst.

        pose proof (DynamicValues.Int64.intrange dst).
        pose proof (Int64.intrange i4).
        pose proof (Int64.intrange i).

        (* Maybe Heqb *)
        unfold MInt64asNT.from_N in EQsz0.
        rewrite Znat.Z2N.id in EQsz0; [|lia].

        pose proof EQsz0 as EQsz0'.
        apply from_Z_intval in EQsz0'.

        rewrite EQsz0'.

        rewrite repr_of_nat_to_nat.
        apply Znat.Z2Nat.inj_lt; [lia|lia|].

        apply NPeano.Nat.ltb_lt in Heqb.
        rewrite Znat.Z2N.id; [|lia].
        rewrite <- EQsz0'.
        auto.
      }

      vstep.
      rewrite denote_term_br_1.
      vstep.
      rewrite denote_ocfg_unfold_not_in.
      2: {
        (* TODO: Add a subst_cfg *)
        destruct VG; subst.
        cbn.

        unfold find_block.
        cbn.
        assert (bid_in ≢ nextblock).
        { (* Should hold from NEXT and Heqs *)
          eapply incBlockNamed_bound_between in Heqs.
          intros CONTRA; symmetry in CONTRA; revert CONTRA.
          eapply bid_bound_fresh; eauto.
          solve_prefix.
        }
        assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false).
        {
          unfold Eqv.eqv_dec_p.
          break_match_goal; [contradiction | reflexivity].
        }
        rewrite H0.
        reflexivity.
      }

      vstep.

      apply eutt_Ret; split; [| split]; cbn.
      - (* TODO: add to solve_state_invariant *)
        do 3 (eapply state_invariant_same_Γ; [reflexivity | solve_not_in_gamma | ]).
        destruct PRE2.
        split; eauto.

        (* Solve memory invariant... *)
        cbn. cbn in mem_is_inv.
        intros n1 v0 τ x H H0.
        destruct x.
        { (* Global *)
          pose proof (dtyp_fits_allocated yFITS) as yALLOC.
          epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
          pose proof WRITE_SUCCEEDS as WRITE'.
          erewrite WRITE_ARRAY in WRITE_SUCCEEDS.


          assert (ID_Global id ≢ ID_Local vy_p) as IDNEQ by discriminate.
          destruct v0.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            cbn.
            destruct INV as (ptr_l & τ' & TYP & INLG' & READ').
            exists ptr_l. exists τ'.

            (* TODO: automate *)
            assert (fst ptr_l ≢ fst yptr).
            { eapply st_no_llvm_ptr_aliasing.
              5: eapply IDNEQ.
              eapply H.
              eapply Heqo0.
              all: eauto.
            }

            repeat (split; eauto).

            assert (fst yptr ≡ fst yptr') by (eapply handle_gep_addr_array_same_block; eauto).
            rewrite H2 in H1.
            eapply write_different_blocks; eauto.
            cbn. reflexivity.

            epose proof (IRState_is_WF _ n1 H) as (id' & N).
            rewrite H0 in N. inv N.
            cbn in H5. inversion H5.
            subst.
            eapply read_type in READ'.
            rewrite typ_to_dtyp_I.
            constructor.

            constructor.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            cbn.
            destruct INV as (ptr_l & τ' & TYP & INLG' & READ').
            exists ptr_l. exists τ'.

            (* TODO: automate *)
            assert (fst ptr_l ≢ fst yptr).
            { eapply st_no_llvm_ptr_aliasing.
              5: eapply IDNEQ.
              eapply H.
              eapply Heqo0.
              all: eauto.
            }

            repeat (split; eauto).

            assert (fst yptr ≡ fst yptr') by (eapply handle_gep_addr_array_same_block; eauto).
            rewrite H2 in H1.
            eapply write_different_blocks; eauto.
            cbn. reflexivity.

            epose proof (IRState_is_WF _ n1 H) as (id' & N).
            rewrite H0 in N. inv N.
            cbn in H5. inversion H5.
            subst.
            eapply read_type in READ'.
            rewrite typ_to_dtyp_D.
            constructor.
            constructor.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            destruct INV as (bk & ptr_l & τ' & MLUP & TYP & FITS & LOOKUP & GETCELL_ptr_l).

            destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
            { exists (mem_add (MInt64asNT.to_nat dst) v ymembk). exists ptr_l. exists τ'.

              subst.
              assert (n1 ≡ y_p) by eauto.
              rewrite yLU in MLUP.
              inv MLUP.

              repeat (split; eauto).
              - eapply memory_lookup_memory_set_eq.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.
                rewrite LUn0 in H0.
                inversion H0; subst.
            }
            { exists bk. exists ptr_l. exists τ'.
              repeat (split; eauto).
              - erewrite memory_lookup_memory_set_neq; eauto.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.

                assert (fst ptr_l ≢ fst yptr).
                { eapply st_no_llvm_ptr_aliasing.
                  5: eapply IDNEQ.
                  eapply H.
                  eapply Heqo0.
                  all: eauto.
                }

                erewrite write_array_cell_untouched_ptr_block; eauto.
                constructor.
            }
        }

        { (* Local *)
          destruct v0.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            eauto.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            eauto.
          - epose proof (mem_is_inv _ _ _ _ H H0) as INV.
            cbn in INV.
            destruct INV as (bk & ptr_l & τ' & MLUP & TYP & FITS & LOCALS & GETCELL_ptr_l).

            pose proof (dtyp_fits_allocated yFITS) as yALLOC.
            epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
            pose proof WRITE_SUCCEEDS as WRITE'.
            erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

            destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
            { exists (mem_add (MInt64asNT.to_nat dst) v ymembk). exists ptr_l. exists τ'.

              subst.
              assert (n1 ≡ y_p) by eauto.
              rewrite yLU in MLUP.
              inv MLUP.

              repeat (split; eauto).
              - eapply memory_lookup_memory_set_eq.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.
                rewrite LUn0 in H0.
                inversion H0; subst.

                rewrite yINLG in LOCALS.
                inversion LOCALS; subst.

                destruct (Nat.eq_dec (MInt64asNT.to_nat idx) (MInt64asNT.to_nat dst)) as [EQdst | NEQdst].
                + rewrite EQdst in *.
                  rewrite mem_lookup_mem_add_eq in H1; inv H1.

                  change (UVALUE_Double v0) with (dvalue_to_uvalue (DVALUE_Double v0)).
                  eapply write_array_cell_get_array_cell; eauto.
                  constructor.
                + rewrite mem_lookup_mem_add_neq in H1; inv H1; eauto.
                  erewrite write_array_cell_untouched; eauto.
                  constructor.
                  apply to_nat_unsigned; auto.
            }
            { exists bk. exists ptr_l. exists τ'.
              repeat (split; eauto).
              - erewrite memory_lookup_memory_set_neq; eauto.
              - eapply dtyp_fits_after_write; eauto.
              - intros idx v0 H1.
                destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
                + unfold Eqv.eqv, eqv_raw_id in EQid.
                  subst.

                  assert (n1 ≡ y_p) by (eapply no_id_aliasing_n_eq; eauto).
                  subst.
                  rewrite Heqo0 in H.
                  inversion H; subst; contradiction.
                + unfold Eqv.eqv, eqv_raw_id in NEQid.
                  assert (fst ptr_l ≢ fst yptr).
                  { assert (ID_Local id ≢ ID_Local vy_p) as NEQl.
                    { intros CONTRA. inv CONTRA. contradiction. }

                    (* May have to recover some things I rewrote / cbn'd *)
                    eapply st_no_llvm_ptr_aliasing.
                    5: eapply NEQl.
                    eapply H.
                    eapply Heqo0.
                    all:eauto.
                  }
                  erewrite write_array_cell_untouched_ptr_block; eauto.
                  constructor.
            }
        }

        { (* id_allocated *)
          unfold id_allocated in *.
          intros n1 addr0 val H.
          specialize (st_id_allocated n1). cbn in *.
          specialize (st_id_allocated _ _ H).
          eapply mem_block_exists_memory_set; eauto.
        }
      - exists bid_in. reflexivity.
      - assert (local_scope_modif s5 sf ρ l0); solve_local_scope_modif.
    }
  }
Qed.
