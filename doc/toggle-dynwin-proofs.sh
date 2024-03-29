#!/usr/bin/env sh

DIFF_CONTENT=$(cat <<'EOF'
diff --git a/coq/DynWin/DynWinProofs.v b/coq/DynWin/DynWinProofs.v
index 285b9e98..49345e6e 100644
--- a/coq/DynWin/DynWinProofs.v
+++ b/coq/DynWin/DynWinProofs.v
@@ -67,7 +67,7 @@ Section HCOL_Breakdown.
   (* Initial HCOL breakdown proof *)
   Theorem DynWinHCOL:  forall (a: avector 3),
       dynwin_orig a = dynwin_HCOL a.
-  Proof.
+  Admitted. (* Proof.
     intros a.
     unfold dynwin_orig, dynwin_HCOL.
     rewrite breakdown_OTLess_Base.
@@ -78,7 +78,7 @@ Section HCOL_Breakdown.
     rewrite breakdown_OVMinus.
     rewrite breakdown_OTInfinityNorm.
     HOperator_reflexivity.
-  Qed.
+  Qed. *)
 
 
 End HCOL_Breakdown.
@@ -158,7 +158,7 @@ Section HCOL_to_SigmaHCOL.
     liftM_HOperator Monoid_RthetaFlags (dynwin_HCOL a)
     =
     dynwin_SHCOL a.
-  Proof.
+  Admitted. (* Proof.
     unfold dynwin_HCOL, dynwin_SHCOL.
     rewrite LiftM_Hoperator_compose.
     rewrite expand_HTDirectSum. (* this one does not work with Diamond_arg_proper *)
@@ -172,12 +172,12 @@ Section HCOL_to_SigmaHCOL.
     repeat rewrite <- SHCompose_assoc.
     reflexivity.
     Transparent SHCompose.
-  Qed.
+  Qed. *)
 
   Lemma DynWinSigmaHCOL_dense_input
         (a: avector 3)
     : Same_set _ (in_index_set _ (dynwin_SHCOL a)) (Full_set (FinNat _)).
-  Proof.
+  Admitted. (* Proof.
     split.
     -
       unfold Included.
@@ -201,12 +201,12 @@ Section HCOL_to_SigmaHCOL.
         unfold In.
         unfold index_map_range_set.
         repeat (destruct x; crush).
-  Qed.
+  Qed. *)
 
   Lemma DynWinSigmaHCOL_dense_output
         (a: avector 3)
     : Same_set _ (out_index_set _ (dynwin_SHCOL a)) (Full_set (FinNat _)).
-  Proof.
+  Admitted. (* Proof.
     split.
     -
       unfold Included.
@@ -220,7 +220,7 @@ Section HCOL_to_SigmaHCOL.
       unfold In in *.
       simpl.
       apply Full_intro.
-  Qed.
+  Qed. *)
 
   Fact two_index_maps_span_I_2
        (x : FinNat 2)
@@ -230,7 +230,7 @@ Section HCOL_to_SigmaHCOL.
       Union (@sig nat (fun x0 : nat => x0 < 2))
             (@index_map_range_set 1 2 (@h_index_map 1 2 1 1 b1))
             (@index_map_range_set 1 2 (@h_index_map 1 2 O 1 b2)) x.
-  Proof.
+  Admitted. (* Proof.
     let lu := fresh "LU" in
     let ru := fresh "RU" in
     match goal with
@@ -263,7 +263,7 @@ Section HCOL_to_SigmaHCOL.
         apply H.
       +
         crush.
-  Qed.
+  Qed. *)
 
   Fact two_h_index_maps_disjoint
        (m n: nat)
@@ -274,7 +274,7 @@ Section HCOL_to_SigmaHCOL.
       Disjoint (FinNat 2)
                (@index_map_range_set 1 2 (@h_index_map 1 2 m 1 b1))
                (@index_map_range_set 1 2 (@h_index_map 1 2 n 1 b2)).
-  Proof.
+  Admitted. (* Proof.
     apply Disjoint_intro.
     intros x.
     unfold not, In.
@@ -294,13 +294,13 @@ Section HCOL_to_SigmaHCOL.
     crush.
     crush.
     crush.
-  Qed.
+  Qed. *)
 
 
   Instance DynWinSigmaHCOL_Facts
            (a: avector 3):
     SHOperator_Facts _ (dynwin_SHCOL a).
-  Proof.
+  Admitted. (* Proof.
     unfold dynwin_SHCOL.
 
     (* First resolve all SHOperator_Facts typeclass instances *)
@@ -337,7 +337,7 @@ Section HCOL_to_SigmaHCOL.
       intros x H.
       apply Union_comm.
       apply two_index_maps_span_I_2.
-  Qed.
+  Qed. *)
 
 End HCOL_to_SigmaHCOL.
 
@@ -357,7 +357,7 @@ Section SigmaHCOL_rewriting.
   Instance DynWinSigmaHCOL1_Facts
            (a: avector 3):
     SHOperator_Facts _ (dynwin_SHCOL1 a).
-  Proof.
+  Admitted. (* Proof.
     unfold dynwin_SHCOL1.
     solve_facts.
     (* Now let's take care of remaining proof obligations *)
@@ -402,7 +402,7 @@ Section SigmaHCOL_rewriting.
       reflexivity.
 
       crush.
-  Qed.
+  Qed. *)
 
   Lemma op_Vforall_P_SHPointwise
         {m n: nat}
@@ -418,7 +418,7 @@ Section SigmaHCOL_rewriting.
                    (SHCompose fm
                               (SHPointwise (n:=n) fm (IgnoreIndex f))
                               F).
-  Proof.
+  Admitted. (* Proof.
     intros H.
     unfold op_Vforall_P.
     intros x.
@@ -436,13 +436,13 @@ Section SigmaHCOL_rewriting.
     rewrite evalWriter_Rtheta_liftM.
     unfold IgnoreIndex, const.
     apply H.
-  Qed.
+  Qed. *)
 
   (* Sigma-HCOL rewriting correctenss *)
   Lemma DynWinSigmaHCOL1_Value_Correctness
         (a: avector 3)
     : dynwin_SHCOL a = dynwin_SHCOL1 a.
-  Proof.
+  Admitted. (* Proof.
     unfold dynwin_SHCOL.
     unfold SumSparseEmbedding.
 
@@ -665,7 +665,7 @@ Section SigmaHCOL_rewriting.
            end.
     replace p with p1 by apply proof_irrelevance.
     reflexivity.
-  Qed.
+  Qed. *)
 
 
   (* Couple additional structual properties: input and output of the
@@ -673,7 +673,7 @@ Section SigmaHCOL_rewriting.
   Lemma DynWinSigmaHCOL1_dense_input
         (a: avector 3)
     : Same_set _ (in_index_set _ (dynwin_SHCOL1 a)) (Full_set (FinNat _)).
-  Proof.
+  Admitted. (* Proof.
     split.
     -
       unfold Included.
@@ -739,12 +739,12 @@ Section SigmaHCOL_rewriting.
       compute in xc.
       exfalso.
       lia.
-  Qed.
+  Qed. *)
 
   Lemma DynWinSigmaHCOL1_dense_output
         (a: avector 3)
     : Same_set _ (out_index_set _ (dynwin_SHCOL1 a)) (Full_set (FinNat _)).
-  Proof.
+  Admitted. (* Proof.
     split.
     -
       unfold Included.
@@ -758,7 +758,7 @@ Section SigmaHCOL_rewriting.
       unfold In in *.
       simpl.
       apply Full_intro.
-  Qed.
+  Qed. *)
 
   (* Putting it all together: Final proof of SigmaHCOL rewriting which
    includes both value and structual correctenss *)
@@ -770,7 +770,7 @@ Section SigmaHCOL_rewriting.
         (dynwin_SHCOL a)
         (DynWinSigmaHCOL1_Facts _)
         (DynWinSigmaHCOL_Facts _).
-  Proof.
+  Admitted. (* Proof.
     split.
     -
       symmetry.
@@ -796,7 +796,7 @@ Section SigmaHCOL_rewriting.
         rewrite E, E1.
         unfold Same_set.
         split; unfold Included; auto.
-  Qed.
+  Qed. *)
 
 End SigmaHCOL_rewriting.
 
@@ -818,7 +818,7 @@ Section SHCOL_to_MSHCOL.
     Included (FinNat 2) (Full_set (FinNat 2))
              (Union (FinNat 2) (singleton 1)
                     (Union (FinNat 2) (singleton 0) (Empty_set (FinNat 2)))).
-  Proof.
+  Admitted. (* Proof.
 
     unfold Included, In.
     intros [x xc] _.
@@ -835,7 +835,7 @@ Section SHCOL_to_MSHCOL.
         reflexivity.
       *
         crush.
-  Qed.
+  Qed. *)
 
   Fact Apply_Family_Vforall_ATT
         {fm}
@@ -843,18 +843,18 @@ Section SHCOL_to_MSHCOL.
         {svalue: CarrierA}
         (op_family: @SHOperatorFamily _ fm i o n svalue):
     Apply_Family_Vforall_P fm (liftRthetaP (ATT CarrierA)) op_family.
-  Proof.
+  Admitted. (* Proof.
     intros x j jc.
     apply Vforall_intro.
     intros y H.
     unfold liftRthetaP.
     cbv;tauto.
-  Qed.
+  Qed. *)
 
 
   Theorem dynwin_SHCOL_MSHCOL_compat (a: avector 3):
     SH_MSH_Operator_compat (dynwin_SHCOL1 a) (dynwin_MSHCOL1 a).
-  Proof.
+  Admitted. (* Proof.
     unfold dynwin_SHCOL1, dynwin_MSHCOL1.
     unfold ISumUnion.
 
@@ -906,7 +906,7 @@ Section SHCOL_to_MSHCOL.
       apply Set_Obligation_1.
     -
       apply Set_Obligation_1.
-  Qed.
+  Qed. *)
 
 End SHCOL_to_MSHCOL.
 
@@ -914,14 +914,14 @@ End SHCOL_to_MSHCOL.
 Lemma memory_lookup_not_next_equiv {m k v}:
   RHCOLEval.memory_lookup m k = Some v ->
   k ≢ RHCOLEval.memory_next_key m.
-Proof.
+Admitted. (* Proof.
   intros H.
   destruct (eq_nat_dec k (RHCOLEval.memory_next_key m)) as [E|NE]; [exfalso|auto].
   rewrite E in H. clear E.
   pose proof (RHCOLEval.memory_lookup_memory_next_key_is_None m) as N.
   unfold util.is_None in N.
   break_match_hyp; [trivial|some_none].
-Qed.
+Qed. *)
 
 Section MSHCOL_to_RHCOL.
 
@@ -992,10 +992,10 @@ Section MSHCOL_to_RHCOL.
   Instance DynWin_pure
     :
       DSH_pure (DynWin_RHCOL) DSH_y_p.
-  Proof.
+  Admitted. (* Proof.
     unfold DynWin_RHCOL, DSH_y_p, DSH_x_p.
     solve_MSH_DSH_compat.
-  Qed.
+  Qed. *)
 
   Section DummyEnv.
 
@@ -1037,7 +1037,7 @@ Section MSHCOL_to_RHCOL.
                         dynwin_R_memory
                         DSH_x_p DSH_y_p
                         DynWin_pure.
-    Proof.
+    Admitted. (* Proof.
       unfold DynWin_RHCOL, DSH_y_p, DSH_x_p.
       unfold dynwin_x_addr, dynwin_y_addr, dynwin_a_addr, nglobals in *.
       unfold dynwin_MSHCOL1.
@@ -1442,7 +1442,7 @@ Section MSHCOL_to_RHCOL.
         -
           solve_facts.
       }
-    Qed.
+    Qed. *)
 
   End DummyEnv.
 
@@ -1459,7 +1459,7 @@ Section RCHOL_to_FHCOL.
      [DynWin.v]. See also [DynWin_FHCOL_hard_check] *)
   Fact DynWin_FHCOL_hard_check :
     RHCOLtoFHCOL.translate DynWin_RHCOL ≡ inr DynWin_FHCOL_hard.
-  Proof.
+  Admitted. (* Proof.
     cbn.
 
     assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
@@ -1491,7 +1491,7 @@ Section RCHOL_to_FHCOL.
                      try setoid_rewrite RF1).
 
     reflexivity.
-  Qed.
+  Qed. *)
 
   (* note: the two [try] blocks are for RHCOL/FHCOL lemma *)
   Ltac destruct_context_range_lookup ΣR x :=
@@ -1527,7 +1527,7 @@ Section RCHOL_to_FHCOL.
          (FHCOLEval.intervalEvalDSHOperator_σ
             dynwin_F_σ dynwin_FHCOL []
             (FHCOLEval.estimateFuel dynwin_FHCOL)).
-  Proof.
+  Admitted. (* Proof.
     intros RF RFΣ.
 
     assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
@@ -1733,7 +1733,7 @@ Section RCHOL_to_FHCOL.
         with (Z.of_nat nv1)
         by (now unfold Int64.unsigned).
       crush_int.
-  Qed.
+  Qed. *)
 
 End RCHOL_to_FHCOL.
 
@@ -1741,13 +1741,13 @@ Section hardcoded.
 
   Fact DynWin_RHCOL_hard_OK :
     DynWin_RHCOL ≡ DynWin_RHCOL_hard.
-  Proof.
+  Admitted. (* Proof.
     reflexivity.
-  Qed.
+  Qed. *)
 
   Fact DynWin_FHCOL_hard_OK :
     RHCOLtoFHCOL.translate DynWin_RHCOL ≡ inr DynWin_FHCOL_hard.
-  Proof.
+  Admitted. (* Proof.
     cbn.
 
     assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
@@ -1779,11 +1779,11 @@ Section hardcoded.
                      try setoid_rewrite RF1).
 
     reflexivity.
-  Qed.
+  Qed. *)
 
   Fact DynWin_SRHCOL_hard_OK :
     RHCOLtoSRHCOL.translate DynWin_RHCOL_hard ≡ inr DynWin_SRHCOL_hard.
-  Proof.
+  Admitted. (* Proof.
     cbn.
     assert (RLR0 : RHCOLtoSRHCOL.translateCTypeConst MRasCT.CTypeZero
                   ≡ @inr string _ MSymbolicCT.CTypeZero).
@@ -1813,11 +1813,11 @@ Section hardcoded.
                      try setoid_rewrite RLR1).
 
     reflexivity.
-  Qed.
+  Qed. *)
 
   Fact DynWin_SFHCOL_hard_OK :
     FHCOLtoSFHCOL.translate DynWin_FHCOL_hard ≡ inr DynWin_SFHCOL_hard.
-  Proof.
+  Admitted. (* Proof.
     cbn.
 
     assert (FLF0 : FHCOLtoSFHCOL.translateCTypeConst MFloat64asCT.CTypeZero
@@ -1858,7 +1858,7 @@ Section hardcoded.
                      try setoid_rewrite I2).
 
     reflexivity.
-  Qed.
+  Qed. *)
 
 End hardcoded.
 
@@ -1882,11 +1882,11 @@ Section CType_impl.
 
   Global Instance CType_impl_proper :
     Proper ((=) ==> (=) ==> (iff)) CType_impl.
-  Proof.
+  Admitted. (* Proof.
     intros x1 x2 X y1 y2 Y.
     invc X; invc Y.
     tauto.
-  Qed.
+  Qed. *)
 
   Fact CType_impl_dec :
     forall p q,
@@ -1894,7 +1894,7 @@ Section CType_impl.
       ({q ≡ MRasCT.CTypeZero} + {q ≡ MRasCT.CTypeOne}) ->
       (float_as_bool p false -> R_as_bool q false) <->
       (R_as_bool q true -> float_as_bool p true).
-  Proof.
+  Admitted. (* Proof.
     intros * PD QD.
     destruct PD, QD; subst.
     all: split; intros.
@@ -1913,11 +1913,11 @@ Section CType_impl.
       invc H.
     -
       invc H0.
-  Qed.
+  Qed. *)
 
   Lemma R_as_bool_Zless (a b : R) :
     R_as_bool (MRasCT.CTypeZLess a b) true <-> a < b.
-  Proof.
+  Admitted. (* Proof.
     unfold MRasCT.CTypeZLess, Zless, CarrierAltdec, CarrierDefs_R.
     break_if; cbv; split; try tauto.
     constructor.
@@ -1925,19 +1925,19 @@ Section CType_impl.
     invc C.
     cbv in H0.
     lra.
-  Qed.
+  Qed. *)
 
   Lemma float_as_bool_Zless (a b : Bits.binary64) :
     float_as_bool (MFloat64asCT.CTypeZLess a b) true
     <->
     safe_lt64 FT_Rounding DynWin_CompareEpsilon.compare_epsilon a b.
-  Proof.
+  Admitted. (* Proof.
     unfold MFloat64asCT.CTypeZLess, MFloat64asCT.CTypeSub,
       Zless, safe_lt64, lt64, Bits.b64_compare.
     repeat break_match.
     all: split; intros; subst.
     all: invc H.
     all: constructor.
-  Qed.
+  Qed. *)
 
 End CType_impl.
diff --git a/coq/DynWin/DynWinTopLevel.v b/coq/DynWin/DynWinTopLevel.v
index 5231794b..e77ee4c6 100644
--- a/coq/DynWin/DynWinTopLevel.v
+++ b/coq/DynWin/DynWinTopLevel.v
@@ -180,7 +180,7 @@ Section RHCOL_to_FHCOL_bounds.
 
   Global Instance DynWinOutRel_Proper :
     Proper ((=) ==> (=) ==> (=) ==> (=) ==> (iff)) DynWinOutRel.
-  Proof.
+  Admitted. (* Proof.
     intros a1 a2 A x1 x2 X y1 y2 Y y64_1 y64_2 Y64.
     unfold DynWinOutRel.
     clear - Y Y64.
@@ -188,7 +188,7 @@ Section RHCOL_to_FHCOL_bounds.
     specialize (Y64 dynwin_y_offset).
     rewrite Y, Y64.
     tauto.
-  Qed.
+  Qed. *)
 
 End RHCOL_to_FHCOL_bounds.
 
@@ -345,7 +345,7 @@ Section Gappa.
     (POLY : poly ≡ a0 + vr * a1 + vr * vr * a2)
     :
     B64R compare_epsilon < ◻ (cheb64 - poly64) -> (poly < cheb)%R.
-  Proof.
+  Admitted. (* Proof.
     intros LT64.
     (* 1b-40 *)
     pose (cheb_delta := B64R (
@@ -416,7 +416,7 @@ Section Gappa.
     clear CU LT64.
 
     gappa_crush.
-  Qed.
+  Qed. *)
 
   Close Scope R_scope.
   
@@ -469,7 +469,7 @@ Section Gappa.
            (MRasCT.CTypeMax MRasCT.CTypeZero
               (MRasCT.CTypeAbs (MRasCT.CTypeSub (B64R fx1) (B64R fx3))))
            (MRasCT.CTypeAbs (MRasCT.CTypeSub (B64R fx2) (B64R fx4))))%R.
-  Proof.
+  Admitted. (* Proof.
     rewrite !fmaxZeroAbs, !R_MaxZeroAbs, !R_PlusZeroLeft, !R_MultOneLeft in *.
 
     autounfold with unfold_RCT.
@@ -588,7 +588,7 @@ Section Gappa.
        but that encounters an anomaly *)
     Unshelve.
     all: crush_floats.
-  Qed.
+  Qed. *)
 
 End Gappa.
 
@@ -712,7 +712,7 @@ Section DynWin_Symbolic.
           end
       | _ => None
       end.
-  Proof.
+  Admitted. (* Proof.
     intros Σ M OP RE MB.
     pose proof RHCOLtoSRHCOL_semantic_preservation
       r_op sr_op
@@ -749,7 +749,7 @@ Section DynWin_Symbolic.
     reflexivity.
     rewrite H4.
     reflexivity.
-  Qed.
+  Qed. *)
 
   (* TODO: this is exactly the same as the above *)
   Lemma FHCOL_to_symbolic_lookup
@@ -789,7 +789,7 @@ Section DynWin_Symbolic.
           end
       | _ => None
       end.
-  Proof.
+  Admitted. (* Proof.
     intros Σ M OP RE MB.
     pose proof FHCOLtoSFHCOL_semantic_preservation
       r_op sr_op
@@ -826,7 +826,7 @@ Section DynWin_Symbolic.
     reflexivity.
     rewrite H4.
     reflexivity.
-  Qed.
+  Qed. *)
 
   (* For some reason the lhs of this
      doesn't [cbn/cbv/etc], but easily [Compute]s *)
@@ -854,9 +854,9 @@ Section DynWin_Symbolic.
               (SMult (SMult (SMult SConstOne (SVar 3)) (SVar 3)) (SVar 2)))
            (SMax (SMax SConstZero (SAbs (SSub (SVar 4) (SVar 6))))
               (SAbs (SSub (SVar 5) (SVar 7))))).
-  Proof.
+  Admitted. (* Proof.
     reflexivity.
-  Qed.
+  Qed. *)
 
   Lemma RHCOL_to_FHCOL_numerical_correct
     (r_omemory : RHCOLEval.memory)
@@ -884,7 +884,7 @@ Section DynWin_Symbolic.
     :
     DynWinInConstr a_rmem x_rmem ->
     DynWinOutRel a_rmem x_rmem y_rmem y_fmem.
-  Proof.
+  Admitted. (* Proof.
     intros INCONSTR.
     unfold DynWinOutRel.
 
@@ -1211,7 +1211,7 @@ Section DynWin_Symbolic.
     eapply oxC.
     eapply oyC.
     all: assumption.
-  Qed.
+  Qed. *)
 
 End DynWin_Symbolic.
 
@@ -1263,7 +1263,7 @@ Theorem HCOL_to_FHCOL_Correctness (a: vector CarrierA 3):
               (FHCOLEval.estimateFuel dynwin_FHCOL) = (Some (inr f_omemory))
             /\ FHCOLEval.memory_lookup f_omemory dynwin_y_addr = Some y_fmem
             /\ DynWinOutRel a_rmem x_rmem y_rmem y_fmem.
-Proof.
+Admitted. (* Proof.
   intros * HC * CR CRM CRE * RA RX INCONSTR.
 
   remember (RHCOLEval.memory_set
@@ -1602,4 +1602,4 @@ Proof.
   now rewrite <-Y_RMEM.
   now rewrite F_EVAL.
   now rewrite <-Y_FMEM.
-Qed.
+Qed. *)
EOF
)

# Ensure a newline at the end of the diff
DIFF_CONTENT="${DIFF_CONTENT}
"

# Check if the diff has been applied
if printf %s "$DIFF_CONTENT" | git apply --check --reverse 2>/dev/null; then
    # The diff has been applied, so unapply it
    echo "Uncommenting proofs... (unapplying diff)"
    printf %s "$DIFF_CONTENT" | git apply --reverse
else
    # The diff hasn't been applied, so apply it
    echo "Commenting out proofs... (applying diff)"
    printf %s "$DIFF_CONTENT" | git apply
fi
