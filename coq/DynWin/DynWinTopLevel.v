From Coq Require Import ZArith Rdefinitions String.

From MathClasses Require Import interfaces.canonical_names.
From Flocq Require Import Binary Bits Core.Defs.

Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Tactics.StructTactics.
Require Import Helix.Tactics.HelixTactics.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.THCOL.

Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.

Require Import Helix.MSigmaHCOL.RasCT.
Require Import Helix.MSigmaHCOL.ReifySHCOL.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.MSigmaHCOL.ReifyProofs.
Require Import Helix.MSigmaHCOL.RasCarrierA.
Require Import Helix.MSigmaHCOL.MemSetoid.

Require Import Helix.RSigmaHCOL.ReifyProofs.
Require Import Helix.RSigmaHCOL.RSigmaHCOL.

Require Import Helix.FSigmaHCOL.FHCOLtoLFHCOL.
Require Import Helix.FSigmaHCOL.ReifyRHCOL.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.LazyFloat64asCT.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.

Require Import Helix.DynWin.DynWin.
Require Import Helix.DynWin.DynWinProofs.

(* TODO: move *)
Section FloatAux.

  Inductive is_NaN_64 : binary64 -> Prop :=
  | B754_nan_is_NaN_64 : forall s pl NPL,
      is_NaN_64 (@B754_nan _ _ s pl NPL).

  Definition le64 (a b : binary64) : Prop :=
    b64_compare a b ≡ Some Datatypes.Eq
    \/ b64_compare a b ≡ Some Datatypes.Lt.

  Definition lt64 (a b : binary64) : Prop :=
    b64_compare a b ≡ Some Datatypes.Lt.

  (* inclusive range check *)
  Definition in_range_64 : (binary64 * binary64) -> binary64 -> Prop
    := fun '(a,b) x => le64 a x /\ le64 x b.

  Lemma in_range_64_finite (lo hi x : binary64) :
    is_finite _ _ lo = true ->
    is_finite _ _ hi = true ->
    in_range_64 (lo, hi) x ->
    is_finite _ _ x = true.
  Proof.
    intros FL FH [LO HI].
    unfold le64 in *.
    destruct LO as [LEQ | LLT], HI as [HEQ | HLT].
    all: unfold b64_compare, Bcompare in *.
    all: repeat break_match; subst.
    all: try reflexivity.
    all: try congruence.
  Qed.

  (* left excluded, right included range check *)
  Definition in_range_64_l : (binary64 * binary64) -> binary64 -> Prop
    := fun '(a,b) x => lt64 a x /\ le64 x b.

  Definition b64_0_1   := b64_of_bits 1036831949%Z. (* 0.1 *)
  Definition b64_0_01  := b64_of_bits 1008981770%Z. (* 0.01 *)
  Definition b64_0     := b64_of_bits 0%Z.          (* 0.0 *)
  Definition b64_1     := b64_of_bits 1065353216%Z. (* 1.0 *)
  Definition b64_2     := b64_of_bits 1073741824%Z. (* 2.0 *)
  Definition b64_5     := b64_of_bits 1084227584%Z. (* 5.0 *)
  Definition b64_6     := b64_of_bits 1086324736%Z. (* 6.0 *)
  Definition b64_10    := b64_of_bits 1092616192%Z. (* 10.0 *)
  Definition b64_20    := b64_of_bits 1101004800%Z. (* 20.0 *)
  Definition b64_100   := b64_of_bits 1120403456%Z. (* 100.0 *)
  Definition b64_5000  := b64_of_bits 1167867904%Z. (* 5000.0 *)

End FloatAux.

Section RHCOL_to_FHCOL_bounds.

  (** Constraints on physical parameters **)
  (* Obstacle velocity constraint *)
  (* 0 <= V <= 20 (m/s) (<= 72 Kmh) *)
  Definition V_constr := (b64_0, b64_20).
  (* 1 < b <= 6 (m/s^2)
     https://copradar.com/chapts/references/acceleration.html *)
  Definition b_constr := (b64_1, b64_6).
  (* 0 <= A <= 5 (m/s^2)
     https://hypertextbook.com/facts/2001/MeredithBarricella.shtml *)
  Definition A_constr := (b64_0, b64_5).
  Definition e_constr := (b64_0_01, b64_0_1). (* 1/100 <= e <= 1/10. 10-100 Hz *)
  (* Constraints for obstacle and robot coordinates.
     Our robot operates on cartesian grid ~10x10 Km *)
  Definition x_constr := (b64_opp b64_5000, b64_5000).
  Definition y_constr := (b64_opp b64_5000, b64_5000).
  (* Robot velocity constraint *)
  Definition v_constr := (b64_0, b64_20).

  (*
    "a" layout:
     a0 = (A/b + 1.0) * ((A/2.0)*e*e + e*V)
     a1 = V/b + e*(A/b+1.0)
     a2 = 1.0/(2.0*b)

    "x" layout:
    0. robot velocity
    1. robot position (X)
    2. robot position (Y)
    3. obstacle position (X)
    4. obstacle position (Y)
   *)
  Definition make_a64 (V64 b64 A64 e64 : binary64) : FHCOL.mem_block :=
    let FT_div := b64_div FT_Rounding in (* DHCOL (and therefore CType) has no division *)
    let a0 :=
      MFloat64asCT.CTypeMult
        (MFloat64asCT.CTypePlus (FT_div A64 b64) b64_1)
        (MFloat64asCT.CTypePlus
           (MFloat64asCT.CTypeMult (MFloat64asCT.CTypeMult (FT_div A64 b64_2) e64) e64)
           (MFloat64asCT.CTypeMult e64 V64))
    in
    let a1 :=
      (MFloat64asCT.CTypePlus
         (FT_div V64 b64)
         (MFloat64asCT.CTypeMult
            e64
            (MFloat64asCT.CTypePlus (FT_div A64 b64) b64_1)))
    in
    let a2 :=
      FT_div
        b64_1
        (MFloat64asCT.CTypeMult b64_2 b64)
    in
    FHCOLEval.mem_add 0%nat a0
      (FHCOLEval.mem_add 1%nat a1
         (FHCOLEval.mem_add 2%nat a2
            (FHCOLEval.mem_empty))).

  Definition make_x64 (r_v_64 r_x_64 r_y_64 o_x_64 o_y_64 : binary64) : FHCOL.mem_block :=
    FHCOLEval.mem_add 0%nat r_v_64
      (FHCOLEval.mem_add 1%nat r_x_64
        (FHCOLEval.mem_add 2%nat r_y_64
          (FHCOLEval.mem_add 3%nat o_x_64
            (FHCOLEval.mem_add 4%nat o_y_64
              (FHCOLEval.mem_empty))))).

  (* Constraints on input memory blocks which we assume to prove
     numerical stability of FHCOL DynWin code.  Here, we enforce some
     reasonable numerical bounds on dynwin physical parameters.  *)
  Definition DynWinInConstr (a : RHCOLEval.mem_block) (x : RHCOLEval.mem_block): Prop
    :=
    exists V64 (* max obstacle speed *)
      b64 (* max braking *)
      A64 (* max accel *)
      e64 (* sampling period *)
      r_v_64
      r_x_64
      r_y_64
      o_x_64
      o_y_64,

      in_range_64 V_constr V64
      /\ in_range_64_l b_constr b64
      /\ in_range_64 A_constr A64
      /\ in_range_64 e_constr e64
      /\ heq_mem_block () () a (make_a64 V64 b64 A64 e64)
      /\ in_range_64 v_constr r_v_64
      /\ in_range_64 x_constr r_x_64
      /\ in_range_64 y_constr r_y_64
      /\ in_range_64 x_constr o_x_64
      /\ in_range_64 y_constr o_y_64
      /\ heq_mem_block () () x (make_x64 r_v_64 r_x_64 r_y_64 o_x_64 o_y_64).

  (* Parametric relation between RHCOL and FHCOL coumputation results  *)
  Definition DynWinOutRel
             (a_r:RHCOLEval.mem_block)
             (x_r:RHCOLEval.mem_block)
             (y_r:RHCOLEval.mem_block)
             (y_64:FHCOLEval.mem_block): Prop
    :=
    (* cast 64 bit output to 32 bit, simlating
       C/LLVM cast as in [cast64_to_32]
       result of the cast should be the same as
       32 bit approximation of result on Reals *)
    heq_mem_block () () y_r y_64.

  Global Instance DynWinOutRel_Proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (iff)) DynWinOutRel.
  Admitted.

End RHCOL_to_FHCOL_bounds.

Section TopLevel.

  (*
  (* User can specify optional constraints on input values and
     arguments. For example, for cyber-physical system it could
     include ranges and relatoin between parameters. *)
  Parameter InConstr: (* a *) RHCOLEval.mem_block -> (*x*) RHCOLEval.mem_block -> Prop.

  (* Parametric relation between RHCOL and FHCOL coumputation results  *)
  Parameter OutRel : (* a *) RHCOLEval.mem_block ->
                     (* x *) RHCOLEval.mem_block ->
                     (* y *) RHCOLEval.mem_block ->
                     (* y_mem *) FHCOLEval.mem_block -> Prop.
   *)

  Lemma DynWin_RHCOL_to_FHCOL_op_OK :
    exists r, RHCOLtoFHCOL.translate dynwin_RHCOL = inr r.
  Proof.
    cbn.

    assert (RF0 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeZero
                  ≡ @inr string _ Float64asCT.Float64Zero).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      all: clear - n; contradict n; reflexivity.
    }

    assert (RF1 : RHCOLtoFHCOL.translateCTypeConst MRasCT.CTypeOne
                  ≡ @inr string _ Float64asCT.Float64One).
    {
      unfold RHCOLtoFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      -
        clear - e.
        cbv in e.
        pose proof MRasCT.CTypeZeroOneApart.
        cbv in H.
        congruence.
      -
        clear - n0.
        contradict n0.
        reflexivity.
    }

    repeat progress (try setoid_rewrite RF0;
                     try setoid_rewrite RF1).
    now eexists.
  Qed.

  Lemma DynWin_LFHCOL_hard_OK :
    FHCOLtoLFHCOL.translate DynWin_FHCOL_hard ≡ inr DynWin_LFHCOL_hard.
  Proof.
    cbn.

    assert (FLF0 : FHCOLtoLFHCOL.translateCTypeConst MFloat64asCT.CTypeZero
                  ≡ @inr string _ MLazyFloat64asCT.CTypeZero).
    {
      unfold FHCOLtoLFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      all: clear - n; contradict n; reflexivity.
    }

    assert (FLF1 : FHCOLtoLFHCOL.translateCTypeConst MFloat64asCT.CTypeOne
                  ≡ @inr string _ MLazyFloat64asCT.CTypeOne).
    {
      unfold FHCOLtoLFHCOL.translateCTypeConst.
      repeat break_if; try reflexivity; exfalso.
      -
        clear - e.
        unfold MFloat64asCT.CTypeOne, MFloat64asCT.CTypeZero in e.
        pose proof MFloat64asCT.CTypeZeroOneApart.
        congruence.
      -
        clear - n0.
        contradict n0.
        reflexivity.
    }

    assert (I0 : FHCOLtoLFHCOL.translateNTypeConst Int64asNT.Int64_0
            ≡ inr Int64asNT.Int64_0) by reflexivity.
    assert (I1 : FHCOLtoLFHCOL.translateNTypeConst Int64asNT.Int64_1
            ≡ inr Int64asNT.Int64_1) by reflexivity.
    assert (I2 : FHCOLtoLFHCOL.translateNTypeConst Int64asNT.Int64_2
                 ≡ inr Int64asNT.Int64_2) by reflexivity.

    repeat progress (try setoid_rewrite FLF0;
                     try setoid_rewrite FLF1;
                     try setoid_rewrite I0;
                     try setoid_rewrite I1;
                     try setoid_rewrite I2).

    reflexivity.
  Qed.

  Require Import List.
  Import ListNotations.

  Section Symbolic_Execultion_Example.

    Definition i3 :=
      {| Int64asNT.Int64.intval := 3;
        Int64asNT.Int64.intrange := conj eq_refl eq_refl |}.
    Definition i5 :=
      {| Int64asNT.Int64.intval := 5;
        Int64asNT.Int64.intrange := conj eq_refl eq_refl |}.
    
    Definition dynwin_LF_σ := 
      [(LFHCOLEval.DSHPtrVal dynwin_a_addr i3, false);
       (LFHCOLEval.DSHPtrVal dynwin_y_addr Int64asNT.Int64_1, false); (* dynwin_i *)
       (LFHCOLEval.DSHPtrVal dynwin_x_addr i5, false)]. (* dynwin_o *)
    
    Definition a_mb :=
      LFHCOLEval.mem_add 0 (LFVar 0)
        (LFHCOLEval.mem_add 1 (LFVar 1)
           (LFHCOLEval.mem_add 2 (LFVar 2)
              LFHCOLEval.mem_empty)).
    
    Definition x_mb :=
      LFHCOLEval.mem_add 0 (LFVar 3)
        (LFHCOLEval.mem_add 1 (LFVar 4)
           (LFHCOLEval.mem_add 2 (LFVar 5)
              (LFHCOLEval.mem_add 3 (LFVar 6)
                 (LFHCOLEval.mem_add 4 (LFVar 7)
                    LFHCOLEval.mem_empty)))).
    
    Definition dynwin_LF_memory := 
      fun (a x : LFHCOLEval.mem_block) =>
        LFHCOLEval.memory_set
          (LFHCOLEval.memory_set
             (LFHCOLEval.memory_set LFHCOLEval.memory_empty
                dynwin_a_addr a)
             dynwin_x_addr x)
          dynwin_y_addr LFHCOLEval.mem_empty.
    
    Notation "0.0" := (B754_zero 53 1024 false).
    Notation "1.0" := (B754_finite 53 1024 false 4503599627370496 
                         (-52)
                         (binary_float_of_bits_aux_correct 52 11 eq_refl
                            eq_refl eq_refl 4607182418800017408)).

    (*
    Compute LFHCOLEval.evalDSHOperator
      dynwin_LF_σ
      DynWin_LFHCOL_hard
      (dynwin_LF_memory a_mb x_mb)
      (LFHCOLEval.estimateFuel DynWin_LFHCOL_hard).
     *)

  End Symbolic_Execultion_Example.

  Lemma RHCOL_to_FHCOL_numerical_correct
    (r_imemory r_omemory : RHCOLEval.memory)
    (a_rmem x_rmem y_rmem : RHCOLEval.mem_block)
    (f_imemory f_omemory : FHCOLEval.memory)
    (f_iσ : FHCOLEval.evalContext)
    (y_fmem : FHCOLEval.mem_block)
    (dynwin_FHCOL : FHCOLEval.DSHOperator)

    (R_EVAL : RHCOLEval.evalDSHOperator dynwin_R_σ dynwin_RHCOL r_imemory
                (RHCOLEval.estimateFuel dynwin_RHCOL)
              = Some (inr r_omemory))
    (A_RMEM : RHCOLEval.memory_lookup r_imemory dynwin_a_addr = Some a_rmem)
    (X_RMEM : RHCOLEval.memory_lookup r_imemory dynwin_x_addr = Some x_rmem)
    (Y_RMEM : RHCOLEval.memory_lookup r_omemory dynwin_y_addr = Some y_rmem)

    (F_EVAL : evalDSHOperator f_iσ dynwin_FHCOL f_imemory
                (FHCOLEval.estimateFuel dynwin_FHCOL)
              = Some (inr f_omemory))
    (Y_FMEM : memory_lookup f_omemory dynwin_y_addr = Some y_fmem)

    (TRANSLATE_OP : translate dynwin_RHCOL = inr dynwin_FHCOL)
    (RF_IM : heq_memory () () r_imemory f_imemory)
    (RF_IΣ : heq_evalContext () () dynwin_R_σ f_iσ)
    :
    DynWinInConstr a_rmem x_rmem ->
    DynWinOutRel a_rmem x_rmem y_rmem y_fmem.
  Proof.
  Admitted.

  (*
    Translation validation proof of semantic preservation
    of successful translation of [dynwin_orig] into FHCOL program.

    Using following definitons from DynWin.v:
     1. dynwin_i
     2. dynwin_o
     3. dynwin_orig

     And the following definition are produced with TemplateCoq:
     1. dynwin_RHCOL
   *)
  Theorem HCOL_to_FHCOL_Correctness (a: vector CarrierA 3):
    forall x y,
      (* evaluatoion of original operator *)
      dynwin_orig a x = y ->

      forall dynwin_F_memory dynwin_F_σ (dynwin_FHCOL:FHCOL.DSHOperator),
        (* Compile -> RHCOL -> FHCOL *)
        RHCOLtoFHCOL.translate dynwin_RHCOL = inr dynwin_FHCOL ->

        (* Equivalent inputs *)
        RHCOLtoFHCOL.heq_memory () () (dynwin_R_memory a x) dynwin_F_memory ->
        RHCOLtoFHCOL.heq_evalContext () () dynwin_R_σ dynwin_F_σ ->

        forall a_rmem x_rmem,
          RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_a_addr = Some a_rmem ->
          RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_x_addr = Some x_rmem ->
          DynWinInConstr a_rmem x_rmem ->

          (* Everything correct on Reals *)
          exists r_omemory y_rmem,
            RHCOLEval.evalDSHOperator
              dynwin_R_σ
              dynwin_RHCOL
              (dynwin_R_memory a x)
              (RHCOLEval.estimateFuel dynwin_RHCOL) = Some (inr r_omemory)
            /\ RHCOLEval.memory_lookup r_omemory dynwin_y_addr = Some y_rmem
            /\ ctvector_to_mem_block y = y_rmem

            (* And floats *)
            /\ exists f_omemory y_fmem,
              FHCOLEval.evalDSHOperator
                dynwin_F_σ dynwin_FHCOL
                dynwin_F_memory
                (FHCOLEval.estimateFuel dynwin_FHCOL) = (Some (inr f_omemory))
              /\ FHCOLEval.memory_lookup f_omemory dynwin_y_addr = Some y_fmem
              /\ DynWinOutRel a_rmem x_rmem y_rmem y_fmem.
  Proof.
    intros * HC * CR CRM CRE * RA RX INCONSTR.

    remember (RHCOLEval.memory_set
                (dynwin_R_memory a x)
                dynwin_y_addr
                (ctvector_to_mem_block y)) as r_omemory eqn:ROM.

    assert(RHCOLEval.evalDSHOperator
             dynwin_R_σ
             dynwin_RHCOL
             (dynwin_R_memory a x)
             (RHCOLEval.estimateFuel dynwin_RHCOL) = Some (inr r_omemory)) as RO.
    {
      pose proof (DynWin_MSH_DSH_compat a) as MRHCOL.
      pose proof (DynWin_pure) as MAPURE.
      pose proof (dynwin_SHCOL_MSHCOL_compat a) as MCOMP.
      pose proof (SHCOL_to_SHCOL1_Rewriting a) as SH1.
      pose proof (DynWinSigmaHCOL_Value_Correctness a) as HSH.
      pose proof (DynWinHCOL a x x) as HH.
      autospecialize HH; [reflexivity|].
      rewrite HC in HH. clear HC.

      (* moved from [dynwin_orig] to [dynwin_HCOL] *)

      remember (sparsify Monoid_RthetaFlags x) as sx eqn:SX.
      remember (sparsify Monoid_RthetaFlags y) as sy eqn:SY.
      assert(SHY: op _ (dynwin_SHCOL a) sx = sy).
      {
        subst sy.
        rewrite_clear HH.

        specialize (HSH sx sx).
        autospecialize HSH; [reflexivity|].
        rewrite <- HSH. clear HSH.
        unfold liftM_HOperator.
        Opaque dynwin_HCOL equiv.
        cbn.
        unfold SigmaHCOLImpl.liftM_HOperator_impl.
        unfold compose.
        f_equiv.
        subst sx.
        rewrite densify_sparsify.
        reflexivity.
      }
      Transparent dynwin_HCOL equiv.
      clear HH HSH.

      (* moved from [dynwin_HCOL] to [dynwin_SHCOL] *)

      assert(SH1Y: op _ (dynwin_SHCOL1 a) sx = sy).
      {
        rewrite <- SHY. clear SHY.
        destruct SH1.
        rewrite H.
        reflexivity.
      }
      clear SHY SH1.

      (* moved from [dynwin_SHCOL] to [dynwin_SHCOL1] *)

      assert(M1: mem_op (dynwin_MSHCOL1 a) (svector_to_mem_block Monoid_RthetaFlags sx) = Some (svector_to_mem_block Monoid_RthetaFlags sy)).
      {
        cut(Some (svector_to_mem_block Monoid_RthetaFlags (op Monoid_RthetaFlags (dynwin_SHCOL1 a) sx)) = mem_op (dynwin_MSHCOL1 a) (svector_to_mem_block Monoid_RthetaFlags sx)).
        {
          intros M0.
          rewrite <- M0. clear M0.
          apply Some_proper.

          cut(svector_is_dense _ (op Monoid_RthetaFlags (dynwin_SHCOL1 a) sx)).
          intros YD.

          apply svector_to_mem_block_dense_kind_of_proper.
          apply YD.

          subst sy.
          apply sparsify_is_dense.
          typeclasses eauto.

          apply SH1Y.

          {
            pose proof (@out_as_range _ _ _ _ _ _ (DynWinSigmaHCOL1_Facts a)) as D.
            specialize (D sx).

            autospecialize D.
            {
              intros j jc H.
              destruct (dynwin_SHCOL1 a).
              cbn in H.
              subst sx.
              rewrite Vnth_sparsify.
              apply Is_Val_mkValue.
            }

                unfold svector_is_dense.
            apply Vforall_nth_intro.
            intros i ip.
            apply D.
            cbn.
            constructor.
          }
        }
        {
          destruct MCOMP.
          apply mem_vec_preservation.
          cut(svector_is_dense Monoid_RthetaFlags (sparsify _ x)).
          intros SD.
          unfold svector_is_dense in SD.
          intros j jc H.
          apply (Vforall_nth jc) in SD.
          subst sx.
          apply SD.
          apply sparsify_is_dense.
          typeclasses eauto.
        }
      }
      clear SH1Y MCOMP.

      (* moved from [dynwin_SHCOL1] to [dynwin_MSHCOL1] *)

      remember (svector_to_mem_block Monoid_RthetaFlags sx) as mx eqn:MX.
      remember (svector_to_mem_block Monoid_RthetaFlags sy) as my eqn:MY.

      specialize (MRHCOL (ctvector_to_mem_block x)).
      replace (dynwin_memory a (ctvector_to_mem_block x))
        with (dynwin_R_memory a x) in MRHCOL by reflexivity.
      destruct MRHCOL as [MRHCOL].
      specialize (MRHCOL (ctvector_to_mem_block x) RHCOLEval.mem_empty).
      autospecialize MRHCOL.
      reflexivity.
      autospecialize MRHCOL.
      reflexivity.

      destruct_h_opt_opterr_c MM AE.
      -
        destruct s; inversion_clear MRHCOL.
        f_equiv; f_equiv.
        rename m0 into m'.
        destruct (lookup_PExpr dynwin_R_σ m' DSH_y_p) eqn:RY.
        +
          exfalso.
          clear - MAPURE AE RY.
          cbn in RY.
          assert (RHCOL.mem_block_exists 1 m').
          {
            erewrite <-mem_stable.
            2: now rewrite AE.
            now apply RHCOLEval.memory_is_set_is_Some.
          }
          apply RHCOLEval.memory_is_set_is_Some in H.
          unfold util.is_Some, RHCOLEval.memory_lookup_err in *.
          break_match; try contradiction.
          inv RY.
        +
          inversion_clear H.
          rename m into ym.
          rename m0 into ym'.
          subst.
          destruct (dynwin_MSHCOL1 a).
          rewrite 2!svector_to_mem_block_ctvector_to_mem_block
            in M1
              by typeclasses eauto.
          Opaque ctvector_to_mem_block.
          cbn in M1, MM.
          rewrite MM in M1.
          clear MM.
          some_inv.
          Transparent ctvector_to_mem_block.

          rewrite <-M1.
          assert (YM : ym = ym').
          {
            clear - H0.
            intros k.
            specialize (H0 k).
            cbn in H0.
            unfold RHCOL.mem_lookup in *.
            inv H0.
            -
              unfold util.is_None in *.
              now break_match.
            -
              symmetry; assumption.
          }
          rewrite YM.

          clear - AE RY MAPURE.
          destruct MAPURE as [_ MWS].
          cbn; cbn in RY.
          eapply memory_equiv_except_memory_set_inv.
          eapply MWS.
          now erewrite AE.
          now cbv.
          eapply RHCOLEval.memory_lookup_err_inr_Some.
          now rewrite RY.
      -
        exfalso.
        pose proof (@RHCOLEval.evalDSHOperator_estimateFuel dynwin_R_σ dynwin_RHCOL (dynwin_R_memory a x)) as CC.
        clear - CC AE.
        apply util.is_None_def in AE.
        generalize dependent (RHCOLEval.evalDSHOperator dynwin_R_σ dynwin_RHCOL
                                                        (dynwin_R_memory a x) (RHCOLEval.estimateFuel dynwin_RHCOL)).
        intros o AE CC.
        some_none.
      -
        exfalso.
        remember (dynwin_MSHCOL1 a) as m.
        destruct m.
        subst sx mx.
        rewrite svector_to_mem_block_ctvector_to_mem_block in M1.
        eq_to_equiv.
        some_none.
        typeclasses eauto.
      -
        exfalso.
        remember (dynwin_MSHCOL1 a) as m.
        destruct m.
        subst sx mx.
        rewrite svector_to_mem_block_ctvector_to_mem_block in M1.
        eq_to_equiv.
        some_none.
        typeclasses eauto.
    }

    (* moved from [dynwin_MSHCOL1] to [dynwin_rhcol] *)

    generalize dependent (ctvector_to_mem_block y).
    intros y_rmem R_OMEM.

    exists r_omemory.
    exists y_rmem.

    split; [assumption |].
    split.
    1: {
      rewrite R_OMEM.
      now rewrite memory_lookup_memory_set_eq by reflexivity.
    }
    split; [reflexivity |].

    pose proof
         RF_Structural_Semantic_Preservation
         dynwin_RHCOL
         dynwin_FHCOL
         (RHCOLEval.estimateFuel dynwin_RHCOL)
         (FHCOLEval.estimateFuel dynwin_FHCOL)
         dynwin_R_σ
         dynwin_F_σ
         (dynwin_R_memory a x)
         dynwin_F_memory
      as HEQRF.
    full_autospecialize HEQRF.
    {
      eapply RHCOLtoFHCOL.translation_syntax_always_correct.
      eapply RF_NTP.
      assumption.
    }
    {
      clear - CRE.
      induction CRE.
      -
        constructor.
      -
        constructor;
          [| apply IHCRE].
        unfold RHCOLtoFHCOL.heq_evalContextElem in *.
        repeat break_let; subst.
        repeat constructor.
        intuition.
        destruct H as [_ D].
        invc D; repeat constructor; assumption.
    }
    {
      clear - CRM.
      generalize dependent (dynwin_R_memory a x).
      clear.
      intros dynwin_R_memory M.

      intros k.
      specialize (M k).
      invc M; constructor.

      intros k'.
      specialize (H1 k').
      invc H1; constructor.
      constructor.
    }
    {
      eapply @RHCOLtoFHCOL_NExpr_closure_trace_equiv.
      assumption.
      clear - CRE.
      Set Printing All.
      eapply CRE.
    }

    subst r_omemory.
    destruct RHCOLEval.evalDSHOperator as [[e | r_omemory] |] eqn:RE in *;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.

    invc HEQRF; invc H1.
    rename b0 into f_omemory, H0 into F_EVAL, H2 into RF_OM.
    symmetry in RO, F_EVAL.

    exists f_omemory.

    unfold RHCOLEval.memory_set in RE.
    pose proof RF_OM as RF_YO.
    pose proof RO as R_YO.
    specialize (RF_YO dynwin_y_addr).
    specialize (R_YO dynwin_y_addr).
    unfold RHCOLEval.memory_set, RHCOLEval.memory_lookup in *.
    rewrite Memory.NP.F.add_eq_o in R_YO by reflexivity.

    invc RF_YO;
      [rewrite <-H0 in *; some_none |].
    rename b into y_fmem, H0 into Y_FMEM.
    rename a0 into y_rmem', H into Y_RMEM'.
    rename H1 into Y_RFE.
    symmetry in Y_RMEM', Y_FMEM.

    exists y_fmem.
    do 2 (split; [reflexivity |]).

    (* get rid of duplicate [y_rmem] *)
    rewrite Y_RMEM' in *.
    some_inv.
    rewrite R_YO.
    clear RO R_YO y_rmem.
    rename y_rmem' into y_rmem, Y_RMEM' into Y_RMEM.

    generalize dependent (dynwin_R_memory a x);
      intros r_imemory TRM A_RMEM X_RMEM R_EVAL.
    clear a x y HC.
    rename dynwin_F_memory into f_imemory, dynwin_F_σ into f_iσ.
    remember dynwin_R_σ as r_iσ.

    subst.

    eapply RHCOL_to_FHCOL_numerical_correct;
      try eassumption.
    now rewrite R_EVAL.
    now rewrite <-Y_RMEM.
    now rewrite F_EVAL.
    now rewrite <-Y_FMEM.
  Qed.

End TopLevel.
