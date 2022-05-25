From Coq Require Import ZArith Rdefinitions String Psatz List.
From ExtLib Require Import Monad.
From MathClasses Require Import interfaces.canonical_names.
From Flocq Require Import Binary Bits Core.Defs.

Require Import Gappa.Gappa_tactic.

Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.FloatUtil.
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

Require Import Helix.FSigmaHCOL.ReifyRHCOL.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.

Require Import Helix.SymbolicDHCOL.SymbolicCT.
Require Import Helix.SymbolicDHCOL.RHCOLtoSRHCOL.
Require Import Helix.SymbolicDHCOL.FHCOLtoSFHCOL.

Require Import Helix.DynWin.DynWin.
Require Import Helix.DynWin.DynWinProofs.

Import ListNotations.
Import MonadNotation.

Section RHCOL_to_FHCOL_bounds.

  Open Scope R_scope.

  (* The memory cell in which the boolean output is written by DynWin *)
  Definition dynwin_y_offset := 0%nat.

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
    (* DHCOL (and therefore CType) has no division *)
    let FT_div := b64_div FT_Rounding in

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
      /\ in_range_64 b_constr b64
      /\ in_range_64 A_constr A64
      /\ in_range_64 e_constr e64
      /\ RHCOLtoFHCOL.heq_mem_block () RF_CHE
          a (make_a64 V64 b64 A64 e64)
      /\ in_range_64 v_constr r_v_64
      /\ in_range_64 x_constr r_x_64
      /\ in_range_64 y_constr r_y_64
      /\ in_range_64 x_constr o_x_64
      /\ in_range_64 y_constr o_y_64
      /\ RHCOLtoFHCOL.heq_mem_block () RF_CHE
          x (make_x64 r_v_64 r_x_64 r_y_64 o_x_64 o_y_64).

  (* Parametric relation between RHCOL and FHCOL coumputation results  *)
  (*
    Requisite relation:

     Binary64 out | Real out ||  Status
     -------------------------------------
     Safe         | Safe     ||  OK        (agreeing)
     Safe         | Unsafe   ||  FORBIDDEN (dangerous in reality, "safe" in 64)
     Unsafe       | Safe     ||  OK        (overly cautious)
     Unsafe       | Unsafe   ||  OK        (agreeing)

     in boolean terms, given "Safe" = true, "Unsafe" = false,
     this is

     [Binary64 out] => [Real out]

     (alternatively "Real = safe \/ Binary64 = unsafe")
   *)
  Definition DynWinOutRel
             (a_r:RHCOLEval.mem_block)
             (x_r:RHCOLEval.mem_block)
             (y_r:RHCOLEval.mem_block)
             (y_64:FHCOLEval.mem_block): Prop
    :=
    hopt_r (flip CType_impl)
      (RHCOLEval.mem_lookup dynwin_y_offset y_r)
      (FHCOLEval.mem_lookup dynwin_y_offset y_64).

  Global Instance DynWinOutRel_Proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (iff)) DynWinOutRel.
  Proof.
    intros a1 a2 A x1 x2 X y1 y2 Y y64_1 y64_2 Y64.
    unfold DynWinOutRel.
    clear - Y Y64.
    specialize (Y dynwin_y_offset).
    specialize (Y64 dynwin_y_offset).
    rewrite Y, Y64.
    tauto.
  Qed.

End RHCOL_to_FHCOL_bounds.

Section Gappa.

  Open Scope Float64asCT_scope.

  Hint Rewrite
    b64_plus_to_R b64_minus_to_R
    b64_mult_to_R b64_div_to_R
    b64_max_to_R b64_abs_to_R

    b64_plus_finite b64_minus_finite
    b64_mult_finite b64_div_finite
    b64_max_finite b64_abs_finite
    : rewrite_to_R.

  Ltac not_known A :=
    match goal with
    | H : A |- _ => fail 1 "Assertion" A "already known in" H
    | _ => idtac
    end.
  
  Ltac assert_if_new_as Name H :=
    not_known H; assert (Name : H).

  Ltac known_finite x :=
    match goal with
    | [H : is_finite _ _ x ≡ true |- _] => idtac
    | _ => fail 1
    end.

  Ltac rewrite_to_R :=
    autounfold with unfold_FCT;
    autorewrite with rewrite_to_R;
    try assumption.
    
  Ltac gappa_form :=
    try apply bpow_lt_to_le;
    repeat (cbv [Defs.F2R IZR IPR IPR_2 Z.pow_pos Pos.iter] in *;
            simpl in *).

  Ltac simple_R :=
    match goal with
    | |- B2R _ _ (B754_finite _ _ _ _ _ _) ≢ 0%R => cbv; lra
    end.

  Ltac gappa_crush :=
    rewrite_to_R;
    autounfold with sugar64 F64_const in *;
    try simple_R;
    gappa_form;
    gappa.

  (* Extra safe match to avoid unnecessarily calling the heavy [gappa_crush] *)
  Ltac solve_with_gappa :=
    match goal with
    | |- no_overflow64 _ => gappa_crush
    | |- _ ≢ 0%R => gappa_crush
    | |- context [Rmax] => unfold Rmax; break_match_goal; gappa_crush
    end.

  Ltac crush_floats :=
    first
      [ assumption
      | reflexivity
      | eapply in_range_finite; eassumption
      | eapply in_range_l_finite; eassumption
      | rewrite_to_R; solve_with_gappa].

  Ltac assert_finite :=
    let FIN := fresh "FIN" in
    match goal with
    | [H : in_range_64 _ ?x |- _] =>
        assert_if_new_as FIN (is_finite _ _ x ≡ true)
    | [H : in_range_64_l _ ?x |- _] =>
        assert_if_new_as FIN (is_finite _ _ x ≡ true)
    | [H : context [?x ⊞ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as FIN (is_finite _ _ (x ⊞ y) ≡ true)
    | [H : context [?x ⊟ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as FIN (is_finite _ _ (x ⊟ y) ≡ true)
    | [H : context [?x ⊠ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as FIN (is_finite _ _ (x ⊠ y) ≡ true)
    | [H : context [?x ⧄ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as FIN (is_finite _ _ (x ⧄ y) ≡ true)
    | [H : context [fabs ?x] |- _] =>
        known_finite x;
        assert_if_new_as FIN (is_finite _ _ (fabs x) ≡ true)
    | [H : context [fmax ?x ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as FIN (is_finite _ _ (fmax x y) ≡ true)
    end.

  Ltac assert_no_overflow :=
    let NOVF := fresh "NOVF" in
    match goal with
    | [H : context [?x ⊞ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as NOVF
          (no_overflow64 (◻ (B64R x + B64R y)))
    | [H : context [?x ⊟ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as NOVF
          (no_overflow64 (◻ (B64R x - B64R y)))
    | [H : context [?x ⊠ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as NOVF
          (no_overflow64 (◻ (B64R x * B64R y)))
    | [H : context [?x ⧄ ?y] |- _] =>
        known_finite x; known_finite y;
        assert_if_new_as NOVF
          (no_overflow64 (◻ (B64R x / B64R y)))
    end.

  Ltac assert_divisor_nz :=
    let NZ := fresh "NZ" in
    match goal with
    | [H : context [?x ⧄ ?y] |- _] =>
        known_finite y;
        assert_if_new_as NZ (B64R y ≢ 0%R)
    end.

  Ltac assert_next :=
    first [assert_divisor_nz | assert_no_overflow | assert_finite].

  Open Scope R_scope.

  Lemma DynWin_arith
    (e a b vr vo a0 a1 a2 rx ry ox oy cheb64 poly64 cheb poly : R)
    (E : B64R b64_0_01 <= e <= B64R b64_0_1)
    (A : B64R b64_0 <= a <= B64R b64_5)
    (B : B64R b64_1 <= b <= B64R b64_6)
    (VR : B64R b64_0 <= vr <= B64R b64_20)
    (VO : B64R b64_0 <= vo <= B64R b64_20)
    (RX : B64R (b64_opp b64_5000) <= rx <= B64R b64_5000)
    (RY : B64R (b64_opp b64_5000) <= ry <= B64R b64_5000)
    (OX : B64R (b64_opp b64_5000) <= ox <= B64R b64_5000)
    (OY : B64R (b64_opp b64_5000) <= oy <= B64R b64_5000)
    (A0 : a0 ≡ ◻ (◻ (◻ (a / b) + B64R b64_1) *
                    ◻ (◻ (◻ (◻ (a / B64R b64_2) * e) * e) + ◻ (e * vo))))
    (A1 : a1 ≡ ◻ (◻ (vo / b) + ◻ (e * ◻ (◻ (a / b) + B64R b64_1))))
    (A2 : a2 ≡ ◻ (B64R b64_1 / ◻ (B64R b64_2 * b)))
    (CHEB64 : cheb64 ≡ Rmax (Rabs ◻ (rx - ox)) (Rabs ◻ (ry - oy)))
    (POLY64 : poly64 ≡ ◻ (◻ (◻ (B64R b64_0 + ◻ (B64R b64_1 * a0)) +
                               ◻ (◻ (B64R b64_1 * vr) * a1)) +
                            ◻ (◻ (◻ (B64R b64_1 * vr) * vr) * a2)))
    (CHEB : cheb ≡ Rmax (Rabs (ox - rx)) (Rabs (oy - ry)))
    (* TODO: this ([CU]) upper bound shouldn't be necessary here *)
    (CU : no_overflow64 ◻ (cheb64 - poly64)) 
    (POLY : poly ≡ a0 + vr * a1 + vr * vr * a2)
    :
    B64R epsilon < ◻ (cheb64 - poly64) -> (poly < cheb)%R.
  Proof.
    intros LT64.
    (* 1b-40 *)
    pose (cheb_delta := B64R (
            B754_finite 53 1024 false 4503599627370496 (-92)
              (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
                 4427038433705197568))).

    assert (CHEB_DELTA : - cheb_delta <= cheb64 - cheb <= cheb_delta).
    {
      clear - RX RY OX OY CHEB CHEB64.
      subst.

      replace cheb_delta with (Rmax cheb_delta cheb_delta)
        by (unfold Rmax; break_if; reflexivity).

      eapply Rmax_no_error.
      -
        replace (Rabs (ox - rx)) with (Rabs (rx - ox))
          by (unfold Rabs; repeat break_if; lra).
        eapply Rabs_no_error.
        subst cheb_delta.
        gappa_crush.
      -
        replace (Rabs (oy - ry)) with (Rabs (ry - oy))
          by (unfold Rabs; repeat break_if; lra).
        eapply Rabs_no_error.
        subst cheb_delta.
        gappa_crush.
    }
    clear CHEB CHEB64.

    pose (poly_delta :=
            B64R (B754_finite 53 1024 false 5665758678918104 (-94)
                    (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
                       4419193393502004184))).

    assert (POLY_DELTA : - poly_delta <= poly64 - poly <= poly_delta).
    {
      clear LT64 CHEB_DELTA.
      subst cheb_delta poly_delta.
      replace (B64R b64_0) with 0 in * by reflexivity.
      replace (B64R b64_1) with 1 in * by (cbv; lra).
      repeat match goal with
             | [H : context [0 + ?x] |- _] =>
                 replace (0 + x) with x in * by lra
             | [H : context [1 * ?x] |- _] =>
                 replace (1 * x) with x in * by lra
             end.
      
      gappa_crush.
    }

    clear - LT64 CU CHEB_DELTA POLY_DELTA.
    subst cheb_delta poly_delta.
    apply RIneq.Rlt_le in LT64.
    enough (E : B64R float64_subnormal_eps <=
                  cheb - poly
                <= 2 * Raux.bpow radix2 1024)
      by (cbv in E; lra).

    assert (BND64 : B64R epsilon <= ◻ (cheb64 - poly64) <= Raux.bpow radix2 1024).
    {
      clear - CU LT64.
      split; [assumption |].
      unfold no_overflow64, Rabs in *.
      break_if; lra.
    }
    clear CU LT64.

    gappa_crush.
  Qed.

  Close Scope R_scope.
  
  Lemma DynWin_numerical_stability
    (V64 b64 A64 e64 v64 rx64 ry64 ox64 oy64 : binary64)
    (fa0 fa1 fa2 fx0 fx1 fx2 fx3 fx4 : binary64)
    (VC  : in_range_64 V_constr V64)
    (bC  : in_range_64 b_constr b64)
    (AC  : in_range_64 A_constr A64)
    (eC  : in_range_64 e_constr e64)
    (vC  : in_range_64 v_constr v64)
    (rxC : in_range_64 x_constr rx64)
    (ryC : in_range_64 y_constr ry64)
    (oxC : in_range_64 x_constr ox64)
    (oyC : in_range_64 y_constr oy64)

    (FFA0 : is_finite _ _ fa0 ≡ true)
    (FFA1 : is_finite _ _ fa1 ≡ true)
    (FFA2 : is_finite _ _ fa2 ≡ true)
    (FFX0 : is_finite _ _ fx0 ≡ true)
    (FFX1 : is_finite _ _ fx1 ≡ true)
    (FFX2 : is_finite _ _ fx2 ≡ true)
    (FFX3 : is_finite _ _ fx3 ≡ true)
    (FFX4 : is_finite _ _ fx4 ≡ true)

    (FX0 : B64R fx0 ≡ B64R v64)
    (FX1 : B64R fx1 ≡ B64R rx64)
    (FX2 : B64R fx2 ≡ B64R ry64)
    (FX3 : B64R fx3 ≡ B64R ox64)
    (FX4 : B64R fx4 ≡ B64R oy64)

    (FA0 : B64R fa0
           ≡ B64R ((A64 ⧄ b64 ⊞ b64_1) ⊠ ((A64 ⧄ b64_2 ⊠ e64) ⊠ e64 ⊞ e64 ⊠ V64)))
    (FA1 : B64R fa1 ≡ B64R (V64 ⧄ b64 ⊞ e64 ⊠ (A64 ⧄ b64 ⊞ b64_1)))
    (FA2 : B64R fa2 ≡ B64R (b64_1 ⧄ (b64_2 ⊠ b64)))

    (F : safe_lt64 FT_Rounding epsilon
           (((0.0 ⊞ 1.0 ⊠ fa0) ⊞ (1.0 ⊠ fx0) ⊠ fa1) ⊞ ((1.0 ⊠ fx0) ⊠ fx0) ⊠ fa2)
           (fmax (fmax 0.0 (fabs (fx1 ⊟ fx3))) (fabs (fx2 ⊟ fx4))))
      :
      (MRasCT.CTypePlus
         (MRasCT.CTypePlus
            (MRasCT.CTypePlus MRasCT.CTypeZero
               (MRasCT.CTypeMult MRasCT.CTypeOne (B64R fa0)))
            (MRasCT.CTypeMult (MRasCT.CTypeMult MRasCT.CTypeOne (B64R fx0)) (B64R fa1)))
         (MRasCT.CTypeMult
            (MRasCT.CTypeMult (MRasCT.CTypeMult MRasCT.CTypeOne (B64R fx0)) (B64R fx0))
            (B64R fa2)) <
         MRasCT.CTypeMax
           (MRasCT.CTypeMax MRasCT.CTypeZero
              (MRasCT.CTypeAbs (MRasCT.CTypeSub (B64R fx1) (B64R fx3))))
           (MRasCT.CTypeAbs (MRasCT.CTypeSub (B64R fx2) (B64R fx4))))%R.
  Proof.
    rewrite !fmaxZeroAbs, !R_MaxZeroAbs, !R_PlusZeroLeft, !R_MultOneLeft in *.

    autounfold with unfold_RCT.
    unfold plus, negate, CarrierAneg, Basics.compose.
    replace (- B64R fx1 + B64R fx3)%R
      with (B64R fx3 - B64R fx1)%R
      by lra.
    replace (- B64R fx2 + B64R fx4)%R
      with (B64R fx4 - B64R fx2)%R
      by lra.

    unfold safe_lt64 in *.
    fold MFloat64asCT.CTypeSub in *.

    repeat
      (let RAN := fresh "RAN" in
       match goal with
       | [H : in_range_64 ?constr ?x |- _] =>
           assert_if_new_as RAN
             (B64R (fst constr) <= B64R x <= B64R (snd constr))%R
       | [H : in_range_64_l ?constr ?x |- _] =>
           assert_if_new_as RAN
             (B64R (fst constr) < B64R x <= B64R (snd constr))%R
       end;
      [first [eapply in_range_64_to_R | eapply in_range_64_l_to_R];
       try reflexivity; eassumption
      |]).
    repeat match goal with
           | [H : context[fst ?x] |- _] => unfold x in *
           | [H : context[snd ?x] |- _] => unfold x in *
           end;
      cbn [fst snd] in *.

    assert (FIN : is_finite _ _ b64_1 ≡ true) by reflexivity.
    assert (FIN0 : is_finite _ _ b64_2 ≡ true) by reflexivity.
    assert (FIN1 : is_finite _ _ 0.0 ≡ true) by reflexivity.
    assert (FIN2 : is_finite _ _ 1.0 ≡ true) by reflexivity.
    assert (FIN3 : is_finite _ _ epsilon ≡ true) by reflexivity.

    (* a hack to avoid matching *)
    pose (hidden_finite := is_finite).
    replace is_finite with hidden_finite in FFA0, FFA1, FFA2 by reflexivity.

    repeat (assert_next; [shelve |]).

    subst hidden_finite.

    autounfold with unfold_FCT in FA0, FA1, FA2;
      autorewrite with rewrite_to_R in FA0, FA1, FA2;
      try assumption.

    repeat (assert_next; [shelve |]).

    apply lt64_correct in F; try assumption.

    pose proof NOVF22 as UF.
    autounfold with unfold_FCT in F;
      autorewrite with rewrite_to_R in F;
      try assumption.

    autounfold with unfold_FCT in UF;
      autorewrite with rewrite_to_R in UF;
      try assumption.

    rewrite !FX0, !FX1, !FX2, !FX3, !FX4 in *.
    clear - FA0 FA1 FA2 UF F RAN RAN0 RAN1 RAN2 RAN3 RAN4 RAN5 RAN6 RAN7.

    generalize dependent (B64R v64); intros vr ? VR.
    generalize dependent (B64R e64); intros e ? ? E.
    generalize dependent (B64R A64); intros a A ? ?.
    generalize dependent (B64R b64); intros b ? B ?.
    generalize dependent (B64R V64); intros vo VO ? ?.

    generalize dependent (B64R fa0); intros a0 ? A0.
    generalize dependent (B64R fa1); intros a1 A1 ?.
    generalize dependent (B64R fa2); intros a2 A2 ?.

    generalize dependent (B64R rx64); intros rx RX ?.
    generalize dependent (B64R ry64); intros ry RY ?.
    generalize dependent (B64R ox64); intros ox OX ?.
    generalize dependent (B64R oy64); intros oy OY ?.
    intros UF.

    repeat match goal with
           | [f : binary64 |- _] => clear f
           end.

    rewrite RCT_max_Rmax.
    setoid_rewrite RCT_abs_Rabs.

    remember (Rmax (Rabs (ox - rx)) (Rabs (oy - ry))) as cheb eqn:CHEB.
    remember (Rmax (Rabs ◻ (rx - ox)) (Rabs ◻ (ry - oy))) as cheb64 eqn:CHEB64.
    remember (a0 + vr * a1 + vr * vr * a2)%R as poly eqn:POLY.
    remember (◻ (◻ (◻ (B64R b64_0 + ◻ (B64R b64_1 * a0)) +
                      ◻ (◻ (B64R b64_1 * vr) * a1)) +
                   ◻ (◻ (◻ (B64R b64_1 * vr) * vr) * a2)))
               as poly64 eqn:POLY64.

    do 15 match goal with | [r : R |- _] => move r at top end.
    move F at bottom.
    move A2 after OY.
    move A1 after OY.
    move A0 after OY.

    eapply DynWin_arith.
    1-3: eassumption.
    eapply VR.
    eapply VO.
    eapply RX.
    eapply RY.
    eapply OX.
    eapply OY.
    all: eassumption.

    (* This would be nicely suitable for [par:] instead of [all:],
       but that encounters an anomaly *)
    Unshelve.
    all: crush_floats.
  Qed.

End Gappa.

Section DynWin_Symbolic.

  Variable ar : vector R 3.
  Variable xr : vector R dynwin_i.

  Fact lt0_3 : 0 < 3. repeat constructor. Qed.
  Fact lt1_3 : 1 < 3. repeat constructor. Qed.
  Fact lt2_3 : 2 < 3. repeat constructor. Qed.

  Fact lt0_5 : 0 < 5. repeat constructor. Qed.
  Fact lt1_5 : 1 < 5. repeat constructor. Qed.
  Fact lt2_5 : 2 < 5. repeat constructor. Qed.
  Fact lt3_5 : 3 < 5. repeat constructor. Qed.
  Fact lt4_5 : 4 < 5. repeat constructor. Qed.

  Let R_env :=
    [Vnth ar lt0_3;
     Vnth ar lt1_3;
     Vnth ar lt2_3;

     Vnth xr lt0_5;
     Vnth xr lt1_5;
     Vnth xr lt2_5;
     Vnth xr lt3_5;
     Vnth xr lt4_5].

  Let r_imemory := dynwin_R_memory ar xr.

  Definition dynwin_SR_σ :=
    [(SRHCOLEval.DSHPtrVal dynwin_a_addr 3, false);
     (SRHCOLEval.DSHPtrVal dynwin_y_addr 1, false);
     (SRHCOLEval.DSHPtrVal dynwin_x_addr 5, false)].

  Definition R_a_mb :=
    SRHCOLEval.mem_add 0 (SVar 0)
      (SRHCOLEval.mem_add 1 (SVar 1)
         (SRHCOLEval.mem_add 2 (SVar 2)
            SRHCOLEval.mem_empty)).

  Definition R_x_mb :=
    SRHCOLEval.mem_add 0 (SVar 3)
      (SRHCOLEval.mem_add 1 (SVar 4)
         (SRHCOLEval.mem_add 2 (SVar 5)
            (SRHCOLEval.mem_add 3 (SVar 6)
               (SRHCOLEval.mem_add 4 (SVar 7)
                  SRHCOLEval.mem_empty)))).

  Definition dynwin_SR_memory :=
    SRHCOLEval.memory_set
      (SRHCOLEval.memory_set
         (SRHCOLEval.memory_set SRHCOLEval.memory_empty
            dynwin_a_addr R_a_mb)
         dynwin_x_addr R_x_mb)
      dynwin_y_addr SRHCOLEval.mem_empty.

  Definition i1 := {| Int64asNT.Int64.intval := 1;
                     Int64asNT.Int64.intrange := conj eq_refl eq_refl |}.
  Definition i3 := {| Int64asNT.Int64.intval := 3;
                     Int64asNT.Int64.intrange := conj eq_refl eq_refl |}.
  Definition i5 := {| Int64asNT.Int64.intval := 5;
                     Int64asNT.Int64.intrange := conj eq_refl eq_refl |}.

  Definition dynwin_SF_σ :=
    [(SFHCOLEval.DSHPtrVal dynwin_a_addr i3, false);
     (SFHCOLEval.DSHPtrVal dynwin_y_addr i1, false);
     (SFHCOLEval.DSHPtrVal dynwin_x_addr i5, false)].

  Definition Fmemory_lookup_deep_unsafe
    (m : FHCOLEval.memory) '(i, off) : MFloat64asCT.t :=
    match FHCOLEval.memory_lookup m i with
    | Some mb => match FHCOLEval.mem_lookup off mb with
                | Some v => v
                | _ => MFloat64asCT.CTypeZero
                end
    | _ => MFloat64asCT.CTypeZero
    end.

  Definition Float_env m :=
    List.map (Fmemory_lookup_deep_unsafe m)
      [(0,0); (0,1); (0,2);
       (2,0); (2,1); (2,2); (2,3); (2,4)].

  (* Convenience wrapper over [RHCOLtoSRHCOL_semantic_preservation] *)
  Lemma RHCOL_to_symbolic_lookup
    (r_σ : RHCOLEval.evalContext)
    (r_op : RHCOLEval.DSHOperator)
    (r_m r_m' : RHCOLEval.memory)
    (r_mb : RHCOLEval.mem_block)

    (sr_σ : SRHCOLEval.evalContext)
    (sr_op : SRHCOLEval.DSHOperator)
    (sr_m : SRHCOLEval.memory)

    (i off : nat)
    (env : RealEnv)
    :
    RHCOLtoSRHCOL.heq_evalContext env RSR_NHE RSR_CHE r_σ sr_σ ->
    RHCOLtoSRHCOL.heq_memory env RSR_CHE r_m sr_m ->

    RHCOLtoSRHCOL.translate r_op = inr sr_op ->

    RHCOLEval.evalDSHOperator r_σ r_op r_m (RHCOLEval.estimateFuel r_op)
    = Some (inr r_m') ->
    RHCOLEval.memory_lookup r_m' i = Some r_mb ->

    RHCOLEval.mem_lookup off r_mb =
      match SRHCOLEval.evalDSHOperator sr_σ sr_op sr_m
              (SRHCOLEval.estimateFuel sr_op) with
      | Some (inr sr_m') =>
          match SRHCOLEval.memory_lookup sr_m' i with
          | Some sr_mb =>
              match SRHCOLEval.mem_lookup off sr_mb with
              | Some sexpr =>
                  evalRealSExpr env sexpr
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end.
  Proof.
    intros Σ M OP RE MB.
    pose proof RHCOLtoSRHCOL_semantic_preservation
      r_op sr_op
      r_σ sr_σ
      r_m sr_m
      env
      as SR_EQUIV.
    full_autospecialize SR_EQUIV; try assumption.

    apply RHCOLtoSRHCOL.translation_syntax_always_correct;
      [apply RSR_NTP | assumption ].

    (* poor man's setoid_rewrite *)
    eapply hopt_r_proper in SR_EQUIV;
      [
      | eapply herr_c_proper, RHCOLtoSRHCOL.heq_memory_proper
      | now rewrite RE
      | reflexivity ].

    invc SR_EQUIV.
    invc H1.
    specialize (H2 i).

    eapply hopt_r_proper in H2;
      [
      | eapply RHCOLtoSRHCOL.heq_mem_block_proper
      | now rewrite MB
      | reflexivity ].

    invc H2.
    specialize (H3 off).

    invc H3.
    reflexivity.
    rewrite H4.
    reflexivity.
  Qed.

  (* TODO: this is exactly the same as the above *)
  Lemma FHCOL_to_symbolic_lookup
    (r_σ : FHCOLEval.evalContext)
    (r_op : FHCOLEval.DSHOperator)
    (r_m r_m' : FHCOLEval.memory)
    (r_mb : FHCOLEval.mem_block)

    (sr_σ : SFHCOLEval.evalContext)
    (sr_op : SFHCOLEval.DSHOperator)
    (sr_m : SFHCOLEval.memory)

    (i off : nat)
    (env : FloatEnv)
    :
    FHCOLtoSFHCOL.heq_evalContext env FSF_NHE FSF_CHE r_σ sr_σ ->
    FHCOLtoSFHCOL.heq_memory env FSF_CHE r_m sr_m ->

    FHCOLtoSFHCOL.translate r_op = inr sr_op ->

    FHCOLEval.evalDSHOperator r_σ r_op r_m (FHCOLEval.estimateFuel r_op)
    = Some (inr r_m') ->
    FHCOLEval.memory_lookup r_m' i = Some r_mb ->

    FHCOLEval.mem_lookup off r_mb =
      match SFHCOLEval.evalDSHOperator sr_σ sr_op sr_m
              (SFHCOLEval.estimateFuel sr_op) with
      | Some (inr sr_m') =>
          match SFHCOLEval.memory_lookup sr_m' i with
          | Some sr_mb =>
              match SFHCOLEval.mem_lookup off sr_mb with
              | Some sexpr =>
                  evalFloatSExpr env sexpr
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end.
  Proof.
    intros Σ M OP RE MB.
    pose proof FHCOLtoSFHCOL_semantic_preservation
      r_op sr_op
      r_σ sr_σ
      r_m sr_m
      env
      as SF_EQUIV.
    full_autospecialize SF_EQUIV; try assumption.

    apply FHCOLtoSFHCOL.translation_syntax_always_correct;
      [apply FSF_NTP | assumption ].

    (* poor man's setoid_rewrite *)
    eapply hopt_r_proper in SF_EQUIV;
      [
      | eapply herr_c_proper, FHCOLtoSFHCOL.heq_memory_proper
      | now rewrite RE
      | reflexivity ].

    invc SF_EQUIV.
    invc H1.
    specialize (H2 i).

    eapply hopt_r_proper in H2;
      [
      | eapply FHCOLtoSFHCOL.heq_mem_block_proper
      | now rewrite MB
      | reflexivity ].

    invc H2.
    specialize (H3 off).

    invc H3.
    reflexivity.
    rewrite H4.
    reflexivity.
  Qed.

  (* For some reason the lhs of this
     doesn't [cbn/cbv/etc], but easily [Compute]s *)
  Fact DynWin_Symbolic_out :
    match
      evalDSHOperator dynwin_SF_σ DynWin_SFHCOL_hard dynwin_SR_memory
        (estimateFuel DynWin_SFHCOL_hard)
    with
    | Some (inr sr_m') =>
        match memory_lookup sr_m' dynwin_y_addr with
        | Some sr_mb =>
            match mem_lookup dynwin_y_offset sr_mb with
            | Some sexpr => Some sexpr
            | None => None
            end
        | None => None
        end
    | _ => None
    end
    ≡ Some
        (SZLess
           (SPlus
              (SPlus (SPlus SConstZero (SMult SConstOne (SVar 0)))
                 (SMult (SMult SConstOne (SVar 3)) (SVar 1)))
              (SMult (SMult (SMult SConstOne (SVar 3)) (SVar 3)) (SVar 2)))
           (SMax (SMax SConstZero (SAbs (SSub (SVar 4) (SVar 6))))
              (SAbs (SSub (SVar 5) (SVar 7))))).
  Proof.
    reflexivity.
  Qed.

  Lemma RHCOL_to_FHCOL_numerical_correct
    (r_omemory : RHCOLEval.memory)
    (a_rmem x_rmem y_rmem : RHCOLEval.mem_block)
    (f_imemory f_omemory : FHCOLEval.memory)
    (f_iσ : FHCOLEval.evalContext)
    (y_fmem : FHCOLEval.mem_block)
    (DynWin_FHCOL : FHCOLEval.DSHOperator)
    
    (R_EVAL : RHCOLEval.evalDSHOperator dynwin_R_σ DynWin_RHCOL r_imemory
                (RHCOLEval.estimateFuel DynWin_RHCOL)
              = Some (inr r_omemory))
    (A_RMEM : RHCOLEval.memory_lookup r_imemory dynwin_a_addr = Some a_rmem)
    (X_RMEM : RHCOLEval.memory_lookup r_imemory dynwin_x_addr = Some x_rmem)
    (Y_RMEM : RHCOLEval.memory_lookup r_omemory dynwin_y_addr = Some y_rmem)
    
    (F_EVAL : FHCOLEval.evalDSHOperator f_iσ DynWin_FHCOL f_imemory
                (FHCOLEval.estimateFuel DynWin_FHCOL)
              = Some (inr f_omemory))
    (Y_FMEM : FHCOLEval.memory_lookup f_omemory dynwin_y_addr = Some y_fmem)
    
    (TRANSLATE_OP : RHCOLtoFHCOL.translate DynWin_RHCOL = inr DynWin_FHCOL)
    (RF_IM : RHCOLtoFHCOL.heq_memory () RF_CHE r_imemory f_imemory)
    (RF_IΣ : RHCOLtoFHCOL.heq_evalContext () RF_NHE RF_CHE dynwin_R_σ f_iσ)
    :
    DynWinInConstr a_rmem x_rmem ->
    DynWinOutRel a_rmem x_rmem y_rmem y_fmem.
  Proof.
    intros INCONSTR.
    unfold DynWinOutRel.

    (* poor man's [setoid_rewrite RHCOL_to_symbolic_lookup] *)
    eapply hopt_r_proper;
      [typeclasses eauto | | reflexivity |].
    {
      rewrite RHCOL_to_symbolic_lookup with
        (sr_σ := dynwin_SR_σ)
        (sr_m := dynwin_SR_memory)
        (i := dynwin_y_addr)
        (off := dynwin_y_offset)
        (env := R_env).
      5,6: eassumption.
      4: {
        rewrite DynWin_RHCOL_hard_OK, DynWin_SRHCOL_hard_OK.
        reflexivity.
      }
        
      reflexivity.

      -
        repeat constructor.
      -
        intros k.
        do 3 try destruct k.
        + (* a *)
          unfold r_imemory.
          cbn - [ctvector_to_mem_block].
          constructor.
          intros k.
          do 3 try destruct k.
          1-3: erewrite mem_lookup_ctvector_to_mem_block.
          1-3: now constructor.
          cbn - [ctvector_to_mem_block].
          rewrite ctvector_to_mem_block_key_oob.
          constructor.
          lia.
        + (* y *)
          unfold r_imemory.
          cbn - [ctvector_to_mem_block].
          repeat constructor.
        + (* x *)
          unfold r_imemory.
          cbn - [ctvector_to_mem_block].
          constructor.
          intros k.
          do 5 try destruct k.
          1-5: erewrite mem_lookup_ctvector_to_mem_block.
          1-5: now constructor.
          cbn - [ctvector_to_mem_block].
          rewrite ctvector_to_mem_block_key_oob.
          constructor.
          lia.
        +
          constructor.
    }

    cbv - [FHCOLEval.mem_lookup CType_impl evalRealSExpr R_env].
    eapply hopt_r_proper;
      [typeclasses eauto | reflexivity | |].
    {
      rewrite FHCOL_to_symbolic_lookup with
        (sr_σ := dynwin_SF_σ)
        (sr_m := dynwin_SR_memory)
        (i := dynwin_y_addr)
        (off := dynwin_y_offset)
        (env := Float_env f_imemory).
      5,6: eassumption.
      4: {
        rewrite DynWin_FHCOL_hard_OK in TRANSLATE_OP.
        invc TRANSLATE_OP.
        erewrite FHCOLtoSFHCOL.translate_proper.
        now rewrite DynWin_SFHCOL_hard_OK.
        now rewrite H1.
      }

      reflexivity.
      -
        clear - RF_IΣ RF_IM.
        invc RF_IΣ; invc H3; invc H5; invc H6.
        repeat constructor.
        all: unfold RHCOLtoFHCOL.heq_evalContextElem in *.
        all: repeat break_let; subst_max.
        all: invc H1; invc H2; invc H3.
        all: invc H; invc H1; invc H2.
        all: invc H0; invc H4; invc H5.
        all: repeat constructor; try congruence.
        all: cbn in *; unfold heq_nat_int in *.
        all: destruct s', s'0, s'1; cbv in H6, H7, H8; subst.
        all: cbv; f_equal; apply proof_irrelevance.
      -
        clear - RF_IM.
        intros k; specialize (RF_IM k).
        do 3 try destruct k.
        + (* a *)
          unfold r_imemory in *.
          cbn - [Float_env ctvector_to_mem_block] in *.
          invc RF_IM.
          constructor.
          intros off; specialize (H1 off).
          do 3 try destruct off.
          4: {
            rewrite ctvector_to_mem_block_key_oob in H1 by lia.
            invc H1.
            constructor.
          }
          
          all: erewrite mem_lookup_ctvector_to_mem_block in H1.
          all: invc H1.
          all: cbn - [Float_env].
          all: constructor.
          all: unfold heq_Float_SExpr; cbn.
          all: now rewrite <-H0, <-H2.
          Unshelve.
          all: cbv; lia.
        + (* y *)
          unfold r_imemory in *.
          cbn - [Float_env ctvector_to_mem_block] in *.
          invc RF_IM.
          constructor.
          intros off; specialize (H1 off); invc H1.
          cbn.
          constructor.
        + (* x *)
          unfold r_imemory in *.
          cbn - [Float_env ctvector_to_mem_block] in *.
          invc RF_IM.
          constructor.
          intros off; specialize (H1 off).
          do 5 try destruct off.
          6: {
            rewrite ctvector_to_mem_block_key_oob in H1 by lia.
            invc H1.
            constructor.
          }
          
          all: erewrite mem_lookup_ctvector_to_mem_block in H1.
          all: invc H1.
          all: cbn - [Float_env].
          all: constructor.
          all: unfold heq_Float_SExpr; cbn.
          all: now rewrite <-H0, <-H2.
          Unshelve.
          all: cbv; lia.
        +
          invc RF_IM.
          constructor.
    }

    pose proof DynWin_Symbolic_out as DS.
    repeat break_match_goal; try some_none.
    invc DS.

    (*
    (evalDSHOperator dynwin_SF_σ DynWin_SFHCOL_hard dynwin_SR_memory
       (estimateFuel DynWin_SFHCOL_hard))
      with (Some (@inr string _ hackity_hack))
      by reflexivity.
    unfold hackity_hack.
     *)
    cbv - [CType_impl evalRealSExpr R_env evalFloatSExpr Float_env].

    assert (RF_Env : forall k, nth_error R_env k ≡
                   liftM (B2R _ _) (nth_error (Float_env f_imemory) k)).
    {
      clear - RF_IM.
      intros.
      do 8 try destruct k.
      9: cbn; now rewrite !nth_error_nil_None.

      all: cbn.
      all: match goal with
           | |- context[FHCOLEval.memory_lookup _ ?n] =>
               specialize (RF_IM n)
           end.
      all: cbn - [ctvector_to_mem_block] in RF_IM; invc RF_IM.
      all: match goal with
           | |- context[FHCOLEval.mem_lookup ?n _] =>
               specialize (H1 n)
           end.
      all: erewrite mem_lookup_ctvector_to_mem_block in H1.
      all: invc H1; invc H3.
      all: rewrite H1; reflexivity.
    }

    clear - INCONSTR A_RMEM X_RMEM RF_IM RF_Env.
    cbn [evalRealSExpr evalFloatSExpr].
    rewrite !RF_Env; clear RF_Env.

    unfold Float_env.
    rewrite !Coqlib.list_map_nth.
    cbn [nth_error Coqlib.option_map
           liftM liftM2 OptionMonad.Monad_option bind ret].
    constructor.

    pose proof RF_IM 0 as RF_A_IM.
    rewrite A_RMEM in RF_A_IM.
    invc RF_A_IM.

    pose proof RF_IM 2 as RF_X_IM.
    rewrite X_RMEM in RF_X_IM.
    invc RF_X_IM.

    cbn [Fmemory_lookup_deep_unsafe].
    rewrite <-!H0, <-!H2.
    clear - INCONSTR H1 H3.
    rename b into a_fmem, b0 into x_fmem, H1 into FA, H3 into FX.

    unfold DynWinInConstr in INCONSTR.
    destruct INCONSTR as
      (V64 & b64 & A64 & e64 & v64 & rx64 & ry64 & ox64 & oy64 & INCONSTR).
    destruct INCONSTR as
      (VC & bC & AC & eC & A & vC & rxC & ryC & oxC & oyC & X).

    unfold make_a64 in *.

    Ltac mem_lookup_simpl :=
      unfold FHCOLEval.mem_add, FHCOLEval.mem_lookup in *;
      repeat (try rewrite Memory.NP.F.add_eq_o in * by lia;
              try rewrite Memory.NP.F.add_neq_o in * by lia).

    (* Hardcoded lookups in a *)
    pose proof (A 0) as A0.
    pose proof (FA 0) as FA0.
    mem_lookup_simpl.
    inversion A0 as [| a0 ? A0E A0'];
      subst; rewrite <-A0' in *; clear A0 A0'.
    inversion FA0 as [| a0' ? FA0E TMP1 TMP2];
      subst; rename b into fa0; clear TMP2 FA0.
    
    pose proof (A 1) as A1.
    pose proof (FA 1) as FA1.
    mem_lookup_simpl.
    inversion A1 as [| a1 ? A1E A1'];
      subst; rewrite <-A1' in *; clear A1 A1'.
    inversion FA1 as [| a1' ? FA1E TMP1 TMP2];
      subst; rename b into fa1; clear TMP2 FA1.

    pose proof (A 2) as A2.
    pose proof (FA 2) as FA2.
    mem_lookup_simpl.
    remember (b64_div FT_Rounding b64_1 (MFloat64asCT.CTypeMult b64_2 b64)) as T.
    inversion A2 as [| a2 ? A2E A2'];
      subst; rewrite <-A2' in *; clear A2 A2'.
    inversion FA2 as [| a2' ? FA2E TMP1 TMP2];
      subst; rename b into fa2; clear TMP2 FA2.

    clear A FA.

    (* Hardcoded lookups in x *)
    pose proof (X 0) as X0.
    pose proof (FX 0) as FX0.
    mem_lookup_simpl.
    inversion X0 as [| x0 ? X0E X0'];
      subst; rewrite <-X0' in *; clear X0 X0'.
    inversion FX0 as [| x0' ? FX0E TMP1 TMP2];
      subst; rename b into fx0; clear TMP2 FX0.

    pose proof (X 1) as X1.
    pose proof (FX 1) as FX1.
    mem_lookup_simpl.
    inversion X1 as [| x1 ? X1E X1'];
      subst; rewrite <-X1' in *; clear X1 X1'.
    inversion FX1 as [| x1' ? FX1E TMP1 TMP2];
      subst; rename b into fx1; clear TMP2 FX1.

    pose proof (X 2) as X2.
    pose proof (FX 2) as FX2.
    mem_lookup_simpl.
    inversion X2 as [| x2 ? X2E X2'];
      subst; rewrite <-X2' in *; clear X2 X2'.
    inversion FX2 as [| x2' ? FX2E TMP1 TMP2];
      subst; rename b into fx2; clear TMP2 FX2.

    pose proof (X 3) as X3.
    pose proof (FX 3) as FX3.
    mem_lookup_simpl.
    inversion X3 as [| x3 ? X3E X3'];
      subst; rewrite <-X3' in *; clear X3 X3'.
    inversion FX3 as [| x3' ? FX3E TMP1 TMP2];
      subst; rename b into fx3; clear TMP2 FX3.

    pose proof (X 4) as X4.
    pose proof (FX 4) as FX4.
    mem_lookup_simpl.
    inversion X4 as [| x4 ? X4E X4'];
      subst; rewrite <-X4' in *; clear X4 X4'.
    inversion FX4 as [| x4' ? FX4E TMP1 TMP2];
      subst; rename b into fx4; clear TMP2 FX4.

    clear X FX.

    unfold RHCOLtoFHCOL.heq_CType', RF_CHE in *.
    destruct FA0E as [FA0F FA0].
    destruct FA1E as [FA1F FA1].
    destruct FA2E as [FA2F FA2].
    destruct FX0E as [FX0F FX0].
    destruct FX1E as [FX1F FX1].
    destruct FX2E as [FX2F FX2].
    destruct FX3E as [FX3F FX3].
    destruct FX4E as [FX4F FX4].
    destruct A0E as [A0F A0].
    destruct A1E as [A1F A1].
    destruct A2E as [A2F A2].
    destruct X0E as [X0F X0].
    destruct X1E as [X1F X1].
    destruct X2E as [X2F X2].
    destruct X3E as [X3F X3].
    destruct X4E as [X4F X4].
    subst.

    intros F.
    rewrite float_as_bool_Zless in F; apply R_as_bool_Zless.

    eapply DynWin_numerical_stability.
    eapply VC.
    eapply bC.
    eapply AC.
    eapply eC.
    eapply vC.
    eapply rxC.
    eapply ryC.
    eapply oxC.
    eapply oyC.
    all: assumption.
  Qed.

End DynWin_Symbolic.

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
      RHCOLtoFHCOL.translate DynWin_RHCOL = inr dynwin_FHCOL ->

      (* Equivalent inputs *)
      RHCOLtoFHCOL.heq_memory () RF_CHE (dynwin_R_memory a x) dynwin_F_memory ->
      RHCOLtoFHCOL.heq_evalContext () RF_NHE RF_CHE dynwin_R_σ dynwin_F_σ ->

      forall a_rmem x_rmem,
        RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_a_addr = Some a_rmem ->
        RHCOLEval.memory_lookup (dynwin_R_memory a x) dynwin_x_addr = Some x_rmem ->
        DynWinInConstr a_rmem x_rmem ->

        (* Everything correct on Reals *)
        exists r_omemory y_rmem,
          RHCOLEval.evalDSHOperator
            dynwin_R_σ
            DynWin_RHCOL
            (dynwin_R_memory a x)
            (RHCOLEval.estimateFuel DynWin_RHCOL) = Some (inr r_omemory)
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
           DynWin_RHCOL
           (dynwin_R_memory a x)
           (RHCOLEval.estimateFuel DynWin_RHCOL) = Some (inr r_omemory)) as RO.
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
      unfold Basics.compose.
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

    specialize (MRHCOL x).
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
      pose proof (@RHCOLEval.evalDSHOperator_estimateFuel dynwin_R_σ DynWin_RHCOL (dynwin_R_memory a x)) as CC.
      clear - CC AE.
      apply util.is_None_def in AE.
      generalize dependent (RHCOLEval.evalDSHOperator dynwin_R_σ DynWin_RHCOL
                                                      (dynwin_R_memory a x) (RHCOLEval.estimateFuel DynWin_RHCOL)).
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
       DynWin_RHCOL
       dynwin_FHCOL
       (RHCOLEval.estimateFuel DynWin_RHCOL)
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

  clear y HC.

  subst.

  eapply RHCOL_to_FHCOL_numerical_correct;
    try eassumption.
  now rewrite RE.
  now rewrite <-Y_RMEM.
  now rewrite F_EVAL.
  now rewrite <-Y_FMEM.
Qed.
