Require Import Helix.Tactics.StructTactics.

From Coq Require Import micromega.Psatz Reals.Rdefinitions.

Require Import MathClasses.interfaces.canonical_names.

From Flocq Require Import Binary Bits PrimFloat Generic_fmt FLT Raux.
From Gappa Require Import Gappa_tactic.

Require Import Helix.FSigmaHCOL.Float64asCT.


Open Scope R_scope.

Section Float64.

  Let prec := 53%Z.
  Let emax := 1024%Z.
  Let fexp := (FLT_exp (3 - emax - prec)%Z prec).

  Variable m : mode.

  Definition le64 (a b : binary64) : Prop :=
    b64_compare a b ≡ Some Datatypes.Eq
    \/ b64_compare a b ≡ Some Datatypes.Lt.

  Definition lt64 (a b : binary64) : Prop :=
    b64_compare a b ≡ Some Datatypes.Lt.

  Definition safe_lt64 (a b : binary64) : Prop :=
    lt64 epsilon (MFloat64asCT.CTypeSub b a).

  (* inclusive range check *)
  Definition in_range_64 : (binary64 * binary64) -> binary64 -> Prop
    := fun '(a,b) x => is_finite _ _ x ≡ true /\ le64 a x /\ le64 x b.

  (* left excluded, right included range check *)
  Definition in_range_64_l : (binary64 * binary64) -> binary64 -> Prop
    := fun '(a,b) x => is_finite _ _ x ≡ true /\ lt64 a x /\ le64 x b.

  Lemma in_range_finite (lo hi x : binary64) :
    in_range_64 (lo, hi) x ->
    is_finite _ _ x ≡ true.
  Proof.
    unfold in_range_64.
    tauto.
  Qed.

  Lemma le64_correct (a b : binary64) :
    is_finite _ _ a ≡ true ->
    is_finite _ _ b ≡ true ->
    le64 a b -> B2R _ _ a <= B2R _ _ b.
  Proof.
    intros FA FB LE64.
    unfold le64, b64_compare in *.
    destruct LE64 as [EQ64 | LT64].
    -
      rewrite Bcompare_correct in EQ64 by assumption.
      inversion EQ64.
      apply Rcompare_Eq_inv in H0.
      lra.
    -
      rewrite Bcompare_correct in LT64 by assumption.
      inversion LT64.
      apply Rcompare_Lt_inv in H0.
      lra.
  Qed.

  Lemma lt64_correct (a b : binary64) :
    is_finite _ _ a ≡ true ->
    is_finite _ _ b ≡ true ->
    lt64 a b -> B2R _ _ a <= B2R _ _ b.
  Proof.
    intros FA FB LT64.
    unfold lt64, b64_compare in *.
    rewrite Bcompare_correct in LT64 by assumption.
    inversion LT64.
    apply Rcompare_Lt_inv in H0.
    lra.
  Qed.

  Lemma in_range_64_to_R (lo hi x : binary64) :
    is_finite _ _ lo ≡ true ->
    is_finite _ _ hi ≡ true ->
    in_range_64 (lo, hi) x ->
    B2R _ _ lo <= B2R _ _ x <= B2R _ _ hi.
  Proof.
    intros FLO FHI INRG.
    unfold in_range_64 in INRG.
    destruct INRG as (F & LO & HI).
    split; now apply le64_correct.
  Qed.

  (* Corollary of Bminus_correct *)
  Lemma b64_minus_to_R (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x - B2R _ _ y))
    < bpow radix2 emax
    ->
      B2R _ _ (b64_minus m x y)
      ≡ Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x - B2R _ _ y).
  Proof.
    intros *.
    intros FX FY B.
    pose proof
      Bminus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y FX FY
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_minus_finite (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x - B2R _ _ y))
    < bpow radix2 emax
    -> is_finite _ _ (b64_minus m x y) ≡ true.
  Proof.
    intros *.
    intros FX FY B.
    pose proof
      Bminus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y FX FY
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  (* Corollary of Bmult_correct *)
  Lemma b64_mult_to_R (x y : binary64) :
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x * B2R _ _ y))
    < bpow radix2 emax
    ->
      B2R _ _ (b64_mult m x y)
      ≡ Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x * B2R _ _ y).
  Proof.
    intros * B.
    pose proof
      Bmult_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_mult_finite (x y : binary64) :
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x * B2R _ _ y))
    < bpow radix2 emax
    -> is_finite _ _ x ≡ true
    -> is_finite _ _ y ≡ true
    -> is_finite _ _ (b64_mult m x y) ≡ true.
  Proof.
    intros * B FX FY.
    pose proof
      Bmult_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    destruct COR as (_ & F & _).
    unfold b64_mult.
    rewrite F, FX, FY.
    reflexivity.
  Qed.

  (* Corollary of Bplus_correct *)
  Lemma b64_plus_to_R (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x + B2R _ _ y))
    < bpow radix2 emax
    ->
      B2R _ _ (b64_plus m x y)
      ≡ Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x + B2R _ _ y).
  Proof.
    intros * XF YF B.
    pose proof
      Bplus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_plus_finite (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x + B2R _ _ y))
    < bpow radix2 emax
    -> is_finite _ _ (b64_plus m x y) ≡ true.
  Proof.
    intros *.
    intros FX FY B.
    pose proof
      Bplus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y FX FY
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  (* Corollary of Bplus_correct *)
  Lemma b64_div_to_R (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    B2R _ _ y <> 0 ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x / B2R _ _ y))
    < bpow radix2 emax
    ->
      B2R _ _ (b64_div m x y)
      ≡ Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x / B2R _ _ y).
  Proof.
    intros * XF YF YO B.
    pose proof
      Bdiv_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_div_finite (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    B2R _ _ y <> 0 ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x / B2R _ _ y))
    < bpow radix2 emax
    -> is_finite _ _ (b64_div m x y) ≡ true.
  Proof.
    intros *.
    intros FX FY YO B.
    pose proof
      Bdiv_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y YO
      as COR.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    destruct COR as [_ [FIN _]].
    unfold b64_div.
    congruence.
  Qed.

End Float64.

Section Float64CT.


End Float64CT.

Section Constants.

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

End Constants.
