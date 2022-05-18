Require Import Helix.Tactics.StructTactics.

From Coq Require Import micromega.Psatz Reals.Rdefinitions.

Require Import MathClasses.interfaces.canonical_names.

From Flocq Require Import Binary Bits PrimFloat Generic_fmt FLT Raux.
From Gappa Require Import Gappa_tactic.

Require Import Helix.FSigmaHCOL.Float64asCT.


Open Scope R_scope.

Notation B64R := (B2R 53 1024).

Section Float64.

  Let prec := 53%Z.
  Let emax := 1024%Z.
  Let fexp := (FLT_exp (3 - emax - prec)%Z prec).

  Variable m : mode.

  Definition no_overflow64 (rf : R) :=
    Rabs rf < bpow radix2 emax.

  Definition round64 : R -> R :=
    Generic_fmt.round radix2 fexp (round_mode m).

  Hint Unfold no_overflow64 round64 : sugar64.

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

  Lemma in_range_l_finite (lo hi x : binary64) :
    in_range_64_l (lo, hi) x ->
    is_finite _ _ x ≡ true.
  Proof.
    unfold in_range_64_l.
    tauto.
  Qed.

  (*
     A common goal is to prove that a real fits in a float range
     (i.e. [r < 2^emax]). Gappa can't handle goals with [lt].
     Shrink the range (generously) and move to [le].
   *)
  Lemma bpow_lt_to_le (r : R) (p : Z) :
    r <= bpow radix2 (p - 1) ->
    r < bpow radix2 p.
  Proof.
    enough (bpow radix2 (p - 1) < bpow radix2 p)
      by lra.
    clear r.
    apply bpow_lt.
    lia.
  Qed.

  Lemma le64_correct (a b : binary64) :
    is_finite _ _ a ≡ true ->
    is_finite _ _ b ≡ true ->
    le64 a b -> B64R a <= B64R b.
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
    lt64 a b -> B64R a < B64R b.
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
    B64R lo <= B64R x <= B64R hi.
  Proof.
    intros FLO FHI INRG.
    unfold in_range_64 in INRG.
    destruct INRG as (F & LO & HI).
    split; now apply le64_correct.
  Qed.

  Lemma in_range_64_l_to_R (lo hi x : binary64) :
    is_finite _ _ lo ≡ true ->
    is_finite _ _ hi ≡ true ->
    in_range_64_l (lo, hi) x ->
    B64R lo < B64R x <= B64R hi.
  Proof.
    intros FLO FHI INRG.
    unfold in_range_64_l in INRG.
    destruct INRG as (F & LO & HI).
    split.
    now apply lt64_correct.
    now apply le64_correct.
  Qed.

  (* Corollary of Bminus_correct *)
  Lemma b64_minus_to_R (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    no_overflow64 (round64 (B64R x - B64R y)) ->
    B64R (b64_minus m x y) ≡ round64 (B64R x - B64R y).
  Proof.
    intros *.
    intros FX FY B.
    pose proof
      Bminus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y FX FY
      as COR.
    autounfold with sugar64 in *.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_minus_finite (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    no_overflow64 (round64 (B64R x - B64R y)) ->
    is_finite _ _ (b64_minus m x y) ≡ true.
  Proof.
    intros *.
    intros FX FY B.
    pose proof
      Bminus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y FX FY
      as COR.
    autounfold with sugar64 in *.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  (* Corollary of Bmult_correct *)
  Lemma b64_mult_to_R (x y : binary64) :
    no_overflow64 (round64 (B64R x * B64R y)) ->
    B64R (b64_mult m x y) ≡ round64 (B64R x * B64R y).
  Proof.
    intros * B.
    pose proof
      Bmult_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    autounfold with sugar64 in *.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_mult_finite (x y : binary64) :
    no_overflow64 (round64 (B64R x * B64R y)) ->
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    is_finite _ _ (b64_mult m x y) ≡ true.
  Proof.
    intros * B FX FY.
    pose proof
      Bmult_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    autounfold with sugar64 in *.
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
    no_overflow64 (round64 (B64R x + B64R y)) ->
    B64R (b64_plus m x y) ≡ round64 (B64R x + B64R y).
  Proof.
    intros * XF YF B.
    pose proof
      Bplus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    autounfold with sugar64 in *.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_plus_finite (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    no_overflow64 (round64 (B64R x + B64R y)) ->
    is_finite _ _ (b64_plus m x y) ≡ true.
  Proof.
    intros *.
    intros FX FY B.
    pose proof
      Bplus_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y FX FY
      as COR.
    autounfold with sugar64 in *.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  (* Corollary of Bplus_correct *)
  Lemma b64_div_to_R (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    B64R y <> 0 ->
    no_overflow64 (round64 (B64R x / B64R y)) ->
    B64R (b64_div m x y) ≡ round64 (B64R x / B64R y).
  Proof.
    intros * XF YF YO B.
    pose proof
      Bdiv_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y
      as COR.
    autounfold with sugar64 in *.
    subst prec emax fexp.
    apply Rlt_bool_true in B.
    rewrite B in COR.
    tauto.
  Qed.

  Lemma b64_div_finite (x y : binary64) :
    is_finite _ _ x ≡ true ->
    is_finite _ _ y ≡ true ->
    B64R y <> 0 ->
    no_overflow64 (round64 (B64R x / B64R y)) ->
    is_finite _ _ (b64_div m x y) ≡ true.
  Proof.
    intros *.
    intros FX FY YO B.
    pose proof
      Bdiv_correct prec emax eq_refl eq_refl binop_nan_pl64 m x y YO
      as COR.
    autounfold with sugar64 in *.
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

  (* 0.0 *)
  Definition b64_0 := B754_zero 53 1024 false.
  (* 0.1 *)
  Definition b64_0_1 :=
    B754_finite 53 1024 false 7205759403792794 (-56)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4591870180066957722).
  (* 0.01 *)
  Definition b64_0_01 :=
    B754_finite 53 1024 false 5764607523034235 (-59)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4576918229304087675).
  (* 1.0 *)
  Definition b64_1 :=
    B754_finite 53 1024 false 4503599627370496 (-52)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4607182418800017408).
  (* 2.0 *)
  Definition b64_2 :=
    B754_finite 53 1024 false 4503599627370496 (-51)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4611686018427387904).
  (* 5.0 *)
  Definition b64_5 :=
    B754_finite 53 1024 false 5629499534213120 (-50)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4617315517961601024).
  (* 6.0 *)
  Definition b64_6 :=
    B754_finite 53 1024 false 6755399441055744 (-50)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4618441417868443648).
  (* 20.0 *)
  Definition b64_20 :=
    B754_finite 53 1024 false 5629499534213120 (-48)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4626322717216342016).
  (* 5000.0 *)
  Definition b64_5000 :=
    B754_finite 53 1024 false 5497558138880000 (-40)
      (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
         4662219572839972864).

End Constants.

Global Hint Unfold
  b64_0 b64_0_1 b64_0_01 b64_1 b64_2 b64_5 b64_6 b64_20 b64_5000
  : F64_const.

  
