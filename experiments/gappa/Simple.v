Require Import Helix.Tactics.StructTactics.

From Coq Require Import micromega.Psatz Reals.Rdefinitions.
From Flocq Require Import Binary Bits PrimFloat Generic_fmt FLT Raux.
From Gappa Require Import Gappa_tactic.

Open Scope R_scope.

Section AUX.

  Definition FT_Rounding : mode := mode_NE.

  Definition CTypePlus     := b64_plus FT_Rounding.
  Definition CTypeSub      := b64_minus FT_Rounding.
  Definition CTypeMult     := b64_mult FT_Rounding.

  Definition le64 (a b : binary64) : Prop :=
    b64_compare a b = Some Datatypes.Eq
    \/ b64_compare a b = Some Datatypes.Lt.

  Definition lt64 (a b : binary64) : Prop :=
    b64_compare a b = Some Datatypes.Lt.

  Definition in_range_64 : (binary64 * binary64) -> binary64 -> Prop
    := fun '(a,b) x => is_finite _ _ x = true /\ le64 a x /\ le64 x b.

  Lemma in_range_finite (lo hi x : binary64) :
    in_range_64 (lo, hi) x ->
    is_finite _ _ x = true.
  Proof.
    unfold in_range_64.
    tauto.
  Qed.

  Lemma le64_correct (a b : binary64) :
    is_finite _ _ a = true ->
    is_finite _ _ b = true ->
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
    is_finite _ _ a = true ->
    is_finite _ _ b = true ->
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
    is_finite _ _ lo = true ->
    is_finite _ _ hi = true ->
    in_range_64 (lo, hi) x ->
    B2R _ _ lo <= B2R _ _ x <= B2R _ _ hi.
  Proof.
    intros FLO FHI INRG.
    unfold in_range_64 in INRG.
    destruct INRG as (F & LO & HI).
    split; now apply le64_correct.
  Qed.

  (* Corollary of Bminus_correct *)
  Lemma b64_minus_to_R (m : mode) (x y : binary64) :
    let prec := 53%Z in
    let emax := 1024%Z in
    let fexp := (FLT_exp (3 - emax - prec)%Z prec) in
    is_finite _ _ x = true ->
    is_finite _ _ y = true ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x - B2R _ _ y))
    < bpow radix2 emax
    ->
      B2R _ _ (b64_minus m x y)
      = Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x - B2R _ _ y).
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

  Lemma b64_minus_finite (m : mode) (x y : binary64) :
    let prec := 53%Z in
    let emax := 1024%Z in
    let fexp := (FLT_exp (3 - emax - prec)%Z prec) in
    is_finite _ _ x = true ->
    is_finite _ _ y = true ->
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x - B2R _ _ y))
    < bpow radix2 emax
    -> is_finite _ _ (b64_minus m x y) = true.
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
  Lemma b64_mult_to_R (m : mode) (x y : binary64) :
    let prec := 53%Z in
    let emax := 1024%Z in
    let fexp := (FLT_exp (3 - emax - prec)%Z prec) in
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x * B2R _ _ y))
    < bpow radix2 emax
    ->
      B2R _ _ (b64_mult m x y)
      = Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x * B2R _ _ y).
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

  Lemma b64_mult_finite (m : mode) (x y : binary64) :
    let prec := 53%Z in
    let emax := 1024%Z in
    let fexp := (FLT_exp (3 - emax - prec)%Z prec) in
    Rabs (Generic_fmt.round radix2 fexp (round_mode m) (B2R _ _ x * B2R _ _ y))
    < bpow radix2 emax
    -> is_finite _ _ x = true
    -> is_finite _ _ y = true
    -> is_finite _ _ (b64_mult m x y) = true.
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

  (*
     A common goal is to prove that a real fits in a float range
     (i.e. [r < 2^emax]). Gappa can't handle goals with [lt].
     Shrink the range and move to [le].
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

  Definition b0_0 := B754_zero 53 1024 false. (* 0.0 *)
  Definition b200 := B754_finite 53 1024 false 7036874417766400 (-45)
                       (binary_float_of_bits_aux_correct 52 11
                          eq_refl eq_refl eq_refl 4641240890982006784).
  Definition b3000 := B754_finite 53 1024 false 6597069766656000 (-41)
                        (binary_float_of_bits_aux_correct 52 11
                           eq_refl eq_refl eq_refl 4658815484840378368).
  Definition tiny := B754_finite 53 1024 false 1 (-1074)
                       (binary_float_of_bits_aux_correct 52 11
                          eq_refl eq_refl eq_refl 1).

End AUX.


Ltac compute_B2R :=
  repeat (cbv [Defs.F2R IZR IPR IPR_2 Z.pow_pos Pos.iter] in *;
          simpl in *).

Ltac gappa_form :=
  try apply bpow_lt_to_le.

(** * Minimal example *)
Section Primitive.
  (* see primitive.g *)
  (*
    The simplest gappa-specific problem.
     Epsilon here given as a binary float for demonstration purposes.
   *)

  (* 1b-44 *)
  Definition d := B754_finite 53 1024 false 4503599627370496 (-96)
                    (binary_float_of_bits_aux_correct 52 11
                       eq_refl eq_refl eq_refl 4409024035195715584).

  Lemma bconst :
    forall x,
      0 <= x <= 1000 ->
      Ropp (B2R _ _ d) <= x - rounding_float rndNE 53 (-1074) x <= B2R _ _ d.
  Proof.
    intros.
    (* reduce binary constants to R *)
    unfold B2R, Defs.F2R, IZR, IPR, IPR_2; cbn.
    gappa.
  Qed.

End Primitive.

Section Problem.
  (*
    See [simple.g].
    This is a description of the same problem in terms of proper Flocq IEEE-754
    binary floats. The [.g] is not used, just left for demonstration purposes.
    The proof is carried out using coq-gappa: the [gappa] tactic.
   *)

  Variable x y : binary64.
  Hypothesis XR : in_range_64 (b0_0, b200) x.
  Hypothesis YR : in_range_64 (b0_0, b3000) y.

  Definition l := (B2R _ _ x) * (B2R _ _ x).
  Definition r := (B2R _ _ y) * (B2R _ _ y).

  Definition l64 := CTypeMult x x.
  Definition r64 := CTypeMult y y.

  (* 1b-38 *)
  Definition eps1 := B754_finite 53 1024 false 4503599627370496 (-90)
                       (binary_float_of_bits_aux_correct 52 11
                          eq_refl eq_refl eq_refl 4436045632959938560).
  (* 1b-30 *)
  Definition eps2 := B754_finite 53 1024 false 4503599627370496 (-82)
                       (binary_float_of_bits_aux_correct 52 11
                          eq_refl eq_refl eq_refl 4472074429978902528).

  Hint Unfold b0_0 b200 b3000 eps1 eps2 tiny : const_unfold.
  Hint Rewrite
    b64_minus_to_R b64_mult_to_R
    b64_minus_finite b64_mult_finite
    lt64_correct
    : rewrite_to_R.

  Lemma safe :
    lt64 b0_0 (CTypeSub (CTypeSub (CTypeSub r64 l64) eps1) eps2) ->
    B2R _ _ tiny <= r - l.
  Proof.
    intros LE.

    unfold l64, r64, CTypeSub, CTypeMult in *.

    (* lift comparison to R *)
    copy_apply in_range_finite XR; rename H into XF.
    copy_apply in_range_finite YR; rename H into YF.
    apply in_range_64_to_R in XR, YR.
    2-5: reflexivity.
    apply lt64_correct in LE.
    2: reflexivity.
    2: {
      repeat (autorewrite with rewrite_to_R;
              try reflexivity; try assumption).
      all: autounfold with const_unfold in *.
      all: gappa_form.
      all: compute_B2R; gappa.
    }

    unfold l, r in *.
    autorewrite with rewrite_to_R in *.
    all: repeat autorewrite with rewrite_to_R.
    all: autounfold with const_unfold in *.
    all: try assumption; try reflexivity.
    all: gappa_form.
    all: compute_B2R; gappa.
  Qed.

End Problem.

Definition much_lt64 (f1 f2 : binary64) :=
  lt64 b0_0 (CTypeSub (CTypeSub (CTypeSub f2 f1) eps1) eps2).

Infix "<<" := much_lt64 (at level 50).

Theorem toplevel_safe
  (x y : binary64)
  (XR : in_range_64 (b0_0, b200) x)  (* [0 <= x <= 200]  *)
  (YR : in_range_64 (b0_0, b3000) y) (* [0 <= y <= 3000] *)
  :
  (* binary64 computations *)
  let l64 := CTypeMult x x in
  let r64 := CTypeMult y y in
  (* Real values *)
  let l := (B2R _ _ x) * (B2R _ _ x) in
  let r := (B2R _ _ y) * (B2R _ _ y) in

  l64 << r64 ->
  l < r.
Proof.
  intros * MLT.
  apply safe in MLT; try assumption.
  replace l0 with (l x) by reflexivity.
  replace r0 with (r y) by reflexivity.
  compute_B2R.
  lra.
Qed.
