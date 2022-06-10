Require Import ZArith.
Require Import Coq.Bool.Bool.

From Flocq Require Import Binary Bits.

Require Import Helix.Util.FloatUtil.
Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.MSigmaHCOL.CType.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Definition FT_Rounding:mode := mode_NE.

Require Import Coq.micromega.Lia.

Instance binary64_Equiv: Equiv binary64 := eq.

(* TODO: rename to something like [DynWin_safety_margin] *)
(* The amount by which two numbers need to differ
   to be considered "clearly" unequal *)
(* ~ 1.2e-12 *)
Definition epsilon : binary64 :=
  B754_finite 53 1024 false 5920039297100023 (-92)
    (binary_float_of_bits_aux_correct 52 11 eq_refl eq_refl eq_refl
       4428454873374927095).

(* Should be somewhere in stdlib but I could not find it *)
Lemma positive_dec : forall p1 p2 : positive, {p1 ≡ p2} + {p1 ≢ p2}.
Proof.
  decide equality.
Defined.

Instance binary64_equiv_dec: forall x y: binary64, Decision (x = y).
Proof.
  intros.
  unfold Decision, equiv, binary64_Equiv.
  unfold binary64 in *.

  destruct x,y; try (right; unfold not; intros C; inversion C; reflexivity).
  1,2:
    destruct (bool_dec s s0) as [HB|NB] ;
    [left; subst; reflexivity| right; contradict NB; inversion NB; auto].
  -
    destruct (bool_dec s s0) as [HB|NB].
    +
      subst.
      destruct (positive_dec pl pl0) as [HP|NP].
      *
        left; subst; f_equiv; apply proof_irrelevance.
      *
        right; contradict NP; inversion NP; auto.
    +
      right; contradict NB; inversion NB; auto.
  -
    destruct (bool_dec s s0) as [HB|NB], (Z.eq_dec e e1) as [HZ|NZ], (positive_dec m m0) as [HP|NP]; subst; try (replace e0 with e2 by (apply proof_irrelevance); clear e0).
    + left; reflexivity.
    + right; contradict NP; inversion NP; auto.
    + right; contradict NZ; inversion NZ; auto.
    + right; contradict NZ; inversion NZ; auto.
    + right; contradict NB; inversion NB; auto.
    + right; contradict NB; inversion NB; auto.
    + right; contradict NB; inversion NB; auto.
    + right; contradict NB; inversion NB; auto.
Qed.


Instance binary64_Setoid: Setoid binary64.
Proof.
  split.
  -
    intros x.
    unfold equiv, binary64_Equiv.
    reflexivity.
  -
    intros x y E.
    unfold equiv, binary64_Equiv in *.
    auto.
  -
    intros x y z Exy Eyz.
    unfold equiv, binary64_Equiv in *.
    rewrite Exy, Eyz.
    reflexivity.
Qed.

Module MFloat64asCT <: CType.

  Definition t := binary64.

  Definition CTypeEquiv := binary64_Equiv.
  Definition CTypeSetoid := binary64_Setoid.

  Definition CTypeZero := b64_0.
  Definition CTypeOne  := b64_1.

  Lemma CTypeZeroOneApart: CTypeZero <> CTypeOne.
  Proof.
    discriminate.
  Qed.

  Definition CTypeEquivDec := binary64_equiv_dec.

  Definition CTypePlus     := b64_plus FT_Rounding.
  Definition CTypeNeg      := b64_opp.
  Definition CTypeMult     := b64_mult FT_Rounding.
  Definition CTypeAbs      := b64_abs.

  (* Quick test that definitoin we have is indeed different from
     directly using [Bcompare]:

  Definition CTypeZLess' (a b: binary64) : binary64 :=
    match Bcompare _ _ a b with
    | Some Datatypes.Lt => CTypeOne
      | _ => CTypeZero
    end.

  Require Import HelixTactics.
  Lemma Foo: forall a b, CTypeZLess' a b ≡ CTypeZLess a b.
  Proof.
    intros.
    unfold CTypeZLess, CTypeZLess'.
    repeat break_match; auto; try reflexivity.
    (* could not be proven. *)
  Qed.
   *)

  Definition CTypeMin      := Float64Min.
  Definition CTypeMax      := Float64Max.
  Definition CTypeSub      := b64_minus FT_Rounding.

  (* For "regular" floating point numbers the comparison is
    straighforward. However we need to handle NaNs. From point of
    view of DHCOL<->FHCOL semantics equivalence, NaNs does not matter,
    as we are going to constant the proof to input data which does not
    contain NaNs and furthermore prove that NaNs will not appear as
    result of any internal computations. So any NaN behaviour will do.

    To simplify FHCOL->IR compiler proofs we will chose to handle NaNs
    as similiar as possible as it is done in [fcmp olt] instruction
    which this one is compiled to. Per IR spec it "yields true if both
    operands are not a QNAN and op1 is less than op2"
  *)
  Definition CTypeZLess (a b: binary64) : binary64 :=
    match Bcompare _ _ epsilon (CTypeSub b a)  with
    | Some Datatypes.Lt => CTypeOne
    | _ => CTypeZero
    end.

  Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Proof. solve_proper. Qed.

  Instance abs_proper: Proper ((=) ==> (=)) b64_abs.
  Proof. solve_proper. Qed.

  Instance plus_proper: Proper ((=) ==> (=) ==> (=)) (b64_plus FT_Rounding).
  Proof. solve_proper. Qed.

  Instance sub_proper: Proper ((=) ==> (=) ==> (=)) (b64_minus FT_Rounding).
  Proof. solve_proper. Qed.

  Instance mult_proper: Proper ((=) ==> (=) ==> (=)) (b64_mult FT_Rounding).
  Proof. solve_proper. Qed.

  Instance min_proper: Proper ((=) ==> (=) ==> (=)) (Float64Min).
  Proof. solve_proper. Qed.

  Instance max_proper: Proper ((=) ==> (=) ==> (=)) (Float64Max).
  Proof. solve_proper. Qed.

End MFloat64asCT.

Declare Scope Float64asCT_scope.

Notation "0.0" := MFloat64asCT.CTypeZero : Float64asCT_scope.
Notation "1.0" := MFloat64asCT.CTypeOne : Float64asCT_scope.
Infix "⊞" := MFloat64asCT.CTypePlus (at level 50) : Float64asCT_scope.
Infix "⊠" := MFloat64asCT.CTypeMult (at level 40) : Float64asCT_scope.
Infix "⊟" := MFloat64asCT.CTypeSub  (at level 50) : Float64asCT_scope.
Infix "⧄" := (b64_div FT_Rounding)  (at level 30) : Float64asCT_scope.
Notation fmax := (MFloat64asCT.CTypeMax).
Notation fabs := (MFloat64asCT.CTypeAbs).
Notation B64R := (B2R 53 1024).
Notation "◻ x" := (round64 FT_Rounding x) (at level 0) : Float64asCT_scope.

Global Hint Unfold
  MFloat64asCT.CTypePlus
  MFloat64asCT.CTypeMult
  MFloat64asCT.CTypeSub
  MFloat64asCT.CTypeAbs
  MFloat64asCT.CTypeZero
  MFloat64asCT.CTypeOne : unfold_FCT.

Open Scope Float64asCT_scope.

Lemma fmaxZeroAbs :
  forall x, fmax 0.0 (fabs x) ≡ fabs x.
Proof.
  intros x.
  unfold fmax, fabs, Float64Max, b64_abs, Babs.
  destruct x.
  all: reflexivity.
Qed.
