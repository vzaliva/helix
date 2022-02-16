Require Import ZArith.
Require Import Coq.Bool.Bool.

From Flocq Require Import Binary Bits.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.MSigmaHCOL.CType.

(* Defining these before importing math classes to avoid name collisions,
   e.g. on [Lt] *)
Section MinMax.

  Definition Float32Min (a b: binary32) :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      match Bcompare _ _ a b with
      | Some Datatypes.Lt => a
      | _ => b
      end
    end.

  Definition Float32Max (a b: binary32): binary32 :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl32 a b)
    | _, _ =>
      match Bcompare _ _ a b with
      | Some Datatypes.Lt => b
      | _ => a
      end
    end.

End MinMax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Definition FT_Rounding:mode := mode_NE.

Require Import Coq.micromega.Lia.

Definition Float32Zero : binary32 := B754_zero _ _ false.
Program Definition Float32One : binary32 := Bone _ _ eq_refl eq_refl.

Instance binary32_Equiv: Equiv binary32 := eq.

(* Should be somewhere in stdlib but I could not find it *)
Lemma positive_dec : forall p1 p2 : positive, {p1 ≡ p2} + {p1 ≢ p2}.
Proof.
  decide equality.
Defined.

Instance binary32_equiv_dec: forall x y: binary32, Decision (x = y).
Proof.
  intros.
  unfold Decision, equiv, binary32_Equiv.
  unfold binary32 in *.

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


Instance binary32_Setoid: Setoid binary32.
Proof.
  split.
  -
    intros x.
    unfold equiv, binary32_Equiv.
    reflexivity.
  -
    intros x y E.
    unfold equiv, binary32_Equiv in *.
    auto.
  -
    intros x y z Exy Eyz.
    unfold equiv, binary32_Equiv in *.
    rewrite Exy, Eyz.
    reflexivity.
Qed.

Module MFloat32asCT <: CType.

  Definition t := binary32.

  Definition CTypeEquiv := binary32_Equiv.
  Definition CTypeSetoid := binary32_Setoid.

  Definition CTypeZero := Float32Zero.
  Definition CTypeOne  := Float32One.

  Lemma CTypeZeroOneApart: Float32Zero ≠ Float32One.
  Proof.
    unfold Float32Zero, Float32One.
    intros H.
    inversion H.
  Qed.

  Definition CTypeEquivDec := binary32_equiv_dec.

  Definition CTypePlus     := b32_plus FT_Rounding.
  Definition CTypeNeg      := b32_opp.
  Definition CTypeMult     := b32_mult FT_Rounding.
  Definition CTypeAbs      := b32_abs.

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
  Definition CTypeZLess (a b: binary32) : binary32 :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => CTypeZero
    | _, _ =>
      match Bcompare _ _ a b with
      | Some Datatypes.Lt => CTypeOne
      | _ => CTypeZero
      end
    end.

  (* Quick test that definitoin we have is indeed different from
     directly using [Bcompare]:

  Definition CTypeZLess' (a b: binary32) : binary32 :=
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

  Definition CTypeMin      := Float32Min.
  Definition CTypeMax      := Float32Max.
  Definition CTypeSub      := b32_minus FT_Rounding.

  Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Proof. solve_proper. Qed.

  Instance abs_proper: Proper ((=) ==> (=)) b32_abs.
  Proof. solve_proper. Qed.

  Instance plus_proper: Proper ((=) ==> (=) ==> (=)) (b32_plus FT_Rounding).
  Proof. solve_proper. Qed.

  Instance sub_proper: Proper ((=) ==> (=) ==> (=)) (b32_minus FT_Rounding).
  Proof. solve_proper. Qed.

  Instance mult_proper: Proper ((=) ==> (=) ==> (=)) (b32_mult FT_Rounding).
  Proof. solve_proper. Qed.

  Instance min_proper: Proper ((=) ==> (=) ==> (=)) (Float32Min).
  Proof. solve_proper. Qed.

  Instance max_proper: Proper ((=) ==> (=) ==> (=)) (Float32Max).
  Proof. solve_proper. Qed.

End MFloat32asCT.
