Require Import ZArith.
From Flocq Require Import Binary Bits.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.MSigmaHCOL.CType.

(* Defining these before importing math classes to avoid name collisions,
   e.g. on [Lt] *)
Section MinMax.

  Definition Float64Min (a b: binary64) :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
    | _, _ =>
      match Bcompare _ _ a b with
      | Some Datatypes.Lt => a
      | _ => b
      end
    end.

  Definition Float64Max (a b: binary64): binary64 :=
    match a, b with
    | B754_nan _ _ _ _ _, _ | _, B754_nan _ _ _ _ _ => build_nan _ _ (binop_nan_pl64 a b)
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

Definition Float64Zero : binary64 := B754_zero _ _ false.
Program Definition Float64One : binary64 := Bone _ _ eq_refl eq_refl.

Instance binary64_Equiv: Equiv binary64 := eq.

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

  Definition CTypeZero := Float64Zero.
  Definition CTypeOne  := Float64One.

  Definition CTypePlus     := b64_plus FT_Rounding.
  Definition CTypeNeg      := b64_opp.
  Definition CTypeMult     := b64_mult FT_Rounding.
  Definition CTypeAbs      := b64_abs.

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

  Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Proof. solve_proper. Qed.

  Definition abs_proper: Proper ((=) ==> (=)) b64_abs.
  Proof. solve_proper. Qed.

  Definition plus_proper: Proper ((=) ==> (=) ==> (=)) (b64_plus FT_Rounding).
  Proof. solve_proper. Qed.

  Definition sub_proper: Proper ((=) ==> (=) ==> (=)) (b64_minus FT_Rounding).
  Proof. solve_proper. Qed.

  Definition mult_proper: Proper ((=) ==> (=) ==> (=)) (b64_mult FT_Rounding).
  Proof. solve_proper. Qed.

  Definition min_proper: Proper ((=) ==> (=) ==> (=)) (Float64Min).
  Proof. solve_proper. Qed.

  Definition max_proper: Proper ((=) ==> (=) ==> (=)) (Float64Max).
  Proof. solve_proper. Qed.

End MFloat64asCT.
