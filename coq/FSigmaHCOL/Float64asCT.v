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

  Definition Float64Lt (a b: binary64) : Prop :=
    match (Bcompare _ _ a b) with
    | Some Datatypes.Lt => True
    | _ => False
    end.

  (* needed for Zless *)
  Instance Float64LtDec: forall x y: binary64, Decision (Float64Lt x y).
  Proof.
    intros x y.
    unfold Float64Lt.
    destruct (Bcompare 53 1024 x y).
    -
      destruct c; solve_trivial_decision.
    -
      solve_trivial_decision.
  Qed.

End MinMax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Definition FT_Rounding:mode := mode_NE.

Require Import Omega.

Definition Float64Zero : binary64 := B754_zero _ _ false.
Program Definition Float64One : binary64 := Bone _ _ _ _ .
Next Obligation. unfold FLX.Prec_gt_0. omega. Qed.
Next Obligation. omega. Qed.

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
  Definition CTypeOne := Float64One.

  Definition CTypePlus     := b64_plus FT_Rounding.
  Definition CTypeNeg      := b64_opp.
  Definition CTypeMult     := b64_mult FT_Rounding.


  Definition CTypeAbs      := b64_abs.
  Definition CTypeZLess (a b: binary64) :=
    if Float64LtDec a b then CTypeOne else CTypeZero.

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
