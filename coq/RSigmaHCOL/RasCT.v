Require Import ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Require Import Helix.MSigmaHCOL.CType.

Instance R_Equiv: Equiv R := eq.

Instance R_Setoid: Setoid R.
Proof. split; auto. Qed.

Module MRasCT <: CType.

  Definition t := R.

  Definition CTypeEquiv := R_Equiv.
  Definition CTypeSetoid := R_Setoid.

  Definition CTypeZero := R0.
  Definition CTypeOne  := R1.

  Definition CTypePlus     := Rplus.
  Definition CTypeNeg      := Ropp.
  Definition CTypeMult     := Rmult.
  Definition CTypeAbs      := Rabs.

  Definition CTypeZLess (a b: R) : R :=
    match (Rlt_dec a b) with
    | left _ => CTypeOne
    | right _ => CTypeZero
    end.

  Definition CTypeMin      := Rmin.
  Definition CTypeMax      := Rmax.
  Definition CTypeSub      := Rminus.

  Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Proof. solve_proper. Qed.

  Instance abs_proper: Proper ((=) ==> (=)) Rabs.
  Proof. solve_proper. Qed.

  Instance plus_proper: Proper ((=) ==> (=) ==> (=)) (Rplus).
  Proof. solve_proper. Qed.

  Instance sub_proper: Proper ((=) ==> (=) ==> (=)) (Rminus).
  Proof. solve_proper. Qed.

  Instance mult_proper: Proper ((=) ==> (=) ==> (=)) (Rmult).
  Proof. solve_proper. Qed.

  Instance min_proper: Proper ((=) ==> (=) ==> (=)) (Rmin).
  Proof. solve_proper. Qed.

  Instance max_proper: Proper ((=) ==> (=) ==> (=)) (Rmax).
  Proof. solve_proper. Qed.

End MRasCT.
