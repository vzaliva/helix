Require Import ZArith.
Require Import Coq.Bool.Bool.

From Flocq Require Import Binary Bits.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.MSigmaHCOL.CType.

Require Import Float64asCT.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Inductive FloatExpr :=
| LFConst : MFloat64asCT.t -> FloatExpr
| LFNeg   : FloatExpr -> FloatExpr
| LFAbs   : FloatExpr -> FloatExpr
| LFPlus  : FloatExpr -> FloatExpr -> FloatExpr
| LFMult  : FloatExpr -> FloatExpr -> FloatExpr
| LFZLess : FloatExpr -> FloatExpr -> FloatExpr
| LFMin   : FloatExpr -> FloatExpr -> FloatExpr
| LFMax   : FloatExpr -> FloatExpr -> FloatExpr
| LFSub   : FloatExpr -> FloatExpr -> FloatExpr.

Fixpoint evalFloatExpr (f : FloatExpr) : MFloat64asCT.t :=
  match f with
  | LFConst b => b
  | LFNeg   f     => MFloat64asCT.CTypeNeg   (evalFloatExpr f)
  | LFAbs   f     => MFloat64asCT.CTypeAbs   (evalFloatExpr f)
  | LFPlus  f1 f2 => MFloat64asCT.CTypePlus  (evalFloatExpr f1) (evalFloatExpr f2)
  | LFMult  f1 f2 => MFloat64asCT.CTypeMult  (evalFloatExpr f1) (evalFloatExpr f2)
  | LFZLess f1 f2 => MFloat64asCT.CTypeZLess (evalFloatExpr f1) (evalFloatExpr f2)
  | LFMin   f1 f2 => MFloat64asCT.CTypeMin   (evalFloatExpr f1) (evalFloatExpr f2)
  | LFMax   f1 f2 => MFloat64asCT.CTypeMax   (evalFloatExpr f1) (evalFloatExpr f2)
  | LFSub   f1 f2 => MFloat64asCT.CTypeSub   (evalFloatExpr f1) (evalFloatExpr f2)
  end.

(* TODO: evaluation might be more suitable here *)
Instance FloatExpr_Equiv: Equiv FloatExpr := eq.

Instance FloatExpr_Setoid: Setoid FloatExpr.
Proof.
  constructor.
  - now intros x.
  - now intros x y E.
  - intros x y z Exy Eyz; auto.
Qed.

Instance FloatExpr_equiv_dec: forall x y : FloatExpr, Decision (x = y).
Proof.
Admitted.

Module MLazyFloat64asCT <: CType.

  Definition t := FloatExpr.

  Definition CTypeEquiv := FloatExpr_Equiv.
  Definition CTypeSetoid := FloatExpr_Setoid.

  Definition CTypeZero := LFConst MFloat64asCT.CTypeZero.
  Definition CTypeOne  := LFConst MFloat64asCT.CTypeOne.

  Lemma CTypeZeroOneApart: CTypeZero ≠ CTypeOne.
  Proof.
    discriminate.
  Qed.

  Definition CTypeEquivDec := FloatExpr_equiv_dec.

  Definition CTypePlus     := LFPlus.
  Definition CTypeNeg      := LFNeg.
  Definition CTypeMult     := LFMult.
  Definition CTypeAbs      := LFAbs.
  Definition CTypeZLess    := LFZLess.
  Definition CTypeMin      := LFMin.
  Definition CTypeMax      := LFMax.
  Definition CTypeSub      := LFSub.

  Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Proof. solve_proper. Qed.

  Instance abs_proper: Proper ((=) ==> (=)) CTypeAbs.
  Proof. solve_proper. Qed.

  Instance plus_proper: Proper ((=) ==> (=) ==> (=)) CTypePlus.
  Proof. solve_proper. Qed.

  Instance sub_proper: Proper ((=) ==> (=) ==> (=)) CTypeSub.
  Proof. solve_proper. Qed.

  Instance mult_proper: Proper ((=) ==> (=) ==> (=)) CTypeMult.
  Proof. solve_proper. Qed.

  Instance min_proper: Proper ((=) ==> (=) ==> (=)) CTypeMin.
  Proof. solve_proper. Qed.

  Instance max_proper: Proper ((=) ==> (=) ==> (=)) CTypeMax.
  Proof. solve_proper. Qed.

End MLazyFloat64asCT.
