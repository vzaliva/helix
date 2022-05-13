Require Import ZArith Bool String.

From Flocq Require Import Binary Bits.

Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.Tactics.StructTactics.

Require Import Float64asCT.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import List.
Import ListNotations.
Import MonadNotation.

Open Scope monad_scope.
Open Scope string_scope.

Inductive SExpr :=
| SConstZero : SExpr
| SConstOne  : SExpr
| SVar       : nat -> SExpr
| SNeg       : SExpr -> SExpr
| SAbs       : SExpr -> SExpr
| SPlus      : SExpr -> SExpr -> SExpr
| SMult      : SExpr -> SExpr -> SExpr
| SZLess     : SExpr -> SExpr -> SExpr
| SMin       : SExpr -> SExpr -> SExpr
| SMax       : SExpr -> SExpr -> SExpr
| SSub       : SExpr -> SExpr -> SExpr.

(* TODO: evaluation might be more suitable here *)
Instance SExpr_Equiv: Equiv SExpr := eq.

Instance SExpr_Setoid: Setoid SExpr.
Proof.
  constructor.
  - now intros x.
  - now intros x y E.
  - intros x y z Exy Eyz; auto.
Qed. 

Instance SExpr_equiv_dec: forall x y : SExpr, Decision (x = y).
Proof.
  intros.
  unfold Decision.
  generalize dependent y.
  induction x; intros.
  all: destruct y.
  all: try (left; reflexivity); try (right; discriminate).

  1: destruct (Nat.eq_dec n n0); [left | right]; congruence.

  1,2: specialize (IHx y).
  1,2: destruct IHx; [left | right]; congruence.

  all: specialize (IHx1 y1); specialize (IHx2 y2).
  all: destruct IHx1, IHx2; [left | right | right | right]; congruence.
Qed.    

Module MSymbolicCT <: CType.

  Definition t := SExpr.

  Definition CTypeEquiv := SExpr_Equiv.
  Definition CTypeSetoid := SExpr_Setoid.

  Definition CTypeZero : SExpr := SConstZero.
  Definition CTypeOne : SExpr := SConstOne.

  Lemma CTypeZeroOneApart: CTypeZero ≠ CTypeOne.
  Proof.
    discriminate.
  Qed.

  Definition CTypeEquivDec := SExpr_equiv_dec.

  Definition CTypeNeg   := SNeg.
  Definition CTypeAbs   := SAbs.
  Definition CTypePlus  := SPlus.
  Definition CTypeMult  := SMult.
  Definition CTypeZLess := SZLess.
  Definition CTypeMin   := SMin.
  Definition CTypeMax   := SMax.
  Definition CTypeSub   := SSub.

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

End MSymbolicCT.
