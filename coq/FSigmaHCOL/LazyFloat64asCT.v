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

Inductive FloatExpr :=
| LFVar : nat -> FloatExpr
| LFConst : MFloat64asCT.t -> FloatExpr
| LFNeg   : FloatExpr -> FloatExpr
| LFAbs   : FloatExpr -> FloatExpr
| LFPlus  : FloatExpr -> FloatExpr -> FloatExpr
| LFMult  : FloatExpr -> FloatExpr -> FloatExpr
| LFZLess : FloatExpr -> FloatExpr -> FloatExpr
| LFMin   : FloatExpr -> FloatExpr -> FloatExpr
| LFMax   : FloatExpr -> FloatExpr -> FloatExpr
| LFSub   : FloatExpr -> FloatExpr -> FloatExpr.

Definition FloatEnv := list MFloat64asCT.t.

(* No use for fancier monads *)
Fixpoint evalFloatExpr (e : FloatEnv) (f : FloatExpr) : option MFloat64asCT.t :=
  match f with
  | LFVar i       => (nth_error e i)
  | LFConst b     => Some b
  | LFNeg   f     => liftM  MFloat64asCT.CTypeNeg   (evalFloatExpr e f)
  | LFAbs   f     => liftM  MFloat64asCT.CTypeAbs   (evalFloatExpr e f)
  | LFPlus  f1 f2 => liftM2 MFloat64asCT.CTypePlus  (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFMult  f1 f2 => liftM2 MFloat64asCT.CTypeMult  (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFZLess f1 f2 => liftM2 MFloat64asCT.CTypeZLess (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFMin   f1 f2 => liftM2 MFloat64asCT.CTypeMin   (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFMax   f1 f2 => liftM2 MFloat64asCT.CTypeMax   (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFSub   f1 f2 => liftM2 MFloat64asCT.CTypeSub   (evalFloatExpr e f1) (evalFloatExpr e f2)
  end.

Definition SymFloat : Type := option (FloatEnv * FloatExpr).

Definition evalSymFloat (sf : SymFloat) : option MFloat64asCT.t :=
  '(e, f) <- sf ;;
  evalFloatExpr e f.

(* TODO: evaluation might be more suitable here *)
Instance SymFloat_Equiv: Equiv SymFloat := eq.

Instance SymFloat_Setoid: Setoid SymFloat.
Proof.
  constructor.
  - now intros x.
  - now intros x y E.
  - intros x y z Exy Eyz; auto.
Qed. 

Instance SymFloat_equiv_dec: forall x y : SymFloat, Decision (x = y).
Proof.
Admitted.

Lemma evalFloatExpr_env_indep (f : FloatExpr) (b : MFloat64asCT.t) :
  evalFloatExpr nil f ≡ Some b ->
  forall e, evalFloatExpr e f ≡ Some b.
Admitted.

Definition symLiftM (c : FloatExpr -> FloatExpr) (sf : SymFloat) : SymFloat :=
  '(e, f) <- sf ;;
  Some (e, c f).
  
Definition symLiftM2
  (c : FloatExpr -> FloatExpr -> FloatExpr)
  (sf1 sf2 : SymFloat)
  : SymFloat
  :=
  sf1 <- sf1 ;;
  sf2 <- sf2 ;;
  match sf1, sf2 with
  | ([], f1), (e, f2) => Some (e, c f1 f2)
  | (e, f1), ([], f2) => Some (e, c f1 f2)
  | (e1, f1), (e2, f2) =>
      if list_eq_dec MFloat64asCT.CTypeEquivDec e1 e2
      then Some (e1, c f1 f2)
      else None
  end.

Module MLazyFloat64asCT <: CType.

  Definition t := SymFloat.

  Definition CTypeEquiv := SymFloat_Equiv.
  Definition CTypeSetoid := SymFloat_Setoid.

  Definition CTypeZero : SymFloat := Some ([], LFConst MFloat64asCT.CTypeZero).
  Definition CTypeOne : SymFloat := Some ([], LFConst MFloat64asCT.CTypeOne).

  Lemma CTypeZeroOneApart: CTypeZero ≠ CTypeOne.
  Proof.
    discriminate.
  Qed.

  Definition CTypeEquivDec := SymFloat_equiv_dec.

  Definition CTypeNeg      := symLiftM LFNeg.
  Definition CTypeAbs      := symLiftM LFAbs.
  Definition CTypePlus     := symLiftM2 LFPlus.
  Definition CTypeMult     := symLiftM2 LFMult.
  Definition CTypeZLess    := symLiftM2 LFZLess.
  Definition CTypeMin      := symLiftM2 LFMin.
  Definition CTypeMax      := symLiftM2 LFMax.
  Definition CTypeSub      := symLiftM2 LFSub.

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
