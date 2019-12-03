(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import ZArith.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.Float64AasCT.

(* Defining these before importing math classes to avoid name collisions,
   e.g. on [Lt] *)
Section MinMax.

  (* TODO: Implement semantics as in LLVM:
     https://llvm.org/docs/LangRef.html#llvm-minimum-intrinsic
   *)
  Definition Float64Min (a b: binary64): binary64. Admitted.

  (* TODO: Implement IEEE-754 semantics for `maxNum` except for the
     handling of signaling `NaNs`. This matches the behavior of libm’s
     `fmax`.

     https://llvm.org/docs/LangRef.html#llvm-maxnum-intrinsic

   *)
  Definition Float64Max (a b: binary64): binary64. Admitted.

  Definition Float64Le (a b: binary64) : Prop :=
    match (Bcompare _ _ a b) with
    | Some Eq => True
    | Some Lt => True
    | _ => False
    end.

  Definition Float64Lt (a b: binary64) : Prop :=
    match (Bcompare _ _ a b) with
    | Some Lt => True
    | _ => False
    end.

End MinMax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Definition FT_Rounding:mode := mode_NE.

Definition Float64Zero : binary64 := B754_zero _ _ false.
Program Definition Float64One : binary64 := Bone _ _ _ _ .
Next Obligation. unfold FLX.Prec_gt_0. omega. Qed.
Next Obligation. omega. Qed.

Module MDSigmaHCOLEvalSigFloat64 <: MDSigmaHCOLEvalSig(MFloat64AasCT).
  Import MFloat64AasCT.

  Definition CTypeZero := Float64Zero.
  Definition CTypeOne := Float64One.

  Definition CTypePlus     := b64_plus FT_Rounding.
  Definition CTypeNeg      := b64_opp.
  Definition CTypeMult     := b64_mult FT_Rounding.
  Definition CTypeLe       := Float64Le.
  Definition CTypeLt       := Float64Lt.

  Instance CTypeLeDec: forall x y: t, Decision (Float64Le x y).
  Proof.
    intros x y.
    unfold Float64Le.
    destruct (Bcompare 53 1024 x y).
    -
      destruct c; solve_trivial_decision.
    -
      solve_trivial_decision.
  Qed.

  (* needed for Zless *)
  Instance CTypeLtDec: forall x y: t, Decision (Float64Lt x y).
  Proof.
    intros x y.
    unfold Float64Lt.
    destruct (Bcompare 53 1024 x y).
    -
      destruct c; solve_trivial_decision.
    -
      solve_trivial_decision.
  Qed.

  Definition CTypeAbs      := b64_abs.
  Definition CTypeZLess (a b: binary64) :=
    if CTypeLtDec a b then CTypeOne else CTypeZero.

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

End MDSigmaHCOLEvalSigFloat64.

Module Export MDSHCOLOnFloat64 := MDSigmaHCOLEval(MFloat64AasCT)(MDSigmaHCOLEvalSigFloat64).
