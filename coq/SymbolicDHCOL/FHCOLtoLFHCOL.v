Require Import Helix.Tactics.StructTactics.
Require Import Helix.Util.OptionSetoid.

Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.LazyFloat64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

Require Import MathClasses.interfaces.canonical_names.
Require Import ZArith String Psatz.

Require Import ExtLib.Structures.Monad.

Module Export FHCOLtoLFHCOL := MDHCOLTypeTranslator
                                 (MFloat64asCT)
                                 (MLazyFloat64asCT)
                                 (MInt64asNT)
                                 (MInt64asNT)
                                 (FHCOL)
                                 (LFHCOL)
                                 (FHCOLEval)
                                 (LFHCOLEval).

(*
Definition FloatEnv := list MFloat64asCT.t.

(* No use for fancier monads *)
Fixpoint evalFloatExpr (e : FloatEnv) (f : FloatExpr) : option MFloat64asCT.t :=
  match f with
  | LFVar i       => (nth_error e i)
  | LFConst b     => Some b
  | LFNeg   f     =>
      liftM  MFloat64asCT.CTypeNeg   (evalFloatExpr e f)
  | LFAbs   f     =>
      liftM  MFloat64asCT.CTypeAbs   (evalFloatExpr e f)
  | LFPlus  f1 f2 =>
      liftM2 MFloat64asCT.CTypePlus  (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFMult  f1 f2 =>
      liftM2 MFloat64asCT.CTypeMult  (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFZLess f1 f2 =>
      liftM2 MFloat64asCT.CTypeZLess (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFMin   f1 f2 =>
      liftM2 MFloat64asCT.CTypeMin   (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFMax   f1 f2 =>
      liftM2 MFloat64asCT.CTypeMax   (evalFloatExpr e f1) (evalFloatExpr e f2)
  | LFSub   f1 f2 =>
      liftM2 MFloat64asCT.CTypeSub   (evalFloatExpr e f1) (evalFloatExpr e f2)
  end.
*)

Definition heq_Float_SymFloat
  (env : FloatEnv)
  (f : MFloat64asCT.t)
  (sf : MLazyFloat64asCT.t)
  : Prop :=
  evalFloatExpr env sf ≡ Some f.

Global Instance FLF_CHE : FHCOLtoLFHCOL.CTranslation_heq FloatEnv.
Proof.
  econstructor.
  -
    instantiate (1:=heq_Float_SymFloat).
    intros f1 f2 F lf1 lf2 LF.
    invc F; invc LF.
    easy.
  -
    intros * T *.
    unfold translateCTypeConst in *.
    repeat break_if; invc T.
    all: now rewrite e, <-H1.
Defined.

Global Instance FLF_COP : @FHCOLtoLFHCOL.COpTranslationProps FloatEnv FLF_CHE.
Proof.
  do 2 constructor.
  all: intros * XE; try intro YE.
  all: unfold heq_CType', FLF_CHE, heq_Float_SymFloat in *.
  all: cbn.
  all: now rewrite ?XE, ?YE.
Qed.

(* Trivial instances for "translating" Int64 -> Int64 *)
Instance FLF_NHE : FHCOLtoLFHCOL.NTranslation_heq.
Proof.
  econstructor.
  -
    instantiate (1:=eq).
    intros i1 i2 I i1' i2' I'.
    invc I. invc I'.

    pose proof Int64.eq_spec i1 i2 as I.
    rewrite H0 in I.
    subst.

    pose proof Int64.eq_spec i1' i2' as I'.
    rewrite H1 in I'.
    subst.

    easy.
  -
    intros * T.
    unfold translateNTypeConst, MInt64asNT.from_nat, MInt64asNT.to_nat in *.
    rewrite Znat.Z2Nat.id in *
      by (pose proof Integers.Int64.intrange x; lia).

    unfold MInt64asNT.from_Z in *.
    repeat break_match; invc T.
    pose proof Int64.eq_spec
               {| Int64.intval := Int64.intval x; Int64.intrange := conj l l0 |}
               x'.
    rewrite H1 in H.
    clear H1.
    rewrite <-H.
    destruct x.
    f_equal.
    apply proof_irrelevance.
Defined.

Instance FLF_NTP : FHCOLtoLFHCOL.NTranslationProps.
Proof.
  constructor.
  -
    intros.
    unfold heq_NType, FLF_NHE in *.
    congruence.
  -
    intros.
    unfold heq_NType, FLF_NHE in *.
    destruct (MInt64asNT.from_nat n);
      repeat constructor.
Qed.

Instance FLF_NOP : FHCOLtoLFHCOL.NOpTranslationProps.
Proof.
  do 2 constructor; intros.
  all: unfold heq_NType, FLF_NHE in *.
  all: congruence.
Qed.
