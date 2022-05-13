Require Import Helix.Tactics.StructTactics.
Require Import Helix.Util.OptionSetoid.

Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.

Require Import Helix.SymbolicDHCOL.SymbolicCT.
Require Import Helix.RSigmaHCOL.NatAsNT.
Require Import Helix.SymbolicDHCOL.SDHCOL.

Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

Require Import MathClasses.interfaces.canonical_names.
Require Import ZArith String Psatz.

Require Import List.
Require Import ExtLib.Structures.Monad.

Import ListNotations.

Module Export FHCOLtoSDHCOL := MDHCOLTypeTranslator
                                 (MFloat64asCT)
                                 (MSymbolicCT)
                                 (MInt64asNT)
                                 (MNatAsNT)
                                 (FHCOL)
                                 (SDHCOL)
                                 (FHCOLEval)
                                 (SDHCOLEval).

Definition FloatEnv := list MFloat64asCT.t.

(* No use for fancier monads *)
Fixpoint evalFloatSExpr (e : FloatEnv) (f : SExpr) : option MFloat64asCT.t :=
  match f with
  | SVar i       => (nth_error e i)
  | SConstZero   => Some MFloat64asCT.CTypeZero
  | SConstOne    => Some MFloat64asCT.CTypeOne
  | SNeg   f     =>
      liftM  MFloat64asCT.CTypeNeg   (evalFloatSExpr e f)
  | SAbs   f     =>
      liftM  MFloat64asCT.CTypeAbs   (evalFloatSExpr e f)
  | SPlus  f1 f2 =>
      liftM2 MFloat64asCT.CTypePlus  (evalFloatSExpr e f1) (evalFloatSExpr e f2)
  | SMult  f1 f2 =>
      liftM2 MFloat64asCT.CTypeMult  (evalFloatSExpr e f1) (evalFloatSExpr e f2)
  | SZLess f1 f2 =>
      liftM2 MFloat64asCT.CTypeZLess (evalFloatSExpr e f1) (evalFloatSExpr e f2)
  | SMin   f1 f2 =>
      liftM2 MFloat64asCT.CTypeMin   (evalFloatSExpr e f1) (evalFloatSExpr e f2)
  | SMax   f1 f2 =>
      liftM2 MFloat64asCT.CTypeMax   (evalFloatSExpr e f1) (evalFloatSExpr e f2)
  | SSub   f1 f2 =>
      liftM2 MFloat64asCT.CTypeSub   (evalFloatSExpr e f1) (evalFloatSExpr e f2)
  end.

Definition heq_Float_SExpr
  (env : FloatEnv)
  (f : MFloat64asCT.t)
  (sf : MSymbolicCT.t)
  : Prop :=
  evalFloatSExpr env sf ≡ Some f.

Global Instance FS_CHE : FHCOLtoSDHCOL.CTranslation_heq FloatEnv.
Proof.
  econstructor.
  -
    instantiate (1:=heq_Float_SExpr).
    intros f1 f2 F lf1 lf2 LF.
    invc F; invc LF.
    easy.
  -
    intros * T *.
    unfold translateCTypeConst in *.
    repeat break_if; invc T.
    all: now rewrite e, <-H1.
Defined.

Global Instance FS_COP : @FHCOLtoSDHCOL.COpTranslationProps FloatEnv FS_CHE.
Proof.
  do 2 constructor.
  all: intros * XE; try intro YE.
  all: unfold heq_CType', FS_CHE, heq_Float_SExpr in *.
  all: cbn.
  all: now rewrite ?XE, ?YE.
Qed.

(* Trivial instances for "translating" Int64 -> Int64 *)
(*
Instance FS_NHE : FHCOLtoSDHCOL.NTranslation_heq.
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

Instance FS_NTP : FHCOLtoSDHCOL.NTranslationProps.
Proof.
  constructor.
  -
    intros.
    unfold heq_NType, FS_NHE in *.
    congruence.
  -
    intros.
    unfold heq_NType, FS_NHE in *.
    destruct (MInt64asNT.from_nat n);
      repeat constructor.
Qed.

Instance FS_NOP : FHCOLtoSDHCOL.NOpTranslationProps.
Proof.
  do 2 constructor; intros.
  all: unfold heq_NType, FS_NHE in *.
  all: congruence.
Qed.
*)
