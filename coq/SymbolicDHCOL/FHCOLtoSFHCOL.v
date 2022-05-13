Require Import ZArith Psatz List.
Require Import MathClasses.interfaces.canonical_names.
Require Import ExtLib.Structures.Monad.

Require Import Helix.Tactics.StructTactics.
Require Import Helix.Util.OptionSetoid.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.

Require Import Helix.SymbolicDHCOL.SymbolicCT.

Import ListNotations.

Module Export SFHCOL <: MDSigmaHCOL(MSymbolicCT)(MInt64asNT).
  Include MDSigmaHCOL MSymbolicCT MInt64asNT.
End SFHCOL.

Module Export SFHCOLEval <: MDSigmaHCOLEval(MSymbolicCT)(MInt64asNT)(SFHCOL).
  Include MDSigmaHCOLEval MSymbolicCT MInt64asNT SFHCOL.
End SFHCOLEval.

Module Export FHCOLtoSFHCOL := MDHCOLTypeTranslator
                                 (MFloat64asCT)
                                 (MSymbolicCT)
                                 (MInt64asNT)
                                 (MInt64asNT)
                                 (FHCOL)
                                 (SFHCOL)
                                 (FHCOLEval)
                                 (SFHCOLEval).

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

Global Instance FSF_CHE : FHCOLtoSFHCOL.CTranslation_heq FloatEnv.
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

Global Instance FSF_COP : @FHCOLtoSFHCOL.COpTranslationProps FloatEnv FSF_CHE.
Proof.
  do 2 constructor.
  all: intros * XE; try intro YE.
  all: unfold heq_CType', FSF_CHE, heq_Float_SExpr in *.
  all: cbn.
  all: now rewrite ?XE, ?YE.
Qed.

(* Trivial instances for "translating" Int64 -> Int64 *)
Instance FSF_NHE : FHCOLtoSFHCOL.NTranslation_heq.
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

Instance FSF_NTP : FHCOLtoSFHCOL.NTranslationProps.
Proof.
  constructor.
  -
    intros.
    unfold heq_NType, FSF_NHE in *.
    congruence.
  -
    intros.
    unfold heq_NType, FSF_NHE in *.
    destruct (MInt64asNT.from_nat n);
      repeat constructor.
Qed.

Instance FSF_NOP : FHCOLtoSFHCOL.NOpTranslationProps.
Proof.
  do 2 constructor; intros.
  all: unfold heq_NType, FSF_NHE in *.
  all: congruence.
Qed.

Lemma FHCOLtoSFHCOL_semantic_preservation
  (op : FHCOL.DSHOperator) (op' : SFHCOL.DSHOperator)
  (σ : FHCOLEval.evalContext) (σ' : evalContext)
  (imem : FHCOL.memory) (imem' : SFHCOL.memory)
  :
  forall env,
    FHCOLtoSFHCOL.heq_DSHOperator env FSF_NHE FSF_CHE op op' →
    FHCOLtoSFHCOL.heq_evalContext env FSF_NHE FSF_CHE σ σ' →
    FHCOLtoSFHCOL.heq_memory env FSF_CHE imem imem' →
    hopt_r (ErrorSetoid.herr_c (FHCOLtoSFHCOL.heq_memory env FSF_CHE))
      (FHCOLEval.evalDSHOperator σ op imem (FHCOLEval.estimateFuel op))
      (SFHCOLEval.evalDSHOperator σ' op' imem' (SFHCOLEval.estimateFuel op')).
Proof.
  intros * OPE ΣE ME.
  eapply FHCOLtoSFHCOL.translation_semantics_correct_strict.
  all: auto using FSF_NTP, FSF_NOP, FSF_COP.
Qed.
