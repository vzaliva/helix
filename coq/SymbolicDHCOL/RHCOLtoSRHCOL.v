(* NOTE: this file is almost an exact copy of [FHCOLtoSFHCOL.v]
   up to some name changes: [s/FHCOL/RHCOL/g], [s/Int64asNT/NatAsNT/g], etc.
   Ideally these two would be merged.
 *)
Require Import ZArith Psatz List.
Require Import MathClasses.interfaces.canonical_names.
Require Import ExtLib.Structures.Monad.

Require Import Helix.Tactics.StructTactics.
Require Import Helix.Util.OptionSetoid.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

Require Import Helix.MSigmaHCOL.RasCT.
Require Import Helix.RSigmaHCOL.NatAsNT.
Require Import Helix.RSigmaHCOL.RSigmaHCOL.

Require Import Helix.SymbolicDHCOL.SymbolicCT.

Import ListNotations.

Module Export SRHCOL <: MDSigmaHCOL(MSymbolicCT)(MNatAsNT).
  Include MDSigmaHCOL MSymbolicCT MNatAsNT.
End SRHCOL.

Module Export SRHCOLEval <: MDSigmaHCOLEval(MSymbolicCT)(MNatAsNT)(SRHCOL).
  Include MDSigmaHCOLEval MSymbolicCT MNatAsNT SRHCOL.
End SRHCOLEval.

Module Export RHCOLtoSRHCOL := MDHCOLTypeTranslator
                                 (MRasCT)
                                 (MSymbolicCT)
                                 (MNatAsNT)
                                 (MNatAsNT)
                                 (RHCOL)
                                 (SRHCOL)
                                 (RHCOLEval)
                                 (SRHCOLEval).

Definition RealEnv := list MRasCT.t.

(* No use for fancier monads *)
Fixpoint evalRealSExpr (e : RealEnv) (f : SExpr) : option MRasCT.t :=
  match f with
  | SVar i       => (nth_error e i)
  | SConstZero   => Some MRasCT.CTypeZero
  | SConstOne    => Some MRasCT.CTypeOne
  | SNeg   f     =>
      liftM  MRasCT.CTypeNeg   (evalRealSExpr e f)
  | SAbs   f     =>
      liftM  MRasCT.CTypeAbs   (evalRealSExpr e f)
  | SPlus  f1 f2 =>
      liftM2 MRasCT.CTypePlus  (evalRealSExpr e f1) (evalRealSExpr e f2)
  | SMult  f1 f2 =>
      liftM2 MRasCT.CTypeMult  (evalRealSExpr e f1) (evalRealSExpr e f2)
  | SZLess f1 f2 =>
      liftM2 MRasCT.CTypeZLess (evalRealSExpr e f1) (evalRealSExpr e f2)
  | SMin   f1 f2 =>
      liftM2 MRasCT.CTypeMin   (evalRealSExpr e f1) (evalRealSExpr e f2)
  | SMax   f1 f2 =>
      liftM2 MRasCT.CTypeMax   (evalRealSExpr e f1) (evalRealSExpr e f2)
  | SSub   f1 f2 =>
      liftM2 MRasCT.CTypeSub   (evalRealSExpr e f1) (evalRealSExpr e f2)
  end.

Definition heq_Real_SExpr
  (env : RealEnv)
  (f : MRasCT.t)
  (sf : MSymbolicCT.t)
  : Prop :=
  evalRealSExpr env sf ≡ Some f.

Global Instance RSR_CHE : RHCOLtoSRHCOL.CTranslation_heq RealEnv.
Proof.
  econstructor.
  -
    instantiate (1:=heq_Real_SExpr).
    intros f1 f2 F lf1 lf2 LF.
    invc F; invc LF.
    easy.
  -
    intros * T *.
    unfold translateCTypeConst in *.
    repeat break_if; invc T.
    all: now rewrite e, <-H1.
Defined.

Global Instance RSR_COP : @RHCOLtoSRHCOL.COpTranslationProps RealEnv RSR_CHE.
Proof.
  do 2 constructor.
  all: intros * XE; try intro YE.
  all: unfold heq_CType', RSR_CHE, heq_Real_SExpr in *.
  all: cbn.
  all: now rewrite ?XE, ?YE.
Qed.

(* Trivial instances for "translating" Int64 -> Int64 *)
Instance RSR_NHE : RHCOLtoSRHCOL.NTranslation_heq.
Proof.
  econstructor.
  -
    instantiate (1:=eq).
    intros i1 i2 I i1' i2' I'.
    invc I. invc I'.
    easy.
  -
    intros * T.
    unfold translateNTypeConst, MNatAsNT.from_nat, MNatAsNT.to_nat in *.
    invc T; invc H1.
    reflexivity.
Defined.

Instance RSR_NTP : RHCOLtoSRHCOL.NTranslationProps.
Proof.
  constructor.
  -
    intros.
    unfold heq_NType, RSR_NHE in *.
    congruence.
  -
    intros.
    unfold heq_NType, RSR_NHE in *.
    destruct (MNatAsNT.from_nat n);
      repeat constructor.
Qed.

Instance RSR_NOP : RHCOLtoSRHCOL.NOpTranslationProps.
Proof.
  do 2 constructor; intros.
  all: unfold heq_NType, RSR_NHE in *.
  all: congruence.
Qed.

Lemma RHCOLtoSRHCOL_semantic_preservation
  (op : RHCOL.DSHOperator) (op' : SRHCOL.DSHOperator)
  (σ : RHCOLEval.evalContext) (σ' : evalContext)
  (imem : RHCOL.memory) (imem' : SRHCOL.memory)
  :
  forall env,
    RHCOLtoSRHCOL.heq_DSHOperator env RSR_NHE RSR_CHE op op' →
    RHCOLtoSRHCOL.heq_evalContext env RSR_NHE RSR_CHE σ σ' →
    RHCOLtoSRHCOL.heq_memory env RSR_CHE imem imem' →
    hopt_r (ErrorSetoid.herr_c (RHCOLtoSRHCOL.heq_memory env RSR_CHE))
      (RHCOLEval.evalDSHOperator σ op imem (RHCOLEval.estimateFuel op))
      (SRHCOLEval.evalDSHOperator σ' op' imem' (SRHCOLEval.estimateFuel op')).
Proof.
  intros * OPE ΣE ME.
  eapply RHCOLtoSRHCOL.translation_semantics_correct_strict.
  all: auto using RSR_NTP, RSR_NOP, RSR_COP.
Qed.
