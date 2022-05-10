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

Inductive heq_Float_SymFloat : MFloat64asCT.t -> MLazyFloat64asCT.t -> Prop :=
| heq_FSF_Some : forall f sf,
    evalSymFloat sf ≡ Some f -> heq_Float_SymFloat f sf
| heq_FSF_None : forall f, heq_Float_SymFloat f None.

Global Instance FLF_CHE : FHCOLtoLFHCOL.CTranslation_heq.
Proof.
  econstructor.
  -
    instantiate (1:=heq_Float_SymFloat).
    intros f1 f2 F lf1 lf2 LF.
    invc F; invc LF.
    easy.
  -
    intros * T.
    unfold translateCTypeConst in *.
    repeat break_if; invc T.
    all: rewrite e.
    all: constructor.
    all: now rewrite <-H1.
Defined.

Global Instance FLF_COP : @FHCOLtoLFHCOL.COpTranslationProps FLF_CHE.
Proof.
  do 2 constructor.
  all: intros * XE; try intro YE.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst;
      inversion YE as [t1 t2 EY t3 t4| t1 t2 EY]; clear YE; subst.
    2-4: cbn; repeat break_match; constructor 2.
    destruct x' as [[xe xf] |],
             y' as [[ye yf] |]; try some_none.
    all: cbn in *.
    2-4: constructor 2.
    all: destruct (List.list_eq_dec MFloat64asCT.CTypeEquivDec xe ye)
      as [EEQ | ENEQ].
    all: repeat break_match; subst.
    6: constructor 2.
    all: constructor; cbn.
    all: rewrite ?EX, ?EY.
    all: try erewrite evalFloatExpr_env_indep by eassumption.
    all: try reflexivity.
    now rewrite EEQ, EY.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst;
      inversion YE as [t1 t2 EY t3 t4| t1 t2 EY]; clear YE; subst.
    2-4: cbn; repeat break_match; constructor 2.
    destruct x' as [[xe xf] |],
             y' as [[ye yf] |]; try some_none.
    all: cbn in *.
    2-4: constructor 2.
    all: destruct (List.list_eq_dec MFloat64asCT.CTypeEquivDec xe ye)
      as [EEQ | ENEQ].
    all: repeat break_match; subst.
    6: constructor 2.
    all: constructor; cbn.
    all: rewrite ?EX, ?EY.
    all: try erewrite evalFloatExpr_env_indep by eassumption.
    all: try reflexivity.
    now rewrite EEQ, EY.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst;
      inversion YE as [t1 t2 EY t3 t4| t1 t2 EY]; clear YE; subst.
    2-4: cbn; repeat break_match; constructor 2.
    destruct x' as [[xe xf] |],
             y' as [[ye yf] |]; try some_none.
    all: cbn in *.
    2-4: constructor 2.
    all: destruct (List.list_eq_dec MFloat64asCT.CTypeEquivDec xe ye)
      as [EEQ | ENEQ].
    all: repeat break_match; subst.
    6: constructor 2.
    all: constructor; cbn.
    all: rewrite ?EX, ?EY.
    all: try erewrite evalFloatExpr_env_indep by eassumption.
    all: try reflexivity.
    now rewrite EEQ, EY.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst;
      inversion YE as [t1 t2 EY t3 t4| t1 t2 EY]; clear YE; subst.
    2-4: cbn; repeat break_match; constructor 2.
    destruct x' as [[xe xf] |],
             y' as [[ye yf] |]; try some_none.
    all: cbn in *.
    2-4: constructor 2.
    all: destruct (List.list_eq_dec MFloat64asCT.CTypeEquivDec xe ye)
      as [EEQ | ENEQ].
    all: repeat break_match; subst.
    6: constructor 2.
    all: constructor; cbn.
    all: rewrite ?EX, ?EY.
    all: try erewrite evalFloatExpr_env_indep by eassumption.
    all: try reflexivity.
    now rewrite EEQ, EY.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst;
      inversion YE as [t1 t2 EY t3 t4| t1 t2 EY]; clear YE; subst.
    2-4: cbn; repeat break_match; constructor 2.
    destruct x' as [[xe xf] |],
             y' as [[ye yf] |]; try some_none.
    all: cbn in *.
    2-4: constructor 2.
    all: destruct (List.list_eq_dec MFloat64asCT.CTypeEquivDec xe ye)
      as [EEQ | ENEQ].
    all: repeat break_match; subst.
    6: constructor 2.
    all: constructor; cbn.
    all: rewrite ?EX, ?EY.
    all: try erewrite evalFloatExpr_env_indep by eassumption.
    all: try reflexivity.
    now rewrite EEQ, EY.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst;
      inversion YE as [t1 t2 EY t3 t4| t1 t2 EY]; clear YE; subst.
    2-4: cbn; repeat break_match; constructor 2.
    destruct x' as [[xe xf] |],
             y' as [[ye yf] |]; try some_none.
    all: cbn in *.
    2-4: constructor 2.
    all: destruct (List.list_eq_dec MFloat64asCT.CTypeEquivDec xe ye)
      as [EEQ | ENEQ].
    all: repeat break_match; subst.
    6: constructor 2.
    all: constructor; cbn.
    all: rewrite ?EX, ?EY.
    all: try erewrite evalFloatExpr_env_indep by eassumption.
    all: try reflexivity.
    now rewrite EEQ, EY.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst.
    2: constructor 2.
    destruct x' as [[xe xf] |]; try some_none.
    2: constructor 2.
    constructor; cbn in *.
    now rewrite EX.
  -
    inversion XE as [t1 t2 EX t3 t4| t1 t2 EX]; clear XE; subst.
    2: constructor 2.
    destruct x' as [[xe xf] |]; try some_none.
    2: constructor 2.
    constructor; cbn in *.
    now rewrite EX.
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
