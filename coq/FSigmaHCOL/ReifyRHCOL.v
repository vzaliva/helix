Require Import Helix.MSigmaHCOL.RasCT.
Require Import Helix.RSigmaHCOL.NatAsNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.RSigmaHCOL.RSigmaHCOL.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

(* Translate RHCOL to FHCOL *)
Module Export RHCOLtoFHCOL := MDHCOLTypeTranslator
                                 (MRasCT)
                                 (MFloat64asCT)
                                 (MNatAsNT)
                                 (MInt64asNT)
                                 (RHCOL)
                                 (FHCOL)
                                 (RHCOLEval)
                                 (FHCOLEval).

(* Translation properties *)
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.

Require Import MathClasses.interfaces.canonical_names.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.Tactics.StructTactics.
Require Import Helix.Util.Misc.

Import ListNotations.

Definition heq_nat_int : nat -> MInt64asNT.t -> Prop :=
  fun n i => Z.of_nat n ≡ Int64.intval i.

Global Instance RF_CHE : RHCOLtoFHCOL.CTranslation_heq ().
Proof.
  econstructor.
  instantiate (1:=fun _ r f => is_finite _ _ f ≡ true /\ B2R _ _ f ≡ r).
  -
    intros r1 r2 RE f1 f2 FE.
    invc RE.
    invc FE.
    easy.
  -
    intros * T *.
    cbn.
    unfold translateCTypeConst in *.
    repeat break_if; invc T.
    now rewrite <-H1, e.
    rewrite <-H1, e.
    unfold Float64asCT.MFloat64asCT.CTypeOne, FloatUtil.b64_1.
    cbv.
    lra.
Defined.

Global Instance RF_NHE : RHCOLtoFHCOL.NTranslation_heq.
Proof.
  econstructor.
  instantiate (1:= heq_nat_int).
  -
    intros n1 n2 EN i1 i2 EI.
    unfold heq_nat_int.
    cbv in EN; subst n2; rename n1 into n.
    pose proof Integers.Int64.eq_spec i1 i2 as EQI.
    rewrite EI in EQI.
    apply f_equal with (f:=Int64.intval) in EQI.
    lia.
  -
    unfold RHCOLtoFHCOL.translateNTypeConst.
    unfold MInt64asNT.from_nat, NatAsNT.MNatAsNT.to_nat, MInt64asNT.from_Z.
    intros * TR.
    repeat break_match; invc TR.
    pose proof Integers.Int64.eq_spec
         {| Int64.intval := Z.of_nat x; Int64.intrange := conj l l0 |}
         x'
      as EQI.
    rewrite H1 in EQI.
    rewrite <-EQI.
    reflexivity.
Defined.

Global Instance RF_NTP : RHCOLtoFHCOL.NTranslationProps.
Proof.
  constructor; intros *.
  all: unfold RF_NHE, heq_NType, heq_nat_int.
  all: unfold NatAsNT.MNatAsNT.to_nat, MInt64asNT.to_nat.
  all: unfold NatAsNT.MNatAsNT.from_nat, MInt64asNT.from_nat, MInt64asNT.from_Z.
  -
    intros NI.
    rewrite <-NI.
    rewrite Nat2Z.id.
    reflexivity.
  -
    unfold MInt64asNT.from_Z.
    repeat break_match;
      constructor.
    reflexivity.
Qed.

Section NT_numerical.

  (* Instances for trivial comparison of CType values
     in RHCOL->FHCOL translation.
     Any two numbers are considered "equal" ([trivial2]).

     These allow to infer structural properties of translation,
     while disregarding CType values (and CType values only).

     The statement [RF_Structural_Semantic_Preservation]
     is the full semantic preservation on RHCOL->FHCOL, up to CType values.
   *)
  Definition trivial_RF_CHE : RHCOLtoFHCOL.CTranslation_heq ().
    econstructor.
    instantiate (1 := trivial3).
    typeclasses eauto.
    repeat constructor.
  Defined.

  Fact trivial_RF_COP
    : @RHCOLtoFHCOL.COpTranslationProps () trivial_RF_CHE.
  Proof.
    repeat constructor.
  Qed.

  Definition RF_Structural_Semantic_Preservation :=
    @RHCOLtoFHCOL.translation_semantics_correct () ()
      RF_NHE
      trivial_RF_CHE
      RF_NTP
      trivial_RF_COP.

End NT_numerical.

Global Hint Unfold 
    NatAsNT.MNatAsNT.to_nat
    NatAsNT.MNatAsNT.from_nat
    MInt64asNT.to_nat
    MInt64asNT.from_nat
    NatAsNT.MNatAsNT.NTypePlus
    NatAsNT.MNatAsNT.NTypeDiv
    NatAsNT.MNatAsNT.NTypeMod
    NatAsNT.MNatAsNT.NTypePlus
    NatAsNT.MNatAsNT.NTypeMinus
    NatAsNT.MNatAsNT.NTypeMult
    NatAsNT.MNatAsNT.NTypeMin
    NatAsNT.MNatAsNT.NTypeMax
  : NatAsNT_ops.

Global Hint Unfold
  MInt64asNT.NTypePlus
  MInt64asNT.NTypeDiv
  MInt64asNT.NTypeMod
  MInt64asNT.NTypePlus
  MInt64asNT.NTypeMinus
  MInt64asNT.NTypeMult
  MInt64asNT.NTypeMin
  MInt64asNT.NTypeMax
  Int64.divu
  Int64.modu
  Int64.add
  Int64.sub
  Int64.mul
  Int64.lt
  : Int64asNT_ops.

Ltac crush_int :=
  repeat rewrite !Int64.unsigned_repr;
  replace Int64.max_unsigned
    with 18446744073709551615%Z
    in *
      by reflexivity;
  try lia.
