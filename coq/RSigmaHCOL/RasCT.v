Require Import ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import micromega.RMicromega.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Require Import Helix.MSigmaHCOL.CType.

Instance R_Equiv: Equiv R := eq.

Instance R_Setoid: Setoid R.
Proof. split; auto. Qed.

Module MRasCT <: CType.

  Definition t := R.

  Definition CTypeEquiv := R_Equiv.
  Definition CTypeSetoid := R_Setoid.

  Instance CTypeEquivDec: forall x y: t, Decision (x = y).
  Proof.
    intros.
    unfold Decision.
    apply R.OT.eq_dec.
  Qed.

  Definition CTypeZero := R0.
  Definition CTypeOne  := R1.

  Lemma CTypeZeroOneApart: R0 ≠ R1.
  Proof.
    unfold equiv.
    eapply OrderedRing.SORneq_0_1.
    apply Rsor.
  Qed.

  Definition CTypePlus     := Rplus.
  Definition CTypeNeg      := Ropp.
  Definition CTypeMult     := Rmult.
  Definition CTypeAbs      := Rabs.

  Definition CTypeZLess (a b: R) : R :=
    match (Rlt_dec a b) with
    | left _ => CTypeOne
    | right _ => CTypeZero
    end.

  Definition CTypeMin      := Rmin.
  Definition CTypeMax      := Rmax.
  Definition CTypeSub      := Rminus.

  Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Proof. solve_proper. Qed.

  Instance abs_proper: Proper ((=) ==> (=)) Rabs.
  Proof. solve_proper. Qed.

  Instance plus_proper: Proper ((=) ==> (=) ==> (=)) (Rplus).
  Proof. solve_proper. Qed.

  Instance sub_proper: Proper ((=) ==> (=) ==> (=)) (Rminus).
  Proof. solve_proper. Qed.

  Instance mult_proper: Proper ((=) ==> (=) ==> (=)) (Rmult).
  Proof. solve_proper. Qed.

  Instance min_proper: Proper ((=) ==> (=) ==> (=)) (Rmin).
  Proof. solve_proper. Qed.

  Instance max_proper: Proper ((=) ==> (=) ==> (=)) (Rmax).
  Proof. solve_proper. Qed.

End MRasCT.

Require Import Helix.HCOL.CarrierType.

Section RasCarrierA.

  Local Definition Abs_R : @Abs R R_Equiv Rle R0 Ropp.
    econstructor.
    instantiate (1:=Rabs x).
    split; intros Z.
    -
      apply Rabs_right.
      now apply Rle_ge.
    -
      now apply Rabs_left1.
  Defined.

  Local Instance CarrierDefs_R : CarrierDefs :=
    { CarrierA := R
    ; CarrierAe := R_Equiv
    ; CarrierAle := Rle
    ; CarrierAlt := Rlt
    ; CarrierAltdec := Rlt_dec
    ; CarrierAequivdec := R.OT.eq_dec
    ; CarrierAz := R0
    ; CarrierA1 := R1
    ; CarrierAplus := Rplus
    ; CarrierAmult := Rmult
    ; CarrierAneg := Ropp
    ; CarrierAabs := Abs_R
    }.

  Local Instance CarrierProperties_R : @CarrierProperties CarrierDefs_R.
  Proof.
    constructor.
    all: unfold CarrierA, CarrierAle, CarrierAlt, CarrierDefs_R.
    -
      typeclasses eauto.
    -
      repeat constructor.
      all: try typeclasses eauto.
      all: cbn.
      all: repeat try intros ?.
      all: try eapply Rsrt.
      + rewrite Radd_comm; apply Rsrt.
      + apply Rplus_opp_l.
      + rewrite Rmul_comm; apply Rsrt.
      + apply Rmult_plus_distr_l.
    -
      constructor; try typeclasses eauto; repeat intros ?.
      constructor; try typeclasses eauto; repeat intros ?.
      constructor; try typeclasses eauto; repeat intros ?.
      + now right.
      + eapply Rle_trans; eassumption.
      + now apply Rle_antisym.
      + pose proof Rle_or_lt x y as [T | T];
          [tauto | right; now apply Rlt_le].
    -
      constructor.
      all: typeclasses eauto.
    -
      constructor; try typeclasses eauto; repeat intros ?.
      constructor; try typeclasses eauto; repeat intros ?.
      constructor; try typeclasses eauto; repeat intros ?.
      all: try (cbv in *; congruence).
      +
        destruct (R.OT.eq_dec x z);
          [right | left]; congruence.
      +
        destruct (R.OT.eq_dec x y);
          now cbv in *.
      +
        destruct H.
        pose proof Rlt_trans _ _ _ H H0.
        now pose proof Rlt_irrefl x.
      +
        pose proof Rlt_dec x z as [T | T];
          [tauto |].
        right.
        apply Rnot_lt_le in T.
        eapply Rle_lt_trans; eassumption.
      +
        pose proof Req_appart_dec x y as [EQ | DEC].
        *
          subst.
          split; repeat intros ?.
          now cbv in *.
          pose proof Rlt_irrefl y.
          tauto.
        *
          destruct DEC;
            split; intros;
            try tauto.
          now apply Rlt_not_eq.
          intros C.
          eapply Rlt_not_eq; [eassumption | congruence].
      +
        split;
          [apply Rle_not_lt | apply Rnot_lt_le].
  Qed.

End RasCarrierA.
