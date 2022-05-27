Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import Coq.micromega.RMicromega.
Require Import Coq.micromega.Lra.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.Util.Misc.

Instance Abs_R : @Abs R R_Equiv Rle R0 Ropp.
Proof.
  econstructor.
  instantiate (1:=Rabs x).
  split; intros Z.
  -
    apply Rabs_right.
    now apply Rle_ge.
  -
    now apply Rabs_left1.
Defined.

Global Instance CarrierDefs_R : CarrierDefs :=
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

Global Instance CarrierProperties_R : @CarrierProperties CarrierDefs_R.
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
  -
    cbv.
    lra.
Qed.

Global Instance R_SRO :
  @orders.SemiRingOrder
    CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle.
Proof.
  constructor;
    try typeclasses eauto;
    intros.
  -
    exists (y - x).
    cbv in *.
    lra.
  -
    constructor; constructor.
    1,3: constructor.
    all: try typeclasses eauto.
    all: intros; cbv in *; lra.
  -
    unfold PropHolds in *.
    now apply Rmult_le_pos.
Qed.
