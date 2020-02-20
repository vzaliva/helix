(* R_theta is type which is used as value for vectors in SPIRAL.  *)

Require Export Helix.HCOL.CarrierType.

Require Import Coq.Bool.Bool.
Require Import Ring.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import Helix.Util.WriterMonadNoT.
Require Import ExtLib.Data.PPair.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.

Require Import Helix.Tactics.HelixTactics.

Import MonadNotation.
Import Monoid.
Local Open Scope monad_scope.


(* Both safe and collision tracking flags monads share same underlying data structure *)

Record RthetaFlags : Type :=
  mkRthetaFlags
    {
      is_struct: bool ;
      is_collision: bool
    }.

(* Propositional predicates *)
Definition IsCollision (x:RthetaFlags) := Is_true (is_collision x).
Definition IsVal       (x:RthetaFlags) := not (Is_true (is_struct x)).
Definition IsStruct    (x:RthetaFlags) := Is_true (is_struct x).

Global Instance IsVal_dec (x: RthetaFlags) : Decision (IsVal x).
Proof.
  unfold Decision, IsVal.
  destruct x.
  destr_bool; auto.
Qed.

Global Instance IsStruct_dec (x: RthetaFlags) : Decision (IsStruct x).
Proof.
  unfold Decision, IsStruct.
  destruct x.
  destr_bool; auto.
Qed.


Global Instance RthetaFlags_equiv:
  Equiv RthetaFlags :=
  fun a b =>
    is_collision a ≡ is_collision b /\
    is_struct a ≡ is_struct b.

Global Instance RthetaFlags_Reflexive_equiv: Reflexive RthetaFlags_equiv.
Proof.
  unfold Reflexive.
  intros x.
  destruct x.
  unfold equiv, RthetaFlags_equiv.
  auto.
Qed.

Global Instance RthetaFlags_Symmetric_equiv: Symmetric RthetaFlags_equiv.
Proof.
  unfold Symmetric.
  intros x y H.
  destruct x,y.
  unfold equiv, RthetaFlags_equiv in *.
  simpl in *.
  split; crush.
Qed.

Global Instance RthetaFlags_Transitive_equiv: Transitive RthetaFlags_equiv.
Proof.
  unfold Transitive.
  intros x y z H0 H1.
  unfold equiv, RthetaFlags_equiv in *.
  crush.
Qed.

Global Instance RthetaFlags_Equivalence_equiv: Equivalence RthetaFlags_equiv.
Proof.
  split.
  apply RthetaFlags_Reflexive_equiv.
  apply RthetaFlags_Symmetric_equiv.
  apply RthetaFlags_Transitive_equiv.
Qed.

Global Instance RthetaFlags_Setoid: @Setoid RthetaFlags RthetaFlags_equiv.
Proof.
  apply RthetaFlags_Equivalence_equiv.
Qed.

(* our [equal] definition for [RthetaFlags] is actually same as [eq] *)
Global Instance RthetaFlags_Equiv: Equiv (RthetaFlags) := eq.

(* our [equiv] definition for [RthetaFlags] is actually same as [eq] *)
Lemma RthetaFlags_equiv_eq
      {a b:RthetaFlags}:
  a = b <-> a ≡ b.
Proof.
  split; auto.
Qed.

(* mzero *)
Definition RthetaFlagsZero := mkRthetaFlags true false.

Section CollisionTrackingRthetaFlags.
  (* mappend which tracks collisions *)
  Definition RthetaFlagsAppend (a b: RthetaFlags) : RthetaFlags :=
    mkRthetaFlags
      (is_struct a && is_struct b)
      (is_collision a || (is_collision b ||
                         (negb (is_struct a || is_struct b)))).

  Definition Monoid_RthetaFlags : Monoid RthetaFlags := Build_Monoid RthetaFlagsAppend RthetaFlagsZero.


  (* Monoid is just a record and equivalence is established pointwise on fields *)
  Global Instance Monoid_equiv `{Equiv f}:
    Equiv (Monoid f) :=
    fun a b =>
      (monoid_plus a = monoid_plus b) /\
      (monoid_unit a = monoid_unit b).

  Lemma RthetaFlags_assoc:
    ∀ a b c : RthetaFlags,
      RthetaFlagsAppend (RthetaFlagsAppend a b) c
                        ≡ RthetaFlagsAppend a (RthetaFlagsAppend b c).
  Proof.
    intros a b c.
    destruct a,b,c.
    destr_bool.
  Qed.

  Lemma RthetaFlags_lunit:
    ∀ a : RthetaFlags, RthetaFlagsAppend RthetaFlagsZero a ≡ a.
  Proof.
    intros a.
    destruct a.
    destr_bool.
  Qed.

  Lemma RthetaFlags_runit:
    ∀ a : RthetaFlags, RthetaFlagsAppend a RthetaFlagsZero ≡ a.
  Proof.
    intros a.
    destruct a.
    destr_bool.
  Qed.

  Global Instance MonoidLaws_RthetaFlags:
    MonoidLaws Monoid_RthetaFlags.
  Proof.
    split.
    - (* monoid_assoc *)
      simpl.
      unfold BinOps.Associative.
      apply RthetaFlags_assoc.
    - (* monoid_lunit *)
      simpl.
      unfold BinOps.LeftUnit.
      apply RthetaFlags_lunit.
    - (* monoid_runit *)
      simpl.
      unfold BinOps.RightUnit.
      apply RthetaFlags_runit.
  Qed.
End CollisionTrackingRthetaFlags.

Section SafeRthetaFlags.

  (* mappend which does not track collisions *)
  Definition RthetaFlagsSafeAppend (a b: RthetaFlags) : RthetaFlags :=
    mkRthetaFlags
      (andb (is_struct a) (is_struct b))
      (orb (is_collision a) (is_collision b)).

  Definition Monoid_RthetaSafeFlags : Monoid RthetaFlags := ExtLib.Structures.Monoid.Build_Monoid RthetaFlagsSafeAppend RthetaFlagsZero.

  Lemma RthetaFlags_safe_assoc:
    ∀ a b c : RthetaFlags,
      RthetaFlagsSafeAppend (RthetaFlagsSafeAppend a b) c
                            ≡ RthetaFlagsSafeAppend a (RthetaFlagsSafeAppend b c).
  Proof.
    intros a b c.
    destruct a,b,c.
    destr_bool.
  Qed.

  Lemma RthetaFlags_safe_lunit:
    ∀ a : RthetaFlags, RthetaFlagsSafeAppend RthetaFlagsZero a ≡ a.
  Proof.
    intros a.
    destruct a.
    destr_bool.
  Qed.

  Lemma RthetaFlags_safe_runit:
    ∀ a : RthetaFlags, RthetaFlagsSafeAppend a RthetaFlagsZero ≡ a.
  Proof.
    intros a.
    destruct a.
    destr_bool.
  Qed.

  Global Instance MonoidLaws_SafeRthetaFlags:
    MonoidLaws Monoid_RthetaSafeFlags.
  Proof.
    split.
    - (* monoid_assoc *)
      simpl.
      unfold BinOps.Associative.
      apply RthetaFlags_safe_assoc.
    - (* monoid_lunit *)
      simpl.
      unfold BinOps.LeftUnit.
      apply RthetaFlags_safe_lunit.
    - (* monoid_runit *)
      simpl.
      unfold BinOps.RightUnit.
      apply RthetaFlags_safe_runit.
  Qed.

End SafeRthetaFlags.

Section RMonad.
  Variable fm:Monoid RthetaFlags.
  (* Monad_RthetaFlags is just a Writer Monad for RthetaFlags *)
  Definition Monad_RthetaFlags := writer fm.

  (* Generic Rtheta type is parametrized by Monoid, which defines how structural flags are handled. *)
  Definition Rtheta' := Monad_RthetaFlags CarrierA.


  Definition mkRtheta' (val: CarrierA) (flags:RthetaFlags) : Rtheta' :=
    tell flags ;; ret val.

  Lemma mkRtheta'_evalWriter
        (val: CarrierA)
        (flags:RthetaFlags):
    evalWriter (mkRtheta' val flags) ≡ val.
  Proof.
    unfold mkRtheta', evalWriter, compose.
    reflexivity.
  Qed.

  Lemma mkRtheta'_execWriter
        (val: CarrierA)
        (flags:RthetaFlags)
        {fml:@MonoidLaws RthetaFlags fm}:
    execWriter (mkRtheta' val flags) ≡ flags.
  Proof.
    unfold mkRtheta', execWriter, compose.
    simpl.
    apply fml.
  Qed.

  Lemma mkRtheta'_id
        {r: Rtheta'}
        {fml:@MonoidLaws RthetaFlags fm}
    :
      r ≡ mkRtheta' (evalWriter r) (execWriter r).
  Proof.
    unfold mkRtheta', execWriter, evalWriter, compose, tell.
    simpl.
    destruct r.
    f_equiv.
    pose proof monoid_runit as U.
    unfold BinOps.RightUnit in U.
    rewrite U.
    destruct runWriterT.
    inversion unIdent.
    f_equiv.
  Qed.

  Lemma Rtheta'_alt_eq
        {a b : Rtheta'}
        {fml:@MonoidLaws RthetaFlags fm}:
    evalWriter a ≡ evalWriter b ->
    execWriter a ≡ execWriter b ->
    a ≡ b.
  Proof.
    intros V S.
    setoid_rewrite mkRtheta'_id.
    rewrite V, S.
    reflexivity.
  Qed.

End RMonad.


Definition Rtheta := Rtheta' Monoid_RthetaFlags.
Definition RStheta := Rtheta' Monoid_RthetaSafeFlags.

(* Monad morhisms *)

Definition Rtheta2RStheta: Rtheta -> RStheta := castWriter Monoid_RthetaSafeFlags.

Definition RStheta2Rtheta: RStheta -> Rtheta := castWriter Monoid_RthetaFlags.

(* Some convenience constructros *)

Section Rtheta'Utils.
  Context {fm:Monoid RthetaFlags}.

  (* `tell` might seems redundant here, as it sets the same flags
     value as `Rthetaflagszero`, but in this context we do not know what unit
     flags value is for given monoid, so we enforce a specific value for it *)
  Definition mkStruct (val: CarrierA) : Rtheta' fm :=
    tell (mkRthetaFlags true false) ;; ret val.

  (* Structural zero is 0 value combined with 'mzero' monoid flags *)
  Definition mkSZero : Rtheta' fm := mkStruct 0.

  Definition mkValue (val: CarrierA) : Rtheta' fm :=
    tell (mkRthetaFlags false false) ;; ret val.

  Definition Is_Val: (Rtheta' fm) -> Prop :=
    IsVal ∘ (@execWriter RthetaFlags CarrierA fm).

  Definition Is_Struct: (Rtheta' fm) -> Prop :=
    IsStruct ∘ (@execWriter RthetaFlags CarrierA fm).

  Definition Is_Collision (x:Rtheta' fm) :=
    (IsCollision ∘ (@execWriter RthetaFlags CarrierA fm)) x.

  Definition Not_Collision := not ∘ Is_Collision.

  Definition liftRthetaP (P: CarrierA -> Prop): (Rtheta' fm) -> Prop :=
    fun x => P (evalWriter x).

  Definition Is_NonNegative (x:Rtheta' fm) : Prop := liftRthetaP (le 0) x.

  Definition Is_ValX (z:CarrierA)
    := fun (x:Rtheta' fm) => (WriterMonadNoT.evalWriter x) = z.

  Global Instance Rtheta'_equiv: Equiv (Rtheta' fm) :=
    fun am bm => (evalWriter am) = (evalWriter bm).

  Global Instance evalWriter_proper:
    Proper ((=) ==> (=)) (@evalWriter RthetaFlags CarrierA fm).
  Proof.
    simpl_relation.
  Qed.

  Global Instance liftRthetaP_proper
         (P: CarrierA -> Prop)
         (P_mor: Proper ((=) ==> iff) P)
    :
      Proper ((=) ==> iff) (@liftRthetaP P).
  Proof.
    unfold liftRthetaP.
    solve_proper.
  Qed.

  Global Instance Is_ValX_proper:
      Proper ((=) ==> (=) ==> (iff)) (Is_ValX).
  Proof.
    unfold Is_ValX.
    solve_proper.
  Qed.

  Ltac unfold_Rtheta'_equiv := unfold equiv, Rtheta'_equiv in *.

  Global Instance Rtheta_Reflexive_equiv:
    @Reflexive (Rtheta' fm) Rtheta'_equiv.
  Proof.
    unfold Reflexive.
    destruct x; (unfold_Rtheta'_equiv; crush).
  Qed.

  Global Instance Rtheta_Symmetric_equiv:
    @Symmetric (Rtheta' fm) Rtheta'_equiv.
  Proof.
    unfold Symmetric.
    destruct x; (unfold_Rtheta'_equiv; crush).
  Qed.

  Global Instance Rtheta_Transitive_equiv:
    @Transitive (Rtheta' fm) Rtheta'_equiv.
  Proof.
    unfold Transitive.
    destruct x; (unfold_Rtheta'_equiv; crush).
  Qed.

  Global Instance Rtheta_Equivalence_equiv:
    @Equivalence (Rtheta' fm) Rtheta'_equiv.
  Proof.
    split.
    apply Rtheta_Reflexive_equiv.
    apply Rtheta_Symmetric_equiv.
    apply Rtheta_Transitive_equiv.
  Qed.

  Global Instance Rtheta_Setoid:
    @Setoid (Rtheta' fm) Rtheta'_equiv.
  Proof.
    apply Rtheta_Equivalence_equiv.
  Qed.

  (* Note: definitional equality *)
  Lemma evalWriter_Rtheta_liftM
        (op: CarrierA -> CarrierA)
        `{a: Rtheta' fm}
    :
      evalWriter (liftM op a) ≡ op (evalWriter a).
  Proof.
    reflexivity.
  Qed.

  (* Note: definitional equality *)
  Lemma evalWriter_Rtheta_liftM2
        (op: CarrierA -> CarrierA -> CarrierA)
        {a b: Rtheta' fm}
    :
      evalWriter (liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
  Proof.
    reflexivity.
  Qed.

  (* mkValue on evalWriter equiv wrt values *)
  Lemma mkValue_evalWriter
        (r: Rtheta' fm):
    mkValue (WriterMonadNoT.evalWriter r) = r.
  Proof.
    unfold WriterMonadNoT.evalWriter.
    unfold_Rtheta'_equiv.
    unfold mkValue.
    simpl.

    destruct r.
    destruct runWriterT.
    simpl in *.
    destruct unIdent.
    simpl in *.
    reflexivity.
  Qed.


  (* mkStruct on evalWriter equiv wrt values *)
  Lemma mkStruct_evalWriter
        (r: Rtheta' fm):
    mkStruct (WriterMonadNoT.evalWriter r) = r.
  Proof.
    unfold WriterMonadNoT.evalWriter.
    unfold_Rtheta'_equiv.
    unfold mkStruct.
    simpl.

    destruct r.
    destruct runWriterT.
    simpl in *.
    destruct unIdent.
    simpl in *.
    reflexivity.
  Qed.

  (* evalWriter on mkStruct equiv wrt values *)
  Lemma evalWriter_mkStruct
        (c: CarrierA):
     WriterMonadNoT.evalWriter (mkStruct c) ≡ c.
  Proof.
    unfold WriterMonadNoT.evalWriter, runWriter, runWriterT, compose, unIdent.
    unfold mkStruct, ret.
    reflexivity.
  Qed.

  Lemma execWriter_mkStruct
        (c: CarrierA)
        {fml:@MonoidLaws RthetaFlags fm}:
    WriterMonadNoT.execWriter (mkStruct c) ≡ RthetaFlagsZero.
  Proof.
    unfold RthetaFlagsZero.
    unfold WriterMonadNoT.execWriter, mkStruct, runWriter, runWriterT, compose, unIdent.
    unfold tell.
    simpl.
    apply fml.
  Qed.

  Lemma evalWriter_mkValue
        (x:CarrierA):
    WriterMonadNoT.evalWriter (mkValue x) ≡ x.
  Proof.
      reflexivity.
  Qed.

  Section WithMonoidLaws.
    Context {fml:@MonoidLaws RthetaFlags fm}.

    Lemma Is_Val_mkValue:
      ∀ (v:CarrierA), Is_Val (mkValue v).
    Proof.
      intros v.
      unfold Is_Val, IsVal, mkValue.
      simpl.
      replace (@monoid_plus RthetaFlags fm (mkRthetaFlags false false)
                            (@monoid_unit RthetaFlags fm)) with
          (mkRthetaFlags false false).
      - apply Bool.negb_prop_elim.
        simpl.
        trivial.
      -
        symmetry.
        apply fml.
    Qed.

    Lemma Not_Collision_mkValue:
      ∀ (v:CarrierA), Not_Collision (mkValue v).
    Proof.
      intros v.
      unfold Not_Collision, Is_Collision, not, mkValue.
      simpl.
      replace (@monoid_plus RthetaFlags fm (mkRthetaFlags false false)
                            (@monoid_unit RthetaFlags fm)) with
          (mkRthetaFlags false false).
      - apply Bool.negb_prop_elim.
        simpl.
        trivial.
      -
        symmetry.
        apply fml.
    Qed.

    Lemma execWriter_liftM:
      ∀ (f : CarrierA → CarrierA)
        (x : Rtheta' fm),
        execWriter (Monad.liftM f x) ≡ execWriter x.
    Proof.
      intros f x.
      unfold Monad.liftM, execWriter.
      destruct x.
      simpl.
      apply fml.
    Qed.

    Lemma execWriter_Rtheta_liftM2
          (op: CarrierA -> CarrierA -> CarrierA)
          {a b: Rtheta' fm}
      :
        execWriter (liftM2 op a b) ≡ monoid_plus fm
                   (@execWriter _ _ fm a) (@execWriter _ _ fm b).
    Proof.
      unfold execWriter, liftM2.
      simpl.
      destruct fml.
      rewrite monoid_runit.
      reflexivity.
    Qed.

    (* mkValue on evalWriter on non-collision value is identity *)
    Lemma mkValue_evalWriter_VNC
          (r : Rtheta' fm)
      :
        Is_Val r → Not_Collision r -> mkValue (WriterMonadNoT.evalWriter r) ≡ r.
    Proof.
      intros D N.
      unfold Is_Val, compose in D.
      unfold Not_Collision, compose, Is_Collision, compose in N.
      unfold WriterMonadNoT.execWriter in D.
      unfold WriterMonadNoT.execWriter in N.
      unfold WriterMonadNoT.evalWriter.

      unfold IsVal in D.
      unfold IsCollision in N.
      unfold mkValue.
      simpl.

      destruct r.
      destruct runWriterT.
      simpl in *.
      apply Bool.negb_prop_intro in D.
      apply Bool.negb_prop_intro in N.
      apply Bool.Is_true_eq_true, Bool.negb_true_iff in D.
      apply Bool.Is_true_eq_true, Bool.negb_true_iff in N.

      destruct unIdent.
      simpl in *.
      destruct fm, fml.
      simpl.
      destruct psnd.
      simpl in *.
      subst.
      rewrite monoid_runit.
      reflexivity.
    Qed.

    Lemma Is_Val_liftM
          (f: CarrierA → CarrierA)
          (r : Rtheta' fm):
      Is_Val r → Is_Val (liftM f r).
    Proof.
      intros H.
      unfold Is_Val, compose in *.
      rewrite execWriter_liftM.
      apply H.
    Qed.

    Lemma Not_Collision_liftM
          (f: CarrierA → CarrierA)
          (r : Rtheta' fm):
      Not_Collision r -> Not_Collision (liftM f r).
    Proof.
      intros H.
      unfold Not_Collision, not, Is_Collision, IsCollision, compose in *.
      rewrite execWriter_liftM.
      apply H.
    Qed.

    Lemma Not_Collision_mkStruct:
      ∀ v, Not_Collision  (mkStruct v).
    Proof.
      intros v.
      unfold Not_Collision, Is_Collision, not, mkStruct, compose.
      unfold tell, IsCollision, Is_true, is_collision.
      unfold execWriter, compose, psnd.
      simpl.
      break_let.
      rewrite monoid_runit in Heqr.
      inversion Heqr.
      tauto.
    Qed.

    Lemma Is_Struct_mkStruct:
      forall a, Is_Struct (mkStruct a).
    Proof.
      intros a.
      unfold Is_Struct, compose, mkStruct, IsStruct, execWriter, runWriter.
      unfold tell, compose, Is_true, is_struct.
      simpl.
      break_let.
      rewrite monoid_runit in Heqr.
      inversion Heqr.
      tauto.
    Qed.

    Global Instance Is_Val_dec
           (x: Rtheta' fm):
      Decision (Is_Val x).
    Proof.
      unfold Decision.
      unfold Is_Val, compose.
      generalize (WriterMonadNoT.execWriter x). intros f.
      apply IsVal_dec.
    Qed.

    Global Instance Is_Struct_dec
           (x: Rtheta' fm):
      Decision (Is_Struct x).
    Proof.
      unfold Decision.
      unfold Is_Struct, compose.
      generalize (WriterMonadNoT.execWriter x). intros f.
      apply IsStruct_dec.
    Qed.

    Lemma Is_Struct_Is_Val_dec:
      forall a, {Is_Struct a}+{Is_Val a}.
    Proof.
      intros a.
      unfold Is_Struct, Is_Val, compose, IsStruct, IsVal.
      destruct (execWriter a).
      destr_bool; auto.
    Qed.

    Lemma not_Is_Val_Is_Struct:
      forall a, not (Is_Val a) <-> Is_Struct a.
    Proof.
      split; intros; destruct (Is_Struct_Is_Val_dec a); auto; tauto.
    Qed.

    Lemma not_Is_Struct_Is_Val:
      forall a, not (Is_Struct a) <-> Is_Val a.
    Proof.
      split; intros; destruct (Is_Struct_Is_Val_dec a); auto; tauto.
    Qed.

    Lemma Is_Val_mkStruct:
      forall a, not (Is_Val (mkStruct a)).
    Proof.
      intros a.
      assert (Is_Struct (mkStruct a)) by apply Is_Struct_mkStruct.
      destruct (Is_Struct_Is_Val_dec (mkStruct a)); auto.
    Qed.

    Lemma Is_Struct_mkValue:
      forall a, not (Is_Struct (mkValue a)).
    Proof.
      intros a.
      assert (Is_Val (mkValue a)) by apply Is_Val_mkValue.
      destruct (Is_Struct_Is_Val_dec (mkValue a)); auto.
    Qed.

    Lemma Is_Val_mkSZero:
      Is_Val (mkSZero) -> False.
    Proof.
      unfold mkSZero.
      apply Is_Val_mkStruct.
    Qed.

    Lemma Is_Struct_mkSZero:
      Is_Struct (mkSZero).
    Proof.
      unfold mkSZero.
      apply Is_Struct_mkStruct.
    Qed.

  End WithMonoidLaws.

End Rtheta'Utils.

Lemma castWriter_mkValue_evalWriter
      (fm1 fm2 : Monoid.Monoid RthetaFlags)
      (r : Rtheta' fm1):
  WriterMonadNoT.castWriter fm2 r = mkValue (WriterMonadNoT.evalWriter r).
Proof.
  unfold equiv, Rtheta'_equiv.
  unfold evalWriter, castWriter, mkValue, runWriter.
  destruct r.
  reflexivity.
Qed.

Lemma castWriter_mkStruct
      (fm1 fm2 : Monoid.Monoid RthetaFlags)
      (r : CarrierA):
  @WriterMonadNoT.castWriter _ _ fm1 fm2 (mkStruct r) = mkStruct r.
Proof.
  unfold equiv, Rtheta'_equiv.
  unfold evalWriter, castWriter, mkStruct, runWriter.
  reflexivity.
Qed.

(* For some reason class resolver could not figure this out on it's own *)
Global Instance Rtheta_equiv: Equiv (Rtheta) := Rtheta'_equiv.
Global Instance RStheta_equiv: Equiv (RStheta) := Rtheta'_equiv.

Ltac unfold_Rtheta_equiv := unfold equiv, Rtheta_equiv, Rtheta'_equiv in *.
Ltac unfold_RStheta_equiv := unfold equiv, RStheta_equiv, Rtheta'_equiv in *.

Ltac fold_Rtheta'_equiv :=
  match goal with
  | [ |- @evalWriter _ _ ?fm ?a = @evalWriter _ _ ?fm ?b ] =>
    change (@evalWriter _ _ ?fm ?a = @evalWriter _ _ ?fm ?b) with (a=b)
  end.

Global Instance Rtheta2RStheta_proper
  : Proper ((=) ==> (=)) (Rtheta2RStheta).
Proof.
  simpl_relation.
Qed.

Global Instance RStheta2Rtheta_proper
  : Proper ((=) ==> (=)) (RStheta2Rtheta).
Proof.
  simpl_relation.
Qed.

Lemma RStheta2Rtheta_liftM2
      (f : CarrierA → CarrierA → CarrierA)
      (f_mor: Proper (equiv ==> equiv ==> equiv) f)
      {a b: Rtheta}
  :
    RStheta2Rtheta (Monad.liftM2 f (Rtheta2RStheta a) (Rtheta2RStheta b)) =
    Monad.liftM2 f a b.
Proof.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  unfold_Rtheta_equiv.
  reflexivity.
Qed.

Lemma RStheta2Rtheta_Rtheta2RStheta {x}:
  RStheta2Rtheta (Rtheta2RStheta x) ≡ x.
Proof.
  unfold Rtheta2RStheta, RStheta2Rtheta.
  unfold WriterMonadNoT.castWriter.
  unfold WriterMonadNoT.castWriterT.
  unfold compose.
  destruct x.
  auto.
Qed.

Lemma RStheta2Rtheta_Rtheta2RStheta_equiv {x}:
  RStheta2Rtheta (Rtheta2RStheta x) = x.
Proof.
  unfold Rtheta2RStheta, RStheta2Rtheta.
  unfold WriterMonadNoT.castWriter.
  unfold WriterMonadNoT.castWriterT.
  unfold compose.
  destruct x.
  reflexivity.
Qed.

Lemma Rtheta2RStheta_RStheta2Rtheta {x}:
  Rtheta2RStheta (RStheta2Rtheta x) ≡ x.
Proof.
  unfold Rtheta2RStheta, RStheta2Rtheta.
  unfold WriterMonadNoT.castWriter.
  unfold WriterMonadNoT.castWriterT.
  unfold compose.
  destruct x.
  auto.
Qed.

Lemma Is_Val_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : Rtheta):
  Is_Val a → Is_Val b → Is_Val (liftM2 f a b).
Proof.
  intros Ha Hb.
  unfold Is_Val, compose in *.
  rewrite execWriter_Rtheta_liftM2.
  simpl.
  unfold RthetaFlagsAppend.
  unfold IsVal, Is_true, not in *.
  simpl in *.
  generalize dependent (is_struct (WriterMonadNoT.execWriter a)).
  generalize dependent (is_struct (WriterMonadNoT.execWriter b)).
  clear a b f.
  intros a Hb b Ha H.
  destr_bool.
  congruence.
Qed.

Lemma Is_Val_Safe_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : RStheta):
  Is_Val a → Is_Val b → Is_Val (liftM2 f a b).
Proof.
  intros Ha Hb.
  unfold Is_Val, compose in *.
  rewrite execWriter_Rtheta_liftM2.
  simpl.
  unfold RthetaFlagsAppend.
  unfold IsVal, Is_true, not in *.
  simpl in *.
  generalize dependent (is_struct (WriterMonadNoT.execWriter a)).
  generalize dependent (is_struct (WriterMonadNoT.execWriter b)).
  clear a b f.
  intros a Hb b Ha H.
  destr_bool.
  congruence.
Qed.

Lemma Is_Val_RStheta2Rtheta
      {x:RStheta}:
  Is_Val x <-> Is_Val (RStheta2Rtheta x).
Proof.
  split; auto.
Qed.

Lemma Is_Val_Rtheta2RStheta
      {x:Rtheta}:
  Is_Val x <-> Is_Val (Rtheta2RStheta x).
Proof.
  split; auto.
Qed.

Lemma Is_Struct_RStheta2Rtheta
      {x:RStheta}:
  Is_Struct x <-> Is_Struct (RStheta2Rtheta x).
Proof.
  split; auto.
Qed.

Lemma Is_Struct_Rtheta2RStheta
      {x:Rtheta}:
  Is_Struct x <-> Is_Struct (Rtheta2RStheta x).
Proof.
  split; auto.
Qed.

Lemma Not_Collision_RStheta2Rtheta
      {x:RStheta}:
  Not_Collision x <-> Not_Collision (RStheta2Rtheta x).
Proof.
  split; auto.
Qed.

Lemma Not_Collision_Rtheta2RStheta
      {x:Rtheta}:
  Not_Collision x <-> Not_Collision (Rtheta2RStheta x).
Proof.
  split; auto.
Qed.


Lemma Not_Collision_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : Rtheta):
  Not_Collision a → Not_Collision b →
  (Is_Struct a \/ Is_Struct b) ->
  Not_Collision (liftM2 f a b).
Proof.
  intros Ha Hb Hab.
  unfold Not_Collision, Is_Collision, not, compose in *.
  rewrite execWriter_Rtheta_liftM2.
  simpl.
  unfold RthetaFlagsAppend.
  unfold IsCollision, Is_true, not in *.
  unfold Is_Struct, Is_Val, compose, IsStruct, Is_true, not in *.
  simpl in *.
  generalize dependent (is_struct (WriterMonadNoT.execWriter a)).
  generalize dependent (is_struct (WriterMonadNoT.execWriter b)).
  generalize dependent (is_collision (WriterMonadNoT.execWriter a)).
  generalize dependent (is_collision (WriterMonadNoT.execWriter b)).
  destr_bool; try congruence.
  tauto.
Qed.

Lemma Not_Collision_Safe_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : RStheta):
  Not_Collision a → Not_Collision b →
  Not_Collision (liftM2 f a b).
Proof.
  intros Ha Hb.
  unfold Not_Collision, Is_Collision, not, compose in *.
  rewrite execWriter_Rtheta_liftM2.
  simpl.
  unfold RthetaFlagsSafeAppend.
  unfold IsCollision, Is_true, not in *.
  unfold Is_Struct, Is_Val, compose, IsVal, Is_true, not in *.
  simpl in *.
  generalize dependent (is_collision (WriterMonadNoT.execWriter a)).
  generalize dependent (is_collision (WriterMonadNoT.execWriter b)).
  destr_bool; congruence.
Qed.

Lemma evalWriter_Rtheta2RStheta_mkValue
      {x}:
  (WriterMonadNoT.evalWriter (Rtheta2RStheta (mkValue x))) ≡ x.
Proof.
  crush.
Qed.

Lemma evalWriter_Rtheta2RStheta_mkValue_equiv {x}:
  (WriterMonadNoT.evalWriter (Rtheta2RStheta (mkValue x))) = x.
Proof.
  rewrite evalWriter_Rtheta2RStheta_mkValue.
  reflexivity.
Qed.

Lemma mkValue_RStheta_dist_liftM2
      (f : CarrierA → CarrierA → CarrierA)
      (f_mor : Proper (equiv ==> equiv ==> equiv) f):
  forall a b,  mkValue (fm:=Monoid_RthetaSafeFlags) (f a b) =
          Monad.liftM2 f (mkValue a) (mkValue b).
Proof.
  intros a b.
  unfold equiv, RStheta_equiv, Rtheta'_equiv.
  rewrite evalWriter_Rtheta_liftM2.
  rewrite 3!evalWriter_mkValue.
  reflexivity.
Qed.

Section Zero_Utils.

  Lemma evalWriter_Rtheta_SZero
        (fm:Monoid RthetaFlags)
  :
    @evalWriter _ _ fm (@mkSZero fm) ≡ zero.
  Proof.
    reflexivity.
  Qed.

  Global Instance mkValue_proper
         {fm:Monoid RthetaFlags}
    :
      Proper((=) ==> (=)) (@mkValue fm).
  Proof.
    simpl_relation.
  Qed.

  Global Instance mkStruct_proper
         {fm:Monoid RthetaFlags}
    :
      Proper((=) ==> (=)) (@mkStruct fm).
  Proof.
    simpl_relation.
  Qed.

  Definition Is_ValZero {fm:Monoid RthetaFlags}
    := @Is_ValX fm 0.

  Global Instance Is_ValZero_dec {fm:Monoid RthetaFlags} (x:Rtheta' fm):
    Decision (Is_ValZero x).
  Proof.
    unfold Is_ValZero.
    unfold Decision.
    destruct (CarrierAequivdec (evalWriter x) zero); crush.
  Qed.

  Global Instance Is_ValZero_proper
         {fm:Monoid RthetaFlags}
    :
      Proper ((=) ==> (iff)) (@Is_ValZero fm).
  Proof.
    unfold Is_ValZero.
    solve_proper.
  Qed.

  Lemma Is_ValZero_to_mkSZero
        {fm:Monoid RthetaFlags}
        (x:Rtheta' fm):
    (Is_ValZero x) <-> (x = mkSZero).
  Proof.
    split; auto.
  Qed.

  Lemma SZero_is_ValZero
        {fm:Monoid RthetaFlags}:
    @Is_ValZero fm mkSZero.
  Proof.
    unfold Is_ValZero.
    compute.
    reflexivity.
  Qed.

  Lemma Is_ValX_mkStruct
        {fm:Monoid RthetaFlags}:
    forall x,
      @Is_ValX fm x (mkStruct x).
  Proof.
    intros x.
    unfold mkStruct, Is_ValX.
    compute.
    reflexivity.
  Qed.

  (* Using setoid equalities on both components *)
  Definition Is_SZero
             {fm:Monoid RthetaFlags}
             (x:Rtheta' fm)
    :=
      (evalWriter x = zero) /\
      (execWriter x = RthetaFlagsZero).

  Lemma Is_SZero_mkSZero:
    @Is_SZero Monoid_RthetaFlags mkSZero.
  Proof.
    unfold Is_SZero.
    split.
    rewrite evalWriter_Rtheta_SZero; reflexivity.
    unfold mkSZero.
    unfold execWriter.
    unfold equiv.
    simpl.
    reflexivity.
  Qed.

  Lemma not_not_on_decidable
        (A: Type)
        (P: A->Prop)
        `{forall x:A, Decision (P x)}
    :
      forall x, (not ∘ (not ∘ P)) x <-> P x.
  Proof.
    intros x.
    unfold compose.
    specialize (H x).
    destruct H; crush.
  Qed.

End Zero_Utils.

Lemma castWriter_equiv
      (fmx fmy: Monoid RthetaFlags)
      (x: Rtheta' fmx)
      (y: Rtheta' fmy):
  WriterMonadNoT.evalWriter x = WriterMonadNoT.evalWriter y
  <-> WriterMonadNoT.castWriter _ x = y.
Proof.
  split; intros H.
  -
    unfold WriterMonadNoT.castWriter,WriterMonadNoT.castWriterT,compose.
    unfold equiv, Rtheta'_equiv.
    rewrite <- H.
    reflexivity.
  -
    unfold WriterMonadNoT.castWriter,WriterMonadNoT.castWriterT,compose.
    unfold equiv, Rtheta'_equiv.
    rewrite <- H.
    reflexivity.
Qed.
