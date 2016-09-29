(* R_theta is type which is used as value for vectors in SPIRAL.  *)

Require Export CarrierType.

Require Import Coq.Bool.Bool.
Require Import Ring.

Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import WriterMonadNoT.
Require Import ExtLib.Structures.MonadLaws.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders MathClasses.orders.orders.

Require Import CpdtTactics.

Import MonadNotation.
Local Open Scope monad_scope.

Record RthetaFlags : Type :=
  mkRthetaFlags
    {
      is_struct: bool ;
      is_collision: bool
    }.

(* Propositional predicates *)
Definition IsCollision (x:RthetaFlags) := Is_true (is_collision x).
Definition IsVal (x:RthetaFlags) := not (Is_true (is_struct x)).

(* mappend *)
Definition RthetaFlagsAppend (a b: RthetaFlags) : RthetaFlags :=
  mkRthetaFlags
    (andb (is_struct a) (is_struct b))
    (orb (is_collision a) (orb (is_collision b)
                               (negb (orb (is_struct a) (is_struct b))))).

(* mzero *)
Definition RthetaFlagsZero := mkRthetaFlags true false.

Definition Monoid_RthetaFlags : ExtLib.Structures.Monoid.Monoid RthetaFlags := ExtLib.Structures.Monoid.Build_Monoid RthetaFlagsAppend RthetaFlagsZero.

Global Instance RthetaFlags_type:
  type RthetaFlags := type_libniz RthetaFlags.

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

Definition flags_m : Type -> Type := writer Monoid_RthetaFlags.

(* Global Instance Writer_flags: MonadWriter Monoid_RthetaFlags flags_m
  := Writer_writerT Monoid_RthetaFlags. *)

Definition Rtheta := flags_m CarrierA.

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

(* Some convenience constructros *)

Definition mkStruct (val: CarrierA) : Rtheta := ret val.

Definition mkSZero : Rtheta := mkStruct 0.

Definition mkValue (val: CarrierA) : Rtheta :=
  tell (mkRthetaFlags false false) ;; ret val.

Definition Is_Val : Rtheta -> Prop :=
  IsVal ∘ (@execWriter RthetaFlags CarrierA Monoid_RthetaFlags).

Definition Is_Struct := not ∘ Is_Val.

Definition Is_Collision (x:Rtheta) :=
  (IsCollision ∘ (@execWriter RthetaFlags CarrierA Monoid_RthetaFlags)) x.
Definition Not_Collision := not ∘ Is_Collision.

Lemma IsVal_mkValue:
  ∀ v : CarrierA, Is_Val (mkValue v).
Proof.
  intros v.
  unfold Is_Val, IsVal, mkValue.
  apply Bool.negb_prop_elim.
  simpl.
  trivial.
Qed.

Global Instance Rtheta_equiv: Equiv (Rtheta) :=
  fun am bm => (evalWriter am) = (evalWriter bm).

Global Instance evalWriter_proper:
  Proper ((=) ==> (=)) (@evalWriter RthetaFlags CarrierA _).
Proof.
  simpl_relation.
Qed.

Ltac unfold_Rtheta_equiv := unfold equiv, Rtheta_equiv in *.

Global Instance Rtheta_Reflexive_equiv: Reflexive Rtheta_equiv.
Proof.
  unfold Reflexive.
  destruct x; (unfold_Rtheta_equiv; crush).
Qed.

Global Instance Rtheta_Symmetric_equiv: Symmetric Rtheta_equiv.
Proof.
  unfold Symmetric.
  destruct x; (unfold_Rtheta_equiv; crush).
Qed.

Global Instance Rtheta_Transitive_equiv: Transitive Rtheta_equiv.
Proof.
  unfold Transitive.
  destruct x; (unfold_Rtheta_equiv; crush).
Qed.

Global Instance Rtheta_Equivalence_equiv: Equivalence Rtheta_equiv.
Proof.
  split.
  apply Rtheta_Reflexive_equiv.
  apply Rtheta_Symmetric_equiv.
  apply Rtheta_Transitive_equiv.
Qed.

Global Instance Rtheta_Setoid: Setoid (Rtheta).
Proof.
  apply Rtheta_Equivalence_equiv.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM
      (op: CarrierA -> CarrierA)
      {a: Rtheta}
  :
    evalWriter (liftM op a) ≡ op (evalWriter a).
Proof.
  reflexivity.
Qed.

Lemma execWriter_liftM:
  ∀ (f : CarrierA → CarrierA)
    (x : Rtheta),
    execWriter (Monad.liftM f x) ≡ execWriter x.
Proof.
      intros f x.
      unfold Monad.liftM, execWriter.
      destruct x.
      simpl.
      rewrite RthetaFlags_runit.
      crush.
Qed.

Lemma execWriter_Rtheta_liftM2
      (op: CarrierA -> CarrierA -> CarrierA)
      {a b: Rtheta}
  :
    execWriter (liftM2 op a b) ≡ RthetaFlagsAppend (execWriter a) (execWriter b).
Proof.
  unfold execWriter, liftM2.
  simpl.
  rewrite RthetaFlags_runit.
  reflexivity.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM2
      (op: CarrierA -> CarrierA -> CarrierA)
      {a b: Rtheta}
  :
    evalWriter (liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
Proof.
  reflexivity.
Qed.

Lemma Is_Val_mkStruct:  forall a, not (Is_Val (mkStruct a)).
Proof.
  crush.
Qed.


(* mkValue on evalWriter on non-collision value is identity *)
Lemma mkValue_evalWriter_VNC (r : Rtheta):
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
  unfold RthetaFlagsAppend.
  simpl.
  destruct psnd.
  simpl in *.
  subst.
  reflexivity.
Qed.

(* mkValue on evalWriter equiv wrt values *)
Lemma mkValue_evalWriter (r : Rtheta):
  mkValue (WriterMonadNoT.evalWriter r) = r.
Proof.
  unfold WriterMonadNoT.evalWriter.
  unfold_Rtheta_equiv.
  unfold mkValue.
  simpl.

  destruct r.
  destruct runWriterT.
  simpl in *.
  destruct unIdent.
  simpl in *.
  unfold RthetaFlagsAppend.
  simpl.
  destruct psnd.
  reflexivity.
Qed.

Section Decidablitiy.

  Global Instance IsVal_dec `(x: RthetaFlags) : Decision (IsVal x).
  Proof.
    unfold Decision, IsVal.
    destruct x.
    destr_bool; auto.
  Qed.

  Global Instance Is_Val_dec `(x: Rtheta) : Decision (Is_Val x).
  Proof.
    unfold Decision.
    unfold Is_Val, compose.
    generalize (WriterMonadNoT.execWriter x). intros f.
    apply IsVal_dec.
  Qed.

End Decidablitiy.

Section Zero_Utils.

  Lemma evalWriter_Rtheta_SZero:
    evalWriter mkSZero = zero.
  Proof.
    reflexivity.
  Qed.

  Global Instance mkValue_Proper:
    Proper((=) ==> (=)) mkValue.
  Proof.
    simpl_relation.
  Qed.

  Global Instance mkStruct_Proper:
    Proper((=) ==> (=)) mkStruct.
  Proof.
    simpl_relation.
  Qed.

  Definition Is_ValZero (x:Rtheta) := (evalWriter x) = 0.

  Global Instance Is_ValZero_Proper:
    Proper ((=) ==> (iff)) (Is_ValZero).
  Proof.
    unfold Is_ValZero.
    solve_proper.
  Qed.

  Lemma Is_ValZero_to_mkSZero (x:Rtheta):
    (Is_ValZero x) <-> (x = mkSZero).
  Proof.
    split; auto.
  Qed.

  Lemma SZero_is_ValZero:
    Is_ValZero mkSZero.
  Proof.
    unfold Is_ValZero.
    compute.
    reflexivity.
  Qed.

  (* Using setoid equalities on both components *)
  Definition Is_SZero (x:Rtheta) :=
    (evalWriter x = zero) /\
    (execWriter x = RthetaFlagsZero).

  Lemma Is_SZero_mkSZero:
    Is_SZero mkSZero.
  Proof.
    unfold Is_SZero.
    split.
    apply evalWriter_Rtheta_SZero.
    unfold mkSZero.
    unfold execWriter.
    unfold equiv.
    reflexivity.
  Qed.

  (* Double negation on inValZero. Follows from decidability on CarrierA and Propernes of evalWriter *)
  Lemma Is_ValZero_not_not:
    ((not ∘ (not ∘ Is_ValZero)) = Is_ValZero).
  Proof.
    unfold compose, equiv, ext_equiv.
    simpl_relation.
    unfold Is_ValZero.
    rewrite H; clear H.
    generalize dependent (evalWriter y).
    intros c.
    split.
    + intros.
      destruct (CarrierAequivdec c zero).
      assumption.
      contradict H.
      assumption.
    +
      intros.
      destruct (CarrierAequivdec c zero).
      contradict H.
      assumption.
      congruence.
  Qed.

  (* Double negation on inValZero. *)
  Lemma Is_ValZero_not_not_impl:
    forall x, (not ∘ (not ∘ (Is_ValZero))) x <-> Is_ValZero x.
  Proof.
    intros x.
    unfold compose, Is_ValZero.
    destruct (CarrierAequivdec (evalWriter x) zero); crush.
  Qed.


End Zero_Utils.

