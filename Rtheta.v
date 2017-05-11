(* R_theta is type which is used as value for vectors in SPIRAL.  *)

Require Export CarrierType.

Require Import Coq.Bool.Bool.
Require Import Ring.

Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import WriterMonadNoT.
Require Import ExtLib.Data.PPair.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders MathClasses.orders.orders.

Require Import SpiralTactics.

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
Definition IsVal (x:RthetaFlags) := not (Is_true (is_struct x)).

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

(* mzero *)
Definition RthetaFlagsZero := mkRthetaFlags true false.

Global Instance RthetaFlags_type:
  type RthetaFlags := type_libniz RthetaFlags.

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
End RMonad.

Definition Rtheta := Rtheta' Monoid_RthetaFlags.
Definition RStheta := Rtheta' Monoid_RthetaSafeFlags.

(* Monad morhisms *)

Definition Rtheta2RStheta: Rtheta -> RStheta := castWriter Monoid_RthetaSafeFlags.

Definition RStheta2Rtheta: RStheta -> Rtheta := castWriter Monoid_RthetaFlags.

(* Some convenience constructros *)

Section Rtheta'Utils.
  Context {fm:Monoid RthetaFlags}.
  Context {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}.

  Definition mkStruct (val: CarrierA) : Rtheta' fm
    := ret val.
  (* Structural zero is 0 value combined with 'mzero' monoid flags *)
  Definition mkSZero : Rtheta' fm := mkStruct 0.

  Definition mkValue (val: CarrierA) : Rtheta' fm :=
    tell (mkRthetaFlags false false) ;; ret val.

  Definition Is_Val: (Rtheta' fm) -> Prop :=
    IsVal ∘ (@execWriter RthetaFlags CarrierA fm).

  Definition Is_Struct:= not ∘ Is_Val.

  Definition Is_Collision (x:Rtheta' fm) :=
    (IsCollision ∘ (@execWriter RthetaFlags CarrierA fm)) x.

  Definition Not_Collision := not ∘ Is_Collision.

  Lemma IsVal_mkValue:
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

  Global Instance Rtheta'_equiv: Equiv (Rtheta' fm) :=
    fun am bm => (evalWriter am) = (evalWriter bm).

  Global Instance evalWriter_proper:
    Proper ((=) ==> (=)) (@evalWriter RthetaFlags CarrierA fm).
  Proof.
    simpl_relation.
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

  (* Note: definitional equality *)
  Lemma evalWriter_Rtheta_liftM2
        (op: CarrierA -> CarrierA -> CarrierA)
        {a b: Rtheta' fm}
    :
      evalWriter (liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
  Proof.
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


End Rtheta'Utils.

(* For some reason class resolver could not figure this out on it's own *)
Global Instance Rtheta_equiv: Equiv (Rtheta) := Rtheta'_equiv.
Global Instance RStheta_equiv: Equiv (RStheta) := Rtheta'_equiv.

Ltac unfold_Rtheta_equiv := unfold equiv, Rtheta_equiv, Rtheta'_equiv in *.
Ltac unfold_RStheta_equiv := unfold equiv, RStheta_equiv, Rtheta'_equiv in *.

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

Lemma Is_Val_mkStruct:
  forall a, not (@Is_Val _ (@mkStruct Monoid_RthetaFlags a)).
Proof.
  intros a.
  unfold Is_Val, compose, mkStruct, IsVal, execWriter, runWriter.
  simpl.
  tauto.
Qed.

Lemma Is_Val_mkSZero:
  @Is_Val _ (@mkSZero Monoid_RthetaFlags) -> False.
Proof.
  unfold mkSZero.
  apply Is_Val_mkStruct.
Qed.

Lemma Is_Struct_mkSZero:
  @Is_Struct _ (@mkSZero Monoid_RthetaFlags).
Proof.
  unfold Is_Struct, compose, not.
  apply Is_Val_mkSZero.
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
  unfold Is_Struct, Is_Val, compose, IsVal, Is_true, not in *.
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

Lemma Not_Collision_Safe_mkStruct:
  ∀ (v:CarrierA), @Not_Collision Monoid_RthetaSafeFlags (mkStruct v).
Proof.
  intros v.
  unfold Not_Collision, Is_Collision, not, mkStruct, compose.
  simpl.
  trivial.
Qed.

Section Decidablitiy.
  Global Instance IsVal_dec (x: RthetaFlags) : Decision (IsVal x).
  Proof.
    unfold Decision, IsVal.
    destruct x.
    destr_bool; auto.
  Qed.

  Global Instance Is_Val_dec
         {fm:Monoid RthetaFlags}
         (x: Rtheta' fm):
    Decision (Is_Val x).
  Proof.
    unfold Decision.
    unfold Is_Val, compose.
    generalize (WriterMonadNoT.execWriter x). intros f.
    apply IsVal_dec.
  Qed.

End Decidablitiy.

Section Zero_Utils.

  Lemma evalWriter_Rtheta_SZero
        {fm:Monoid RthetaFlags}
  :
    @evalWriter _ _ fm mkSZero = zero.
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

  Definition Is_ValZero {fm:Monoid RthetaFlags} (x:Rtheta' fm)
    := (evalWriter x) = 0.

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
    apply evalWriter_Rtheta_SZero.
    unfold mkSZero.
    unfold execWriter.
    unfold equiv.
    simpl.
    reflexivity.
  Qed.

  (* Double negation on inValZero. Follows from decidability on CarrierA and Propernes of evalWriter *)
  Lemma Is_ValZero_not_not
        {fm:Monoid RthetaFlags}
    :
      ((not ∘ (not ∘ @Is_ValZero fm)) = Is_ValZero).
  Proof.
    unfold compose, equiv, ext_equiv.
    simpl_relation.
    unfold Is_ValZero.
    rewrite_clear H.
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
  Lemma Is_ValZero_not_not_impl
        {fm:Monoid RthetaFlags}
    :
      forall x, (not ∘ (not ∘ (@Is_ValZero fm))) x <-> Is_ValZero x.
  Proof.
    intros x.
    unfold compose, Is_ValZero.
    destruct (CarrierAequivdec (evalWriter x) zero); crush.
  Qed.


End Zero_Utils.

