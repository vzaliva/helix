(* 

R_theta is type which is used as value for vectors in Spiral.  It
holds a value (for example Real) and two boolean flags:

IsStruct: indicates that this value should be treated as "structural"
isSErr: indicates that this value was a result of structural error.

 *)

Require Import Coq.Bool.Bool.
Require Import Ring.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.

Require Import CpdtTactics.

Parameter A: Type.
Parameter Ae: Equiv A.
Parameter Az: Zero A.
Parameter A1: One A.
Parameter Aplus: Plus A.
Parameter Amult: Mult A.
Parameter Aneg: Negate A.
Parameter Ale: Le A.
Parameter Alt: Lt A.
Parameter Asetoid: @Setoid A Ae.
Parameter Aabs: @Abs A Ae Ale Az Aneg.
Parameter Aledec: ∀ x y: A, Decision (x ≤ y).
Parameter Ar: Ring A.

Add Ring RingA: (stdlib_ring_theory A).

(* Rtheta is product type of type A, and two booleans *)
Definition Rtheta := prod (prod A bool) bool.


(* Some convenient constructros *)
Definition Rtheta_new (val:A) (is_s_zero is_s_err: bool) := (val, is_s_zero, is_s_err).
Definition Rtheta_normal (val:A) := (val, false, false).
Definition Rtheta_szero := (0, true, false).
Definition Rtheta_szero_err := (0, true, true).


(* Projections: *)
Definition RthetaVal (x:Rtheta) := fst (fst x). (* value *)
Definition RthetaIsStruct (x:Rtheta) := snd (fst x). (* structural *)
Definition RthetaIsSErr (x:Rtheta) := snd x. (* structural error *)

(* Propositional predicates *)
Definition Is_Struct (x:Rtheta) := Is_true (RthetaIsStruct x).
Definition Is_SErr (x:Rtheta) :=  Is_true (RthetaIsSErr x).
Definition Is_SZero (x:Rtheta) := (Is_Struct x) /\ (RthetaVal x ≡ 0). (* The value is structural zero. Error flag is ignored *)
Definition Is_Val (x:Rtheta) := (not (Is_Struct x)) /\ (not (Is_SErr x)). (* Non-structural and not error *)
Definition Is_StructNonErr (x:Rtheta) := (Is_Struct x) /\ (not (Is_SErr x)). (* structural, but not error *)

(* Pointwise application of 3 functions to elements of Rtheta *)
Definition Rtheta_pointwise 
           (oA:A->A->A) (ob1 ob2: bool->bool->bool)
           (a b: Rtheta)
  :=
    (
      oA (RthetaVal a) (RthetaVal b),
      ob1 (RthetaIsStruct a) (RthetaIsStruct b),
      ob2  (RthetaIsSErr a) (RthetaIsSErr b)
    ).

(* Unary application of a function to first element, preserving remaining ones *)
Definition Rtheta_unary
           (oA:A->A) 
           (x: Rtheta)
  := (oA (RthetaVal x), (RthetaIsStruct x), (RthetaIsSErr x)).

(* Relation on the first element, ignoring the rest *)
Definition Rtheta_rel_first
           (oA:relation A)
           (a b: Rtheta)
  := oA (RthetaVal a) (RthetaVal b).

(* Setoid equality is defined by taking into account only the first element. If you need full equality, use 'eq' instead *)
Instance Rtheta_equiv: Equiv Rtheta := Rtheta_rel_first equiv.

(* --- Rheta properties (as MathClasses instances) below --- *)

Instance Rtheta_Reflexive_equiv: Reflexive Rtheta_equiv.
Proof.
  unfold Reflexive.
  intros. 
  unfold equiv, Rtheta_equiv, Rtheta_rel_first in *.
  reflexivity.
Qed.

Instance Rtheta_Symmetric_equiv: Symmetric Rtheta_equiv.
Proof.
  unfold Reflexive.
  intros. 
  unfold equiv, Rtheta_equiv, Rtheta_rel_first in *.
  auto.
Qed.

Instance Rtheta_Transitive_equiv: Transitive Rtheta_equiv.
Proof.
  unfold Reflexive.
  intros. 
  unfold equiv, Rtheta_equiv, Rtheta_rel_first in *.
  auto.
Qed.

Instance Rtheta_Setoid: Setoid Rtheta.
Proof.
  split.
  apply Rtheta_Reflexive_equiv.
  apply Rtheta_Symmetric_equiv.
  apply Rtheta_Transitive_equiv.
Qed.

Instance Rtheta_Zero: Zero Rtheta := (0, false, false).
Instance Rtheta_One: One Rtheta := (1, false, false).
Instance Rtheta_Plus: Plus Rtheta := Rtheta_pointwise plus orb orb.
Instance Rtheta_Mult: Mult Rtheta := Rtheta_pointwise mult orb orb.
Instance Rtheta_Neg: Negate Rtheta := Rtheta_unary negate.
Instance Rtheta_Le: Le Rtheta := Rtheta_rel_first le.
Instance Rtheta_Lt: Lt Rtheta := Rtheta_rel_first lt.

Instance Rtheta_Associative_plus: Associative Rtheta_Plus.
Proof.
  unfold Associative, HeteroAssociative, Rtheta_Plus, Rtheta_pointwise,
  RthetaVal, RthetaIsStruct, RthetaIsSErr, equiv, Rtheta_equiv, Rtheta_rel_first.
  intros.
  apply plus_assoc.
Qed.

Instance Rtheta_Associative_mult: Associative Rtheta_Mult.
Proof.
  unfold Associative, HeteroAssociative, Rtheta_Mult, Rtheta_pointwise,
  RthetaVal, RthetaIsStruct, RthetaIsSErr, equiv, Rtheta_equiv, Rtheta_rel_first.
  intros.
  apply mult_assoc.
Qed.

Ltac destruct_Rtheta x :=
  let x01 := fresh x "01" in
  let x2 := fresh x "2" in
  let x0 := fresh x "0" in
  let x1 := fresh x "1" in
  destruct x as (x01, x2); 
    destruct x01 as (x0, x1).

Global Instance Rtheta_plus_proper:
  Proper ((=) ==> (=) ==> (=)) (Rtheta_Plus).
Proof.
  intros a a' aEq b b' bEq.
  unfold Rtheta_Plus, Rtheta_pointwise, equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta a. destruct_Rtheta b.
  destruct_Rtheta a'. destruct_Rtheta b'.
  simpl.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in aEq. simpl in aEq.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in bEq. simpl in bEq.
  rewrite aEq, bEq.
  reflexivity.
Qed.

Global Instance Rtheta_neg_proper:
  Proper ((=) ==> (=)) (Rtheta_Neg).
Proof.
  intros a b aEq.
  unfold Rtheta_Neg, Rtheta_unary, equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta a. destruct_Rtheta b.
  simpl.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in aEq. simpl in aEq.
  rewrite aEq.
  reflexivity.
Qed.

Global Instance Rtheta_mult_proper:
  Proper ((=) ==> (=) ==> (=)) (Rtheta_Mult).
Proof.
  intros a a' aEq b b' bEq.
  unfold Rtheta_Mult, Rtheta_pointwise, equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta a. destruct_Rtheta b.
  destruct_Rtheta a'. destruct_Rtheta b'.
  simpl.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in aEq. simpl in aEq.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in bEq. simpl in bEq.
  rewrite aEq, bEq.
  reflexivity.
Qed.

Instance Rtheta_SemiGroup_plus:
  @SemiGroup Rtheta Rtheta_equiv plus.
Proof.
  split.
  apply Rtheta_Setoid.
  apply Rtheta_Associative_plus.
  apply Rtheta_plus_proper.
Qed.

Instance Rtheta_LeftIdentity_plus_0:
  @LeftIdentity Rtheta Rtheta Rtheta_equiv plus zero.
Proof.
  unfold LeftIdentity.
  intros.
  unfold  plus, zero, equiv, Rtheta_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
  Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta y.
  simpl.
  ring.
Qed.

Instance Rtheta_RightIdentity_plus_0:
  @RightIdentity Rtheta Rtheta_equiv Rtheta plus zero.
Proof.
  unfold RightIdentity.
  intros.
  unfold  plus, zero, equiv, Rtheta_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
  Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta x.
  simpl.
  ring.
Qed.

Instance Rtheta_Monoid_plus_0:
  @Monoid Rtheta Rtheta_equiv plus zero.
Proof.
  split.
  apply Rtheta_SemiGroup_plus.
  apply Rtheta_LeftIdentity_plus_0.
  apply Rtheta_RightIdentity_plus_0.
Qed.

Instance Rtheta_Commutative_plus:
  @Commutative Rtheta Rtheta_equiv Rtheta plus.
Proof.
  unfold Commutative.
  intros.
  unfold  plus, zero, equiv, Rtheta_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
  Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta x.
  destruct_Rtheta y.
  simpl.
  ring.
Qed.

Instance Rtheta_CommutativeMonoid_plus_0:
  @CommutativeMonoid Rtheta Rtheta_equiv plus zero.
Proof.
  split.
  apply Rtheta_Monoid_plus_0.
  apply Rtheta_Commutative_plus.
Qed.

Instance Rtheta_SemiGroup_mult:
  @SemiGroup Rtheta Rtheta_equiv mult.
Proof.
  split.
  apply Rtheta_Setoid.
  apply Rtheta_Associative_mult.
  apply Rtheta_mult_proper.
Qed.

Instance Rtheta_LeftIdentity_mult_1:
  @LeftIdentity Rtheta Rtheta Rtheta_equiv mult one.
Proof.
  unfold LeftIdentity.
  intros.
  unfold  mult, one, equiv, Rtheta_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
  Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta y.
  simpl.
  ring.
Qed.

Instance Rtheta_RightIdentity_mult_1:
  @RightIdentity Rtheta Rtheta_equiv Rtheta mult one.
Proof.
  unfold RightIdentity.
  intros.
  unfold  mult, one, equiv, Rtheta_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
  Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta x.
  simpl.
  ring.
Qed.

Instance Rtheta_Monoid_mult_1:
  @Monoid Rtheta Rtheta_equiv mult one.
Proof.
  split.
  apply Rtheta_SemiGroup_mult.
  apply Rtheta_LeftIdentity_mult_1.
  apply Rtheta_RightIdentity_mult_1.
Qed.

Instance Rtheta_Commutative_mult:
  @Commutative Rtheta Rtheta_equiv Rtheta mult.
Proof.
  unfold Commutative.
  intros.
  unfold  mult, zero, equiv, Rtheta_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
  Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta x. destruct_Rtheta y.
  simpl.
  ring.
Qed.

Instance Rtheta_LeftDistribute_mult_plus:
  LeftDistribute mult plus.
Proof.
  unfold LeftDistribute, LeftHeteroDistribute, equiv, Rtheta_equiv, Rtheta_rel_first, plus, mult, Rtheta_Plus, Rtheta_Mult, Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  intros.
  destruct_Rtheta a. destruct_Rtheta b. destruct_Rtheta c.
  simpl.
  ring.
Qed.

Instance Rtheta_CommutativeMonoid_mult_1:
  @CommutativeMonoid Rtheta Rtheta_equiv mult one.
Proof.
  split.
  apply Rtheta_Monoid_mult_1.
  apply Rtheta_Commutative_mult.
Qed.

Instance Rtheta_LeftAbsorb:
  LeftAbsorb mult 0.
Proof.
  unfold LeftAbsorb.
  intros.
  destruct_Rtheta y.    
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, plus, mult, Rtheta_Mult, Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  simpl.
  ring.
Qed.

Instance: SemiRing Rtheta.
Proof.
  split.
  apply Rtheta_CommutativeMonoid_plus_0.
  apply Rtheta_CommutativeMonoid_mult_1.
  apply Rtheta_LeftDistribute_mult_plus.
  apply Rtheta_LeftAbsorb.
Qed.

Instance Rtheta_LeftInverse_plus_neg_0:
  LeftInverse plus negate 0.
Proof.
  unfold LeftInverse, equiv, Rtheta_Plus, Rtheta_Neg, Rtheta_unary, Rtheta_equiv, Rtheta_rel_first, Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  intros.
  simpl.
  ring.
Qed.

Instance Rtheta_RightInverse_plus_neg_0:
  RightInverse plus negate 0.
Proof.
  unfold RightInverse, equiv, Rtheta_Plus, Rtheta_Neg, Rtheta_unary, Rtheta_equiv, Rtheta_rel_first, Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  intros.
  simpl.
  ring.
Qed.

Instance Rtheta_Group_plus_0_neg:
  @Group Rtheta Rtheta_equiv Rtheta_Plus Rtheta_Zero Rtheta_Neg.
Proof.
  split.
  apply Rtheta_Monoid_plus_0.
  split.
  apply Rtheta_Setoid.
  apply Rtheta_Setoid.
  apply Rtheta_neg_proper.
  apply Rtheta_LeftInverse_plus_neg_0.
  apply Rtheta_RightInverse_plus_neg_0.
Qed.

Instance: Ring Rtheta.
Proof.
  split. split.
  apply Rtheta_Group_plus_0_neg.
  apply Rtheta_Commutative_plus.
  apply Rtheta_CommutativeMonoid_mult_1.
  apply Rtheta_LeftDistribute_mult_plus.
Qed.  

Add Ring RingRtheta: (stdlib_ring_theory Rtheta).
  
Instance Rtheta_ledec (x y: Rtheta): Decision (x ≤ y) :=
  Aledec (RthetaVal x) (RthetaVal y).

Program Instance Rtheta_abs: Abs Rtheta := fun (x:Rtheta) =>
                                             (abs (RthetaVal x), RthetaIsStruct x, RthetaIsSErr x).
Next Obligation.
  unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  split; unfold abs; crush.
Qed.
