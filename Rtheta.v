(* 

R_theta is type which is used as value for vectors in Spiral.  It
holds a value (for example Real) and two boolean flags:

IsStruct: indicates that this value should be treated as "structural"
isSErr: indicates that this value was a result of structural error.

 *)

Require Export CarrierType.

Require Import Coq.Bool.Bool.
Require Import Ring.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders MathClasses.orders.orders.

Require Import CpdtTactics.
Require Import JRWTactics.

(* Rtheta is product type of type A, and two booleans *)
Definition Rtheta := prod (prod CarrierA bool) bool.


(* Some convenient constructros *)
Definition Rtheta_new (val:CarrierA) (is_s_zero is_s_err: bool) := (val, is_s_zero, is_s_err).
Definition Rtheta_normal (val:CarrierA) := (val, false, false).
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
           (oA:CarrierA->CarrierA->CarrierA) (ob1 ob2: bool->bool->bool)
           (a b: Rtheta)
  :=
    (
      oA (RthetaVal a) (RthetaVal b),
      ob1 (RthetaIsStruct a) (RthetaIsStruct b),
      ob2  (RthetaIsSErr a) (RthetaIsSErr b)
    ).

(* Unary application of a function to first element, preserving remaining ones *)
Definition Rtheta_unary
           (oA:CarrierA->CarrierA) 
           (x: Rtheta)
  := (oA (RthetaVal x), (RthetaIsStruct x), (RthetaIsSErr x)).

(* Relation on the first element, ignoring the rest *)
Definition Rtheta_rel_first
           (oA:relation CarrierA)
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

Instance Rtheta_Equivalence_equiv: Equivalence Rtheta_equiv.
Proof.
  split.
  apply Rtheta_Reflexive_equiv.
  apply Rtheta_Symmetric_equiv.
  apply Rtheta_Transitive_equiv.
Qed.

Instance Rtheta_Setoid: Setoid Rtheta.
Proof.
  apply Rtheta_Equivalence_equiv.
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

Instance Rtheta_val_proper:
  Proper ((=) ==> (=)) (RthetaVal).
Proof.
  simpl_relation.
Qed.

Instance Rtheta_plus_proper:
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

Instance Rtheta_neg_proper:
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

Instance Rtheta_mult_proper:
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

Instance Rtheta_RightAbsorb:
  RightAbsorb mult 0.
Proof.
  unfold RightAbsorb.
  intros.
  destruct_Rtheta x.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, plus, mult, Rtheta_Mult, Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  simpl.
  ring.
Qed.

Instance Rtheta_SemiRing: SemiRing Rtheta.
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
  CarrierAledec (RthetaVal x) (RthetaVal y).

Instance Rtheta_ltdec (x y: Rtheta): Decision (x < y) :=
  CarrierAltdec (RthetaVal x) (RthetaVal y).

Program Instance Rtheta_abs: Abs Rtheta := fun (x:Rtheta) =>
                                             (abs (RthetaVal x), RthetaIsStruct x, RthetaIsSErr x).
Next Obligation.
  unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  split; unfold abs; crush.
Qed.

Instance Rtheta_le_proper:
  Proper ((=) ==> (=) ==> (iff)) (Rtheta_Le).
Proof.
  intros a a' aEq b b' bEq.
  unfold Rtheta_Le, Rtheta_rel_first, Rtheta_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta a. destruct_Rtheta b.
  destruct_Rtheta a'. destruct_Rtheta b'.
  simpl.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in aEq, bEq.
  simpl in *.
  rewrite <- aEq, <- bEq.
  split; auto.
Qed.

Instance Rtheta_lt_proper:
  Proper ((=) ==> (=) ==> (iff)) (Rtheta_Lt).
Proof.
  intros a a' aEq b b' bEq.
  unfold Rtheta_Lt, Rtheta_rel_first, Rtheta_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsSErr.
  destruct_Rtheta a. destruct_Rtheta b.
  destruct_Rtheta a'. destruct_Rtheta b'.
  simpl.
  unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal in aEq, bEq.
  simpl in *.
  rewrite <- aEq, <- bEq.
  split; auto.
Qed.

Instance Rtheta_le_Reflexive:
  Reflexive le.
Proof.
  unfold Reflexive.
  intros.
  unfold le, Rtheta_Le, Rtheta_rel_first.
  reflexivity.
Qed.

Instance Rtheta_le_Transitive:
  Transitive le.
Proof.
  unfold Transitive.
  unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
  intros.
  destruct_Rtheta x. destruct_Rtheta y. destruct_Rtheta z.
  simpl in *.
  auto.
Qed.

Instance Rtheta_le_AntiSymmetric:
  AntiSymmetric le.
Proof.
  unfold AntiSymmetric.
  unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal, equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal.
  destruct_Rtheta x. destruct_Rtheta y.
  intros.
  simpl in *.
  apply (antisymmetry (≤)); assumption.
Qed.

Instance Rtheta_le_PreOrder:
  PreOrder le.
Proof.
  split.
  apply Rtheta_le_Reflexive.
  apply Rtheta_le_Transitive.
Qed.

Instance Rtheta_le_PartialOrder:
  PartialOrder Rtheta_Le.
Proof.
  split.
  apply Rtheta_Setoid.
  apply Rtheta_le_proper.
  apply Rtheta_le_PreOrder.
  apply Rtheta_le_AntiSymmetric.
Qed.

Instance Rtheta_le_TotalRelation:
  TotalRelation le.
Proof.
  unfold TotalRelation.
  unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
  destruct_Rtheta x. destruct_Rtheta y.
  simpl.
  apply (total (≤)).
Qed.

Instance Rtheta_TotalOrder: TotalOrder Rtheta_Le.
Proof.
  split.
  apply Rtheta_le_PartialOrder.
  apply Rtheta_le_TotalRelation.
Qed.

Instance Rtheta_plus_Order_Morphism: ∀ (z : Rtheta), Order_Morphism (plus z).
Proof.
  split.
  split.
  apply Rtheta_Setoid.
  apply Rtheta_Setoid.
  apply Rtheta_plus_proper.
  reflexivity.
  apply Rtheta_le_PartialOrder.
  apply Rtheta_le_PartialOrder.
Qed.

Lemma Rtheta_le_plus_lemma1:
  ∀ z x y : Rtheta, x ≤ y <-> z + x ≤ z + y.
Proof.
  intros z x y.
  destruct_Rtheta x.
  destruct_Rtheta y.
  destruct_Rtheta z.
  unfold le, Rtheta_Le, Rtheta_rel_first, plus, Rtheta_Plus, Rtheta_pointwise, RthetaVal.
  simpl.
  assert(H: SemiRingOrder CarrierAle) by apply CarrierASRO.
  destruct H.
  specialize srorder_plus with (z:=z0).
  destruct srorder_plus.
  destruct order_embedding_preserving.
  destruct order_embedding_reflecting.
  split; auto.
Qed.

Instance Rtheta_plus_OrderPreserving: ∀ (z : Rtheta), OrderPreserving (plus z).
Proof.
  split.
  apply Rtheta_plus_Order_Morphism.
  apply Rtheta_le_plus_lemma1.
Qed.

Instance Rtheta_plus_OrderReflecting: ∀ (z : Rtheta), OrderReflecting (plus z).
Proof.
  split.
  apply Rtheta_plus_Order_Morphism.
  apply Rtheta_le_plus_lemma1.
Qed.

Instance Rtheta_plus_OrderEmbedding: ∀ (z : Rtheta), OrderEmbedding (plus z).
Proof.
  intros.
  split.
  apply Rtheta_plus_OrderPreserving.
  apply Rtheta_plus_OrderReflecting.
Qed.

Instance Rtheta_SemiRingOrder: SemiRingOrder Rtheta_Le.
Proof.
  split.
  - apply total_order_po.
  - apply Rtheta_SemiRing.
  - 
    destruct_Rtheta x. destruct_Rtheta y.
    unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
    unfold plus, Rtheta_Plus, Rtheta_pointwise, RthetaVal.
    unfold equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal.
    unfold RthetaIsStruct, RthetaIsSErr.
    simpl.
    intros H.
    exists (y0-x0, false, false).
    simpl; ring.
  - apply Rtheta_plus_OrderEmbedding.
  - destruct_Rtheta x. destruct_Rtheta y.
    unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
    apply CarrierASRO.
Qed.

Lemma Rtheta_eq_equiv:
  forall (a b: Rtheta), eq a b -> equiv a b.
Proof.
  intros.
  crush.
Qed.

