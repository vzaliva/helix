(*

R_theta is type which is used as value for vectors in Spiral.  It
holds a value (for example Real) and two boolean flags:

IsStruct: indicates that this value should be treated as "structural"
isVCollision: indicates that this a result of a value collision: an operation on two non-structural values .
isSCollision: indicates that this a result of a structual collision: an operation on two structural values .
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

(* Rtheta is product type of type A, and three booleans *)
Definition Rtheta := prod (prod (prod CarrierA bool) bool) bool.

(* Some convenience constructros *)
Definition Rtheta_new (val:CarrierA) (is_struct is_v_col is_s_col: bool) := (val, is_struct, is_v_col, is_s_col).
Definition Rtheta_normal (val:CarrierA) := (val, false, false, false).
Definition Rtheta_SZero := (0, true, false, false).
Definition Rtheta_SOne := (1, true, false, false).


(* Projections: *)
Definition RthetaVal (x:Rtheta) :=
  match x with
  | (val, is_struct, is_v_col, is_s_col) => val
  end.

Definition RthetaIsStruct (x:Rtheta) :=
  match x with
  | (val, is_struct, is_v_col, is_s_col) => is_struct
  end.

Definition RthetaIsVCollision (x:Rtheta) :=
  match x with
  | (val, is_struct, is_v_col, is_s_col) => is_v_col
  end.

Definition RthetaIsSCollision (x:Rtheta) :=
  match x with
  | (val, is_struct, is_v_col, is_s_col) => is_s_col
  end.

(* Propositional predicates *)
Definition Is_Struct (x:Rtheta) := Is_true (RthetaIsStruct x).
Definition Is_SCollision (x:Rtheta) :=  Is_true (RthetaIsSCollision x).
Definition Is_VCollision (x:Rtheta) :=  Is_true (RthetaIsVCollision x).
Definition Is_Collision (x:Rtheta) :=  Is_SCollision x \/ Is_VCollision x.
Definition Is_Val (x:Rtheta) := (not (Is_Struct x)) /\ (not (Is_Collision x)). (* Non-structural and not collision *)
Definition Is_StructNonCol (x:Rtheta) := (Is_Struct x) /\ (not (Is_Collision x)). (* structural, but not collision *)
Definition Is_SZeroNonCol (x:Rtheta) := Is_StructNonCol x /\ RthetaVal x = 0.

(* Pointwise application of 3 functions to elements of Rtheta *)
Definition Rtheta_pointwise
           (oA:CarrierA->CarrierA->CarrierA) (ob1 ob2 ob3: bool->bool->bool)
           (a b: Rtheta)
  :=
    (
      oA (RthetaVal a) (RthetaVal b),
      ob1 (RthetaIsStruct a) (RthetaIsStruct b),
      ob3  (RthetaIsVCollision a) (RthetaIsVCollision b),
      ob2  (RthetaIsSCollision a) (RthetaIsSCollision b)
    ).

(* Unary application of a function to first element, preserving remaining ones *)
Definition Rtheta_unary
           (oA:CarrierA->CarrierA)
           (x: Rtheta)
  := (oA (RthetaVal x), (RthetaIsStruct x), (RthetaIsVCollision x), (RthetaIsSCollision x)).

(* Relation on the first element, ignoring the rest *)
Definition Rtheta_rel_first
           (oA:relation CarrierA)
           (a b: Rtheta)
  := oA (RthetaVal a) (RthetaVal b).

Ltac destruct_Rtheta x :=
  let x01 := fresh x "01" in
  let x02 := fresh x "02" in
  let x0 := fresh x "_val" in
  let x1 := fresh x "_struct" in
  let x2 := fresh x "_v_col" in
  let x3 := fresh x "_s_col" in
  destruct x as (x01, x3);
    destruct x01 as (x02, x2);
    destruct x02 as (x0, x1).

Section Rtheta_val_Setoid_equiv.
  (* Setoid equality is defined by taking into account only the first element. *)
  Global Instance Rtheta_val_equiv: Equiv Rtheta := Rtheta_rel_first equiv.
  
  Global Instance Rtheta_Reflexive_equiv: Reflexive Rtheta_val_equiv.
  Proof.
    unfold Reflexive.
    intros.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in *.
    reflexivity.
  Qed.
  
  Global Instance Rtheta_Symmetric_equiv: Symmetric Rtheta_val_equiv.
  Proof.
    unfold Reflexive.
    intros.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in *.
    auto.
  Qed.

  Global Instance Rtheta_Transitive_equiv: Transitive Rtheta_val_equiv.
  Proof.
    unfold Reflexive.
    intros.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in *.
    auto.
  Qed.

  Global Instance Rtheta_Equivalence_equiv: Equivalence Rtheta_val_equiv.
  Proof.
    split.
    apply Rtheta_Reflexive_equiv.
    apply Rtheta_Symmetric_equiv.
    apply Rtheta_Transitive_equiv.
  Qed.

  Global Instance Rtheta_Setoid: Setoid Rtheta.
  Proof.
    apply Rtheta_Equivalence_equiv.
  Qed.

  Global Instance Rtheta_Zero: Zero Rtheta := (0, false, false, false).
  Global Instance Rtheta_One: One Rtheta := (1, false, false, false).
  Global Instance Rtheta_Plus: Plus Rtheta := Rtheta_pointwise plus orb orb orb.
  Global Instance Rtheta_Mult: Mult Rtheta := Rtheta_pointwise mult orb orb orb.
  Global Instance Rtheta_Neg: Negate Rtheta := Rtheta_unary negate.
  Global Instance Rtheta_Le: Le Rtheta := Rtheta_rel_first le.
  Global Instance Rtheta_Lt: Lt Rtheta := Rtheta_rel_first lt.

  Global Instance Rtheta_Associative_plus: Associative Rtheta_Plus.
  Proof.
    unfold Associative, HeteroAssociative, Rtheta_Plus, Rtheta_pointwise,
    RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision, equiv, Rtheta_val_equiv, Rtheta_rel_first.
    intros.
    apply plus_assoc.
  Qed.

  Global Instance Rtheta_Associative_mult: Associative Rtheta_Mult.
  Proof.
    unfold Associative, HeteroAssociative, Rtheta_Mult, Rtheta_pointwise,
    RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision, equiv, Rtheta_val_equiv, Rtheta_rel_first.
    intros.
    apply mult_assoc.
  Qed.

  Global Instance Rtheta_val_proper:
    Proper ((=) ==> (=)) (RthetaVal).
  Proof.
    simpl_relation.
  Qed.

  Global Instance Rtheta_plus_proper:
    Proper ((=) ==> (=) ==> (=)) (Rtheta_Plus).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Plus, Rtheta_pointwise, equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta a. destruct_Rtheta b.
    destruct_Rtheta a'. destruct_Rtheta b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in aEq. simpl in aEq.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in bEq. simpl in bEq.
    rewrite aEq, bEq.
    reflexivity.
  Qed.

  Global Instance Rtheta_neg_proper:
    Proper ((=) ==> (=)) (Rtheta_Neg).
  Proof.
    intros a b aEq.
    unfold Rtheta_Neg, Rtheta_unary, equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta a. destruct_Rtheta b.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in aEq. simpl in aEq.
    rewrite aEq.
    reflexivity.
  Qed.

  Global Instance Rtheta_mult_proper:
    Proper ((=) ==> (=) ==> (=)) (Rtheta_Mult).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Mult, Rtheta_pointwise, equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta a. destruct_Rtheta b.
    destruct_Rtheta a'. destruct_Rtheta b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in aEq. simpl in aEq.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in bEq. simpl in bEq.
    rewrite aEq, bEq.
    reflexivity.
  Qed.

  Global Instance Rtheta_SemiGroup_plus:
    @SemiGroup Rtheta Rtheta_val_equiv plus.
  Proof.
    split.
    apply Rtheta_Setoid.
    apply Rtheta_Associative_plus.
    apply Rtheta_plus_proper.
  Qed.

  Global Instance Rtheta_LeftIdentity_plus_0:
    @LeftIdentity Rtheta Rtheta Rtheta_val_equiv plus zero.
  Proof.
    unfold LeftIdentity.
    intros.
    unfold  plus, zero, equiv, Rtheta_val_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta y.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_RightIdentity_plus_0:
    @RightIdentity Rtheta Rtheta_val_equiv Rtheta plus zero.
  Proof.
    unfold RightIdentity.
    intros.
    unfold  plus, zero, equiv, Rtheta_val_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta x.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_Monoid_plus_0:
    @Monoid Rtheta Rtheta_val_equiv plus zero.
  Proof.
    split.
    apply Rtheta_SemiGroup_plus.
    apply Rtheta_LeftIdentity_plus_0.
    apply Rtheta_RightIdentity_plus_0.
  Qed.

  Global Instance Rtheta_Commutative_plus:
    @Commutative Rtheta Rtheta_val_equiv Rtheta plus.
  Proof.
    unfold Commutative.
    intros.
    unfold  plus, zero, equiv, Rtheta_val_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta x.
    destruct_Rtheta y.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_CommutativeMonoid_plus_0:
    @CommutativeMonoid Rtheta Rtheta_val_equiv plus zero.
  Proof.
    split.
    apply Rtheta_Monoid_plus_0.
    apply Rtheta_Commutative_plus.
  Qed.

  Global Instance Rtheta_SemiGroup_mult:
    @SemiGroup Rtheta Rtheta_val_equiv mult.
  Proof.
    split.
    apply Rtheta_Setoid.
    apply Rtheta_Associative_mult.
    apply Rtheta_mult_proper.
  Qed.

  Global Instance Rtheta_LeftIdentity_mult_1:
    @LeftIdentity Rtheta Rtheta Rtheta_val_equiv mult one.
  Proof.
    unfold LeftIdentity.
    intros.
    unfold  mult, one, equiv, Rtheta_val_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
    Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta y.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_RightIdentity_mult_1:
    @RightIdentity Rtheta Rtheta_val_equiv Rtheta mult one.
  Proof.
    unfold RightIdentity.
    intros.
    unfold  mult, one, equiv, Rtheta_val_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
    Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta x.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_Monoid_mult_1:
    @Monoid Rtheta Rtheta_val_equiv mult one.
  Proof.
    split.
    apply Rtheta_SemiGroup_mult.
    apply Rtheta_LeftIdentity_mult_1.
    apply Rtheta_RightIdentity_mult_1.
  Qed.

  Global Instance Rtheta_Commutative_mult:
    @Commutative Rtheta Rtheta_val_equiv Rtheta mult.
  Proof.
    unfold Commutative.
    intros.
    unfold  mult, zero, equiv, Rtheta_val_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
    Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta x. destruct_Rtheta y.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_LeftDistribute_mult_plus:
    LeftDistribute mult plus.
  Proof.
    unfold LeftDistribute, LeftHeteroDistribute, equiv, Rtheta_val_equiv, Rtheta_rel_first, plus, mult, Rtheta_Plus, Rtheta_Mult, Rtheta_pointwise, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    intros.
    destruct_Rtheta a. destruct_Rtheta b. destruct_Rtheta c.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_CommutativeMonoid_mult_1:
    @CommutativeMonoid Rtheta Rtheta_val_equiv mult one.
  Proof.
    split.
    apply Rtheta_Monoid_mult_1.
    apply Rtheta_Commutative_mult.
  Qed.

  Global Instance Rtheta_LeftAbsorb:
    LeftAbsorb mult 0.
  Proof.
    unfold LeftAbsorb.
    intros.
    destruct_Rtheta y.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, plus, mult, Rtheta_Mult, Rtheta_pointwise, RthetaVal, RthetaIsStruct.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_RightAbsorb:
    RightAbsorb mult 0.
  Proof.
    unfold RightAbsorb.
    intros.
    destruct_Rtheta x.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, plus, mult, Rtheta_Mult, Rtheta_pointwise, RthetaVal, RthetaIsStruct.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_SemiRing: SemiRing Rtheta.
  Proof.
    split.
    apply Rtheta_CommutativeMonoid_plus_0.
    apply Rtheta_CommutativeMonoid_mult_1.
    apply Rtheta_LeftDistribute_mult_plus.
    apply Rtheta_LeftAbsorb.
  Qed.

  Global Instance Rtheta_LeftInverse_plus_neg_0:
    LeftInverse plus negate 0.
  Proof.
    unfold LeftInverse, equiv, Rtheta_Plus, Rtheta_Neg, Rtheta_unary, Rtheta_val_equiv, Rtheta_rel_first, Rtheta_pointwise.
    intros.
    destruct_Rtheta x.
    unfold RthetaVal.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_RightInverse_plus_neg_0:
    RightInverse plus negate 0.
  Proof.
    unfold RightInverse, equiv, Rtheta_Plus, Rtheta_Neg, Rtheta_unary, Rtheta_val_equiv, Rtheta_rel_first, Rtheta_pointwise, RthetaVal, RthetaIsStruct.
    intros.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_Group_plus_0_neg:
    @Group Rtheta Rtheta_val_equiv Rtheta_Plus Rtheta_Zero Rtheta_Neg.
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

  Global Instance: Ring Rtheta.
  Proof.
    split. split.
    apply Rtheta_Group_plus_0_neg.
    apply Rtheta_Commutative_plus.
    apply Rtheta_CommutativeMonoid_mult_1.
    apply Rtheta_LeftDistribute_mult_plus.
  Qed.

  Add Ring RingRtheta: (stdlib_ring_theory Rtheta).

  Global Instance Rtheta_ledec (x y: Rtheta): Decision (x ≤ y) :=
    CarrierAledec (RthetaVal x) (RthetaVal y).

  Global Instance Rtheta_ltdec (x y: Rtheta): Decision (x < y) :=
    CarrierAltdec (RthetaVal x) (RthetaVal y).

  Global Program Instance Rtheta_abs: Abs Rtheta := fun (x:Rtheta) =>
                                                      (abs (RthetaVal x), RthetaIsStruct x, RthetaIsVCollision x, RthetaIsSCollision x).
  Next Obligation.
    unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    split; unfold abs; crush.
  Qed.

  Global Instance Rtheta_le_proper:
    Proper ((=) ==> (=) ==> (iff)) (Rtheta_Le).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Le, Rtheta_rel_first, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta a. destruct_Rtheta b.
    destruct_Rtheta a'. destruct_Rtheta b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in aEq, bEq.
    simpl in *.
    rewrite <- aEq, <- bEq.
    split; auto.
  Qed.

  Global Instance Rtheta_lt_proper:
    Proper ((=) ==> (=) ==> (iff)) (Rtheta_Lt).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Lt, Rtheta_rel_first, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal, RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
    destruct_Rtheta a. destruct_Rtheta b.
    destruct_Rtheta a'. destruct_Rtheta b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal in aEq, bEq.
    simpl in *.
    rewrite <- aEq, <- bEq.
    split; auto.
  Qed.

  Global Instance Rtheta_le_Reflexive:
    Reflexive le.
  Proof.
    unfold Reflexive.
    intros.
    unfold le, Rtheta_Le, Rtheta_rel_first.
    reflexivity.
  Qed.

  Global Instance Rtheta_le_Transitive:
    Transitive le.
  Proof.
    unfold Transitive.
    unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
    intros.
    destruct_Rtheta x. destruct_Rtheta y. destruct_Rtheta z.
    simpl in *.
    auto.
  Qed.

  Global Instance Rtheta_le_AntiSymmetric:
    AntiSymmetric le.
  Proof.
    unfold AntiSymmetric.
    unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal, equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal.
    destruct_Rtheta x. destruct_Rtheta y.
    intros.
    simpl in *.
    apply (antisymmetry (≤)); assumption.
  Qed.

  Global Instance Rtheta_le_PreOrder:
    PreOrder le.
  Proof.
    split.
    apply Rtheta_le_Reflexive.
    apply Rtheta_le_Transitive.
  Qed.

  Global Instance Rtheta_le_PartialOrder:
    PartialOrder Rtheta_Le.
  Proof.
    split.
    apply Rtheta_Setoid.
    apply Rtheta_le_proper.
    apply Rtheta_le_PreOrder.
    apply Rtheta_le_AntiSymmetric.
  Qed.

  Global Instance Rtheta_le_TotalRelation:
    TotalRelation le.
  Proof.
    unfold TotalRelation.
    unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
    destruct_Rtheta x. destruct_Rtheta y.
    simpl.
    apply (total (≤)).
  Qed.

  Global Instance Rtheta_TotalOrder: TotalOrder Rtheta_Le.
  Proof.
    split.
    apply Rtheta_le_PartialOrder.
    apply Rtheta_le_TotalRelation.
  Qed.

  Global Instance Rtheta_plus_Order_Morphism: ∀ (z : Rtheta), Order_Morphism (plus z).
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
    specialize srorder_plus with (z:=z_val).
    destruct srorder_plus.
    destruct order_embedding_preserving.
    destruct order_embedding_reflecting.
    split; auto.
  Qed.

  Global Instance Rtheta_plus_OrderPreserving: ∀ (z : Rtheta), OrderPreserving (plus z).
  Proof.
    split.
    apply Rtheta_plus_Order_Morphism.
    apply Rtheta_le_plus_lemma1.
  Qed.

  Global Instance Rtheta_plus_OrderReflecting: ∀ (z : Rtheta), OrderReflecting (plus z).
  Proof.
    split.
    apply Rtheta_plus_Order_Morphism.
    apply Rtheta_le_plus_lemma1.
  Qed.

  Global Instance Rtheta_plus_OrderEmbedding: ∀ (z : Rtheta), OrderEmbedding (plus z).
  Proof.
    intros.
    split.
    apply Rtheta_plus_OrderPreserving.
    apply Rtheta_plus_OrderReflecting.
  Qed.

  Global Instance Rtheta_SemiRingOrder: SemiRingOrder Rtheta_Le.
  Proof.
    split.
    - apply total_order_po.
    - apply Rtheta_SemiRing.
    -
      destruct_Rtheta x. destruct_Rtheta y.
      unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
      unfold plus, Rtheta_Plus, Rtheta_pointwise, RthetaVal.
      unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, RthetaVal.
      unfold RthetaIsStruct, RthetaIsVCollision, RthetaIsSCollision.
      simpl.
      intros H.
      exists (y_val-x_val, false, false, false).
      simpl; ring.
    - apply Rtheta_plus_OrderEmbedding.
    - destruct_Rtheta x. destruct_Rtheta y.
      unfold le, Rtheta_Le, Rtheta_rel_first, RthetaVal.
      apply CarrierASRO.
  Qed.

  Lemma Rtheta_eq_val_equiv:
    forall (a b: Rtheta), eq a b -> Rtheta_val_equiv a b.
  Proof.
    intros.
    crush.
  Qed.

End Rtheta_val_Setoid_equiv.

Section Rtheta_Poinitwise_Setoid_equiv.

  (* Setoid equality is defined by pointwise comparison of all elements. *)
  Global Instance Rtheta_pw_equiv: Equiv Rtheta := fun a b =>
    match a, b with
      (a_val, a_struct, a_v_col, a_s_col), (b_val, b_struct, b_v_col, b_s_col) =>
      a_val = b_val /\
      a_struct ≡ b_struct /\
      a_v_col ≡ b_v_col /\
      a_s_col ≡ b_s_col
    end.

  Lemma Rtheta_poinitwise_equiv_equiv (a b: Rtheta):
    Rtheta_pw_equiv a b -> Rtheta_val_equiv a b.
  Proof.
    destruct_Rtheta a. destruct_Rtheta b.
    crush.
  Qed.

  Lemma Rtheta_eq_pw_equiv:
    forall (a b: Rtheta), eq a b -> Rtheta_pw_equiv a b.
  Proof.
    intros.
    destruct_Rtheta a. destruct_Rtheta b.
    tuple_inversion.
    crush.
  Qed.
  
End Rtheta_Poinitwise_Setoid_equiv.

Lemma Rtheta_Val_is_not_Struct:
  ∀ z : Rtheta, Is_Val z → ¬Is_Struct z.
Proof.
  intros z H.
  unfold Is_Val in H.
  destruct H as [H1 H2].
  assumption.
Qed.

