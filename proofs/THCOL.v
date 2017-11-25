(* Template HCOL. HCOL meta-operators *)

Require Import Spiral.VecUtil.
Require Import Spiral.VecSetoid.
Require Import Spiral.Spiral.
Require Import Spiral.CarrierType.
Require Import Spiral.THCOLImpl.
Require Import Spiral.HCOL.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Program.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.

Require Import Spiral.SpiralTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.


Import VectorNotations.
Open Scope vector_scope.

(* Templete HCOL operator which uses two HOperators to build a new HOperator *)
Class THOperator2 {i1 o1 i2 o2 ix ox} (top: (avector i1 -> avector o1) -> (avector i2 -> avector o2) -> avector ix -> avector ox) :=
  THOperator2_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

(* Curried Templete HCOL operator with arity 2 is HOperators *)
Global Instance THOperator_HOperator
         `{O1: @HOperator i1 o1 op1}
         `{O2: @HOperator i2 o2 op2}
         `{T: @THOperator2 i1 o1 i2 o2 ix ox to}:
  HOperator (to op1 op2).
Proof.
  split; try apply vec_Setoid.
  apply T ; [apply O1 | apply O2].
Qed.

Definition HCross
           {i1 o1 i2 o2}
           (f: avector i1 -> avector o1)
           (g: avector i2 -> avector o2):
  avector (i1+i2) -> avector (o1+o2)
  := pair2vector ∘ Cross (f, g) ∘ (@Vbreak CarrierA i1 i2).

Global Instance HCross_THOperator2 {i1 o1 i2 o2}:
  THOperator2 (@HCross i1 o1 i2 o2).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold HCross, compose, pair2vector, vector2pair.
  destruct (Vbreak x) as [x0 x1] eqn: X.
  destruct (Vbreak y) as [y0 y1] eqn: Y.
  assert(Ye: Vbreak y = (y0, y1)) by crush.
  assert(Xe: Vbreak x = (x0, x1)) by crush.
  rewrite Ex in Xe.
  rewrite Xe in Ye.
  clear X Y Xe Ex.
  inversion Ye. rename H into Ey, H0 into Ex.
  simpl in *.

  assert(A1: f x0 = f' y0).
  apply Ef, Ey.
  rewrite A1.

  assert(A2: g x1 = g' y1).
  apply Eg, Ex.
  rewrite A2.
  reflexivity.
Qed.

Definition HStack
           {i1 o1 o2}
           (f: avector i1 -> avector o1)
           (g: avector i1 -> avector o2)
  : avector i1 -> avector (o1+o2) :=
  fun x =>  pair2vector (Stack (f, g) x).

Global Instance HStack_THOperator2 {i1 o1 o2}:
  THOperator2 (@HStack i1 o1 o2).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold HStack, compose, pair2vector, vector2pair, Stack.
  setoid_replace (f x) with (f' y).
  setoid_replace (g x) with (g' y).
  reflexivity.
  apply Eg; assumption.
  apply Ef; assumption.
Qed.


Global Instance compose_THOperator2 {o2 o3 i1 o2:nat}:
  @THOperator2 o2 o3 i1 o2 i1 o3 (compose).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold compose, pair2vector, vector2pair.
  apply Ef, Eg, Ex.
Qed.


Global Instance compose_HOperator
         {i1 o2 o3}
        `{hop1: HOperator o2 o3 op1}
        `{hop2: HOperator i1 o2 op2}
:
  HOperator (op1 ∘ op2).
Proof.
  unfold HOperator. split; try (apply vec_Setoid).
  intros x y E.
  unfold compose.
  rewrite E.
  reflexivity.
Qed.

Definition HTLess {i1 i2 o}
           (f: avector i1 -> avector o)
           (g: avector i2 -> avector o)
  : avector (i1+i2) -> avector o
  := fun v0 => let (v1,v2) := vector2pair i1 v0 in
               ZVLess (f v1, g v2).

Global Instance HTLess_THOperator2 {i1 i2 o}:
  THOperator2 (@HTLess i1 i2 o).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold HTLess, compose, pair2vector, vector2pair, ZVLess.
  destruct (Vbreak x) as [x0 x1] eqn: X.
  destruct (Vbreak y) as [y0 y1] eqn: Y.
  assert(Ye: Vbreak y = (y0, y1)) by crush.
  assert(Xe: Vbreak x = (x0, x1)) by crush.
  rewrite Ex in Xe.
  rewrite Xe in Ye.
  clear X Y Xe Ex.
  inversion Ye. rename H into Ey, H0 into Ex.
  simpl in *.
  setoid_replace (f x0) with (f' y0).
  setoid_replace (g x1) with (g' y1).
  reflexivity.
  apply Eg, Ex.
  apply Ef, Ey.
Qed.

(* Per Vadim's discussion with Franz on 2015-12-14, DirectSum is just
same as Cross, where input vectors are passed as concateneated
vector. Since Coq formalization of HCross is already dfined this way
we just alias DirectSum to it.
 *)
Notation HTDirectSum := HCross.

(* Not sure if this is needed *)
Global Instance HTDirectSum_THOperator2 {i1 o1 i2 o2}:
  THOperator2 (@HTDirectSum i1 o1 i2 o2) := HCross_THOperator2.



