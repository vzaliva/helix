(* Template HCOL. HCOL meta-operators *)

(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import THCOLImpl.
Require Import HCOL.

Require Import Arith.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Open Scope vector_scope.


(* Templete HCOL operator which uses two HOperators to build a new HOperator *)
Class THOperator2 {i1 o1 i2 o2 ix ox} (top: (svector i1 -> svector o1) -> (svector i2 -> svector o2) -> svector ix -> svector ox) :=
  mop_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

(* Curried Templete HCOL operator with arity 2 is HOperators *)
Instance THOperator_HOperator
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
           (f: svector i1 -> svector o1)
           (g: svector i2 -> svector o2):
  svector (i1+i2) -> svector (o1+o2)
  := pair2vector ∘ Cross (f, g) ∘ (@Vbreak Rtheta i1 i2).

Instance HCross_THOperator2 {i1 o1 i2 o2}:
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
           (f: svector i1 -> svector o1)
           (g: svector i1 -> svector o2)
  : svector i1 -> svector (o1+o2) :=
  fun x =>  pair2vector (Stack (f, g) x).

Instance HStack_THOperator2 {i1 o1 o2}:
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

Definition HCompose
           {i1 o2 o3}
           (op1: svector o2 -> svector o3)
           (op2: svector i1 -> svector o2)
  := compose op1 op2.

Notation " g ∘ f " := (HCompose g f)
                        (at level 40, left associativity) : hcol_scope.

Local Open Scope hcol_scope.

(*
Functional compoition of 2 HOperators is also an HCross_HOperator
 *)
Instance HCompose_HOperator
         {i1 o2 o3}
         (op1: svector o2 -> svector o3)
         (op2: svector i1 -> svector o2)
         `{hop1: !HOperator op1}
         `{hop2: !HOperator op2}:
  HOperator (HCompose op1 op2).
Proof.
  unfold HOperator. split; try (apply vec_Setoid).
  intros x y E.
  unfold HOperator in *.
  unfold HCompose, compose.
  rewrite E.
  reflexivity.
Qed.

Definition HTLess {i1 i2 o}
           (f: svector i1 -> svector o)
           (g: svector i2 -> svector o)
  : svector (i1+i2) -> svector o
  := fun v0 => let (v1,v2) := vector2pair i1 v0 in
            ZVLess (f v1, g v2).

Instance HTLess_HOperator {i1 i2 o}
         (op1: svector i1 -> svector o)
         (op2: svector i2 -> svector o)
         `{hop1: !HOperator op1}
         `{hop2: !HOperator op2}:
  HOperator (HTLess op1 op2).
Proof.
  unfold HOperator. split; try (apply vec_Setoid).
  intros x y E.
  unfold HTLess, vector2pair.
  destruct (Vbreak x) as [x0 x1] eqn: X.
  destruct (Vbreak y) as [y0 y1] eqn: Y.
  assert(Ye: Vbreak y = (y0, y1)) by crush.
  assert(Xe: Vbreak x = (x0, x1)) by crush.
  rewrite E in Xe.
  rewrite Xe in Ye.
  clear X Y Xe E.
  inversion Ye. simpl in *.
  rewrite H, H0.
  reflexivity.
Qed.

(* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
just Union of two vectors, produced by application of two operators
to the input.

We put an additional constraint of 'f' and 'g' being HOperators
 *)
Definition HTSUMUnion {i o}
           (f: svector i -> svector o)
           (g: svector i -> svector o)
           `{!HOperator f}
           `{!HOperator g}
           (x: svector i): svector o
  :=  Vec2Union (f x) (g x).

(* Per Vadim's discussion with Franz on 2015-12-14, DirectSum is just
same as Cross, where input vectors are passed as concateneated
vector. Since Coq formalization of HCross is already dfined this way
we just alias DirectSum to it.

We put an additional constraint of 'f' and 'g' being HOperators
 *)
Definition HTDirectSum
           {i1 o1 i2 o2}
           (f: svector i1 -> svector o1)
           (g: svector i2 -> svector o2)
           `{!HOperator f}
           `{!HOperator g}
  : svector (i1+i2) -> svector (o1+o2) := HCross f g.
