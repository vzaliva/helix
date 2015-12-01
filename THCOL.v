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

Definition HCross
           {i1 o1 i2 o2}
           (f: svector i1 -> svector o1)
           (g: svector i2 -> svector o2)
  : svector (i1+i2) -> svector (o1+o2) :=
  fun x =>  pair2vector (Cross (f, g) (Vbreak x)).


Instance HCross_arg_proper
       {i1 o1 i2 o2}
       `(xop1pf: !Proper ((=) ==> (=)) (xop1: svector i1 -> svector o1))
       `(xop2pf: !Proper ((=) ==> (=)) (xop2: svector i2 -> svector o2)):
  Proper ((=) ==> (=)) (HCross xop1 xop2).
Proof.
  intros x y E.
  unfold HCross.
  unfold compose, pair2vector, vector2pair.
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

Instance HCross_proper {i1 o1 i2 o2:nat}:
    Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> ((=) ==> (=))) (@HCross i1 o1 i2 o2).
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

Instance HStack_arg_proper
       {i1 o1 o2}
       `(xop1pf: !Proper ((=) ==> (=)) (xop1: svector i1 -> svector o1))
       `(xop2pf: !Proper ((=) ==> (=)) (xop2: svector i1 -> svector o2)):
  Proper ((=) ==> (=)) (HStack xop1 xop2).
Proof.
  intros x y E.
  unfold HStack.
  unfold pair2vector.
  simpl.
  rewrite E.
  reflexivity.
Qed.

(* HCompose becomes just ∘ *)

Definition HTLess {i1 i2 o}
           (lop1: svector i1 -> svector o)
           (lop2: svector i2 -> svector o)
  : svector (i1+i2) -> svector o
  := fun v0 => let (v1,v2) := vector2pair i1 v0 in
            ZVLess (lop1 v1, lop2 v2).

Instance HTLess_arg_proper {i1 i2 o}
       `(!Proper ((=) ==> (=)) (lop1: svector i1 -> svector o))
       `(!Proper ((=) ==> (=)) (lop2: svector i2 -> svector o)):
  Proper ((=) ==> (=)) (@HTLess i1 i2 o lop1 lop2).
Proof.
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

