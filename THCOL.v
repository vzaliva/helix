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

Global Instance HCross_arg_proper
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

(* Apply 2 functions to 2 inputs returning tuple of results *)
Definition HOCross {i1 o1 i2 o2} (f:@HOperator i1 o1) (g:@HOperator i2 o2): @HOperator (i1+i2) (o1+o2)
  := Build_HOperator _ _ (HCross (op f) (op g)) (HCross_arg_proper (opf f) (opf g)).

Definition HStack
           {i1 o1 o2}
           (f: svector i1 -> svector o1)
           (g: svector i1 -> svector o2)
  : svector i1 -> svector (o1+o2) :=
  fun x =>  pair2vector (Stack (f, g) x).

Global Instance HStack_arg_proper
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

(* Apply 2 functions to the same input returning tuple of results *)
Definition HOStack {i o1 o2} (f:@HOperator i o1) (g:@HOperator i o2): @HOperator i (o1+o2) 
  := Build_HOperator _ _ (HStack (op f) (op g)) (HStack_arg_proper (opf f) (opf g)).

(* HCompose becomes just ∘ *)

Definition HTLess {i1 i2 o}
           (lop1: svector i1 -> svector o)
           (lop2: svector i2 -> svector o)
  : svector (i1+i2) -> svector o
  := fun v0 => let (v1,v2) := vector2pair i1 v0 in
            ZVLess (lop1 v1, lop2 v2).

Global Instance HTLess_arg_proper {i1 i2 o}
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

(* Apply 2 functions to the same input returning tuple of results *)
Definition HOTLess {i1 i2 o} (f:@HOperator i1 o) (g:@HOperator i2 o): @HOperator (i1+i2) o
  := Build_HOperator _ _ (HTLess (op f) (op g)) (HTLess_arg_proper (opf f) (opf g)).

