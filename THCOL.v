(* Template HCOL. HCOL meta-operators *)

(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import HCOLImpl.
Require Import HCOL.

Require Import Arith.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import CpdtTactics.
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

(* Apply 2 functions to the same input returning tuple of results *)
Definition Stack {D R S: Type} (fg:(D->R)*(D->S)) (x:D) : (R*S) :=
  match fg with
  | (f,g) => pair (f x) (g x)
  end.

(* Apply 2 functions to 2 inputs returning tuple of results *)
Definition Cross {D R E S: Type} (fg:(D->R)*(E->S)) (x:D*E) : (R*S) :=
  match fg with
  | (f,g) => match x with
            | (x0,x1) => pair (f x0) (g x1)
            end
  end.

Global Instance Cross_proper
       {D R E S: Type}
       `{Equiv D,Equiv R,Equiv E,Equiv S}
       (f:D->R)
       (g:E->S)
       `{pF: !Proper ((=) ==> (=)) f}
       `{pG: !Proper ((=) ==> (=)) g}:
  Proper ((=) ==> (=))  (Cross (f,g)).
Proof.
  intros fg fg' fgE.
  destruct fg, fg'.
  destruct fgE as [M2 M1]. simpl in *.
  split; simpl.
  apply pF; assumption.
  apply pG; assumption.
Qed.



(* HCompose becomes just ∘ *)

Definition HTLess {i1 i2 o}
           (lop1: svector i1 -> svector o)
           (lop2: svector i2 -> svector o)
  : svector (i1+i2) -> svector o
  := fun v0 => let (v1,v2) := vector2pair i1 v0 in
            ZVLess (lop1 v1, lop2 v2).

Definition HCross
           {i1 o1 i2 o2}
           `(xop1pf: !Proper ((=) ==> (=)) (xop1: svector i1 -> svector o1))
           `(xop2pf: !Proper ((=) ==> (=)) (xop2: svector i2 -> svector o2))
  : svector (i1+i2) -> svector (o1+o2)
  := pair2vector ∘ (Cross (xop1, xop2)) ∘ (vector2pair i1).

Definition HStack {i o1 o2}
           (op1: svector i -> svector o1)
           (op2: svector i -> svector o2)
  : svector i -> svector (o1+o2)
  := pair2vector ∘ (Stack (op1, op2)).

Global Instance HTLess_proper {i1 i2 o}
       `{!Proper ((=) ==> (=)) (lop1: svector i1 -> svector o)}
       `{!Proper ((=) ==> (=)) (lop2: svector i2 -> svector o)}:
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

Global Instance HCross_arg_proper
       {i1 o1 i2 o2}
       `{xop1pf: !Proper ((=) ==> (=)) (xop1: svector i1 -> svector o1)}
       `{xop2pf: !Proper ((=) ==> (=)) (xop2: svector i2 -> svector o2)}:
  Proper ((=) ==> (=)) (HCross xop1pf xop2pf).
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

(*
    Global Instance HCross_proper {i1 o1 i2 o2}:
      Proper ((=) ==> (=) ==> (=)) (@HCross i1 o1 i2 o2).
    Proof.
      intros op1 op2 E1 xop1 xop2 E2.
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
 *)


(*
      Global Instance HStack_proper i o1 o2:
        Proper ((=) ==> (=) ==> (=)) (@HStack i o1 o2).
      Proof.
        intros op1 op1' op1E  op2 op2' op2E.
        unfold equiv, HCOL_equiv.
        intros.
        simpl.
        unfold pair2vector, Stack, compose.
        unfold equiv, HCOL_equiv in op1E.
        rewrite op1E, op2E.
        reflexivity.
      Qed.
      
      Global Instance HCross_proper i1 o1 i2 o2:
        Proper ((=) ==> (=) ==> (=)) (@HCross i1 o1 i2 o2).
      Proof.
        intros op1 op1' op1E  op2 op2' op2E.
        unfold equiv, HCOL_equiv.
        intros.
        simpl.
        unfold compose.
        generalize (vector2pair i1 x). intros.
        destruct p.
        unfold Cross.
        unfold pair2vector.
        rewrite op1E, op2E.
        reflexivity.
      Qed.

 *)

