(* Experimental alternative Sigma-HCOL construction, avoiding notion of Error *)

(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import HCOLSyntax.
Require Import IndexFunctions.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

(* Options compatible *)
Definition OptComp {A} (a b: option A) : Prop :=
  match a, b with
  |  Some _, Some _ => False
  |  None, None as x | None, Some _ as x | Some _ as x, None => True
  end.

Program Definition OptionUnion {A}
           (a b: option A)
           (ok: OptComp a b) : option A
  :=
  match a, b with
  |  None, None as x | None, Some _ as x | Some _ as x, None => x
  |  Some _ as x, Some _ => ! (* impossible case *)
  end.

(* Two option vectors compatible *)
Definition OptVecComp {A} {n} (a: svector A n)  (b: svector A n): Prop :=
  Vforall2 OptComp a b.

Lemma OptVecComp_tl {A} {n} {a b: svector A (S n)}:
  OptVecComp a b -> OptVecComp (Vtail a) (Vtail b).
Proof.
  intros C.
  dependent destruction a.
  dependent destruction b.
  unfold OptVecComp, Vforall2 in C.
  destruct C as [H T].
  simpl.
  assumption.
Qed.

Lemma OptVecComp_hd {A} {n} {a b: svector A (S n)}:
  OptVecComp a b -> OptComp (Vhead a) (Vhead b).
Proof.
  intros C.
  dependent destruction a.
  dependent destruction b.
  unfold OptVecComp, Vforall2 in C.
  destruct C as [H T].
  simpl.
  assumption.
Qed.

Fixpoint SparseUnion {A} {n}:
  forall (a b: svector A n), OptVecComp a b -> svector A n
  :=
    match n with
    | O => fun _ _  _=> @Vnil (option A)
    | (S _) => fun a' b' ok=> 
                Vcons
                  (OptionUnion (Vhead a') (Vhead b') (OptVecComp_hd ok))
                  (SparseUnion (Vtail a') (Vtail b')  (OptVecComp_tl ok))
    end.
