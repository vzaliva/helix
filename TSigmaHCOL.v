(* Template HCOL. HCOL meta-operators *)

Require Import VecUtil.
Require Import VecSetoid.
Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import IndexFunctions.
Require Import SigmaHCOL. (* Presently for SHOperator only. Consider moving it elsewhere *)

Require Import Arith.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Open Scope vector_scope.

Class TSHOperator2 {i1 o1 i2 o2 ix ox} (top: (svector i1 -> svector o1) -> (svector i2 -> svector o2) -> svector ix -> svector ox) :=
  TSHOperator2_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

(* Curried Templete SigmaHCOL operator with arity 2 is SHOperators *)
Global Instance THOperator2_SHOperator
       `{O1: @SHOperator i1 o1 op1}
       `{O2: @SHOperator i2 o2 op2}
       `{T: @TSHOperator2 i1 o1 i2 o2 ix ox to}:
  SHOperator (to op1 op2).
Proof.
  split; try apply vec_Setoid.
  apply T ; [apply O1 | apply O2].
Qed.


Section TSigmaHCOLOperators.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input. *)
  Definition HTSUMUnion {i o}
             (dot:CarrierA->CarrierA->CarrierA)
             (f: svector i -> svector o)
             (g: svector i -> svector o)
             (x: svector i): svector o
    :=  Vec2Union dot (f x) (g x).


  Global Instance TSHOperator2_HTSUMUnion {i o}
         (dot:CarrierA->CarrierA->CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    :
    TSHOperator2 (@HTSUMUnion i o dot).
  Proof.
    intros f f' Ef g g' Eg x y Ex.
    unfold HTSUMUnion.
    unfold Vec2Union.
    vec_index_equiv j jp.
    rewrite 2!Vnth_map2.
    setoid_replace (Vnth (f x) jp) with (Vnth (f' y) jp).
    setoid_replace (Vnth (g x) jp) with (Vnth (g' y) jp).
    reflexivity.
    - apply Vnth_arg_equiv.
      apply Eg, Ex.
    - apply Vnth_arg_equiv.
      apply Ef, Ex.
  Qed.

End TSigmaHCOLOperators.
