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

(* ExtLib *)
Require Import ExtLib.Structures.Monoid.
Import Monoid.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.

Section TSigmaHCOLOperators.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Class TSHOperator2 {i1 o1 i2 o2 ix ox} (top: (svector fm i1 -> svector fm o1) -> (svector fm i2 -> svector fm o2) -> svector fm ix -> svector fm ox) :=
    TSHOperator2_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

  (* Curried Templete SigmaHCOL operator with arity 2 is SHOperators *)
  Global Instance THOperator2_SHOperator
         `{O1: @SHOperator fm i1 o1 op1}
         `{O2: @SHOperator fm i2 o2 op2}
         `{T: @TSHOperator2 i1 o1 i2 o2 ix ox to}:
    SHOperator fm (to op1 op2).
  Proof.
    split; try apply vec_Setoid.
    apply T ; [apply O1 | apply O2].
  Qed.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input. *)
  Definition HTSUMUnion {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (f: svector fm i -> svector fm o)
             (g: svector fm i -> svector fm o)
             (x: svector fm i): svector fm o
    :=  Vec2Union fm dot (f x) (g x).


  Global Instance TSHOperator2_HTSUMUnion {i o}
         (dot: CarrierA -> CarrierA -> CarrierA)
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
