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
Require Import MathClasses.theory.setoids.

(* ExtLib *)
Require Import ExtLib.Structures.Monoid.
Import Monoid.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.

Section TSigmaHCOLOperators.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Class TSHOperator2 {i1 o1 i2 o2 ix ox}
        {P1 Q1 P2 Q2}
        (P : svector fm ix → Prop)
        (Q : svector fm ox → Prop)
        (top: (psvector fm i1 P1 -> psvector fm o1 Q1) -> (psvector fm i2 P2 -> psvector fm o2 Q2) -> psvector fm ix P -> psvector fm ox Q) :=
    TSHOperator2_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

  (* Curried Templete SigmaHCOL operator with arity 2 is SHOperators *)
  Global Instance THOperator2_SHOperator
         {i1 o1 i2 o2 ix ox}
         {P1 Q1 P2 Q2}
         (P : svector fm ix → Prop)
         (Q : svector fm ox → Prop)
         `{O1: @SHOperator fm i1 o1 P1 Q1 op1}
         `{O2: @SHOperator fm i2 o2 P2 Q2 op2}
         `{T: @TSHOperator2 i1 o1 i2 o2 ix ox P1 Q1 P2 Q2 P Q to}:
    SHOperator fm P Q (to op1 op2).
  Proof.
    split; try apply sig_setoid.
    apply T ; [apply O1 | apply O2].
  Qed.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.

     This is very specialized implementation. In future, if we have more
     TSHOperator2 instances, it makes sense to use approach similar to what
     we are using for SigmaHCOL with AddPrepost wrapper.
   *)
  Definition HTSUMUnion {i o}
             {Q1 Q2 P}
             {Q: svector fm o -> Prop}
             (dot: CarrierA -> CarrierA -> CarrierA)
             {PQ: forall (a:psvector fm o Q1) (b:psvector fm o Q2),
                 Q (Vec2Union fm dot (proj1_sig a) (proj1_sig b))
             }             (op1: psvector fm i P -> psvector fm o Q1)
             (op2: psvector fm i P -> psvector fm o Q2)
    :
      psvector fm i P -> psvector fm o Q
    := fun x =>
         let a := op1 x in
         let a' := proj1_sig a in
         let b := op2 x in
         let b' := proj1_sig b in
         @exist _ _ (Vec2Union fm dot a' b') (PQ a b).

  Global Instance TSHOperator2_HTSUMUnion {i o}
         {P: svector fm i → Prop}
         {Q Q1 Q2: svector fm o → Prop}
         (dot: CarrierA -> CarrierA -> CarrierA)
         {PQ: forall (a: {x:svector fm o | Q1 x}) (b : {x:svector fm o | Q2 x}),
             Q (Vec2Union fm dot (` a) (` b))}
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    :
      TSHOperator2 P Q (@HTSUMUnion i o Q1 Q2 P Q dot PQ).
  Proof.
    intros f f' Ef g g' Eg x y Ex.
    unfold HTSUMUnion.
    unfold Vec2Union.
    vec_index_equiv j jp.
    simpl.
    rewrite 2!Vnth_map2.
    setoid_replace (Vnth (proj1_sig (f x)) jp) with (Vnth (proj1_sig (f' y)) jp).
    setoid_replace (Vnth (proj1_sig (g x)) jp) with (Vnth (proj1_sig (g' y)) jp).
    reflexivity.
    - apply Vnth_arg_equiv.
      apply Eg, Ex.
    - apply Vnth_arg_equiv.
      apply Ef, Ex.
  Qed.

End TSigmaHCOLOperators.
