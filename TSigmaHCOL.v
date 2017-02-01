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

(* For now we are not define special type for TSigmahcolOperators, like we did for SHOperator. Currently we have only 2 of these: SHCompose and HTSumunion. We will generalize in future, if needed *)
Section TSigmaHCOLOperators.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.
   *)
  Definition HTSUMUnion' {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (op1: svector fm i -> svector fm o)
             (op2: svector fm i -> svector fm o):
    svector fm i -> svector fm o
    := fun x => Vec2Union fm dot (op1 x) (op2 x).


  (* TODO: make dot part of morphism *)
  Global Instance HTSUMUnion'_proper {i o}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=) ==> (=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot).
  Proof.
    intros f f' Ef g g' Eg x y Ex.
    unfold HTSUMUnion'.
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

  Global Instance HTSUMUnion'_arg_proper {i o}
         (op1: svector fm i -> svector fm o)
         `{op1_proper: !Proper ((=) ==> (=)) op1}
         (op2: svector fm i -> svector fm o)
         `{op2_proper: !Proper ((=) ==> (=)) op2}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot op1 op2).
  Proof.
    partial_application_tactic. instantiate (1 := equiv).
    partial_application_tactic. instantiate (1 := equiv).
    apply HTSUMUnion'_proper.
    - apply dot_mor.
    - apply op1_proper.
    - apply op2_proper.
  Qed.

  Definition HTSUMUnion {i o}
             {P: svector fm i -> Prop}
             {Q Q1 Q2: svector fm o -> Prop}
             (op1: @SHOperator fm i o P Q1)
             (op2: @SHOperator fm i o P Q2)
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
             (PQ: forall (y1 y2 : svector fm o) d,  (Q1 y1 /\ Q2 y2) → Q (Vec2Union fm d y1 y2))
    : @SHOperator fm i o P Q.
  Proof.
    refine (
        mkSHOperator fm i o P Q (HTSUMUnion' dot (op fm op1) (op fm op2)) _
                     (@HTSUMUnion'_arg_proper i o
                                              (op fm op1) (op_proper fm op1)
                                              (op fm op2) (op_proper fm op2)
                                              dot dot_mor)).
    intros x Px.
    unfold HTSUMUnion'.
    unfold Vec2Union in *.
    destruct op1, op2.
    auto.
  Defined.

  Section CoerceHTSUMUnion.
    Variable i o : nat.
    Variable dot: CarrierA -> CarrierA -> CarrierA.
    Variable dot_mor: Proper ((=) ==> (=) ==> (=)) dot.

    Variable P: svector fm i -> Prop.
    Variable Q Q1 Q2: svector fm o -> Prop.
    Variable op1: @SHOperator fm i o P Q1.
    Variable op2: @SHOperator fm i o P Q2.

    Variable P': svector fm i -> Prop.
    Variable Q' Q1' Q2': svector fm o -> Prop.
    Variable op1': @SHOperator fm i o P' Q1'.
    Variable op2': @SHOperator fm i o P' Q2'.

    Lemma coerce_HTSUMUnion
          (S1: coerce_SHOperator fm op1 op1')
          (S2: coerce_SHOperator fm op2 op2')
          (PQ:  forall (y1 y2 : svector fm o) d, Q1  y1 /\ Q2  y2 → Q  (Vec2Union fm d y1 y2))
          (PQ': forall (y1 y2 : svector fm o) d, Q1' y1 /\ Q2' y2 → Q' (Vec2Union fm d y1 y2))
          (QQ: forall y, Q' y -> Q y)
      :
        coerce_SHOperator fm
                          (HTSUMUnion op1 op2 dot PQ)
                          (HTSUMUnion op1' op2' dot PQ').
    Proof.
      split.
      -
        simpl.
        apply HTSUMUnion'_proper.
        + apply dot_mor.
        + apply S1.
        + apply S2.
      -
        unfold coerce_SHOperator in S1.
        destruct S1 as [H0 [H1 H2]].
        tauto.
    Qed.

  End CoerceHTSUMUnion.


End TSigmaHCOLOperators.
