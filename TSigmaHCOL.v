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

  Definition HTSUMUnion' {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (op1: svector fm i -> svector fm o)
             (op2: svector fm i -> svector fm o):
    svector fm i -> svector fm o
    := fun x => Vec2Union fm dot (op1 x) (op2 x).

  Global Instance HTSUMUnion'_Proper {i o}
         (op1: svector fm i -> svector fm o)
         (op2: svector fm i -> svector fm o)
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

  Global Instance HTSUMUnion'_arg_Proper {i o}
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
    apply HTSUMUnion'_Proper.
    - apply op1.
    - apply op2.
    - apply dot_mor.
    - apply op1_proper.
    - apply op2_proper.
  Qed.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.

     This is very specialized implementation. In future, if we have more
     TSHOperator2 instances, it makes sense to use approach similar to what
     we are using for SigmaHCOL with AddPrepost wrapper.
   *)
  Definition HTSUMUnion {i o}
             {P: svector fm i -> Prop}
             {Q Q1 Q2: svector fm o -> Prop}
             (op1: @SHOperator fm i o P Q1)
             (op2: @SHOperator fm i o P Q2)
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
             (PQ: forall x : svector fm i, P x → Q (HTSUMUnion' dot (op fm op1) (op fm op2) x))
    : @SHOperator fm i o P Q
    := mkSHOperator fm i o P Q (HTSUMUnion' dot (op fm op1) (op fm op2)) PQ
                    (@HTSUMUnion'_arg_Proper i o
                                             (op fm op1) (op_proper fm op1)
                                             (op fm op2) (op_proper fm op2)
                                             dot dot_mor).


End TSigmaHCOLOperators.
