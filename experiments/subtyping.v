
Require Import Coq.Init.Specif.
Require Import Coq.Relations.Relations.

Record RRR
       {P Q : nat -> Prop}
  : Type
  :=  {
      op: nat -> nat ;
      pre_post: forall (x:nat), P x -> Q (op x) ;
    }.


Definition RRR_subtype
           {P1 Q1 P2 Q2: nat -> Prop}
  :=
    (forall x, P1 x -> P2 x) /\
    (forall y, Q2 y -> Q1 y).

Class Subtype (A B: Set) := subtype: A -> B -> Prop.

Instance Subtype_RRR
         {P1 P2 Q1 Q2}:
  Subtype (@RRR P1 Q1) (@RRR P2 Q2)
  := fun a b => a.
