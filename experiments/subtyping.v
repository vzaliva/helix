
Require Import Coq.Init.Specif.
Require Import Coq.Relations.Relations.

Class Subtype A := subtype: relation A.

Infix "<:" := subtype (at level 40) : type_scope.
Notation "(<:)" := subtype (only parsing) : type_scope.

Variable A: Type.
Variable P1 P2: A->Prop.

Goal (forall (x:A), P1 x -> P2 x) ->
{x:A | P1 x} <: {x:A | P2 x}.
