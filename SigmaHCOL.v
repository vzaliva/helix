(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SPMatrix.

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
Require Import MathClasses.interfaces.naturals.


(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Open Scope vector_scope.

(* === Sigma HCOL Operators === *)

Module SigmaHCOLOperators.

  (* zero - based, (stride-1) parameter *)
  Program Fixpoint GathH_0 {A} {t:nat} (n s:nat) : vector A ((n*(S s)+t)) -> vector A n :=
    let stride := S s in (
      match n return vector A ((n*stride)+t) -> vector A n with
        | 0 => fun _ => Vnil
        | S p => fun a => Vcons (hd a) (GathH_0 p s (t0:=t) (drop_plus stride a))
      end).
  Next Obligation.
    ring.
  Defined.

  Program Definition GathH {A: Type} (n base stride: nat) {s t} {snz: stride≡S s} (v: vector A (base+n*stride+t)) : vector A n :=
    GathH_0 n s (t0:=t) (drop_plus base v).
  Next Obligation.
    ring.
  Defined.

  (* zero - based, pad=(stride-1) parameter *)
  Program Fixpoint ScatHUnion_0 `{Zero A} {n:nat} (pad:nat): vector A n -> vector A ((S pad)*n) :=
    match n return (vector A n) -> (vector A ((S pad)*n)) with
      | 0 => fun _ => Vnil
      | S p => fun a => Vcons (hd a) (Vector.append (Vconst 0 pad) (ScatHUnion_0 pad (tl a)))
    end.  
  Next Obligation.
    revert a.
    revert p.
    revert pad.
    clear H.
    clear n.

    
  Defined.
      | S p => fun a => Vconst 0 ((S pad)*(S p)) -- OK
      | S p => fun a => Vconst 0 ((S pad)*n) -- Seems OK
      | S p => Vector.append (Vconst 0 (S pad)) (Vconst 0 ((S pad)*p))  -- OK!!!


      | S p => fun a => Vector.append (Vcons (hd a) (Vconst 0 pad)) (ScatHUnion_0 pad (tl a))
  
(*
Motivating example:

BinOp(2, Lambda([ r4, r5 ], sub(r4, r5)))

-->

ISumUnion(i3, 2,
  ScatHUnion(2, 1, i3, 1) o
  BinOp(1, Lambda([ r4, r5 ], sub(r4, r5))) o
  GathH(4, 2, i3, 2)
)

*)  


End SigmaHCOLOperators.

Import HCOLOperators.
  
Close Scope vector_scope.

