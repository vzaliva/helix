(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import HCOL.

Require Import ArithRing.

Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

(* === Sigma HCOL Operators === *)

Module SigmaHCOLOperators.

  (* zero - based, (stride-1) parameter *)
  Program Fixpoint GathH_0 {A} {t:nat} (n s:nat) : vector A ((n*(S s)+t)) -> vector A n :=
    let stride := S s in (
      match n return vector A ((n*stride)+t) -> vector A n with
        | O => fun _ => Vnil
        | S p => fun a => Vcons (hd a) (GathH_0 p s (t0:=t) (drop_plus stride a))
      end).
  Next Obligation.
    lia.
  Defined.

  Program Definition GathH {A: Type} (n base stride: nat) {s t} {snz: stride≡S s} (v: vector A (base+n*stride+t)) : vector A n :=
    GathH_0 n s (t0:=t) (drop_plus base v).
  Next Obligation.
    lia.
  Defined.

  Section Coq84Workaround.
    
    (* 
This section is workaround for Coq 8.4 bug in Program construct. under Coq 8.5 
the following definition suffice:

Program Fixpoint ScatHUnion_0 {A} {n:nat} (pad:nat): t A n -> t (option A) ((S pad)*n) :=
  match n return (t A n) -> (t (option A) ((S pad)*n)) with
  | 0 => fun _ => @nil (option A)
  | S p => fun a => cons _ (Some (hd a)) _ (append (const None pad) (ScatHUnion_0 pad (tl a)))
  end.
Next Obligation.
  ring.
Defined.
     *)
    
    Open Scope nat_scope.
    
    Fixpoint ScatHUnion_0 (A:Type) (n:nat) (pad:nat) {struct n}:
      vector A n -> vector (option A) ((S pad)*n).
        refine(
            match n as m return m=n -> _ with
            | O =>  fun _ _ => (fun _ => _) nil
            | S p => fun H1 a =>
                       let aa := (fun _ => _) a in
                       let hh := Some (hd aa) in
                       let tt := ScatHUnion_0 A p pad (tl aa) in
                       let ttt := append (Vector.const None pad) tt in
                       (fun _ => _) (Vcons hh ttt)
            end
              (eq_refl _)
          );
      replace (S pad * 0) with 0;
      try replace ( (S (pad + S pad * p))) with (S pad * S p) in *;
      eauto; lia.
    Defined.
    
    Close Scope nat_scope.
  End Coq84Workaround.
  
  Definition ScatHUnion {A} {n:nat} (base:nat) (pad:nat) (v:vector A n): vector (option A) (base+((S pad)*n)) :=
    Vector.append (Vconst None base) (ScatHUnion_0 A n pad v).

End SigmaHCOLOperators.
  
Import SigmaHCOLOperators.
Import HCOLOperators.

(*
Motivating example:

BinOp(2, Lambda([ r4, r5 ], sub(r4, r5)))

-->

ISumUnion(i3, 2,
  ScatHUnion(2, 1, i3, 1) o
  BinOp(1, Lambda([ r4, r5 ], sub(r4, r5))) o
  GathH(4, 2, i3, 2)
)

Inductive SHOperator : nat -> nat -> Type :=
  | ScatHUnion {n} base pad 
  | HOPrepend i {n} (a:vector A n): HOperator i (n+i)
  | HOInfinityNorm {i}: HOperator i 1

*)  




  
