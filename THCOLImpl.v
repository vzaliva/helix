(* HCOL metaoperators *)

Require Import Spiral.
Require Import VecSetoid.
Require Import CarrierType.

Require Import Arith.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import SpiralTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.

Import VectorNotations.
Open Scope vector_scope.

Section THCOL_implementations.

  (* Apply 2 functions to the same input returning tuple of results *)
  Definition Stack {D R F: Type} (fg:(D->R)*(D->F)) (x:D) : (R*F) :=
    match fg with
    | (f,g) => pair (f x) (g x)
    end.

  (* Apply 2 functions to 2 inputs returning tuple of results *)
  Definition Cross {D R E F: Type} (fg:(D->R)*(E->F)) (x:D*E) : (R*F) :=
    match fg with
    | (f,g) => match x with
              | (x0,x1) => pair (f x0) (g x1)
              end
    end.

  Definition Zless (a b: CarrierA): CarrierA
    := if CarrierAltdec a b then one else zero.

  Global Instance Zless_proper:
    Proper ((=) ==> (=) ==> (=)) (Zless).
  Proof.
    unfold Proper.
    intros a a' aE z z' zE.
    unfold Zless.
    destruct (CarrierAltdec a z), (CarrierAltdec a' z'); auto.
    rewrite aE, zE in l; contradiction.
    rewrite <- aE, <- zE in l; contradiction.
  Qed.

  (* --- Pointwise Comparison --- *)

  (* Zero/One version *)
  Definition ZVLess {n}
             (ab: (avector n)*(avector n)) : avector n :=
    match ab with
    | (a,b) => Vmap2 (Zless) a b
    end.

  Global Instance ZVLess_proper {n:nat}:
    Proper ((=) ==> (=))  (@ZVLess n).
  Proof.
    (* solve_proper. *)
    intros x y E.
    unfold ZVLess.
    repeat break_let.
    inversion E. simpl in *.
    unfold equiv, vec_Equiv.
    rewrite H0, H.
    reflexivity.
  Qed.

End THCOL_implementations.


Section THCOL_implementation_proper.

  Global Instance Cross_arg_proper
         `{Equiv D,Equiv R,Equiv E,Equiv F}
         `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
         `{pG: !Proper ((=) ==> (=)) (g: E -> F)}:
    Proper ((=) ==> (=))  (Cross (f,g)).
  Proof.
    intros fg fg' fgE.
    destruct fg, fg'.
    destruct fgE as [M2 M1]. simpl in *.
    split; simpl.
    apply pF; assumption.
    apply pG; assumption.
  Qed.

  Global Instance Stack_arg_proper
         `{Equiv D,Equiv R,Equiv F}
         `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
         `{pG: !Proper ((=) ==> (=)) (g: D -> F)}:
    Proper ((=) ==> (=))  (Stack (f,g)).
  Proof.
    intros fg fg' fgE.
    split; simpl.
    apply pF; assumption.
    apply pG; assumption.
  Qed.

End THCOL_implementation_proper.

