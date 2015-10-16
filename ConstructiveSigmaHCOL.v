(* Experimental alternative Sigma-HCOL construction, avoiding notion of Error *)

(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import HCOLSyntax.
Require Import IndexFunctions.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Definition OptionDontCollide {A} (a b: option A) : Prop :=
  match a, b with
  |  Some _, Some _ => False
  |  None, None as x | None, Some _ as x | Some _ as x, None => True
  end.

Definition OptionUnion {A}
           (a b: option A)
           {ok: OptionDontCollide a b}
  :=
  match a, b with
  |  None, None as x | None, Some _ as x | Some _ as x, None => x
  |  Some _ as x, Some _ => x (* impossible case *)
  end.

Fixpoint SparseUnion {A} {n}: (svector A n) -> (svector A n) -> @maybeError (svector A n) := 
  match n with
  | O => fun _ _ => OK (@Vnil (option A))
  | (S _) => fun a b =>
              match SparseUnion (Vtail a) (Vtail b) as t with
              | Error msg => Error msg
              | OK xs =>
                match OptionUnion (Vhead a) (Vhead b) with
                |  Error _ => Error "incompatible values"
                |  OK x => OK (Vcons x xs)
                end
              end
  end.
