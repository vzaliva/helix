Require Import Spiral.
Require Import Rtheta.

Require Import Program. (* compose *)

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Open Scope vector_scope.

(* "sparse" vector type: vector holding Rhteta values *)
Notation svector n := (vector Rtheta n) (only parsing).

Section SparseVectors.

  (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
  Definition svector_from_vector {n} (v:vector A n): svector n :=
    Vmap Rtheta_normal v.

  (* Project out carrier type values from vector of Rheta values *)
  Definition vector_from_svector {n} (v:svector n): vector A n :=
    Vmap RthetaVal v.

  (* Our definition of "dense" vector means that it does not contain "structural" values. *)
  
  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall (not ∘ Is_Struct) v.
  
  (* Construct "Zero svector". All values are structural zeros. *)
  Definition szero_svector n: svector n := Vconst Rtheta_szero n.
  
End SparseVectors.

