(**  Matrix definition very similar to one provided by CoLoR but without using their OrderedSemiRing because we are using MathClasses for that instead.  **)

Global Generalizable All Variables.

Require Import Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Lt.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.orders.orders.
Require Import MathClasses.interfaces.orders MathClasses.orders.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.theory.rings.

(*  CoLoR *)
Require Export Vector.
Require Export CoLoR.Util.Vector.VecUtil.
Require Import CoLoR.Util.Nat.NatUtil.
Require Import CoLoR.Util.Logic.LogicUtil.
Import VectorNotations.

Open Scope vector_scope.

(* Matrix represented by a vector of vectors (in a row-wise fashion) *)
Definition matrix (A:Type) m n := vector (vector A n) m.

Definition get_row (A:Type) m n (M : matrix A m n) i (ip : i < m) := Vnth M ip.

Definition get_col (A:Type) m n (M : matrix A m n) i (ip : i < n) := 
  Vmap (fun v => Vnth v ip) M.

Definition get_elem (A:Type) m n (M : matrix A m n) i j (ip : i < m) (jp : j < n) :=
  Vnth (get_row A m n M i ip) jp.

Definition zero_vec (A:Type) `{!Zero A} (n:nat) : vector A n:= @Vconst A 0 n.
Definition one_vec (A:Type) `{!One A} (n:nat) : vector A n:= @Vconst A 1 n.

Definition id_vec (A:Type) `{!Zero A, !One A} n i (ip : i < n) := Vreplace (zero_vec A n) ip 1.

Definition zero_1column_mat (A:Type) (n:nat)`{!Zero A, !One A}:= @Vconst (vector A 1) [0] n.

Definition id_matrix (A:Type) `{!Zero A, !One A} (n:nat): matrix A n n := Vbuild (fun i ip => id_vec A n i ip).

(* Basis Vector as 1xN matrix *)
Definition id_row_mat (A:Type) `{!Zero A, !One A} n i {ip : i < n} : matrix A 1 n :=  [ id_vec A n i ip ].

(* Basis Vector as Nx1 matrix *)
Definition id_col_mat (A:Type) `{!Zero A, !One A} n i {ip : i < n} :=  Vreplace (zero_1column_mat A n) ip [1].

Definition mat_vec_prod (A:Type) `{!Mult A, !Plus A, !Zero A} {m} {n} (a: @matrix A m n) (x: vector A n) : (vector A m) := Vmap (fun i => (Vfold_right (+) (Vmap2 (.*.) i x) 0)) a.

Close Scope vector_scope.


