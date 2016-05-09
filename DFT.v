

Require Export Utf8_core.
Require Import Coq.Arith.Arith.

Require Coq.Program.Tactics.

Record Matrix (m n : nat).

Definition DFT (n:nat) : Matrix n n. Admitted.

Definition I (n:nat): Matrix n n. Admitted.
Definition T (m n:nat): Matrix m m. Admitted.
Definition L (m n:nat): Matrix m m. Admitted.

(*
The Kronecker product is a special case of the tensor product, so it is bilinear and associative.
The Kronecker product is non-commutative.
*)

Bind Scope matrix_scope with Matrix.

Definition KroneckerProduct {m n p q: nat} (A: Matrix m n) (B: Matrix p q):
  Matrix (m*p) (n*q). Admitted.

Notation "x ⊗ y" := (KroneckerProduct x y) (at level 50, left associativity) : matrix_scope.

Definition MatrixProduct {m n p: nat} (A: Matrix n m) (B: Matrix m p):
  Matrix n p. Admitted.

Notation "x * y" := (MatrixProduct x y) : matrix_scope.

Section ShortVectorCooleyTurkeyFFT.

  Local Open Scope matrix_scope.

  Definition Eq15 (m n: nat)
             (mnz: m ≠ 0)
             (nnz: n ≠ 0)
    := ((DFT m) ⊗ (I n)) * (T (m*n) n) *
       ((I m) ⊗ (DFT n)) * (L (m*n) m).

  Program Definition Eq23 (m0 n0 v:nat)
          (mnz: m0 ≠ 0)
          (nnz: n0 ≠ 0)
          (vzz: v ≠ 0)
    :=
      let m := (m0 * v)%nat in
      let n := (n0 * v)%nat in
      (((DFT m) ⊗ (I n0)) ⊗ (I v))
      *
      (T (m*n) n) *
      (
        (I m0)
          ⊗ ((I n0) ⊗ (L (v*v) v))
        * ((L n n0) ⊗ (I v))
        * ((DFT n) ⊗ (I v))
      ) *
      ((L (m0*n0*v)%nat m0) ⊗ (I v)).
  Next Obligation. Proof. ring. Qed.
  Next Obligation. Proof. ring. Qed.
  Next Obligation. Proof. ring. Qed.
  Next Obligation. Proof. ring. Qed.


End ShortVectorCooleyTurkeyFFT.