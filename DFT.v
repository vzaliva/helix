

Require Export Utf8_core.


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

Notation "x ⊗ y" := (KroneckerProduct x y) (at level 40, left associativity) : matrix_scope.

Definition MatrixProduct {m n p: nat} (A: Matrix n m) (B: Matrix m p):
  Matrix n p. Admitted.

Notation "x * y" := (MatrixProduct x y) : matrix_scope.

Local Open Scope matrix_scope.


Definition Eq15 (m n: nat) := ((DFT m) ⊗ (I n)) * (T (m*n) n) *
                            ((I m) ⊗ (DFT n)) * (L (m*n) m).


Definition Eq23 (m n v: nat) := (((DFT m) ⊗ (I (n/v))) * (I v)) *
                              (T (m*n) n) *
                              (
                                (I (m/v))
                                  ⊗ ((I (n/v)) ⊗ (L (v*v) v))
                                * ((L n (n/v)) ⊗ (I v))
                                * ((DFT n) ⊗ (I v))
                              ) *
                              ((L (m*n/v) (m/v)) ⊗ (I v)).


Local Close Scope matrix_scope.
