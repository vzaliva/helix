

Require Export Utf8_core.
Require Import Coq.Arith.Arith.

Require Coq.Program.Tactics.

Record Matrix (m n : nat).

Definition DFT (n:nat) : Matrix n n. Admitted.

Definition I (n:nat): Matrix n n. Admitted.
Definition T (m n:nat): Matrix m m. Admitted.
Definition L (m n:nat): Matrix m m. Admitted.

Bind Scope matrix_scope with Matrix.

Definition KroneckerProduct {m n p q: nat} (A: Matrix m n) (B: Matrix p q):
  Matrix (m*p) (n*q). Admitted.

Notation "x ⊗ y" := (KroneckerProduct x y) (at level 50, left associativity) : matrix_scope.

Definition MatrixProduct {m n p: nat} (A: Matrix n m) (B: Matrix m p):
  Matrix n p. Admitted.

Notation "x * y" := (MatrixProduct x y) : matrix_scope.

Section ProductLemmas.
  Local Open Scope matrix_scope.

(*   Program Fact KroneckerProduct_assoc
          (xr xc yr yc zr zc: nat)
          (x: Matrix xr xc) (y: Matrix yr yc) (z: Matrix zr zc):
    x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z. *)

End ProductLemmas.


Section Table1Lemmas.
  Local Open Scope matrix_scope.

  Lemma Lemma6:
    forall m n, I (m*n) = I m ⊗ I n.
  Admitted.
End Table1Lemmas.

Section ShortVectorCooleyTurkeyFFT.
  Local Open Scope matrix_scope.

  Definition Eq15 (m n: nat)
    : Matrix (m * n) (m * n)
    := ((DFT m) ⊗ (I n)) * (T (m*n) n) *
       ((I m) ⊗ (DFT n)) * (L (m*n) m).

  Obligation Tactic := (Tactics.program_simpl; ring).
  Program Definition Eq23 (m0 n0 v:nat)
    : Matrix ((m0 * v) * (n0 * v)) ((m0 * v) * (n0 * v))
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

  Lemma Eq23FromEq15 (m0 n0 v: nat)
        (mnz: m0 ≠ 0)
        (nnz: n0 ≠ 0)
        (vzz: v ≠ 0):
    Eq15 (m0 * v) (n0 * v) = Eq23 m0 n0 v.
  Proof.
    unfold Eq15.
    rewrite Lemma6.
  Qed.

End ShortVectorCooleyTurkeyFFT.