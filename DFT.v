

Require Export Utf8_core.
Require Import Coq.Arith.Arith.

Require Coq.Program.Tactics.
Require Import Coq.Program.Equality.

Require Import CpdtTactics.

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

Obligation Tactic := (Tactics.program_simpl; subst; auto with arith; try ring).
Set Shrink Obligations.

Section ProductLemmas.
  Local Open Scope matrix_scope.

   Program Definition KroneckerProduct_assoc_def
          {xr xc yr yc zr zc: nat}
          (x: Matrix xr xc) (y: Matrix yr yc) (z: Matrix zr zc) :=
     x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z.

  Fact KroneckerProduct_assoc
          {xr xc yr yc zr zc: nat}
          (x: Matrix xr xc) (y: Matrix yr yc) (z: Matrix zr zc):
    KroneckerProduct_assoc_def x y z.
  Proof.
    unfold KroneckerProduct_assoc_def.
  Admitted.

End ProductLemmas.


Section Table1Lemmas.
  Local Open Scope matrix_scope.

  Lemma Lemma6:
    forall m n, I (m*n) = I m ⊗ I n.
  Admitted.

  (*
  Program Definition Identity1_1c_def (k m n:nat) :=
    L (k*m*n) (k*m) = (I k ⊗ L (m*n) m) * (L (k*n) k ⊗ I m).

  Lemma Identity1_1c (k m n:nat):
    Identity1_1c_def k m n.
  Admitted.

  Program Definition Identity1_6b_def (m n k:nat) (A: Matrix k k) :=
    (L (k*m*n) n) * (L (k*m) m * (A ⊗ I m) ⊗ I n) =
    (I n ⊗ L (k*m) m) *
    (L (k*n) n * (A ⊗ I n) ⊗ I m) *
    (I k ⊗ L (m*n) n).

  Lemma Identity1_6b (m n k:nat) (A: Matrix k k):
    Identity1_6b_def m n k A.
  Admitted.

  Program Definition Identity1_7a_def (n0 v:nat) :=
    let n := (n0*v)%nat in
    L (n*v) n = (I n0 ⊗ L (v*v) v) * (L n n0 ⊗ I v).

  Lemma Identity1_7a (n0 v:nat):
    Identity1_7a_def n0 v.
  Admitted.

   *)

  Program Definition Identity1_7b_def (n0 v:nat) :=
    let n := (n0*v)%nat in
    L (n*v) v = (L n v ⊗ I v) * (I n0 ⊗ L (v*v) v).

  Lemma Identity1_7b (n0 v:nat):
    Identity1_7b_def n0 v.
  Admitted.

  Program Definition Identity1_8b_def (m0 n v:nat) (A: Matrix n n) :=
    let m := (m0 * v)%nat in
    ((I m ⊗ A) * L (m*n) m) =
    (I m0 ⊗ L (n*v) v * (A ⊗ I v)) * (L (m0*n) m0 ⊗ I v).

  Lemma Identity1_8b (m0 n v:nat) (A: Matrix n n):
    Identity1_8b_def m0 n v A.
  Admitted.

End Table1Lemmas.

Section ShortVectorCooleyTurkeyFFT.
  Local Open Scope matrix_scope.

  Definition Eq15 (m n: nat)
    : Matrix (m * n) (m * n)
    := (DFT m ⊗ I n) * T (m*n) n *
       ((I m ⊗ DFT n) * L (m*n) m).

  Program Definition Eq23 (m0 n0 v:nat)
    : Matrix ((m0 * v) * (n0 * v)) ((m0 * v) * (n0 * v))
    :=
      let m := (m0 * v)%nat in
      let n := (n0 * v)%nat in
      ((DFT m ⊗ I n0) ⊗ I v)
      *
      (T (m*n) n) *
      (
        (I m0)
          ⊗ (I n0 ⊗ L (v*v) v)
        * (L n n0 ⊗ I v)
        * (DFT n ⊗ I v)
      ) *
      (L (m0*n0*v) m0 ⊗ I v).

  Lemma Eq23FromEq15 (m0 n0 v: nat)
        (mnz: m0 ≠ 0)
        (nnz: n0 ≠ 0)
        (vzz: v ≠ 0):
    Eq15 (m0 * v) (n0 * v) = Eq23 m0 n0 v.
  Proof.
    unfold Eq15.
    (* LHS *)
    rewrite Lemma6.
    rewrite KroneckerProduct_assoc.

    (* RHS *)
    rewrite Identity1_8b.
    rewrite Identity1_7b.
    unfold Eq23.
    clear_eq_proofs.
    simpl_eq.
    reflexivity.
  Qed.

End ShortVectorCooleyTurkeyFFT.
