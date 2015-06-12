(* Sparse/Dense vector *)

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import CaseNaming.
Require Import CpdtTactics.

Require Import Spiral.

(* "sparse" vector type *)
Notation svector A n := (vector (option A) n).

Global Instance sparce_vec_equiv `{Equiv A} {n}: Equiv (svector A n) :=
  Vforall2 (n:=n) opt_equiv.

Definition SparseCast {A} {n} (v:vector A n): svector A n :=
  Vmap (Some) v.

Definition is_Dense {A} {n} (v:svector A n) : Prop :=
  Vforall is_Some v.

Definition from_Some {A} (x:option A) {S: is_Some x}: A.
Proof.
  destruct x.
  tauto.
  unfold is_Some in S.
  tauto.
Defined.

Lemma dense_get_hd {A} {n} (v:svector A (S n)): is_Dense v -> A.
Proof.
  unfold is_Dense.
  intros.
  assert (is_Some (Vhead v)).
  apply Vforall_hd. assumption.
  revert H0.
  apply from_Some.
Defined.

Lemma dense_tl {A} {n} {v: svector A (S n)}: is_Dense v -> is_Dense (Vtail v).
Proof.
  unfold is_Dense.
  intros.
  dep_destruct v.
  simpl in H.
  simpl.
  apply H.
Defined.

Inductive DenseV {A:Type} {n:nat} : Type :=
| buildDenseV (v:svector A n) (H:is_Dense v): DenseV.

Definition DenseVtail {A:Type} {n:nat} (d:@DenseV A (S n)): @DenseV A n :=
  match d with
  | buildDenseV v H => buildDenseV (Vtail v) (dense_tl H)
  end.
  
Fixpoint DenseCast' {A} {n} (d:@DenseV A n): vector A n :=
  match n return @DenseV A n -> (vector A n) with
  | O => fun _ => @Vnil A
  | (S p) => fun d0 =>
               match d0 return @DenseV A (S p) -> (vector A (S p)) with
               | buildDenseV v i =>
                 fun d2 => Vcons (dense_get_hd v i) (DenseCast' (DenseVtail d2))
               end d0
  end d.

Fixpoint DenseCast {A} {n} (v:svector A n) (H:is_Dense v): vector A n :=
  DenseCast' (buildDenseV v H).
    


