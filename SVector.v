(* Sparse/Dense vector *)

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.
Require Import MathClasses.misc.decision.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import CaseNaming.
Require Import CpdtTactics.

Require Import Spiral.

(* "sparse" vector type *)
Notation svector A n := (vector (option A) n).

Global Instance svector_equiv `{Equiv A} {n}: Equiv (svector A n) :=
  Vforall2 (n:=n) opt_Equiv.

Definition svector_from_vector {A} {n} (v:vector A n): svector A n :=
  Vmap (Some) v.

Definition svector_is_dense {A} {n} (v:svector A n) : Prop :=
  Vforall is_Some v.

Definition from_Some {A} (x:option A) {S: is_Some x}: A :=
  match x as o return (@is_Some A o -> A) with
  | Some a => fun _ : @is_Some A (@Some A a) => a
  | None => fun S0 : @is_Some A (@None A) => False_rect A S0
  end S.

(* Alternative but equal definition:
Definition from_Some {A} (x:option A) {S: is_Some x}: A.
Proof.
  destruct x.
  assumption.
  contradiction.
Defined.
 *)

Definition svector_hd {A} {n} (v:svector A (S n)): svector_is_dense v -> A.
Proof.
  unfold svector_is_dense.  
  intros.
  assert (is_Some (Vhead v)).
  apply Vforall_hd. assumption.
  revert H0.
  apply from_Some.
Defined.

Lemma svector_tl_dense {A} {n} {v: svector A (S n)}:
  svector_is_dense v -> svector_is_dense (Vtail v).
Proof.
  unfold svector_is_dense.
  intros.
  dep_destruct v.
  simpl in H.
  simpl.
  apply H.
Defined.

Lemma svector_nil_is_dense {A:Type}: svector_is_dense (@Vnil (option A)).
Proof.
  crush.
Qed.

Fixpoint vector_from_svector {A} {n} (v:svector A n) (D:svector_is_dense v): vector A n :=
  match n return forall (w:svector A n), (svector_is_dense w) -> (vector A n) with
  | O => fun _ _ => @Vnil A
  | (S p) => fun v0 D0 => Vcons
                            (svector_hd v0 D0)
                            (vector_from_svector (Vtail v0) (svector_tl_dense D0))
  end v D.

Fixpoint try_vector_from_svector {A} {n} (v:svector A n): @maybeError (vector A n) :=
  match n return (svector A n) -> (@maybeError (vector A n)) with
  | O => fun _ => OK (@Vnil A)
  | (S p) => fun v0 =>
               match v0 return (svector A (S p)) -> (@maybeError (vector A (S p))) with
               | Vnil => fun _ => Error "Assertion failed: vector size mismatch"
               | (Vcons None _ _) => fun _ => Error "Sparse vector could not be converted to Dense"
               | (Vcons (Some x) _ _) => fun v1 =>
                                            match (try_vector_from_svector (Vtail v1)) with
                                            | Error msg => Error msg
                                            | OK t' => OK (Vcons x t')
                                            end
               end v0
  end v.


(* -------------------------------------------------------- *)

Section ProofCarryingSparseVector.

  (* Inductive type representing both sparse and dense vectors. While underlying
vector storage structure is the same (svector), in dense case it is paired with
proof of density.

It should be noted that "sparse" vector could be in fact dense, but we just
lacking a proof of it.
   *)
  Inductive Vector {A:Type} {n:nat}: Type :=
  | DVector (v:svector A n) (D:svector_is_dense v): Vector
  | SVector (v:svector A n): Vector.

  Definition VectorTail {A:Type} {n:nat} (d:@Vector A (S n)): @Vector A n :=
    match d with
    | DVector v D => DVector (Vtail v) (svector_tl_dense D)
    | SVector v => SVector (Vtail v)
    end.

  Definition tryDenseVectorExtract {A} {n} (d:@Vector A n): @maybeError (vector A n) :=
    match d with
    | SVector _ => Error "Attempting to extract dense vector from sparse or"
    | DVector v H => OK (vector_from_svector v H)
    end.

  Definition sparseVectorExtract {A} {n} (d:@Vector A n): (svector A n) :=
    match d with
    | DVector v _ => v
    | SVector v => v
    end.

  Definition densifyVector {A} {n} (d:@Vector A n) (D: svector_is_dense (sparseVectorExtract d)):
    (@Vector A n) :=
    match d with
    | DVector _ _ as ad => ad (* already dense *)
    | SVector _ => DVector (sparseVectorExtract d) D
    end.

End ProofCarryingSparseVector.

    
