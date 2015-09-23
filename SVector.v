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

Definition empty_svector {A} n: svector A n := @Vconst (option A) None n.

Definition svector_is_empty {A} {n} (v:svector A n) := Vforall is_None v.


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


Lemma dense_cons:
  forall A n (h:option A) (t: svector A n),
    (is_Some h /\ svector_is_dense t) = svector_is_dense (Vcons h t).
Proof.
  crush.
Qed.

Lemma dense_casts_OK:
  ∀ A n (x : svector A n),
    svector_is_dense x → is_OK (try_vector_from_svector x).
Proof.
  induction x. 
  auto.

  intros.
  assert (svector_is_dense x). apply svector_tl_dense in H. auto.
  assert (is_Some h). apply H.

  dep_destruct h.
  simpl.
 
  destruct (try_vector_from_svector x);auto.
  auto.
Qed.

Lemma svector_from_vector_is_dense
      {A:Type} {n:nat}
      (y: svector A n) (x: vector A n):
  (svector_from_vector x ≡ y) → svector_is_dense y.
Proof.
  intros.
  destruct H.
  unfold svector_from_vector, svector_is_dense.
  induction n.
  VOtac. crush. 
  VSntac x. simpl.
  auto.
Qed.
  

Lemma VnthDense {B} {n} {x: svector B n} {i} {ip:(i<n)%nat}:
  svector_is_dense x -> is_Some (Vnth x ip).
Proof.
  intros D.
    unfold svector_is_dense in D.
    apply Vforall_nth.
    auto.
Qed.


