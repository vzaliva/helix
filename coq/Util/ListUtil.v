Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint fold_left_rev
         {A B : Type}
         (f : A -> B -> A) (a : A) (l : list B)
  : A
  := match l with
     | List.nil => a
     | List.cons b l => f (fold_left_rev f a l) b
     end.

Program Fixpoint Lbuild {A: Type}
        (n : nat)
        (gen : forall i, i < n -> A) {struct n}: list A :=
  match n with
  | O => List.nil
  | S p =>
    let gen' := fun i ip => gen (S i) _ in
    List.cons (gen 0 _) (@Lbuild A p gen')
  end.
Next Obligation. apply lt_n_S, ip. Qed.
Next Obligation. apply Nat.lt_0_succ. Qed.

Lemma nth_error_Sn {A:Type} (x:A) (xs:list A) (n:nat):
  nth_error (x::xs) (S n) = nth_error xs n.
Proof.
  reflexivity.
Qed.
