Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Require Import ExtLib.Data.ListNth.

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

Lemma rev_nil (A:Type) (x:list A):
  rev x = nil -> x = nil.
Proof.
  intros H.
  destruct x.
  -
    reflexivity.
  -
    simpl in H.
    symmetry in H.
    contradict H.
    apply app_cons_not_nil.
Qed.

(* List elements unique wrt projection [p] using [eq] *)
Definition list_uniq {A B:Type} (p: A -> B) (l:list A): Prop
  := forall x y a b,
    List.nth_error l x = Some a ->
    List.nth_error l y = Some b ->
    (p a) = (p b) -> x=y.

Lemma list_uniq_nil {A B:Type} (p: A -> B):
  list_uniq p (@nil A).
Proof.
  unfold list_uniq.
  intros x y a b H H0 H1.
  rewrite nth_error_nil in H.
  inversion H.
Qed.

Lemma list_uniq_cons {A B:Type} (p: A -> B) (a:A) (l:list A):
  list_uniq p l /\
  not (exists j x, nth_error l j = Some x /\ p x = p a) <->
  list_uniq p (a :: l).
Proof.
  split.
  -
    intros [U E].
    unfold list_uniq in *.
    intros x y a0 b H H0 H1.
    destruct x,y; cbn in *.
    +
      reflexivity.
    +
      inversion H; subst.
      contradict E.
      exists y, b.
      auto.
    +
      inversion H0; subst.
      contradict E.
      exists x, a0.
      auto.
    +
      apply eq_S.
      eapply U; eauto.
  -
    admit.
Admitted.

Lemma list_uniq_de_cons {A B:Type} (p: A -> B) (a:A) (l:list A):
  list_uniq p (a :: l) ->
  list_uniq p l.
Proof.
  intros H.
  unfold list_uniq in *.
  intros x y a0 b H0 H1 H2.
  cut (S x = S y). auto.
  eapply H; eauto.
Qed.

Lemma app_nth_error2 :
  forall {A: Type} (l:list A) l' n, n >= List.length l -> nth_error (l++l') n = nth_error l' (n-length l).
Proof.
  induction l; intros l' d [|n]; auto;
    cbn; rewrite IHl; auto with arith.
Qed.

Lemma app_nth_error1 :
  forall {A:Type} (l:list A) l' n, n < length l -> nth_error (l++l') n = nth_error l n.
Proof.
  induction l.
  - inversion 1.
  - intros l' n H.
    cbn.
    destruct n; [reflexivity|].
    rewrite 2!nth_error_Sn.
    apply IHl.
    cbn in H.
    auto with arith.
Qed.

Lemma rev_nth_error : forall {A:Type} (l:list A) n,
    (n < List.length l)%nat ->
    nth_error (rev l) n = nth_error l (List.length l - S n) .
Proof.
  induction l.
  intros; inversion H.
  intros.
  simpl in H.
  simpl (rev (a :: l)).
  simpl (List.length (a :: l) - S n).
  inversion H.
  rewrite <- minus_n_n; simpl.
  rewrite <- rev_length.
  rewrite app_nth_error2; auto.
  rewrite <- minus_n_n; auto.
  rewrite app_nth_error1; auto.
  rewrite (minus_plus_simpl_l_reverse (length l) n 1).
  replace (1 + length l) with (S (length l)); auto with arith.
  rewrite <- minus_Sn_m; auto with arith.
  apply IHl ; auto with arith.
  rewrite rev_length; auto.
Qed.
