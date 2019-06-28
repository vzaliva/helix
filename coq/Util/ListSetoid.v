Require Import Coq.Arith.Lt.
Require Import CoLoR.Util.Nat.NatUtil.
Require Import Coq.Lists.List.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.

Import ListNotations.

Global Instance List_equiv {A: Type} `{Ea: Equiv A}: Equiv (list A) := List.Forall2 equiv.

Global Instance Forall2_Reflexive
       {A: Type} {R: relation A} `{RR: Reflexive A R}:
  Reflexive (Forall2 R).
Proof.
  intros x.
  induction x; constructor; auto.
Qed.

Global Instance nth_error_proper {A: Type} `{Ae: Equiv A} `{AEe: Equivalence A Ae}:
  Proper ((=) ==> (=) ==> (=)) (@nth_error A).
Proof.
  intros l1 l2 El n1 n2 En.
  unfold equiv, peano_naturals.nat_equiv in En.
  subst n2. rename n1 into n.
  revert l1 l2 El.
  induction n.
  -
    intros l1 l2 El.
    simpl.
    repeat break_match; auto; try inversion El.
    rewrite H2.
    reflexivity.
  -
    intros l1 l2 El.
    destruct l1, l2; try inversion El.
    auto.
    simpl.
    apply IHn.
    inversion El.
    auto.
Qed.

Definition isNth {A:Type} `{Equiv A} (l:list A) (n:nat) (v:A) : Prop :=
  match nth_error l n with
  | None => False
  | Some x => x = v
  end.

Lemma isNth_Sn {A:Type} `{Equiv A} (h:A) (l:list A) (n:nat) (v:A):
  isNth (h :: l) (S n) v ≡ isNth l n v.
Proof.
  crush.
Qed.

Definition listsDiffByOneElement {A:Type} `{Ae:Equiv A} (l0 l1:list A) (n:nat) : Prop :=
  forall i, i≢n -> nth_error l0 i = nth_error l1 i.

Lemma listsDiffByOneElement_Sn {A:Type} `{Ae:Equiv A} {Aeq: Equivalence Ae} (h0 h1:A) (l0 l1:list A) (n:nat):
  h0 = h1 ->
  listsDiffByOneElement l0 l1 n ->
  listsDiffByOneElement (h0::l0) (h1::l1) (S n).
Proof.
  intros E H.
  unfold listsDiffByOneElement in *.
  intros i ic.
  destruct i.
  -
    simpl.
    some_apply.
  -
    simpl.
    apply H.
    crush.
Qed.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Section Monadic.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Fixpoint monadic_fold_left
           {A B : Type}
           {m : Type -> Type}
           {M : Monad m}
           (f : A -> B -> m A) (a : A) (l : list B)
    : m A
    := match l with
       | List.nil => ret a
       | List.cons b l =>
         a' <- f a b ;;
            monadic_fold_left f a' l
       end.


  Fixpoint monadic_fold_left_rev
           {A B : Type}
           {m : Type -> Type}
           {M : Monad m}
           (f : A -> B -> m A) (a : A) (l : list B)
    : m A
    := match l with
       | List.nil => ret a
       | List.cons b l => a' <- monadic_fold_left_rev f a l ;;
                             f a' b
       end.

  (* Probably could be proven more generally for any monad with with some properties *)
  Global Instance monadic_fold_left_rev_opt_proper
         {A B : Type}
         `{Eb: Equiv B}
         `{Ae: Equiv A}
         `{Equivalence A Ae}
         (f : A -> B -> option A)
         `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
         (a : A)
    :
      Proper ((=) ==> (=)) (monadic_fold_left_rev f a).
  Proof.
    intros x y E.
    induction E.
    -
      reflexivity.
    -
      simpl.
      repeat break_match; try some_none.
      some_inv.
      apply f_mor; auto.
  Qed.

  Program Fixpoint monadic_Lbuild
          {A: Type}
          {m : Type -> Type}
          {M : Monad m}
          (n : nat)
          (gen : forall i, i < n -> m A) {struct n}: m (list A) :=
    match n with
    | O => ret (List.nil)
    | S p =>
      let gen' := fun i ip => gen (S i) _ in
      liftM2 List.cons (gen 0 (lt_O_Sn p)) (@monadic_Lbuild A m M p gen')
    end.

  Lemma monadic_Lbuild_cons
        {A: Type}
        {m : Type -> Type}
        {M : Monad m}
        (n : nat)
        (gen : forall i, i < S n -> m A)
    :
      monadic_Lbuild _ gen ≡
                     liftM2 List.cons (gen 0 (lt_O_Sn n)) (monadic_Lbuild _ (fun i ip => gen (S i) (lt_n_S ip))).
  Proof.
    simpl.
    f_equiv.
    f_equiv.
    extensionality i.
    extensionality ip.
    f_equiv.
    apply NatUtil.lt_unique.
  Qed.

  Lemma monadic_Lbuild_opt_length
        {A: Type}
        (n : nat)
        (gen : forall i, i < n -> option A)
        (l: list A)
    :
      monadic_Lbuild _ gen ≡ Some l → Datatypes.length l ≡ n.
  Proof.
    intros H.
    dependent induction n.
    -
      simpl in H.
      some_inv.
      reflexivity.
    -
      destruct l.
      +
        exfalso.
        simpl in *.
        repeat break_match_hyp; try some_none.
        inversion H.
      +
        simpl.
        f_equiv.
        apply IHn with (gen:=fun i ip => gen (S i) (lt_n_S ip)).
        simpl in H.
        repeat break_match_hyp; try some_none.
        inversion H.
        subst.
        rewrite <- Heqo0.
        f_equiv.
        extensionality i.
        extensionality ip.
        f_equiv.
        apply NatUtil.lt_unique.
  Qed.

  (* Could be proven <-> *)
  Lemma monadic_Lbuild_op_eq_None
        {A: Type}
        (n : nat)
        (gen : forall i, i < n -> option A):

    monadic_Lbuild _ gen ≡ None -> exists i ic, gen i ic ≡ None.
  Proof.
    intros H.
    dependent induction n.
    -
      simpl in H.
      some_none.
    -
      simpl in H.
      repeat break_match_hyp; try some_none; clear H.
      +
        remember (λ (i : nat) (ip : i < n), gen (S i)
                                              (orders.strictly_order_preserving S i n ip)) as gen' eqn:G.
        specialize (IHn gen' Heqo0).
        subst gen'.
        destruct IHn as [i [ic IHn]].
        eexists; eexists; eapply IHn.
      +
        eexists; eexists; eapply Heqo.
  Qed.

  Lemma monadic_Lbuild_op_eq_Some
        {A: Type}
        (n : nat)
        (gen : forall i, i < n -> option A)
        (l: list A)
    :

      monadic_Lbuild _ gen ≡ Some l -> (forall i ic, List.nth_error l i ≡ gen i ic).
  Proof.
    intros H i ic.
    pose proof (monadic_Lbuild_opt_length _ gen _ H).
    dependent induction n.
    -
      inversion ic.
    -
      destruct l as [| l0 l].
      inversion H0.
      simpl in H.
      destruct i.
      +
        repeat break_match_hyp; simpl in *; try some_none.
        inversion H.
        subst.
        rewrite <- Heqo.
        f_equiv.
        apply NatUtil.lt_unique.
      +
        simpl.
        specialize (IHn (fun i ip => gen (S i) (lt_n_S ip))).
        assert(ic1: i<n) by  apply lt_S_n, ic.
        rewrite IHn with (ic:=ic1); clear IHn.
        *
          f_equiv.
          apply NatUtil.lt_unique.
        *
          repeat break_match_hyp; simpl in *; try some_none.
          inversion H.
          subst.
          rewrite <- Heqo0.
          f_equiv.
          extensionality j.
          extensionality jc.
          f_equiv.
          apply NatUtil.lt_unique.
        *
          simpl in H0.
          auto.
  Qed.


End Monadic.
