(*
Copyright (c) 2009 Wouter Swierstra.
All rights reserved.

Tested with Coq version 8.2.
 *)

Require Import Program.
Require Import Arith.
Require Import Omega.
Require Import List.

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Implicit Arguments Leaf [a].
Implicit Arguments Node [a].

Fixpoint flatten (a : Set) (t : Tree a) : list a
  :=  match t with
      | Leaf x => x :: nil
      | Node l r => flatten (a)l ++ flatten (a) r end.

Section HoareState.
  Variable s : Set.
  Definition Pre : Type := s -> Prop.

  Definition Post (a : Set) : Type := s -> a -> s -> Prop.

  Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set
    := forall i : { t : s | pre t }, { (x,f) : a * s | post i x f}.

  Definition top : Pre := fun s => True.

  Program Definition returns (a : Set)
    : forall x, HoareState top a (fun i y f => i = f /\ y = x)
    := fun x s => (x , s).

  Program Definition bind : forall a b P1 P2 Q1 Q2,
      (HoareState P1 a Q1) ->
      (forall (x : a), HoareState (P2 x) b (Q2 x)) ->
      HoareState  (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
                  b
                  (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)
    :=  fun a b P1 P2 Q1 Q2 c1 c2 s1 =>
          match c1 s1 with (x, s2) => c2 x s2 end.
  Next Obligation.
  Proof.
    rename Heq_anonymous into H.
    unfold proj1_sig in H.
    elim H; auto.
  Qed.

  Next Obligation.
  Proof with simpl in *; trivial.
    destruct_call c1...
    destruct H as [P1s P2rh].
    apply (P2rh x s2).
    rewrite <- Heq_anonymous in y...
  Qed.

  Next Obligation.
  Proof with simpl in *; trivial.
    destruct_call c2...
    destruct_call c1 in Heq_anonymous...
    rewrite <- Heq_anonymous in y0...
    destruct x0 as [x2  f0].
    exists x; exists s2; split...
  Qed.
  Program Definition get : HoareState top s (fun i x f => i = f /\ x = i)
    := fun s => (s, s).

  Program Definition put (x : s) : HoareState top unit (fun _ _ f => f = x)
    := fun _ => (tt, x).
End HoareState.


Implicit Arguments returns [a s].
Implicit Arguments bind [a b P1 P2 Q1 Q2 s].
Infix ">>=" := bind (at level 80, right associativity).
Notation "c >> d" := (bind c (fun _ => d))
                       (at level 80, right associativity).
Implicit Arguments get [s].
Implicit Arguments put [s].

Fixpoint size (a : Set) (t : Tree a) : nat :=
  match t with
  | Leaf x => 1
  | Node l r => size (a) l + size (a) r end.

Implicit  Arguments size [a].

Fixpoint seq (x n : nat) : list nat :=
  match n with
  | 0 => nil
  | S k => x :: seq (S x) k end.

Program Fixpoint relabel (a : Set) (t : Tree a) :
  HoareState nat  (top nat)
             (Tree nat)
             (fun i t f => f = i + size t /\ flatten (nat) t = seq i (size t))
  := match t with
     | Leaf x =>  get (s := nat) >>= fun n =>
                                       put (n + 1) >>
                                           returns (Leaf n)
     | Node l r =>  relabel (a) l >>= fun l' =>
                                        relabel (a) r >>= fun r' =>
                                                            returns (Node l' r') end.

Lemma SeqSplit : forall y x z, seq x (y + z) = seq x y ++ seq (x + y) z.
Proof with simpl; auto.
  induction y...
  intros x z...
  rewrite IHy, plus_Snm_nSm...
Qed.

Next Obligation.
Proof with simpl in *; auto.
  destruct_call (bind (s:=nat))...
  clear relabel l r H.
  destruct_conjs...
  rename y into l, H1 into r, H into lState, H3 into rState.
  rename H0 into sizeL, H4 into sizeR, H2 into flattenL, H7 into flattenR.
  rename H5 into finalState, H6 into finalRes.
  rewrite finalRes.
  split...
  omega.
  rewrite flattenL, flattenR, sizeL, SeqSplit...
Defined.

Implicit Arguments flatten [a].

Program Definition do (s a : Set) (P1 P2 : Pre s) (Q1 Q2 : Post s a) :
  (forall i, P2 i -> P1 i) -> (forall i x f, Q1 i x f -> Q2 i x f) ->
  HoareState s P1 a Q1 -> HoareState s P2 a Q2
  := fun str wkn c => c.
Next Obligation.
Proof with simpl; auto.
  destruct_call c...
  destruct x0 as [x1 f]...
Defined.
Implicit Arguments do [s a P1 P2 Q1 Q2].


Program Fixpoint final (a : Set) (t : Tree a) :
  HoareState (nat) (top nat) (Tree nat) (fun i t f => NoDup (flatten t))
  := do _ _ (relabel a t).

Lemma SeqLemma : forall n x y, x < y -> ~ In x (seq y n).
Proof with auto.
  induction n...
  intros x y H.
  intro T; elim T.
  intro F.
  rewrite F in H.
  apply (lt_irrefl x H).
  apply IHn; auto.
Qed.

Lemma NElemLemma : forall n i, ~ In i (seq (S i) n).
  induction n; intros; apply SeqLemma; auto.
Qed.

Lemma NoDupSeq (n i : nat) : NoDup (seq i n).
  induction n; simpl; constructor.
  apply NElemLemma.
  apply IHn.
Qed.

Next Obligation.
  rewrite H0.
  apply NoDupSeq.
Qed.
