Require Import Coq.Arith.EqNat.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Structures.Monoid.


Set Implicit Arguments.

Section with_monad.
  Import MonadNotation.
  Local Open Scope monad_scope.


  Definition sticky: Monoid bool := Build_Monoid orb false.
  Definition m : Type -> Type := writerT sticky option.
  Context {Monad_m: Monad m}.
  Context {Writer_m: MonadWriter sticky m}.


  Definition lift_uop
             (op: nat -> nat)
             (mx: m nat) : m nat :=
    x <- mx ;;
      tell (beq_nat x 0) ;;
      ret (op x).

  Definition lift_bop
             (op: nat -> nat -> nat)
             (mx my: m nat) : m nat :=
    x <- mx ;; y <- my ;;
      tell (orb (beq_nat x 0) (beq_nat y 0)) ;;
      ret (op x y).
End with_monad.


Definition ex1 : m nat :=  (lift_bop plus) (ret 1) (ret 2).
Definition ex2 : m nat :=  (lift_bop plus) (ret 0) (ret 5).
Definition ex3 : m nat :=  (lift_bop plus) (mzero) (mzero).
Definition ex4 : m nat :=  (lift_bop plus) (mzero) (ret 5).

Definition run x := (@runWriterT bool sticky option nat x).
Definition exec x:= liftM (@snd nat bool) (run x).
Definition eval x:= liftM (@fst nat bool) (run x).

Compute (run ex1).
Compute (exec ex1).
Compute (eval ex1).

Compute (run ex2).
Compute (run ex3).
Compute (run ex4).


(* TODO: Not converted code below *)

Definition equiv {T: Type} (a b: m T) :=
  (eval a) = (eval b).

Require Import Coq.Classes.Morphisms.

Lemma eval_lift_uop
      (op: nat -> nat)
      {a: m nat}
  :
    eval ((lift_uop op) a) = op (eval a).
Proof.
  reflexivity.
Qed.

Lemma eval_lift_bop
      (op: nat -> nat -> nat)
      {a b: m nat}
  :
    eval (lift_bop op a b) = op (eval a) (eval b).
Proof.
  reflexivity.
Qed.

Lemma test2
      (op: nat -> nat)
      `{op_mor: !Proper ((eq) ==> (eq)) op}
      {a b: m nat}
  :
    equiv a b ->
    equiv ((lift_uop op) a) ((lift_uop op) b).
Proof.
  intros H.

  (*  Direct proof:
  unfold equiv in *.
  unfold eval, runWriter in *.
  unfold lift_uop.

  simpl. (* also cbv or compute works *)
  rewrite H.
  reflexivity.
   *)

  unfold equiv in *.
  rewrite 2!eval_lift_uop.
  rewrite H.
  reflexivity.
Qed.




