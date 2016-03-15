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

Definition runWriter x := @runWriterT bool sticky option nat x.
Definition execWriter x:= liftM (@snd nat bool) (runWriter x).
Definition evalWriter x:= liftM (@fst nat bool) (runWriter x).

Compute (runWriter ex1).
Compute (execWriter ex1).
Compute (evalWriter ex1).

Compute (runWriter ex2).


(* TODO: Not converted code below *)

Definition equiv {T: Type} (a b: m T) :=
  (evalWriter a) = (evalWriter b).

Require Import Coq.Classes.Morphisms.

Lemma evalWriter_lift_uop
      (op: nat -> nat)
      {a: m nat}
  :
    evalWriter ((lift_uop op) a) = op (evalWriter a).
Proof.
  reflexivity.
Qed.

Lemma evalWriter_lift_bop
      (op: nat -> nat -> nat)
      {a b: m nat}
  :
    evalWriter (lift_bop op a b) = op (evalWriter a) (evalWriter b).
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
  unfold evalWriter, runWriter in *.
  unfold lift_uop.

  simpl. (* also cbv or compute works *)
  rewrite H.
  reflexivity.
   *)

  unfold equiv in *.
  rewrite 2!evalWriter_lift_uop.
  rewrite H.
  reflexivity.
Qed.




