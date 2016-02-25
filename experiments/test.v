Require Import Coq.Arith.EqNat.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.

Set Implicit Arguments.

Section with_monad.
  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition FlagsT : Type := bool.

  Variable Monoid_B : Monoid FlagsT.
  Variable m : Type -> Type.
  Context {Monad_m: Monad m}.
  Context {Writer_m: MonadWriter Monoid_B m}.

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

Section WriterMonad.
  Variable s t : Type.
  Variable Monoid_s : Monoid s.

  Definition writer := writerT Monoid_s ident.
  Definition runWriter x := unIdent (@runWriterT s Monoid_s ident t x).
  Definition execWriter x:= snd (runWriter x).
  Definition evalWriter x:= fst (runWriter x).
End WriterMonad.


Definition sticky := Build_Monoid orb false.
Definition m : Type -> Type := writer sticky.

Definition ex1 : m nat :=  (lift_bop plus) (ret 1) (ret 2).
Definition ex2 : m nat :=  (lift_bop plus) (ret 0) (ret 5).

Compute (runWriter ex1).
Compute (execWriter ex1).
Compute (evalWriter ex1).

Compute (runWriter ex2).

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




