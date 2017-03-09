Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Structures.CoMonad.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Import MonadNotation.
Local Open Scope program_scope.
Local Open Scope monad_scope.

Section Writer_Monad.
  Variable s t : Type.
  Variable Monoid_s : Monoid s.

  Definition writer := writerT Monoid_s ident.
  Definition runWriter x := unIdent (@runWriterT s Monoid_s ident t x).
  Definition execWriter x:= psnd (runWriter x).
  Definition evalWriter x:= pfst (runWriter x).
End Writer_Monad.

Section CoMonad_Laws.
  Variable m : Type -> Type.
  Variable C : CoMonad m.

  (* Convenience functions, renaming and changing arguments order *)
  Definition extract {A:Type}: (m A) -> A := @coret m C A.
  Definition extend {A B:Type} (f: m A -> B): m A -> m B  :=
    fun x => @cobind m C A B x f.

  Class CoMonadLaws : Type :=
    {
      extend_extract: forall (A B:Type),
        extend (B:=A) extract = id ;

      extract_extend: forall (A B:Type) {f},
          extract ∘ (@extend A B) f = f;

      extend_extend:forall (A B:Type) {f g},
          (@extend B A) f ∘ (@extend A B) g = extend (f ∘ extend g)
    }.
End CoMonad_Laws.

Section Writer_Comonad.
  Global Instance WriterCoMonad {w:Type} {m: Monoid w}:
    CoMonad (@writer w m) :=
    {
      coret A x := evalWriter x ;
      cobind A B wa f := tell (execWriter wa) ;; ret (f wa)
    }.

  Global Instance WriterCoMonadLaws {w:Type} {m: Monoid w}:
    CoMonadLaws (@WriterCoMonad w m).
  Proof.
    split.
    -
      intros A B.
      extensionality x.
      admit.
    -
      intros A B f.
      extensionality x.
      unfold compose.
      admit.
    -
      intros A B f g.
      extensionality x.
      unfold compose.
      admit.
  Qed.
End Writer_Comonad.
