Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Structures.CoMonad.
Require Import ExtLib.Core.Type.

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

  Variable w: Type.
  Variable m: Monoid w.
  Local Instance w_type: type w := type_libniz w.
  Variable ml: MonoidLaws m.

  Global Instance WriterCoMonad:
    CoMonad (@writer w m) :=
    {
      coret A x := evalWriter x ;
      cobind A B wa f := tell (execWriter wa) ;; ret (f wa)
    }.

  Global Instance WriterCoMonadLaws:
    CoMonadLaws (@WriterCoMonad).
  Proof.
    split.
    -
      intros A B.
      unfold extract, extend.
      extensionality x.
      unfold coret, cobind, WriterCoMonad, id.
      unfold evalWriter, execWriter, runWriter.
      destruct x, runWriterT, unIdent.
      simpl.
      repeat f_equal.
      apply ml.
    -
      reflexivity.
    -
      intros A B f g.
      unfold extract, extend, compose.
      unfold coret, cobind, WriterCoMonad.
      extensionality x.
      repeat f_equal.
      apply ml.
  Qed.
End Writer_Comonad.
