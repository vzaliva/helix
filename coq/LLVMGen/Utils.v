Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import ExtLib.Structures.Monads.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

(* Temporary workaround until coq-ext-lib is updated in OPAM *)
Notation "' pat <- c1 ;; c2" :=
    (@pbind _ _ _ _ _ c1 (fun x => match x with pat => c2 end))
      (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

(* Placeholder section for config variables. Probably should be a
module in future *)
Section Config.
  Definition IntType := TYPE_I 64%Z.
  Definition ArrayPtrParamAttrs := [ PARAMATTR_Align 16%Z ].
  Definition GlobalPtrAlignment := Some 16%Z.
  Definition TempPtrAlignment := Some 16%Z.
End Config.
