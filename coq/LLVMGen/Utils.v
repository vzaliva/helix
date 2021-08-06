Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.Util.Misc.

Require Import Vellvm.Syntax.

From ITree Require Import ITree Eq.Eq.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.
From Coq Require Import ZArith.

Require Import ExtLib.Structures.Monads.

Require Import Ceres.CeresString.

Import Memory.NM.
Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

(* Placeholder section for config variables. Probably should be a
module in future *)
Section Config.
  Definition IntType := TYPE_I 64%N.
  Definition PtrAlignment := 16%Z.
  Definition ArrayPtrParamAttrs := [ PARAMATTR_Align PtrAlignment; PARAMATTR_Nonnull ].
End Config.

Definition string_of_raw_id (r:raw_id): string
:= match r with
   | Name s => s
   | Anon _ => "#ANON"
   | Raw  _ => "#RAW"
   end.

Definition string_of_ident (i:ident) : string :=
  match i with
  | ID_Global n => (append "Global " (string_of_raw_id n))
  | ID_Local  n => (append "Local " (string_of_raw_id n))
  end.

Fixpoint string_of_IRType (t: typ) :=
  match t with
  | TYPE_I 64%N => "int64"
  | TYPE_Double => "float64"
  | TYPE_Array n TYPE_Double => append "float64[" ((Ceres.CeresString.string_of_N n) ++ "]")
  | TYPE_Pointer p => append "*" (string_of_IRType p)
  | _ => "#INVALID"
  end.

Definition string_of_Γ (Γ:list (ident * typ)) : string
  := "[" ++ String.concat ", " (List.map
                                  (fun '(n,t) =>
                                     append (string_of_ident n)
                                            (":" ++(string_of_IRType t))
                                  )
                           Γ) ++ "]".

Definition Same_t e `{canonical_names.Equiv e} (B C : t e) := forall k : key, find (elt:=e) k B = find (elt:=e) k C.
    (* Same Extensionality property as [Extensionality_Ensembles] in [Coq.Sets.Ensembles]. *)
Axiom Extensionality_t : forall e `{canonical_names.Equiv e} (A B: t e), Same_t A B -> A = B.

Lemma typ_to_dtyp_P :
    forall t s,
      typ_to_dtyp s (TYPE_Pointer t) = DTYPE_Pointer.
Proof.
  intros t s.
  apply typ_to_dtyp_equation.
Qed.

Ltac typ_to_dtyp_simplify :=
  repeat
    (try rewrite typ_to_dtyp_I in *;
      try rewrite typ_to_dtyp_D in *;
      try rewrite typ_to_dtyp_D_array in *;
      try rewrite typ_to_dtyp_P in *).
