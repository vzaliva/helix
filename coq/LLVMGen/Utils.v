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

(* Placeholder section for config variables. Probably should be a
module in future *)
Section Config.
  Definition IntType := TYPE_I 64%Z.
  Definition PtrAlignment := 16%Z.
  Definition ArrayPtrParamAttrs := [ PARAMATTR_Align PtrAlignment; PARAMATTR_Nonnull ].
End Config.

(* TODO: move. Lifted from Software foundations *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match Nat.modulo n 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := append d acc in
  match time with
  | 0 => acc'
  | S time' =>
    match Nat.div n 10 with
    | 0 => acc'
    | n' => string_of_nat_aux time' n' acc'
    end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

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
  | TYPE_I 64%Z => "int64"
  | TYPE_Double => "float64"
  | TYPE_Array n TYPE_Double => append "float64[" ((String.string_of_Z n) ++ "]")
  | TYPE_Pointer p => append "*" (string_of_IRType p)
  | _ => "#INVALID"
  end.

Definition string_of_vars (vars:list (ident * typ)) : string
  := "[" ++ String.concat ", " (List.map
                                  (fun '(n,t) =>
                                     append (string_of_ident n)
                                            (":" ++(string_of_IRType t))
                                  )
                           vars) ++ "]".
