(* integer type as module *)

Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.Misc.

Require Import MathClasses.interfaces.abstract_algebra.

Module Type NType.

  Parameter Inline t : Type.

  Declare Instance NTypeEquiv: Equiv t.
  Declare Instance NTypeSetoid: @Setoid t NTypeEquiv.

  (* could always be converted to `nat` *)
  Parameter to_nat: t -> nat.
  Declare Instance to_nat_proper: Proper ((=) ==> (=)) to_nat.

  (* not all nats could be converted to `t` *)
  Parameter from_nat: nat -> err t.
  Declare Instance from_nat_proper: Proper ((=) ==> (=)) from_nat.

  (* arithmetics operators *)
  Parameter NTypeDiv   : t -> t -> t.
  Parameter NTypeMod   : t -> t -> t.
  Parameter NTypePlus  : t -> t -> t.
  Parameter NTypeMinus : t -> t -> t.
  Parameter NTypeMult  : t -> t -> t.
  Parameter NTypeMin   : t -> t -> t.
  Parameter NTypeMax   : t -> t -> t.

  Declare Instance NTypeDiv_proper: Proper ((=) ==> (=) ==> (=)) NTypeDiv  .
  Declare Instance NTypeMod_proper: Proper ((=) ==> (=) ==> (=)) NTypeMod  .
  Declare Instance NTypePlus_proper: Proper ((=) ==> (=) ==> (=)) NTypePlus .
  Declare Instance NTypeMinus_proper: Proper ((=) ==> (=) ==> (=)) NTypeMinus.
  Declare Instance NTypeMult_proper: Proper ((=) ==> (=) ==> (=)) NTypeMult .
  Declare Instance NTypeMin_proper: Proper ((=) ==> (=) ==> (=)) NTypeMin  .
  Declare Instance NTypeMax_proper: Proper ((=) ==> (=) ==> (=)) NTypeMax  .

  Parameter to_string: t -> String.string.

  (* If [from_nat] succeeds for a number, it also succeeds for all
     numbers less than it.
   *)
  Parameter from_nat_lt:
    forall x xi y,
      from_nat x ≡ inr xi ->
      (y<x)%nat ->
      exists yi, from_nat y ≡ inr yi.

End NType.
