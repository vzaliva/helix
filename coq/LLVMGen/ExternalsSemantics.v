From Vellvm Require Import
     LLVMIO
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

Require Import ExtLib.Structures.Monads.

Import MonadNotation.
Import ListNotations.

Definition Float_maxnum (a b: float): float :=
  if Float.cmp Clt a b then b else a.

Definition Float32_maxnum (a b: float32): float32 :=
  if Float32.cmp Clt a b then b else a.

Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).
  Open Scope string_scope.

  Import LLVMIO.
  Import DV.

  Definition semantic_function := (list dvalue) -> err dvalue.
  Definition intrinsic_definitions := list (string * semantic_function).

  Definition llvm_maxnum_f64 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double a; DVALUE_Double b] => ret (DVALUE_Double (Float_maxnum a b))
      | _ => raise "llvm_maxnum_f64 got incorrect / ill-typed intputs"
      end.

  Definition llvm_maxnum_f32 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float a; DVALUE_Float b] => ret (DVALUE_Float (Float32_maxnum a b))
      | _ => raise "llvm_maxnum_f32 got incorrect / ill-typed intputs"
      end.

  Definition helix_intrinsics : intrinsic_definitions :=
    [ ("llvm.maxnum.f64", llvm_maxnum_f64) ;
        ("llvm.maxnum.f32", llvm_maxnum_f32)
    ].

End Make.
