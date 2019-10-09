From Vellvm Require Import
     LLVMEvents
     LLVMAst
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

Import MonadNotation.
Import ListNotations.

Definition Float_maxnum (a b: float): float :=
  if Float.cmp Clt a b then b else a.

Definition Float32_maxnum (a b: float32): float32 :=
  if Float32.cmp Clt a b then b else a.

Definition maxnum_64_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.maxnum.f64";
    dc_type        := TYPE_Function TYPE_Double [TYPE_Double;TYPE_Double] ;
    dc_param_attrs := ([], [[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition maxnum_32_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.maxnum.f32";
    dc_type        := TYPE_Function TYPE_Float [TYPE_Float;TYPE_Float] ;
    dc_param_attrs := ([], [[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition helix_intrinsics_decls :=
  [ maxnum_32_decl ; maxnum_64_decl ].

Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).
  Open Scope string_scope.

  Import LLVMIO.
  Import DV.

  Definition semantic_function := (list dvalue) -> err dvalue.
  Definition intrinsic_definitions := list (declaration typ * semantic_function).

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
    [ (maxnum_64_decl, llvm_maxnum_f64) ;
        (maxnum_32_decl, llvm_maxnum_f32)
    ].

End Make.
