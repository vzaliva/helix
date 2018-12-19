Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.LLVMGen.Utils.

Import ListNotations.

Section memcpy.

  Definition memcpy_8: declaration :=
    let pt := TYPE_Pointer (TYPE_I 8%Z) in
    let i32 := TYPE_I 32%Z in
    let i1 := TYPE_I 1%Z in
    {|
      dc_name        := Name "llvm.memcpy.p0i8.p0i8.i32";
      dc_type        := TYPE_Function TYPE_Void [pt; pt; i32; i32; i1] ;
      dc_param_attrs := ([], [[];[];[];[];[]]);
      dc_linkage     := None ;
      dc_visibility  := None ;
      dc_dll_storage := None ;
      dc_cconv       := None ;
      dc_attrs       := [] ;
      dc_section     := None ;
      dc_align       := None ;
      dc_gc          := None
    |}.

End memcpy.

Section fabs.
  (*
    declare float     @llvm.fabs.f32(float  %Val)
    declare double    @llvm.fabs.f64(double %Val)
   *)

  Definition fabs_32: declaration :=
    {|
      dc_name        := Name "llvm.fabs.f32";
      dc_type        := TYPE_Function TYPE_Float [TYPE_Float] ;
      dc_param_attrs := ([], [[]]);
      dc_linkage     := None ;
      dc_visibility  := None ;
      dc_dll_storage := None ;
      dc_cconv       := None ;
      dc_attrs       := [] ;
      dc_section     := None ;
      dc_align       := None ;
      dc_gc          := None
    |}.

  Definition fabs_64: declaration :=
    {|
      dc_name        := Name "llvm.fabs.f64";
      dc_type        := TYPE_Function TYPE_Double [TYPE_Double] ;
      dc_param_attrs := ([], [[]]);
      dc_linkage     := None ;
      dc_visibility  := None ;
      dc_dll_storage := None ;
      dc_cconv       := None ;
      dc_attrs       := [] ;
      dc_section     := None ;
      dc_align       := None ;
      dc_gc          := None
    |}.

End fabs.

Section maxnum.
  (*
    declare float     @llvm.maxnum.f32(float  %Val0, float  %Val1l)
    declare double    @llvm.maxnum.f64(double %Val0, double %Val1)
   *)

  Definition maxnum_32: declaration :=
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

  Definition maxnum_64: declaration :=
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

End maxnum.

Definition intrinsic_exp (d:declaration): exp :=
  EXP_Ident (ID_Global (dc_name d)).

Definition all_intrinsics : toplevel_entities (list block)
  := [
      @TLE_Comment (list block) "Prototypes for intrinsics we use" ;
        TLE_Declaration memcpy_8 ;
        TLE_Declaration maxnum_32 ;
        TLE_Declaration maxnum_64 ;
        TLE_Declaration fabs_32 ;
        TLE_Declaration fabs_64].