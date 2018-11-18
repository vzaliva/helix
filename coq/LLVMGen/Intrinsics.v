Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.LLVMGen.Utils.

Import ListNotations.

Section fabs.
  (*
    declare float     @llvm.fabs.f32(float  %Val)
    declare double    @llvm.fabs.f64(double %Val)
   *)

  Definition fabs_32: toplevel_entity (list block) :=
    TLE_Declaration
      {|
        dc_name        := Name ("llvm.fabs.f32");
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

  Definition fabs_64: toplevel_entity (list block) :=
    TLE_Declaration
      {|
        dc_name        := Name ("llvm.fabs.f64");
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

  Definition maxnum_32: toplevel_entity (list block) :=
    TLE_Declaration
      {|
        dc_name        := Name ("llvm.maxnum.f32");
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

  Definition maxnum_64: toplevel_entity (list block) :=
    TLE_Declaration
      {|
        dc_name        := Name ("llvm.maxnum.f64");
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

Definition all_intrinsics : toplevel_entities (list block)
  := [ maxnum_32 ; maxnum_64 ;
         fabs_32 ; fabs_64].