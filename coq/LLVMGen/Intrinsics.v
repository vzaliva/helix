Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.


Require Import Helix.LLVMGen.Utils.

(*
declare float     @llvm.fabs.f32(float  %Val)
declare double    @llvm.fabs.f64(double %Val)
declare float     @llvm.maxnum.f32(float  %Val0, float  %Val1l)
declare double    @llvm.maxnum.f64(double %Val0, double %Val1)
*)