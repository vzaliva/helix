
(* Core types *)
Module Type Types.
  (* Scalar types *)
  Parameter F32 F64: Type. (* floats *)
  Parameter I32 I64: Type. (* integers *)

  (* Machine epsilon values *)
  Parameter eps_S: F32.
  Parameter eps_D: F64.

  (* Arithmetic Operations *)
  Parameter addF64: F64 -> F64 -> F64.
  Parameter mulF64: F64 -> F64 -> F64.
End Types.

(* Memory *)
Module Type Memory (T:Types).
  Import T.

  Parameter PtrF32 PtrF64: Type.
  Parameter PtrI32 PtrI64: Type.

  Parameter nth_S: PtrF32 -> nat -> F32.
  Parameter nth_D: PtrF64 -> nat -> F64.
  Parameter nth_I: PtrI32 -> nat -> I32.
  Parameter nth_L: PtrI64 -> nat -> I64.
End Memory.

(* Vector operations *)
Module Type Intrinsics (T:Types).
  Import T.

  (* Supported vector types *)
  Parameter v2x64f : Type.
  Parameter v4x32f : Type.
  Parameter v2x64i : Type.
  Parameter v4x32i : Type.

  (* Constructors for common vector types *)
  Parameter vconst2x64f: F64 -> F64 -> v2x64f.
  Parameter vconst4x32f: F32 -> F32 -> F32 -> F32 -> v4x32f.
  Parameter vconst2x64i: I64 -> I64 -> v2x64i.
  Parameter vconst4x32i: I32 -> I32 -> I32 -> I32 -> v4x32i.

  (* Vector operations *)
  Parameter vdup_2x64f      : F64 -> v2x64f.
  Parameter vdup_4x32f      : F32 -> v4x32f.
  Parameter vcvt_64f32f     : v4x32f -> v2x64f.
  Parameter vcvt_64i32i     : v4x32i -> v2x64i.
  Parameter vcvt_32f64f     : v2x64f -> v4x32f.
  Parameter vcvt_32i64i     : v2x64i -> v4x32i.
  Parameter neg_2x64f       : v2x64f -> v2x64f.
  Parameter mul_2x64f       : v2x64f -> v2x64f -> v2x64f.
  Parameter add_2x64f       : v2x64f -> v2x64f -> v2x64f.
  Parameter addsub_4x32f    : v4x32f -> v4x32f -> v4x32f.
  Parameter addsub_2x64f    : v2x64f -> v2x64f -> v2x64f.
  Parameter min_2x64f       : v2x64f -> v2x64f -> v2x64f.
  Parameter max_2x64f       : v2x64f -> v2x64f -> v2x64f.
  Parameter cmpge_2x64f     : v2x64f -> v2x64f -> v2x64i.
  Parameter testc_4x32i     : v4x32i -> v4x32i -> bool.
  Parameter testnzc_4x32i   : v4x32i -> v4x32i -> bool.
  Parameter max3_2x64f      : v2x64f -> v2x64f -> v2x64f -> v2x64f.
  Parameter vushuffle_2x64f : v2x64f -> nat -> nat -> v2x64f.
  Parameter vshuffle_2x64f  : v2x64f -> v2x64f -> nat -> nat -> v2x64f.
End Intrinsics.
