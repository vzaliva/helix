(* iCode AST *)

Require Import List.
Require Import ZArith.
Require Import String.

Import ListNotations.

Open Scope list_scope.

Inductive inttype :=
| Int8Type
| Int16Type
| Int32Type
| Int64Type
| UInt8Type
| UInt16Type
| UInt32Type
| UInt64Type
| BoolType.

Inductive fptype :=
| FloatType (* IEEE 32-bit float *)
| DoubleType (* IEEE 64-bit float *).

Inductive arithtype :=
| I (value:inttype)
| F (value: fptype).

Inductive itype :=
| A (value:arithtype)
| VoidType
| ArrType (t:itype) (len:Z)
| VecType (t:arithtype) (len:Z)
| PtrType (t:itype) (alignment:Z).

(* Types for function and vairable names. For simplicity we will index them by integers *)
Definition varname := Z.
Definition funcname := string.

Definition float := string.

Inductive fconst :=
| FLiteral (value:float)
| FEPS.

Inductive dconst :=
| DLiteral (value:float)
| DEPS.

Inductive rvalue :=
| FunCallValue (f:funcall)
| VarRValue (var:varname)
| FConst (value:fconst)
| DConst (value:dconst)
| IConst (type:inttype) (value:Z)
| IConstArr (type:inttype) (values: list Z)
| FConstArr (values: list fconst)
| DConstArr (values: list dconst)
| FConstVec (values: list fconst)
| DConstVec (values: list dconst)
| IConstVec (type:inttype) (values: list Z)
| VdupRvalue (r:rvalue) (n:Z)
| NthRvalue (r:rvalue) (index:rvalue)
| RCast (type:itype) (r:rvalue)
| RDeref (r:rvalue)
with funcall :=
     (* polymorphic codnition operator *)
     | F_cond: rvalue -> rvalue -> rvalue -> funcall

     (* polymorphic artihmetic n-nary (n >= 2) operators *)
     | F_min: rvalue -> rvalue -> list rvalue -> funcall
     | F_max : rvalue -> rvalue -> list rvalue -> funcall

     (* polymorphic artihmetic binary operators *)

     | F_add : rvalue -> rvalue -> funcall
     | F_sub : rvalue -> rvalue -> funcall
     | F_mul : rvalue -> rvalue -> funcall
     | F_div : rvalue -> rvalue -> funcall

     (* polymorphic binary operators *)
     | F_geq : rvalue -> rvalue -> funcall

     (* polimorphic unary operators *)
     | F_neg: rvalue -> funcall
     | F_abs: rvalue -> funcall

     | F_vcvt_64f32f: rvalue -> rvalue -> funcall
     | F_addsub_4x32f: rvalue -> rvalue -> funcall
     | F_addsub_2x64f: rvalue -> rvalue -> funcall

     | F_vushuffle_2x64f: rvalue -> rvalue -> funcall

     | F_vshuffle_2x64f: rvalue -> rvalue -> rvalue -> funcall
     | F_vshuffle_4x32f: rvalue -> rvalue -> rvalue -> funcall
     | F_vshuffle_8x32f: rvalue -> rvalue -> rvalue -> funcall

     | F_vunpacklo_4x32f: rvalue -> rvalue -> funcall
     | F_vunpacklo_8x32f: rvalue -> rvalue -> funcall
     | F_vunpacklo_4x64f: rvalue -> rvalue -> funcall

     | F_vunpackhi_4x32f: rvalue -> rvalue -> funcall
     | F_vunpackhi_4x64f: rvalue -> rvalue -> funcall
     | F_vunpackhi_8x32f: rvalue -> rvalue -> funcall

     | F_cmpge_2x64f: rvalue -> rvalue -> funcall
     | F_testc_4x32i: rvalue -> rvalue -> funcall
     | F_testnzc_4x32i: rvalue -> rvalue -> funcall

     | F_vpermf128_4x64f: rvalue -> rvalue -> rvalue -> funcall
     | F_vpermf128_8x32f: rvalue -> rvalue -> rvalue -> funcall

     | F_vload_2l_4x32f: rvalue -> rvalue -> funcall
     | F_vload_2h_4x32f: rvalue -> rvalue -> funcall
     | F_vloadu_4x32f: rvalue -> funcall

     | F_vstore_2l_4x32f: rvalue -> rvalue -> funcall
     | F_vstore_2h_4x32f: rvalue -> rvalue -> funcall

     | F_vstoreu_4x32f: rvalue -> rvalue -> funcall.

Inductive lvalue :=
| VarLValue (var:varname)
| NthLvalue (l:lvalue) (index:rvalue)
| LDeref (r:rvalue)
| LCast (type:itype) (l:lvalue).


Inductive istmt :=
| IFunction (name: funcname) (type:itype) (param: list varname) (body:istmt)
| Skip
| Chain (body: list istmt)
| Data (var: varname) (values: list rvalue) (body:istmt)
| Assign (l:lvalue) (r:rvalue)
| Loop (var: varname) (from:Z) (to:Z) (body:istmt)
| If (cond:rvalue) (thenbranch:istmt) (elsebranch:istmt)
| FunCallStmt (f:funcall)
| Return (r:rvalue).

Inductive iprogram :=
| Program (bindings: varname -> option itype) (body:istmt). (* TODO: map? *)

