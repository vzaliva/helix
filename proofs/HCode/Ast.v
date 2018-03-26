(* iCode AST *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Import ListNotations.

Open Scope list_scope.

Inductive arithtype :=
| RealType
| IntType.

Inductive itype :=
| A (value:arithtype)
| VoidType
| ArrType (t:itype) (len:Z)
| PtrType (t:itype) (alignment:Z).

(* Types for function and vairable names. For simplicity we will index them by integers *)
Definition varname := Z.
Definition funcname := string.

Definition fconst := string.

Inductive rvalue :=
| FunCallValue (f:funcall)
| VarRValue (var:varname)
| RConst (value:fconst)
| IConst (value:Z)
| IConstArr (values: list Z)
| RConstArr (values: list fconst)
| NthRvalue (r:rvalue) (index:rvalue)
| RCast (type:itype) (r:rvalue)
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
     | F_abs: rvalue -> funcall.

Inductive lvalue :=
| VarLValue (var:varname)
| NthLvalue (l:lvalue) (index:rvalue)
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

