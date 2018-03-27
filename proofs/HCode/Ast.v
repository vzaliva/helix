(* hCode AST *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Inductive htype :=
| RealType
| IntType
| VoidType
| BoolType
| ArrType (t:htype) (len:Z)
| PtrType (t:htype) (alignment:Z).

(* Types for function and vairable names. For simplicity we will index them by integers *)
Definition varname := Z.
Definition funcname := string.

Definition fconst := string.

Inductive rvalue :=
| FunCallValue (f:hbuiltin)
| VarRValue (var:varname)
| RConst (value:fconst)
| IConst (value:Z)
| IConstArr (values: list Z)
| RConstArr (values: list fconst)
| NthRvalue (r:rvalue) (index:rvalue)
| RCast (type:htype) (r:rvalue)
(* builtin functions *)
with hbuiltin :=
     (* polymorphic codnition operator *)
     | F_cond: rvalue -> rvalue -> rvalue -> hbuiltin

     (* polymorphic artihmetic n-nary (n >= 2) operators *)
     | F_min: rvalue -> rvalue -> list rvalue -> hbuiltin
     | F_max: rvalue -> rvalue -> list rvalue -> hbuiltin

     (* polymorphic artihmetic binary operators *)
     | F_add: rvalue -> rvalue -> hbuiltin
     | F_sub: rvalue -> rvalue -> hbuiltin
     | F_mul: rvalue -> rvalue -> hbuiltin
     | F_div: rvalue -> rvalue -> hbuiltin

     (* polymorphic binary operators *)
     | F_geq: rvalue -> rvalue -> hbuiltin

     (* polimorphic unary operators *)
     | F_neg: rvalue -> hbuiltin
     | F_abs: rvalue -> hbuiltin.

Inductive lvalue :=
| VarLValue (var:varname)
| NthLvalue (l:lvalue) (index:rvalue)
| LCast (type:htype) (l:lvalue).

Inductive hstmt :=
| FunctionDef (name: funcname) (type:htype) (param: list varname) (body:hstmt)
| Skip
| Chain (body: list hstmt)
| Decl (vars: list varname) (body:hstmt)
| Data (var: varname) (values: list rvalue) (body:hstmt)
| Assign (l:lvalue) (r:rvalue)
| Loop (var: varname) (from:Z) (to:Z) (body:hstmt)
| If (cond:rvalue) (thenbranch:hstmt) (elsebranch:hstmt)
| FunCallStmt (f:hbuiltin) (* call for side-effect *)
| Return (r:rvalue).

Inductive hprogram :=
| Program (bindings: varname -> option htype) (body:hstmt).
