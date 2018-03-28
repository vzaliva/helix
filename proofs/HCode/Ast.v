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

Definition varname  := string.
Definition funcname := string.

(* FP/Real constant *)
Definition fconst   := string.

Inductive rvalue :=
| FunCallValue (f:builtin)
| VarRValue (name: varname)
| RConst (value: fconst)
| IConst (value: Z)
| IConstArr (values: list Z)
| RConstArr (values: list fconst)
| NthRvalue (r: rvalue) (index: rvalue)
| RCast (type: htype) (r: rvalue)
with builtin :=
     (* polymorphic codnition operator *)
     | F_cond: rvalue -> rvalue -> rvalue -> builtin

     (* polymorphic artihmetic n-nary (n >= 2) operators *)
     | F_min: rvalue -> rvalue -> list rvalue -> builtin
     | F_max: rvalue -> rvalue -> list rvalue -> builtin

     (* polymorphic artihmetic binary operators *)
     | F_add: rvalue -> rvalue -> builtin
     | F_sub: rvalue -> rvalue -> builtin
     | F_mul: rvalue -> rvalue -> builtin
     | F_div: rvalue -> rvalue -> builtin

     (* polymorphic binary operators *)
     | F_geq: rvalue -> rvalue -> builtin

     (* polimorphic unary operators *)
     | F_neg: rvalue -> builtin.

Inductive lvalue :=
| VarLValue (var:varname)
| NthLvalue (l:lvalue) (index:rvalue)
| LCast (type:htype) (l:lvalue).

Inductive hstmt :=
| FunctionDef (name: funcname) (rettype:htype) (param: list varname) (body:hstmt)
| Skip
| Chain (body: list hstmt)
| Decl (vars: list varname) (body:hstmt)
| Data (var: varname) (values: list rvalue) (body:hstmt)
| Assign (l:lvalue) (r:rvalue)
| Loop (var: varname) (from: rvalue) (to: rvalue) (body:hstmt)
| If (cond:rvalue) (thenbranch:hstmt) (elsebranch:hstmt)
| Return (r:rvalue).

Inductive hprogram :=
| Program
    (var_bindings: varname -> option htype)
    (body:hstmt).
