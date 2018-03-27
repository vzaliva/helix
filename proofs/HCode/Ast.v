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
| FunCallValue (name: funcname) (params: list rvalue)
| VarRValue (name: varname)
| RConst (value: fconst)
| IConst (value: Z)
| IConstArr (values: list Z)
| RConstArr (values: list fconst)
| NthRvalue (r: rvalue) (index: rvalue)
| RCast (type: htype) (r: rvalue).

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
| Loop (var: varname) (from:Z) (to:Z) (body:hstmt)
| If (cond:rvalue) (thenbranch:hstmt) (elsebranch:hstmt)
| FunCallStmt (name: funcname) (params: list rvalue) (* call for side-effect *)
| Return (r:rvalue).

Inductive hprogram :=
| Program
    (var_bindings: varname -> option htype)
    (fun_bindings: funcname -> list htype -> option htype)
    (body:hstmt).
