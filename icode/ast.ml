(* I-code AST *)

type itype = string option

type ivar = Var of string*itype

type rvalue =
  | FunCall of string*(rvalue list)
  | VarRValue of ivar
  | FConst of float
  | IConst of int
  | NthRvalue of rvalue*rvalue (* 'int' type for index will be checked later *)

type lvalue =
  | VarLValue of ivar
  | NthLvalue of lvalue*rvalue

type istmt =
  | Function of string*itype*(ivar list)*istmt
  | Skip
  | Decl of (ivar list)*istmt
  | Chain of (istmt list)
  | Assign of lvalue*rvalue
  | Loop of ivar*rvalue*rvalue*istmt (* 'int' type for bounds, and a<=b will be checked later *)
  | Return of rvalue


type iprogram = Program of istmt list
