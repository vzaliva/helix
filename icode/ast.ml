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
  | Decl of (ivar list)*istmt
  | Chain of (istmt list)
  | Assign of lvalue*rvalue
  | Loop of ivar*int*int*istmt
  | Return of rvalue

(* function definition: name, type, args, body *)
type ifunction = Function of string*itype*(ivar list)*istmt

type iprogram = Program of ifunction list
