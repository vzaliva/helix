(* I-code AST *)

type itype =
  | Iunknown (* to be inferred later *)
  | Iint32
  | Ifloat

type ivar = Var of string*itype

type iexpr =
  | FunCall of string*(iexpr list)
  | FConst of float
  | IConst of int
  | Return of iexpr
  | Loop of ivar*int*int

type istmt =
  | Decl of (ivar list)*istmt
  | Chain of (istmt list)
  | Assign of ivar*iexpr

(* function definition: name, type, args, body *)
type i_function = Functoin of string*itype*(ivar list)*istmt

type i_program = Program of i_function list
