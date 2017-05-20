(* I-code AST *)

type itype =
  | RealType
  | IntType
  | BoolType
  | OtherType of string
  | UnknownType

type ivar = Var of string*itype

type rvalue =
  | FunCall of string*(rvalue list)
  | VarRValue of string
  | FConst of float
  | IConst of int
  | NthRvalue of rvalue*rvalue (* 'int' type for index will be checked later *)

type lvalue =
  | VarLValue of string
  | NthLvalue of lvalue*rvalue

type istmt =
  | Function of string*itype*(ivar list)*istmt
  | Skip
  | Decl of (ivar list)*istmt
  | Chain of (istmt list)
  | Data of ivar*(rvalue list)*istmt (* homogenity of rvalues to be checked later *)
  | Assign of lvalue*rvalue
  | Loop of ivar*rvalue*rvalue*istmt (* 'int' type for bounds, and a<=b will be checked later *)
  | Return of rvalue


type iprogram = Program of istmt list

open Format

let pr_itype ppf = function
  | RealType -> fprintf ppf "@[TReal@]"
  | IntType -> fprintf ppf "@[TInt@]"
  | BoolType -> fprintf ppf "@[TBool@]"
  | OtherType n -> fprintf ppf "@[%s@]" n
  | UnknownType -> fprintf ppf "@[?@]"

let pr_ivar ppf = function
  | Var (n,t) -> fprintf ppf "@[%s:%a@]" n pr_itype t
