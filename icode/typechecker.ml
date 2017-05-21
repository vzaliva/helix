open Core

open Ast

exception Error of string

let rec collect_vars = function
  | Function (_, _, args, stmt) -> args @ collect_vars stmt
  | Decl (vars, astmt) -> vars @ collect_vars astmt
  | Chain stmts -> List.concat_map stmts collect_vars
  | Data (v, _, stmt) -> v :: (collect_vars stmt)
  | Loop (v, _, _, stmt) -> v :: (collect_vars stmt)
  | _ -> []

(*
      let iv =
        match v with
        | Var (n, t) -> (match t with
            | IntType | UnknownType -> Var (n, IntType)
            | _ -> raise (TypeError "Loop variable type mismatch. Must be int"))
        in
 *)
