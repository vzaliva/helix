open Core

open Ast

exception Error of string

let rec collect_vars istmts =
  List.concat_map istmts collect_vars_istmt
and collect_vars_istmt = function
  | Function (_, _, args, stmt) -> args @ collect_vars_istmt stmt
  | Decl (vars, astmt) -> vars @ collect_vars_istmt astmt
  | Chain stmts -> List.concat_map stmts collect_vars_istmt
  | Data (v, _, stmt) -> v :: (collect_vars_istmt stmt)
  | Loop (v, _, _, stmt) -> v :: (collect_vars_istmt stmt)
  | _ -> []

