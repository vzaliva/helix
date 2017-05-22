open Core

open Ast

exception Error of string

let rec collect_vars = function
  | Function (_, _, args, stmt) -> args @ collect_vars stmt
  | Decl (vars, astmt) -> vars @ collect_vars astmt
  | Chain stmts -> List.concat_map stmts collect_vars
  | Data (v, _, stmt) -> v :: (collect_vars stmt)
  | Loop (v, _, _, stmt) -> v :: (collect_vars stmt)
  | If (_, then_stmt, else_stmt) -> collect_vars then_stmt @ collect_vars else_stmt
  | _ -> []

let var_enforce_int = function
  | Var (n, t) -> (match t with
                   | IntType | UnknownType -> Var (n, IntType)
                   | _ -> raise (Error "Loop variable type mismatch. Must be int"))

let var_enforce_array d = function
  | Var (n, t) -> (match t with
                   | ArrayType (at,ado) ->
                      (match ado with
                      | None -> Var (n, ArrayType (at, Some d))
                      | Some ad -> if ad = d then
                                     Var (n, ArrayType (at, Some d))
                                   else
                                     raise (Error "Array size mismatch"))
                   | UnknownType -> Var (n, ArrayType (UnknownType, Some d))
                   | _ -> raise (Error "Loop variable type mismatch. Must be array"))

let rec fix_operator_types = function
  | Function (n, t, args, stmt) -> Function (n, t, args, fix_operator_types stmt)
  | Decl (vars, stmt) -> Decl (vars, fix_operator_types stmt)
  | Chain stmts ->  Chain (List.map stmts fix_operator_types)
  | Data (v, values, stmt) ->
     Data (
         var_enforce_array (List.length values) v,
         values,
         fix_operator_types stmt)
  | Loop (v, f, t, stmt) -> Loop (var_enforce_int v, f, t, fix_operator_types stmt)
  | If (rv, then_stmt, else_stmt) -> If (rv, fix_operator_types then_stmt, fix_operator_types else_stmt)
  | _ as x -> x
