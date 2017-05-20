open Core

open Ast

exception Error of string

let rec collect_types = function
  | Program istmts -> List.concat_map istmts collect_types_istmt
and collect_types_istmt = function
  | Function (_, rettype, args, astmt) ->
     rettype ::
       List.map args ivar_type @
       collect_types_istmt astmt
  | Skip -> []
  | Decl (vars, astmt) -> List.map ~f:ivar_type vars @
                            collect_types_istmt astmt
  | Chain stmts -> List.concat_map stmts collect_types_istmt
  | Data (v, vals, stmt) ->
     (ivar_type v) ::
       List.concat_map vals collect_types_rvalue @
       collect_types_istmt stmt
  | Assign (lv, rv) ->
              collect_types_lvalue lv @
                collect_types_rvalue rv
  | Loop (v, f, t, astmt) ->
     (ivar_type v) ::
       collect_types_rvalue f @
       collect_types_rvalue t @
         collect_types_istmt astmt
  | Return _ -> []
and ivar_type = function
  | Var (_, t) -> t
and collect_types_lvalue = function
  | VarLValue v -> [ivar_type v]
  | NthLvalue (l, r) -> collect_types_lvalue l @ collect_types_rvalue r
and collect_types_rvalue = function
  | FunCall (r, rl) -> List.concat_map rl collect_types_rvalue
  | VarRValue v -> [ivar_type v]
  | FConst _ -> []
  | IConst _ -> []
  | NthRvalue (v, i) -> collect_types_rvalue v @ collect_types_rvalue i
