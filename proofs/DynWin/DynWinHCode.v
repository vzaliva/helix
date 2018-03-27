Require Import Helix.HCode.Ast.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.

Require Import Helix.Util.StringOT.

Module Import VM := FMapList.Make(StringOT).
Module MP := WProperties_fun StringOT VM.
Module MF := MP.F.

Section Ast.

  Import ListNotations.
  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition DynWin_vars_map : (VM.t htype) := MP.of_list [
                                                   ("i3", IntType);
                                                     ("i5", IntType);
                                                     ("w2", BoolType);
                                                     ("w1", RealType);
                                                     ("s8", RealType);
                                                     ("s7", RealType);
                                                     ("s6", RealType);
                                                     ("s5", RealType);
                                                     ("s4", RealType);
                                                     ("s1", RealType);
                                                     ("q4", RealType);
                                                     ("q3", RealType);
                                                     ("D", PtrType RealType 16);
                                                     ("X", PtrType RealType 16)
                                                 ].

  Definition DynWin_var_resolver (name:varname) := VM.find name DynWin_vars_map.

  Definition DynWin_ast :=
    Program DynWin_var_resolver
            (FunctionDef "transform" IntType ["X"; "D"]
                         Skip
            ).
End Ast.
