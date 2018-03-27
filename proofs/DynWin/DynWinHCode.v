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
            (fun _ _ => None)
            (FunctionDef
               "transform" IntType ["X"; "D"]
               (Decl [ "q3"; "q4"; "s1"; "s4"; "s5"; "s6"; "s7"; "s8"; "w1"; "w2" ]
                     (Chain [
                          Assign (VarLValue "s5") (RConst "0.0");
                            Assign (VarLValue "s8")
                                   (NthRvalue (VarRValue "X") (IConst 0));
                            (Loop "i5" (IConst 0) (IConst 2)
                                  (Chain [
                                       Assign (VarLValue "s4")
                                              (FunCallValue "mul" [VarRValue "s7" ; NthRvalue (VarRValue "D") (VarRValue "i5")]);
                                         Assign (VarLValue "s5")
                                                (FunCallValue "add" [VarRValue "s5" ; VarRValue "s4"]);
                                         Assign (VarLValue "s7")
                                                (FunCallValue "mul" [VarRValue "s7" ; VarRValue "s8"])
                            ]));
                            Assign (VarLValue "s1") (RConst "0.0");
                            (Loop "i3" (IConst 0) (IConst 1)
                                  (Chain [
                                       Assign (VarLValue "q3")
                                              (NthRvalue (VarRValue "X")
                                                         (FunCallValue "add" [VarRValue "i3" ; IConst 1]));
                                         Assign (VarLValue "q4")
                                                (NthRvalue (VarRValue "X")
                                                           (FunCallValue "add" [IConst 3; VarRValue "i3"]));
                                         Assign (VarLValue "w1")
                                                (FunCallValue "sub" [VarRValue "q3"; VarRValue "q4"]);
                                         Assign (VarLValue "s6")
                                                (FunCallValue "cond" [
                                                                FunCallValue "geq" [VarRValue "w1"; IConst 0]; VarRValue "w1"; FunCallValue "neg" [VarRValue "w1"]]);
                                         Assign (VarLValue "s1")
                                                (FunCallValue "cond" [
                                                                FunCallValue "geq" [VarRValue "s1"; VarRValue "s6"]; VarRValue "s1"; VarRValue "s6"])
                            ]));
                            Assign (VarLValue "w2") (FunCallValue "geq" [VarRValue "s1"; VarRValue "s5"]);
                            Return (VarRValue "w2")
                     ])
               )
            ).
End Ast.
