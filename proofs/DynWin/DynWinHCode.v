Require Import Helix.HCode.Ast.

Require Import Coq.Lists.List.

Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.

Import ListNotations.
Open Scope Z_scope.

Module Import VM := FMapList.Make(Z_as_OT).
Module MP := WProperties_fun Z_as_OT VM.
Module MF := MP.F.

Section Ast.

  Definition i3:Z := 0.
  Definition i5:Z := 1.
  Definition w2:Z := 2.
  Definition w1:Z := 3.
  Definition s8:Z := 4.
  Definition s7:Z := 5.
  Definition s6:Z := 6.
  Definition s5:Z := 7.
  Definition s4:Z := 8.
  Definition s1:Z := 9.
  Definition q4:Z := 10.
  Definition q3:Z := 11.
  Definition D:Z  := 100.
  Definition X:Z  := 101.

  Definition DynWin_vars_map : (VM.t htype) := MP.of_list [
                                                   (i3, A IntType);
                                                   (i5, A IntType);
                                                   (w2, BoolType);
                                                   (w1, A RealType);
                                                   (s8, A RealType);
                                                   (s7, A RealType);
                                                   (s6, A RealType);
                                                   (s5, A RealType);
                                                   (s4, A RealType);
                                                   (s1, A RealType);
                                                   (q4, A RealType);
                                                   (q3, A RealType);
                                                   (D, PtrType (A RealType) 16);
                                                   (X, PtrType (A RealType) 16)
                                                 ].

  Definition DynWin_var_resolver (name:Z) := VM.find name DynWin_vars_map.

End Ast.
