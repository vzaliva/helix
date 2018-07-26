Require Import Coq.Strings.String.
Require Import Template.All.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.

Import MonadNotation.
Require Import List. Import ListNotations.

(* for testing *)

Require Import Helix.DynWin.DynWin.
Quote Definition dast := Eval hnf in dynwin_SHCOL1.

Inductive DSHCOLType :=
| DSHnat : DSHCOLType
| DSHCarrierA : DSHCOLType
| DSHvec (n:nat): DSHCOLType.

Definition toDSHCOLType (t:term): option DSHCOLType :=
  match t with
  | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ => Some DSHnat
  | tConst "Helix.HCOL.CarrierType.CarrierA" _ => Some DSHCarrierA
  | tApp
      (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} _)
      [tConst "Helix.HCOL.CarrierType.CarrierA" _ ; nat_term] =>
    Some (DSHvec 3) (* TODO: unquoteTyped? *)
  | _ => None
  end.

Definition varbindings:Type := list (name*term).

Record reifyResult := {
                       rei_i: nat;
                       rei_o: nat;
                       rei_op: DSHOperator rei_i rei_o;
                     }.

Fixpoint SHCOL_to_DSHCol (vars:varbindings) (t:term): option (varbindings*term*term*term*reifyResult) :=
  match t with
  | tLambda (nNamed n) vt b =>
    (if toDSHCOLType vt then SHCOL_to_DSHCol ((nNamed n,vt)::vars) b
     else None)
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.eUnion"      _) (fm :: o :: b :: _ :: z :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.eT"          _) (fm :: i :: b :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHPointwise" _) (fm :: n :: f :: _ :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHBinOp"     _) (fm :: o :: f :: _ :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHInductor"  _) (fm :: n :: f :: _ :: z :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.IUnion"      _) (i :: o :: n :: f :: _ :: z :: op_family :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.ISumUnion"   _) (i :: n :: op_family :: _) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.IReduction"  _) (i :: o :: n :: f :: _ :: z :: opfamily :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHCompose"   _) (fm :: i1 :: o2 :: o3 :: op1 :: op2 :: nil) => Some (vars, fm, i1, o3, {| rei_i:=5; rei_o:=1; rei_op:=@DSHDummy 5 1 |})
  | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.SafeCast"   _) (i :: o :: f :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.UnSafeCast" _) (i :: o :: f :: nil) => None
  | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.HTSUMUnion" _) (fm :: i :: o :: dot :: _ :: op1 :: op2 :: nil) => None
  | _ => None
  end.

Fixpoint build_forall g s:=
  match g with
  | [] => s
  | (n,t)::gs => tProd n t (build_forall gs s)
  end.

Inductive collisionHandling := CollNorm | CollSafe.

Definition fm_select (t:term): option collisionHandling
  := match t with
     | tConst "Helix.SigmaHCOL.Rtheta.Monoid_RthetaFlags" []%list => Some CollNorm
     | tConst "Helix.SigmaHCOL.Rtheta.Monoid_RthetaSafeFlags" []%list => Some CollSafe
     | _ => None
     end.

Definition fm_unquote (t:term): option (Monoid.Monoid RthetaFlags) :=
  match fm_select t with
  | Some CollNorm => Some Monoid_RthetaFlags
  | Some CollSafe => Some Monoid_RthetaSafeFlags
  | None => None
  end.

Fixpoint quoteNat (n:nat) : term :=
  match n with
  | O => tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 []
  | S p => tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 []) [quoteNat p]
  end.

Fixpoint build_dsh_globals (g:varbindings) : option term :=
  match g with
  | [] => Some (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []])
  | (n,t)::gs =>
    match toDSHCOLType t with
    | None => None
    | Some dt =>
      let i := length g in
      let dv := (match dt with
                 | DSHnat => tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 0 []) [tRel i]
                 | DSHCarrierA => tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 1 []) [tRel i]
                 | DSHvec n => tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 2 [])
                                   [quoteNat n; tRel i]
                 end) in
      match build_dsh_globals gs with
      | Some ts =>  Some (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []; dv; ts])
      | None => None
      end
    end
  end.

(*

Definition fm: Monoid.Monoid RthetaFlags := Monoid_RthetaFlags.
Parameter dshcol : DSHOperator (1 + (2 + 2)) 1.
Definition lfoo := forall (a: avector 3),
    forall (x: svector fm (1 + (2 + 2))),
      option_Equiv
        (Some (densify fm (op fm (dynwin_SHCOL1 a) x)))
        (evalDSHOperator [] dshcol (densify fm x)).

Quote Definition l := Eval hnf in lfoo.
Print l.

Set Printing All. Print lfoo.

lfoo =
forall (a : t CarrierA (S (S (S O))))
  (x : svector fm (Nat.add (S O) (Nat.add (S (S O)) (S (S O))))),
@option_Equiv (t CarrierA (S O)) (@vec_Equiv CarrierA CarrierAe (S O))

  (@Some (t CarrierA (S O))
     (@densify fm (S O)
        (@op fm (Nat.add (S O) (Nat.add (S (S O)) (S (S O)))) (S O) (dynwin_SHCOL1 a) x)))

  (@evalDSHOperator (Nat.add (S O) (Nat.add (S (S O)) (S (S O))))
     (S O) (@Datatypes.nil DSHVar) dshcol
     (@densify fm (Nat.add (S O) (Nat.add (S (S O)) (S (S O)))) x))
     : Prop
 *)


Fixpoint rev_nat_seq_to_1 (len: nat) : list nat :=
  match len with
  | O => []
  | S len' => List.cons len (rev_nat_seq_to_1 len')
  end.

Definition reifySHCOL {A:Type} (expr: A) (lemma_name:string): TemplateMonad (option reifyResult) :=
  a_expr <- @tmQuote A expr ;;
         eexpr <- @tmEval hnf A expr  ;;
         ast <- @tmQuote A eexpr ;;
         match SHCOL_to_DSHCol [] ast with
         | Some (globals, a_fm, a_i, a_o, {| rei_i:=i; rei_o:=o; rei_op:=dshcol |}) =>
           match fm_unquote a_fm with
           | Some fm =>
             match build_dsh_globals globals with
             | Some a_globals =>
               x <- tmFreshName "x" ;;
                 let x_type := tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} []) [tApp (tConst "Helix.SigmaHCOL.Rtheta.Rtheta'" []) [a_fm]; a_i] in
                 let global_idx := List.map tRel (rev_nat_seq_to_1 (length globals)) in
                 (* Some (densify fm (op fm (dynwin_SHCOL1 a) x)) *)
                 let lhs := tApp
                              (tConstruct {| inductive_mind := "Coq.Init.Datatypes.option"; inductive_ind := 0 |} 0 [])
                              [tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} [])
                                    [tConst "Helix.HCOL.CarrierType.CarrierA" []; a_o];
                                 tApp (tConst "Helix.SigmaHCOL.SVector.densify" [])
                                      [a_fm; a_o;
                                         tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.op" [])
                                              [a_fm;
                                                 a_i;
                                                 a_o;
                                                 tApp a_expr global_idx;
                                                 tRel 0]]] in
                 (* evalDSHOperator [] dshcol (densify fm x) *)
                 a_dshcol <- tmQuote dshcol ;;

                          let rhs := tApp (tConst "Helix.DSigmaHCOL.DSigmaHCOL.evalDSHOperator" [])
                                          [a_i; a_o; a_globals ; a_dshcol;
                                             (tApp (tConst "Helix.SigmaHCOL.SVector.densify" [])
                                                   [a_fm; a_i; tRel 0])
                                          ] in
                          let lemma_concl :=
                              tProd (nNamed x) x_type
                                    (tApp (tConst "Helix.Util.OptionSetoid.option_Equiv" [])
                                          [
                                            (tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} []) [tConst "Helix.HCOL.CarrierType.CarrierA" []; a_o]);
                                              (tApp (tConst "Helix.Util.VecSetoid.vec_Equiv" [])
                                                    [tConst "Helix.HCOL.CarrierType.CarrierA" [];
                                                       tConst "Helix.HCOL.CarrierType.CarrierAe" [];
                                                       a_o]);
                                              lhs;
                                              rhs
                                    ]) in
                          let lemma_ast := build_forall globals lemma_concl in

                          (tmBind (tmUnquoteTyped Prop lemma_ast)
                                  (fun lemma_body => tmLemma lemma_name lemma_body
                                                          ;;
                                                          tmReturn (Some {| rei_i := i;
                                                                            rei_o := o;
                                                                            rei_op := dshcol |})))
             | _ => tmReturn None
             end
           | _ => tmReturn None
           end
         | None => tmReturn None
         end.

Obligation Tactic := idtac.
Run TemplateProgram (reifySHCOL dynwin_SHCOL1 "bar").
