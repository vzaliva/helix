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

Definition toDSHCOLType (tt: TemplateMonad term): TemplateMonad (option DSHCOLType) :=
  t <- tt ;;
    match t with
    | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ =>
      tmReturn (Some DSHnat)
    | tConst "Helix.HCOL.CarrierType.CarrierA" _ => tmReturn (Some DSHCarrierA)
    | tApp
        (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} _)
        [tConst "Helix.HCOL.CarrierType.CarrierA" _ ; nat_term] =>
      n <- tmUnquoteTyped nat nat_term ;;
        tmReturn (Some (DSHvec n))
    | _ => tmReturn None
    end.

Definition varbindings:Type := list (name*term).

Record reifyResult := {
                       rei_i: nat;
                       rei_o: nat;
                       rei_op: DSHOperator rei_i rei_o;
                     }.

(* TODO: implement *)
Definition compileNatExpr (a_n:term): option DSHNatExpr := Some tt.

Fixpoint compileSHCOL (tvars:TemplateMonad varbindings) (t:term) {struct t}: TemplateMonad (option (varbindings*term*term*term*reifyResult)) :=
  vars <- tvars ;;
       match t with
       | tLambda (nNamed n) vt b =>
         dt <- toDSHCOLType (tmReturn vt) ;;
            (match dt with
             | Some _ => compileSHCOL (tmReturn (((nNamed n,vt)::vars))) b
             | None =>  tmReturn None
             end)
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.eUnion" _) (fm :: o :: b :: _ :: z :: nil) =>
         one <- tmQuote (1%nat) ;;
             no <- tmUnquoteTyped nat o ;;
             zconst <- tmUnquoteTyped CarrierA z ;;
             tmReturn (match compileNatExpr b with
                       | Some bc => Some (vars, fm, one, o, {| rei_i:=1; rei_o:=no; rei_op := @DSHeUnion no bc zconst |})
                       | None => None
                       end)
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.eT"          _) (fm :: i :: b :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHPointwise" _) (fm :: n :: f :: _ :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHBinOp"     _) (fm :: o :: f :: _ :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHInductor"  _) (fm :: n :: f :: _ :: z :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.IUnion"      _) (i :: o :: n :: f :: _ :: z :: op_family :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.ISumUnion"   _) (i :: n :: op_family :: _) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.IReduction"  _) (i :: o :: n :: f :: _ :: z :: opfamily :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHCompose"   _) (fm :: i1 :: o2 :: o3 :: op1 :: op2 :: nil) =>
         i <- tmUnquoteTyped nat i1 ;;
           o <- tmUnquoteTyped nat o3 ;;
           tmReturn (Some (vars, fm, i1, o3, {| rei_i:=i; rei_o:=o; rei_op:=@DSHDummy i o |}))
       | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.SafeCast"   _) (i :: o :: f :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.UnSafeCast" _) (i :: o :: f :: nil) => tmReturn None
       | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.HTSUMUnion" _) (fm :: i :: o :: dot :: _ :: op1 :: op2 :: nil) => tmReturn None
       | _ => tmReturn None
       end.

Fixpoint build_forall g s:=
  match g with
  | [] => s
  | (n,t)::gs => tProd n t (build_forall gs s)
  end.

Fixpoint build_dsh_globals (u:TemplateMonad unit) (g:varbindings) : TemplateMonad (option term) :=
  _ <- u ;;
    match g with
    | [] => tmReturn (Some (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []]))
    | (n,t)::gs =>
      t' <- toDSHCOLType (tmReturn t) ;;
         match t' with
         | None => tmReturn None
         | Some dt =>
           let i := length g in
           dv <- (match dt with
                 | DSHnat => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 0 []) [tRel i])
                 | DSHCarrierA => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 1 []) [tRel i])
                 | DSHvec m =>
                   a_m <- tmQuote m ;;
                       tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 2 []) [a_m; tRel i])
                 end) ;;
              g' <- build_dsh_globals (tmReturn tt) gs ;;
              tmReturn (match g' with
                        | Some ts =>  Some (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []; dv; ts])
                        | None => None
                        end)
         end
    end.

Fixpoint rev_nat_seq_to_1 (len: nat) : list nat :=
  match len with
  | O => []
  | S len' => List.cons len (rev_nat_seq_to_1 len')
  end.

Definition reifySHCOL {A:Type} (expr: A) (lemma_name:string): TemplateMonad (option reifyResult) :=
  a_expr <- @tmQuote A expr ;;
         eexpr <- @tmEval hnf A expr  ;;
         ast <- @tmQuote A eexpr ;;
         d' <- compileSHCOL (tmReturn []) ast ;;
         match d' with
         | Some (globals, a_fm, a_i, a_o, {| rei_i:=i; rei_o:=o; rei_op:=dshcol |}) =>
           g' <- build_dsh_globals (tmReturn tt) globals ;;
              match g' with
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
         | None => tmReturn None
         end.

(*
Here is the lemma we are trying to build:

Definition fm: Monoid.Monoid RthetaFlags := Monoid_RthetaFlags.
Parameter dshcol : DSHOperator (1 + (2 + 2)) 1.
Definition lfoo := forall (a: avector 3),
    forall (x: svector fm (1 + (2 + 2))),
      option_Equiv
        (Some (densify fm (op fm (dynwin_SHCOL1 a) x)))
        (evalDSHOperator [] dshcol (densify fm x)).
 *)

Obligation Tactic := idtac.
Run TemplateProgram (reifySHCOL dynwin_SHCOL1 "bar").
Next Obligation.
  intros a x.
Admitted.

