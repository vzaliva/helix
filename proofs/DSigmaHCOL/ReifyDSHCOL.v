Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Template.All.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.

Import MonadNotation.
Require Import List. Import ListNotations.

Inductive DSHCOLType :=
| DSHnat : DSHCOLType
| DSHCarrierA : DSHCOLType
| DSHvec (n:nat): DSHCOLType.

Definition toDSHCOLType (tt: TemplateMonad term): TemplateMonad DSHCOLType :=
  t <- tt ;;
    match t with
    | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ =>
      tmReturn DSHnat
    | (tApp(tInd {| inductive_mind := "Coq.Init.Specif.sig"; inductive_ind := 0 |} _)
           [tInd
              {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ ; _])
      => tmReturn DSHnat (* `FinNat` is treated as `nat` *)
    | tConst "Helix.HCOL.CarrierType.CarrierA" _ => tmReturn DSHCarrierA
    | tApp
        (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} _)
        [tConst "Helix.HCOL.CarrierType.CarrierA" _ ; nat_term] =>
      n <- tmUnquoteTyped nat nat_term ;;
        tmReturn (DSHvec n)
    | _ => tmFail "non-DSHCOL type encountered"
    end.

Definition varbindings:Type := list (name*term).

Record reifyResult := {
                       rei_i: nat;
                       rei_o: nat;
                       rei_op: DSHOperator rei_i rei_o;
                     }.

Fixpoint compileNExpr (a_n:term): TemplateMonad NExpr :=
  match a_n with
  | (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 [])
    => tmReturn (NConst 0)
  | (tApp (tConst "Coq.Init.Specif.proj1_sig" []) [ _ ; _ ; tRel i])
    => tmReturn (NVar i)
  | (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 []) [e]) =>
    d_e <- compileNExpr e ;;
        tmReturn (match d_e with
                  | NConst v => NConst (v+1)
                  | o => NPlus o (NConst 1)
                  end)
  | (tApp (tConst "Coq.Init.Nat.add" []) [ a_a ; a_b]) =>
    d_a <- compileNExpr a_a ;;
        d_b <- compileNExpr a_b ;;
        tmReturn (NPlus d_a d_b)
  | (tApp (tConst "Coq.Init.Nat.mul" []) [ a_a ; a_b]) =>
    d_a <- compileNExpr a_a ;;
        d_b <- compileNExpr a_b ;;
        tmReturn (NMult d_a d_b)
  (* TODO: more cases *)
  | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
  end.

Definition compileAExpr (a_n:term): TemplateMonad AExpr := tmReturn (AConst CarrierAz).

Definition compileDSHIBinCarrierA (a_f:term): TemplateMonad DSHIBinCarrierA := compileAExpr a_f.
Definition compileDSHBinCarrierA (a_f:term): TemplateMonad DSHBinCarrierA := compileAExpr a_f.

Definition castReifyResult (i o:nat) (rr:reifyResult): TemplateMonad (DSHOperator i o) :=
  match rr with
  | {| rei_i := i'; rei_o := o'; rei_op := f' |} =>
    match PeanoNat.Nat.eq_dec i i', PeanoNat.Nat.eq_dec o o' with
    | left Ei, left Eo =>
      tmReturn
        (eq_rect_r (fun i0 : nat => DSHOperator i0 o)
                   (eq_rect_r (fun o0 : nat => DSHOperator i' o0) f' Eo) Ei)
    | _, _ => tmFail "castReifyResult failed"
    end
  end.

Inductive SHCOL_Op_Names :=
| n_eUnion
| n_eT
| n_SHPointwise
| n_SHBinOp
| n_SHInductor
| n_IUnion
| n_ISumUnion
| n_IReduction
| n_SHCompose
| n_SafeCast
| n_UnSafeCast
| n_HTSUMUnion
| n_Unsupported (n:string).

(* For fast string matching *)
Definition parse_SHCOL_Op_Name (s:string): SHCOL_Op_Names :=
  if string_dec s "Helix.SigmaHCOL.SigmaHCOL.eUnion" then n_eUnion
  else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.eT" then n_eT
       else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.SHPointwise" then n_SHPointwise
            else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.SHBinOp" then n_SHBinOp
                 else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.SHInductor" then n_SHInductor
                      else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.IUnion" then n_IUnion
                           else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.ISumUnion" then n_ISumUnion
                                else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.IReduction" then n_IReduction
                                     else if string_dec s "Helix.SigmaHCOL.SigmaHCOL.SHCompose" then n_SHCompose
                                          else if string_dec s "Helix.SigmaHCOL.TSigmaHCOL.SafeCast" then n_SafeCast
                                               else if string_dec s "Helix.SigmaHCOL.TSigmaHCOL.UnSafeCast" then n_UnSafeCast
                                                    else if string_dec s "Helix.SigmaHCOL.TSigmaHCOL.HTSUMUnion" then n_HTSUMUnion
                                                         else n_Unsupported s.


Open Scope string_scope.
Fixpoint compileSHCOL (vars:varbindings) (t:term) {struct t}: TemplateMonad (varbindings*term*reifyResult) :=
  match t with
  | tLambda (nNamed n) vt b =>
    tmPrint ("lambda " ++ n)  ;;
            toDSHCOLType (tmReturn vt) ;; compileSHCOL ((nNamed n,vt)::vars) b

  | tApp (tConst opname _) args =>
    match parse_SHCOL_Op_Name opname, args with
    | n_eUnion, [fm ; o ; b ; _ ; z] =>
      tmPrint "eUnion" ;;
              no <- tmUnquoteTyped nat o ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, fm, {| rei_i:=1; rei_o:=no; rei_op := @DSHeUnion no bc zconst |})
    | n_eT, [fm ; i ; b ; _] =>
      tmPrint "eT" ;;
              ni <- tmUnquoteTyped nat i ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, fm,  {| rei_i:=ni; rei_o:=1; rei_op := @DSHeT ni bc |})
    | n_SHPointwise, [fm ; n ; f ; _ ] =>
      tmPrint "SHPointwise" ;;
              nn <- tmUnquoteTyped nat n ;;
              df <- compileDSHIBinCarrierA f ;;
              tmReturn (vars, fm, {| rei_i:=nn; rei_o:=nn; rei_op := @DSHPointwise nn df |})
    | n_SHBinOp, [fm ; o ; f ; _]
      =>
      tmPrint "SHBinOp" ;;
              no <- tmUnquoteTyped nat o ;;
              df <- compileDSHIBinCarrierA f ;;
              tmReturn (vars, fm, {| rei_i:=(no+no); rei_o:=no; rei_op := @DSHBinOp no df |})
    | n_SHInductor, [fm ; n ; f ; _ ; z] =>
      tmPrint "SHInductor" ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              nc <- compileNExpr n ;;
              df <- compileDSHBinCarrierA f ;;
              tmReturn (vars, fm, {| rei_i:=1; rei_o:=1; rei_op := @DSHInductor nc df zconst |})
    | n_IUnion, [i ; o ; n ; f ; _ ; z ; op_family] =>
      tmPrint "IUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              fm <- tmQuote (Monoid_RthetaFlags) ;;
              df <- compileDSHIBinCarrierA f ;;
              c' <- compileSHCOL vars op_family ;;
              let '( _, _, rr) := (c':varbindings*term*reifyResult) in
              tmReturn (vars, fm, {| rei_i:=(rei_i rr); rei_o:=(rei_o rr); rei_op := @DSHIUnion (rei_i rr) (rei_o rr) nn df zconst (rei_op rr) |})
    | n_ISumUnion, [i ; o ; n ; op_family] =>
      tmPrint "ISumUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              fm <- tmQuote (Monoid_RthetaFlags) ;;
              c' <- compileSHCOL vars op_family ;;
              let '(_, _, rr) := (c':varbindings*term*reifyResult) in
              tmReturn (vars, fm, {| rei_i:=(rei_i rr); rei_o:=(rei_o rr); rei_op := @DSHISumUnion (rei_i rr) (rei_o rr) nn (rei_op rr) |})
    | n_IReduction, [i ; o ; n ; f ; _ ; z ; op_family] =>
      tmPrint "IReduction" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              fm <- tmQuote (Monoid_RthetaSafeFlags) ;;
              c' <- compileSHCOL vars op_family ;;
              df <- compileDSHIBinCarrierA f ;;
              let '(_, _, rr) := (c':varbindings*term*reifyResult) in
              tmReturn (vars, fm, {| rei_i:=(rei_i rr); rei_o:=(rei_o rr); rei_op := @DSHIReduction (rei_i rr) (rei_o rr) nn df zconst (rei_op rr) |})
    | n_SHCompose, [fm ; i1 ; o2 ; o3 ; op1 ; op2] =>
      tmPrint "SHCompose" ;;
              ni1 <- tmUnquoteTyped nat i1 ;;
              no2 <- tmUnquoteTyped nat o2 ;;
              no3 <- tmUnquoteTyped nat o3 ;;
              cop1' <- compileSHCOL vars op1 ;;
              cop2' <- compileSHCOL vars op2 ;;
              let '(_, _, cop1) := (cop1':varbindings*term*reifyResult) in
              let '(_, _, cop2) := (cop2':varbindings*term*reifyResult) in
              cop1 <- castReifyResult no2 no3 cop1 ;;
                   cop2 <- castReifyResult ni1 no2 cop2 ;;
                   tmReturn (vars, fm, {| rei_i:=ni1; rei_o:=no3; rei_op:=@DSHCompose ni1 no2 no3 cop1 cop2 |})
    | n_SafeCast, [i ; o ; c] =>
      tmPrint "SafeCast" ;;
              compileSHCOL vars c (* TODO: fm *)
    | n_UnSafeCast, [i ; o ; c] =>
      tmPrint "UnSafeCast" ;;
              compileSHCOL vars c (* TODO: fm *)
    | n_HTSUMUnion, [fm ; i ; o ; dot ; _ ; op1 ; op2] =>
      tmPrint "HTSumunion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              ddot <- compileDSHBinCarrierA dot ;;
              cop1' <- compileSHCOL vars op1 ;;
              cop2' <- compileSHCOL vars op2 ;;
              let '(_, _, cop1) := (cop1':varbindings*term*reifyResult) in
              let '(_, _, cop2) := (cop2':varbindings*term*reifyResult) in
              cop1 <- castReifyResult ni no cop1 ;;
                   cop2 <- castReifyResult ni no cop2 ;;
                   tmReturn (vars, fm, {| rei_i:=ni; rei_o:=no; rei_op:=@DSHHTSUMUnion ni no ddot cop1 cop2 |})

    | n_Unsupported u, _ =>
      tmFail ("Usupported SHCOL operator" ++ u)
    | _, _ =>
      tmFail ("Usupported arguments "
                ++ string_of_list string_of_term args
                ++ "for SHCOL operator" ++ opname)
    end
  | _ as t =>
    tmFail ("Usupported SHCOL syntax" ++ (Checker.string_of_term t))
  end.

Fixpoint build_forall g s:=
  match g with
  | [] => s
  | (n,t)::gs => tProd n t (build_forall gs s)
  end.

Fixpoint build_dsh_globals (g:varbindings) : TemplateMonad term :=
  match g with
  | [] => tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []])
  | (n,t)::gs =>
    dt <- toDSHCOLType (tmReturn t) ;;
       let i := length g in
       dv <- (match dt with
             | DSHnat => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 0 []) [tRel i])
             | DSHCarrierA => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 1 []) [tRel i])
             | DSHvec m =>
               a_m <- tmQuote m ;;
                   tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 2 []) [a_m; tRel i])
             end) ;;
          ts <- build_dsh_globals gs ;;
          tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []; dv; ts])
  end.

Fixpoint rev_nat_seq_to_1 (len: nat) : list nat :=
  match len with
  | O => []
  | S len' => List.cons len (rev_nat_seq_to_1 len')
  end.

Definition reifySHCOL {A:Type} (expr: A) (lemma_name:string): TemplateMonad reifyResult :=
  a_expr <- @tmQuote A expr ;;
         eexpr0 <- @tmEval hnf A expr  ;;
         eexpr <- @tmEval (unfold "SHFamilyOperatorCompose") A eexpr0 ;;
         ast <- @tmQuote A eexpr ;;
         d' <- compileSHCOL [] ast ;;
         match d' with
         | (globals, a_fm, {| rei_i:=i; rei_o:=o; rei_op:=dshcol |}) =>
           a_i <- tmQuote i ;;
               a_o <- tmQuote o ;;
               a_globals <- build_dsh_globals globals ;;
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
               dshcol' <- tmEval cbv dshcol ;;
                       a_dshcol <- tmQuote dshcol' ;;
                       let rhs := tApp (tConst "Helix.DSigmaHCOL.DSigmaHCOLEval.evalDSHOperator" [])
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
                                                       tmReturn {| rei_i := i;
                                                                   rei_o := o;
                                                                   rei_op := dshcol |}))
         end.

(* for testing *)
Require Import Helix.DynWin.DynWin.
(* Quote Definition dast := Eval hnf in dynwin_SHCOL1. *)

Obligation Tactic := idtac.
Run TemplateProgram (reifySHCOL dynwin_SHCOL1 "bar").
Next Obligation.
  intros a x.

Qed.