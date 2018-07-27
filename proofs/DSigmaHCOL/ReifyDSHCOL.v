Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
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

Definition toDSHCOLType (tt: TemplateMonad term): TemplateMonad DSHCOLType :=
  t <- tt ;;
    match t with
    | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ =>
      tmReturn DSHnat
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

(* TODO: implement *)
Definition compileNatExpr (a_n:term): TemplateMonad DSHNatExpr := tmReturn tt.
Definition compileDSHIBinCarrierA (a_f:term): TemplateMonad DSHIBinCarrierA := tmReturn tt.
Definition compileDSHBinCarrierA (a_f:term): TemplateMonad DSHBinCarrierA := tmReturn tt.

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

Open Scope string_scope.
Fixpoint compileSHCOL (vars:varbindings) (t:term) {struct t}: TemplateMonad (varbindings*term*reifyResult) :=
  match t with
  | tLambda (nNamed n) vt b =>
    tmPrint ("lambda " ++ n)  ;;
    toDSHCOLType (tmReturn vt) ;; compileSHCOL ((nNamed n,vt)::vars) b
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.eUnion" _) (fm :: o :: b :: _ :: z :: nil) =>
    tmPrint "eUnion" ;;
            no <- tmUnquoteTyped nat o ;;
            zconst <- tmUnquoteTyped CarrierA z ;;
            bc <- compileNatExpr b ;;
            tmReturn (vars, fm, {| rei_i:=1; rei_o:=no; rei_op := @DSHeUnion no bc zconst |})
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.eT" _) (fm :: i :: b :: nil) =>
    tmPrint "eT" ;;
    ni <- tmUnquoteTyped nat i ;;
       bc <- compileNatExpr b ;;
       tmReturn (vars, fm,  {| rei_i:=ni; rei_o:=1; rei_op := @DSHeT ni bc |})
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHPointwise" _) (fm :: n :: f :: _ :: nil) =>
    tmPrint "SHPointwise" ;;
    nn <- tmUnquoteTyped nat n ;;
       df <- compileDSHIBinCarrierA f ;;
       tmReturn (vars, fm, {| rei_i:=nn; rei_o:=nn; rei_op := @DSHPointwise nn df |})
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHBinOp" _) (fm :: o :: f :: _ :: nil)
    =>
    tmPrint "SHBinOp" ;;
    no <- tmUnquoteTyped nat o ;;
       df <- compileDSHIBinCarrierA f ;;
       tmReturn (vars, fm, {| rei_i:=(no+no); rei_o:=no; rei_op := @DSHBinOp no df |})
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHInductor" _) (fm :: n :: f :: _ :: z :: nil) =>
    tmPrint "SHInductor" ;;
    zconst <- tmUnquoteTyped CarrierA z ;;
           nc <- compileNatExpr n ;;
           df <- compileDSHBinCarrierA f ;;
           tmReturn (vars, fm, {| rei_i:=1; rei_o:=1; rei_op := @DSHInductor nc df zconst |})
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.IUnion" _) (i :: o :: n :: f :: _ :: z :: op_family :: nil) =>
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
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.ISumUnion" _) (i :: o :: n :: op_family :: _) =>
    tmPrint "ISumUnion" ;;
    ni <- tmUnquoteTyped nat i ;;
       no <- tmUnquoteTyped nat o ;;
       nn <- tmUnquoteTyped nat n ;;
       fm <- tmQuote (Monoid_RthetaFlags) ;;
       c' <- compileSHCOL vars op_family ;;
       let '(_, _, rr) := (c':varbindings*term*reifyResult) in
       tmReturn (vars, fm, {| rei_i:=(rei_i rr); rei_o:=(rei_o rr); rei_op := @DSHISumUnion (rei_i rr) (rei_o rr) nn (rei_op rr) |})
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.IReduction" _) (i :: o :: n :: f :: _ :: z :: op_family :: nil) =>
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
  | tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.SHCompose" _) (fm :: i1 :: o2 :: o3 :: op1 :: op2 :: nil) =>
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
  | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.SafeCast" _) (i :: o :: c :: nil) =>
    tmPrint "SafeCast" ;;
    compileSHCOL vars c (* TODO: fm *)
  | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.UnSafeCast" _) (i :: o :: c :: nil) =>
    tmPrint "UnSafeCast" ;;
    compileSHCOL vars c (* TODO: fm *)
  | tApp (tConst "Helix.SigmaHCOL.TSigmaHCOL.HTSUMUnion" _) (fm :: i :: o :: dot :: _ :: op1 :: op2 :: nil) =>
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

  | _ as t => tmFail ("Usupported SHCOL syntax" ++ (Checker.string_of_term t))
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
         eexpr <- @tmEval hnf A expr  ;;
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
                                                        tmReturn {| rei_i := i;
                                                                    rei_o := o;
                                                                    rei_op := dshcol |}))
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
Qed.