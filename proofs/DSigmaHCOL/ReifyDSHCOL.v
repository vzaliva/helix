Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Basics.
Require Import Template.All.

Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.VecUtil.
Require Import Helix.HCOL.HCOL.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.canonical_names.


Import MonadNotation.
Require Import Coq.Lists.List. Import ListNotations.
Open Scope string_scope.

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

Fixpoint compileVExpr {n} (a_e:term): TemplateMonad (VExpr n):=
  match a_e with
  | tRel i => tmReturn (VVar i)
  (* TODO: more cases *)
  | _ => tmFail ("Unsupported VExpr" ++ (string_of_term a_e))
  end.

Fixpoint compileAExpr (a_e:term): TemplateMonad AExpr :=
  match a_e with
  | tApp (tConst "MathClasses.interfaces.canonical_names.abs" [])
         [tConst "Helix.HCOL.CarrierType.CarrierA" [];
            _; _; _;  _; _; a_a] =>
    d_a <- compileAExpr a_a ;;
        tmReturn (AAbs d_a)
  | tApp (tConst "Helix.HCOL.CarrierType.sub" []) [a_a ; a_b] =>
    d_a <- compileAExpr a_a ;;
        d_b <- compileAExpr a_b ;;
        tmReturn (AMinus d_a d_b)
  | tApp (tConst "Helix.HCOL.CarrierType.CarrierAmult" []) [a_a ; a_b] =>
    d_a <- compileAExpr a_a ;;
        d_b <- compileAExpr a_b ;;
        tmReturn (AMult d_a d_b)
  | tApp (tConst "CoLoR.Util.Vector.VecUtil.Vnth" [])
         [tConst "Helix.HCOL.CarrierType.CarrierA" [] ; a_n ; a_v ; a_i ; _] =>
    n <- tmUnquoteTyped nat a_n ;;
      d_v <- @compileVExpr n a_v ;;
      d_i <- compileNExpr a_i ;;
      tmReturn (@ANth n d_v d_i)
  | tRel i => tmReturn (AVar i)
  | _ => tmFail ("Unsupported AExpr" ++ (string_of_term a_e))
  end.

Definition compileDSHUnCarrierA (a_f:term): TemplateMonad DSHUnCarrierA :=
  match a_f with
  | tLambda _ _ a_f' => compileAExpr a_f'
  | _ => tmFail ("Unsupported UnCarrierA" ++ (string_of_term a_f))
  end.

Definition compileDSHIUnCarrierA (a_f:term): TemplateMonad DSHIUnCarrierA :=
  match a_f with
  | tLambda _ _ a_f' => compileDSHUnCarrierA a_f'
  | _ => tmFail ("Unsupported IUnCarrierA" ++ (string_of_term a_f))
  end.

Definition compileDSHBinCarrierA (a_f:term): TemplateMonad DSHBinCarrierA :=
  match a_f with
  | tApp (tConst "MathClasses.orders.minmax.max" [])
         [tConst "Helix.HCOL.CarrierType.CarrierA" []; _; _ ] =>
    tmReturn (AMax (AVar 1) (AVar 0))
  | tConst "Helix.HCOL.CarrierType.Zless" [] =>
    tmReturn (AZless (AVar 1) (AVar 0))
  | tConst "Helix.HCOL.CarrierType.CarrierAplus" [] =>
    tmReturn (APlus (AVar 1) (AVar 0))
  | tConst "Helix.HCOL.CarrierType.CarrierAmult" [] =>
    tmReturn (AMult (AVar 1) (AVar 0))
  | tLambda _ _ (tLambda _ _ a_f') => compileAExpr a_f'
  | tLambda _ _ a_f' => compileAExpr a_f'
  | _ => tmFail ("Unsupported BinCarrierA" ++ (string_of_term a_f))
  end.

Definition compileDSHIBinCarrierA (a_f:term): TemplateMonad DSHIBinCarrierA :=
  match a_f with
  | tLambda _ _ a_f' => compileDSHBinCarrierA a_f'
  | _ => tmFail ("Unsupported IBinCarrierA" ++ (string_of_term a_f))
  end.

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
              df <- compileDSHIUnCarrierA f ;;
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
              df <- compileDSHBinCarrierA f ;;
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
              df <- compileDSHBinCarrierA f ;;
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
              compileSHCOL vars c (* TODO: fm? *)
    | n_UnSafeCast, [i ; o ; c] =>
      tmPrint "UnSafeCast" ;;
              compileSHCOL vars c (* TODO: fm? *)
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

Fixpoint build_forall p conc :=
  match p with
  | [] => conc
  | (n,t)::ps => tProd n t (build_forall ps conc)
  end.

Fixpoint build_dsh_globals (g:varbindings) : TemplateMonad term :=
  match g with
  | [] => tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []])
  | (n,t)::gs =>
    dt <- toDSHCOLType (tmReturn t) ;;
       let i := length gs in
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

Fixpoint rev_nat_seq (len: nat) : list nat :=
  match len with
  | O => []
  | S len' => List.cons len' (rev_nat_seq len')
  end.

Fixpoint tmUnfoldList {A:Type} (names:list string) (e:A): TemplateMonad A :=
  match names with
  | [] => tmReturn e
  | x::xs =>  u <- @tmEval (unfold x) A e ;;
               tmUnfoldList xs u
  end.

(* Heterogenous relation of semantic equivalence of SHCOL and DSHCOL operators *)
Open Scope list_scope.
Definition SHCOL_DSHCOL_equiv {i o:nat} {fm} (σ: evalContext) (s: @SHOperator fm i o) (d: DSHOperator i o) : Prop
  := forall (Γ: evalContext) (x:svector fm i),
    (Some (densify fm (op fm s x))) = (evalDSHOperator (σ ++ Γ) d (densify fm x)).

Require Import Coq.Program.Basics. (* to unfold `const` *)
Definition reifySHCOL {A:Type} (expr: A) (lemma_name:string): TemplateMonad reifyResult :=
  a_expr <- @tmQuote A expr ;; eexpr0 <- @tmEval hnf A expr  ;;
         let unfold_names := ["SHFamilyOperatorCompose"; "IgnoreIndex"; "Fin1SwapIndex"; "Fin1SwapIndex2"; "IgnoreIndex2"; "mult_by_nth"; "plus"; "mult"; "const"] in
         eexpr <- tmUnfoldList unfold_names eexpr0 ;;
               ast <- @tmQuote A eexpr ;;
               d' <- compileSHCOL [] ast ;;
               match d' with
               | (globals, a_fm, {| rei_i:=i; rei_o:=o; rei_op:=dshcol |}) =>
                 a_i <- tmQuote i ;; a_o <- tmQuote o ;;
                     a_globals <- build_dsh_globals globals ;;
                     let global_idx := List.map tRel (rev_nat_seq (length globals)) in
                     (* dynwin_SHCOL1 a *)
                     let a_shcol := tApp a_expr global_idx in
                     dshcol' <- tmEval cbv dshcol ;; a_dshcol <- tmQuote dshcol' ;;
                             let lemma_concl :=
                                 (tApp (tConst "Top.SHCOL_DSHCOL_equiv" [])
                                       [a_i; a_o; a_fm; a_globals;
                                          a_shcol;
                                          a_dshcol])
                             in
                             let lemma_ast := build_forall globals lemma_concl in
                             (tmBind (tmUnquoteTyped Prop lemma_ast)
                                     (fun lemma_body => tmLemma lemma_name lemma_body
                                                             ;;
                                                             tmReturn {| rei_i := i;
                                                                         rei_o := o;
                                                                         rei_op := dshcol |}))
               end.


(* TODO: move *)
Global Instance evalDSHOperator_arg_proper
       {i o} (Γ: evalContext) (op: DSHOperator i o):
  Proper ((=) ==> (=)) (@evalDSHOperator i o Γ op).
Proof.
  intros x y E.
  induction op.
  -
    simpl.
    repeat break_match; auto.
    f_equiv.
    rewrite E.
    reflexivity.
  -
    simpl.
    repeat break_match; auto.
    f_equiv.
    rewrite E.
    reflexivity.
  -
    simpl.
    unfold evalDSHPointwise.
    apply vsequence_option_proper.
    f_equiv.
    intros j jc.
    unfold evalIUnCarrierA.
    apply evalAexp_proper.
    *
      unfold equiv, List_equiv.
      apply Forall2_cons.
      --
        unfold equiv, DSHVar_Equiv.
        simpl.
        constructor.
        apply Vnth_arg_equiv.
        apply E.
      --
        reflexivity.
    *
      reflexivity.
  -
    simpl.
    unfold evalDSHBinOp.
    break_let.
    break_let.
    apply vsequence_option_proper.
    f_equiv.
    intros j jc.
Admitted.

Lemma SHCompose_DSHCompose
      {i1 o2 o3} {fm}
      (σ: evalContext)
      (f: @SHOperator fm o2 o3)
      (g: @SHOperator fm i1 o2)
      (df: DSHOperator o2 o3)
      (dg: DSHOperator i1 o2)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    SHCOL_DSHCOL_equiv σ
                       (SHCompose fm f g)
                       (DSHCompose df dg).
Proof.
  intros Ef Eg.
  intros Γ x.
  simpl.
  break_match.
  -
    unfold compose.
    specialize (Eg Γ x).
    specialize (Ef Γ (op fm g x)).
    rewrite Ef.
    apply evalDSHOperator_arg_proper.
    apply Some_inj_equiv.
    rewrite <- Heqo.
    apply Eg.
  -
    specialize (Eg Γ x).
    rewrite Heqo in Eg.
    some_none_contradiction.
Qed.

Lemma SHCOL_DSHCOL_equiv_SafeCast
      {i o: nat}
      (Γ: evalContext)
      (s: @SHOperator Monoid_RthetaSafeFlags i o)
      (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv Γ s d ->
  SHCOL_DSHCOL_equiv Γ (TSigmaHCOL.SafeCast s) d.
Proof.
Admitted.

Lemma SHCOL_DSHCOL_equiv_UnSafeCast
      {i o: nat}
      (Γ: evalContext)
      (s: @SHOperator Monoid_RthetaFlags i o)
      (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv Γ s d ->
  SHCOL_DSHCOL_equiv Γ (TSigmaHCOL.UnSafeCast s) d.
Proof.
Admitted.

Lemma SHBinOp_DSHBinOp
      {o: nat}
      {fm}
      (Γ: evalContext)
      (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
      `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      (df: DSHIBinCarrierA)
  :
    (forall j a b, Some (f j a b) = evalIBinCarrierA
                                 Γ
                                 df (proj1_sig j) a b) ->
    @SHCOL_DSHCOL_equiv (o+o) o fm Γ
                        (@SHBinOp fm o f pF)
                        (DSHBinOp df).
Proof.
Admitted.

Lemma HTSUMUnion_DSHHTSUMUnion
      {i o: nat}
      {fm}
      (dot: CarrierA -> CarrierA -> CarrierA)
      `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
      (ddot: DSHBinCarrierA)
      (Γ: evalContext)
      (f g: @SHOperator fm i o)
      (df dg: DSHOperator i o)
  :
    SHCOL_DSHCOL_equiv Γ f df ->
    SHCOL_DSHCOL_equiv Γ g dg ->
    (forall a b, Some (dot a b) = evalBinCarrierA Γ ddot a b) ->
    SHCOL_DSHCOL_equiv Γ
                       (@HTSUMUnion fm i o dot dot_mor f g)
                       (DSHHTSUMUnion ddot df dg).
Proof.
Admitted.

Lemma eUnion_DSHeUnion
      {fm}
      (Γ: evalContext)
      {o b:nat}
      (bc: b < o)
      (z: CarrierA)
      (db: NExpr)
  :
    Some b = evalNexp Γ db ->
    SHCOL_DSHCOL_equiv Γ
                       (eUnion fm bc z)
                       (DSHeUnion db z).
Proof.
Admitted.

Definition SHOperatorFamily_DSHCOL_equiv {i o n:nat} {fm} (Γ: evalContext)
           (s: @SHOperatorFamily fm i o n)
           (d: DSHOperator i o) : Prop :=
  forall j, SHCOL_DSHCOL_equiv (DSHnatVar (proj1_sig j) :: Γ)
                          (s j)
                          d.

Lemma IReduction_DSHIReduction
      {i o n}
      (dot: CarrierA -> CarrierA -> CarrierA)
      `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
      (initial: CarrierA)
      (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
      (ddot: DSHBinCarrierA)
      (dop_family: DSHOperator i o)
      (Γ: evalContext)
  :
    (forall a b, Some (dot a b) = evalBinCarrierA Γ ddot a b) ->
    SHOperatorFamily_DSHCOL_equiv Γ op_family dop_family ->
    SHCOL_DSHCOL_equiv Γ
                       (@IReduction i o n dot pdot initial op_family)
                       (@DSHIReduction i o n ddot initial dop_family).
Proof.
Admitted.

Lemma SHPointwise_DSHPointwise
      {fm}
      {n: nat}
      (f: FinNat n -> CarrierA -> CarrierA)
      `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      (df: DSHIUnCarrierA)
      (Γ: evalContext)
  :
    (forall j a, Some (f j a) = evalIUnCarrierA Γ df (proj1_sig j) a) ->
           SHCOL_DSHCOL_equiv Γ
                              (@SHPointwise fm n f pF)
                              (DSHPointwise df).
Proof.
Admitted.

Lemma SHInductor_DSHInductor
      {fm}
      (n:nat)
      (f: CarrierA -> CarrierA -> CarrierA)
      `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      (initial: CarrierA)
      (dn:NExpr)
      (df: DSHBinCarrierA)
      (Γ: evalContext)
  :
    Some n = evalNexp Γ dn ->
    (forall a b, Some (f a b) = evalBinCarrierA Γ df a b) ->
    SHCOL_DSHCOL_equiv Γ
                       (@SHInductor fm n f pF initial)
                       (DSHInductor dn df initial).
Proof.
Admitted.

Lemma eT_DSHeT
      {fm}
      {i b:nat}
      (bc: b < i)
      (db:NExpr)
      (Γ: evalContext)
  :
    Some b = evalNexp Γ db ->
    SHCOL_DSHCOL_equiv Γ
                       (@eT fm i b bc)
                       (@DSHeT i (db:NExpr)).
Proof.
Admitted.

Lemma ISumUnion_DSHISumUnion
      {i o n}
      (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
      (dop_family: DSHOperator i o)
      (Γ: evalContext)
  :
    SHOperatorFamily_DSHCOL_equiv Γ op_family dop_family ->
    SHCOL_DSHCOL_equiv Γ
                       (@ISumUnion i o n op_family)
                       (@DSHISumUnion i o n dop_family).
Proof.
Admitted.

(* for testing *)
Require Import Helix.DynWin.DynWin.
Obligation Tactic := idtac.
Run TemplateProgram (reifySHCOL dynwin_SHCOL1 "dynwin_DSHCOL").
Next Obligation.
  intros a.
  unfold dynwin_SHCOL1.

  apply SHCompose_DSHCompose.
  apply SHCOL_DSHCOL_equiv_SafeCast.
  apply SHBinOp_DSHBinOp.
  reflexivity.
  apply HTSUMUnion_DSHHTSUMUnion.
  apply SHCompose_DSHCompose.
  apply eUnion_DSHeUnion.
  reflexivity.
  apply SHCOL_DSHCOL_equiv_SafeCast.
  apply IReduction_DSHIReduction.
  reflexivity.
  unfold SHOperatorFamily_DSHCOL_equiv.
  intros.
  apply SHCompose_DSHCompose.
  apply SHCompose_DSHCompose.
  apply SHPointwise_DSHPointwise.
  {
    intros.
    unfold Fin1SwapIndex, const, mult_by_nth.
    destruct j, j0.
    unfold evalIUnCarrierA.
    simpl.
    repeat break_match; crush.
    f_equiv.
    f_equiv.
    apply Vnth_eq. reflexivity.
  }
  apply SHInductor_DSHInductor.
  reflexivity.
  reflexivity.
  apply eT_DSHeT.
  reflexivity.
  apply SHCompose_DSHCompose.
  apply eUnion_DSHeUnion.
  reflexivity.
  apply SHCOL_DSHCOL_equiv_SafeCast.
  apply IReduction_DSHIReduction.
  reflexivity.
  unfold SHOperatorFamily_DSHCOL_equiv.
  intros.
  apply SHCompose_DSHCompose.
  apply SHBinOp_DSHBinOp.
  reflexivity.
  apply SHCOL_DSHCOL_equiv_UnSafeCast.
  apply ISumUnion_DSHISumUnion.
  unfold SHOperatorFamily_DSHCOL_equiv.
  intros.
  apply SHCompose_DSHCompose.
  apply eUnion_DSHeUnion.
  reflexivity.
  apply eT_DSHeT.
  reflexivity.
  reflexivity.
Qed.