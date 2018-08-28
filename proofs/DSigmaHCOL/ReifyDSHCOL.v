Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Basics.
Require Import Template.All.

Require Import Helix.Util.Misc.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.VecUtil.
Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.WriterMonadNoT.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.

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
                                 (tApp (tConst "SHCOL_DSHCOL_equiv" [])
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

Theorem SHCompose_DSHCompose
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

Theorem SHCOL_DSHCOL_equiv_SafeCast
        {i o: nat}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaSafeFlags i o)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.SafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rvector2rsvector _ x)).
  rewrite densify_rvector2rsvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHCOL_DSHCOL_equiv_UnSafeCast
        {i o: nat}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaFlags i o)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.UnSafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rsvector2rvector _ x)).
  rewrite densify_rsvector2rvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHBinOp_DSHBinOp
        {o: nat}
        {fm}
        (σ: evalContext)
        (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (df: DSHIBinCarrierA)
  :
    (forall (Γ: evalContext) j a b, Some (f j a b) = evalIBinCarrierA
                                                       (σ ++ Γ)
                                                       df (proj1_sig j) a b) ->
    @SHCOL_DSHCOL_equiv (o+o) o fm σ
                        (@SHBinOp fm o f pF)
                        (DSHBinOp df).
Proof.
  intros H.
  intros Γ x.
  simpl.
  unfold evalDSHBinOp.
  unfold SHBinOp'.
  break_let.
  rename t into x0, t0 into x1.

  unfold densify.
  rewrite Vmap_Vbuild.

  break_let.
  unfold vector2pair in *.

  apply Vbreak_arg_app in Heqp.
  subst x.
  rewrite Vmap_app in Heqp0.
  apply Vbreak_arg_app in Heqp0.
  apply Vapp_eq in Heqp0.
  destruct Heqp0 as [H0 H1].
  subst t. subst t0.
  setoid_rewrite Vnth_map.

  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  rewrite Vmap_Vbuild with (fm:=Some).

  vec_index_equiv j jc.
  rewrite 2!Vbuild_nth.
  rewrite evalWriter_Rtheta_liftM2.
  symmetry.
  specialize (H Γ (mkFinNat jc)).
  rewrite H.
  reflexivity.
Qed.

Theorem HTSUMUnion_DSHHTSUMUnion
        {i o: nat}
        {fm}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
        (ddot: DSHBinCarrierA)
        (σ: evalContext)
        (f g: @SHOperator fm i o)
        (df dg: DSHOperator i o)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    (forall (Γ:evalContext) a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@HTSUMUnion fm i o dot dot_mor f g)
                       (DSHHTSUMUnion ddot df dg).
Proof.
  intros Ef Eg Edot.
  intros Γ x.
  specialize (Ef Γ).
  specialize (Eg Γ).
  specialize (Edot Γ).
  simpl.
  repeat break_match.
  -
    rewrite Vmap2_as_Vbuild.
    symmetry.
    apply vsequence_Vbuild_equiv_Some.
    unfold HTSUMUnion', Vec2Union.
    unfold densify.
    rewrite Vmap_map.
    rewrite Vmap2_as_Vbuild.
    rewrite Vmap_Vbuild.
    unfold Union.

    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    rewrite evalWriter_Rtheta_liftM2.
    symmetry.

    specialize (Ef x). specialize (Eg x).
    rewrite Heqo0 in Ef; clear Heqo0; some_inv.
    rewrite Heqo1 in Eg; clear Heqo1; some_inv.
    rewrite Edot; clear Edot.
    apply evalBinCarrierA_proper; try reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Ef.
    rewrite <- Ef.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Eg.
    rewrite <- Eg.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.
  -
    specialize (Eg x).
    rewrite Heqo1 in Eg.
    some_none_contradiction.
  -
    specialize (Ef x).
    rewrite Heqo0 in Ef.
    some_none_contradiction.
Qed.

Theorem eUnion_DSHeUnion
        {fm}
        (σ: evalContext)
        {o b:nat}
        (bc: b < o)
        (z: CarrierA)
        (db: NExpr)
  :
    (forall Γ, Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ
                       (eUnion fm bc z)
                       (DSHeUnion db z).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none_contradiction.
  break_match; some_inv; repeat nat_equiv_to_eq; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.

    apply castWriter_equiv.
    unfold eUnion'.
    repeat rewrite Vbuild_nth.
    break_if.
    +
      subst.
      rewrite Vhead_Vmap.
      apply castWriter_mkValue_evalWriter.
    +
      apply castWriter_mkStruct.
  -
    destruct n0; auto.
Qed.

Definition SHOperatorFamily_DSHCOL_equiv {i o n:nat} {fm} (Γ: evalContext)
           (s: @SHOperatorFamily fm i o n)
           (d: DSHOperator i o) : Prop :=
  forall j, SHCOL_DSHCOL_equiv (DSHnatVar (proj1_sig j) :: Γ)
                          (s j)
                          d.

(* TODO: move *)
Definition isNth {A:Type} `{Equiv A} (l:list A) (n:nat) (v:A) : Prop :=
  match nth_error l n with
  | None => False
  | Some x => x = v
  end.

(* TODO: move *)
Lemma isNth_Sn {A:Type} `{Equiv A} (h:A) (l:list A) (n:nat) (v:A):
  isNth (h :: l) (S n) v ≡ isNth l n v.
Proof.
  crush.
Qed.

Definition listsDiffByOneElement {A:Type} `{Ae:Equiv A} (l0 l1:list A) (n:nat) : Prop :=
  forall i, i≢n -> nth_error l0 i = nth_error l1 i.

Lemma listsDiffByOneElement_Sn {A:Type} `{Ae:Equiv A} {Aeq: Equivalence Ae} (h0 h1:A) (l0 l1:list A) (n:nat):
  h0 = h1 ->
  listsDiffByOneElement l0 l1 n ->
  listsDiffByOneElement (h0::l0) (h1::l1) (S n).
Proof.
  intros E H.
  unfold listsDiffByOneElement in *.
  intros i ic.
  destruct i.
  -
    simpl.
    some_apply.
  -
    simpl.
    apply H.
    crush.
Qed.

Section Expr_NVar_subst_S.

  Local Ltac twoarg := simpl;
                       repeat break_match; auto; try some_none_contradiction;
                       f_equiv;
                       repeat some_inv;
                       crush.

  Fact NExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : NExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVar j) ->
    isNth Γs pos (DSHnatVar (S j)) ->
    evalNexp Γs exp =
    evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      break_if.
      +
        (* accessing variable at pos *)
        subst n.
        simpl.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity; try some_none_contradiction.
        *
          some_inv.
          inversion H0. inversion H1. subst.
          f_equiv.
          repeat nat_equiv_to_eq; subst.
          apply peano_naturals.S_nat_plus_1.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

  Fact VExpr_NVar_subst_S
       {d: nat}
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : VExpr d)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVar j) ->
    isNth Γs pos (DSHnatVar (S j)) ->
    evalVexp Γs exp =
    evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n0 pos).
      +
        (* accessing variable at pos *)
        subst n0.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H0.
        * inversion H0.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n0 n1).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        repeat break_match; try reflexivity.
        subst.
        symmetry.
        compute.
        f_equiv.
        apply H3.
    -
      reflexivity.
  Qed.

  Fact AExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : AExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVar j) ->
    isNth Γs pos (DSHnatVar (S j)) ->
    evalAexp Γs exp =
    evalAexp Γ (AExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n pos).
      +
        (* accessing variable at pos *)
        subst n.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0. subst. inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    -
      rename n0 into ne.
      simpl.
      assert(V:evalVexp Γs v = evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) v)) by (apply VExpr_NVar_subst_S with (j0:=j); auto).
      unfold listsDiffByOneElement, isNth in *.
      assert (C: evalNexp Γs ne = evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) ne)) by (apply NExpr_NVar_subst_S with (j:=j); auto).
      twoarg.
      repeat nat_equiv_to_eq.
      subst.
      replace l0 with l by apply proof_irrelevance; clear l0.
      apply Vnth_proper, V.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

End Expr_NVar_subst_S.

Fact DSHOperator_NVar_subst_S
     {i o : nat}
     (Γ Γs : evalContext)
     (dop_family : DSHOperator i o)
     (pos:nat)
     (y : vector CarrierA i)
     (j : nat):
  listsDiffByOneElement Γ Γs pos ->
  isNth Γ pos (DSHnatVar j) ->
  isNth Γs pos (DSHnatVar (S j)) ->
  evalDSHOperator Γs dop_family y =
  evalDSHOperator Γ
                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family) y.
Proof.
  revert Γ Γs.
  revert pos.
  induction dop_family; intros pos Γ Γs L L0 L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none_contradiction; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    reflexivity.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none_contradiction; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    replace l0 with l by apply proof_irrelevance.
    reflexivity.
  -
    simpl.
    unfold evalDSHPointwise, evalIUnCarrierA.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros t tc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    unfold evalDSHBinOp, evalIBinCarrierA.
    break_let.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros m mc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+3)%nat with (S (S (S pos))).
    2:{
      rewrite <- 3!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos n j) as Hn.
    specialize (Hn L L0 L1).

    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      destruct a ; destruct b
    end; try some_none_contradiction; try reflexivity.


    some_inv.
    nat_equiv_to_eq.
    subst n0.
    generalize (Vhead y); intros y'; clear y; rename y' into y.

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b)
    end.
    {
      induction n1.
      * reflexivity.
      *
        rewrite 2!evalDSHInductor_Sn.
        Opaque evalDSHInductor. simpl.
        repeat break_match; try reflexivity.
        unfold evalBinCarrierA.
        apply AExpr_NVar_subst_S with (j:=j).
        Transparent evalDSHInductor.
        --
          some_inv.
          apply listsDiffByOneElement_Sn; try reflexivity.
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply IHn1).
          apply L.
        -- apply L0.
        -- apply L1.
        -- some_none_contradiction.
        -- some_none_contradiction.
    }

    repeat break_match; try some_none_contradiction; try reflexivity.
    f_equiv.
    f_equiv.
    some_inv.
    apply C.
  -
    simpl.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }

    assert(D: evalBinCarrierA Γs dot =
              evalBinCarrierA Γ
                              (AExpr_natvar_subst (S (S pos))
                                                  (NPlus (NVar (S (S pos)))
                                                         (NConst 1)) dot)).
    {
      unfold evalBinCarrierA.
      intros a a' Ea b b' Eb.
      apply AExpr_NVar_subst_S with (j:=j).
      apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
      apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
      apply L.
      -- apply L0.
      -- apply L1.
    }

    induction n.
    + reflexivity.
    +
      unfold evalDiamond in *.
      rewrite 2!Vbuild_cons.
      rewrite 2!Vfold_left_rev_cons.
      apply optDot_proper.
      *
        apply D.
      *
        eapply Vfold_left_rev_proper.
        --
          apply optDot_proper.
          unfold evalBinCarrierA.
          intros a a' Ea b b' Eb.

          apply AExpr_NVar_subst_S with (j:=j).
          ++
            apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
            apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
            apply L.
          ++ apply L0.
          ++ apply L1.
        --
          reflexivity.
        --
          vec_index_equiv j jc.
          rewrite 2!Vbuild_nth.
          apply IHdop_family.
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
          apply L.
          apply L0.
          apply L1.
      *
        apply IHdop_family.
        apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
        apply L.
        apply L0.
        apply L1.
  -
    HERE ^^^

Admitted.


Theorem IReduction_DSHIReduction
        {i o n}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        (initial: CarrierA)
        (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
        (ddot: DSHBinCarrierA)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    (forall Γ a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@IReduction i o n dot pdot initial op_family)
                       (@DSHIReduction i o n ddot initial dop_family).
Proof.
  intros Hdot Hfam Γ x.
  simpl.
  unfold Diamond', MUnion', Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaSafeFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn dot pdot Hdot ddot x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaSafeFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaSafeFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVar 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaSafeFlags)) x))
      with
        (Some
           (densify Monoid_RthetaSafeFlags
                    (op Monoid_RthetaSafeFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    setoid_rewrite <- Hdot.
    clear ddot Hdot Γ σ.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply pdot.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

Theorem SHPointwise_DSHPointwise
        {fm}
        {n: nat}
        (f: FinNat n -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (df: DSHIUnCarrierA)
        (σ: evalContext)
  :
    (forall Γ j a, Some (f j a) = evalIUnCarrierA (σ++Γ) df (proj1_sig j) a) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHPointwise fm n f pF)
                       (DSHPointwise df).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  unfold evalDSHPointwise.
  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  unfold densify.
  rewrite Vmap_map.
  simpl.
  unfold SHPointwise'.
  rewrite Vmap_Vbuild.
  apply Vbuild_proper.
  intros j jc.
  rewrite Vnth_map.
  rewrite evalWriter_Rtheta_liftM.
  specialize (H (mkFinNat jc)).
  rewrite <- H.
  reflexivity.
Qed.

Lemma evalDSHInductor_not_None
      (n : nat)
      (initial : CarrierA)
      (df : DSHBinCarrierA)
      (σ Γ : evalContext)
      (Edot: forall a b : CarrierA, is_Some (evalBinCarrierA (σ ++ Γ) df a b)) :
  forall x : CarrierA, is_Some (evalDSHInductor (σ ++ Γ) n df initial x).
Proof.
  intros x.
  induction n.
  -
    crush.
  -
    simpl.
    break_match; crush.
Qed.

Theorem SHInductor_DSHInductor
        {fm}
        (n:nat)
        (f: CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (initial: CarrierA)
        (dn:NExpr)
        (df: DSHBinCarrierA)
        (σ: evalContext)
  :
    (forall Γ, Some n = evalNexp (σ++Γ) dn) ->
    (forall  Γ a b, Some (f a b) = evalBinCarrierA (σ++Γ) df a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHInductor fm n f pF initial)
                       (DSHInductor dn df initial).
Proof.
  intros E Edot.
  intros Γ x.
  specialize (E Γ).
  specialize (Edot Γ).
  simpl evalDSHOperator.
  break_match; try some_none_contradiction.
  apply Some_inj_equiv in E.
  unfold equiv, peano_naturals.nat_equiv in E.
  subst n0.

  simpl op.
  unfold SHInductor', Lst, Vconst, densify.
  rewrite Vmap_cons.
  rewrite evalWriter_Rtheta_liftM.
  simpl.
  dep_destruct x.
  simpl.
  clear x0 x.
  generalize (WriterMonadNoT.evalWriter h). intros x. clear h.

  break_match.
  -
    f_equiv.
    apply Vcons_proper; try reflexivity.
    clear dn Heqo.
    dependent induction n.
    +
      crush.
    +
      simpl.
      specialize (IHn f pF initial df σ Γ Edot).
      simpl in Heqo0.
      break_match.
      *
        rewrite IHn with (x:=x) (c:=c0).
        specialize (Edot c0 x).
        rewrite Heqo0 in Edot.
        some_inv; auto.
        auto.
      *
        some_none_contradiction.
  -
    contradict Heqo0.
    apply is_Some_ne_None.
    apply evalDSHInductor_not_None.
    intros a b.
    specialize (Edot a b).
    symmetry in Edot.
    apply equiv_Some_is_Some in Edot.
    apply Edot.
Qed.

Theorem eT_DSHeT
        {fm}
        {i b:nat}
        (bc: b < i)
        (db: NExpr)
        (σ: evalContext)
  :
    (forall (Γ:evalContext), Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ
                       (@eT fm i b bc)
                       (@DSHeT i (db:NExpr)).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none_contradiction.
  break_match; some_inv; unfold equiv, peano_naturals.nat_equiv in H; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.
    dep_destruct jc;try inversion x0.
    rewrite Vnth_cons.
    break_match. inversion l0.
    apply castWriter_equiv.
    simpl.
    rewrite Vnth_map.
    replace l with bc by apply proof_irrelevance.
    apply castWriter_mkValue_evalWriter.
  -
    destruct n0; auto.
Qed.

Theorem ISumUnion_DSHISumUnion
        {i o n}
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@ISumUnion i o n op_family)
                       (@DSHISumUnion i o n dop_family).
Proof.
  (* significant code duplication with `IReduction_DSHIReduction` *)
  intros Hfam Γ x.

  induction n.
  -
    simpl.
    f_equiv.
    unfold Diamond', MUnion', Apply_Family'.
    simpl.
    vec_index_equiv j jc.
    unfold densify.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    rewrite evalDSHOperator_DSHISumunion_Sn.
    assert(nc: n < S n).
    {
      unfold lt, peano_naturals.nat_lt.
      auto.
    }
    Opaque evalDSHOperator ISumUnion.
    simpl.

    assert(H: SHOperatorFamily_DSHCOL_equiv σ (shrink_op_family Monoid_RthetaFlags op_family) dop_family).
    {
      intros j g x'.
      simpl.
      specialize (Hfam (mkSFinNat j) g x').
      simpl in Hfam.
      rewrite <- mkSFinNat_proj1_eq in Hfam.
      rewrite <- Hfam.
      unfold shrink_op_family.
      f_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      unfold mkSFinNat.
      break_let.
      reflexivity.
    }

    assert(Hdot: forall Γ a b, Some (plus a b) = evalBinCarrierA (σ++Γ) (APlus (AVar 1) (AVar 0)) a b).
    {
      intros g a b.
      unfold evalBinCarrierA.
      reflexivity.
    }

    repeat break_match; try some_none_contradiction.
    +
      specialize (Hfam (mkFinNat nc) Γ x).
      simpl in Hfam.
      rewrite Heqo1 in Hfam.
      some_inv.
      specialize (IHn (shrink_op_family _ op_family) H).
      some_inv.
      clear  Heqo0 Heqo1 dop_family H.

      rewrite Vmap2_as_Vbuild.
      symmetry.
      apply vsequence_Vbuild_equiv_Some.
      unfold densify.
      rewrite Vmap_map.
      vec_index_equiv j jc.
      rewrite Vbuild_nth.
      rewrite Vnth_map.
      rewrite <- Hdot.
      clear Γ σ Hdot.
      f_equiv.

      rewrite 2!Vnth_to_Vnth_aux.
      rewrite <- Hfam. clear Hfam.
      rewrite <- IHn. clear IHn.
      rewrite <- 2!Vnth_to_Vnth_aux.
      clear t0 t.

      unfold densify.
      rewrite 2!Vnth_map.
      simpl.
      Transparent evalDSHOperator ISumUnion.
      unfold ISumUnion, IUnion. simpl.

      rewrite <- evalWriter_Rtheta_liftM2.
      fold_Rtheta'_equiv.
      symmetry.
      apply Vnth_Diamond'_Sn.
      typeclasses eauto.
    +
      exfalso.
      clear IHn.
      specialize (Hfam (mkFinNat nc) Γ x).
      simpl in Hfam.
      rewrite Heqo1 in Hfam.
      some_none_contradiction.
    +
      exfalso.
      clear Hfam.
      specialize (IHn (shrink_op_family _ op_family) H).
      some_none_contradiction.
Qed.

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