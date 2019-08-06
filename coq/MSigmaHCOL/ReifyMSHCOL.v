Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import MetaCoq.Template.All.

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
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.MSigmaHCOL.MemVecEq.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.Tactics.HelixTactics.

Require Import Switch.Switch.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.

(* This import must be after Vector stuff, so `const` will point to
   Basics.const not Vector.const. We need this to be able to unfold it
   in TemplateCoq, which does not understand qualified names (with
   ".") *)
Require Import Coq.Program.Basics.

Import MonadNotation.
Require Import Coq.Lists.List. Import ListNotations.
Open Scope string_scope.

Run TemplateProgram
    (mkSwitch string
              string_beq
              [("Helix.SigmaHCOL.SigmaHCOL.eUnion", "n_eUnion") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.eT", "n_eT") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.SHPointwise", "n_SHPointwise") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.SHBinOp", "n_SHBinOp") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.SHInductor", "n_SHInductor") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.IUnion", "n_IUnion") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.ISumUnion", "n_ISumUnion") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.IReduction", "n_IReduction") ;
                 ("Helix.SigmaHCOL.SigmaHCOL.SHCompose", "n_SHCompose") ;
                 ("Helix.SigmaHCOL.TSigmaHCOL.SafeCast", "n_SafeCast") ;
                 ("Helix.SigmaHCOL.TSigmaHCOL.UnSafeCast", "n_UnSafeCast") ;
                 ("Helix.SigmaHCOL.TSigmaHCOL.HTSUMUnion", "n_HTSUMUnion")]
              "SHCOL_Op_Names" "parse_SHCOL_Op_Name"
    ).

Fixpoint compileSHCOL2MSHCOL (t:term) {struct t}: TemplateMonad (term) :=
  match t with
  | tLambda (nNamed n) vt b =>
    tmPrint ("lambda " ++ n)  ;;
            c <- compileSHCOL2MSHCOL b ;;
            tmReturn(tLambda (nNamed n) vt c)
  | tApp (tConst opname u) args =>
    match parse_SHCOL_Op_Name opname, args with
    | Some n_eUnion, [fm ; svalue; o ; b ; bc] =>
      tmPrint "eUnion" ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHeUnion" u)
                              [o; b ; bc])
    | Some n_eT, [fm ; svalue; i ; b ; bc] =>
      tmPrint "eT" ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHeT" u)
                              [i; b; bc])
    | Some n_SHPointwise, [fm ; svalue; n ; f ; pF ] =>
      tmPrint "SHPointwise" ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHPointwise" u)
                              [n; f; pF])
    | Some n_SHBinOp, [fm ; svalue; o ; f ; pF]
      =>
      tmPrint "SHBinOp" ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHBinOp" u)
                              [o; f; pF])
    | Some n_SHInductor, [fm ; svalue; n ; f ; pF ; z] =>
      tmPrint "SHInductor" ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHInductor" u)
                              [n; f; pF; z])
    | Some n_IUnion, [svalue; i ; o ; n ; f ; pF ; scompat ; op_family] =>
      tmPrint "IUnion" ;;
              c <- compileSHCOL2MSHCOL op_family ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHIUnion" u)
                              [i; o; n; c])
    | Some n_ISumUnion, [i ; o ; n ; op_family] =>
      (* Same as [IUnion] *)
      tmPrint "ISumUnion" ;;
              c <- compileSHCOL2MSHCOL op_family ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHIUnion" u)
                              [i; o; n; c])
    | Some n_IReduction, [svalue; i ; o ; n ; f ; pF ; scompat ; op_family] =>
      tmPrint "IReduction" ;;
              c <- compileSHCOL2MSHCOL op_family ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHIReduction" u)
                              [i; o; n; svalue; f; pF; c])
    | Some n_SHCompose, [fm ; svalue; i1 ; o2 ; o3 ; op1 ; op2] =>
      tmPrint "SHCompose" ;;
              c1 <- compileSHCOL2MSHCOL op1 ;;
              c2 <- compileSHCOL2MSHCOL op2 ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MSHCompose" u)
                              [i1; o2; o3; c1; c2])
    | Some n_SafeCast, [svalue; i ; o ; c] =>
      tmPrint "SafeCast" ;;
              compileSHCOL2MSHCOL c
    | Some n_UnSafeCast, [svalue; i ; o ; c] =>
      tmPrint "UnSafeCast" ;;
              compileSHCOL2MSHCOL c
    | Some n_HTSUMUnion, [fm ; i ; o ; svalue; dot ; _ ; _; op1 ; op2] =>
      tmPrint "HTSumunion" ;;
              c1 <- compileSHCOL2MSHCOL op1 ;;
              c2 <- compileSHCOL2MSHCOL op2 ;;
              tmReturn  (tApp (tConst "Helix.MSigmaHCOL.MSigmaHCOL.MHTSUMUnion" u)
                              [i; o; dot; c1; c2])

    | None, _ =>
      tmFail ("Usupported SHCOL operator" ++ opname)
    | _, _ =>
      tmFail ("Usupported arguments "
                ++ string_of_list string_of_term args
                ++ "for SHCOL operator" ++ opname)
    end
  | _ as t =>
    tmFail ("Usupported SHCOL syntax" ++ (AstUtils.string_of_term t))
  end.



Fixpoint tmUnfoldList {A:Type} (names:list string) (e:A): TemplateMonad A :=
  match names with
  | [] => tmReturn e
  | x::xs =>  u <- @tmEval (unfold x) A e ;;
               tmUnfoldList xs u
  end.

Definition reifySHCOL {A:Type} (expr: A)
           (unfold_names: list ident) (* list of top-level names to unfold *)
           (res_name:string)
           (lemma_name:string): TemplateMonad unit
  :=
    let extra_unfold_names := List.app ["SHFamilyOperatorCompose"; "IgnoreIndex"; "Fin1SwapIndex"; "Fin1SwapIndex2"; "IgnoreIndex2"; "mult_by_nth"; "plus"; "mult"; "const"] unfold_names in
    eexpr <- tmUnfoldList extra_unfold_names expr ;;
          ast <- @tmQuote A eexpr ;;
          tmPrint ("AST" ++ (AstUtils.string_of_term ast)) ;;
          mast <- compileSHCOL2MSHCOL ast ;;
          tmPrint ("MAST" ++ (AstUtils.string_of_term mast)) ;;
          mexpr <- tmUnquote mast ;;
          (match mexpr with
           | existT_typed_term mexprt mexprv =>
             mexpr' <- tmEval (unfold "my_projT1") mexprv ;;
                    mshcol_def <- tmDefinition res_name mexpr'
                    ;; tmReturn tt
           end).


 (* Testing only *)
Require Import Omega.
Program Definition foo := @eUnion Monoid_RthetaFlags CarrierAz 10 3 _.
Next Obligation. omega. Defined.

Obligation Tactic := idtac.
Run TemplateProgram (reifySHCOL foo ["foo"] "foo_def" "foo_lemma").
Check foo_def.
Print foo_def.


               mt <- tmQuote (mem_block) ;;
               d' <- compileOperator [] 0 1 2 ast ;;
               let '(globals, a_fm, a_svalue, i, o, heap_i, dshcol) := (d':varbindings*term*term*nat*nat*nat*DSHOperator) in
               a_i <- tmQuote i ;; a_o <- tmQuote o ;;
                   a_globals <- build_dsh_globals globals ;;
                   let global_idx := List.map tRel (rev_nat_seq (length globals)) in
                   let a_shcol := tApp a_expr global_idx in
                   dshcol' <- tmEval cbv dshcol ;;
                           d_dshcol <- tmDefinition res_name dshcol'
                           (* fm <- tmUnquoteTyped (Monoid.Monoid RthetaFlags) a_fm ;;
                           sva   lue <- tmUnquoteTyped CarrierA a_svalue ;;
                           let facts_a :=
                               build_lambda globals (tApp
                                                       (tInd {| inductive_mind := "SHOperator_Facts"; inductive_ind := 0 |} [])
                                                       [a_fm; a_i; a_o; a_svalue; a_shcol]) in
                           tmPrint facts_a ;;
                           facts <- tmUnquote facts_a ;;
                           facts_i <- tmInferInstance (Some cbv) facts ;;
                           tmPrint facts_i ;;
                           ;;
                             a_dshcol <- tmQuote d_dshcol ;;
                             let lemma_concl :=
                                 (tApp (tConst "SHCOL_DSHCOL_equiv" [])
                                       [a_i; a_o; a_svalue; a_fm; a_globals;
                                          a_shcol;
                                          a_facts;
                                          a_mem;
                                          a_dshcol])
                             in
                             let lemma_ast := build_forall globals lemma_concl in
                             (tmBind (tmUnquoteTyped Prop lemma_ast)
                                     (fun lemma_body => tmLemma lemma_name lemma_body
                                                             ;;
                                                             tmReturn dshcol)) *)

                             ;; tmReturn dshcol
               .


