Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import MetaCoq.Template.All.

Require Import Helix.Util.Misc.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.SigmaHCOL.SigmaHCOL.
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

MetaCoq Run
    (mkSwitch string
              string_beq
              [  ("Embed", "n_Embed") ;
                 ("Pick", "n_Pick") ;
                 ("SHPointwise", "n_SHPointwise") ;
                 ("SHBinOp", "n_SHBinOp") ;
                 ("SHInductor", "n_SHInductor") ;
                 ("IUnion", "n_IUnion") ;
                 ("ISumUnion", "n_ISumUnion") ;
                 ("IReduction", "n_IReduction") ;
                 ("SHCompose", "n_SHCompose") ;
                 ("SafeCast", "n_SafeCast") ;
                 ("UnSafeCast", "n_UnSafeCast") ;
                 ("Apply2Union", "n_Apply2Union")
              ]
              "SHCOL_Op_Names" "parse_SHCOL_Op_Name"
    ).

Fixpoint compileSHCOL2MSHCOL (t:term) (fuel: nat) {struct fuel}: TemplateMonad (term) :=
  let kmshop name := (MPdot (MPfile ["MSigmaHCOL"; "MSigmaHCOL"; "Helix"]) "MMSCHOL", name) in
  match fuel with
  | O => tmFail "expression complexity limit reached"
  | S fuel' =>
    match t with
    | tConst (cmod,cname) _ =>
      tmPrint ("Trying to unfold constant" ++ cname) ;;
              et <- tmUnquote t ;;
              (match et with
               | existT_typed_term _ e =>
                 e' <-  tmEval (unfold (cmod,cname)) e ;;
                    t' <- tmQuote e' ;;
                    match t' with
                    | tConst (cmod',cname') _ =>
                      if string_beq
                           (string_of_kername (cmod, cname))
                           (string_of_kername (cmod',cname'))
                      then
                        tmFail ("Could not unfold constant " ++ cname')
                      else
                        tmPrint ("Sucessfully nfolded constant " ++ cname) ;;
                                compileSHCOL2MSHCOL t' fuel'
                    | _ =>
                      tmPrint ("Sucessfully nfolded constant " ++ cname) ;;
                              compileSHCOL2MSHCOL t' fuel'
                    end
               end)
    | tLambda (nNamed n) vt b =>
      tmPrint ("lambda " ++ n)  ;;
              c <- compileSHCOL2MSHCOL b fuel' ;;
              tmReturn(tLambda (nNamed n) vt c)
    | tApp (tConst (_,opname) u) args =>
      match parse_SHCOL_Op_Name opname, args with
      | Some n_Embed, [fm ; svalue; o ; b ; bc] =>
        tmPrint "Embed" ;;
                tmReturn  (tApp (tConst (kmshop "MSHEmbed") u)
                                [o; b ; bc])
      | Some n_Pick, [fm ; svalue; i ; b ; bc] =>
        tmPrint "Pick" ;;
                tmReturn  (tApp (tConst (kmshop "MSHPick") u)
                                [i; b; bc])
      | Some n_SHPointwise, [fm ; svalue; n ; f ; pF ] =>
        tmPrint "SHPointwise" ;;
                tmReturn  (tApp (tConst (kmshop "MSHPointwise") u)
                                [n; f; pF])
      | Some n_SHBinOp, [fm ; svalue; o ; f ; pF]
        =>
        tmPrint "SHBinOp" ;;
                tmReturn  (tApp (tConst (kmshop "MSHBinOp") u)
                                [o; f; pF])
      | Some n_SHInductor, [fm ; svalue; n ; f ; pF ; z] =>
        tmPrint "SHInductor" ;;
                tmReturn  (tApp (tConst (kmshop "MSHInductor") u)
                                [n; f; pF; z])
      | Some n_IUnion, [svalue; i ; o ; n ; f ; pF ; scompat ; op_family] =>
        tmPrint "IUnion" ;;
                c <- compileSHCOL2MSHCOL op_family fuel' ;;
                tmReturn  (tApp (tConst (kmshop "MSHIUnion") u)
                                [i; o; n; c])
      | Some n_ISumUnion, [i ; o ; n ; op_family] =>
        (* Same as [IUnion] *)
        tmPrint "ISumUnion" ;;
                c <- compileSHCOL2MSHCOL op_family fuel';;
                tmReturn  (tApp (tConst (kmshop "MSHIUnion") u)
                                [i; o; n; c])
      | Some n_IReduction, [svalue; i ; o ; n ; f ; pF ; scompat ; op_family] =>
        tmPrint "IReduction" ;;
                c <- compileSHCOL2MSHCOL op_family fuel' ;;
                tmReturn  (tApp (tConst (kmshop "MSHIReduction") u)
                                [i; o; n; svalue; f; pF; c])
      | Some n_SHCompose, [fm ; svalue; i1 ; o2 ; o3 ; op1 ; op2] =>
        tmPrint "SHCompose" ;;
                c1 <- compileSHCOL2MSHCOL op1 fuel' ;;
                c2 <- compileSHCOL2MSHCOL op2 fuel' ;;
                tmReturn  (tApp (tConst (kmshop "MSHCompose") u)
                                [i1; o2; o3; c1; c2])
      | Some n_SafeCast, [svalue; i ; o ; c] =>
        tmPrint "SafeCast" ;;
                compileSHCOL2MSHCOL c fuel'
      | Some n_UnSafeCast, [svalue; i ; o ; c] =>
        tmPrint "UnSafeCast" ;;
                compileSHCOL2MSHCOL c fuel'
      | Some n_Apply2Union, [fm ; i ; o ; svalue; dot ; _ ; _; op1 ; op2] =>
        tmPrint "Apply2Union" ;;
                c1 <- compileSHCOL2MSHCOL op1 fuel' ;;
                c2 <- compileSHCOL2MSHCOL op2 fuel' ;;
                tmReturn  (tApp (tConst (kmshop "MApply2Union") u)
                                [i; o; dot; c1; c2])
      | None, _ =>
        tmFail ("Usupported function call " ++ opname)
      | _, _ =>
        tmFail ("Usupported arguments "
                  ++ string_of_list string_of_term args
                  ++ "for SHCOL operator " ++ opname)
      end
    | _ as t =>
      tmFail ("Usupported SHCOL syntax " ++ (AstUtils.string_of_term t))
    end
  end.

Fixpoint tmUnfoldList {A:Type} (names:list kername) (e:A): TemplateMonad A :=
  match names with
  | [] => tmReturn e
  | x::xs =>  u <- @tmEval (unfold x) A e ;;
               tmUnfoldList xs u
  end.

Definition reifySHCOL {A:Type} (expr: A)
           (fuel: nat)
           (unfold_names: list kername)
           (res_name: string)
  : TemplateMonad unit
  :=
    let unfold_names := List.app unfold_names [(MPfile ["SigmaHCOL"; "SigmaHCOL"; "Helix"], "SHFamilyOperatorCompose")] in
    eexpr <- tmUnfoldList unfold_names expr ;;
          ast <- @tmQuote A eexpr ;;
          (* tmPrint ("AST" ++ (AstUtils.string_of_term ast)) ;; *)
          mast <- compileSHCOL2MSHCOL ast fuel ;;
          (* tmPrint ("MAST" ++ (AstUtils.string_of_term mast)) ;; *)
          mexpr <- tmUnquote mast ;;
          (match mexpr with
           | existT_typed_term mexprt mexprv =>
             mexpr' <- tmEval (unfold (MPfile ["Common"; "TemplateMonad"; "Template"; "MetaCoq"], "my_projT1")) mexprv ;;
                    mshcol_def <- tmDefinition res_name mexpr'
                    ;; tmReturn tt
           end).

