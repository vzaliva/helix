Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import MetaCoq.Template.All.

Require Import Helix.Util.Misc.
Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.FinNat.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
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

Definition toDSHType (tt: TemplateMonad term): TemplateMonad DSHType :=
  t <- tt ;;
    match t with
    | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ =>
      tmReturn DSHnat
    | (tApp(tInd {| inductive_mind := "Coq.Init.Specif.sig"; inductive_ind := 0 |} _)
           [tInd
              {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ ; _])
      => tmReturn DSHnat (* `FinNat` is treated as `nat` *)
    | tConst "Helix.HCOL.CarrierType.CarrierA" _ => tmReturn DSHCarrierA
    | tConst "Helix.SigmaHCOL.Memory.mem_block" _ => tmReturn DSHMemBlock
    | tApp
        (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} _)
        [tConst "Helix.HCOL.CarrierType.CarrierA" _ ; nat_term] =>
      (* n <- tmUnquoteTyped nat nat_term ;; *)
        tmReturn DSHMemBlock (* hacky! mapping vectors to memory blocks *)
    | _ =>
      (* tmPrint t ;; this print slows complilation down *)
      tmFail "non-DSHCOL type encountered"
    end.

(* DeBruijn indixed list variables. Each variable has name and type *)
Definition varbindings:Type := list (name*term).

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
  | (tApp (tConst "Coq.Init.Nat.sub" []) [ a_a ; a_b]) =>
    d_a <- compileNExpr a_a ;;
        d_b <- compileNExpr a_b ;;
        tmReturn (NMinus d_a d_b)
  | (tApp (tConst "Coq.Init.Nat.mul" []) [ a_a ; a_b]) =>
    d_a <- compileNExpr a_a ;;
        d_b <- compileNExpr a_b ;;
        tmReturn (NMult d_a d_b)
  (* TODO: more cases *)
  | _ => tmFail ("Unsupported NExpr" ++ (string_of_term a_n))
  end.

Fixpoint compileMExpr (a_e:term): TemplateMonad (MExpr):=
  match a_e with
  | tRel i => tmReturn (MVar i)
  (* TODO: support for constant vectors as MConst *)
  | _ => tmFail ("Unsupported MExpr" ++ (string_of_term a_e))
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
    (* n <- tmUnquoteTyped nat a_n ;; *)
      d_v <- compileMExpr a_v ;;
      d_i <- compileNExpr a_i ;;
      tmReturn (ANth d_v d_i)
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

Run TemplateProgram
    (mkSwitch string
              string_beq
              [  ("Helix.MSigmaHCOL.MSigmaHCOL.MSHeUnion"    , "n_eUnion"     ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHeT"        , "n_eT"         ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHPointwise" , "n_SHPointwise") ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHBinOp"     , "n_SHBinOp"    ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHInductor"  , "n_SHInductor" ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHIUnion"    , "n_IUnion"     ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHIReduction", "n_IReduction" ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MSHCompose"   , "n_SHCompose"  ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MHTSUMUnion"  , "n_HTSUMUnion" ) ]

              "SHCOL_Op_Names" "parse_SHCOL_Op_Name"
    ).

(* return tuple: vars, heap_i, DSHOperator *)
Fixpoint compileMSHCOL2DSHCOL (vars:varbindings) (x_i y_i heap_i: mem_block_id) (t:term) {struct t}: TemplateMonad (varbindings*nat*DSHOperator) :=
  match t with
  | tLambda (nNamed n) vt b =>
    tmPrint ("lambda " ++ n)  ;;
            toDSHType (tmReturn vt) ;;
            compileMSHCOL2DSHCOL ((nNamed n,vt)::vars) x_i y_i heap_i b
  | tApp (tConst opname _) args =>
    match parse_SHCOL_Op_Name opname, args with
    | Some n_eUnion, [o ; b ; _] =>
      tmPrint "MSHeUnion" ;;
              no <- tmUnquoteTyped nat o ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, heap_i, DSHAssign (x_i,NConst 0) (y_i, bc))
    | Some n_eT, [i ; b ; _] =>
      tmPrint "MSHeT" ;;
              ni <- tmUnquoteTyped nat i ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, heap_i, DSHAssign (x_i, bc) (y_i, NConst 0))
    | Some n_SHPointwise, [n ; f ; _ ] =>
      tmPrint "MSHPointwise" ;;
              nn <- tmUnquoteTyped nat n ;;
              df <- compileDSHIUnCarrierA f ;;
              tmReturn (vars, heap_i, DSHIMap nn x_i y_i df)
    | Some n_SHBinOp, [o ; f ; _]
      =>
      tmPrint "MSHBinOp" ;;
              no <- tmUnquoteTyped nat o ;;
              df <- compileDSHIBinCarrierA f ;;
              tmReturn (vars, heap_i, DSHBinOp no x_i y_i df )
    | Some n_SHInductor, [n ; f ; _ ; z] =>
      tmPrint "MSHInductor" ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              nc <- compileNExpr n ;;
              df <- compileDSHBinCarrierA f ;;
              tmReturn (vars, heap_i,
                        DSHPower nc (x_i, NConst 0) (y_i, NConst 0) df zconst)
    | Some n_IUnion, [i ; o ; n ; op_family] =>
      tmPrint "MSHIUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              c' <- compileMSHCOL2DSHCOL vars x_i y_i heap_i op_family ;;
              let '(_,heap_i',rr) := c' in
              tmReturn (vars, heap_i', DSHLoop nn rr)
    | Some n_IReduction, [i ; o ; n ; z; f ; _ ; op_family] =>
      tmPrint "MSHIReduction" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              let t_i := heap_i in
              c' <- compileMSHCOL2DSHCOL vars x_i t_i (S heap_i) op_family ;;
                 df <- compileDSHBinCarrierA f ;;
                 let '(_, heap_i', rr) := c' in
                 tmReturn (vars, heap_i',
                           (DSHAlloc no t_i
                                     (DSHSeq
                                        (DSHMemInit no y_i zconst)
                                        (DSHLoop nn
                                                 (DSHSeq
                                                    rr
                                                    (DSHMemMap2 nn t_i y_i y_i df))))))
    | Some n_SHCompose, [i1 ; o2 ; o3 ; op1 ; op2] =>
      tmPrint "MSHCompose" ;;
              ni1 <- tmUnquoteTyped nat i1 ;;
              no2 <- tmUnquoteTyped nat o2 ;;
              no3 <- tmUnquoteTyped nat o3 ;;
              let t_i := heap_i in
              cop2' <- compileMSHCOL2DSHCOL vars x_i t_i (S heap_i) op2 ;;
                    let '(_,heap_i',cop2) := cop2' in
                    cop1' <- compileMSHCOL2DSHCOL vars t_i y_i heap_i' op1 ;;
                          let '(_, heap_i'', cop1) := cop1' in
                          tmReturn (vars, heap_i'',
                                    (DSHAlloc no2 t_i (DSHSeq cop2 cop1)))
    | Some n_HTSUMUnion, [i ; o ; dot ; op1 ; op2] =>
      tmPrint "MHTSUMUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              let tyf_i := heap_i in
              let tyg_i := S heap_i in
              ddot <- compileDSHBinCarrierA dot ;;
                   cop1' <- compileMSHCOL2DSHCOL vars x_i tyf_i (S (S heap_i)) op1 ;;
                   let '(_, heap_i',cop1) := cop1' in
                   cop2' <- compileMSHCOL2DSHCOL vars x_i tyg_i heap_i' op2 ;;
                         let '(_,heap_i'',cop2) := cop2' in
                         tmReturn (vars, heap_i'',
                                   (DSHAlloc no tyf_i
                                             (DSHAlloc no tyg_i
                                                       (DSHSeq
                                                          (DSHSeq cop1 cop2)
                                                          (DSHMemMap2 no tyf_i tyg_i y_i ddot)))))
    | None, _ =>
      tmFail ("Usupported SHCOL operator " ++ opname)
    | _, _ =>
      tmFail ("Usupported arguments "
                ++ string_of_list string_of_term args
                ++ "for SHCOL operator " ++ opname)
    end
  | _ as t =>
    tmFail ("Usupported SHCOL syntax " ++ (AstUtils.string_of_term t))
  end.

Fixpoint build_forall p conc :=
  match p with
  | [] => conc
  | (n,t)::ps => tProd n t (build_forall ps conc)
  end.

Fixpoint build_lambda p conc :=
  match p with
  | [] => conc
  | (n,t)::ps => tLambda n t (build_lambda ps conc)
  end.

Fixpoint build_dsh_globals (g:varbindings) : TemplateMonad term :=
  match g with
  | [] => tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVal"; inductive_ind := 0 |} []])
  | (_,t)::gs =>
    dt <- toDSHType (tmReturn t) ;;
       let i := length gs in
       dv <- (match dt with
              | DSHnat => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVal"; inductive_ind := 0 |} 0 []) [tRel i])
              | DSHCarrierA => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVal"; inductive_ind := 0 |} 1 []) [tRel i])
              | DSHMemBlock => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVal"; inductive_ind := 0 |} 3 []) [tRel i])
              end) ;;
          ts <- build_dsh_globals gs ;;
          tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVal"; inductive_ind := 0 |} []; dv; ts])
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

Definition reifyMSHCOL {A:Type} (expr: A)
           (unfold_names: list string)
           (res_name:string)
  : TemplateMonad unit :=
  let unfold_names := List.app unfold_names ["SHFamilyOperatorCompose"; "IgnoreIndex"; "Fin1SwapIndex"; "Fin1SwapIndex2"; "IgnoreIndex2"; "mult_by_nth"; "plus"; "mult"; "const"] in
  eexpr <- tmUnfoldList unfold_names expr ;;
        ast <- @tmQuote A eexpr ;;
        ast <- @tmQuote A eexpr ;;
        mt <- tmQuote (mem_block) ;;
        d' <- compileMSHCOL2DSHCOL [] 0 1 2 ast ;;
        let '(globals, heap_i, dshcol) := (d':varbindings*nat*DSHOperator) in
            a_globals <- build_dsh_globals globals ;;
            let global_idx := List.map tRel (rev_nat_seq (length globals)) in
            dshcol' <- tmEval cbv dshcol ;;
                    d_dshcol <- tmDefinition res_name dshcol'
                    ;; tmReturn tt.

