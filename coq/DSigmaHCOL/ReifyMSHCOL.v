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
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.

Require Import Helix.Tactics.HelixTactics.

Require Import Switch.Switch.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.

(* This import must be after Vector stuff, so `const` will point to
   Basics.const not Vector.const. We need this to be able to unfold it
   in TemplateCoq, which does not understand qualified names (with
   ".") *)
Require Import Coq.Program.Basics.

Import MDSHCOLOnCarrierA.

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
    | tConst "Helix.HCOL.CarrierType.CarrierA" _ => tmReturn DSHCType
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
  | _ => tmFail ("Unsupported NExpr " ++ (string_of_term a_n))
  end.

Fixpoint compileMExpr (a_e:term): TemplateMonad (MExpr):=
  match a_e with
  | tRel i => tmReturn (MVar i)
  (* TODO: support for constant vectors as MConst *)
  | _ => tmFail ("Unsupported MExpr " ++ (string_of_term a_e))
  end.

Fixpoint compileAExpr (a_e:term): TemplateMonad AExpr :=
  match a_e with
  | tApp (tConst "MathClasses.interfaces.canonical_names.abs" [])
         [tConst "Helix.HCOL.CarrierType.CarrierA" [];
            _; _; _;  _; _; a_a] =>
    d_a <- compileAExpr a_a ;;
        tmReturn (AAbs d_a)
  | tApp (tConst "Helix.HCOL.CarrierType.sub" []) [_; _; _; a_a ; a_b] =>
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
  | _ => tmFail ("Unsupported AExpr " ++ (string_of_term a_e))
  end.

Definition compileDSHUnCarrierA (a_f:term): TemplateMonad AExpr :=
  match a_f with
  | tLambda _ _ a_f' => compileAExpr a_f'
  | _ => tmFail ("Unsupported UnCarrierA " ++ (string_of_term a_f))
  end.

Definition compileDSHIUnCarrierA (a_f:term): TemplateMonad AExpr :=
  match a_f with
  | tLambda _ _ a_f' => compileDSHUnCarrierA a_f'
  | _ => tmFail ("Unsupported IUnCarrierA " ++ (string_of_term a_f))
  end.

Definition compileDSHBinCarrierA (a_f:term): TemplateMonad AExpr :=
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
  | _ => tmFail ("Unsupported BinCarrierA " ++ (string_of_term a_f))
  end.

Definition compileDSHIBinCarrierA (a_f:term): TemplateMonad AExpr :=
  match a_f with
  | tLambda _ _ a_f' => compileDSHBinCarrierA a_f'
  | _ => tmFail ("Unsupported IBinCarrierA " ++ (string_of_term a_f))
  end.

Run TemplateProgram
    (mkSwitch string
              string_beq
              [  ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHPick"      , "n_Pick"       ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHEmbed"     , "n_Embed"      ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHPointwise" , "n_SHPointwise") ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHBinOp"     , "n_SHBinOp"    ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHInductor"  , "n_SHInductor" ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHIUnion"    , "n_IUnion"     ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHIReduction", "n_IReduction" ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHCompose"   , "n_SHCompose"  ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MHTSUMUnion"  , "n_HTSUMUnion" ) ]

              "SHCOL_Op_Names" "parse_SHCOL_Op_Name"
    ).


(* return tuple: vars, [DSHOperator x_p y_p] *)
Fixpoint compileMSHCOL2DSHCOL
         (skip:nat)
         (vars:varbindings)
         (t:term)
         (x_p y_p: PExpr)
  : TemplateMonad (varbindings*(DSHOperator)) :=
  match t with
  | tLambda (nNamed n) vt b =>
    tmPrint ("lambda " ++ n)  ;;
            toDSHType (tmReturn vt) ;; (* to enforce valid type *)
            compileMSHCOL2DSHCOL (S skip) ((nNamed n,vt)::vars) b (incrPVar skip x_p) (incrPVar skip y_p)
  | tApp (tConst opname _) args =>
    match parse_SHCOL_Op_Name opname, args with
    | Some n_Pick, [o ; b ; _] =>
      tmPrint "MSHPick" ;;
              no <- tmUnquoteTyped nat o ;;
              bc <- compileNExpr b ;;
              tmReturn (vars,  DSHAssign (x_p, NConst 0) (y_p, bc))
    | Some n_Embed, [i ; b ; _] =>
      tmPrint "MSHEmbed" ;;
              ni <- tmUnquoteTyped nat i ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, DSHAssign (x_p, bc) (y_p, NConst 0))
    | Some n_SHPointwise, [n ; f ; _ ] =>
      tmPrint "MSHPointwise" ;;
              nn <- tmUnquoteTyped nat n ;;
              df <- compileDSHIUnCarrierA f ;;
              tmReturn (vars, DSHIMap nn (x_p) (y_p) df)
    | Some n_SHBinOp, [o ; f ; _] =>
      tmPrint "MSHBinOp" ;;
              no <- tmUnquoteTyped nat o ;;
              df <- compileDSHIBinCarrierA f ;;
              tmReturn (vars, DSHBinOp no (x_p) (y_p) df )
    | Some n_SHInductor, [n ; f ; _ ; z] =>
      tmPrint "MSHInductor" ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              nc <- compileNExpr n ;;
              df <- compileDSHBinCarrierA f ;;
              tmReturn (vars, DSHPower nc (x_p, NConst 0) (y_p, NConst 0) df zconst)
    | Some n_IUnion, [i ; o ; n ; op_family] =>
      tmPrint "MSHIUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              (* op_family will increase [skip] offset automatically *)
              c' <- compileMSHCOL2DSHCOL skip vars op_family x_p y_p ;;
              let '(_, rr) := c' in
              tmReturn (vars, DSHLoop nn rr )
    | Some n_IReduction, [i ; o ; n ; z; f ; _ ; op_family] =>
      tmPrint "MSHIReduction" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              tt <- tmQuote DSHnat ;;
              (* Stack states:
                 Before alloc: ... x_p y_p ...
                 After alloc: ... x_p y_p ... t_i
                 In the loop: ... x_p y_p ... t_i j
               *)
              (* freshly allocated, inside alloc before loop *)
              let t_i := PVar 0 in
              (* single inc. inside loop *)
              let t_i' := incrPVar 0 t_i in
              (* single inc. inside alloca before loop *)
              let x_p' := incrPVar 0 x_p in
              (* double inc. inside alloc and loop *)
              let x_p'' := incrPVar 0 x_p' in
              let y_p'' := incrPVar 0 (incrPVar 0 y_p) in
              (* op_family will increase [skip] offset automatically,
                 but we need to increase it once more for [DSHAlloc]
               *)
              c' <- compileMSHCOL2DSHCOL (S skip) ((nAnon, tt)::vars) op_family x_p' t_i ;;
                 df <- compileDSHBinCarrierA f ;;
                 (* [df] increased twice to skip loop and alloc *)
                 let df'' := incrDSHBinCType (S skip) df in
                 let '(_, rr) := c' in
                 tmReturn (vars, DSHAlloc no
                                          (DSHSeq
                                             (DSHMemInit no t_i zconst)
                                             (DSHLoop nn
                                                      (DSHSeq
                                                         rr
                                                         (DSHMemMap2 no t_i' y_p'' y_p'' df'')))))
    | Some n_SHCompose, [i1 ; o2 ; o3 ; op1 ; op2] =>
      tmPrint "MSHCompose" ;;
              ni1 <- tmUnquoteTyped nat i1 ;;
              no2 <- tmUnquoteTyped nat o2 ;;
              no3 <- tmUnquoteTyped nat o3 ;;
              (* freshly allocated, inside alloc *)
              let t_i := PVar 0 in
              (* single inc. inside alloc *)
              let x_p' := incrPVar 0 x_p in
              let y_p' := incrPVar 0 y_p in
              cop2' <- compileMSHCOL2DSHCOL (S skip) vars op2 x_p' t_i ;;
                    let '(_, cop2) := cop2' in
                    cop1' <- compileMSHCOL2DSHCOL (S skip) vars op1 t_i y_p' ;;
                          let '(_, cop1) := cop1' in
                          tmReturn (vars, DSHAlloc no2 (DSHSeq cop2 cop1))
    | Some n_HTSUMUnion, [i ; o ; dot ; op1 ; op2] =>
      tmPrint "MHTSUMUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              ddot <- compileDSHBinCarrierA dot ;;
              (* [ddot] increased twice for 2 allocs *)
              let ddot' := incrDSHIBinCType (S (S skip)) ddot in
              tt <- tmQuote DSHnat ;;
              let tyf_i := PVar 0 in
              let tyg_i := PVar 1 in
              let vars' := ((nAnon, tt)::((nAnon, tt)::vars)) in
              (* double increase after 2 allocs *)
              let x_p'' := incrPVar 0 (incrPVar 0 x_p) in
              let y_p'' := incrPVar 0 (incrPVar 0 y_p) in
              cop1' <- compileMSHCOL2DSHCOL (S (S skip)) vars' op1 x_p'' tyf_i ;;
                    let '(_, cop1) := cop1' in
                    cop2' <- compileMSHCOL2DSHCOL (S (S skip)) vars' op2 x_p'' tyg_i ;;
                          let '(_,cop2) := cop2' in
                          tmReturn (vars,
                                    DSHAlloc no
                                             (DSHAlloc no
                                                       (DSHSeq
                                                          (DSHSeq cop1 cop2)
                                                          (DSHMemMap2 no tyf_i tyg_i y_p'' ddot'))))
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
  | [] => tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSHCOLOnCarrierA.MDSHCOLOnCarrierA.DSHVal"; inductive_ind := 0 |} []])
  | (_,t)::gs =>
    dt <- toDSHType (tmReturn t) ;;
       let i := length gs in
       dv <- (match dt with
             | DSHnat => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSHCOLOnCarrierA.MDSHCOLOnCarrierA.DSHVal"; inductive_ind := 0 |} 0 []) [tRel i])
             | DSHCType => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSHCOLOnCarrierA.MDSHCOLOnCarrierA.DSHVal"; inductive_ind := 0 |} 1 []) [tRel i])
             | DSHMemBlock => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSHCOLOnCarrierA.MDSHCOLOnCarrierA.DSHVal"; inductive_ind := 0 |} 2 []) [tRel i])
             | DSHPtr => tmReturn (tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSHCOLOnCarrierA.MDSHCOLOnCarrierA.DSHVal"; inductive_ind := 0 |} 3 []) [tRel i])
             end) ;;
          ts <- build_dsh_globals gs ;;
          tmReturn (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSHCOLOnCarrierA.MDSHCOLOnCarrierA.DSHVal"; inductive_ind := 0 |} []; dv; ts])
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
           (res_name: string)
           (vars: varbindings)
           (x_p y_p: PExpr)
  : TemplateMonad unit :=
  let unfold_names := List.app unfold_names ["SHFamilyOperatorCompose"; "IgnoreIndex"; "Fin1SwapIndex"; "Fin1SwapIndex2"; "IgnoreIndex2"; "mult_by_nth"; "plus"; "mult"; "const"] in
  eexpr <- tmUnfoldList unfold_names expr ;;
        ast <- @tmQuote A eexpr ;;
        ast <- @tmQuote A eexpr ;;
        mt <- tmQuote (mem_block) ;;
        d' <- compileMSHCOL2DSHCOL 0 vars ast x_p y_p ;;
        let '(globals, dshcol) := d' in
        dshcol' <- tmEval cbv dshcol ;;
                d_dshcol <- tmDefinition res_name dshcol'
                ;; tmReturn tt.
