Require Import Coq.Arith.Compare_dec.

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

(* Workaround. See https://github.com/MetaCoq/metacoq/pull/362 *)
Notation "'mlet' ' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
  (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

Require Import Coq.Lists.List. Import ListNotations.
Open Scope string_scope.

Definition toDSHType (t: term): TemplateMonad DSHType :=
  match t with
  | tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ =>
    tmReturn DSHnat
  | (tApp(tInd {| inductive_mind := "Coq.Init.Specif.sig"; inductive_ind := 0 |} _)
         [tInd
            {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} _ ; _])
    => tmReturn DSHnat (* `FinNat` is treated as `nat` *)
  | tConst "Helix.HCOL.CarrierType.CarrierA" _ => tmReturn DSHCType
  | tConst "Helix.SigmaHCOL.Memory.mem_block" _ => tmReturn DSHPtr (* pass by reference *)
  | tApp
      (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} _)
      [tConst "Helix.HCOL.CarrierType.CarrierA" _ ; nat_term] =>
    tmReturn DSHPtr (* mapping vectors to memory blocks pointers *)
  | _ =>
    (* tmPrint t ;; this print slows complilation down *)
    tmFail "non-DSHCOL type encountered"
  end.

(* DeBruijn indixed list variables. Each variable has name and type *)
Definition varbindings:Type := list (string*DSHType).

Definition var_resolver := nat -> var_id.
Definition ID_var_resolver : var_resolver := id.
Definition Fake_var_resolver (parent: var_resolver) (n:nat)
  := fun r => ((parent r)+n)%nat.
Definition Lambda_var_resolver (parent: var_resolver) (n:nat)
  := fun r => if lt_dec r n then r else ((parent (r-n))+n)%nat.

Fixpoint compileNExpr (res:var_resolver) (a_n:term): TemplateMonad NExpr :=
  match a_n with
  | tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 []
    => tmReturn (NConst 0)
  | tApp (tConst "Coq.Init.Specif.proj1_sig" []) [ _ ; _ ; tRel i]
    => tmReturn (NVar (res i))
  | tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 []) [e] =>
    d_e <- compileNExpr res e ;;
        tmReturn (match d_e with
                  | NConst v => NConst (v+1)
                  | o => NPlus o (NConst 1)
                  end)
  | tApp (tConst "Coq.Init.Nat.add" []) [ a_a ; a_b] =>
    d_a <- compileNExpr res a_a ;;
        d_b <- compileNExpr res a_b ;;
        tmReturn (NPlus d_a d_b)
  | tApp (tConst "Coq.Init.Nat.sub" []) [ a_a ; a_b] =>
    d_a <- compileNExpr res a_a ;;
        d_b <- compileNExpr res a_b ;;
        tmReturn (NMinus d_a d_b)
  | tApp (tConst "Coq.Init.Nat.mul" []) [ a_a ; a_b] =>
    d_a <- compileNExpr res a_a ;;
        d_b <- compileNExpr res a_b ;;
        tmReturn (NMult d_a d_b)
  (* TODO: more cases *)
  | _ => tmFail ("Unsupported NExpr " ++ (string_of_term a_n))
  end.

Fixpoint compileMExpr (res:var_resolver) (a_e:term): TemplateMonad (MExpr):=
  match a_e with
  | tRel i => tmReturn (MPtrDeref (PVar (res i)))
  (* TODO: support for constant vectors as MConst *)
  | _ => tmFail ("Unsupported MExpr " ++ (string_of_term a_e))
  end.

(* TODO: this one takes a long time to compile. Speed up! *)
Fixpoint compileAExpr (res:var_resolver) (a_e:term): TemplateMonad AExpr :=
  match a_e with
  | tApp (tConst "MathClasses.interfaces.canonical_names.abs" [])
         [tConst "Helix.HCOL.CarrierType.CarrierA" [];
            _; _; _;  _; _; a_a] =>
    d_a <- compileAExpr res a_a ;;
        tmReturn (AAbs d_a)
  | tApp (tConst "Helix.HCOL.CarrierType.sub" []) [_; _; _; a_a ; a_b] =>
    d_a <- compileAExpr res a_a ;;
        d_b <- compileAExpr res a_b ;;
        tmReturn (AMinus d_a d_b)
  | tApp (tConst "Helix.HCOL.CarrierType.CarrierAmult" []) [a_a ; a_b] =>
    d_a <- compileAExpr res a_a ;;
        d_b <- compileAExpr res a_b ;;
        tmReturn (AMult d_a d_b)
  | tApp (tConst "CoLoR.Util.Vector.VecUtil.Vnth" [])
         [tConst "Helix.HCOL.CarrierType.CarrierA" [] ; _ ; a_v ; a_i ; _] =>
      d_v <- compileMExpr res a_v ;;
      d_i <- compileNExpr res a_i ;;
      tmReturn (ANth d_v d_i)
  | tRel i =>
    tmReturn (AVar (res i))
  | _ => tmFail ("Unsupported AExpr " ++ (string_of_term a_e))
  end.

Definition compileDSHUnCarrierA (res:var_resolver) (a_f:term): TemplateMonad AExpr :=
  match a_f with
  | tLambda _ _ a_f' => compileAExpr (Lambda_var_resolver res 1) a_f'
  | _ => tmFail ("Unsupported UnCarrierA " ++ (string_of_term a_f))
  end.

Definition compileDSHIUnCarrierA (res:var_resolver) (a_f:term): TemplateMonad AExpr :=
  match a_f with
  | tLambda _ _ a_f' => compileDSHUnCarrierA (Lambda_var_resolver res 1) a_f'
  | _ => tmFail ("Unsupported IUnCarrierA " ++ (string_of_term a_f))
  end.

Definition compileDSHBinCarrierA (res:var_resolver) (a_f:term): TemplateMonad AExpr :=
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
  | tLambda _ _ (tLambda _ _ a_f') => compileAExpr (Lambda_var_resolver res 2) a_f'
  | tLambda _ _ a_f' => compileAExpr (Lambda_var_resolver res 1) a_f'
  | _ => tmFail ("Unsupported BinCarrierA " ++ (string_of_term a_f))
  end.

Definition compileDSHIBinCarrierA (res:var_resolver) (a_f:term): TemplateMonad AExpr :=
  match a_f with
  | tLambda _ _ a_f' => compileDSHBinCarrierA (Lambda_var_resolver res 1) a_f'
  | _ => tmFail ("Unsupported IBinCarrierA " ++ (string_of_term a_f))
  end.

Run TemplateProgram
    (mkSwitch string
              string_beq
              [  ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHEmbed"     , "n_Embed"       ) ;
                 ("Helix.MSigmaHCOL.MSigmaHCOL.MMSCHOL.MSHPick"      , "n_Pick"      ) ;
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
         (res: var_resolver)
         (vars:varbindings)
         (t:term)
         (x_p y_p: PExpr)
  : TemplateMonad (varbindings*(DSHOperator)) :=
  match t with
  | tLambda (nNamed n) vt b =>
    tmPrint ("lambda " ++ n)  ;;
            dt <- toDSHType vt ;; (* to enforce valid type *)
            compileMSHCOL2DSHCOL (Lambda_var_resolver res 1) ((n,dt)::vars) b (incrPVar 0 x_p) (incrPVar 0 y_p)
  | tApp (tConst opname _) args =>
    match parse_SHCOL_Op_Name opname, args with
    | Some n_Embed, [o ; b ; _] =>
      tmPrint "MSHEmbed" ;;
              no <- tmUnquoteTyped nat o ;;
              bc <- compileNExpr res b ;;
              tmReturn (vars,  DSHAssign (x_p, NConst 0) (y_p, bc))
    | Some n_Pick, [i ; b ; _] =>
      tmPrint "MSHPick" ;;
              ni <- tmUnquoteTyped nat i ;;
              bc <- compileNExpr res b ;;
              tmReturn (vars, DSHAssign (x_p, bc) (y_p, NConst 0))
    | Some n_SHPointwise, [n ; f ; _ ] =>
      tmPrint "MSHPointwise" ;;
              nn <- tmUnquoteTyped nat n ;;
              df <- compileDSHIUnCarrierA res f ;;
              tmReturn (vars, DSHIMap nn (x_p) (y_p) df)
    | Some n_SHBinOp, [o ; f ; _] =>
      tmPrint "MSHBinOp" ;;
              no <- tmUnquoteTyped nat o ;;
              df <- compileDSHIBinCarrierA res f ;;
              tmReturn (vars, DSHBinOp no (x_p) (y_p) df )
    | Some n_SHInductor, [n ; f ; _ ; z] =>
      tmPrint "MSHInductor" ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              nc <- compileNExpr res n ;;
              df <- compileDSHBinCarrierA res f ;;
              tmReturn (vars, DSHPower nc (x_p, NConst 0) (y_p, NConst 0) df zconst)
    | Some n_IUnion, [i ; o ; n ; op_family] =>
      tmPrint "MSHIUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              '(_, rr) <- compileMSHCOL2DSHCOL res vars op_family x_p y_p ;;
              tmReturn (vars, DSHLoop nn rr )
    | Some n_IReduction, [i ; o ; n ; z; f ; _ ; op_family] =>
      tmPrint "MSHIReduction" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              tnt <- tmQuote DSHnat ;;
              (* freshly allocated, inside alloc before loop *)
              let t_i := PVar 0 in
              (* single inc. inside loop *)
              let t_i' := PVar 1 in
              (* single inc. inside alloca before loop *)
              let x_p' := incrPVar 0 x_p in
              (* double inc. inside alloc and loop *)
              let x_p'' := incrPVar 0 x_p' in
              let y_p'' := incrPVar 0 (incrPVar 0 y_p) in
              (* op_family will introduce [Lambda_var_resolver],
                 but we need [Fake_var_resolver] for alloc
               *)
              let res1 := Fake_var_resolver res 1 in
              '(_, rr) <- compileMSHCOL2DSHCOL res1 vars op_family x_p' t_i' ;;
               df <- compileDSHBinCarrierA res1 f ;;
               tmReturn (vars, DSHAlloc no
                                        (DSHSeq
                                           (DSHMemInit no t_i zconst)
                                           (DSHLoop nn
                                                    (DSHSeq
                                                       rr
                                                       (DSHMemMap2 no t_i' y_p'' y_p'' df)))))
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
              let res1 := Fake_var_resolver res 1 in
              '(_, cop2) <- compileMSHCOL2DSHCOL res1 vars op2 x_p' t_i ;;
               '(_, cop1) <- compileMSHCOL2DSHCOL res1 vars op1 t_i y_p' ;;
               tmReturn (vars, DSHAlloc no2 (DSHSeq cop2 cop1))
    | Some n_HTSUMUnion, [i ; o ; dot ; op1 ; op2] =>
      tmPrint "MHTSUMUnion" ;;
              (* This only works under assumption that output index
                 sets of [op1] and [op2] are disjount *)
              '(_, cop1) <- compileMSHCOL2DSHCOL res vars op1 x_p y_p ;;
              '(_,cop2) <- compileMSHCOL2DSHCOL res vars op2 x_p y_p ;;
               tmReturn (vars, DSHSeq cop1 cop2)
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

Fixpoint tmUnfoldList {A:Type} (names:list string) (e:A): TemplateMonad A :=
  match names with
  | [] => tmReturn e
  | x::xs =>  u <- @tmEval (unfold x) A e ;;
              tmUnfoldList xs u
  end.

Definition reifyMSHCOL
           {A:Type}
           (expr: A)
           (unfold_names: list string)
           (res_name: string)
           (res_globals_name: string)
  : TemplateMonad unit :=
  let unfold_names := List.app unfold_names ["SHFamilyOperatorCompose"; "IgnoreIndex"; "Fin1SwapIndex"; "Fin1SwapIndex2"; "IgnoreIndex2"; "mult_by_nth"; "plus"; "mult"; "const"] in
  eexpr <- tmUnfoldList unfold_names expr ;;
        ast <- @tmQuote A eexpr ;;
        ast <- @tmQuote A eexpr ;;
        mt <- tmQuote (mem_block) ;;
        (* Fake resolver for 2 vars *)
        let res := Fake_var_resolver (ID_var_resolver) 2 in
        '(globals, dshcol) <- compileMSHCOL2DSHCOL res [] ast (PVar 1) (PVar 0) ;;
        dshcol' <- tmEval cbv dshcol ;;
        d_dshcol <- tmDefinition res_name dshcol' ;;
        d_globals <- tmDefinition res_globals_name globals
        ;; tmReturn tt.

(*
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.
Require Import Helix.HCOL.HCOL.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.SigmaHCOLRewriting.
Import MDSHCOLOnCarrierA.


Definition foo := MSHPointwise (n:=4) (IgnoreIndex (fun x => abs x)).

Definition foo0 := fun a => MSHPointwise (n:=4) (mult_by_nth a).

Definition foo1 :=
  MSHIReduction (i:=2) CarrierAz minmax.max
                (fun (jf: FinNat 2) =>
                   MSHCompose
                     (MSHBinOp
                        (fun i a b =>
                           IgnoreIndex abs i
                                       (Fin1SwapIndex2 jf
                                                       (IgnoreIndex2 sub) i a b)))

                     (MSHPointwise (n:=2) (IgnoreIndex (fun x => abs x)))
                ).

Definition foo2 := fun a => MHTSUMUnion plus
                                     (MSHPointwise (n:=4) (IgnoreIndex (fun x => abs x)))
                                     (MSHPointwise (n:=4) (mult_by_nth a)).


Run TemplateProgram (reifyMSHCOL foo2 ["foo2"] "bar" "bar_globals").

Print bar_globals.
Print bar.
*)
