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

Inductive DSHCOLType :=
| DSHnat : DSHCOLType
| DSHCarrierA : DSHCOLType
| DSHMemBlock : DSHCOLType.

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

Print Instances MSHOperator_Facts.

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
            toDSHCOLType (tmReturn vt) ;;
            compileMSHCOL2DSHCOL ((nNamed n,vt)::vars) x_i y_i heap_i b
  | tApp (tConst opname _) args =>
    match parse_SHCOL_Op_Name opname, args with
    | Some n_eUnion, [o ; b ; _] =>
      tmPrint "eUnion" ;;
              no <- tmUnquoteTyped nat o ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, heap_i, DSHAssign (x_i,NConst 0) (y_i, bc))
    | Some n_eT, [i ; b ; _] =>
      tmPrint "eT" ;;
              ni <- tmUnquoteTyped nat i ;;
              bc <- compileNExpr b ;;
              tmReturn (vars, heap_i, DSHAssign (x_i, bc) (y_i, NConst 0))
    | Some n_SHPointwise, [n ; f ; _ ] =>
      tmPrint "SHPointwise" ;;
              nn <- tmUnquoteTyped nat n ;;
              df <- compileDSHIUnCarrierA f ;;
              tmReturn (vars, heap_i, DSHIMap nn x_i y_i df)
    | Some n_SHBinOp, [o ; f ; _]
      =>
      tmPrint "SHBinOp" ;;
              no <- tmUnquoteTyped nat o ;;
              df <- compileDSHIBinCarrierA f ;;
              tmReturn (vars, heap_i, DSHBinOp no x_i y_i df )
    | Some n_SHInductor, [n ; f ; _ ; z] =>
      tmPrint "SHInductor" ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              nc <- compileNExpr n ;;
              df <- compileDSHBinCarrierA f ;;
              tmReturn (vars, heap_i,
                        DSHPower nc (x_i, NConst 0) (y_i, NConst 0) df zconst)
    | Some n_IUnion, [i ; o ; n ; op_family] =>
      tmPrint "IUnion" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              c' <- compileMSHCOL2DSHCOL vars x_i y_i heap_i op_family ;;
              let '(_,heap_i',rr) := c' in
              tmReturn (vars, heap_i', DSHLoop nn rr)
    | Some n_IReduction, [i ; o ; n ; z; f ; _ ; op_family] =>
      tmPrint "IReduction" ;;
              ni <- tmUnquoteTyped nat i ;;
              no <- tmUnquoteTyped nat o ;;
              nn <- tmUnquoteTyped nat n ;;
              zconst <- tmUnquoteTyped CarrierA z ;;
              let t_i := heap_i in
              c' <- compileMSHCOL2DSHCOL vars x_i t_i (S heap_i) op_family ;;
                 df <- compileDSHBinCarrierA f ;;
                 let '(_, heap_i', rr) := c' in
                 tmReturn (vars, heap_i',
                           (DSHSeq
                              (DSHSeq
                                 (DSHAlloc no t_i)
                                 (DSHMemInit no y_i zconst))
                              (DSHLoop nn
                                       (DSHSeq
                                          rr
                                          (DSHMemMap2 nn t_i y_i y_i df)))))
    | Some n_SHCompose, [i1 ; o2 ; o3 ; op1 ; op2] =>
      tmPrint "SHCompose" ;;
              ni1 <- tmUnquoteTyped nat i1 ;;
              no2 <- tmUnquoteTyped nat o2 ;;
              no3 <- tmUnquoteTyped nat o3 ;;
              let t_i := heap_i in
              cop2' <- compileMSHCOL2DSHCOL vars x_i t_i (S heap_i) op2 ;;
                    let '(_,heap_i',cop2) := cop2' in
                    cop1' <- compileMSHCOL2DSHCOL vars t_i y_i heap_i' op1 ;;
                          let '(_, heap_i'', cop1) := cop1' in
                          tmReturn (vars, heap_i'',
                                    (DSHSeq
                                       (DSHAlloc no2 t_i)
                                       (DSHSeq cop2 cop1)))
    | Some n_HTSUMUnion, [i ; o ; dot ; op1 ; op2] =>
      tmPrint "HTSumunion" ;;
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
                                   (DSHSeq
                                      (DSHAlloc no tyf_i)
                                      (DSHSeq
                                         (DSHAlloc no tyg_i)
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
    dt <- toDSHCOLType (tmReturn t) ;;
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

(* Heterogenous relation of semantic equivalence of structurally correct SHCOL and DSHCOL operators *)

(*
Open Scope list_scope.
Definition SHCOL_DSHCOL_equiv {i o:nat} {svalue:CarrierA} {fm}
           (σ: evalContext)
           (s: @SHOperator fm i o svalue)
           `{facts: !SHOperator_Facts fm s}
           `{SHM: !SHOperator_Mem  s}
           (d: DSHOperator) (x_i y_i: nat): Prop
  := forall (Γ: evalContext) (x:svector fm i),

    let Γ := σ ++ in

    (List.nth_error Γ' x_i = Some (svector_to_mem_block x)) ->
    match evalDSHOperator Γ' d (estimateFuel d), mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end.


    let xm := svector_to_mem_block x in (* input as mem_block *)
    let ym := mem_empty in (* placeholder for output *)
    let x_i := List.length (σ ++ Γ) in
    let y_i := x_i + 1 in
    let Γ := σ ++ Γ ++ [DSHmemVal xm ; DSHmemVal ym]  in (* add them to context *)
    let fuel := estimateFuel d in
    match evalDSHOperator Γ d fuel, mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end
    | None, None  => True
    | _, _ => False
    end.
*)

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

(*
Theorem SHCompose_DSHCompose
        {i1 o2 o3} {svalue} {fm}
        (σ: evalContext)
        (f: @SHOperator fm o2 o3 svalue)
        (g: @SHOperator fm i1 o2 svalue)
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
    some_none.
Qed.

Theorem SHCOL_DSHCOL_equiv_SafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaSafeFlags i o svalue)
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
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaFlags i o svalue)
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
        {svalue: CarrierA}
        {fm}
        (σ: evalContext)
        (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (df: DSHIBinCarrierA)
  :
    (forall (Γ: evalContext) j a b, Some (f j a b) = evalIBinCarrierA
                                                       (σ ++ Γ)
                                                       df (proj1_sig j) a b) ->
    @SHCOL_DSHCOL_equiv (o+o) o svalue fm σ
                        (@SHBinOp fm svalue o f pF)
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
        {svalue: CarrierA}
        {fm}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (ddot: DSHBinCarrierA)
        (σ: evalContext)
        (f g: @SHOperator fm i o svalue)
        (df dg: DSHOperator i o)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    (forall (Γ:evalContext) a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@HTSUMUnion fm i o svalue dot dot_mor scompat f g)
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
    some_none.
  -
    specialize (Ef x).
    rewrite Heqo0 in Ef.
    some_none.
Qed.

Theorem eUnion_DSHeUnion
        {fm}
        (σ: evalContext)
        {o b:nat}
        (bc: b < o)
        (svalue: CarrierA)
        (db: NExpr)
  :
    (forall Γ, Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ (svalue:=svalue)
                       (eUnion fm bc)
                       (DSHeUnion db svalue).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
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

 *)

               (*
Definition SHOperatorFamily_DSHCOL_equiv
           {i o n:nat}
           {svalue: CarrierA}
           {fm}
           (Γ: evalContext)
           (op_family: @SHOperatorFamily fm i o n svalue)
           {op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc))}
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
           (d: DSHOperator) : Prop :=
  forall (j:nat) (jc:j<n), SHCOL_DSHCOL_equiv (DSHnatVal j :: Γ)
                                       (op_family (mkFinNat jc))
                                       d.
                *)

(*
Section Expr_NVar_subst_S.

  Local Ltac twoarg := simpl;
                       repeat break_match; auto; try some_none;
                       f_equiv;
                       repeat some_inv;
                       crush.

  Fact NExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : NExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
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
        repeat break_match ; subst; try reflexivity; try some_none.
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
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
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
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
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

Fact evalDiamond_NVar_subst_S:
  ∀ (i o n : nat) (dot : DSHBinCarrierA) (initial : CarrierA)
    (dop_family : DSHOperator i o) (y : vector CarrierA i)
    (j : nat), (∀ (y0 : vector CarrierA i) (pos : nat) (Γ Γs : evalContext),
                   listsDiffByOneElement Γ Γs pos
                   → isNth Γ pos (DSHnatVal j)
                   → isNth Γs pos (DSHnatVal (S j))
                   → evalDSHOperator Γs dop_family y0 =
                     evalDSHOperator Γ
                                     (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1))
                                                            dop_family) y0)
               → ∀ (pos : nat) (Γ Γs : evalContext), listsDiffByOneElement Γ Γs pos
                                                     → isNth Γ pos (DSHnatVal j)
                                                     → isNth Γs pos (DSHnatVal (S j))
                                                     →
                                                     evalDiamond
                                                       (evalBinCarrierA Γs dot)
                                                       initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γs)
                                                             dop_family y)) =
                                                     evalDiamond
                                                       (evalBinCarrierA Γ
                                                                        (AExpr_natvar_subst
                                                                           (pos + 2)
                                                                           (NPlus
                                                                              (if
                                                                                  PeanoNat.Nat.eq_dec pos pos
                                                                                then NVar (pos + 2)
                                                                                else NVar pos)
                                                                              (NConst 1)) dot)) initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γ)
                                                             (DSHOperator_NVar_subt
                                                                (S pos)
                                                                (NPlus
                                                                   (if
                                                                       PeanoNat.Nat.eq_dec pos pos
                                                                     then NVar (S pos)
                                                                     else NVar pos)
                                                                   (NConst 1)) dop_family) y)).
Proof.
  intros i o n dot initial dop_family y j IHdop_family pos Γ Γs L L0 L1.


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
Qed.

Fact DSHOperator_NVar_subst_S
     {i o : nat}
     (Γ Γs : evalContext)
     (dop_family : DSHOperator i o)
     (pos:nat)
     (y : vector CarrierA i)
     (j : nat):
  listsDiffByOneElement Γ Γs pos ->
  isNth Γ pos (DSHnatVal j) ->
  isNth Γs pos (DSHnatVal (S j)) ->
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
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    reflexivity.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
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
    end; try some_none; try reflexivity.


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
        -- some_none.
        -- some_none.
    }

    repeat break_match; try some_none; try reflexivity.
    f_equiv.
    f_equiv.
    some_inv.
    apply C.
  -
    simpl.
    apply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    eapply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b) by (apply IHdop_family2; auto)
    end.
    repeat break_match; try reflexivity; try some_none.
    some_inv.
    rewrite <- C.
    eapply IHdop_family1; auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C0: a = b) by (apply IHdop_family1; auto)
    end.

    assert(C1: evalDSHOperator Γs dop_family2 y = evalDSHOperator Γ
                                                                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family2) y) by (apply IHdop_family2; auto).

    repeat break_match; try reflexivity; try some_none; try contradiction.
    repeat some_inv.
    rewrite C0, C1.
    apply vsequence_option_proper.
    rewrite 2!Vmap2_as_Vbuild.
    apply Vbuild_proper.
    intros m mc.
    unfold evalBinCarrierA.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    --
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    -- apply L0.
    -- apply L1.
Qed.

Theorem IReduction_DSHIReduction
        {i o n: nat}
        {svalue: CarrierA}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n svalue)
        (ddot: DSHBinCarrierA)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    (forall Γ a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@IReduction svalue i o n dot pdot scompat op_family)
                       (@DSHIReduction i o n ddot svalue dop_family).
Proof.
  intros Hdot Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

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
      clear IHn pdot Hdot ddot x Γ.
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
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
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
        {svalue: CarrierA}
        {n: nat}
        (f: FinNat n -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (df: DSHIUnCarrierA)
        (σ: evalContext)
  :
    (forall Γ j a, Some (f j a) = evalIUnCarrierA (σ++Γ) df (proj1_sig j) a) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHPointwise fm svalue  n f pF)
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
        {svalue: CarrierA}
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
                       (@SHInductor fm svalue n f pF initial)
                       (DSHInductor dn df initial).
Proof.
  intros E Edot.
  intros Γ x.
  specialize (E Γ).
  specialize (Edot Γ).
  simpl evalDSHOperator.
  break_match; try some_none.
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
        some_none.
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
        {svalue: CarrierA}
        {i b:nat}
        (bc: b < i)
        (db: NExpr)
        (σ: evalContext)
  :
    (forall (Γ:evalContext), Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ
                       (@eT fm svalue i b bc)
                       (@DSHeT i (db:NExpr)).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
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
        {i o n: nat}
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n zero)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@ISumUnion i o n op_family)
                       (@DSHIUnion i o n (APlus (AVar 1) (AVar 0)) 0 dop_family).
Proof.
  (* significant code duplication with `IReduction_DSHIReduction` *)
  intros Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

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
                                            (shrink_op_family_up Monoid_RthetaFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn x Γ.
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
        remember (@Vmap (Rtheta' Monoid_RthetaFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaFlags) i x) as y.
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
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaFlags)) x))
      with
        (Some
           (densify Monoid_RthetaFlags
                    (op Monoid_RthetaFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    assert(Hdot: forall Γ a b, Some (CarrierAplus a b) = evalBinCarrierA (σ++Γ) (APlus (AVar 1) (AVar 0))  a b) by reflexivity.

    setoid_rewrite <- Hdot.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply CarrierAPlus_proper.
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

(* Attemts to solve evaluation lemmas on DSHCOL Aexpr *)
Ltac solve_evalAexp :=
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ H: FinNat _ |- _ ] => destruct H
         | [ |- evalAexp _ _ = Some _] =>
           unfold Fin1SwapIndex, const, mult_by_nth; simpl;
           try (repeat break_match; try some_none; try congruence)
         | [H: Some ?A ≡ Some ?b |- _ ] => inversion H; clear H
         | [H: Some ?A = Some ?b |- _ ] => apply Some_inj_equiv in H
         | [ |- ?a _ = ?a _ ] => f_equiv
         | [ |- Vnth ?a _ ≡ Vnth ?a _] => try apply Vnth_eq
         | [ |- _ ] => auto
         end.

(* Solves obligations generated by `reifySHCOL` *)
Ltac solve_reifySHCOL_obligations E :=
  intros ;
  unfold E ;
  match goal with
  | [ |- SHCOL_DSHCOL_equiv _ _ ?d] => unfold d
  end ;
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ |- SHCOL_DSHCOL_equiv _ (SHCompose _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_SafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (UnSafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_UnSafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (SHBinOp _ _) (DSHBinOp _) ] => apply SHBinOp_DSHBinOp
         | [ |- SHCOL_DSHCOL_equiv _ (HTSUMUnion _ _ _ _) (DSHHTSUMUnion _ _ _) ] => apply HTSUMUnion_DSHHTSUMUnion
         | [ |- SHCOL_DSHCOL_equiv _ (eUnion _ _) (DSHeUnion _ _)] => apply eUnion_DSHeUnion
         | [  |- SHCOL_DSHCOL_equiv _ (IReduction _ _) (DSHIReduction _ _ _ _)] => apply IReduction_DSHIReduction
         | [ |- SHOperatorFamily_DSHCOL_equiv _ _ _ ] => unfold SHOperatorFamily_DSHCOL_equiv
         | [ |- SHCOL_DSHCOL_equiv _ (SHFamilyOperatorCompose _ _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SHPointwise _ _) (DSHPointwise _) ] =>  apply SHPointwise_DSHPointwise
         | [ |- SHCOL_DSHCOL_equiv _ (SHInductor _ _ _ _) (DSHInductor _ _ _)] => apply SHInductor_DSHInductor
         | [ |- SHCOL_DSHCOL_equiv _ (eT _ _) (DSHeT _)] => apply eT_DSHeT
         | [ |- SHCOL_DSHCOL_equiv _(ISumUnion _) (DSHIUnion _ _ _ _) ] => apply ISumUnion_DSHISumUnion
         | [ |- Some _ = evalIUnCarrierA _ _ _ _ ] => unfold evalIUnCarrierA; symmetry; solve_evalAexp
         | [ |- _ ] => try reflexivity
         end.
*)
