Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.


(* Temporary workaround until coq-ext-lib is updated in OPAM *)
Notation "' pat <- c1 ;; c2" :=
    (@pbind _ _ _ _ _ c1 (fun x => match x with pat => c2 end))
      (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.


Program Definition FloatV64Zero := Float64V (@FF2B _ _ (F754_zero false) _).

Program Definition FloatV64One := Float64V (BofZ _ _ _ _ 1%Z).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* sample definition to be moved to DynWin.v *)
Definition DynWinFSHCOL: @FSHOperator Float64 (1 + 4) 1 :=
  FSHCompose (FSHBinOp (AZless (AVar 1) (AVar 0)))
   (FSHHTSUMUnion (APlus (AVar 1) (AVar 0))
      (FSHCompose (FSHeUnion (NConst 0) FloatV64Zero)
         (FSHIReduction 3 (APlus (AVar 1) (AVar 0)) FloatV64Zero
            (FSHCompose
               (FSHCompose (FSHPointwise (AMult (AVar 0) (ANth 3 (VVar 3) (NVar 2))))
                  (FSHInductor (NVar 0) (AMult (AVar 1) (AVar 0)) FloatV64One))
               (FSHeT (NConst 0)))))
      (FSHCompose (FSHeUnion (NConst 1) FloatV64Zero)
         (FSHIReduction 2 (AMax (AVar 1) (AVar 0)) FloatV64Zero
            (FSHCompose (FSHBinOp (AAbs (AMinus (AVar 1) (AVar 0))))
               (FSHIUnion 2 (APlus (AVar 1) (AVar 0)) FloatV64Zero
                  (FSHCompose (FSHeUnion (NVar 0) FloatV64Zero)
                     (FSHeT
                        (NPlus (NPlus (NConst 1) (NMult (NVar 1) (NConst 1)))
                           (NMult (NVar 0) (NMult (NConst 2) (NConst 1))))))))))).



(* Placeholder section for config variables. Probably should be a
module in future *)
Section Config.
  Definition IntType := TYPE_I 64%Z.
  Definition ArrayPtrParamAttrs := [ PARAMATTR_Align 16%Z ].
  Definition GlobalPtrAlignment := Some 16%Z.
  Definition TempPtrAlignment := Some 16%Z.
End Config.

Inductive FSHValType {ft:FloatT}: Type :=
| FSHnatValType: FSHValType
| FSHFloatValType: FSHValType
| FSHvecValType {n:nat}: FSHValType.

Definition FloatTtyp (ft: FloatT) : typ :=
  match ft with
  | Float32 => TYPE_Float
  | Float64 => TYPE_Double
  end.

Definition getIRType
           {ft: FloatT}
           (t: @FSHValType ft): typ :=
  match t with
  | FSHnatValType => IntType
  | FSHFloatValType => FloatTtyp ft
  | FSHvecValType n => TYPE_Array (Z.of_nat n) (FloatTtyp ft)
  end.

Definition genIRGlobals
           {ft: FloatT}:
  (list (string* (@FSHValType ft))) -> (toplevel_entities (list block))
  := List.map
       (fun g:(string* (@FSHValType ft)) =>
          let (n,t) := g in
          TLE_Global {|
              g_ident        := Name n;
              g_typ          := getIRType t ;
              g_constant     := false ; (* TODO: maybe true? *)
              g_exp          := None ;
              g_linkage      := Some LINKAGE_External ;
              g_visibility   := None ;
              g_dll_storage  := None ;
              g_thread_local := None ;
              g_unnamed_addr := true ;
              g_addrspace    := None ;
              g_externally_initialized:= true ;
              g_section      := None ;
              g_align        := GlobalPtrAlignment ;
            |}
       ).

Record IRState :=
  mkIRstate
    {
      block_count: nat ;
      local_count: nat ;
      void_count : nat ;
      vars: list (ident * typ)
    }.

Definition newState: IRState :=
  {|
    block_count := 0 ;
    local_count := 0 ;
    void_count  := 0 ;
    vars := []
  |}.

(* TODO: move. Lifted from Software foundations *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match Nat.modulo n 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := append d acc in
  match time with
    | 0 => acc'
    | S time' =>
      match Nat.div n 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.
Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

(* Returns block ID and a new state where it is incremented *)
Definition incBlock (st:IRState): (IRState*block_id) :=
  ({|
      block_count := S (block_count st);
      local_count := local_count st ;
      void_count := void_count st ;
      vars := vars st
    |}, Name (append "b" (string_of_nat (block_count st)))).

(* Returns local ID and a new state where it is incremented *)
Definition incLocal (st:IRState): (IRState*raw_id) :=
  ({|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := vars st
    |}, Name (append "l" (string_of_nat (local_count st)))).

(* Returns void ID and a new state where it is incremented *)
Definition incVoid (st:IRState): (IRState*int) :=
  ({|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := S (void_count st) ;
      vars := vars st
    |}, Z.of_nat (void_count st)).

Definition addVars (st:IRState) (newvars: list (ident * typ)): IRState :=
  {|
    block_count := block_count st ;
    local_count := local_count st ;
    void_count  := void_count st ;
    vars := newvars ++ vars st
  |}.

(* TODO: move *)
Fixpoint drop_err {A:Type} (n:nat) (lst:list A) : option (list A)
  := match n, lst with
     | O, xs => Some xs
     | S n', (_::xs) => drop_err n' xs
     | _, _ => None
     end.

Definition dropVars (st:IRState) (n: nat): option IRState :=
  vars' <- drop_err n (vars st) ;;
        ret {|
          block_count := block_count st ;
          local_count := local_count st ;
          void_count  := void_count st ;
          vars := vars'
        |}.

Definition allocTempArray
           {ft: FloatT}
           (st: IRState)
           (name: local_id)
           (nextblock: block_id)
           (size: nat): (IRState * local_id * block)
  :=
    let (st,retid) := incVoid st in
    let (st,bid) := incBlock st in
    (st, name,
     {|
       blk_id    := bid ;
       blk_phis  := [];
       blk_code  := [(IId name,
                      INSTR_Alloca (getIRType (@FSHvecValType ft size)) None TempPtrAlignment)];
       blk_term  := (IVoid retid, TERM_Br_1 nextblock)
     |}).

Fixpoint genNExpr
         {ft: FloatT}
         (st: IRState)
         (nexp: @NExpr ft) :
  option (IRState * exp * code) :=
  match nexp with
  | NVar n => p <- List.nth_error (vars st) n ;;
               (* TODO: type check *)
               Some (st, EXP_Ident (fst p), [])
  | NConst v => Some (st, EXP_Integer (Z.of_nat v), [])
  | NDiv a b => None (* TODO *)
  | NMod a b => None (* TODO *)
  | NPlus a b => None (* TODO *)
  | NMinus a b => None (* TODO *)
  | NMult a b => None (* TODO *)
  | NMin a b => None (* TODO *)
  | NMax a b => None (* TODO *)
  end.

Fixpoint genFExpr
         {ft: FloatT}
         (st: IRState)
         (fexp: @FExpr ft) :
  option (IRState * exp * code) :=
  match fexp with
  | AVar n => p <- List.nth_error (vars st) n ;;
               (* TODO: type check *)
               Some (st, EXP_Ident (fst p), [])
  | AConst (Float64V v) => Some (st, EXP_Float v, [])
  | AConst (Float32V _) => None (* 32-bit constants are not supported for now *)
  | ANth n v i => None (* TODO *)
  | AAbs v => None (* TODO *)
  | APlus a b => None (* TODO *)
  | AMinus a b => None (* TODO *)
  | AMult a b => None (* TODO *)
  | AMin a b => None (* TODO *)
  | AMax a b => None (* TODO *)
  | AZless a b =>
    '(st, aexp, acode) <- genFExpr st a ;;
     '(st, bexp, bcode) <- genFExpr st b ;;
     let '(st, ires) := incLocal st in
     let '(st, fres) := incLocal st in
     Some (st,
           EXP_Ident (ID_Local fres),
           acode ++ bcode ++
                 [(IId ires, INSTR_Op (OP_FCmp FOlt (* TODO: or FUlt? *)
                                               (FloatTtyp ft)
                                               aexp
                                               bexp));
                    (IId fres, INSTR_Op (OP_Conversion
                                           Uitofp
                                           (TYPE_I 1%Z)
                                           (EXP_Ident (ID_Local ires))
                                           (FloatTtyp ft)))
          ])
  end.

Definition genFSHeT
           {i:nat}
           {ft: FloatT}
           (st: IRState)
           (x y: local_id)
           (nextblock: block_id)
           (b: @NExpr ft)
  : option (IRState * block_id * list block)
  :=
    let '(st, entryblock) := incBlock st in
    let '(st, retentry) := incVoid st in
    let '(st, px) := incLocal st in
    let '(st, py) := incLocal st in
    let '(st, v) := incLocal st in
    let xtyp := getIRType (@FSHvecValType ft i) in
    let xptyp := TYPE_Pointer xtyp in
    '(st, nexpr, nexpcode) <- genNExpr st b  ;;
     Some (st , entryblock, [
             {|
               blk_id    := entryblock ;
               blk_phis  := [];
               blk_code  := nexpcode ++ [
                             (IId px,  INSTR_Op (OP_GetElementPtr
                                                   xtyp (xptyp, (EXP_Ident (ID_Local x)))
                                                   [(IntType, EXP_Integer 0%Z);
                                                      (IntType, nexpr)]

                             )) ;
                               (IId v, INSTR_Load false (FloatTtyp ft)
                                                   (TYPE_Pointer (FloatTtyp ft),
                                                    (EXP_Ident (ID_Local px)))
                                                   (Some 8%Z));
                               (* TODO: store *)
                                     ];
               blk_term  := (IVoid retentry, TERM_Br_1 nextblock)
             |}
          ]).

Definition genFSHBinOp
           {n: nat}
           {ft: FloatT}
           (st: IRState)
           (x y: local_id)
           (nextblock: block_id)
           (f:@FSHIBinFloat ft)
  : option (IRState * block_id * list block)
  :=
    let '(st, entryblock) := incBlock st in
    let '(st, retentry) := incVoid st in
    let '(st, loopblock) := incBlock st in
    let '(st, retloop) := incVoid st in
    let '(st, storeid) := incVoid st in
    let '(st, loopvar) := incLocal st in
    let '(st, loopvar2) := incLocal st in
    let '(st, loopcond) := incLocal st in
    let '(st, nextvar) := incLocal st in
    let '(st, px0) := incLocal st in
    let '(st, px1) := incLocal st in
    let '(st, py) := incLocal st in
    let '(st, v0) := incLocal st in
    let '(st, v1) := incLocal st in
    let xtyp := getIRType (@FSHvecValType ft (n+n)) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (@FSHvecValType ft n) in
    let yptyp := TYPE_Pointer ytyp in
    let st := addVars st [(ID_Local v0, (FloatTtyp ft)); (ID_Local v1, (FloatTtyp ft))] in
    '(st, fexpr, fexpcode) <- genFExpr st f ;;
     st <- dropVars st 2 ;;
     Some (st , entryblock, [
             {|
               blk_id    := entryblock ;
               blk_phis  := [];
               blk_code  := [];
               blk_term  := (IVoid retentry, TERM_Br_1 loopblock)
             |} ;

               {|
                 blk_id    := loopblock ;
                 blk_phis  := [(loopvar,
                                Phi IntType
                                    [(entryblock, EXP_Integer 0%Z) ;
                                       (loopblock, EXP_Ident (ID_Local loopvar))
                                    ]
                              )];
                 blk_code  := [
                               (IId px0,  INSTR_Op (OP_GetElementPtr
                                                     xtyp (xptyp, (EXP_Ident (ID_Local x)))
                                                     [(IntType, EXP_Integer 0%Z);
                                                        (IntType,(EXP_Ident (ID_Local loopvar)))]

                               ));

                                 (IId v0, INSTR_Load false (FloatTtyp ft)
                                                     (TYPE_Pointer (FloatTtyp ft),
                                                      (EXP_Ident (ID_Local px0)))
                                                     (Some 8%Z));

                                 (IId loopvar2, INSTR_Op (OP_IBinop (Add false false)
                                                                      IntType
                                                                      (EXP_Ident (ID_Local loopvar))
                                                                      (EXP_Ident (ID_Local loopvar))));


                                 (IId px1,  INSTR_Op (OP_GetElementPtr
                                                        xtyp (xptyp, (EXP_Ident (ID_Local x)))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType,(EXP_Ident (ID_Local loopvar2)))]

                                 ));

                                 (IId v1, INSTR_Load false (FloatTtyp ft)
                                                     (TYPE_Pointer (FloatTtyp ft),
                                                      (EXP_Ident (ID_Local px1)))
                                                     (Some 8%Z))
                             ]


                                ++ fexpcode ++

                                [ (IId py,  INSTR_Op (OP_GetElementPtr
                                                        ytyp (yptyp, (EXP_Ident (ID_Local y)))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType,(EXP_Ident (ID_Local loopvar)))]

                                  ));


                                    (IVoid storeid, INSTR_Store false
                                                                ((FloatTtyp ft), fexpr)
                                                                (TYPE_Pointer (FloatTtyp ft),
                                                                 (EXP_Ident (ID_Local py)))
                                                                (Some 8%Z)); (*TODO: not sure about 8 *)


                                    (IId nextvar, INSTR_Op (OP_IBinop (Add false false)
                                                                      IntType
                                                                      (EXP_Ident (ID_Local loopvar))
                                                                      (EXP_Integer 1%Z))) ;
                                    (IId loopcond, INSTR_Op (OP_ICmp Eq
                                                                     IntType
                                                                     (EXP_Ident (ID_Local loopvar))
                                                                     (EXP_Integer (Z.of_nat n))))

                                ];
                 blk_term  := (IVoid retloop, TERM_Br (TYPE_I 1%Z, EXP_Ident (ID_Local loopcond)) nextblock loopblock)
               |}
          ]).

Fixpoint genIR
         {i o: nat}
         {ft: FloatT}
         (st: IRState)
         (x y: local_id)
         (nextblock: block_id)
         (fshcol: @FSHOperator ft i o):
  option (IRState * block_id * list block)
  := match fshcol with
     | FSHeUnion o b z => Some (st, nextblock, [])
     | FSHeT i b => @genFSHeT i ft st x y nextblock b
     | FSHPointwise i f => Some (st, nextblock, [])
     | FSHBinOp n f => @genFSHBinOp n ft st x y nextblock f
     | FSHInductor n f initial => Some (st, nextblock, [])
     | FSHIUnion i o n dot initial x => Some (st, nextblock, [])
     | FSHIReduction i o n dot initial x => Some (st, nextblock, [])
     | FSHCompose i1 o2 o3 f g =>
       let '(st, tmpid) := incLocal st in
       '(st, fb, f') <- genIR st tmpid y nextblock f ;;
        '(st, gb, g') <- genIR st x tmpid fb g ;;
        let '(st, alloid, tmpalloc) := @allocTempArray ft st tmpid fb o2 in
        Some (st, gb, [tmpalloc]++g'++f')
     | FSHHTSUMUnion i o dot f g =>
       (* Note: 'g' computed before 'f', as in compose *)
       '(st, fb, f') <- genIR st x y nextblock f ;;
        '(st, gb, g') <- genIR st x y fb g ;;
        Some (st, gb, g'++f')
     end.

Definition LLVMGen
           {i o: nat}
           {ft: FloatT}
           (globals: list (string* (@FSHValType ft)))
           (fshcol: @FSHOperator ft i o) (funname: string)
  : option (toplevel_entities (list block))
  :=
    let x := Name "X" in
    let xtyp := TYPE_Pointer (getIRType (@FSHvecValType ft i)) in
    let y := Name "Y" in
    let ytyp := TYPE_Pointer (getIRType (@FSHvecValType ft o)) in
    let st := newState in

    let st :=
        addVars st
                (List.map
                   (fun g:(string* (@FSHValType ft)) =>
                      let (n,t) := g in (ID_Global (Name n), getIRType t))
                   globals) in

    let st := addVars st [(ID_Local x, xtyp)] in

    let (st,rid) := incBlock st in
    let (st,rsid) := incBlock st in
    let retblock :=
        {|
          blk_id    := rid ;
          blk_phis  := [];
          blk_code  := [];
          blk_term  := (IId rsid, TERM_Ret_void)
        |} in
    '(st,body) <- genIR st x y rid fshcol ;;
     let body := body ++ [retblock] in
     Some
       (genIRGlobals globals ++
                     [TLE_Definition
                        {|
                          df_prototype   :=
                            {|
                              dc_name        := Name funname;
                              dc_type        := TYPE_Function TYPE_Void [xtyp; ytyp] ;
                              dc_param_attrs := ([],[ArrayPtrParamAttrs; ArrayPtrParamAttrs]);
                              dc_linkage     := None;
                              dc_visibility  := None;
                              dc_dll_storage := None;
                              dc_cconv       := None;
                              dc_attrs       := [];
                              dc_section     := None;
                              dc_align       := None;
                              dc_gc          := None;
                            |} ;
                          df_args        := [x;y];
                          df_instrs      := body
                        |}
                     ]
       ).
