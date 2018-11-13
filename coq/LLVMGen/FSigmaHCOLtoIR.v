Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Coq.Strings.String.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.

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


Inductive FSHValType {ft:FloatT}: Type :=
| FSHnatValType: FSHValType
| FSHFloatValType: FSHValType
| FSHvecValType {n:nat}: FSHValType.

Require Import Coq.Lists.List.
Import ListNotations.

Definition getIRType
           {ft: FloatT}
           (t: @FSHValType ft): typ :=
  match t with
  | FSHnatValType => TYPE_I 64%Z (* TODO: config *)
  | FSHFloatValType => match ft with
                      | Float32 => TYPE_Float
                      | Float64 => TYPE_Double
                      end
  | FSHvecValType n => match ft with
                      | Float32 => TYPE_Array (Z.of_nat n) TYPE_Float
                      | Float64 => TYPE_Array (Z.of_nat n) TYPE_Double
                      end
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
              g_align        := Some 16%Z ; (* TODO: not for all? *)
            |}
       ).

Section WithState.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition IRState : Type :=
    (
      nat * (* block_count *)
      nat * (* local_count *)
      nat * (* void_count *)
      (list (raw_id * typ)) (* vars *)
    ).

  Definition newState: IRState := (0,0,0,[]).

  Variable state_m : Type -> Type.
  Context {Monad_m: Monad state_m}.
  Context {State_m: MonadState IRState state_m}.

  Definition incBlock (st:IRState): state_m unit :=
    let '(block_count, local_count, void_count, vars) := st in
    put (
        S block_count,
        local_count,
        void_count,
        vars
      ).

  Definition getNextBlock (st:IRState): block_id :=
    let '(block_count, _, _ , _ ) := st in
    Anon (Z.of_nat block_count).

  Definition incLocal (st:IRState): state_m unit :=
    let '(block_count, local_count, void_count, vars) := st in
    put (
        block_count,
        S local_count,
        void_count,
        vars
      ).

  Definition getNextLocal (st:IRState): local_id :=
    let '(_, local_count, _, _) := st in
    Anon (Z.of_nat local_count).

  Definition incVoid (st:IRState): state_m unit:=
    let '(block_count, local_count, void_count, vars) := st in
    put (
        block_count,
        local_count,
        S void_count,
        vars
      ).

  Definition getNextVoid (st:IRState): Z :=
    let '(_, _, void_count, _) := st in
    Z.of_nat void_count.

  Definition addVars (st:IRState) (newvars: list (raw_id * typ)): state_m unit :=
    let '(block_count, local_count, void_count, vars) := st in
    put (
        block_count,
        local_count,
        void_count,
        vars ++ newvars
      ).

  Definition allocTempArray
             {ft: FloatT}
             (name: local_id)
             (nextblock: block_id)
             (size: nat): state_m (local_id * block)
    :=
      st <- get ;;
         let retid := getNextLocal st in
         incLocal st ;;
                  let bid := getNextBlock st in
                  ret (name,
                       {|
                         blk_id    := bid ;
                         blk_phis  := [];
                         blk_code  := [(IId name,
                                        INSTR_Alloca (getIRType (@FSHvecValType ft size)) None (Some 16%Z))]; (* TODO: default align to config *)
                         blk_term  := (IId retid, TERM_Br_1 nextblock) (* TODO: IVoid? *)
                       |}).

  Fixpoint genIR
           {i o: nat}
           {ft: FloatT}
           (x y: local_id)
           (nextblock: block_id)
           (fshcol: @FSHOperator ft i o) {struct fshcol}
    : state_m (block_id * list block)
    := match fshcol with
       | FSHeUnion o b z => ret (nextblock, [])
       | FSHeT i b => ret (nextblock, [])
       | FSHPointwise i f => ret (nextblock, [])
       | FSHBinOp o f => ret (nextblock, [])
       | FSHInductor n f initial => ret (nextblock, [])
       | FSHIUnion i o n dot initial x => ret (nextblock, [])
       | FSHIReduction i o n dot initial x => ret (nextblock, [])
       | FSHCompose i1 o2 o3 f g =>
         st <- get ;;
            let tmpid := getNextLocal st in
            incLocal st ;;
                     fm <- genIR tmpid y nextblock f ;;
                     let '(fb, f') := fm in
                     gm <- genIR x tmpid fb g ;;
                        let '(gb, g') := gm in
                        am <- @allocTempArray ft tmpid fb o2 ;;
                           let '(alloid, tmpalloc) := am in
                           ret (alloid, [tmpalloc]++g'++f')
       | FSHHTSUMUnion i o dot f g => ret (nextblock, [])
       end.

  Definition LLVMGen_m
             {i o: nat}
             {ft: FloatT}
             (globals: list (string* (@FSHValType ft)))
             (fshcol: @FSHOperator ft i o) (funname: string)
    : state_m (toplevel_entities (list block))
    :=
      let x := Name "X" in
      let xtyp := TYPE_Pointer (getIRType (@FSHvecValType ft i)) in
      let y := Name "Y" in
      let ytyp := TYPE_Pointer (getIRType (@FSHvecValType ft o)) in

      st <- get ;; addVars st (List.map
                                (fun g:(string* (@FSHValType ft)) =>
                                   let (n,t) := g in (Name n, getIRType t))
                                globals) ;;
         st <- get ;; addVars st [(x, xtyp)] ;;
         st <- get ;;
         let rid := getNextBlock st in
         incBlock st ;;
                  st <- get ;;
                  let rsid := getNextBlock st in
                  let retblock :=
                      {|
                        blk_id    := rid ;
                        blk_phis  := [];
                        blk_code  := [];
                        blk_term  := (IId rsid, TERM_Ret_void)
                      |} in
                  incBlock st ;;
                           mbody <- genIR x y rid fshcol ;;
                           let '(_,body) := mbody in
                           ret
                             (genIRGlobals globals ++
                                           [TLE_Definition
                                              {|
                                                df_prototype   :=
                                                  {|
                                                    dc_name        := Name funname;
                                                    dc_type        := TYPE_Function TYPE_Void [xtyp;ytyp ] ;
                                                    dc_param_attrs := ([],[[PARAMATTR_Align 16%Z] ; (* TODO: align to config *)
                                                                             [PARAMATTR_Align 16%Z]]);
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
                                                df_instrs      := body ++ [retblock]
                                              |}
                                           ]
                             ).

End WithState.

Definition LLVMGen
           {i o: nat}
           {ft: FloatT}
           (globals: list (string* (@FSHValType ft)))
           (fshcol: @FSHOperator ft i o) (funname: string)
  : toplevel_entities (list block)
  :=
    evalState (LLVMGen_m (state IRState) globals fshcol funname) newState.
