Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

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

Record IRState :=
  mkIRstate
    {
      block_count: nat ;
      local_count: nat ;
      void_count : nat ;
      vars: list (raw_id * typ)
    }.

Definition newState: IRState :=
  {|
    block_count := 0 ;
    local_count := 0 ;
    void_count  := 0 ;
    vars := []
  |}.

(* Returns block ID and a new state where it is incremented *)
Definition incBlock (st:IRState): (IRState*block_id) :=
  ({|
      block_count := S (block_count st);
      local_count := local_count st ;
      void_count := void_count st ;
      vars := vars st
    |}, Raw (Z.of_nat (block_count st))).

(* Returns local ID and a new state where it is incremented *)
Definition incLocal (st:IRState): (IRState*raw_id) :=
  ({|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := vars st
    |}, Raw (Z.of_nat (local_count st))).

(* Returns void ID and a new state where it is incremented *)
Definition incVoid (st:IRState): (IRState*int) :=
  ({|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := S (void_count st) ;
      vars := vars st
    |}, Z.of_nat (void_count st)).

Definition addVars (st:IRState) (newvars: list (raw_id * typ)): IRState :=
  {|
    block_count := block_count st ;
    local_count := local_count st ;
    void_count  := void_count st ;
    vars := vars st ++ newvars
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
                      INSTR_Alloca (getIRType (@FSHvecValType ft size)) None (Some 16%Z))]; (* TODO: default align to config *)
       blk_term  := (IVoid retid, TERM_Br_1 nextblock) (* TODO: IVoid? *)
     |}).


Definition genFSHBinOp
           {i o: nat}
           {ft: FloatT}
           (st: IRState)
           (x y: local_id)
           (nextblock: block_id)
           (f:@FSHIBinFloat ft)
  : (IRState * block_id * list block)
  :=
    let '(st, entryblock) := incBlock st in
    let '(st, retentry) := incVoid st in
    let '(st, loopblock) := incBlock st in
    let '(st, retloop) := incVoid st in
    let '(st, storeid) := incVoid st in
    let '(st, loopvar) := incLocal st in
    let '(st, loopcond) := incLocal st in
    let '(st, nextvar) := incLocal st in
    let '(st, px) := incLocal st in
    let '(st, py) := incLocal st in
    let '(st, v) := incLocal st in
    let '(st, u) := incLocal st in
    let xtyp := getIRType (@FSHvecValType ft i) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (@FSHvecValType ft o) in
    let yptyp := TYPE_Pointer ytyp in
    (st, entryblock, [
       {|
         blk_id    := entryblock ;
         blk_phis  := [];
         blk_code  := [];
         blk_term  := (IVoid retentry, TERM_Br_1 loopblock)
       |} ;

         {|
           blk_id    := loopblock ;
           blk_phis  := [(loopvar,
                          Phi  (TYPE_I 64%Z (* TODO: config *))
                               [(entryblock, EXP_Integer 0%Z) ;
                                  (loopblock, EXP_Ident (ID_Local loopvar))
                               ]
                        )];
           blk_code  := [
                         (IId px,  INSTR_Op (OP_GetElementPtr
                                               xtyp (xptyp, (EXP_Ident (ID_Local x)))
                                               [(TYPE_I 64%Z, EXP_Integer 0%Z);
                                                  (TYPE_I 64%Z,(EXP_Ident (ID_Local loopvar)))]

                         ));

                           (IId v, INSTR_Load false TYPE_Double
                                              (TYPE_Pointer TYPE_Double,
                                               (EXP_Ident (ID_Local px)))
                                              (Some 8%Z)); (*TODO: not sure about 8 *)


                           (* TODO:
                             %u = call double %f (double %v)
                            *)

                           (IId py,  INSTR_Op (OP_GetElementPtr
                                                 ytyp (yptyp, (EXP_Ident (ID_Local y)))
                                                 [(TYPE_I 64%Z, EXP_Integer 0%Z);
                                                    (TYPE_I 64%Z,(EXP_Ident (ID_Local loopvar)))]

                           ));


                           (IVoid storeid, INSTR_Store false
                                                       (TYPE_Double, (EXP_Ident (ID_Local u)))
                                                       (TYPE_Pointer TYPE_Double,
                                                        (EXP_Ident (ID_Local py)))
                                                       (Some 8%Z)); (*TODO: not sure about 8 *)


                           (IId nextvar, INSTR_Op (OP_IBinop (Add false false)
                                                             (TYPE_I 64%Z (* TODO: config *))
                                                             (EXP_Ident (ID_Local loopvar))
                                                             (EXP_Integer 1%Z))) ;
                           (IId loopcond, INSTR_Op (OP_ICmp Eq
                                                            (TYPE_I 64%Z (* TODO: config *))
                                                            (EXP_Ident (ID_Local loopvar))
                                                            (EXP_Integer (Z.of_nat o))))

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
         (fshcol: @FSHOperator ft i o): (IRState * block_id * list block)
  := match fshcol with
     | FSHeUnion o b z => (st, nextblock, [])
     | FSHeT i b => (st, nextblock, [])
     | FSHPointwise i f => (st, nextblock, [])
     | FSHBinOp o f => @genFSHBinOp i o ft st x y nextblock f
     | FSHInductor n f initial => (st, nextblock, [])
     | FSHIUnion i o n dot initial x => (st, nextblock, [])
     | FSHIReduction i o n dot initial x => (st, nextblock, [])
     | FSHCompose i1 o2 o3 f g =>
       let '(st, tmpid) := incLocal st in
       let '(st, fb, f') := genIR st tmpid y nextblock f in
       let '(st, gb, g') := genIR st x tmpid fb g in
       let '(st, alloid, tmpalloc) := @allocTempArray ft st tmpid fb o2 in
       (st, alloid, [tmpalloc]++g'++f')
     | FSHHTSUMUnion i o dot f g => (st, nextblock, [])
     end.

Definition LLVMGen
           {i o: nat}
           {ft: FloatT}
           (globals: list (string* (@FSHValType ft)))
           (fshcol: @FSHOperator ft i o) (funname: string)
  :option (toplevel_entities (list block))
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
                      let (n,t) := g in (Name n, getIRType t))
                   globals) in

    let st := addVars st [(x, xtyp)] in

    let (st,rid) := incBlock st in
    let (st,rsid) := incBlock st in
    let retblock :=
        {|
          blk_id    := rid ;
          blk_phis  := [];
          blk_code  := [];
          blk_term  := (IId rsid, TERM_Ret_void)
        |} in
    let (st,body) := genIR st x y rid fshcol in
    let body := body ++ [retblock] in
    Some
      (genIRGlobals globals ++
                    [TLE_Definition
                       {|
                         df_prototype   :=
                           {|
                             dc_name        := Name funname;
                             dc_type        := TYPE_Function TYPE_Void [xtyp; ytyp] ;
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
                         df_instrs      := body
                       |}
                    ]
      ).
