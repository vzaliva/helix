Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Coq.Strings.String.

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
    |}, Anon (Z.of_nat (block_count st))).

(* Returns local ID and a new state where it is incremented *)
Definition incLocal (st:IRState): (IRState*raw_id) :=
  ({|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := vars st
    |}, Anon (Z.of_nat (local_count st))).

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
    let (st,retid) := incLocal st in
    let (st,bid) := incBlock st in
    (st, name,
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
         (st: IRState)
         (x y: local_id)
         (nextblock: block_id)
         (fshcol: @FSHOperator ft i o): (IRState * block_id * list block)
  := match fshcol with
     | FSHeUnion o b z => (st, nextblock, [])
     | FSHeT i b => (st, nextblock, [])
     | FSHPointwise i f => (st, nextblock, [])
     | FSHBinOp o f => (st, nextblock, [])
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
                         df_instrs      := body
                       |}
                    ]
      ).
