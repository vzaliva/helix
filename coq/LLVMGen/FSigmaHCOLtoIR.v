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

(* Placeholder section for config variables. Probably should be a
module in future *)
Section Config.
  Definition IntType := TYPE_I 64%Z.
  Definition ArrayPtrParamAttrs := [ PARAMATTR_Align 16%Z ].
  Definition GlobalPtrAlignment := Some 16%Z.
  Definition TempPtrAlignment := Some 16%Z.
End Config.

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

Definition incBlockNamed (st:IRState) (prefix:string): (IRState*block_id) :=
  ({|
      block_count := S (block_count st);
      local_count := local_count st ;
      void_count := void_count st ;
      vars := vars st
    |}, Name (append prefix (string_of_nat (block_count st)))).

Definition incBlock (st:IRState): (IRState*block_id) := incBlockNamed st "b".

Definition incLocalNamed (st:IRState) (prefix:string): (IRState*raw_id) :=
  ({|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := vars st
    |}, Name (append prefix (string_of_nat (local_count st)))).

Definition incLocal (st:IRState): (IRState*raw_id) := incLocalNamed st "l".

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

Definition newLocalVarNamed (st:IRState) (t:typ) (prefix:string): (IRState*raw_id) :=
  let v := Name (append prefix (string_of_nat (local_count st))) in
  ({|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := [(ID_Local v,t)] ++ (vars st)
    |}, v).

Definition newLocalVar (st:IRState) (t:typ): (IRState*raw_id) := newLocalVarNamed st t "l".

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

Definition allocTempArrayCode
           {ft: FloatT}
           (name: local_id)
           (size: nat): code
  :=
    [(IId name, INSTR_Alloca (getIRType (@FSHvecValType ft size)) None TempPtrAlignment)].

Definition allocTempArrayBlock
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
       blk_code  := @allocTempArrayCode ft name size;
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
  option (IRState * exp * code)
  :=
    let gen_binop a b fop :=
        '(st, aexp, acode) <- genFExpr st a ;;
         '(st, bexp, bcode) <- genFExpr st b ;;
         let '(st, res) := incLocal st in
         Some (st,
               EXP_Ident (ID_Local res),
               acode ++ bcode ++
                     [(IId res, INSTR_Op (OP_FBinop fop
                                                    [] (* TODO: list fast_math *)
                                                    (FloatTtyp ft)
                                                    aexp
                                                    bexp))
              ]) in
    let gen_call2 a b f :=
        '(st, aexp, acode) <- genFExpr st a ;;
         '(st, bexp, bcode) <- genFExpr st b ;;
         let '(st, res) := incLocal st in
         let ftyp := FloatTtyp ft in
         Some (st,
               EXP_Ident (ID_Local res),
               acode ++ bcode ++
                     [(IId res, INSTR_Call (ftyp,f)
                                           [(ftyp,aexp); (ftyp,bexp)])
              ]) in
    match fexp with
    | AVar n => p <- List.nth_error (vars st) n ;;
                 (* TODO: type check *)
                 Some (st, EXP_Ident (fst p), [])
    | AConst (Float64V v) => Some (st, EXP_Float v, [])
    | AConst (Float32V _) => None (* 32-bit constants are not supported for now *)
    | ANth n v i => None (* TODO *)
    | AAbs v => None (* TODO *)
    | APlus a b => gen_binop a b FAdd
    | AMinus a b => gen_binop a b FSub
    | AMult a b => gen_binop a b FMul
    | AMin a b => None (* TODO *)
    | AMax a b => match ft with
                 | Float32 => gen_call2 a b (EXP_Ident (ID_Global (Name "fmaxf")))
                 | Float64 => gen_call2 a b (EXP_Ident (ID_Global (Name "fmax")))
                 end
    | AZless a b =>
      (* this is special as requires bool -> double cast *)
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

(* List of blocks with entry point *)
Definition segment:Type := block_id * list block.

(* AKA "pick" *)
Definition genFSHeT
           {i:nat}
           {ft: FloatT}
           (st: IRState)
           (x y: local_id)
           (b: @NExpr ft)
           (nextblock: block_id)
  : option (IRState * segment)
  :=
    let '(st, entryblock) := incBlockNamed st "eT" in
    let '(st, retentry) := incVoid st in
    let '(st, storeid) := incVoid st in
    let '(st, px) := incLocal st in
    let '(st, py) := incLocal st in
    let '(st, v) := incLocal st in
    let xtyp := getIRType (@FSHvecValType ft i) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (@FSHvecValType ft 1) in
    let yptyp := TYPE_Pointer ytyp in
    '(st, nexpr, nexpcode) <- genNExpr st b  ;;
     Some (st , (entryblock, [
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

                                               (IId py,  INSTR_Op (OP_GetElementPtr
                                                                     ytyp (yptyp, (EXP_Ident (ID_Local y)))
                                                                     [(IntType, EXP_Integer 0%Z);
                                                                        (IntType, nexpr)]

                                               ));

                                               (IVoid storeid, INSTR_Store false
                                                                           ((FloatTtyp ft), (EXP_Ident (ID_Local v)))
                                                                           (TYPE_Pointer (FloatTtyp ft),
                                                                            (EXP_Ident (ID_Local py)))
                                                                           (Some 8%Z))

                                           ];
                     blk_term  := (IVoid retentry, TERM_Br_1 nextblock)
                   |}
          ])).

Definition genLoop
           (prefix: string)
           (from to: exp)
           (loopvar: raw_id)
           (loopcontblock: block_id)
           (body_entry: block_id)
           (body_blocks: list block)
           (init_code: code)
           (st: IRState)
           (nextblock: block_id)
  : option (IRState * segment)
  :=
    let '(st, entryblock) := incBlockNamed st (append prefix "_entry") in
    let '(st, loopblock) := incBlockNamed st (append prefix "_loop") in
    let '(st, loopcond) := incLocal st in
    let '(st, nextvar) := incLocalNamed st (append prefix "_next_i") in
    let '(st, void0) := incVoid st in
    let '(st, void1) := incVoid st in
    let '(st, retloop) := incVoid st in

    (* Not strictly necessary to split loop blocks, but for
        readability it is nice to have body in-place inside the
        loop *)
    let loop_pre := [
          {|
            blk_id    := entryblock ;
            blk_phis  := []; blk_code  := init_code;
            blk_term  := (IVoid void0, TERM_Br_1 loopblock)
          |} ;

            {|
              blk_id    := loopblock ;
              blk_phis  := [(loopvar, Phi IntType [(entryblock, from); (loopcontblock, EXP_Ident (ID_Local nextvar))])];
              blk_code  := [];
              blk_term  := (IVoid void1, TERM_Br_1 body_entry)
            |}
        ] in
    let loop_post := [
          {|
            blk_id    := loopcontblock;
            blk_phis  := [];
            blk_code  := [
                          (IId nextvar, INSTR_Op (OP_IBinop (Add false false)
                                                            IntType
                                                            (EXP_Ident (ID_Local loopvar))
                                                            (EXP_Integer 1%Z))) ;
                            (IId loopcond, INSTR_Op (OP_ICmp Eq
                                                             IntType
                                                             (EXP_Ident (ID_Local loopvar))
                                                             to))

                        ];
            blk_term  := (IVoid retloop, TERM_Br (TYPE_I 1%Z, EXP_Ident (ID_Local loopcond)) nextblock loopblock)
          |}
        ] in
    Some (st, (entryblock, loop_pre ++ body_blocks ++ loop_post)).

Definition genBinOpBody
           {n: nat}
           {ft: FloatT}
           (x y: local_id)
           (f:@FSHIBinFloat ft)
           (st: IRState)
           (nextblock: block_id)
  : option (IRState * segment)
  :=
    let '(st, binopblock) := incBlockNamed st "BinOpLoopBody" in
    let '(st, binopret) := incVoid st in
    let '(st, storeid) := incVoid st in
    let '(st, loopvar2) := incLocal st in
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
     '(loopvar,_) <- hd_error (vars st) ;;
     Some (st,
           (binopblock,
            [
              {|
                blk_id    := binopblock ;
                blk_phis  := [];
                blk_code  := [
                              (IId px0,  INSTR_Op (OP_GetElementPtr
                                                     xtyp (xptyp, (EXP_Ident (ID_Local x)))
                                                     [(IntType, EXP_Integer 0%Z);
                                                        (IntType,(EXP_Ident loopvar))]

                              ));

                                (IId v0, INSTR_Load false (FloatTtyp ft)
                                                    (TYPE_Pointer (FloatTtyp ft),
                                                     (EXP_Ident (ID_Local px0)))
                                                    (Some 8%Z));

                                (IId loopvar2, INSTR_Op (OP_IBinop (Add false false)
                                                                   IntType
                                                                   (EXP_Ident loopvar)
                                                                   (EXP_Ident loopvar)));


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
                                                          (IntType,(EXP_Ident loopvar))]

                                 ));

                                   (IVoid storeid, INSTR_Store false
                                                               ((FloatTtyp ft), fexpr)
                                                               (TYPE_Pointer (FloatTtyp ft),
                                                                (EXP_Ident (ID_Local py)))
                                                               (Some 8%Z))


                               ];
                blk_term  := (IVoid binopret, TERM_Br_1 nextblock) |}
          ])).

Definition genFloatV {ft:FloatT} (fv:@FloatV ft) : option exp :=
  match ft,fv with
  | Float32, Float32V b32 => None (* TODO: 32 not supported now *)
  | Float64, Float64V b64 => Some (EXP_Float b64)
  | _ , _ => None
  end.

Definition genIReductionInit
           {i o: nat}
           {ft: FloatT}
           (n: nat)
           (t: raw_id)
           (x y: local_id)
           (dot: @FSHBinFloat ft) (initial: FloatV ft)
           (st: IRState)
           (nextblock: block_id):
  option (IRState * segment) :=

  ini <- genFloatV initial ;;
      let tmpalloc := @allocTempArrayCode ft t o in
      let ttyp := getIRType (@FSHvecValType ft o) in
      let tptyp := TYPE_Pointer ttyp in
      let '(st, pt) := incLocal st in
      let '(st, init_block_id) := incBlockNamed st "IReduction_init" in
      let '(st, loopcontblock) := incBlockNamed st "IReduction_init_lcont" in
      let '(st, loopvar) := newLocalVarNamed st IntType "IReduction_init_i" in
      let '(st, void0) := incVoid st in
      let '(st, storeid) := incVoid st in
      let init_block :=
          {|
            blk_id    := init_block_id ;
            blk_phis  := [];
            blk_code  := [
                          (IId pt,  INSTR_Op (OP_GetElementPtr
                                                ttyp (tptyp, (EXP_Ident (ID_Local t)))
                                                [(IntType, EXP_Integer 0%Z);
                                                   (IntType,(EXP_Ident (ID_Local loopvar)))]

                          ));

                            (IVoid storeid, INSTR_Store false
                                                        ((FloatTtyp ft), ini)
                                                        (TYPE_Pointer (FloatTtyp ft),
                                                         (EXP_Ident (ID_Local pt)))
                                                        (Some 8%Z))



                        ];
            blk_term  := (IVoid void0, TERM_Br_1 loopcontblock)
          |} in
      st <- dropVars st 1 ;;
         genLoop "IReduction_init_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock init_block_id [init_block] tmpalloc st nextblock.

Definition genIReductionFold
           {i o n: nat}
           {ft: FloatT}
           (y t: local_id)
           (dot: @FSHBinFloat ft)
           (st: IRState)
           (nextblock: block_id): option (IRState * segment)
  :=
    let ttyp := getIRType (@FSHvecValType ft o) in
    let tptyp := TYPE_Pointer ttyp in
    let ytyp := getIRType (@FSHvecValType ft o) in
    let yptyp := TYPE_Pointer ytyp in
    let '(st, pt) := incLocal st in
    let '(st, py) := incLocal st in
    let '(st, tv) := incLocalNamed st "tv" in
    let '(st, yv) := incLocalNamed st "yv" in
    let '(st, fold_block_id) := incBlockNamed st "IReduction_fold" in
    let '(st, loopcontblock) := incBlockNamed st "IReduction_fold_lcont" in
    let '(st, loopvar) := newLocalVarNamed st IntType "IReduction_fold_i" in
    let '(st, storeid) := incVoid st in
    let '(st, void0) := incVoid st in
    let st := addVars st [(ID_Local tv, (FloatTtyp ft)); (ID_Local yv, (FloatTtyp ft))] in
    '(st, fexpr, fexpcode) <- genFExpr st dot ;;
     st <- dropVars st 2 ;;
     let fold_block :=
         {|
           blk_id    := fold_block_id ;
           blk_phis  := [];
           blk_code  := [

                         (IId pt,  INSTR_Op (OP_GetElementPtr
                                               ttyp (tptyp, (EXP_Ident (ID_Local t)))
                                               [(IntType, EXP_Integer 0%Z);
                                                  (IntType, (EXP_Ident (ID_Local loopvar)))]

                         ));
                           (IId py,  INSTR_Op (OP_GetElementPtr
                                                 ytyp (yptyp, (EXP_Ident (ID_Local y)))
                                                 [(IntType, EXP_Integer 0%Z);
                                                    (IntType, (EXP_Ident (ID_Local loopvar)))]

                           ));

                           (IId tv, INSTR_Load false (FloatTtyp ft)
                                               (TYPE_Pointer (FloatTtyp ft),
                                                (EXP_Ident (ID_Local pt)))
                                               (Some 8%Z));
                           (IId yv, INSTR_Load false (FloatTtyp ft)
                                               (TYPE_Pointer (FloatTtyp ft),
                                                (EXP_Ident (ID_Local py)))
                                               (Some 8%Z))

                       ] ++ fexpcode ++  [

                           (IVoid storeid, INSTR_Store false
                                                       ((FloatTtyp ft), fexpr)
                                                       (TYPE_Pointer (FloatTtyp ft),
                                                        (EXP_Ident (ID_Local py)))
                                                       (Some 8%Z))

                         ];
           blk_term  := (IVoid void0, TERM_Br_1 loopcontblock)
         |} in
     genLoop "IReduction_fold_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock fold_block_id [fold_block] [] st nextblock.

Fixpoint genIR
         {i o: nat}
         {ft: FloatT}
         (x y: local_id)
         (fshcol: @FSHOperator ft i o)
         (st: IRState)
         (nextblock: block_id):
  option (IRState * segment)
  := match fshcol with
     | FSHeUnion o b z => Some (st, (nextblock, []))
     | FSHeT i b => @genFSHeT i ft st x y b nextblock
     | FSHPointwise i f => Some (st, (nextblock, []))
     | FSHBinOp n f =>
       let '(st, loopcontblock) := incBlockNamed st "BinOp_lcont" in
       let '(st, loopvar) := newLocalVarNamed st IntType "BinOp_i" in
       '(st, (body_entry, body_blocks)) <- @genBinOpBody n ft x y f st loopcontblock ;;
        st <- dropVars st 1 ;;
        genLoop "BinOp" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] st nextblock
     | FSHInductor n f initial => Some (st, (nextblock, []))
     | FSHIUnion i o n dot initial x => Some (st, (nextblock, []))
     | FSHIReduction i o n dot initial child =>
       let '(st, t) := incLocalNamed st "IReductoin_tmp" in
       let '(st, loopcontblock) := incBlockNamed st "IReduction_main_lcont" in
       let '(st, loopvar) := newLocalVarNamed st IntType "IReduction_main_i" in
       '(st,(fold_block_id, fold_blocks))
        <- @genIReductionFold i o n ft y t dot st loopcontblock ;;
        '(st,(child_block_id, child_blocks))
        <- genIR x t child st fold_block_id ;;
        let st := addVars st [(ID_Local loopvar, IntType)] in
        '(st, (loop_block_id, loop_blocks))
         <- genLoop "IReduction_main_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
         loopvar loopcontblock child_block_id (child_blocks++fold_blocks)
         [] st nextblock ;;
         st <- dropVars st 1 ;;
         @genIReductionInit i o ft n t x y dot initial st loop_block_id
     | FSHCompose i1 o2 o3 f g =>
       let '(st, tmpid) := incLocal st in
       '(st, (fb, f')) <- genIR tmpid y f st nextblock ;;
        '(st, (gb, g')) <- genIR x tmpid g st fb ;;
        let '(st, alloid, tmpalloc) := @allocTempArrayBlock ft st tmpid fb o2 in
        Some (st, (gb, [tmpalloc]++g'++f'))
     | FSHHTSUMUnion i o dot f g =>
       (* Note: 'g' computed before 'f', as in compose *)
       '(st, (fb, f')) <- genIR x y f st nextblock  ;;
        '(st, (gb, g')) <- genIR x y g st fb  ;;
        Some (st, (gb, g'++f'))
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
    '(st,(_,body)) <- genIR x y fshcol st rid ;;
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
