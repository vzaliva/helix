Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.LLVMGen.Intrinsics.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.EitherMonad.
Require Import ExtLib.Data.String.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

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
           {ft: FloatT}
           {FnBody: Set}
  :
  (list (string* (@FSHValType ft))) -> (toplevel_entities FnBody)
  := List.map
       (fun g:(string* (@FSHValType ft)) =>
          let (n,t) := g in
          TLE_Global {|
              g_ident        := Name n;
              g_typ          := getIRType t ; (* globals are always pointers *)
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


Section monadic.

  (** Going to work over any monad [m] that is:
   ** 1) a Monad, i.e. [Monad m]
   ** 2) has string-valued exceptions, i.e. [MonadExc string m]
   **)
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MonadExc_m : MonadExc string m}.

  (* TODO: move *)
  Fixpoint drop_err {A:Type} (n:nat) (lst:list A) : m (list A)
    := match n, lst with
       | O, xs => ret xs
       | S n', (_::xs) => drop_err n' xs
       | _, _ => raise "drop on empty list"
       end.

  Definition dropVars (st:IRState) (n: nat): m IRState :=
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

  (* TODO: move *)
  Definition opt2err {A:Type} (msg:string) (x: option A) : m A :=
    match x with
    | Some x => ret x
    | None => raise msg
    end.

  Fixpoint genNExpr
           {ft: FloatT}
           (st: IRState)
           (nexp: @NExpr ft) :
    m (IRState * exp * code) :=
    match nexp with
    | NVar n => '(i,t) <- opt2err "NVar out of range" (List.nth_error (vars st) n) ;;
                match t, IntType with
                | TYPE_I z, TYPE_I zi =>
                  if Z.eq_dec z zi then
                    ret (st, EXP_Ident i, [])
                  else
                    raise "NVar int size mismatch"
                | TYPE_Pointer (TYPE_I z), TYPE_I zi =>
                  if Z.eq_dec z zi then
                    let '(st, res) := incLocal st in
                    ret (st, EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false (IntType)
                                               (TYPE_Pointer (IntType),
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  else
                    raise "NVar int (via ptr) size mismatch"
                | _,_ => raise "NVar type mismatch"
                end
    | NConst v => ret (st, EXP_Integer (Z.of_nat v), [])
    | NDiv   a b => raise "NDiv not implemented" (* TODO *)
    | NMod   a b => raise "NMod not implemented" (* TODO *)
    | NPlus  a b => raise "NPlus not implemented" (* TODO *)
    | NMinus a b => raise "NMinus not implemented" (* TODO *)
    | NMult  a b => raise "NMult not implemented" (* TODO *)
    | NMin   a b => raise "NMin not implemented" (* TODO *)
    | NMax   a b => raise "NMax not implemented" (* TODO *)
    end.

  Definition genVExpr
             {n:nat}
             {ft: FloatT}
             (st: IRState)
             (vexp: @VExpr ft n) :
    m (IRState * exp * code)
    := match vexp with
       | VVar n x => p <- opt2err "VVar out of range" (List.nth_error (vars st) n) ;;
                      (* TODO: type check *)
                      ret (st, EXP_Ident (fst p), [])
       | VConst n c => raise "VConst not implemented" (* TODO *)
       end.

  Fixpoint genFExpr
           {ft: FloatT}
           (st: IRState)
           (fexp: @FExpr ft) :
    m (IRState * exp * code)
    :=
      let gen_binop a b fop :=
          '(st, aexp, acode) <- genFExpr st a ;;
           '(st, bexp, bcode) <- genFExpr st b ;;
           let '(st, res) := incLocal st in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++ bcode ++
                      [(IId res, INSTR_Op (OP_FBinop fop
                                                     [] (* TODO: list fast_math *)
                                                     (FloatTtyp ft)
                                                     aexp
                                                     bexp))
               ]) in
      let gen_call1 a f :=
          '(st, aexp, acode) <- @genFExpr ft st a ;;
           let '(st, res) := incLocal st in
           let ftyp := FloatTtyp ft in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++
                      [(IId res, INSTR_Call (ftyp,f) [(ftyp,aexp)])
               ]) in
      let gen_call2 a b f :=
          '(st, aexp, acode) <- genFExpr st a ;;
           '(st, bexp, bcode) <- genFExpr st b ;;
           let '(st, res) := incLocal st in
           let ftyp := FloatTtyp ft in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++ bcode ++
                      [(IId res, INSTR_Call (ftyp,f)
                                            [(ftyp,aexp); (ftyp,bexp)])
               ]) in
      match fexp with
      | AVar n => '(i,t) <- opt2err "AVar out of range" (List.nth_error (vars st) n) ;;
                  match t, ft with
                  | TYPE_Double, Float64 => ret (st, EXP_Ident i, [])
                  | TYPE_Float, Float32 => ret (st, EXP_Ident i, [])
                  | TYPE_Pointer TYPE_Double, Float64 =>
                    let '(st, res) := incLocal st in
                    ret (st, EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false (FloatTtyp ft)
                                               (TYPE_Pointer (FloatTtyp ft),
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  | TYPE_Pointer TYPE_Float, Float32 =>
                    let '(st, res) := incLocal st in
                    ret (st, EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false (FloatTtyp ft)
                                               (TYPE_Pointer (FloatTtyp ft),
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  | _,_ => raise "AVar type mismatch"
                  end
      | AConst (Float64V v) => ret (st, EXP_Float v, [])
      | AConst (Float32V _) => raise "32-bit constants are not implemented"
      | ANth n vec i =>
        '(st, iexp, icode) <- genNExpr st i ;;
         '(st, vexp, vcode) <- genVExpr st vec ;;
         let '(st, px) := incLocal st in
         let xtyp := getIRType (@FSHvecValType ft n) in
         let xptyp := TYPE_Pointer xtyp in
         let '(st, res) := incLocal st in
         ret (st, EXP_Ident (ID_Local res),
              icode ++ vcode ++
                    [
                      (IId px,  INSTR_Op (OP_GetElementPtr
                                            xtyp (xptyp, vexp)
                                            [(IntType, EXP_Integer 0%Z);
                                               (IntType, iexp)]

                      )) ;
                        (IId res, INSTR_Load false (FloatTtyp ft)
                                             (TYPE_Pointer (FloatTtyp ft),
                                              (EXP_Ident (ID_Local px)))
                                             (ret 8%Z))
             ])
      | AAbs a => match ft with
                 | Float32 => gen_call1 a (EXP_Ident (ID_Global (Name "llvm.fabs.f32")))
                 | Float64 => gen_call1 a (EXP_Ident (ID_Global (Name "llvm.fabs.f64")))
                 end
      | APlus a b => gen_binop a b FAdd
      | AMinus a b => gen_binop a b FSub
      | AMult a b => gen_binop a b FMul
      | AMin a b => raise "AMin not implemented" (* TODO *)
      | AMax a b => match ft with
                   | Float32 => gen_call2 a b (EXP_Ident (ID_Global (Name "llvm.maxnum.f32")))
                   | Float64 => gen_call2 a b (EXP_Ident (ID_Global (Name "llvm.maxnum.f64")))
                   end
      | AZless a b =>
        (* this is special as requires bool -> double cast *)
        '(st, aexp, acode) <- genFExpr st a ;;
         '(st, bexp, bcode) <- genFExpr st b ;;
         let '(st, ires) := incLocal st in
         let '(st, fres) := incLocal st in
         ret (st,
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

  Definition genFSHeUnion
             {o: nat}
             {ft: FloatT}
             (st: IRState)
             (x y: local_id)
             (b: @NExpr ft)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, entryblock) := incBlockNamed st "eUnion" in
      let '(st, retentry) := incVoid st in
      let '(st, storeid) := incVoid st in
      let '(st, px) := incLocal st in
      let '(st, py) := incLocal st in
      let '(st, v) := incLocal st in
      let xtyp := getIRType (@FSHvecValType ft 1) in
      let xptyp := TYPE_Pointer xtyp in
      let ytyp := getIRType (@FSHvecValType ft o) in
      let yptyp := TYPE_Pointer ytyp in
      '(st, nexpr, nexpcode) <- genNExpr st b  ;;
       ret (st , (entryblock, [
                     {|
                       blk_id    := entryblock ;
                       blk_phis  := [];
                       blk_code  := nexpcode ++ [
                                               (IId px,  INSTR_Op (OP_GetElementPtr
                                                                     xtyp (xptyp, (EXP_Ident (ID_Local x)))
                                                                     [(IntType, EXP_Integer 0%Z);
                                                                        (IntType, EXP_Integer 0%Z)]

                                               )) ;
                                                 (IId v, INSTR_Load false (FloatTtyp ft)
                                                                    (TYPE_Pointer (FloatTtyp ft),
                                                                     (EXP_Ident (ID_Local px)))
                                                                    (ret 8%Z));

                                                 (IId py,  INSTR_Op (OP_GetElementPtr
                                                                       ytyp (yptyp, (EXP_Ident (ID_Local y)))
                                                                       [(IntType, EXP_Integer 0%Z);
                                                                          (IntType, nexpr)]

                                                 ));

                                                 (IVoid storeid, INSTR_Store false
                                                                             ((FloatTtyp ft), (EXP_Ident (ID_Local v)))
                                                                             (TYPE_Pointer (FloatTtyp ft),
                                                                              (EXP_Ident (ID_Local py)))
                                                                             (ret 8%Z))

                                             ];
                       blk_term  := (IVoid retentry, TERM_Br_1 nextblock)
                     |}
            ])).

  (* AKA "pick" *)
  Definition genFSHeT
             {i:nat}
             {ft: FloatT}
             (st: IRState)
             (x y: local_id)
             (b: @NExpr ft)
             (nextblock: block_id)
    : m (IRState * segment)
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
       ret (st , (entryblock, [
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
                                                                    (ret 8%Z));

                                                 (IId py,  INSTR_Op (OP_GetElementPtr
                                                                       ytyp (yptyp, (EXP_Ident (ID_Local y)))
                                                                       [(IntType, EXP_Integer 0%Z);
                                                                          (IntType, EXP_Integer 0%Z)]

                                                 ));

                                                 (IVoid storeid, INSTR_Store false
                                                                             ((FloatTtyp ft), (EXP_Ident (ID_Local v)))
                                                                             (TYPE_Pointer (FloatTtyp ft),
                                                                              (EXP_Ident (ID_Local py)))
                                                                             (ret 8%Z))

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
    : m (IRState * segment)
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
      ret (st, (entryblock, loop_pre ++ body_blocks ++ loop_post)).


  Definition genPointwiseBody
             {n: nat}
             {ft: FloatT}
             (x y: local_id)
             (f:@FSHIUnFloat ft)
             (st: IRState)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, pwblock) := incBlockNamed st "PointwiseLoopBody" in
      let '(st, pwret) := incVoid st in
      let '(st, storeid) := incVoid st in
      let '(st, px) := incLocal st in
      let '(st, py) := incLocal st in
      let '(st, v) := incLocal st in
      let xytyp := getIRType (@FSHvecValType ft n) in
      let xyptyp := TYPE_Pointer xytyp in
      let st := addVars st [(ID_Local v, (FloatTtyp ft))] in
      '(st, fexpr, fexpcode) <- genFExpr st f ;;
       st <- dropVars st 1 ;;
       '(loopvar,_) <- opt2err "Could not drop 1 var in genPointwiseBody" (hd_error (vars st)) ;;
       ret (st,
             (pwblock,
              [
                {|
                  blk_id    := pwblock ;
                  blk_phis  := [];
                  blk_code  := [
                                (IId px,  INSTR_Op (OP_GetElementPtr
                                                       xytyp (xyptyp, (EXP_Ident (ID_Local x)))
                                                       [(IntType, EXP_Integer 0%Z);
                                                          (IntType,(EXP_Ident loopvar))]

                                ));

                                  (IId v, INSTR_Load false (FloatTtyp ft)
                                                      (TYPE_Pointer (FloatTtyp ft),
                                                       (EXP_Ident (ID_Local px)))
                                                      (ret 8%Z))
                              ]

                                 ++ fexpcode ++

                                 [ (IId py,  INSTR_Op (OP_GetElementPtr
                                                         xytyp (xyptyp, (EXP_Ident (ID_Local y)))
                                                         [(IntType, EXP_Integer 0%Z);
                                                            (IntType,(EXP_Ident loopvar))]

                                   ));

                                     (IVoid storeid, INSTR_Store false
                                                                 ((FloatTtyp ft), fexpr)
                                                                 (TYPE_Pointer (FloatTtyp ft),
                                                                  (EXP_Ident (ID_Local py)))
                                                                 (ret 8%Z))


                                 ];
                  blk_term  := (IVoid pwret, TERM_Br_1 nextblock) |}
            ])).

  Definition genBinOpBody
             {n: nat}
             {ft: FloatT}
             (x y: local_id)
             (f:@FSHIBinFloat ft)
             (st: IRState)
             (nextblock: block_id)
    : m (IRState * segment)
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
       '(loopvar,_) <- opt2err "Could not drop 2 vars in genBinOpBody" (hd_error (vars st)) ;;
       ret (st,
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
                                                      (ret 8%Z));

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
                                                      (ret 8%Z))
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
                                                                 (ret 8%Z))


                                 ];
                  blk_term  := (IVoid binopret, TERM_Br_1 nextblock) |}
            ])).

  Definition genFloatV {ft:FloatT} (fv:@FloatV ft) : m exp :=
    match ft,fv with
    | Float32, Float32V b32 => raise "32bit float constants not supported"
    | Float64, Float64V b64 => ret (EXP_Float b64)
    | _ , _ => raise "Float constant casts not supported"
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
    m (IRState * segment)
    :=
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
                                                            (ret 8%Z))



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
             (nextblock: block_id): m (IRState * segment)
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
                                                 (ret 8%Z));
                             (IId yv, INSTR_Load false (FloatTtyp ft)
                                                 (TYPE_Pointer (FloatTtyp ft),
                                                  (EXP_Ident (ID_Local py)))
                                                 (ret 8%Z))

                         ] ++ fexpcode ++  [

                             (IVoid storeid, INSTR_Store false
                                                         ((FloatTtyp ft), fexpr)
                                                         (TYPE_Pointer (FloatTtyp ft),
                                                          (EXP_Ident (ID_Local py)))
                                                         (ret 8%Z))

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
    m (IRState * segment)
    := match fshcol with
       | FSHDummy i o => ret (st, (nextblock, []))
       | FSHeUnion o b _ => @genFSHeUnion o ft st x y b nextblock
       | FSHeT i b => @genFSHeT i ft st x y b nextblock
       | FSHPointwise i f =>
         let '(st, loopcontblock) := incBlockNamed st "Pointwise_lcont" in
         let '(st, loopvar) := newLocalVarNamed st IntType "Pointwise_i" in
         '(st, (body_entry, body_blocks)) <- @genPointwiseBody i ft x y f st loopcontblock ;;
          st <- dropVars st 1 ;;
          genLoop "Pointwise" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat i)) loopvar loopcontblock body_entry body_blocks [] st nextblock
       | FSHBinOp n f =>
         let '(st, loopcontblock) := incBlockNamed st "BinOp_lcont" in
         let '(st, loopvar) := newLocalVarNamed st IntType "BinOp_i" in
         '(st, (body_entry, body_blocks)) <- @genBinOpBody n ft x y f st loopcontblock ;;
          st <- dropVars st 1 ;;
          genLoop "BinOp" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] st nextblock
       | FSHInductor n f initial => ret (st, (nextblock, []))
       | FSHIUnion i o n dot initial x => ret (st, (nextblock, []))
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
           '(st, (init_block_id, init_blocks)) <- @genIReductionInit i o ft n t x y dot initial st loop_block_id ;;
           ret (st, (init_block_id, init_blocks++loop_blocks))
       | FSHCompose i1 o2 o3 f g =>
         let '(st, tmpid) := incLocal st in
         '(st, (fb, f')) <- genIR tmpid y f st nextblock ;;
          '(st, (gb, g')) <- genIR x tmpid g st fb ;;
          let '(st, alloid, tmpalloc) := @allocTempArrayBlock ft st tmpid fb o2 in
          ret (st, (gb, [tmpalloc]++g'++f'))
       | FSHHTSUMUnion i o dot f g =>
         (* Note: 'g' computed before 'f', as in compose *)
         '(st, (fb, f')) <- genIR x y f st nextblock  ;;
          '(st, (gb, g')) <- genIR x y g st fb  ;;
          ret (st, (gb, g'++f'))
       end.

  Definition LLVMGen'
             {i o: nat}
             {ft: FloatT}
             (globals: list (string* (@FSHValType ft)))
             (fshcol: @FSHOperator ft i o) (funname: string)
    : m (toplevel_entities (list block))
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
                        let (n,t) := g in (ID_Global (Name n), TYPE_Pointer (getIRType t)))
                     globals) in (* TODO: check order of globals. Maybe reverse. *)

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
       ret
         (all_intrinsics ++
                         (genIRGlobals (FnBody:=list block) globals ++
                                       [TLE_Definition
                                          {|
                                            df_prototype   :=
                                              {|
                                                dc_name        := Name funname;
                                                dc_type        := TYPE_Function TYPE_Void [xtyp; ytyp] ;
                                                dc_param_attrs := ([],[ArrayPtrParamAttrs; ArrayPtrParamAttrs]);
                                                dc_linkage     := None ;
                                                dc_visibility  := None ;
                                                dc_dll_storage := None ;
                                                dc_cconv       := None ;
                                                dc_attrs       := []   ;
                                                dc_section     := None ;
                                                dc_align       := None ;
                                                dc_gc          := None
                                              |} ;
                                            df_args        := [x;y];
                                            df_instrs      := body
                                          |}
                                       ]
         )).

End monadic.


(** Wrap the [eval] function up with the monad instance that we
 ** want to use
 **)
Definition LLVMGen
           {i o: nat}
           {ft: FloatT}
           (globals: list (string* (@FSHValType ft)))
           (fshcol: @FSHOperator ft i o) (funname: string)
  := LLVMGen' (m := sum string) globals fshcol funname.
