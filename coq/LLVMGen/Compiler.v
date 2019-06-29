Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.LLVMGen.Externals.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.IntrinsicsDefinitions.
Require Import Vellvm.Numeric.Floats.
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

Definition SizeofFloatT (ft:FloatT): nat :=
  match ft with
  | Float32 => 4
  | Float64 => 8
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
           (x: list (string* (@FSHValType ft)))
  : list (toplevel_entity FnBody)
  := let l := List.map
       (fun g:(string* (@FSHValType ft)) =>
          let (n,t) := g in
          TLE_Global {|
              g_ident        := Name n;
              g_typ          := getIRType t ; (* globals are always pointers *)
              g_constant     := true ;
              g_exp          := None ;
              g_linkage      := Some LINKAGE_External ;
              g_visibility   := None ;
              g_dll_storage  := None ;
              g_thread_local := None ;
              g_unnamed_addr := true ; (* TODO: unsure about this *)
              g_addrspace    := None ;
              g_externally_initialized:= true ;
              g_section      := None ;
              g_align        := Some PtrAlignment ;
            |}
       ) x in
     match l with
     | nil => []
     | cons _ _ => [TLE_Comment _ "Global variables"] ++ l
     end.

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

Definition add_comments (b:block) (xs:list string): block :=
  {|
    blk_id    := blk_id b;
    blk_phis  := blk_phis b;
    blk_code  := blk_code b;
    blk_term  := blk_term b;
    blk_comments := match blk_comments b with
                    | None => Some xs
                    | Some ys => Some (ys++xs)
                    end
  |}.

Definition add_comment (bs:list block) (xs:list string): list block :=
  match bs with
  | nil => nil
  | cons b bs => cons (add_comments b xs) bs
  end.

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

Definition intrinsic_exp (d:declaration): exp :=
  EXP_Ident (ID_Global (dc_name d)).

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
      [(IId name, INSTR_Alloca (getIRType (@FSHvecValType ft size)) None (Some PtrAlignment))].

  Definition allocTempArrayBlock
             {ft: FloatT}
             (st: IRState)
             (name: local_id)
             (nextblock: block_id)
             (size: nat): (IRState * local_id * block)
    :=
      let (st,retid) := incVoid st in
      let (st,bid) := incBlock st in
      (st, bid,
       {|
         blk_id    := bid ;
         blk_phis  := [];
         blk_code  := @allocTempArrayCode ft name size;
         blk_term  := (IVoid retid, TERM_Br_1 nextblock) ;
         blk_comments := None
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
    m (IRState * exp * code)
    :=
      let gen_binop a b iop :=
          '(st, aexp, acode) <- @genNExpr ft st a ;;
           '(st, bexp, bcode) <- @genNExpr ft st b ;;
           let '(st, res) := incLocal st in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++ bcode ++
                      [(IId res, INSTR_Op (OP_IBinop iop
                                                     IntType
                                                     aexp
                                                     bexp))
               ]) in
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
      | NDiv   a b => gen_binop a b (SDiv true)
      | NMod   a b => gen_binop a b SRem
      | NPlus  a b => gen_binop a b (Add true true)
      | NMinus a b => gen_binop a b (Sub true true)
      | NMult  a b => gen_binop a b (Mul true true)
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
       | VVar n x => '(i,t) <- opt2err "VVar out of range" (List.nth_error (vars st) n) ;;
                     match t, ft with
                     | TYPE_Pointer (TYPE_Array zi TYPE_Double), Float64 | TYPE_Pointer (TYPE_Array zi TYPE_Float), Float32 =>
                       if Z.eq_dec (Z.of_nat n) zi then
                         ret (st, EXP_Ident i, [])
                       else
                         raise "VVar array size mismatch"
                     | _,_ => raise "VVar type mismatch"
                     end
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
                  | TYPE_Double, Float64 | TYPE_Float, Float32 => ret (st, EXP_Ident i, [])
                  | TYPE_Pointer TYPE_Double, Float64 | TYPE_Pointer TYPE_Float, Float32 =>
                    let '(st, res) := incLocal st in
                    ret (st, EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false (FloatTtyp ft)
                                               (TYPE_Pointer (FloatTtyp ft),
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  | _,_ => raise "AVar type mismatch"
                  end
      | AConst (Float64V v) => ret (st, EXP_Double v, [])
      | AConst (Float32V v) => ret (st, EXP_Float v, [])
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
                 | Float32 => gen_call1 a (intrinsic_exp fabs_32_decl)
                 | Float64 => gen_call1 a (intrinsic_exp fabs_64_decl)
                 end
      | APlus a b => gen_binop a b FAdd
      | AMinus a b => gen_binop a b FSub
      | AMult a b => gen_binop a b FMul
      | AMin a b => raise "AMin not implemented" (* TODO *)
      | AMax a b => match ft with
                   | Float32 => gen_call2 a b (intrinsic_exp maxnum_32_decl)
                   | Float64 => gen_call2 a b (intrinsic_exp maxnum_64_decl)
                   end
      | AZless a b =>
        (* this is special as requires bool -> double cast *)
        '(st, aexp, acode) <- genFExpr st a ;;
         '(st, bexp, bcode) <- genFExpr st b ;;
         let '(st, ires) := incLocal st in
         let '(st, fres) := incLocal st in
         let '(st, void0) := incVoid st in
         ret (st,
              EXP_Ident (ID_Local fres),
              acode ++ bcode ++
                    [(IId ires, INSTR_Op (OP_FCmp FOlt
                                                  (FloatTtyp ft)
                                                  aexp
                                                  bexp));
                       (IVoid void0, INSTR_Comment "Cast bool to float") ;
                       (IId fres, INSTR_Op (OP_Conversion
                                              Uitofp
                                              (TYPE_I 1%Z)
                                              (EXP_Ident (ID_Local ires))
                                              (FloatTtyp ft)))
             ])
      end.

  (* List of blocks with entry point *)
  Definition segment:Type := block_id * list block.

  Definition genId
             (o: nat)
             (ft: FloatT)
             (st: IRState)
             (x y: local_id)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, entryblock) := incBlockNamed st "ID" in
      let '(st, retentry) := incVoid st in
      let '(st, callid) := incVoid st in
      let '(st, xb) := incLocal st in
      let '(st, yb) := incLocal st in
      let oz := (Z.of_nat o) in
      let atyp := TYPE_Pointer (TYPE_Array oz (FloatTtyp ft)) in
      let ptyp := TYPE_Pointer (TYPE_I 8%Z) in
      let len:Z := Z.of_nat (o * (SizeofFloatT ft)) in
      let i32 := TYPE_I 32%Z in
      let i1 := TYPE_I 1%Z in
      ret (st , (entryblock, [
                   {|
                     blk_id    := entryblock ;
                     blk_phis  := [];
                     blk_code  := [
                                   (IId xb, INSTR_Op (OP_Conversion
                                                        Bitcast
                                                        atyp
                                                        (EXP_Ident (ID_Local x))
                                                        ptyp
                                   ));
                                     (IId yb, INSTR_Op (OP_Conversion
                                                          Bitcast
                                                          atyp
                                                          (EXP_Ident (ID_Local y))
                                                          ptyp
                                     ));

                                     (IVoid callid, INSTR_Call (TYPE_Void, intrinsic_exp memcpy_8_decl)
                                                               [
                                                                 (ptyp, EXP_Ident (ID_Local yb));
                                                                   (ptyp, EXP_Ident (ID_Local xb));
                                                                   (i32, EXP_Integer len);
                                                                   (i32, EXP_Integer PtrAlignment) ;
                                                                   (i1, EXP_Integer 0%Z)])
                                 ];
                     blk_term  := (IVoid retentry, TERM_Br_1 nextblock);
                     blk_comments := None
                   |}
          ])).

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
                      blk_term  := (IVoid retentry, TERM_Br_1 nextblock);
                      blk_comments := None
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
                      blk_term  := (IVoid retentry, TERM_Br_1 nextblock);
                      blk_comments := None
                    |}
           ])).

  (* Generates while loop `init_code(); i=from; while(i<to){ body(); i++;}`

    .entry:
      (init_code)
      %c0 = icmp slt i32 %start, %n
      br i1 %c0, label %.loop, label %.nextblock
    .loop:
      %i = phi i32 [ %next_i, .loopcontblock], [ %start, .entry ]
     (body)
    .loopcontblock:
      %next_i = add nsw i32 %i, 1
      %c = icmp slt i32 %next_i, %n
      br i1 %c, label %.loop, label nextblock
    nextblock:
   *)
  Definition genWhileLoop
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
      let '(st, loopcond1) := incLocal st in
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
              blk_phis  := [];
              blk_code  :=
                init_code ++
                          [
                            (IId loopcond, INSTR_Op (OP_ICmp Slt
                                                             IntType
                                                             from
                                                             to))

                                     ];
              blk_term  := (IVoid void0, TERM_Br (TYPE_I 1%Z, EXP_Ident (ID_Local loopcond)) loopblock nextblock);
              blk_comments := None
            |} ;

              {|
                blk_id    := loopblock ;
                blk_phis  := [(loopvar, Phi IntType [(entryblock, from); (loopcontblock, EXP_Ident (ID_Local nextvar))])];
                blk_code  := [];
                blk_term  := (IVoid void1, TERM_Br_1 body_entry);
                blk_comments := None
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
                              (IId loopcond1, INSTR_Op (OP_ICmp Slt
                                                               IntType
                                                               (EXP_Ident (ID_Local nextvar))
                                                               to))

                          ];
              blk_term  := (IVoid retloop, TERM_Br (TYPE_I 1%Z, EXP_Ident (ID_Local loopcond1)) loopblock nextblock );
              blk_comments := None
            |}
          ] in
      ret (st, (entryblock, loop_pre ++ body_blocks ++ loop_post)).

  Definition genHTSUMUnionpBody
             {n: nat}
             {ft: FloatT}
             (a b y: local_id)
             (f:@FSHBinFloat ft)
             (st: IRState)
             (loopvar: raw_id)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, pwblock) := incBlockNamed st "genHTSUMUnionpBody" in
      let '(st, pwret) := incVoid st in
      let '(st, storeid) := incVoid st in
      let '(st, pa) := incLocal st in
      let '(st, pb) := incLocal st in
      let '(st, py) := incLocal st in
      let '(st, va) := incLocal st in
      let '(st, vb) := incLocal st in
      let xytyp := getIRType (@FSHvecValType ft n) in
      let xyptyp := TYPE_Pointer xytyp in
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local va, (FloatTtyp ft)); (ID_Local vb, (FloatTtyp ft))] in
      '(st, fexpr, fexpcode) <- genFExpr st f ;;
       st <- dropVars st 2 ;;
       ret (st,
            (pwblock,
             [
               {|
                 blk_id    := pwblock ;
                 blk_phis  := [];
                 blk_code  := [
                               (IId pa,  INSTR_Op (OP_GetElementPtr
                                                     xytyp (xyptyp, (EXP_Ident (ID_Local a)))
                                                     [(IntType, EXP_Integer 0%Z);
                                                        (IntType,(EXP_Ident loopvarid))]

                               ));

                                 (IId va, INSTR_Load false (FloatTtyp ft)
                                                     (TYPE_Pointer (FloatTtyp ft),
                                                      (EXP_Ident (ID_Local pa)))
                                                     (ret 8%Z));

                                 (IId pb,  INSTR_Op (OP_GetElementPtr
                                                       xytyp (xyptyp, (EXP_Ident (ID_Local b)))
                                                       [(IntType, EXP_Integer 0%Z);
                                                          (IntType,(EXP_Ident loopvarid))]

                                 ));

                                 (IId vb, INSTR_Load false (FloatTtyp ft)
                                                     (TYPE_Pointer (FloatTtyp ft),
                                                      (EXP_Ident (ID_Local pb)))
                                                     (ret 8%Z))
                             ]

                                ++ fexpcode ++

                                [ (IId py,  INSTR_Op (OP_GetElementPtr
                                                        xytyp (xyptyp, (EXP_Ident (ID_Local y)))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType,(EXP_Ident loopvarid))]

                                  ));

                                    (IVoid storeid, INSTR_Store false
                                                                ((FloatTtyp ft), fexpr)
                                                                (TYPE_Pointer (FloatTtyp ft),
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid pwret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genPointwiseBody
             {n: nat}
             {ft: FloatT}
             (x y: local_id)
             (f:@FSHIUnFloat ft)
             (st: IRState)
             (loopvar: raw_id)
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
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local v, (FloatTtyp ft)); (loopvarid, IntType)] in
      '(st, fexpr, fexpcode) <- genFExpr st f ;;
       st <- dropVars st 2 ;;
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
                                                        (IntType,(EXP_Ident loopvarid))]

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
                                                           (IntType,(EXP_Ident loopvarid))]

                                  ));

                                    (IVoid storeid, INSTR_Store false
                                                                ((FloatTtyp ft), fexpr)
                                                                (TYPE_Pointer (FloatTtyp ft),
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid pwret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genBinOpBody
             {n: nat}
             {ft: FloatT}
             (x y: local_id)
             (f:@FSHIBinFloat ft)
             (st: IRState)
             (loopvar: raw_id)
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
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local v1, (FloatTtyp ft)); (ID_Local v0, (FloatTtyp ft)); (loopvarid, IntType)] in
      '(st, fexpr, fexpcode) <- genFExpr st f ;;
       st <- dropVars st 3 ;;
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
                                                         (IntType,(EXP_Ident loopvarid))]

                               ));

                                 (IId v0, INSTR_Load false (FloatTtyp ft)
                                                     (TYPE_Pointer (FloatTtyp ft),
                                                      (EXP_Ident (ID_Local px0)))
                                                     (ret 8%Z));

                                 (IId loopvar2, INSTR_Op (OP_IBinop (Add false false)
                                                                    IntType
                                                                    (EXP_Ident loopvarid)
                                                                    (EXP_Integer (Z.of_nat n))));


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
                                                           (IntType, (EXP_Ident loopvarid))]

                                  ));

                                    (IVoid storeid, INSTR_Store false
                                                                ((FloatTtyp ft), fexpr)
                                                                (TYPE_Pointer (FloatTtyp ft),
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid binopret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genFloatV {ft:FloatT} (fv:@FloatV ft) : exp :=
    match fv with
    | Float32V b32 => EXP_Float b32
    | Float64V b64 => EXP_Double b64
    end.

  (* !!!TODO: this may be wrong! We initializint [t] while we must intialize [y] *)
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
      let ini := genFloatV initial in
      let tmpalloc := @allocTempArrayCode ft t o in
      let ttyp := getIRType (@FSHvecValType ft o) in
      let tptyp := TYPE_Pointer ttyp in
      let '(st, pt) := incLocal st in
      let '(st, init_block_id) := incBlockNamed st "IReduction_init" in
      let '(st, loopcontblock) := incBlockNamed st "IReduction_init_lcont" in
      let '(st, loopvar) := incLocalNamed st "IReduction_init_i" in
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
            blk_term  := (IVoid void0, TERM_Br_1 loopcontblock);
            blk_comments := None
          |} in
      genWhileLoop "IReduction_init_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock init_block_id [init_block] tmpalloc st nextblock.

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
      let '(st, loopvar) := incLocalNamed st "IReduction_fold_i" in
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
             blk_term  := (IVoid void0, TERM_Br_1 loopcontblock);
             blk_comments := None
           |} in
       genWhileLoop "IReduction_fold_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock fold_block_id [fold_block] [] st nextblock.

  Definition genFSHInductor
             {ft: FloatT}
             (x y: local_id)
             (n: @NExpr ft)
             (f: @FSHBinFloat ft)
             (initial: @FloatV ft)
             (st: IRState)
             (nextblock: block_id): m (IRState * segment)
    :=
      let '(st, loopcontblock) := incBlockNamed st "Inductor_lcont" in
      let '(st, loopvar) := incLocalNamed st "Inductor_i" in
      let xytyp := getIRType (@FSHvecValType ft 1) in
      let xyptyp := TYPE_Pointer xytyp in
      let '(st, py) := incLocal st in
      let '(st, storeid0) := incVoid st in
      let '(st, void1) := incVoid st in
      '(st, nexp, ncode) <- genNExpr st n ;;
       let ini := genFloatV initial in
       let init_code := ncode ++ [
                                (IId py,  INSTR_Op (OP_GetElementPtr
                                                      xytyp (xyptyp, (EXP_Ident (ID_Local y)))
                                                      [(IntType, EXP_Integer 0%Z);
                                                         (IntType,EXP_Integer 0%Z)]

                                ));

                                  (IVoid storeid0, INSTR_Store false
                                                               ((FloatTtyp ft), ini)
                                                               (TYPE_Pointer (FloatTtyp ft),
                                                                (EXP_Ident (ID_Local py)))
                                                               (ret 8%Z))

                              ] in

       let '(st, body_block_id) := incBlockNamed st "InductorLoopBody" in
       let '(st, storeid1) := incVoid st in
       let '(st, void2) := incVoid st in
       let '(st, px) := incLocal st in
       let '(st, yv) := incLocal st in
       let '(st, xv) := incLocal st in
       let st := addVars st [(ID_Local yv, (FloatTtyp ft)); (ID_Local xv, (FloatTtyp ft))] in
       '(st, fexpr, fexpcode) <- genFExpr st f ;;
        st <- dropVars st 2 ;;
        let body_block := {|
              blk_id    := body_block_id ;
              blk_phis  := [];
              blk_code  := [
                            (IId px,  INSTR_Op (OP_GetElementPtr
                                                  xytyp (xyptyp, (EXP_Ident (ID_Local x)))
                                                  [(IntType, EXP_Integer 0%Z);
                                                     (IntType,EXP_Integer 0%Z)]

                            ));
                              (IId yv, INSTR_Load false (FloatTtyp ft)
                                                  (TYPE_Pointer (FloatTtyp ft),
                                                   (EXP_Ident (ID_Local py)))
                                                  (ret 8%Z));
                              (IId xv, INSTR_Load false (FloatTtyp ft)
                                                  (TYPE_Pointer (FloatTtyp ft),
                                                   (EXP_Ident (ID_Local px)))
                                                  (ret 8%Z))
                          ]
                             ++ fexpcode ++
                             [
                               (IVoid storeid1, INSTR_Store false
                                                            ((FloatTtyp ft), fexpr)
                                                            (TYPE_Pointer (FloatTtyp ft),
                                                             (EXP_Ident (ID_Local py)))
                                                            (ret 8%Z))
                             ];
              blk_term  := (IVoid void2, TERM_Br_1 loopcontblock);
              blk_comments := None
            |} in
        genWhileLoop "Inductor" (EXP_Integer 0%Z) nexp loopvar loopcontblock body_block_id [body_block] init_code st nextblock.

  Fixpoint genIR
           {i o: nat}
           {ft: FloatT}
           (x y: local_id)
           (fshcol: @FSHOperator ft i o)
           (st: IRState)
           (nextblock: block_id):
    m (IRState * segment)
    :=
      let add_comment r s : m (IRState * segment) := '(st, (e, b)) <- r ;; ret (st,(e,add_comment b [s])) in

      match fshcol with
      | FSHId i =>
        add_comment
          (genId i ft st x y nextblock)
          "--- Operator: FSHId ---"
      | FSHeUnion o b _ =>
        add_comment
          (@genFSHeUnion o ft st x y b nextblock)
          "--- Operator: FSHeUnion ---"
      | FSHeT i b =>
        add_comment
          (@genFSHeT i ft st x y b nextblock)
          "--- Operator: FSHeT ---"
      | FSHPointwise i f =>
        let '(st, loopcontblock) := incBlockNamed st "Pointwise_lcont" in
        let '(st, loopvar) := incLocalNamed st "Pointwise_i" in
        '(st, (body_entry, body_blocks)) <- @genPointwiseBody i ft x y f st loopvar loopcontblock ;;
         add_comment
         (genWhileLoop "Pointwise" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat i)) loopvar loopcontblock body_entry body_blocks [] st nextblock)
         "--- Operator: FSHPointwise ---"
      | FSHBinOp n f =>
        let '(st, loopcontblock) := incBlockNamed st "BinOp_lcont" in
        let '(st, loopvar) := incLocalNamed st "BinOp_i" in
        '(st, (body_entry, body_blocks)) <- @genBinOpBody n ft x y f st loopvar loopcontblock ;;
         add_comment
         (genWhileLoop "BinOp" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] st nextblock)
         "--- Operator: FSHBinOp ---"
      | FSHInductor n f initial =>
        add_comment
          (genFSHInductor x y n f initial st nextblock)
          "--- Operator: FSHInductor ---"
      | FSHIUnion i o n _ _ child =>
        let '(st, loopcontblock) := incBlockNamed st "Union_lcont" in
        let '(st, loopvar) := incBlockNamed st "Union_i" in
        let st := addVars st [(ID_Local loopvar, IntType)] in
        '(st,(child_block_id, child_blocks)) <- genIR x y child st loopcontblock ;;
         st <- dropVars st 1 ;;
         add_comment
         (genWhileLoop "Union_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock child_block_id child_blocks[] st nextblock)
         "--- Operator: FSHIUnion ---"
      | FSHIReduction i o n dot initial child =>
        let '(st, t) := incLocalNamed st "IReductoin_tmp" in
        let '(st, loopcontblock) := incBlockNamed st "IReduction_main_lcont" in
        let '(st, loopvar) := incBlockNamed st "IReduction_main_i" in
        '(st,(fold_block_id, fold_blocks)) <- @genIReductionFold i o n ft y t dot st loopcontblock ;;
         let st := addVars st [(ID_Local loopvar, IntType)] in
         '(st,(child_block_id, child_blocks)) <- genIR x t child st fold_block_id ;;
          st <- dropVars st 1 ;;
          '(st, (loop_block_id, loop_blocks))
          <- genWhileLoop "IReduction_main_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
          loopvar loopcontblock child_block_id (child_blocks++fold_blocks)
          [] st nextblock ;;
          '(st, (init_block_id, init_blocks)) <- @genIReductionInit i o ft n t x y dot initial st loop_block_id ;;
          add_comment (ret (st, (init_block_id, init_blocks++loop_blocks))) "--- Operator: FSHIReduction ---"
      | FSHCompose i1 o2 o3 f g =>
        let '(st, tmpid) := incLocal st in
        '(st, (fb, f')) <- genIR tmpid y f st nextblock ;;
         '(st, (gb, g')) <- genIR x tmpid g st fb ;;
         let '(st, alloid, tmpalloc) := @allocTempArrayBlock ft st tmpid gb o2 in
         (* TODO: free? *)
         add_comment (ret (st, (alloid, [tmpalloc]++g'++f'))) "--- Operator: FSHCompose ---"
      | FSHHTSUMUnion i o dot f g =>
        let '(st, tmpfy) := incLocal st in
        let '(st, tmpgy) := incLocal st in
        let '(st, loopcontblock) := incBlockNamed st "HTSUMUnion_lcont" in
        let '(st, loopvar) := incLocalNamed st "HTSUMUnion_i" in
        '(st, (body_entry, body_blocks)) <- @genHTSUMUnionpBody o ft tmpfy tmpgy y dot st loopvar loopcontblock ;;
         '(st, (loopblock, loop_blocks)) <-  genWhileLoop "HTSUMUnion" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock body_entry body_blocks [] st nextblock ;;
         '(st, (fb, f')) <- genIR x tmpfy f st loopblock  ;;
         '(st, (gb, g')) <- genIR x tmpgy g st fb  ;;
         let (st,retid) := incVoid st in
         let (st,tmp_alloc_block_id) := incBlock st in
         let tmp_alloc_block :=
             {|
               blk_id    := tmp_alloc_block_id ;
               blk_phis  := [];
               blk_code  :=
                 @allocTempArrayCode ft tmpfy o ++ @allocTempArrayCode ft tmpgy o;
               blk_term  := (IVoid retid, TERM_Br_1 gb) ;
               blk_comments := None
             |} in
         add_comment (ret (st, (tmp_alloc_block_id, [tmp_alloc_block]++g'++f'++loop_blocks)))
                     "--- Operator: FSHHTSUMUnion ---"
      end.

  Definition LLVMGen'
             {i o: nat}
             {ft: FloatT}
             (globals: list (string* (@FSHValType ft)))
             (globals_extern: bool)
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

      let (st,rid) := incBlock st in
      let (st,rsid) := incBlock st in
      let retblock :=
          {|
            blk_id    := rid ;
            blk_phis  := [];
            blk_code  := [];
            blk_term  := (IId rsid, TERM_Ret_void);
            blk_comments := None
          |} in
      '(st,(_,body)) <- genIR x y fshcol st rid ;;
       let body := body ++ [retblock] in
       let all_intrinsics:toplevel_entities (list block)
           := [@TLE_Comment (list block) "Prototypes for intrinsics we use"]
                ++ (List.map (TLE_Declaration) (
                               helix_intrinsics_decls ++ defined_intrinsics_decls))
       in
       ret
         (all_intrinsics ++
                         (if globals_extern then
                              (genIRGlobals (FnBody:=list block) globals) else []) ++
                                       [
                                         TLE_Comment _ " Top-level operator definition" ;
                                         TLE_Definition
                                          {|
                                            df_prototype   :=
                                              {|
                                                dc_name        := Name funname;
                                                dc_type        := TYPE_Function TYPE_Void [xtyp; ytyp] ;
                                                dc_param_attrs := ([],
                                                                   [[PARAMATTR_Readonly] ++ ArrayPtrParamAttrs;
                                                                      ArrayPtrParamAttrs]);
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
         ).

End monadic.


(** Wrap the [eval] function up with the monad instance that we
 ** want to use
 **)
Definition LLVMGen
           {i o: nat}
           {ft: FloatT}
           (globals: list (string* (@FSHValType ft)))
           (fshcol: @FSHOperator ft i o) (funname: string)
  := LLVMGen' (m := sum string) globals true fshcol funname.
