Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.LLVMGen.Externals.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.IntrinsicsDefinitions.
Require Import Vellvm.Numeric.Floats.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

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

Import MDSHCOLOnFloat64.

(* 64-bit IEEE floats *)
Definition SizeofFloatT := 8.

(* Type of values. Used for global variables *)
Inductive FSHValType :=
| FSHnatValType       :FSHValType
| FSHFloatValType     :FSHValType
| FSHvecValType (n:nat) :FSHValType.

Definition getIRType (t: FSHValType): typ :=
  match t with
  | FSHnatValType => IntType
  | FSHFloatValType => TYPE_Double
  | FSHvecValType n => TYPE_Array (Z.of_nat n) TYPE_Double
  end.

Definition genIRGlobals
           {FnBody: Set}
           (x: list (string*FSHValType))
  : list (toplevel_entity _ FnBody)
  := let l := List.map
                (fun g:(string * FSHValType) =>
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
     | cons _ _ => [TLE_Comment "Global variables"] ++ l
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

Definition setVars (s:IRState) (newvars:list (ident * typ)): IRState :=
  {|
    block_count := block_count s ;
    local_count := local_count s ;
    void_count  := void_count s ;
    vars := newvars
  |}.

Definition add_comments (b:block typ) (xs:list string): block typ :=
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

Definition add_comment (bs:list (block typ)) (xs:list string): list (block typ) :=
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

Definition intrinsic_exp (d:declaration typ): exp typ :=
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


  Definition allocTempArrayCode (name: local_id) (size:nat)
    :=
      [(IId name, INSTR_Alloca (getIRType (FSHvecValType size)) None (Some PtrAlignment))].

  Definition allocTempArrayBlock
             (st: IRState)
             (name: local_id)
             (nextblock: block_id)
             (size: nat): (IRState * (local_id * (block typ)))
    :=
      let (st,retid) := incVoid st in
      let (st,bid) := incBlock st in
      (st, (bid,
            {|
              blk_id    := bid ;
              blk_phis  := [];
              blk_code  := allocTempArrayCode name size;
              blk_term  := (IVoid retid, TERM_Br_1 nextblock) ;
              blk_comments := None
            |})).

  (* TODO: move to OptionMonad.v? *)
  Definition opt2err {A:Type} (msg:string) (x: option A) : m A :=
    match x with
    | Some x => ret x
    | None => raise msg
    end.

  Definition nat_eq_or_err (msg:string) (a b:nat) : m unit :=
    if PeanoNat.Nat.eq_dec a b
    then ret tt
    else raise (append msg (" "++(string_of_nat a)++"!="++(string_of_nat b))).

  Fixpoint genNExpr
           (st: IRState)
           (nexp: NExpr) :
    m (IRState * (exp typ) * (code typ))
    :=
      let gen_binop a b iop :=
          '(st, aexp, acode) <- genNExpr st a ;;
           '(st, bexp, bcode) <- genNExpr st b ;;
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
                      raise (append "NVar #" ((string_of_nat n) ++ " dimensions mismatch in " ++ string_of_vars (vars st)))
                  | TYPE_Pointer (TYPE_I z), TYPE_I zi =>
                    if Z.eq_dec z zi then
                      let '(st, res) := incLocal st in
                      ret (st, EXP_Ident (ID_Local res),
                           [(IId res, INSTR_Load false (IntType)
                                                 (TYPE_Pointer (IntType),
                                                  (EXP_Ident i))
                                                 (ret 8%Z))])
                    else
                      raise (append "NVar #" ((string_of_nat n) ++ " pointer type mismatch in " ++ string_of_vars (vars st)))
                  | _,_ => raise (append "NVar #" ((string_of_nat n) ++ " type mismatch in " ++ string_of_vars (vars st)))
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


  Definition genMExpr
             (st: IRState)
             (mexp: MExpr)
    :
      m (IRState * (exp typ) * (code typ) * typ)
    := match mexp with
       | MVar x => '(i,t) <- opt2err "MVar out of range" (List.nth_error (vars st) x) ;;
                   match t with
                   | TYPE_Pointer (TYPE_Array zi TYPE_Double) =>
                     ret (st, EXP_Ident i, [], (TYPE_Array zi TYPE_Double))
                  | _  => raise (append "MVar #" ((string_of_nat x) ++ " type mismatch in " ++ string_of_vars (vars st)))
                   end
       | MConst c => raise "MConst not implemented" (* TODO *)
       end.

  Fixpoint genAExpr
           (st: IRState)
           (fexp: AExpr) :
    m (IRState * (exp typ) * (code typ))
    :=
      let gen_binop a b fop :=
          '(st, aexp, acode) <- genAExpr st a ;;
           '(st, bexp, bcode) <- genAExpr st b ;;
           let '(st, res) := incLocal st in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++ bcode ++
                      [(IId res, INSTR_Op (OP_FBinop fop
                                                     [] (* TODO: list fast_math *)
                                                     TYPE_Double
                                                     aexp
                                                     bexp))
               ]) in
      let gen_call1 a f :=
          '(st, aexp, acode) <- genAExpr st a ;;
           let '(st, res) := incLocal st in
           let ftyp := TYPE_Double in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++
                      [(IId res, INSTR_Call (ftyp,f) [(ftyp,aexp)])
               ]) in
      let gen_call2 a b f :=
          '(st, aexp, acode) <- genAExpr st a ;;
           '(st, bexp, bcode) <- genAExpr st b ;;
           let '(st, res) := incLocal st in
           let ftyp := TYPE_Double in
           ret (st,
                EXP_Ident (ID_Local res),
                acode ++ bcode ++
                      [(IId res, INSTR_Call (ftyp,f)
                                            [(ftyp,aexp); (ftyp,bexp)])
               ]) in
      match fexp with
      | AVar n => '(i,t) <- opt2err "AVar out of range" (List.nth_error (vars st) n) ;;
                  match t with
                  | TYPE_Double => ret (st, EXP_Ident i, [])
                  | TYPE_Pointer TYPE_Double =>
                    let '(st, res) := incLocal st in
                    ret (st, EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false TYPE_Double
                                               (TYPE_Pointer TYPE_Double,
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  | _ => raise (append "AVar #" ((string_of_nat n) ++ " type mismatch in " ++ string_of_vars (vars st)))
                  end
      | AConst v => ret (st, EXP_Double v, [])
      | ANth vec i =>
        '(st, iexp, icode) <- genNExpr st i ;;
         '(st, vexp, vcode, xtyp) <- genMExpr st vec ;;
         let '(st, px) := incLocal st in
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
                        (IId res, INSTR_Load false TYPE_Double
                                             (TYPE_Pointer TYPE_Double,
                                              (EXP_Ident (ID_Local px)))
                                             (ret 8%Z))
             ])
      | AAbs a => gen_call1 a (intrinsic_exp fabs_64_decl)
      | APlus a b => gen_binop a b FAdd
      | AMinus a b => gen_binop a b FSub
      | AMult a b => gen_binop a b FMul
      | AMin a b => gen_call2 a b (intrinsic_exp minimum_64_decl)
      | AMax a b => gen_call2 a b (intrinsic_exp maxnum_64_decl)
      | AZless a b =>
        (* this is special as requires bool -> double cast *)
        '(st, aexp, acode) <- genAExpr st a ;;
         '(st, bexp, bcode) <- genAExpr st b ;;
         let '(st, ires) := incLocal st in
         let '(st, fres) := incLocal st in
         let '(st, void0) := incVoid st in
         ret (st,
              EXP_Ident (ID_Local fres),
              acode ++ bcode ++
                    [(IId ires, INSTR_Op (OP_FCmp FOlt
                                                  TYPE_Double
                                                  aexp
                                                  bexp));
                       (IVoid void0, INSTR_Comment "Cast bool to float") ;
                       (IId fres, INSTR_Op (OP_Conversion
                                              Uitofp
                                              (TYPE_I 1%Z)
                                              (EXP_Ident (ID_Local ires))
                                              TYPE_Double))
             ])
      end.

  (* List of blocks with entry point *)
  Definition segment:Type := block_id * list (block typ).

  Definition genMemCopy
             (o: nat)
             (st: IRState)
             (x y: ident)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, entryblock) := incBlockNamed st "ID" in
      let '(st, retentry) := incVoid st in
      let '(st, callid) := incVoid st in
      let '(st, xb) := incLocal st in
      let '(st, yb) := incLocal st in
      let oz := (Z.of_nat o) in
      let atyp := TYPE_Pointer (TYPE_Array oz TYPE_Double) in
      let ptyp := TYPE_Pointer (TYPE_I 8%Z) in
      let len:Z := Z.of_nat (o * SizeofFloatT) in
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
                                                        (EXP_Ident x)
                                                        ptyp
                                   ));
                                     (IId yb, INSTR_Op (OP_Conversion
                                                          Bitcast
                                                          atyp
                                                          (EXP_Ident y)
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

  Definition genFSHAssign
             (i o: nat)
             (st: IRState)
             (x y: ident)
             (src dst: NExpr)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, entryblock) := incBlockNamed st "Assign" in
      let '(st, retentry) := incVoid st in
      let '(st, storeid) := incVoid st in
      let '(st, px) := incLocal st in
      let '(st, py) := incLocal st in
      let '(st, v) := incLocal st in
      let xtyp := getIRType (FSHvecValType i) in
      let xptyp := TYPE_Pointer xtyp in
      let ytyp := getIRType (FSHvecValType o) in
      let yptyp := TYPE_Pointer ytyp in
      '(st, src_nexpr, src_nexpcode) <- genNExpr st src  ;;
       '(st, dst_nexpr, dst_nexpcode) <- genNExpr st dst  ;;
       ret (st , (entryblock, [
                    {|
                      blk_id    := entryblock ;
                      blk_phis  := [];
                      blk_code  := src_nexpcode ++ dst_nexpcode ++ [
                                                  (IId px,  INSTR_Op (OP_GetElementPtr
                                                                        xtyp (xptyp, (EXP_Ident x))
                                                                        [(IntType, EXP_Integer 0%Z);
                                                                           (IntType, src_nexpr)]

                                                  )) ;
                                                    (IId v, INSTR_Load false TYPE_Double
                                                                       (TYPE_Pointer TYPE_Double,
                                                                        (EXP_Ident (ID_Local px)))
                                                                       (ret 8%Z));

                                                    (IId py,  INSTR_Op (OP_GetElementPtr
                                                                          ytyp (yptyp, (EXP_Ident y))
                                                                          [(IntType, EXP_Integer 0%Z);
                                                                             (IntType, dst_nexpr)]

                                                    ));

                                                    (IVoid storeid, INSTR_Store false
                                                                                (TYPE_Double, (EXP_Ident (ID_Local v)))
                                                                                (TYPE_Pointer TYPE_Double,
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
             (from to: exp typ)
             (loopvar: raw_id)
             (loopcontblock: block_id)
             (body_entry: block_id)
             (body_blocks: list (block typ))
             (init_code: (code typ))
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
             (a b y: local_id)
             (f:AExpr)
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
      let xytyp := getIRType (FSHvecValType n) in
      let xyptyp := TYPE_Pointer xytyp in
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local va, TYPE_Double); (ID_Local vb, TYPE_Double)] in
      '(st, fexpr, fexpcode) <- genAExpr st f ;;
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

                                 (IId va, INSTR_Load false TYPE_Double
                                                     (TYPE_Pointer TYPE_Double,
                                                      (EXP_Ident (ID_Local pa)))
                                                     (ret 8%Z));

                                 (IId pb,  INSTR_Op (OP_GetElementPtr
                                                       xytyp (xyptyp, (EXP_Ident (ID_Local b)))
                                                       [(IntType, EXP_Integer 0%Z);
                                                          (IntType,(EXP_Ident loopvarid))]

                                 ));

                                 (IId vb, INSTR_Load false TYPE_Double
                                                     (TYPE_Pointer TYPE_Double,
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
                                                                (TYPE_Double, fexpr)
                                                                (TYPE_Pointer TYPE_Double,
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid pwret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genIMapBody
             (n: nat)
             (x y: ident)
             (f: AExpr)
             (st: IRState)
             (loopvar: raw_id)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, pwblock) := incBlockNamed st "IMapLoopBody" in
      let '(st, pwret) := incVoid st in
      let '(st, storeid) := incVoid st in
      let '(st, px) := incLocal st in
      let '(st, py) := incLocal st in
      let '(st, v) := incLocal st in
      let xytyp := getIRType (FSHvecValType n) in
      let xyptyp := TYPE_Pointer xytyp in
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local v, TYPE_Double); (loopvarid, IntType)] in
      '(st, fexpr, fexpcode) <- genAExpr st f ;;
       st <- dropVars st 2 ;;
       ret (st,
            (pwblock,
             [
               {|
                 blk_id    := pwblock ;
                 blk_phis  := [];
                 blk_code  := [
                               (IId px,  INSTR_Op (OP_GetElementPtr
                                                     xytyp (xyptyp, (EXP_Ident x))
                                                     [(IntType, EXP_Integer 0%Z);
                                                        (IntType,(EXP_Ident loopvarid))]

                               ));

                                 (IId v, INSTR_Load false TYPE_Double
                                                    (TYPE_Pointer TYPE_Double,
                                                     (EXP_Ident (ID_Local px)))
                                                    (ret 8%Z))
                             ]

                                ++ fexpcode ++

                                [ (IId py,  INSTR_Op (OP_GetElementPtr
                                                        xytyp (xyptyp, (EXP_Ident y))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType,(EXP_Ident loopvarid))]

                                  ));

                                    (IVoid storeid, INSTR_Store false
                                                                (TYPE_Double, fexpr)
                                                                (TYPE_Pointer TYPE_Double,
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid pwret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genBinOpBody
             (n: nat)
             (x y: ident)
             (f: AExpr)
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
      let xtyp := getIRType (FSHvecValType (n+n)) in
      let xptyp := TYPE_Pointer xtyp in
      let ytyp := getIRType (FSHvecValType n) in
      let yptyp := TYPE_Pointer ytyp in
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local v1, TYPE_Double); (ID_Local v0, TYPE_Double); (loopvarid, IntType)] in
      '(st, fexpr, fexpcode) <- genAExpr st f ;;
       st <- dropVars st 3 ;;
       ret (st,
            (binopblock,
             [
               {|
                 blk_id    := binopblock ;
                 blk_phis  := [];
                 blk_code  := [
                               (IId px0,  INSTR_Op (OP_GetElementPtr
                                                      xtyp (xptyp, (EXP_Ident x))
                                                      [(IntType, EXP_Integer 0%Z);
                                                         (IntType,(EXP_Ident loopvarid))]

                               ));

                                 (IId v0, INSTR_Load false TYPE_Double
                                                     (TYPE_Pointer TYPE_Double,
                                                      (EXP_Ident (ID_Local px0)))
                                                     (ret 8%Z));

                                 (IId loopvar2, INSTR_Op (OP_IBinop (Add false false)
                                                                    IntType
                                                                    (EXP_Ident loopvarid)
                                                                    (EXP_Integer (Z.of_nat n))));


                                 (IId px1,  INSTR_Op (OP_GetElementPtr
                                                        xtyp (xptyp, (EXP_Ident x))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType,(EXP_Ident (ID_Local loopvar2)))]

                                 ));

                                 (IId v1, INSTR_Load false TYPE_Double
                                                     (TYPE_Pointer TYPE_Double,
                                                      (EXP_Ident (ID_Local px1)))
                                                     (ret 8%Z))
                             ]


                                ++ fexpcode ++

                                [ (IId py,  INSTR_Op (OP_GetElementPtr
                                                        ytyp (yptyp, (EXP_Ident y))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType, (EXP_Ident loopvarid))]

                                  ));

                                    (IVoid storeid, INSTR_Store false
                                                                (TYPE_Double, fexpr)
                                                                (TYPE_Pointer TYPE_Double,
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid binopret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genMemMap2Body
             (n: nat)
             (x0 x1 y: ident)
             (f: AExpr)
             (st: IRState)
             (loopvar: raw_id)
             (nextblock: block_id)
    : m (IRState * segment)
    :=
      let '(st, binopblock) := incBlockNamed st "MemMap2LoopBody" in
      let '(st, binopret) := incVoid st in
      let '(st, storeid) := incVoid st in
      let '(st, px0) := incLocal st in
      let '(st, px1) := incLocal st in
      let '(st, py) := incLocal st in
      let '(st, v0) := incLocal st in
      let '(st, v1) := incLocal st in
      let xtyp := getIRType (FSHvecValType n) in
      let xptyp := TYPE_Pointer xtyp in
      let ytyp := getIRType (FSHvecValType n) in
      let yptyp := TYPE_Pointer ytyp in
      let loopvarid := ID_Local loopvar in
      let st := addVars st [(ID_Local v1, TYPE_Double); (ID_Local v0, TYPE_Double)] in
      '(st, fexpr, fexpcode) <- genAExpr st f ;;
       st <- dropVars st 2 ;;
       ret (st,
            (binopblock,
             [
               {|
                 blk_id    := binopblock ;
                 blk_phis  := [];
                 blk_code  := [
                               (IId px0,  INSTR_Op (OP_GetElementPtr
                                                      xtyp (xptyp, (EXP_Ident x0))
                                                      [(IntType, EXP_Integer 0%Z);
                                                         (IntType,(EXP_Ident loopvarid))]

                               ));

                                 (IId v0, INSTR_Load false TYPE_Double
                                                     (TYPE_Pointer TYPE_Double,
                                                      (EXP_Ident (ID_Local px0)))
                                                     (ret 8%Z));

                                 (IId px1,  INSTR_Op (OP_GetElementPtr
                                                        xtyp (xptyp, (EXP_Ident x1))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType,(EXP_Ident (ID_Local loopvar)))]

                                 ));

                                 (IId v1, INSTR_Load false TYPE_Double
                                                     (TYPE_Pointer TYPE_Double,
                                                      (EXP_Ident (ID_Local px1)))
                                                     (ret 8%Z))
                             ]


                                ++ fexpcode ++

                                [ (IId py,  INSTR_Op (OP_GetElementPtr
                                                        ytyp (yptyp, (EXP_Ident y))
                                                        [(IntType, EXP_Integer 0%Z);
                                                           (IntType, (EXP_Ident loopvarid))]

                                  ));

                                    (IVoid storeid, INSTR_Store false
                                                                (TYPE_Double, fexpr)
                                                                (TYPE_Pointer TYPE_Double,
                                                                 (EXP_Ident (ID_Local py)))
                                                                (ret 8%Z))


                                ];
                 blk_term  := (IVoid binopret, TERM_Br_1 nextblock);
                 blk_comments := None
               |}
           ])).

  Definition genFloatV (fv:binary64) : (exp typ) :=  EXP_Double fv.

  Definition genMemInit
             (o n: nat)
             (y: ident)
             (initial: binary64)
             (st: IRState)
             (nextblock: block_id):
    m (IRState * segment)
    :=
      let ini := genFloatV initial in
      let ttyp := getIRType (FSHvecValType o) in
      let tptyp := TYPE_Pointer ttyp in
      let '(st, pt) := incLocal st in
      let '(st, init_block_id) := incBlockNamed st "MemInit_init" in
      let '(st, loopcontblock) := incBlockNamed st "MemInit_init_lcont" in
      let '(st, loopvar) := incLocalNamed st "MemInit_init_i" in
      let '(st, void0) := incVoid st in
      let '(st, storeid) := incVoid st in
      let init_block :=
          {|
            blk_id    := init_block_id ;
            blk_phis  := [];
            blk_code  := [
                          (IId pt,  INSTR_Op (OP_GetElementPtr
                                                ttyp (tptyp, (EXP_Ident y))
                                                [(IntType, EXP_Integer 0%Z);
                                                   (IntType,(EXP_Ident (ID_Local loopvar)))]

                          ));

                            (IVoid storeid, INSTR_Store false
                                                        (TYPE_Double, ini)
                                                        (TYPE_Pointer TYPE_Double,
                                                         (EXP_Ident (ID_Local pt)))
                                                        (ret 8%Z))



                        ];
            blk_term  := (IVoid void0, TERM_Br_1 loopcontblock);
            blk_comments := None
          |} in
      genWhileLoop "MemInit_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock init_block_id [init_block] [] st nextblock.

  Definition genPower
             (x y: ident)
             (n: NExpr)
             (f: AExpr)
             (initial: binary64)
             (st: IRState)
             (nextblock: block_id): m (IRState * segment)
    :=
      let '(st, loopcontblock) := incBlockNamed st "Power_lcont" in
      let '(st, loopvar) := incLocalNamed st "Power_i" in
      let xytyp := getIRType (FSHvecValType 1) in
      let xyptyp := TYPE_Pointer xytyp in
      let '(st, py) := incLocal st in
      let '(st, storeid0) := incVoid st in
      let '(st, void1) := incVoid st in
      '(st, nexp, ncode) <- genNExpr st n ;;
       let ini := genFloatV initial in
       let init_code := ncode ++ [
                                (IId py,  INSTR_Op (OP_GetElementPtr
                                                      xytyp (xyptyp, (EXP_Ident y))
                                                      [(IntType, EXP_Integer 0%Z);
                                                         (IntType,EXP_Integer 0%Z)]

                                ));

                                  (IVoid storeid0, INSTR_Store false
                                                               (TYPE_Double, ini)
                                                               (TYPE_Pointer TYPE_Double,
                                                                (EXP_Ident (ID_Local py)))
                                                               (ret 8%Z))

                              ] in

       let '(st, body_block_id) := incBlockNamed st "PowerLoopBody" in
       let '(st, storeid1) := incVoid st in
       let '(st, void2) := incVoid st in
       let '(st, px) := incLocal st in
       let '(st, yv) := incLocal st in
       let '(st, xv) := incLocal st in
       let st := addVars st [(ID_Local yv, TYPE_Double); (ID_Local xv, TYPE_Double)] in
       '(st, fexpr, fexpcode) <- genAExpr st f ;;
        st <- dropVars st 2 ;;
        let body_block := {|
              blk_id    := body_block_id ;
              blk_phis  := [];
              blk_code  := [
                            (IId px,  INSTR_Op (OP_GetElementPtr
                                                  xytyp (xyptyp, (EXP_Ident x))
                                                  [(IntType, EXP_Integer 0%Z);
                                                     (IntType,EXP_Integer 0%Z)]

                            ));
                              (IId yv, INSTR_Load false TYPE_Double
                                                  (TYPE_Pointer TYPE_Double,
                                                   (EXP_Ident (ID_Local py)))
                                                  (ret 8%Z));
                              (IId xv, INSTR_Load false TYPE_Double
                                                  (TYPE_Pointer TYPE_Double,
                                                   (EXP_Ident (ID_Local px)))
                                                  (ret 8%Z))
                          ]
                             ++ fexpcode ++
                             [
                               (IVoid storeid1, INSTR_Store false
                                                            (TYPE_Double, fexpr)
                                                            (TYPE_Pointer TYPE_Double,
                                                             (EXP_Ident (ID_Local py)))
                                                            (ret 8%Z))
                             ];
              blk_term  := (IVoid void2, TERM_Br_1 loopcontblock);
              blk_comments := None
            |} in
        genWhileLoop "Power" (EXP_Integer 0%Z) nexp loopvar loopcontblock body_block_id [body_block] init_code st nextblock.
        

  Definition resolve_PVar (vars: list (ident * typ)) (p:PExpr): m (ident*nat)
    :=
      match p with
      | PVar n =>
        '(l,t) <- opt2err "NVar out of range" (List.nth_error vars n) ;;
         match t with
         | TYPE_Pointer (TYPE_Array sz TYPE_Double) =>
           ret (l, Z.to_nat sz)
         | _ => raise "Invalid type of PVar"
         end
      end.

  Fixpoint genIR
           (fshcol: DSHOperator)
           (st: IRState)
           (nextblock: block_id):
    m (IRState * segment)
    :=
      let add_comment r s : m (IRState * segment) := '(st, (e, b)) <- r ;; ret (st,(e,add_comment b [s])) in

      match fshcol with
      | DSHNop =>
        let '(st, nopblock) := incBlockNamed st "Nop" in
        add_comment
          (ret (st, (nopblock,[])))
          "--- Operator: DSHNop ---"
      | DSHAssign (src_p,src_n) (dst_p,dst_n) =>
        '(x,i) <- resolve_PVar (vars st) src_p ;;
         '(y,o) <- resolve_PVar (vars st) dst_p ;;
         add_comment
         (genFSHAssign i o st x y src_n dst_n nextblock)
         "--- Operator: DSHAssign ---"
      | DSHIMap n x_p y_p f =>
        '(x,i) <- resolve_PVar (vars st) x_p ;;
         '(y,o) <- resolve_PVar (vars st) y_p ;;
         nat_eq_or_err "IMap dimensions do not match" i o ;;
         let '(st, loopcontblock) := incBlockNamed st "IMap_lcont" in
         let '(st, loopvar) := incLocalNamed st "IMap_i" in
         '(st, (body_entry, body_blocks)) <- genIMapBody i x y f st loopvar loopcontblock ;;
          add_comment
          (genWhileLoop "IMap" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat i)) loopvar loopcontblock body_entry body_blocks [] st nextblock)
          "--- Operator: DSHIMap ---"
      | DSHBinOp n x_p y_p f =>
        let '(st, loopcontblock) := incBlockNamed st "BinOp_lcont" in
        '(x,i) <- resolve_PVar (vars st) x_p ;;
         '(y,o) <- resolve_PVar (vars st) y_p ;;
         let vs := string_of_vars (vars st) in
         nat_eq_or_err "BinOp input dimensions do not match" i (n+n) ;;
         nat_eq_or_err (append "BinOp output dimensions do not match" vs) o n ;;
         let '(st, loopvar) := incLocalNamed st "BinOp_i" in
         '(st, (body_entry, body_blocks)) <- genBinOpBody n x y f st loopvar loopcontblock ;;
          add_comment
          (genWhileLoop "BinOp" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] st nextblock)
         "--- Operator: DSHBinOp ---"
      | DSHMemMap2 n x0_p x1_p y_p f =>
        let '(st, loopcontblock) := incBlockNamed st "MemMap2_lcont" in
        '(x0,i0) <- resolve_PVar (vars st) x0_p ;;
         '(x1,i1) <- resolve_PVar (vars st) x1_p ;;
         '(y,o) <- resolve_PVar (vars st) y_p ;;
         nat_eq_or_err "MemMap2 output dimensions do not match" o n ;;
         nat_eq_or_err "MemMap2 input 1 dimensions do not match" i0 n ;;
         nat_eq_or_err "MemMap2 input 2 dimensions do not match" i1 n ;;
         let '(st, loopvar) := incLocalNamed st "MemMap2_i" in
         '(st, (body_entry, body_blocks)) <- genMemMap2Body n x0 x1 y f st loopvar loopcontblock ;;
          add_comment
          (genWhileLoop "MemMap2" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] st nextblock)
         "--- Operator: DSHMemMap2 ---"
      | DSHPower n (src_p,src_n) (dst_p,dst_n) f initial =>
        '(x,i) <- resolve_PVar (vars st) src_p ;;
         '(y,o) <- resolve_PVar (vars st) dst_p ;;
         add_comment
         (genPower x y n f initial st nextblock)
         "--- Operator: DSHPower ---"
      | DSHLoop n body =>
        let '(st, loopcontblock) := incBlockNamed st "Union_lcont" in

        let '(st, loopvar) := incLocalNamed st "Union_i" in
        '(st,(child_block_id, child_blocks)) <- genIR body st loopcontblock ;;
         add_comment
         (genWhileLoop "Union_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock child_block_id child_blocks[] st nextblock)
         "--- Operator: DSHLoop ---"
      | DSHAlloc size body =>
         let '(st, aname) := newLocalVar st (TYPE_Pointer (getIRType (FSHvecValType size))) in
        '(st, (bblock, bcode)) <- genIR body st nextblock ;;
         let '(st,(ablock,acode)) := allocTempArrayBlock st aname bblock size in
         add_comment (ret (st, (ablock, [acode]++bcode))) "--- Operator: DSHAlloc ---"
      | DSHMemInit size y_p value =>
        '(y,o) <- resolve_PVar (vars st) y_p ;;
         '(st,(ablock,acode)) <- genMemInit o size y value st nextblock ;;
         add_comment (ret (st, (ablock, acode))) "--- Operator: DSHMemInit ---"
      | DSHMemCopy size x_p y_p =>
        '(x,i) <- resolve_PVar (vars st) x_p ;;
         '(y,o) <- resolve_PVar (vars st) y_p ;;
         nat_eq_or_err "MemCopy input/output dimensions do not match" i o ;;
         add_comment
         (genMemCopy size st x y nextblock)
         "--- Operator: DSHMemCopy ---"
      | DSHSeq f g =>
        let vars := vars st in
        '(st, (gb, g')) <- genIR g st nextblock ;;
         '(st, (fb, f')) <- genIR f st gb ;;
         let st := setVars st vars in
         add_comment (ret (st, (fb, g'++f'))) "--- Operator: DSHSeq ---"
      end.

  Definition LLVMGen'
             (i o: nat)
             (globals: list (string*FSHValType))
             (globals_extern: bool)
             (fshcol: DSHOperator)
             (funname: string)
    : m (toplevel_entities typ (list (block typ)))
    :=
      let x := Name "X" in
      let xtyp := TYPE_Pointer (getIRType (FSHvecValType i)) in
      let y := Name "Y" in
      let ytyp := TYPE_Pointer (getIRType (FSHvecValType o)) in
      let st := newState in

      (* Add globals *)
      let st :=
          addVars st
                  (List.map
                     (fun g:(string* FSHValType) =>
                        let (n,t) := g in (ID_Global (Name n), TYPE_Pointer (getIRType t)))
                     globals) in (* TODO: check order of globals. Maybe reverse. *)

      (* Add parameters as locals *)
      let st := addVars st [(ID_Local x, xtyp);(ID_Local y, ytyp)] in

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
      '(st,(_,body)) <- genIR fshcol st rid ;;
       let body := body ++ [retblock] in
       let all_intrinsics:toplevel_entities typ (list (block typ))
           := [TLE_Comment "Prototypes for intrinsics we use"]
                ++ (List.map (TLE_Declaration) (
                               helix_intrinsics_decls ++ defined_intrinsics_decls))
       in
       ret
         (all_intrinsics ++
                         (if globals_extern then
                            (genIRGlobals (FnBody:=list (block typ)) globals) else []) ++
                         [
                           TLE_Comment "Top-level operator definition" ;
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
           (i o: nat)
           (globals: list (string* FSHValType))
           (fshcol: DSHOperator)
           (funname: string)
  := LLVMGen' (m := sum string) i o globals true fshcol funname.
