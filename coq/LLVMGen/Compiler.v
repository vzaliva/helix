Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.Util.Misc.
Require Import Helix.Tactics.HelixTactics.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.IntrinsicsDefinitions.
Require Import Vellvm.Numeric.Floats.
Require Import Vellvm.LLVMAst.
Require Import Helix.Util.ErrorSetoid.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import ExtLib.Structures.Monads.
Require Import Helix.Util.ErrorWithState.
Require Import Helix.LLVMGen.Data.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.

(* Both [String] and [List] define [(++)] notation. We use both.
   To avoid implicit scoping, we re-define one for String *)
Notation "x @@ y" := (String.append x y) (right associativity, at level 60) : string_scope.

Section withErrorStateMonad.

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

  Definition cerr := errS IRState.

  Definition setVars (s:IRState) (newvars:list (ident * typ)): IRState :=
    {|
      block_count := block_count s ;
      local_count := local_count s ;
      void_count  := void_count s ;
      vars := newvars
    |}.

  (* Returns n-th varable from state or error if [n] index oob *)
  Definition getStateVar (msg:string) (n:nat): cerr (ident * typ) :=
    st <- get ;;
    option2errS msg (List.nth_error (vars st) n).

  (* for debugging and error reporting *)
  Definition getVarsAsString : cerr string :=
    st <- get ;;
    ret (string_of_vars (vars st)).

  Definition nat_eq_or_cerr msg a b : cerr _ := err2errS  (nat_eq_or_err msg a b).

End withErrorStateMonad.

(* 64-bit IEEE floats *)
Definition SizeofFloatT := 8.

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
     | _::_ => [TLE_Comment "Global variables"] ++ l
     end.

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
  | b::bs => (add_comments b xs)::bs
  end.

Definition incBlockNamed (prefix:string): (cerr block_id) :=
  st <- get  ;;
  put
    {|
      block_count := S (block_count st);
      local_count := local_count st ;
      void_count := void_count st ;
      vars := vars st
    |} ;;
  ret (Name (prefix ++ string_of_nat (block_count st))).

Definition incBlock := incBlockNamed "b".

Definition incLocalNamed (prefix:string): (cerr raw_id) :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := vars st
    |} ;;
  ret (Name (prefix @@ string_of_nat (local_count st))).

Definition incLocal := incLocalNamed "l".

Definition incVoid: (cerr int) :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := S (void_count st) ;
      vars := vars st
    |} ;;
  ret (Z.of_nat (void_count st)).

Definition addVars (newvars: list (ident * typ)): cerr unit :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      vars := newvars ++ vars st
    |}.

Definition newLocalVar (t:typ) (prefix:string): (cerr raw_id) :=
  st <- get ;;
  let v := Name (prefix @@ string_of_nat (local_count st)) in
  put
    {|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      vars := [(ID_Local v,t)] ++ (vars st)
    |} ;;
  ret v.

Definition intrinsic_exp (d:declaration typ): exp typ :=
  EXP_Ident (ID_Global (dc_name d)).

(* TODO: move *)
Fixpoint drop_err {A:Type} (n:nat) (lst:list A) : err (list A)
  := match n, lst with
     | O, xs => ret xs
     | S n', (_::xs) => drop_err n' xs
     | _, _ => raise "drop on empty list"
     end.

Definition dropVars (n: nat): cerr unit :=
  st <- get ;;
  vars' <- err2errS (drop_err n (vars st)) ;;
  put {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      vars := vars'
    |}.

Definition allocTempArrayCode (name: local_id) (size:nat)
  :=
    [(IId name, INSTR_Alloca (getIRType (FSHvecValType size)) None (Some PtrAlignment))].

Definition allocTempArrayBlock
           (name: local_id)
           (nextblock: block_id)
           (size: nat): (cerr (local_id * (block typ)))
  :=
    retid <- incVoid ;;
    bid <- incBlock ;;
    ret (bid,
         {|
           blk_id    := bid ;
           blk_phis  := [];
           blk_code  := allocTempArrayCode name size;
           blk_term  := (IVoid retid, TERM_Br_1 nextblock) ;
           blk_comments := None
         |}).

Fixpoint genNExpr
         (nexp: NExpr) :
  cerr ((exp typ) * (code typ))
  :=
    let gen_binop a b iop :=
        '(aexp, acode) <- genNExpr a ;;
        '(bexp, bcode) <- genNExpr b ;;
        res <- incLocal ;;
        ret (EXP_Ident (ID_Local res),
             acode ++ bcode ++
                   [(IId res, INSTR_Op (OP_IBinop iop
                                                  IntType
                                                  aexp
                                                  bexp))
            ]) in
    match nexp with
    | NVar n => '(i,t) <- getStateVar "NVar out of range" n ;;
                match t, IntType with
                | TYPE_I z, TYPE_I zi =>
                  if Z.eq_dec z zi then
                    ret (EXP_Ident i, [])
                  else
                    (svars <- getVarsAsString ;;
                     raise ("NVar #" @@ string_of_nat n @@ " dimensions mismatch in " @@ svars))
                | TYPE_Pointer (TYPE_I z), TYPE_I zi =>
                  if Z.eq_dec z zi then
                    res <- incLocal ;;
                    ret (EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false (IntType)
                                               (TYPE_Pointer (IntType),
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  else
                    (svars <- getVarsAsString ;;
                     raise ("NVar #" @@ string_of_nat n @@ " pointer type mismatch in " @@ svars))
                | _,_ =>
                  svars <- getVarsAsString ;;
                  raise ("NVar #" @@ string_of_nat n @@ " type mismatch in " @@ svars)
                end
    | NConst v => ret (EXP_Integer (Z.of_nat v), [])
    | NDiv   a b => gen_binop a b (SDiv true)
    | NMod   a b => gen_binop a b SRem
    | NPlus  a b => gen_binop a b (Add true true)
    | NMinus a b => gen_binop a b (Sub true true)
    | NMult  a b => gen_binop a b (Mul true true)
    | NMin   a b => raise "NMin not implemented" (* TODO *)
    | NMax   a b => raise "NMax not implemented" (* TODO *)
    end.

Definition genMExpr
           (mexp: MExpr)
  :
    cerr ((exp typ) * (code typ) * typ)
  := match mexp with
     | MPtrDeref (PVar x) => '(i,t) <- getStateVar "PVar un MPtrDeref out of range" x ;;
                             match t with
                             | TYPE_Pointer (TYPE_Array zi TYPE_Double) =>
                               ret (EXP_Ident i, [], (TYPE_Array zi TYPE_Double))
                             | _  =>
                               svars <- getVarsAsString ;;
                               raise ("MPtrDeref's PVar #" @@ string_of_nat x @@ " type mismatch in " @@ svars)
                             end
     | MConst c => raise "MConst not implemented" (* TODO *)
     end.

Fixpoint genAExpr
         (fexp: AExpr) :
  cerr ((exp typ) * (code typ))
  :=
    let gen_binop a b fop :=
        '(aexp, acode) <- genAExpr a ;;
        '(bexp, bcode) <- genAExpr b ;;
        res <- incLocal ;;
        ret (EXP_Ident (ID_Local res),
             acode ++ bcode ++
                   [(IId res, INSTR_Op (OP_FBinop fop
                                                  [] (* TODO: list fast_math *)
                                                  TYPE_Double
                                                  aexp
                                                  bexp))
            ]) in
    let gen_call1 a f :=
        '(aexp, acode) <- genAExpr a ;;
        res <- incLocal ;;
        let ftyp := TYPE_Double in
        ret (EXP_Ident (ID_Local res),
             acode ++
                   [(IId res, INSTR_Call (ftyp,f) [(ftyp,aexp)])
            ]) in
    let gen_call2 a b f :=
        '(aexp, acode) <- genAExpr a ;;
        '(bexp, bcode) <- genAExpr b ;;
        res <- incLocal ;;
        let ftyp := TYPE_Double in
        ret (EXP_Ident (ID_Local res),
             acode ++ bcode ++
                   [(IId res, INSTR_Call (ftyp,f)
                                         [(ftyp,aexp); (ftyp,bexp)])
            ]) in
    match fexp with
    | AVar n => '(i,t) <- getStateVar "AVar out of range" n ;;
                match t with
                | TYPE_Double => ret (EXP_Ident i, [])
                | TYPE_Pointer TYPE_Double =>
                  res <- incLocal ;;
                  ret (EXP_Ident (ID_Local res),
                       [(IId res, INSTR_Load false TYPE_Double
                                             (TYPE_Pointer TYPE_Double,
                                              (EXP_Ident i))
                                             (ret 8%Z))])
                | _ =>
                  svars <- getVarsAsString ;;
                  raise ("AVar #" @@ string_of_nat n @@ " type mismatch in " @@ svars)
                end
    | AConst v => ret (EXP_Double v, [])
    | ANth vec i =>
      '(iexp, icode) <- genNExpr i ;;
      '(vexp, vcode, xtyp) <- genMExpr vec ;;
      px <- incLocal ;;
      let xptyp := TYPE_Pointer xtyp in
      res <- incLocal ;;
      ret (EXP_Ident (ID_Local res),
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
      '(aexp, acode) <- genAExpr a ;;
      '(bexp, bcode) <- genAExpr b ;;
      ires <- incLocal ;;
      fres <- incLocal ;;
      void0 <- incVoid ;;
      ret (EXP_Ident (ID_Local fres),
           acode ++ bcode ++
                 [(IId ires, INSTR_Op (OP_FCmp FOlt
                                               TYPE_Double
                                               aexp
                                               bexp));
                    (IVoid void0, INSTR_Comment "Casting bool to float") ;
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
           (x y: ident)
           (nextblock: block_id)
  : cerr segment
  :=
    entryblock <- incBlockNamed "MemCopy" ;;
    retentry <- incVoid ;;
    callid <- incVoid ;;
    xb <- incLocal ;;
    yb <- incLocal ;;
    let oz := (Z.of_nat o) in
    let atyp := TYPE_Pointer (TYPE_Array oz TYPE_Double) in
    let ptyp := TYPE_Pointer (TYPE_I 8%Z) in
    let len:Z := Z.of_nat (o * SizeofFloatT) in
    let i32 := TYPE_I 32%Z in
    let i1 := TYPE_I 1%Z in
    ret ((entryblock, [
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
           (x y: ident)
           (src dst: NExpr)
           (nextblock: block_id)
  : cerr segment
  :=
    entryblock <- incBlockNamed "Assign" ;;
    retentry <- incVoid ;;
    storeid <- incVoid ;;
    px <- incLocal ;;
    py <- incLocal ;;
    v <- incLocal ;;
    let xtyp := getIRType (FSHvecValType i) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (FSHvecValType o) in
    let yptyp := TYPE_Pointer ytyp in
    '(src_nexpr, src_nexpcode) <- genNExpr src  ;;
    '(dst_nexpr, dst_nexpcode) <- genNExpr dst  ;;
    ret (entryblock, [
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
        ]).

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
           (nextblock: block_id)
  : cerr segment
  :=
    entryblock <- incBlockNamed (prefix @@ "_entry") ;;
    loopblock <- incBlockNamed (prefix @@ "_loop") ;;
    loopcond <- incLocal ;;
    loopcond1 <- incLocal ;;
    nextvar <- incLocalNamed (prefix @@ "_next_i") ;;
    void0 <- incVoid ;;
    void1 <- incVoid ;;
    retloop <- incVoid ;;

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
    ret (entryblock, loop_pre ++ body_blocks ++ loop_post).

Definition genIMapBody
           (n: nat)
           (x y: ident)
           (f: AExpr)
           (loopvar: raw_id)
           (nextblock: block_id)
  : cerr segment
  :=
    pwblock <- incBlockNamed "IMapLoopBody" ;;
    pwret <- incVoid ;;
    storeid <- incVoid ;;
    px <- incLocal ;;
    py <- incLocal ;;
    v <- incLocal ;;
    let xytyp := getIRType (FSHvecValType n) in
    let xyptyp := TYPE_Pointer xytyp in
    let loopvarid := ID_Local loopvar in
    addVars [(ID_Local v, TYPE_Double); (loopvarid, IntType)] ;;
    '(fexpr, fexpcode) <- genAExpr f ;;
    dropVars 2 ;;
    ret (pwblock,
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
        ]).

Definition genBinOpBody
           (n: nat)
           (x y: ident)
           (f: AExpr)
           (loopvar: raw_id)
           (nextblock: block_id)
  : cerr segment
  :=
    binopblock <- incBlockNamed "BinOpLoopBody" ;;
    binopret <- incVoid ;;
    storeid <- incVoid ;;
    loopvar2 <- incLocal ;;
    px0 <- incLocal ;;
    px1 <- incLocal ;;
    py <- incLocal ;;
    v0 <- incLocal ;;
    v1 <- incLocal ;;
    let xtyp := getIRType (FSHvecValType (n+n)) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (FSHvecValType n) in
    let yptyp := TYPE_Pointer ytyp in
    let loopvarid := ID_Local loopvar in
    addVars [(ID_Local v1, TYPE_Double); (ID_Local v0, TYPE_Double); (loopvarid, IntType)] ;;
    '(fexpr, fexpcode) <- genAExpr f ;;
    dropVars 3 ;;
    ret (binopblock,
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
        ]).

Definition genMemMap2Body
           (n: nat)
           (x0 x1 y: ident)
           (f: AExpr)
           (loopvar: raw_id)
           (nextblock: block_id)
  : cerr segment
  :=
    binopblock <- incBlockNamed "MemMap2LoopBody" ;;
    binopret <- incVoid ;;
    storeid <- incVoid ;;
    px0 <- incLocal ;;
    px1 <- incLocal ;;
    py <- incLocal ;;
    v0 <- incLocal ;;
    v1 <- incLocal ;;
    let xtyp := getIRType (FSHvecValType n) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (FSHvecValType n) in
    let yptyp := TYPE_Pointer ytyp in
    let loopvarid := ID_Local loopvar in
    addVars [(ID_Local v1, TYPE_Double); (ID_Local v0, TYPE_Double)] ;;
    '(fexpr, fexpcode) <- genAExpr f ;;
    dropVars 2 ;;
    ret (binopblock,
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
        ]).

Definition genMemInit
           (o n: nat)
           (y: ident)
           (initial: binary64)
           (nextblock: block_id):
  cerr segment
  :=
    let ini := genFloatV initial in
    let ttyp := getIRType (FSHvecValType o) in
    let tptyp := TYPE_Pointer ttyp in
    pt <- incLocal ;;
    init_block_id <- incBlockNamed "MemInit_init" ;;
    loopcontblock <- incBlockNamed "MemInit_init_lcont" ;;
    loopvar <- incLocalNamed "MemInit_init_i" ;;
    void0 <- incVoid ;;
    storeid <- incVoid ;;
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
    genWhileLoop "MemInit_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat o)) loopvar loopcontblock init_block_id [init_block] [] nextblock.

Definition genPower
           (x y: ident)
           (n: NExpr)
           (f: AExpr)
           (initial: binary64)
           (nextblock: block_id): cerr segment
  :=
    loopcontblock <- incBlockNamed "Power_lcont" ;;
    loopvar <- incLocalNamed "Power_i" ;;
    let xytyp := getIRType (FSHvecValType 1) in
    let xyptyp := TYPE_Pointer xytyp in
    py <- incLocal ;;
    storeid0 <- incVoid ;;
    void1 <- incVoid ;;
    '(nexp, ncode) <- genNExpr n ;;
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

    body_block_id <- incBlockNamed "PowerLoopBody" ;;
    storeid1 <- incVoid ;;
    void2 <- incVoid ;;
    px <- incLocal ;;
    yv <- incLocal ;;
    xv <- incLocal ;;
    addVars [(ID_Local yv, TYPE_Double); (ID_Local xv, TYPE_Double)] ;;
    '(fexpr, fexpcode) <- genAExpr f ;;
    dropVars 2 ;;
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
    genWhileLoop "Power" (EXP_Integer 0%Z) nexp loopvar loopcontblock body_block_id [body_block] init_code nextblock.

Definition resolve_PVar (p:PExpr): cerr (ident*nat)
  :=
    svars <- getVarsAsString ;;
    match p with
    | PVar n =>
      let ns := string_of_nat n in
      '(l,t) <- getStateVar ("NVar#" @@ ns @@ " out of range in " @@ svars) n ;;
      match t with
      | TYPE_Pointer (TYPE_Array sz TYPE_Double) =>
        ret (l, Z.to_nat sz)
      | _ => raise ("Invalid type of PVar#" @@ ns @@ " in " @@ svars)
      end
    end.

Fixpoint genIR
         (fshcol: DSHOperator)
         (nextblock: block_id):
  cerr segment
  :=
    let fshcol_s := string_of_DSHOperator fshcol in
    let op_s := ("--- Operator: " @@ fshcol_s @@ "---") in
    let add_comment r : cerr (segment) := '((e, b)) <- r ;; ret (e,add_comment b [op_s]) in
    catch (
        match fshcol with
        | DSHNop =>
          nopblock <- incBlockNamed "Nop" ;;
          add_comment
            (ret (nopblock,[]))
        | DSHAssign (src_p,src_n) (dst_p,dst_n) =>
          '(x,i) <- resolve_PVar src_p ;;
          '(y,o) <- resolve_PVar dst_p ;;
          add_comment
            (genFSHAssign i o x y src_n dst_n nextblock)
        | DSHIMap n x_p y_p f =>
          '(x,i) <- resolve_PVar x_p ;;
          '(y,o) <- resolve_PVar y_p ;;
          vs <- getVarsAsString ;;
          nat_eq_or_cerr (fshcol_s @@ " dimensions do not match in " @@ vs) i o ;;
          loopcontblock <- incBlockNamed "IMap_lcont" ;;
          loopvar <- incLocalNamed "IMap_i" ;;
          '(body_entry, body_blocks) <- genIMapBody i x y f loopvar loopcontblock ;;
          add_comment
            (genWhileLoop "IMap" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat i)) loopvar loopcontblock body_entry body_blocks [] nextblock)
        | DSHBinOp n x_p y_p f =>
          loopcontblock <- incBlockNamed "BinOp_lcont" ;;
          '(x,i) <- resolve_PVar x_p ;;
          '(y,o) <- resolve_PVar y_p ;;
          vs <- getVarsAsString ;;
          nat_eq_or_cerr (fshcol_s @@ " input dimensions do not match in " @@ vs) i (n+n) ;;
          nat_eq_or_cerr (fshcol_s @@ " output dimensions do not match in " @@ vs) o n ;;
          loopvar <- incLocalNamed "BinOp_i" ;;
          '(body_entry, body_blocks) <- genBinOpBody n x y f loopvar loopcontblock ;;
          add_comment
            (genWhileLoop "BinOp" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock)
        | DSHMemMap2 n x0_p x1_p y_p f =>
          loopcontblock <- incBlockNamed "MemMap2_lcont" ;;
          '(x0,i0) <- resolve_PVar x0_p ;;
          '(x1,i1) <- resolve_PVar x1_p ;;
          '(y,o) <- resolve_PVar y_p ;;
          vs <- getVarsAsString ;;
          nat_eq_or_cerr (fshcol_s @@ " output dimensions do not match in " @@ vs) o n ;;
          nat_eq_or_cerr (fshcol_s @@ " input 1 dimensions do not match in " @@ vs) i0 n ;;
          nat_eq_or_cerr (fshcol_s @@ " input 2 dimensions do not match in " @@ vs) i1 n ;;
          loopvar <- incLocalNamed "MemMap2_i" ;;
          '(body_entry, body_blocks) <- genMemMap2Body n x0 x1 y f loopvar loopcontblock ;;
          add_comment
            (genWhileLoop "MemMap2" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock)
        | DSHPower n (src_p,src_n) (dst_p,dst_n) f initial =>
          '(x,i) <- resolve_PVar src_p ;;
          '(y,o) <- resolve_PVar dst_p ;;
          add_comment
            (genPower x y n f initial nextblock)
        | DSHLoop n body =>
          loopcontblock <- incBlockNamed "Loop_lcont" ;;

          loopvar <- newLocalVar IntType "Loop_i" ;;
          '(child_block_id, child_blocks) <- genIR body loopcontblock ;;
          dropVars 1 ;;
          add_comment
            (genWhileLoop "Loop_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                          loopvar loopcontblock child_block_id child_blocks[] nextblock)
        | DSHAlloc size body =>
          aname <- newLocalVar (TYPE_Pointer (getIRType (FSHvecValType size))) "a" ;;
          '(bblock, bcode) <- genIR body nextblock ;;
          '(ablock,acode) <- allocTempArrayBlock aname bblock size ;;
          dropVars 1 ;;
          add_comment (ret (ablock, [acode]++bcode))
        | DSHMemInit size y_p value =>
          '(y,o) <- resolve_PVar y_p ;;
          '(ablock,acode) <- genMemInit o size y value nextblock ;;
          add_comment (ret (ablock, acode))
        | DSHMemCopy size x_p y_p =>
          '(x,i) <- resolve_PVar x_p ;;
          '(y,o) <- resolve_PVar y_p ;;
          vs <- getVarsAsString ;;
          nat_eq_or_cerr (fshcol_s @@ " input/output dimensions do not match in " @@ vs) i o ;;
          add_comment
            (genMemCopy size x y nextblock)
        | DSHSeq f g =>
          '(gb, g') <- genIR g nextblock ;;
          '(fb, f') <- genIR f gb ;;
          add_comment (ret (fb, f'++g'))
        end)
          (fun m => raise (m @@ " in " @@ fshcol_s)).

Definition LLVMGen
           (i o: nat)
           (globals: list (string*FSHValType))
           (globals_extern: bool)
           (fshcol: DSHOperator)
           (funname: string)
  : cerr (toplevel_entities typ (list (block typ)))
  :=
    let x := Name "X" in
    let xtyp := TYPE_Pointer (getIRType (FSHvecValType i)) in
    let y := Name "Y" in
    let ytyp := TYPE_Pointer (getIRType (FSHvecValType o)) in

    (* Add parameters as locals X=PVar 1, Y=PVar 0 *)
    addVars [(ID_Local y, ytyp);(ID_Local x, xtyp)] ;;

    (* Add globals *)
    addVars
      (List.map
         (fun g:(string* FSHValType) =>
            let (n,t) := g in (ID_Global (Name n), TYPE_Pointer (getIRType t)))
         globals) ;; (* TODO: check order of globals. Maybe reverse. *)

    rid <- incBlock ;;
    rsid <- incBlock ;;
    let retblock :=
        {|
          blk_id    := rid ;
          blk_phis  := [];
          blk_code  := [];
          blk_term  := (IId rsid, TERM_Ret_void);
          blk_comments := None
        |} in
    '(_,body) <- genIR fshcol rid ;;
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


Definition initOneIRGlobal
           (t: FSHValType)
           (data: list binary64)
           (nm: string)
  : err (list binary64 * (toplevel_entity typ (list (block typ))))
  :=
    match t with
    | FSHnatValType => raise "FSHnatValType global type not supported"
    | FSHFloatValType =>
      let '(x, data) := rotate Float64Zero data in
      let g := TLE_Global {|
                   g_ident        := Name nm;
                   g_typ          := getIRType t ;
                   g_constant     := true ;
                   g_exp          := Some (EXP_Double x);
                   g_linkage      := Some LINKAGE_Internal ;
                   g_visibility   := None ;
                   g_dll_storage  := None ;
                   g_thread_local := None ;
                   g_unnamed_addr := true ;
                   g_addrspace    := None ;
                   g_externally_initialized := false ;
                   g_section      := None ;
                   g_align        := None ; (* TODO: maybe need to alight to 64-bit boundary? *)
                 |} in
      ret (data, g)
    | FSHvecValType n =>
      let (data, arr) := constArray n data in
      let g := TLE_Global {|
                   g_ident        := Name nm;
                   g_typ          := getIRType t ;
                   g_constant     := true ;
                   g_exp          := Some (EXP_Array arr);
                   g_linkage      := Some LINKAGE_Internal ;
                   g_visibility   := None ;
                   g_dll_storage  := None ;
                   g_thread_local := None ;
                   g_unnamed_addr := true ;
                   g_addrspace    := None ;
                   g_externally_initialized := false ;
                   g_section      := None ;
                   g_align        := Some Utils.PtrAlignment ;
                 |} in
      ret (data, g)
    end.


Definition globals_name_present
           (name:string)
           (l:list (string * FSHValType)) : bool
  :=
    List.fold_right (fun v f => orb f (string_beq (fst v) name)) false l.

Fact nth_to_globals_name_present (globals:list (string * FSHValType)) nm :
  (exists res j, (nth_error globals j = Some res /\ fst res = nm))
  ->
  globals_name_present nm globals = true.
Proof.
  revert nm.
  unfold globals_name_present.
  induction globals.
  -
    cbn.
    intros.
    exfalso.
    destruct H as [res [j [H0 H1]]].
    rewrite Util.nth_error_nil in H0.
    inv H0.
  -
    intros.
    destruct H as [res [j H]].
    specialize (IHglobals nm).
    cbn.
    apply orb_true_iff.
    destruct j.
    +
      right.
      cbn in H.
      destruct H.
      inv H.
      unfold Misc.string_beq.
      break_if; auto.
    +
      left.
      apply IHglobals.
      eauto.
Qed.

(* Could not use [monadic_fold_left] here because of error check. *)
Fixpoint initIRGlobals
         (data: list binary64)
         (x: list (string * FSHValType))
  : err (list binary64 * list (toplevel_entity typ (list (block typ))))
  :=  match x with
      | nil => ret (data,[])
      | cons (nm, t) xs =>
        if globals_name_present nm xs
        then
          inl ("duplicate global name: " ++ nm)%string
        else
          '(data,g) <- initOneIRGlobal t data nm ;;
          '(data,gs) <- initIRGlobals data xs ;;
          ret (data,g::gs)
      end.

(*
   When code genration generates [main], the input
   will be stored in pre-initialized [X] global variable.
 *)
Definition global_YX (i o:nat) (data:list binary64) x xtyp y ytyp:
  LLVMAst.toplevel_entities _ (list (LLVMAst.block typ))
  :=
    let '(data,ydata) := constArray o data in
    let '(_,xdata) := constArray i data in
    [ TLE_Global
        {|
          g_ident        := y;
          g_typ          := ytyp;
          g_constant     := true;
          g_exp          := Some (EXP_Array ydata);
          g_linkage      := None;
          g_visibility   := None;
          g_dll_storage  := None;
          g_thread_local := None;
          g_unnamed_addr := false;
          g_addrspace    := None;
          g_externally_initialized := false;
          g_section      := None;
          g_align        := None;
        |}
      ; TLE_Global
          {|
            g_ident        := x;
            g_typ          := xtyp;
            g_constant     := true;
            g_exp          := Some (EXP_Array xdata);
            g_linkage      := None;
            g_visibility   := None;
            g_dll_storage  := None;
            g_thread_local := None;
            g_unnamed_addr := false;
            g_addrspace    := None;
            g_externally_initialized := false;
            g_section      := None;
            g_align        := None;
          |}
    ].

Definition genMain
           (i o: nat)
           (op_name: string)
           (x:raw_id)
           (xptyp:typ)
           (y:raw_id)
           (ytyp:typ)
           (yptyp:typ)
           (globals: list (string * FSHValType))
           (data:list binary64)
  : LLVMAst.toplevel_entities _ (list (LLVMAst.block typ))
  :=
    let z := Name "z" in
    [
      TLE_Comment " Main function"
      ; TLE_Definition
          {|
            df_prototype   :=
              {|
                dc_name        := Name ("main") ;
                dc_type        := TYPE_Function ytyp [] ;
                dc_param_attrs := ([],
                                   []);
                dc_linkage     := None ;
                dc_visibility  := None ;
                dc_dll_storage := None ;
                dc_cconv       := None ;
                dc_attrs       := []   ;
                dc_section     := None ;
                dc_align       := None ;
                dc_gc          := None
              |} ;
            df_args        := [];
            df_instrs      := [
                               {|
                                 blk_id    := Name "main_block" ;
                                 blk_phis  := [];
                                 blk_code  :=
                                   [
                                     (IVoid 0%Z, INSTR_Call (TYPE_Void, EXP_Ident (ID_Global (Name op_name))) [(xptyp, EXP_Ident (ID_Global x)); (yptyp, EXP_Ident (ID_Global y))]) ;
                                   (IId z, INSTR_Load false ytyp (yptyp, EXP_Ident (ID_Global y)) None )
                                   ]
                                 ;

                                 blk_term  := (IId (Name "main_ret"), TERM_Ret (ytyp, EXP_Ident (ID_Local z))) ;
                                 blk_comments := None
                               |}

                             ]
          |}].

Definition compile (p: FSHCOLProgram) (just_compile:bool) (data:list binary64): err (toplevel_entities typ (list (block typ))) :=
  match p with
  | mkFSHCOLProgram i o name globals op =>
    '(data,ginit) <- initIRGlobals data globals ;;
    let ginit := app [TLE_Comment "Global variables"] ginit in

    if just_compile then
      evalErrS (LLVMGen i o globals just_compile op name) newState
    else
      let x := Anon 0%Z in
      let xtyp := getIRType (FSHvecValType i) in
      let xptyp := TYPE_Pointer xtyp in

      let y := Anon 1%Z in
      let ytyp := getIRType (FSHvecValType o) in
      let yptyp := TYPE_Pointer ytyp in

      let yxinit := global_YX i o data x xtyp y ytyp in
      let main := genMain i o name x xptyp y ytyp yptyp globals data in

      prog <- evalErrS (LLVMGen i o globals just_compile op name) newState ;;
      ret (ginit ++ yxinit ++ prog ++ main)%list
  end.

Definition compile_w_main (p: FSHCOLProgram): list binary64 -> err (toplevel_entities typ (list (block typ))) :=
  compile p false.
