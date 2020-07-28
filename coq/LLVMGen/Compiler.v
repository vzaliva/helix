Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.Util.Misc.
Require Import Helix.Tactics.HelixTactics.

Require Import Vellvm.IntrinsicsDefinitions.
Require Import Vellvm.Util.
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
        Γ: list (ident * typ)
      }.

  Definition newState: IRState :=
    {|
      block_count := 0 ;
      local_count := 0 ;
      void_count  := 0 ;
      Γ := []
    |}.

  Definition cerr := errS IRState.

  Definition setVars (s:IRState) (newvars:list (ident * typ)): IRState :=
    {|
      block_count := block_count s ;
      local_count := local_count s ;
      void_count  := void_count s ;
      Γ := newvars
    |}.

  (* Returns n-th varable from state or error if [n] index oob *)
  Definition getStateVar (msg:string) (n:nat): cerr (ident * typ) :=
    st <- get ;;
    option2errS msg (List.nth_error (Γ st) n).

  (* for debugging and error reporting *)
  Definition getVarsAsString : cerr string :=
    st <- get ;;
    ret (string_of_Γ (Γ st)).

  Definition nat_eq_or_cerr msg a b : cerr _ := err2errS (nat_eq_or_err msg a b).
  Definition Z_eq_or_cerr msg a b : cerr _ := err2errS (Z_eq_or_err msg a b).
  Definition Int64_eq_or_cerr msg a b : cerr _ := Z_eq_or_cerr msg
                                                               (Int64.intval a)
                                                               (Int64.intval b).

  Definition evalCErrS {St:Type} {A:Type} (c : errS St A) (initial : St) : cerr A :=
    match c initial with
    | inl msg => raise msg
    | inr (s,v) => ret v
    end.

End withErrorStateMonad.

(* 64-bit IEEE floats *)
Definition SizeofFloatT: nat := 8.

Definition getIRType (t: DSHType): typ :=
  match t with
  | DSHnat => IntType
  | DSHCType => TYPE_Double
  | DSHPtr n => TYPE_Array (Int64.intval n) TYPE_Double
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
      Γ := Γ st
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
      Γ := Γ st
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
      Γ := Γ st
    |} ;;
  ret (Z.of_nat (void_count st)).

Definition addVars (newvars: list (ident * typ)): cerr unit :=
  st <- get ;;
  put
    {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      Γ := newvars ++ Γ st
    |}.

Definition newLocalVar (t:typ) (prefix:string): (cerr raw_id) :=
  st <- get ;;
  let v := Name (prefix @@ string_of_nat (local_count st)) in
  put
    {|
      block_count := block_count st ;
      local_count := S (local_count st) ;
      void_count  := void_count st ;
      Γ := [(ID_Local v,t)] ++ (Γ st)
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
  Γ' <- err2errS (drop_err n (Γ st)) ;;
  put {|
      block_count := block_count st ;
      local_count := local_count st ;
      void_count  := void_count st ;
      Γ := Γ'
    |}.

Definition allocTempArrayCode (name: local_id) (size:Int64.int)
  :=
    [(IId name, INSTR_Alloca (getIRType (DSHPtr size)) None (Some PtrAlignment))].

Definition allocTempArrayBlock
           (name: local_id)
           (nextblock: block_id)
           (size: Int64.int): (cerr (local_id * (block typ)))
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
                    (sΓ <- getVarsAsString ;;
                     raise ("NVar #" @@ string_of_nat n @@ " dimensions mismatch in " @@ sΓ))
                | TYPE_Pointer (TYPE_I z), TYPE_I zi =>
                  if Z.eq_dec z zi then
                    res <- incLocal ;;
                    ret (EXP_Ident (ID_Local res),
                         [(IId res, INSTR_Load false (IntType)
                                               (TYPE_Pointer (IntType),
                                                (EXP_Ident i))
                                               (ret 8%Z))])
                  else
                    (sΓ <- getVarsAsString ;;
                     raise ("NVar #" @@ string_of_nat n @@ " pointer type mismatch in " @@ sΓ))
                | _,_ =>
                  sΓ <- getVarsAsString ;;
                  raise ("NVar #" @@ string_of_nat n @@ " type mismatch in " @@ sΓ)
                end
    | NConst v => ret (EXP_Integer (Int64.intval v), [])
    | NDiv   a b => gen_binop a b (UDiv false)
    | NMod   a b => gen_binop a b URem
    | NPlus  a b => gen_binop a b (Add false false)
    | NMinus a b => gen_binop a b (Sub false false)
    | NMult  a b => gen_binop a b (Mul false false)
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
                               sΓ <- getVarsAsString ;;
                               raise ("MPtrDeref's PVar #" @@ string_of_nat x @@ " type mismatch in " @@ sΓ)
                             end
     | MConst _ _ => raise "MConst not implemented" (* TODO *)
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
                  sΓ <- getVarsAsString ;;
                  raise ("AVar #" @@ string_of_nat n @@ " type mismatch in " @@ sΓ)
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

Definition genFSHAssign
           (i o: Int64.int)
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
    let xtyp := getIRType (DSHPtr i) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (DSHPtr o) in
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
           (i o: Int64.int)
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
    let xtyp := getIRType (DSHPtr i) in
    let ytyp := getIRType (DSHPtr o) in
    let xptyp := TYPE_Pointer xtyp in
    let yptyp := TYPE_Pointer ytyp in
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
                                                 xtyp (xptyp, (EXP_Ident x))
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
                                                    ytyp (yptyp, (EXP_Ident y))
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
           (i o: Int64.int)
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
    n' <- err2errS (MInt64asNT.from_nat n) ;;
    let xtyp := getIRType (DSHPtr i) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (DSHPtr o) in
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
           (i0 i1 o: Int64.int)
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
    let x0typ := getIRType (DSHPtr i0) in
    let x1typ := getIRType (DSHPtr i1) in
    let ytyp := getIRType (DSHPtr o) in
    let x0ptyp := TYPE_Pointer x0typ in
    let x1ptyp := TYPE_Pointer x1typ in
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
                                                  x0typ (x0ptyp, (EXP_Ident x0))
                                                  [(IntType, EXP_Integer 0%Z);
                                                     (IntType,(EXP_Ident loopvarid))]

                           ));

                             (IId v0, INSTR_Load false TYPE_Double
                                                 (TYPE_Pointer TYPE_Double,
                                                  (EXP_Ident (ID_Local px0)))
                                                 (ret 8%Z));

                             (IId px1,  INSTR_Op (OP_GetElementPtr
                                                    x1typ (x1ptyp, (EXP_Ident x1))
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
           (size: Int64.int)
           (y: ident)
           (initial: binary64)
           (nextblock: block_id):
  cerr segment
  :=
    let ini := genFloatV initial in
    let ttyp := getIRType (DSHPtr size) in
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
    genWhileLoop "MemInit_loop" (EXP_Integer 0%Z) (EXP_Integer (Int64.intval size)) loopvar loopcontblock init_block_id [init_block] [] nextblock.

Definition genPower
           (i o: Int64.int)
           (x y: ident)
           (src dst: NExpr)
           (n: NExpr)
           (f: AExpr)
           (initial: binary64)
           (nextblock: block_id): cerr segment
  :=
    loopcontblock <- incBlockNamed "Power_lcont" ;;
    loopvar <- incLocalNamed "Power_i" ;;

    let xtyp := getIRType (DSHPtr i) in
    let xptyp := TYPE_Pointer xtyp in
    let ytyp := getIRType (DSHPtr o) in
    let yptyp := TYPE_Pointer ytyp in
    '(src_nexpr, src_nexpcode) <- genNExpr src  ;;
    '(dst_nexpr, dst_nexpcode) <- genNExpr dst  ;;
    py <- incLocal ;;
    storeid0 <- incVoid ;;
    void1 <- incVoid ;;
    '(nexp, ncode) <- genNExpr n ;;
    let ini := genFloatV initial in
    let init_code := src_nexpcode ++ dst_nexpcode ++ ncode ++ [
                             (IId py,  INSTR_Op (OP_GetElementPtr
                                                   ytyp (yptyp, (EXP_Ident y))
                                                   [(IntType, EXP_Integer 0%Z);
                                                      (IntType,dst_nexpr)]

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
    addVars [(ID_Local xv, TYPE_Double); (ID_Local yv, TYPE_Double)] ;;
    '(fexpr, fexpcode) <- genAExpr f ;;
    dropVars 2 ;;
    let body_block := {|
          blk_id    := body_block_id ;
          blk_phis  := [];
          blk_code  := [
                        (IId px,  INSTR_Op (OP_GetElementPtr
                                              xtyp (xtyp, (EXP_Ident x))
                                              [(IntType, EXP_Integer 0%Z);
                                                 (IntType, src_nexpr)]

                        ));
                          (IId xv, INSTR_Load false TYPE_Double
                                              (TYPE_Pointer TYPE_Double,
                                               (EXP_Ident (ID_Local px)))
                                              (ret 8%Z));
                          (IId yv, INSTR_Load false TYPE_Double
                                              (TYPE_Pointer TYPE_Double,
                                               (EXP_Ident (ID_Local py)))
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

Definition resolve_PVar (p:PExpr): cerr (ident*Int64.int)
  :=
    sΓ <- getVarsAsString ;;
    match p with
    | PVar n =>
      let ns := string_of_nat n in
      '(l,t) <- getStateVar ("NVar#" @@ ns @@ " out of range in " @@ sΓ) n ;;
      match t with
      | TYPE_Pointer (TYPE_Array sz TYPE_Double) =>
        sz' <- err2errS (MInt64asNT.from_Z sz) ;;
        ret (l, sz')
      | _ => raise ("Invalid type of PVar#" @@ ns @@ " in " @@ sΓ)
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
          loopcontblock <- incBlockNamed "IMap_lcont" ;;
          loopvar <- incLocalNamed "IMap_i" ;;
          '(body_entry, body_blocks) <- genIMapBody i o x y f loopvar loopcontblock ;;
          add_comment
            (genWhileLoop "IMap" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock)
        | DSHBinOp n x_p y_p f =>
          loopcontblock <- incBlockNamed "BinOp_lcont" ;;
          '(x,i) <- resolve_PVar x_p ;;
          '(y,o) <- resolve_PVar y_p ;;
          loopvar <- incLocalNamed "BinOp_i" ;;
          '(body_entry, body_blocks) <- genBinOpBody i o n x y f loopvar loopcontblock ;;
          add_comment
            (genWhileLoop "BinOp" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock)
        | DSHMemMap2 n x0_p x1_p y_p f =>
          loopcontblock <- incBlockNamed "MemMap2_lcont" ;;
          '(x0,i0) <- resolve_PVar x0_p ;;
          '(x1,i1) <- resolve_PVar x1_p ;;
          '(y,o) <- resolve_PVar y_p ;;
          n' <- err2errS (MInt64asNT.from_nat n) ;;
          loopvar <- incLocalNamed "MemMap2_i" ;;
          '(body_entry, body_blocks) <- genMemMap2Body i0 i1 o x0 x1 y f loopvar loopcontblock ;;
          add_comment
            (genWhileLoop "MemMap2" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock)
        | DSHPower n (src_p,src_n) (dst_p,dst_n) f initial =>
          '(x,i) <- resolve_PVar src_p ;;
          '(y,o) <- resolve_PVar dst_p ;;
          add_comment
            (genPower i o x y src_n dst_n n f initial nextblock)
        | DSHLoop n body =>
          loopcontblock <- incBlockNamed "Loop_lcont" ;;

          loopvar <- newLocalVar IntType "Loop_i" ;;
          '(child_block_id, child_blocks) <- genIR body loopcontblock ;;
          dropVars 1 ;;
          add_comment
            (genWhileLoop "Loop_loop" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                          loopvar loopcontblock child_block_id child_blocks[] nextblock)
        | DSHAlloc size body =>
          aname <- newLocalVar (TYPE_Pointer (getIRType (DSHPtr size))) "a" ;;
          '(bblock, bcode) <- genIR body nextblock ;;
          '(ablock,acode) <- allocTempArrayBlock aname bblock size ;;
          dropVars 1 ;;
          add_comment (ret (ablock, [acode]++bcode))
        | DSHMemInit size y_p value =>
          '(y,_) <- resolve_PVar y_p ;; (* ignore actual block size *)
          '(ablock,acode) <- genMemInit size y value nextblock ;;
          add_comment (ret (ablock, acode))
        | DSHSeq f g =>
          '(gb, g') <- genIR g nextblock ;;
          '(fb, f') <- genIR f gb ;;
          add_comment (ret (fb, f'++g'))
        end)
          (fun m => raise (m @@ " in " @@ fshcol_s)).

Definition body_non_empty_cast (body : list (block typ)) : cerr (block typ * list (block typ)) :=
  match body with
  | [] => raise "Attempting to generate a function containing no block"
  | b::body => ret (b,body)
  end.

Definition LLVMGen
           (i o: Int64.int)
           (fshcol: DSHOperator)
           (funname: string)
  : cerr (toplevel_entities typ (block typ * list (block typ)))
  :=
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

    bodyt <- body_non_empty_cast (body ++ [retblock]) ;;
    let all_intrinsics:toplevel_entities typ (block typ * list (block typ))
        := [TLE_Comment "Prototypes for intrinsics we use"]
             ++ (List.map (TLE_Declaration) defined_intrinsics_decls)
    in

    let x := Name "X" in
    let xtyp := TYPE_Pointer (getIRType (DSHPtr i)) in
    let y := Name "Y" in
    let ytyp := TYPE_Pointer (getIRType (DSHPtr o)) in

    ret
      (all_intrinsics ++
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
                          df_args        := [x; y];
                          df_instrs      := bodyt
                        |}
      ]).

Definition initOneIRGlobal
           (data: list binary64)
           (nmt:string * DSHType)
  : cerr (list binary64 * (toplevel_entity typ (block typ * list (block typ))))
  :=
    let (nm,t) := nmt in
    match t with
    | DSHnat =>
      let '(x, data) := rotate Float64Zero data in
      let xi := bits_of_b64 x in (* a potential size overflow here ? *)
      let v_id := Name nm in
      let v_typ := getIRType t in
      let g := TLE_Global {|
                   g_ident        := v_id;
                   g_typ          := v_typ ;
                   g_constant     := true ;
                   g_exp          := Some (EXP_Integer xi);
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
      addVars [(ID_Global v_id, TYPE_Pointer v_typ)] ;;
      ret (data, g)

    | DSHCType =>
      let '(x, data) := rotate Float64Zero data in
      let v_id := Name nm in
      let v_typ := getIRType t in
      let g := TLE_Global {|
                   g_ident        := v_id;
                   g_typ          := v_typ ;
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
      addVars [(ID_Global v_id, TYPE_Pointer v_typ)] ;;
      ret (data, g)
    | DSHPtr n =>
      let (data, arr) := constArray (MInt64asNT.to_nat n) data in
      let v_id := Name nm in
      let v_typ := getIRType t in
      let g := TLE_Global {|
                   g_ident        := v_id;
                   g_typ          := v_typ;
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
      addVars [(ID_Global v_id, TYPE_Pointer v_typ)] ;;
      ret (data, g)
    end.

Definition globals_name_present
           (name:string)
           (l:list (string * DSHType)) : bool
  :=
    List.fold_right (fun v f => orb f (string_beq (fst v) name)) false l.


Fact nth_to_globals_name_present (globals:list (string * DSHType)) nm :
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


Definition global_uniq_chk: string * DSHType -> list (string * DSHType) -> cerr unit
  := fun x xs =>
       let nm := (fst x) in
       err2errS (assert_false_to_err
         ("duplicate global name: " @@ nm)
         (globals_name_present nm xs)
         tt).


(*
  Generate IR external definitoins for all globals.
  They are externally linked and not initialized here.
  (c.f [initIRglobals]

  TODO: this is ugly. 2 maps should be replaced with single monadic fold.
 *)
Definition genIRGlobals
           {FnBody: Set}
           (x: list (string*DSHType))
  : cerr (list (toplevel_entity _ FnBody))
  := let l := List.map
                (fun g:(string * DSHType) =>
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
     | nil => ret []
     | _::_ =>
       (* Add globals *)
       addVars
         (List.map
            (fun g:(string* DSHType) =>
               let (n,t) := g in (ID_Global (Name n), TYPE_Pointer (getIRType t)))
            x) ;;
       ret ([TLE_Comment "Global variables"] ++ l)
     end.


(*
  Generate delclarations for all globals. They are all internally linked
  and initialized in-place.

  (c.f. genIRglobals)

  NOTE: Could not use [monadic_fold_left] here because of error check.
*)
Definition initIRGlobals
         (data: list binary64)
         (x: list (string * DSHType))
  : cerr (list binary64 * list (toplevel_entity typ (block typ * list (block typ))))
  := init_with_data initOneIRGlobal global_uniq_chk (data) x.

(*
   When code genration generates [main], the input
   will be stored in pre-initialized [X] global placeholder variable.
 *)
Definition initXYplaceholders (i o:Int64.int) (data:list binary64) x xtyp y ytyp:
  cerr (list binary64 * (LLVMAst.toplevel_entities _ (LLVMAst.block typ * list (LLVMAst.block typ))))
  :=
    let '(data,ydata) := constArray (MInt64asNT.to_nat o) data in
    let '(data,xdata) := constArray (MInt64asNT.to_nat i) data in
    addVars [(ID_Global y, ytyp); (ID_Global x, xtyp)] ;;
    ret (data,[ TLE_Global
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
    ]).

(* Generates "main" function which will call "op_name", passing
   global "x" and "y" as arguments. Returns "y". Pseudo-code:

   global float[i] x;
   global float[y] y;

   float[o] main() {
        tmp = op_name(x,y);
        return y;
   }
*)
Definition genMain
           (op_name: string)
           (* Global X placeholder: *)
           (x:raw_id) (xptyp:typ)
           (* Global Y placeholder: *)
           (y:raw_id) (ytyp:typ)
           (yptyp:typ)
  : LLVMAst.toplevel_entities _ (LLVMAst.block typ * list (LLVMAst.block typ))
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
            df_instrs      := (
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
                               |}, [])
          |}].


(* Drop 2 vars before the last 2 in Γ *)
Definition dropFakeVars: cerr unit :=
  st <- get ;;
  let l := List.length (Γ st) in
  if Nat.ltb l 4 then raise "Γ too short"
  else
    '(globals, Γ') <- option2errS "Γ too short"
                                 (ListUtil.split (Γ st) (l-4)) ;;
    '(_, Γ'') <- option2errS "Γ too short"
                            (ListUtil.split Γ' 2) ;;
    put {|
        block_count := block_count st ;
        local_count := local_count st ;
        void_count  := void_count st ;
        Γ := (globals ++ Γ'')
      |}.

Definition compile (p: FSHCOLProgram) (just_compile:bool) (data:list binary64): cerr (toplevel_entities typ (block typ * list (block typ))) :=
  match p with
  | mkFSHCOLProgram i o name globals op =>
    if just_compile then
      ginit <- genIRGlobals (FnBody:= block typ * list (block typ)) globals ;;
      prog <- LLVMGen i o op name ;;
      ret (ginit ++ prog)
    else
      (* Global placeholders for X,Y *)
      let gx := Anon 0%Z in
      let gxtyp := getIRType (DSHPtr i) in
      let gxptyp := TYPE_Pointer gxtyp in

      let gy := Anon 1%Z in
      let gytyp := getIRType (DSHPtr o) in
      let gyptyp := TYPE_Pointer gytyp in

      '(data,yxinit) <- initXYplaceholders i o data gx gxtyp gy gytyp ;;
      (* Γ := [fake_y; fake_x] *)

      (* While generate operator's function body, add parameters as
         locals X=PVar 1, Y=PVar 0.

        We want them to be in `Γ` before globals *)
      let x := Name "X" in
      let xtyp := TYPE_Pointer (getIRType (DSHPtr i)) in
      let y := Name "Y" in
      let ytyp := TYPE_Pointer (getIRType (DSHPtr o)) in


      addVars [(ID_Local y, ytyp);(ID_Local x, xtyp)] ;;
      (* Γ := [y; x; fake_y; fake_x] *)

      (* Global variables *)
      '(data,ginit) <- initIRGlobals data globals ;;
      (* Γ := [globals; y; x; fake_y; fake_x] *)

      (* operator function *)
      prog <- LLVMGen i o op name ;;

      (* After generation of operator function, we no longer need
         [x] and [y] in [Γ]. *)

      dropFakeVars ;;

      (* Main function *)
      let main := genMain name gx gxptyp gy gytyp gyptyp in
      ret (yxinit ++ ginit ++ prog ++ main)
  end.

Definition compile_w_main (p: FSHCOLProgram): list binary64 -> cerr (toplevel_entities typ (block typ * list (block typ))) :=
  compile p false.
