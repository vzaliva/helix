(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Coq.Strings.String.

Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.DSigmaHCOL.NType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Tactics.StructTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

(* Translation between two families of DHCOL languages L and L'
   substituting types:
   CT -> CT'
   NT -> NT'
 *)
Module MDHCOLTypeTranslator
       (Import CT: CType)
       (Import CT': CType)
       (Import NT: NType)
       (Import NT': NType)
       (Import L: MDSigmaHCOL(CT)(NT))
       (Import L': MDSigmaHCOL(CT')(NT'))
       (Import LE: MDSigmaHCOLEval(CT)(NT)(L))
       (Import LE': MDSigmaHCOLEval(CT')(NT')(L')).

  Definition translateNTypeConst (a:NT.t): err NT'.t
    := NT'.from_nat (NT.to_nat a).

  Definition translatePExpr (p:L.PExpr): L'.PExpr :=
    match p with
    | L.PVar x => L'.PVar x
    end.

  Fixpoint translateNExpr (n:L.NExpr) : err L'.NExpr :=
    match n with
    | L.NVar x => inr (NVar x)
    | L.NConst x =>
      x' <- translateNTypeConst x ;; ret (NConst x')
    | L.NDiv x x0 => liftM2 NDiv (translateNExpr x) (translateNExpr x0)
    | L.NMod x x0 => liftM2 NMod (translateNExpr x) (translateNExpr x0)
    | L.NPlus x x0 => liftM2 NPlus (translateNExpr x) (translateNExpr x0)
    | L.NMinus x x0 => liftM2 NMinus (translateNExpr x) (translateNExpr x0)
    | L.NMult x x0 => liftM2 NMult (translateNExpr x) (translateNExpr x0)
    | L.NMin x x0 => liftM2 NMin (translateNExpr x) (translateNExpr x0)
    | L.NMax x x0 => liftM2 NMax (translateNExpr x) (translateNExpr x0)
    end.

  Definition translateMemRef: L.MemRef -> err L'.MemRef
    := fun '(p,n) =>
         n' <- translateNExpr n ;;
         ret (translatePExpr p, n').

  (* This one is tricky. There are only 2 known constants we know how to translate:
   '1' and '0'. Everything else will trigger an error *)
  Definition translateCTypeConst (a:CT.t): err CT'.t :=
    if CT.CTypeEquivDec a CT.CTypeZero then inr CT'.CTypeZero
    else if CT.CTypeEquivDec a CT.CTypeOne then inr CT'.CTypeOne
         else (inl "unknown CType constant").

  Set Universe Polymorphism.

  (* This should be defined as:

   Definition NM_err_sequence
           {A: Type}
           (mv: NM.t (err A)): err (NM.t A)
           := @NM_sequence A err Monad_err mv.

   But it gives us a problem:

   The term "Monad_err" has type "Monad err" while it is expected to have type
   "Monad (fun B : Type => err B)".

   *)
  Definition NM_err_sequence
             {A: Type}
             (mv: NM.t (err A)): err (NM.t A)
    := NM.fold
         (fun k v acc =>
            match v with
            | inr v' =>
              match acc with
              | inr acc' => inr (NM.add k v' acc')
              | inl msg => inl msg
              end
            | inl msg => inl msg
            end)
         mv
         (inr (@NM.empty A)).

  (* This should use [NM_sequence] directly making [NM_err_sequence] unecessary, but we run into universe inconsistency *)
  Definition translate_mem_block (m:L.mem_block) : err L'.mem_block
    := NM_err_sequence (NM.map translateCTypeConst m).

  Definition translateMExpr (m:L.MExpr) : err L'.MExpr :=
    match m with
    | L.MPtrDeref x => ret (MPtrDeref (translatePExpr x))
    | L.MConst x size =>
      x' <- translate_mem_block x ;;
      size' <- translateNTypeConst size ;;
      ret (MConst x' size')
    end.

  Fixpoint translateAExpr (a:L.AExpr): err L'.AExpr :=
    match a with
    | L.AVar x => ret (AVar x)
    | L.AConst x => x' <- translateCTypeConst x ;; ret (AConst x')
    | L.ANth m n =>
      m' <- translateMExpr m ;;
      n' <- translateNExpr n ;;
      ret (ANth m' n')
    | L.AAbs x =>
      x' <- translateAExpr x ;;
      ret (AAbs x')
    | L.APlus x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (APlus x' x0')
    | L.AMinus x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMinus x' x0')
    | L.AMult x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMult x' x0')
    | L.AMin x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMin x' x0')
    | L.AMax x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMax x' x0')
    | L.AZless x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AZless x' x0')
    end.

  Fixpoint translate (d: L.DSHOperator): err L'.DSHOperator
    :=
      match d with
      | L.DSHNop =>
        ret DSHNop
      | L.DSHAssign src dst =>
        src' <- translateMemRef src ;;
        dst' <- translateMemRef dst ;;
        ret (DSHAssign src' dst')
      | L.DSHIMap n x_p y_p f =>
        f' <- translateAExpr f ;;
        ret (DSHIMap
               n
               (translatePExpr x_p)
               (translatePExpr y_p)
               f')
      | L.DSHBinOp n x_p y_p f =>
        f' <- translateAExpr f ;;
        ret (DSHBinOp
               n
               (translatePExpr x_p)
               (translatePExpr y_p)
               f')
      | L.DSHMemMap2 n x0_p x1_p y_p f =>
        f' <- translateAExpr f ;;
        ret (DSHMemMap2
               n
               (translatePExpr x0_p)
               (translatePExpr x1_p)
               (translatePExpr y_p)
               f')
      | L.DSHPower n src dst f initial =>
        f' <- translateAExpr f ;;
        initial' <- translateCTypeConst initial ;;
        n' <- translateNExpr n ;;
        src' <- translateMemRef src ;;
        dst' <- translateMemRef dst ;;
        ret (DSHPower
               n'
               src' dst'
               f'
               initial')
      | L.DSHLoop n body =>
        body' <- translate body ;;
        ret (DSHLoop
               n
               body')
      | L.DSHAlloc size body =>
        body' <- translate body ;;
        size' <- translateNTypeConst size ;;
        ret (DSHAlloc
               size'
               body')
      | L.DSHMemInit y_p value =>
        value' <- translateCTypeConst value ;;
        ret (DSHMemInit
               (translatePExpr y_p)
               value')
      | L.DSHSeq f g =>
        f' <- translate f ;;
        g' <- translate g ;;
        ret (DSHSeq f' g')
      end.

  Class CTranslationOp :=
    {
    (* Heterogeneous equality *)
    heq_CType: CT.t -> CT'.t -> Prop ;

    (* Partial mapping of [CT.t] values to [CT'.t] *)
    translateCTypeValue: CT.t -> err CT'.t ;
    }.

    Class NTranslationOp :=
    {

    (* Heterogeneous equality *)
    heq_NType: NT.t -> NT'.t -> Prop ;

    (* Partial mapping of [NT.t] values to [NT'.t] *)
    translateNTypeValue: NT.t -> err NT'.t ;
    }.

  Class NBinOpTranslation
        `{NTranslationOp}
        (f: NT.t -> NT.t -> NT.t)
        (f': NT'.t -> NT'.t -> NT'.t)
    :=
      {
    nbinop_translate_compat: forall x x' y y',
          translateNTypeValue x = inr x' ->
          translateNTypeValue y = inr y' ->
          translateNTypeValue (f x y) = inr (f' x' y')
      }.

  Class NTranslationProps `{NTT: NTranslationOp} :=
    {
    (* Value mapping should result in "equal" values *)
    heq_NType_translateNTypeValue_compat:
      forall x x', translateNTypeValue x = inr x' -> heq_NType x x';

    (* Ensure [translateNTypeConst] is compatible with [translateNTypeValue] *)
    translateNTypeConst_translateNTypeValue_compat:
      forall x x', translateNTypeConst x = inr x' ->
              translateNTypeValue x = inr x';

    (* So surjectivity property. This allows use for example map
       natural numbers to signed integers *)

    heq_NType_to_from_nat:
      forall x x', heq_NType x x' -> NT.to_nat x = NT'.to_nat x';

    NTypeDiv_translation   : NBinOpTranslation NT.NTypeDiv   NT'.NTypeDiv  ;
    NTypeMod_translation   : NBinOpTranslation NT.NTypeMod   NT'.NTypeMod  ;
    NTypePlus_translation  : NBinOpTranslation NT.NTypePlus  NT'.NTypePlus ;
    NTypeMinus_translation : NBinOpTranslation NT.NTypeMinus NT'.NTypeMinus;
    NTypeMult_translation  : NBinOpTranslation NT.NTypeMult  NT'.NTypeMult ;
    NTypeMin_translation   : NBinOpTranslation NT.NTypeMin   NT'.NTypeMin  ;
    NTypeMax_translation   : NBinOpTranslation NT.NTypeMax   NT'.NTypeMax  ;
    }.

  Class CBinOpTranslation
        `{CTranslationOp}
        (f: CT.t -> CT.t -> CT.t)
        (f': CT'.t -> CT'.t -> CT'.t)
    :=
      {
    binop_translate_compat: forall x x' y y',
          translateCTypeValue x = inr x' ->
          translateCTypeValue y = inr y' ->
          translateCTypeValue (f x y) = inr (f' x' y')
      }.

  Class CUnOpTranslation
        `{CTranslationOp}
        (f: CT.t -> CT.t)
        (f': CT'.t -> CT'.t)
    :=
      {
    unop_translate_compat: forall x x',
          translateCTypeValue x = inr x' ->
          translateCTypeValue (f x) = inr (f' x')
      }.

  Class CTranslationProps `{C: CTranslationOp} :=
    {
    (* Value mapping should result in "equal" values *)
    heq_CType_translateCTypeValue_compat:
      forall x x', translateCTypeValue x = inr x' -> heq_CType x x';

    (* Ensure [translateCTypeConst] is compatible with [translateCTypeValue] *)
    translateCTypeConst_translateCTypeValue_compat:
      forall x x', translateCTypeConst x = inr x' ->
              translateCTypeValue x = inr x';

    (* Surjectivity: all values in CT't should have correspoding CT.t values
       Not sure if we need this
       translate_surj: forall (x':CT'.t), exists x, translateCTypeValue x = inr x';
     *)

    CTypePlus_translation  : CBinOpTranslation CT.CTypePlus  CT'.CTypePlus ;
    CTypeMult_translation  : CBinOpTranslation CT.CTypeMult  CT'.CTypeMult ;
    CTypeZLess_translation : CBinOpTranslation CT.CTypeZLess CT'.CTypeZLess;
    CTypeMin_translation   : CBinOpTranslation CT.CTypeMin   CT'.CTypeMin  ;
    CTypeMax_translation   : CBinOpTranslation CT.CTypeMax   CT'.CTypeMax  ;
    CTypeSub_translation   : CBinOpTranslation CT.CTypeSub   CT'.CTypeSub  ;

    CTypeNeg_translation: CUnOpTranslation CT.CTypeNeg CT'.CTypeNeg ;
    CTypeAbs_translation: CUnOpTranslation CT.CTypeAbs CT'.CTypeAbs ;
    }.


  Section Relations.

    Context `{CTT: CTranslationOp}
            `{CTP: @CTranslationProps CTT}
            `{NTT: NTranslationOp}
            `{NTP: @NTranslationProps NTT}.

    (* Well-defined [heq_CType] preserves constnats *)
    Fact heq_CType_zero_one_wd:
      heq_CType CT.CTypeZero CT'.CTypeZero /\
      heq_CType CT.CTypeOne CT'.CTypeOne.
    Proof.
      split;
        apply heq_CType_translateCTypeValue_compat, translateCTypeConst_translateCTypeValue_compat; cbv.
      -
        break_if.
        + reflexivity.
        + break_if; clear -n; contradict n; reflexivity.
      -
        break_if.
        +
          clear -e.
          symmetry in e.
          contradict e.
          apply CT.CTypeZeroOneApart.
        +
          break_if.
          * reflexivity.
          * clear -n0; contradict n0; reflexivity.
    Qed.

    Definition heq_mem_block: L.mem_block -> L'.mem_block -> Prop :=
      fun m m' => forall k : NM.key, hopt_r heq_CType (NM.find k m) (NM.find k m').

    Inductive heq_NExpr: L.NExpr -> L'.NExpr -> Prop :=
    | heq_NVar: forall x x', x=x' -> heq_NExpr (L.NVar x) (L'.NVar x')
    | heq_NConst: forall x x', heq_NType x x' -> heq_NExpr (L.NConst x) (L'.NConst x')
    | heq_NDiv : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NDiv x y) (L'.NDiv x' y')
    | heq_NMod : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NMod x y) (L'.NMod x' y')
    | heq_NPlus : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NPlus x y) (L'.NPlus x' y')
    | heq_NMinus : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NMinus x y) (L'.NMinus x' y')
    | heq_NMult : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NMult x y) (L'.NMult x' y')
    | heq_NMin : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NMin x y) (L'.NMin x' y')
    | heq_NMax : forall x y x' y', heq_NExpr x x' -> heq_NExpr y y' -> heq_NExpr (L.NMax x y) (L'.NMax x' y').

    Inductive heq_PExpr: L.PExpr -> L'.PExpr -> Prop :=
    | heq_PVar: forall x x', x=x' -> heq_PExpr (L.PVar x) (L'.PVar x').

    Inductive heq_MExpr: L.MExpr -> L'.MExpr -> Prop :=
    | heq_MPtrDeref: forall x x', heq_PExpr x x' -> heq_MExpr (L.MPtrDeref x) (L'.MPtrDeref x')
    | heq_MConst: forall m m' n n', heq_NType n n' -> heq_mem_block m m' -> heq_MExpr (L.MConst m n) (L'.MConst m' n').

    Inductive heq_AExpr: L.AExpr -> L'.AExpr -> Prop :=
    | heq_AVar: forall x x', x=x' -> heq_AExpr (L.AVar x) (L'.AVar x')
    | heq_ANth: forall m m' n n', heq_MExpr m m' ->  heq_NExpr n n' -> heq_AExpr (L.ANth m n) (L'.ANth m' n')
    | heq_AAbs: forall x x', heq_AExpr x x' ->  heq_AExpr (L.AAbs x) (L'.AAbs x')
    | heq_AConst: forall x x', heq_CType x x' -> heq_AExpr (L.AConst x) (L'.AConst x')
    | heq_APlus : forall x y x' y', heq_AExpr x x' -> heq_AExpr y y' -> heq_AExpr (L.APlus x y) (L'.APlus x' y')
    | heq_AMinus : forall x y x' y', heq_AExpr x x' -> heq_AExpr y y' -> heq_AExpr (L.AMinus x y) (L'.AMinus x' y')
    | heq_AMult : forall x y x' y', heq_AExpr x x' -> heq_AExpr y y' -> heq_AExpr (L.AMult x y) (L'.AMult x' y')
    | heq_AMin : forall x y x' y', heq_AExpr x x' -> heq_AExpr y y' -> heq_AExpr (L.AMin x y) (L'.AMin x' y')
    | heq_AMax : forall x y x' y', heq_AExpr x x' -> heq_AExpr y y' -> heq_AExpr (L.AMax x y) (L'.AMax x' y')
    | heq_AZless: forall x y x' y', heq_AExpr x x' -> heq_AExpr y y' -> heq_AExpr (L.AZless x y) (L'.AZless x' y').

    Inductive heq_DSHOperator: L.DSHOperator -> L'.DSHOperator -> Prop :=
    | heq_DSHNop: heq_DSHOperator L.DSHNop L'.DSHNop
    | heq_DSHAssign:
        forall src_p src_n dst_p dst_n src_p' src_n' dst_p' dst_n',
          heq_NExpr src_n src_n' ->
          heq_NExpr dst_n dst_n' ->
          heq_PExpr src_p src_p' ->
          heq_PExpr dst_p dst_p' ->
          heq_DSHOperator (L.DSHAssign (src_p,src_n) (dst_p, dst_n))
                          (L'.DSHAssign (src_p',src_n') (dst_p', dst_n'))
    | heq_DSHIMap:
        forall n x_p y_p f n' x_p' y_p' f',
          n=n' ->
          heq_PExpr x_p x_p' ->
          heq_PExpr y_p y_p' ->
          heq_AExpr f f' ->
          heq_DSHOperator (L.DSHIMap n x_p y_p f) (L'.DSHIMap n' x_p' y_p' f')

    | heq_DSHBinOp:
        forall n x_p y_p f n' x_p' y_p' f',
          n=n' ->
          heq_PExpr x_p x_p' ->
          heq_PExpr y_p y_p' ->
          heq_AExpr f f' ->
          heq_DSHOperator (L.DSHBinOp n x_p y_p f) (L'.DSHBinOp n' x_p' y_p' f')
    | heq_DSHMemMap2:
        forall n x0_p x1_p y_p f n' x0_p' x1_p' y_p' f',
          n=n' ->
          heq_PExpr x0_p x0_p' ->
          heq_PExpr x1_p x1_p' ->
          heq_PExpr y_p y_p' ->
          heq_AExpr f f' ->
          heq_DSHOperator (L.DSHMemMap2 n x0_p x1_p y_p f) (L'.DSHMemMap2 n' x0_p' x1_p' y_p' f')
    | heq_DSHPower:
        forall n src_p src_n dst_p dst_n f ini n' src_p' src_n' dst_p' dst_n' f' ini',
          heq_NExpr n n' ->
          heq_NExpr src_n src_n' ->
          heq_NExpr dst_n dst_n' ->
          heq_PExpr src_p src_p' ->
          heq_PExpr dst_p dst_p' ->
          heq_AExpr f f' ->
          heq_CType ini ini' ->
          heq_DSHOperator
            (L.DSHPower n (src_p,src_n) (dst_p, dst_n) f ini)
            (L'.DSHPower n' (src_p',src_n') (dst_p', dst_n') f' ini')
    | heq_DSHLoop:
        forall n n' body body',
          n=n' ->
          heq_DSHOperator body body' ->
          heq_DSHOperator (L.DSHLoop n body) (L'.DSHLoop n' body')
    | heq_DSHAlloc:
        forall n n' body body',
          heq_NType n n' ->
          heq_DSHOperator body body' ->
          heq_DSHOperator (L.DSHAlloc n body) (L'.DSHAlloc n' body')
    | heq_DSHMemInit:
        forall p p' v v',
          heq_PExpr p p' ->
          heq_CType v v' ->
          heq_DSHOperator (L.DSHMemInit p v) (L'.DSHMemInit p' v')
    | heq_DSHSeq:
        forall f f' g g',
          heq_DSHOperator f f' ->
          heq_DSHOperator g g' ->
          heq_DSHOperator (L.DSHSeq f g) (L'.DSHSeq f' g').

    Lemma translation_syntax_correctenss:
      forall x x', translate x = inr x' ->
              heq_DSHOperator x x'.
    Proof.
    Admitted.

    Inductive heq_DSHVal: LE.DSHVal -> LE'.DSHVal -> Prop :=
    | heq_DSHnatVal: forall x x', heq_NType x x' -> heq_DSHVal (LE.DSHnatVal x) (LE'.DSHnatVal x')
    | heq_DSHCTypeVal: forall x x', heq_CType x x' -> heq_DSHVal (LE.DSHCTypeVal x) (LE'.DSHCTypeVal x')
    | heq_DSHPtrVal: forall a a' s s', a=a' -> heq_NType s s' -> heq_DSHVal (LE.DSHPtrVal a s) (LE'.DSHPtrVal a s').

    Definition heq_evalContext: LE.evalContext -> LE'.evalContext -> Prop :=
      List.Forall2 (fun '(x,p) '(x',p') => p=p' /\ heq_DSHVal x x').

    Definition heq_memory: L.memory -> L'.memory -> Prop.
      Admitted.

    Lemma translation_semantics_correctness
          (σ: LE.evalContext) (σ': LE'.evalContext)
          (Eσ: heq_evalContext σ σ')

          (op: L.DSHOperator) (op': L'.DSHOperator)
          (Eop: heq_DSHOperator op op')

          (imem omem: L.memory) (imem' omem': L'.memory)
          (Emem: heq_memory imem imem')
          (fuel: nat):

      LE.evalDSHOperator σ op imem fuel = Some (inr omem) ->
      LE'.evalDSHOperator σ' op' imem' fuel = Some (inr omem') ->
      heq_memory imem imem'.
    Proof.
    Admitted.

  End Relations.


End MDHCOLTypeTranslator.
