(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Psatz.

Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.DSigmaHCOL.NType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Util.Misc.
Require Import Helix.Tactics.HelixTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import MathClasses.interfaces.canonical_names.

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
    | L.NDiv   x x0 => liftM2 NDiv   (translateNExpr x) (translateNExpr x0)
    | L.NMod   x x0 => liftM2 NMod   (translateNExpr x) (translateNExpr x0)
    | L.NPlus  x x0 => liftM2 NPlus  (translateNExpr x) (translateNExpr x0)
    | L.NMinus x x0 => liftM2 NMinus (translateNExpr x) (translateNExpr x0)
    | L.NMult  x x0 => liftM2 NMult  (translateNExpr x) (translateNExpr x0)
    | L.NMin   x x0 => liftM2 NMin   (translateNExpr x) (translateNExpr x0)
    | L.NMax   x x0 => liftM2 NMax   (translateNExpr x) (translateNExpr x0)
    end.

  Definition translateMemRef: L.MemRef -> err L'.MemRef
    := fun '(p,n) =>
         n' <- translateNExpr n ;;
         ret (translatePExpr p, n').

  (* There are only 2 known constants we know how to translate:
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

  Definition NM_err_seq_step
             {A : Type}
             (k : NM.key)
             (v : err A)
             (acc : err (NM.t A))
    :=
      match v with
      | inr v' =>
        match acc with
        | inr acc' => inr (NM.add k v' acc')
        | inl msg => inl msg
        end
      | inl msg => inl msg
      end.

  Definition NM_err_sequence
             {A: Type}
             (mv: NM.t (err A)): err (NM.t A)
    := NM.fold NM_err_seq_step
         mv
         (inr (@NM.empty A)).

  Class CTranslationOp :=
    {
    (* Heterogeneous equality *)
    heq_CType: CT.t -> CT'.t -> Prop ;

    (* Proper wrt [equiv] *)
    heq_CType_proper: Proper ((=) ==> (=) ==> iff) heq_CType;
    (* Partial mapping of [CT.t] values to [CT'.t] *)
    translateCTypeValue: CT.t -> err CT'.t ;
    }.

  Class NTranslationOp :=
    {

    (* Heterogeneous equality *)
    heq_NType: NT.t -> NT'.t -> Prop ;

    (* Proper wrt [equiv] *)
    heq_NType_proper: Proper ((=) ==> (=) ==> iff) heq_NType ;

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

    heq_NType_to_nat:
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

  Section EvalTranslations.

    Context `{CTT: CTranslationOp} (* `{CTP: @CTranslationProps CTT} *)
            `{NTT: NTranslationOp}. (* `{NTP: @NTranslationProps NTT}. *)

    Import ListNotations.

    Definition translateDSHVal (d:LE.DSHVal): err LE'.DSHVal
      := match d with
         | LE.DSHnatVal n => n' <- translateNTypeValue n ;; ret (LE'.DSHnatVal n')
         | LE.DSHCTypeVal a => a' <- translateCTypeValue a ;; ret (LE'.DSHCTypeVal a')
         | LE.DSHPtrVal a size => size' <- translateNTypeValue size ;; ret (LE'.DSHPtrVal a size')
         end.

    Fixpoint translateEvalContext (σ: LE.evalContext): err LE'.evalContext
      := match σ with
         | [] => inr []
         | ((x,f)::xs) => d <- translateDSHVal x ;;
                        t <- translateEvalContext xs ;;
                        ret ((d,f) :: t)
         end.

    (* These should use [NM_sequence] directly,
       making [NM_err_sequence] unecessary,
       but we run into universe inconsistency *)

    (* Note: the following use [translateCTypeConst], meaning
       any value other than 0 or 1 produces an error. This is used for
       translation of constants embedded into the operator itself. *)
    Definition translate_mem_block (m:L.mem_block) : err L'.mem_block
      := NM_err_sequence (NM.map translateCTypeConst m).

    Definition translate_memory (m:L.memory): err L'.memory :=
      NM_err_sequence (NM.map translate_mem_block m).

    (* Note: the following is based on [translateCTypeValue], only to be used
       when translating *input values* - not constants. *)
    Definition translate_runtime_mem_block (m:L.mem_block) : err L'.mem_block
      := NM_err_sequence (NM.map translateCTypeValue m).

    Definition translate_runtime_memory (m:L.memory): err L'.memory :=
      NM_err_sequence (NM.map translate_runtime_mem_block m).

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
          _ <- NT.from_nat n ;;  (* ensure loop bounds fit source [NType] *)
          _ <- NT'.from_nat n ;; (* ensure loop bounds fit target [NType] *)
          f' <- translateAExpr f ;;
          ret (DSHIMap
                 n
                 (translatePExpr x_p)
                 (translatePExpr y_p)
                 f')
        | L.DSHBinOp n x_p y_p f =>
          _ <- NT.from_nat n ;;
          _ <- NT'.from_nat n ;;
          f' <- translateAExpr f ;;
          ret (DSHBinOp
                 n
                 (translatePExpr x_p)
                 (translatePExpr y_p)
                 f')
        | L.DSHMemMap2 n x0_p x1_p y_p f =>
          _ <- NT.from_nat n ;;
          _ <- NT'.from_nat n ;;
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
          _ <- NT.from_nat n ;;
          _ <- NT'.from_nat n ;;
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

  End EvalTranslations.

  Section Relations.

    Context `{CTT: CTranslationOp} `{NTT: NTranslationOp}.

    (* [heq_CType] generalized *)
    Variable heq_CConst : CT.t -> CT'.t -> Prop.

    Hypothesis heq_CConst_proper :
      Proper ((=) ==> (=) ==> (iff)) heq_CConst.

    Definition heq_mem_block: L.mem_block -> L'.mem_block -> Prop :=
      fun m m' => forall k : nat, hopt_r heq_CConst (LE.mem_lookup k m) (LE'.mem_lookup k m').

    (* Check if two [nat]s translate successfully and to equivalent [NType] values *)
    Inductive heq_NT_nat: nat -> nat -> Prop :=
    | heq_NT_from_nat : forall n n',
        herr heq_NType (NT.from_nat n) (NT'.from_nat n') ->
        heq_NT_nat n n'.

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
    | heq_AConst: forall x x', heq_CConst x x' -> heq_AExpr (L.AConst x) (L'.AConst x')
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
          heq_NT_nat n n' ->
          heq_PExpr x_p x_p' ->
          heq_PExpr y_p y_p' ->
          heq_AExpr f f' ->
          heq_DSHOperator (L.DSHIMap n x_p y_p f) (L'.DSHIMap n' x_p' y_p' f')

    | heq_DSHBinOp:
        forall n x_p y_p f n' x_p' y_p' f',
          heq_NT_nat n n' ->
          heq_PExpr x_p x_p' ->
          heq_PExpr y_p y_p' ->
          heq_AExpr f f' ->
          heq_DSHOperator (L.DSHBinOp n x_p y_p f) (L'.DSHBinOp n' x_p' y_p' f')
    | heq_DSHMemMap2:
        forall n x0_p x1_p y_p f n' x0_p' x1_p' y_p' f',
          heq_NT_nat n n' ->
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
          heq_CConst ini ini' ->
          heq_DSHOperator
            (L.DSHPower n (src_p,src_n) (dst_p, dst_n) f ini)
            (L'.DSHPower n' (src_p',src_n') (dst_p', dst_n') f' ini')
    | heq_DSHLoop:
        forall n n' body body',
          heq_NT_nat n n' ->
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
          heq_CConst v v' ->
          heq_DSHOperator (L.DSHMemInit p v) (L'.DSHMemInit p' v')
    | heq_DSHSeq:
        forall f f' g g',
          heq_DSHOperator f f' ->
          heq_DSHOperator g g' ->
          heq_DSHOperator (L.DSHSeq f g) (L'.DSHSeq f' g').

    Inductive heq_DSHVal: LE.DSHVal -> LE'.DSHVal -> Prop :=
    | heq_DSHnatVal: forall x x', heq_NType x x' -> heq_DSHVal (LE.DSHnatVal x) (LE'.DSHnatVal x')
    | heq_DSHCTypeVal: forall x x', heq_CConst x x' -> heq_DSHVal (LE.DSHCTypeVal x) (LE'.DSHCTypeVal x')
    | heq_DSHPtrVal: forall a a' s s', a=a' -> heq_NType s s' -> heq_DSHVal (LE.DSHPtrVal a s) (LE'.DSHPtrVal a' s').

    Definition heq_evalContextElem : (LE.DSHVal * bool) -> (LE'.DSHVal * bool) -> Prop :=
      fun '(x,p) '(x',p') => p=p' /\ heq_DSHVal x x'.

    Definition heq_evalContext : LE.evalContext -> LE'.evalContext -> Prop :=
      List.Forall2 heq_evalContextElem.

    Definition heq_memory : L.memory -> L'.memory -> Prop :=
      fun m m' => forall k : nat, hopt_r heq_mem_block
                               (LE.memory_lookup m k)
                               (LE'.memory_lookup m' k).

    Definition heq_evalPExpr : nat * NT.t -> nat * NT'.t -> Prop :=
      fun '(v, size) '(v', size') => v = v' /\ heq_NType size size'.

    Definition heq_evalMExpr
      : LE.mem_block * NT.t -> LE'.mem_block * NT'.t -> Prop :=
      fun '(mb, size) '(mb', size') => heq_mem_block mb mb' /\ heq_NType size size'.

    Inductive heq_DSHIndexRange : LE.DSHIndexRange -> LE'.DSHIndexRange -> Prop :=
    | heq_DSHIndex : forall t t', heq_NType t t' ->
                             heq_DSHIndexRange (LE.DSHIndex t) (LE'.DSHIndex t')
    | heq_DSHOtherVar : heq_DSHIndexRange LE.DSHOtherVar LE'.DSHOtherVar.

    Definition heq_evalNatContext: LE.evalNatContext -> LE'.evalNatContext -> Prop :=
      List.Forall2 heq_DSHIndexRange.

    (* Check if two NExprs always produce the same results,
       given compatible contexts *)
    Definition evalNExpr_closure_equiv
               '((σn, n) : LE.evalNatClosure)
               '((σn', n') : LE'.evalNatClosure)
      : Prop :=
      forall σ σ',
        LE.evalContext_in_range σ σn ->
        LE'.evalContext_in_range σ' σn' ->
        heq_evalContext σ σ' ->
        heq_NExpr n n' ->
        herr_c heq_NType
               (LE.evalNExpr σ n)
               (LE'.evalNExpr σ' n').

    Definition evalNExpr_closure_trace_equiv
               (ncs : list LE.evalNatClosure)
               (ncs' : list LE'.evalNatClosure)
      : Prop :=
      Forall2 evalNExpr_closure_equiv ncs ncs'.

    Instance heq_DSHVal_proper:
      Proper ((=) ==> (=) ==> iff) heq_DSHVal.
    Proof.
      intros a a' Ea b b' Eb; split; intros H.
      -
        destruct a,b,a',b'; invc H; inv Eb; inv Ea; constructor.
        + eapply heq_NType_proper; eauto; crush.
        + eapply heq_CConst_proper; eauto; crush.
        + crush.
        + eapply heq_NType_proper; eauto; crush.
      -
        destruct a,b,a',b'; invc H; inv Eb; inv Ea; constructor.
        + eapply heq_NType_proper; eauto; crush.
        + eapply heq_CConst_proper; eauto; crush.
        + crush.
        + eapply heq_NType_proper; eauto; crush.
    Qed.

    Instance heq_mem_block_proper:
      Proper ((=) ==> (=) ==> iff) heq_mem_block.
    Proof.
      intros a a' Ea b b' Eb; split; intros H.
      -
        intros k.
        specialize (H k).
        invc H.
        +
          eq_to_equiv_hyp.
          rewrite Ea in H1.
          rewrite Eb in H2.
          symmetry in H1, H2.
          apply None_equiv_eq in H1.
          apply None_equiv_eq in H2.
          rewrite H1, H2.
          constructor.
        +
          eq_to_equiv_hyp.
          rewrite Ea in H0.
          rewrite Eb in H1.
          destruct (L.mem_lookup k a') eqn:H0';
            destruct (L'.mem_lookup k b') eqn:H1'; try constructor;
              repeat some_inv; try some_none.
          eapply heq_CConst_proper;try symmetry; eauto.
      -
        intros k.
        specialize (H k).
        invc H.
        +
          eq_to_equiv_hyp.
          rewrite <- Ea in H1.
          rewrite <- Eb in H2.
          symmetry in H1, H2.
          apply None_equiv_eq in H1.
          apply None_equiv_eq in H2.
          rewrite H1, H2.
          constructor.
        +
          eq_to_equiv_hyp.
          rewrite <- Ea in H0.
          rewrite <- Eb in H1.
          destruct (L.mem_lookup k a) eqn:H0';
            destruct (L'.mem_lookup k b) eqn:H1'; try constructor;
              repeat some_inv; try some_none.
          eapply heq_CConst_proper;try symmetry; eauto.
    Qed.

    Instance heq_memory_proper:
      Proper ((=) ==> (=) ==> iff) heq_memory.
    Proof.
      intros a a' Ea b b' Eb; split; intros H.
      -
        intros k.
        specialize (H k).
        invc H.
        +
          eq_to_equiv_hyp.
          rewrite Ea in H1.
          rewrite Eb in H2.
          symmetry in H1, H2.
          apply None_equiv_eq in H1.
          apply None_equiv_eq in H2.
          rewrite H1, H2.
          constructor.
        +
          eq_to_equiv_hyp.
          rewrite Ea in H0.
          rewrite Eb in H1.
          destruct (L.memory_lookup a' k) eqn:H0';
            destruct (L'.memory_lookup b' k) eqn:H1'; try constructor;
              repeat some_inv; try some_none.
          rewrite <-H0,<-H1.
          apply H2.
      -
        intros k.
        specialize (H k).
        invc H.
        +
          eq_to_equiv_hyp.
          rewrite <- Ea in H1.
          rewrite <- Eb in H2.
          symmetry in H1, H2.
          apply None_equiv_eq in H1.
          apply None_equiv_eq in H2.
          rewrite H1, H2.
          constructor.
        +
          eq_to_equiv_hyp.
          rewrite <- Ea in H0.
          rewrite <- Eb in H1.
          destruct (L.memory_lookup a k) eqn:H0';
            destruct (L'.memory_lookup b k) eqn:H1'; try constructor;
              repeat some_inv; try some_none.
          rewrite <-H0,<-H1.
          apply H2.
    Qed.

  End Relations.

  (** * TODO: refine *)
  Section Necessary_NT_Props.

    Context `{NTT: NTranslationOp}.

    (* NOTE: this has nothing to do with translation
       and would be moved into the [NType] module if accepted *)
    Lemma to_nat_of_from_nat (n : nat) (nt : NT.t) :
      NT.from_nat n = inr nt ->
      NT.to_nat nt = n.
    Admitted.

    (* NOTE: this has nothing to do with translation
       and would be moved into the [NType] module if accepted *)
    (* hence two "duplicate" lemmas for two modules *)
    Lemma to_nat_of_from_nat' (n : nat) (nt : NT'.t) :
      NT'.from_nat n = inr nt ->
      NT'.to_nat nt = n.
    Admitted.

    (* [heq_NType_to_nat] from Props *)
    Lemma heq_NType_to_nat'
          (n : NT.t)
          (n' : NT'.t)
      :
        heq_NType n n' ->
        NT.to_nat n = NT'.to_nat n'.
    Admitted.

    (* [heq_NType_translateNTypeValue_compat] from Props *)
    (* Required to prove the preservation of NType values in [σ] after
       translation *)
    Lemma heq_NType_translateNTypeValue_compat'
          (n : NT.t)
          (n' : NT'.t)
      :
        translateNTypeValue n = inr n' →
        heq_NType n n'.
    Admitted.

    (* NOTE: this is defined in terms of [from_nat ∘ to_nat],
       might follow from some of their properites. The current assumptions do
       not seem sufficient *)
    Lemma heq_NType_translateNTypeConst_compat
          (n : NT.t)
          (n' : t)
      :
        translateNTypeConst n = inr n' ->
        heq_NType n n'.
    Proof.
      intros TN.
      unfold translateNTypeConst in TN.
      apply to_nat_of_from_nat' in TN.
    Admitted.

    (* NOTE: [herr_f] vacuously holds if ANY argument is [inl].
       In ohter words, this is stating
       "If the same nat is *successfully* converted to NType before and after
       translation, both NType values are equivalent" *)
    Lemma heq_NType_from_nat (n : nat) :
      herr_f heq_NType (NT.from_nat n) (NT'.from_nat n).
    Proof.
      destruct (NT.from_nat n) as [msg|nt] eqn:FN;
        destruct (NT'.from_nat n) as [msg'|nt'] eqn:FN'.
      all: constructor.
    Admitted.

    Lemma heq_NT_nat_eq (n n' : nat) :
      heq_NT_nat n n' -> n = n'.
    Proof.
      intros EN.
      invc EN.
      invc H.
      rename a into nt, b into nt',
      H0 into NT, H1 into NT',
      H2 into ENT.
      symmetry in NT, NT'.
      apply err_equiv_eq in NT, NT'.

      apply to_nat_of_from_nat in NT.
      apply to_nat_of_from_nat' in NT'.
      rewrite <-NT, <-NT'.
      apply heq_NType_to_nat'.
      assumption.
    Qed.
    
    Lemma heq_NT_nat_S (n n' : nat) :
      heq_NT_nat (S n) (S n') ->
      heq_NT_nat n n'.
    Proof.
      intros SE.
      invc SE; constructor.
      invc H.
      rename H2 into SE,
      a into snt, b into snt',
      H0 into FSN, H1 into FSN'.

      symmetry in FSN, FSN'.

      replace n' with n in *.
      2: {
        apply heq_NType_to_nat' in SE.
        apply err_equiv_eq in FSN, FSN'.
        apply to_nat_of_from_nat in FSN.
        apply to_nat_of_from_nat' in FSN'.
        congruence.
      }

      copy_apply (NT.from_nat_lt (S n) snt n) FSN;
        [rename H into FN | constructor].
      copy_apply (NT'.from_nat_lt (S n) snt' n) FSN';
        [rename H into FN' | constructor].
      destruct FN as [nt FN], FN' as [nt' FN'].
      
      clear - FN FN'.
      pose proof heq_NType_from_nat n as E.
      inv E; try congruence.
      now constructor.
    Qed.

    Lemma heq_NType_heq_assert_NT_lt
          (msg msg' : string)
          (a : NT.t)
          (a' : t)
          (b : NT.t)
          (b' : t)
      :
        heq_NType a a' ->
        heq_NType b b' ->
        herr_c equiv
               (LE.assert_NT_lt msg a b)
               (LE'.assert_NT_lt msg' a' b').
    Proof.
      intros A B.
      unfold LE.assert_NT_lt, LE'.assert_NT_lt.
      apply heq_NType_to_nat' in A, B.
      cbv in A, B.
      rewrite !A, !B.
      destruct (Nat.ltb (to_nat a') (to_nat b')).
      now constructor.
      now constructor.
    Qed.

    Lemma heq_NType_heq_assert_NT_le
          (msg msg' : string)
          (a : NT.t)
          (a' : t)
          (b : NT.t)
          (b' : t)
      :
        heq_NType a a' ->
        heq_NType b b' ->
        herr_c equiv
               (LE.assert_NT_le msg a b)
               (LE'.assert_NT_le msg' a' b').
    Proof.
      intros A B.
      unfold LE.assert_NT_le, LE'.assert_NT_le.
      apply heq_NType_to_nat' in A, B.
      cbv in A, B.
      rewrite !A, !B.
      destruct (Nat.leb (to_nat a') (to_nat b')).
      now constructor.
      now constructor.
    Qed.

    Lemma heq_assert_nat_neq
          (msg msg' : string)
          (n1 n1' n2 n2' : nat)
      :
        n1 = n1' ->
        n2 = n2' ->
        herr_c equiv
               (LE.assert_nat_neq msg n1 n2)
               (LE'.assert_nat_neq msg' n1' n2').
    Proof.
      intros N1 N2.
      invc N1; invc N2.
      unfold LE.assert_nat_neq, LE'.assert_nat_neq, assert_false_to_err.
      break_if;
        repeat constructor.
    Qed.

  End Necessary_NT_Props.



  (* TODO: move *)
  (* NOTE: the other direction does not hold: [eq] vs [equiv] *)
  Lemma NP_Add_NM_add
        `{EQ : Equiv A}
        `{EQv : Equivalence A EQ}
        (k : NM.key)
        (v : A)
        (m1 m2 : NM.t A)
    :
      NP.Add k v m1 m2 -> NM.add k v m1 = m2.
  Proof.
    intros ADD k';
      specialize (ADD k').
    destruct (NM.E.eq_dec k k').
    1: rewrite NP.F.add_eq_o in * by assumption.
    2: rewrite NP.F.add_neq_o in * by assumption.
    all: now rewrite ADD.
  Qed.

  (* TODO: move *)
  Lemma NM_Empty_find
        `{EQ : Equiv A}
        (m : NM.t A)
    :
      NM.Empty m <-> forall k, NM.find k m ≡ None.
  Proof.
    split; intros E k.
    -
      specialize (E k).
      enough (T : forall v, NM.find k m ≢ Some v).
      {
        destruct (NM.find k m).
        now specialize (T a).
        constructor.
      }
      intros v C.
      apply NM.find_2 in C.
      now apply E in C.
    -
      intros v C.
      specialize (E k).
      apply NM.find_1 in C.
      now rewrite C in E.
  Qed.

  (* TODO: move *)
  Lemma NM_map_add
        `{EQa : Equiv A}
        `{EQb : Equiv B}
        `{EQva : Equivalence A EQa}
        `{EQvb : Equivalence B EQb}
        (f : A -> B)
        (PF : Proper ((=) ==> (=)) f)
        (k : NM.key)
        (v : A)
        (m m' : NM.t A)
        (mm mm' : NM.t B)
    :
      NM.map f m = mm ->
      ¬ NM.In (elt:=B) k mm ->
      NM.add k (f v) mm = mm' ->
      NM.add k v m = m' ->
      NM.map f m' = mm'.
  Proof.
    intros M NI AM AM' k'.
    specialize (M k');
      specialize (AM k');
      specialize (AM' k').
    rewrite NP.F.map_o in *.
    destruct (NM.E.eq_dec k k').
    1: rewrite NP.F.add_eq_o in * by assumption.
    2: rewrite NP.F.add_neq_o in * by assumption.
    -
      rewrite <-AM.
      unfold option_map.
      break_match; try some_none; some_inv.
      now rewrite AM'.
    -
      now rewrite AM, AM' in M.
  Qed.

  (* TODO: move *)
  Lemma NM_map_add_inv
        `{EQa : Equiv A}
        `{EQb : Equiv B}
        `{EQva : Equivalence A EQa}
        `{EQvb : Equivalence B EQb}
        (f : A -> B)
        (INJ : forall x y, f x = f y -> x = y)
        (k : NM.key)
        (v : A)
        (m m' : NM.t A)
        (mm mm' : NM.t B)
    :
      NM.map f m = mm ->
      ¬ NM.In k mm →
      NM.add k (f v) mm = mm' →
      NM.map f m' = mm' ->
      NM.add k v m = m'.
  Proof.
    intros M NI AM M' k'.
    specialize (M k');
      specialize (M' k');
      specialize (AM k').
    rewrite NP.F.map_o in *.
    destruct (NM.E.eq_dec k k').
    1: rewrite NP.F.add_eq_o in * by assumption.
    2: rewrite NP.F.add_neq_o in * by assumption.
    -
      rewrite <- AM in M'.
      unfold option_map in M'.
      break_match; try some_none; try some_inv.
      apply INJ in M'.
      now f_equiv.
    -
      rewrite AM, <-M' in M.
      unfold option_map in M.
      repeat break_match; try some_none; try some_inv.
      apply INJ in M.
      now f_equiv.
  Qed.

  (* TODO: move *)
  Lemma NM_map_inr_all_OK
        `{EQ : Equiv A} :
    forall (m : NM.t A) em,
      NM.map inr m = em ->
      NP.for_all_range is_OK_bool em = true.
  Proof.
    intros.
    unfold NP.for_all_range.
    apply NP.for_all_iff.
    {
      intros _ _ _ v1 v2 VE.
      unfold is_OK_bool.
      repeat break_match;
        now try inl_inr.
    }

    intros.
    specialize (H k).
    apply NM.find_1 in H0.
    rewrite H0 in H; clear H0.
    rewrite NP.F.map_o in H.
    unfold option_map, is_OK_bool in *.
    repeat break_match;
      inv H.
    inv H2.
    reflexivity.
  Qed.

  Lemma NM_err_sequence_OK
        `{EQ : Equiv A}
        `{EQv : Equivalence A EQ}
        (em: NM.t (err A))
    :
      NP.for_all_range is_OK_bool em = true <->
      exists vm,
        NM_err_sequence em = inr vm.
  Proof.
    split.
    -
      intro OK.
      unfold NP.for_all_range, NP.for_all in OK.
      unfold NM_err_sequence.

      rewrite NM.fold_1 in *.
      match goal with
      | [ |- context [fold_left ?f _ _]] => remember f as acc
      end.

      generalize dependent (NM.empty A).
      generalize dependent (NM.elements (elt:=err A) em).
      clear - Heqacc EQv.
      induction l as [|e];
        intros OK s.
      + now exists s.
              +
                destruct e as (k, [v | v]).
                *
                  cbn in *.
                  exfalso; clear - OK.
                  contradict OK.
                  apply Bool.not_true_iff_false.
                  induction l.
                  reflexivity.
                  cbn in *; now break_if.
                *
                  cbn in *.
                  autospecialize IHl; [assumption |].
                  subst acc.
                  eapply IHl.
              -
                intros [vm OK].
                unfold NP.for_all_range, NP.for_all.
                unfold NM_err_sequence in OK.

                rewrite NM.fold_1 in *.
                match goal with
                | [ _ : context [fold_left ?f _ _] |- _] => remember f as acc
                end.
                generalize dependent (NM.empty A).
                generalize dependent (NM.elements (elt:=err A) em).
                clear - Heqacc.

                induction l as [|e];
                  intros s OK.
                + reflexivity.
                +
                  destruct e as (k, [v | v]).
                  all: cbn in *.
                  all: (* poor man's [cbv [acc] in OK.] *)
                    rewrite Heqacc in OK;
                    cbn in OK;
                    rewrite <-Heqacc in OK.
                  *
                    exfalso; clear - OK Heqacc.
                    contradict OK.
                    generalize dependent v.
                    induction l.
                    subst; now cbv.
                    rewrite Heqacc; cbn; rewrite <-Heqacc.
                    cbv [NM_err_seq_step].
                    now break_match.
                  *
                    cbn in *.
                    apply IHl in OK.
                    assumption.
  Qed.

  Lemma NM_err_seq_step_add
        `{EQ : Equiv A}
        `{EQv : Equivalence A EQ}
        (em em' : NM.t (err A))
        (k : NM.key)
        (ev : err A)
        (m0 : err (NM.t A))
    :
      ¬ (NM.In k em) ->
      NP.Add k ev em em' ->
      NM.fold NM_err_seq_step em' m0 =
      NM_err_seq_step k ev (NM.fold NM_err_seq_step em m0).
  Proof.
    intros * NI ADD.
    eapply NP.fold_Add.
    -
      (* typeclasses eauto. *)
      apply err_Equivalence.
    -
      clear - EQv.
      intros k' k EK ev' ev EV em1 em2 EM.
      subst.
      destruct ev.
      +
        cbv.
        constructor.
      +
        cbn.
        repeat break_match;
          try inl_inr; try inl_inr_inv;
            subst.
        constructor.
        f_equiv.
        intros k'.
        destruct (NM.E.eq_dec k k').
        all: try rewrite !NP.F.add_eq_o by assumption.
        all: try rewrite !NP.F.add_neq_o by assumption.
        reflexivity.
        apply EM.
    -
      clear - EQv.
      intros k1 k2 v1 v2 em NK.
      unfold NM_err_seq_step.
      repeat break_match;
        try constructor;
        try inl_inr; try inl_inr_inv;
          subst.
      inv Heqs0.
      intros k.
      destruct (NM.E.eq_dec k1 k), (NM.E.eq_dec k2 k).
      congruence.
      all: try rewrite !NP.F.add_eq_o by assumption.
      all: try rewrite !NP.F.add_neq_o by assumption.
      all: try rewrite !NP.F.add_eq_o by assumption.
      all: reflexivity.
    -
      assumption.
    -
      assumption.
  Qed.

  Lemma NM_err_sequence_inr_fun_spec
        `{EQ : Equiv A}
        `{EQv : Equivalence A EQ}
        (em: NM.t (err A))
        (vm: NM.t A)
    :
      NM_err_sequence em = inr vm <->
      NM.map inr vm = em.
  Proof.
    unfold NM_err_sequence.
    revert vm.
    induction em
      as [em E | em em' IH k v NI ADD]
           using NP.map_induction;
      intro vm.
    -
      split; intros H.
      +
        intro k.
        pose proof E as E'.
        apply NM_Empty_find with (k0:=k) in E'.
        rewrite E'; clear E'.
        eapply NP.fold_Empty in E.
        rewrite E in H.
        inl_inr_inv.
        rewrite NP.F.map_o.
        specialize (H k).
        rewrite <-H.
        reflexivity.
        apply flip_Equivalence.
        typeclasses eauto.
      +
        rewrite NP.fold_Empty.
        3: assumption.
        2: typeclasses eauto.
        f_equiv.
        intros k.
        specialize (H k).
        apply NM_Empty_find with (k0:=k) in E.
        rewrite NP.F.map_o in H.
        rewrite E in H.
        unfold option_map in H.
        break_match; try some_none.
        reflexivity.
    -
      rename vm into vm'.
      rewrite NM_err_seq_step_add; try eassumption.
      destruct (NM.fold NM_err_seq_step em (inr (NM.empty A)))
        as [msg|vm] eqn:P.
      +
        split.
        *
          intros C.
          cbv in C.
          break_match; inv C.
        *
          intros OK.
          exfalso.
          eapply NM_map_inr_all_OK in OK.
          apply NM_err_sequence_OK in OK.
          destruct OK as [vm OK].
          unfold NM_err_sequence in OK.
          rewrite NM_err_seq_step_add in OK; try eassumption.
          rewrite P in OK.
          cbv in OK.
          break_match; inv OK.
      +
        specialize (IH vm).
        assert (M : NM.map inr vm = em)
          by now apply IH.
        clear IH.
        split.
        *
          intro ST.
          destruct v as [?|v]; [inv ST |].
          cbn in ST.
          inl_inr_inv.
          eapply NM_map_add.
          1: typeclasses eauto.
          3: apply NP_Add_NM_add.
          all: eassumption.
        *
          intros M'.
          destruct v as [msg|v].
          --
            exfalso.
            apply NP_Add_NM_add in ADD.
            rewrite <-ADD in M'.
            clear - M'.
            specialize (M' k).
            rewrite NP.F.map_o in M'.
            rewrite NP.F.add_eq_o in M' by reflexivity.
            unfold option_map in M'.
            break_match.
            some_inv; inl_inr.
            some_none.
          --
            cbn.
            f_equiv.
            eapply NM_map_add_inv in NI.
            4: apply NP_Add_NM_add.
            all: try eassumption.
            intros; now inl_inr_inv.
  Qed.

  Section Value_Translation_Correctness.

    Context `{CTT: CTranslationOp} `{CTP: @CTranslationProps CTT}
            `{NTT: NTranslationOp} `{NTP: @NTranslationProps NTT}.

    Instance sheq_DSHVal_proper :
      Proper ((=) ==> (=) ==> iff) (heq_DSHVal heq_CType).
    Proof.
      apply heq_DSHVal_proper.
      apply heq_CType_proper.
    Qed.

    Instance sheq_mem_block_proper:
      Proper ((=) ==> (=) ==> iff) (heq_mem_block heq_CType).
    Proof.
      apply heq_mem_block_proper.
      apply heq_CType_proper.
    Qed.

    Instance sheq_memory_proper:
      Proper ((=) ==> (=) ==> iff) (heq_memory heq_CType).
    Proof.
      apply heq_memory_proper.
      apply heq_CType_proper.
    Qed.

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

    Lemma translateEvalContext_heq_evalContext_eq
          (σ: LE.evalContext) (σ': LE'.evalContext)
      :
        translateEvalContext σ ≡ inr σ' ->
        heq_evalContext heq_CType σ σ'.
    Proof.
      revert σ σ'.
      unfold heq_evalContext, heq_evalContextElem.
      induction σ, σ'; intros.
      -
        auto.
      -
        inv H.
      -
        cbn in H.
        break_let.
        repeat break_match; inv H.
      -
        constructor.
        +
          cbn in *.
          break_let.
          break_let.
          subst.
          repeat break_match; inv H.
          split.
          * auto.
          * inl_inr_inv.
            clear IHσ.
            induction d; cbn in Heqs.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              constructor.
              apply heq_NType_translateNTypeValue_compat.
              rewrite Heqs1.
              reflexivity.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              constructor.
              apply heq_CType_translateCTypeValue_compat.
              rewrite Heqs1.
              reflexivity.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              constructor.
              reflexivity.
              apply heq_NType_translateNTypeValue_compat.
              rewrite Heqs1.
              reflexivity.
        +
          apply IHσ.
          clear IHσ.
          cbn in H.
          break_let.
          repeat break_match_hyp; inv H.
          reflexivity.
    Qed.

    Lemma translateEvalContext_heq_evalContext
          (σ: LE.evalContext) (σ': LE'.evalContext)
      :
        translateEvalContext σ = inr σ' ->
        heq_evalContext heq_CType σ σ'.
    Proof.
      revert σ σ'.
      unfold heq_evalContext, heq_evalContextElem.
      induction σ, σ'; intros.
      -
        auto.
      -
        cbn in H.
        inl_inr_inv.
        contradict H.
        apply cons_nequiv_nil.
      -
        cbn in H.
        break_let.
        repeat break_match; inv H.
        inl_inr_inv.
        symmetry in H.
        contradict H.
        apply cons_nequiv_nil.
      -
        constructor.
        +
          cbn in *.
          break_let.
          break_let.
          subst.
          repeat break_match; inv H.
          split.
          *
            inv H2.
            apply H4.
          * inl_inr_inv.
            clear IHσ.
            induction d; cbn in Heqs.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              inv H.
              unfold products.prod_equiv in H5.
              cbn in H5.
              destruct H5 as [TD BB0].
              rewrite <- TD.


              constructor.
              apply heq_NType_translateNTypeValue_compat.
              rewrite Heqs1.
              reflexivity.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              subst.
              clear H2.
              apply cons_equiv_inv in H.
              destruct H as [H1 H2].
              apply tuple_equiv_inv in H1.
              destruct H1 as [H1 H3].
              setoid_rewrite <- H1.
              constructor.
              apply heq_CType_translateCTypeValue_compat.
              rewrite Heqs1.
              reflexivity.
            --
              break_match.
              inl_inr.
              inl_inr_inv.


              clear H2.
              apply cons_equiv_inv in H.
              destruct H as [H2 H3].
              apply tuple_equiv_inv in H2.
              destruct H2 as [H2 H4].
              setoid_rewrite <-H2.
              setoid_rewrite <-H1.
              constructor.
              reflexivity.
              apply heq_NType_translateNTypeValue_compat.
              rewrite Heqs1.
              reflexivity.
        +
          apply IHσ.
          clear IHσ.
          cbn in H.
          break_let.
          repeat break_match_hyp; inv H.
          apply cons_equiv_inv in H2.
          crush.
    Qed.

    Lemma translate_mem_block_heq_mem_block
          (m:L.mem_block) (m':L'.mem_block):
      translate_mem_block m = inr m' ->
      heq_mem_block heq_CType m m'.
    Proof.
      intros H.
      unfold translate_mem_block in H.
      unfold heq_mem_block.
      intros k.

      remember (L.mem_lookup k m) as e eqn:E; symmetry in E.
      remember (L'.mem_lookup k m') as e' eqn:E'; symmetry in E'.

      apply NM_err_sequence_inr_fun_spec in H.
      specialize (H k).
      unfold L.mem_lookup, L'.mem_lookup in *.
      remember (NM.find k (NM.map inr m')) as re eqn:RE; symmetry in RE.
      remember (NM.find k (NM.map translateCTypeConst m)) as te eqn:TE;
        symmetry in TE.
      destruct e' as [e'|], e as [e|].
      4: constructor.
      -
        destruct re as [re|],te as [te|]; try some_none; try reflexivity.
        +
          some_inv.
          constructor.

          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
          repeat some_inv.
          subst.

          rewrite NP.F.map_o in TE.
          unfold option_map in TE.
          break_match; try some_none.
          repeat some_inv.
          subst.

          apply CTP.
          apply CTP.
          symmetry in H.
          assumption.
        +
          exfalso.
          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
      -
        exfalso.
        destruct re as [re|],te as [te|]; try some_none; try reflexivity.
        +
          some_inv.

          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
          repeat some_inv.
          subst.

          rewrite NP.F.map_o in TE.
          unfold option_map in TE.
          break_match; try some_none.
        +
          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
      -
        exfalso.
        destruct re as [re|],te as [te|]; try some_none; try reflexivity.
        +
          some_inv.

          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
        +
          rewrite NP.F.map_o in TE.
          unfold option_map in TE.
          break_match; try some_none.
    Qed.

    Lemma translate_memory_heq_memory
          (m:L.memory) (m':L'.memory):
      translate_memory m = inr m' ->
      heq_memory heq_CType m m'.
    Proof.
      intros H.
      unfold translate_memory in H.
      unfold heq_memory.
      intros k.

      remember (L.memory_lookup m k) as e eqn:E; symmetry in E.
      remember (L'.memory_lookup m' k) as e' eqn:E'; symmetry in E'.

      apply NM_err_sequence_inr_fun_spec in H.
      specialize (H k).
      unfold L.memory_lookup, L'.memory_lookup in *.
      remember (NM.find k (NM.map inr m')) as re eqn:RE; symmetry in RE.
      remember (NM.find k (NM.map translate_mem_block m)) as te eqn:TE;
        symmetry in TE.

      destruct e' as [e'|], e as [e|].
      4: constructor.
      -
        destruct re as [re|],te as [te|]; try some_none; try reflexivity.
        +
          some_inv.
          constructor.

          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
          repeat some_inv.
          subst.

          rewrite NP.F.map_o in TE.
          unfold option_map in TE.
          break_match; try some_none.
          repeat some_inv.
          subst.

          apply translate_mem_block_heq_mem_block.
          auto.
        +
          exfalso.
          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
      -
        exfalso.
        destruct re as [re|],te as [te|]; try some_none; try reflexivity.
        +
          some_inv.

          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
          repeat some_inv.
          subst.

          rewrite NP.F.map_o in TE.
          unfold option_map in TE.
          break_match; try some_none.
        +
          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
      -
        exfalso.
        destruct re as [re|],te as [te|]; try some_none; try reflexivity.
        +
          some_inv.

          rewrite NP.F.map_o in RE.
          unfold option_map in RE.
          break_match; try some_none.
        +
          rewrite NP.F.map_o in TE.
          unfold option_map in TE.
          break_match; try some_none.
    Qed.

    Lemma translateDSHVal_heq
          (d : L.DSHVal)
          (d' : L'.DSHVal)
      :
        translateDSHVal d = inr d' ->
        heq_DSHVal trivial2 d d'.
    Proof.
      (* NOTE: this lemma must not rely on TranslationProps *)
      clear.
      intros D.
      destruct d;
        cbn in D.
      all: break_match; invc D.
      all: destruct d'; invc H1.
      -
        constructor.
        unfold equiv in H2.
        pose proof heq_NType_proper.
        specialize (H n n).
        autospecialize H; [reflexivity |].
        specialize (H t0 n0 H2).
        apply H.
        clear - Heqs.
        apply heq_NType_translateNTypeValue_compat'.
        now rewrite Heqs.
      -
        repeat constructor.
      -
        destruct H0.
        constructor.
        assumption.
        apply heq_NType_translateNTypeValue_compat'.
        rewrite Heqs; now f_equiv.
    Qed.

    Lemma translateEvalContext_same_indices
          (σ : LE.evalContext)
          (σ' : evalContext)
      :
        translateEvalContext σ = inr σ' ->
        heq_evalContext trivial2 σ σ'.
    Proof.
      (* NOTE: this lemma must not rely on TranslationProps *)
      clear.
      revert σ'.
      induction σ;
        intros σ' Σ'.
      -
        invc Σ'.
        destruct σ'; [| inv H1].
        constructor.
      -
        cbn in *.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
            subst_max.
        destruct σ'; [inv Σ' |].
        apply cons_equiv_inv in Σ'.
        destruct Σ' as [P E].
        constructor.
        +
          destruct p; invc P.
          constructor.
          apply H0.
          clear - H Heqs.
          cbn in H.

          apply translateDSHVal_heq.
          rewrite Heqs.
          f_equiv.
          assumption.
        +
          apply IHσ.
          f_equiv.
          assumption.
    Qed.

    Lemma translate_runtime_mem_block_same_indices
          (mb : L.mem_block)
          (mb' : L'.mem_block)
      :
        translate_runtime_mem_block mb = inr mb' ->
        heq_mem_block trivial2 mb mb'.
    Proof.
      intros M.
      unfold translate_runtime_memory in M.
      apply NM_err_sequence_inr_fun_spec in M.

      intros k.
      specialize (M k).
      unfold LE.mem_lookup, LE'.mem_lookup.
      rewrite !NP.F.map_o in M.
      unfold option_map in M.
      repeat break_match; invc M;
        constructor.
      constructor.
    Qed.

    Lemma translate_mem_block_same_indices
          (mb : L.mem_block)
          (mb' : L'.mem_block)
      :
        translate_mem_block mb = inr mb' ->
        heq_mem_block trivial2 mb mb'.
    Proof.
      intros M.
      unfold translate_runtime_memory in M.
      apply NM_err_sequence_inr_fun_spec in M.

      intros k.
      specialize (M k).
      unfold LE.mem_lookup, LE'.mem_lookup.
      rewrite !NP.F.map_o in M.
      unfold option_map in M.
      repeat break_match; invc M;
        constructor.
      constructor.
    Qed.

    Lemma translate_runtime_memory_same_indices
          (m : L.memory)
          (m' : L'.memory)
      :
        translate_runtime_memory m = inr m' ->
        heq_memory trivial2 m m'.
    Proof.
      intros M.
      unfold translate_runtime_memory in M.
      apply NM_err_sequence_inr_fun_spec in M.

      intros k.
      specialize (M k).
      unfold LE.memory_lookup, LE'.memory_lookup.
      rewrite !NP.F.map_o in M.
      unfold option_map in M.
      repeat break_match; invc M;
        constructor.
      apply translate_runtime_mem_block_same_indices.
      symmetry in H1.
      assumption.
    Qed.

  End Value_Translation_Correctness.

  Section Semantic_Translation_Correctness.

    Context `{CTT: CTranslationOp} `{NTT: NTranslationOp}.

    Lemma heq_PExpr_heq_evalPExpr
          (heq : CT.t → CT'.t → Prop)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (p : L.PExpr)
          (p' : L'.PExpr)
      :
        heq_evalContext heq σ σ' ->
        heq_PExpr p p' ->
        herr_c heq_evalPExpr
               (LE.evalPExpr σ p)
               (LE'.evalPExpr σ' p').
    Proof.
      intros * Σ P.
      inv P.
      invc H; clear P.
      rename x' into x.
      cbn.
      apply Forall2_nth_error with (n:=x) in Σ.
      repeat break_match.
      all: inv Σ.
      all: try constructor.
      all: try now inv H1.
      inv H1; inv H0.
      now constructor.
    Qed.

    Lemma heq_memory_heq_memory_lookup_err
          (heq : CT.t → CT'.t → Prop)
          (msg msg' : string)
          (n n' : nat)
          (m : L.memory)
          (m' : L'.memory)
      :
        n = n' ->
        heq_memory heq m m' ->
        herr_c (heq_mem_block heq)
               (LE.memory_lookup_err msg m n)
               (LE'.memory_lookup_err msg' m' n').
    Proof.
      intros N ME.
      inv N; rename n' into n.
      specialize (ME n).
      inversion ME as [M M' | mb mb' MB M M'].
      +
        symmetry in M, M'.
        apply Option_equiv_eq in M, M'.
        rewrite <-LE.memory_lookup_err_inl_None in M.
        rewrite <-LE'.memory_lookup_err_inl_None in M'.
        destruct (LE.memory_lookup_err msg m n) eqn:M0;
          destruct (LE'.memory_lookup_err msg' m' n) eqn:M1.
        all: rewrite M0, M1 in *; try inl_inr.
        Unshelve. 2,3: exact "". (* to avoid dangling evars *)
        constructor.
      +
        symmetry in M, M'.
        rewrite <-LE.memory_lookup_err_inr_Some_eq in M.
        rewrite <-LE'.memory_lookup_err_inr_Some_eq in M'.
        rewrite M, M'.
        now repeat constructor.
    Qed.

    Lemma heq_mem_block_heq_mem_lookup_err
          (heq : CT.t → CT'.t → Prop)
          (msg msg' : string)
          (n n' : nat)
          (mb : L.mem_block)
          (mb' : L'.mem_block)
      :
        n = n' ->
        heq_mem_block heq mb mb' ->
        herr_c heq
               (LE.mem_lookup_err msg n mb)
               (LE'.mem_lookup_err msg' n' mb').
    Proof.
      intros N ME.
      inv N; rename n' into n.
      specialize (ME n).
      inversion ME as [M M' | t t' T M M'].
      +
        symmetry in M, M'.
        apply Option_equiv_eq in M, M'.
        rewrite <-LE.mem_lookup_err_inl_None in M.
        rewrite <-LE'.mem_lookup_err_inl_None in M'.
        destruct (LE.mem_lookup_err msg n mb) eqn:M0;
          destruct (LE'.mem_lookup_err msg' n mb') eqn:M1.
        all: rewrite M0, M1 in *; try inl_inr.
        Unshelve. 2,3: exact "". (* to avoid dangling evars *)
        constructor.
      +
        symmetry in M, M'.
        rewrite <-LE.mem_lookup_err_inr_Some_eq in M.
        rewrite <-LE'.mem_lookup_err_inr_Some_eq in M'.
        rewrite M, M'.
        now repeat constructor.
    Qed.

    Lemma heq_MExpr_heq_evalMExpr
          (heq : CT.t → CT'.t → Prop)
          (m : L.memory)
          (m' : L'.memory)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (e : L.MExpr)
          (e' : L'.MExpr)
      :
        heq_memory heq m m' ->
        heq_evalContext heq σ σ' ->
        heq_MExpr heq e e' ->
        herr_c (heq_evalMExpr heq)
               (LE.evalMExpr m σ e)
               (LE'.evalMExpr m' σ' e').
    Proof.
      intros * M Σ E.
      inv E.
      -
        rename H into P.
        cbn.
        eapply heq_PExpr_heq_evalPExpr in P;
          [| eassumption].
        inv P.
        constructor.
        repeat break_let; subst.
        inv H1; invc H2.
        apply heq_memory_heq_memory_lookup_err with
            (msg:="MPtrDeref lookup failed")
            (msg':="MPtrDeref lookup failed")
            (n:=n0)
            (n':=n0)
          in M;
          [| reflexivity].
        inversion M.
        constructor.
        now repeat constructor.
      -
        now repeat constructor.
    Qed.

    Lemma heq_evalContext_heq_context_lookup
          (heq : CT.t → CT'.t → Prop)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (msg msg' : string)
          (n : LE.var_id)
      :
        heq_evalContext heq σ σ' ->
        herr_c (heq_evalContextElem heq)
               (LE.context_lookup msg σ n)
               (LE'.context_lookup msg' σ' n).
    Proof.
      intros Σ.
      eapply Forall2_nth_error with (n0:=n) in Σ.
      unfold LE.context_lookup, LE'.context_lookup.
      inv Σ;
        now repeat constructor.
    Qed.

    (* TODO: move *)
    Lemma evalAExpr_NatClosures_length
          (heq : CT.t → CT'.t → Prop)
          (f : LE.AExpr)
          (f' : LE'.AExpr)
          (σ : LE.evalNatContext)
          (σ' : evalNatContext)
      :
        heq_AExpr heq f f' ->
        length (LE.evalAExpr_NatClosures σ f) =
        length (LE'.evalAExpr_NatClosures σ' f').
    Proof.
      intros AE.
      induction AE; cbn.
      all: try rewrite !app_length.
      all: congruence.
    Qed.

    Lemma evalNExpr_closure_trace_equiv_cons_inv
          (heq : CT.t → CT'.t → Prop)
          (x : LE.evalNatClosure)
          (x' : evalNatClosure)
          (l : list LE.evalNatClosure)
          (l' : list evalNatClosure)
      :
        evalNExpr_closure_trace_equiv heq (x :: l) (x' :: l') ->
        evalNExpr_closure_equiv heq x x'
        /\ evalNExpr_closure_trace_equiv heq l l'.
    Proof.
      intro.
      now invc H.
    Qed.

    Lemma evalNExpr_closure_trace_equiv_app_inv
          (heq : CT.t → CT'.t → Prop)
          (l1 l2 : list LE.evalNatClosure)
          (l1' l2' : list LE'.evalNatClosure)
      :
        length l1 = length l1' ->
        evalNExpr_closure_trace_equiv heq (l1 ++ l2) (l1' ++ l2') ->
        evalNExpr_closure_trace_equiv heq l1 l1'
        /\ evalNExpr_closure_trace_equiv heq l2 l2'.
    Proof.
      intros L E.
      unfold evalNExpr_closure_trace_equiv in *.
      pose proof E as E1.
      pose proof E as E2.
      apply Forall2_firstn with (n:=length l1) in E1.
      apply Forall2_skipn with (n:=length l1) in E2.
      rewrite !firstn_app_exact in E1 by congruence.
      rewrite !skipn_app_exact in E2 by congruence.
      tauto.
    Qed.

    Lemma heq_DSHOperator_evalNExpr_closure_trace_equiv_inv
          (heq : CT.t → CT'.t → Prop)
          (op : L.DSHOperator)
          (op' : L'.DSHOperator)
          (σ : LE.evalNatContext)
          (σ' : evalNatContext)
          (σn0 : list LE.evalNatClosure)
          (σn0' : list evalNatClosure)
          (fuel fuel' : nat)
      :
        heq_DSHOperator heq op op' -> (* NOTE: this might not be necessary *)
        heq_evalNatContext σ σ' -> (* NOTE: this might not be necessary *)
        hopt (herr (evalNExpr_closure_trace_equiv heq))
             (LE.intervalEvalDSHOperator σ op σn0 fuel)
             (LE'.intervalEvalDSHOperator σ' op' σn0' fuel') ->
        evalNExpr_closure_trace_equiv heq σn0 σn0'.
    Proof.
      intros O.
      move O before op'.
      revert_until O.
      induction O;
        intros * Σ EO.
      all: destruct fuel, fuel'; try (cbn in EO; inv EO; fail).
      all: try apply hopt_herr_inv in EO.
      -
        assumption.
      -
        do 2 eapply evalNExpr_closure_trace_equiv_cons_inv.
        eassumption.
      -
        invc H.
        invc H3.
        cbn in EO.
        rewrite <-H, <-H4 in *.
        apply hopt_herr_inv in EO.
        apply evalNExpr_closure_trace_equiv_app_inv in EO.
        tauto.
        eapply evalAExpr_NatClosures_length; eassumption.
      -
        invc H.
        invc H3.
        cbn in EO.
        rewrite <-H, <-H4 in *.
        apply hopt_herr_inv in EO.
        apply evalNExpr_closure_trace_equiv_app_inv in EO.
        tauto.
        eapply evalAExpr_NatClosures_length; eassumption.
      -
        invc H.
        invc H4.
        cbn in EO.
        rewrite <-H, <-H5 in *.
        apply hopt_herr_inv in EO.
        apply evalNExpr_closure_trace_equiv_app_inv in EO.
        tauto.
        eapply evalAExpr_NatClosures_length; eassumption.
      -
        eapply evalNExpr_closure_trace_equiv_app_inv.
        2: {
          do 3 eapply evalNExpr_closure_trace_equiv_cons_inv.
          eassumption.
        }
        eapply evalAExpr_NatClosures_length; eassumption.
      -
        copy_apply heq_NT_nat_eq H.
        cbv in H0; subst n'.

        (* quick and dirty fuel tricks:
           to avoid proving -fuel_monotone *)
        generalize dependent (S fuel').
        generalize dependent (S fuel).
        clear fuel fuel'.

        intros fuel' fuel EO.

        generalize dependent fuel'.
        generalize dependent fuel.

        induction n;
          intros fuel fuel' EO.
        +
          destruct fuel, fuel';
            cbn in EO; inv EO.
          apply hopt_herr_inv in EO.
          assumption.
        +
          cbn in EO.
          apply heq_NT_nat_S in H.
          inv H; inv H0.

          destruct fuel, fuel';
            cbn in EO; inv EO.

          rewrite <-H1, <-H2 in *.
          inv EO.
          inv H6.
          repeat break_match;
            inv H4; inv H5.
          eapply IHn.
          eassumption.
          rewrite Heqo, Heqo0.
          do 2 constructor.
          eapply IHO.
          2: eassumption.
          constructor; [| assumption].
          now constructor.
      -
        cbn in EO.
        eapply IHO.
        2: eassumption.
        now repeat constructor.
      -
        assumption.
      -
        cbn in EO.
        repeat break_match;
          inv EO; inv H1.
        eapply IHO1.
        eassumption.
        erewrite Heqo, Heqo0.
        repeat constructor.
        eapply IHO2.
        eassumption.
        rewrite <-H, <-H0.
        now repeat constructor.
    Qed.

    Lemma heq_evalContext_heq_evalNatContext
          (heq : CT.t → CT'.t → Prop)
          (σ : LE.evalContext)
          (σ' : evalContext)
      :
        heq_evalContext heq σ σ' ->
        heq_evalNatContext
          (LE.evalNatContext_of_evalContext σ)
          (LE'.evalNatContext_of_evalContext σ').
    Proof.
      intros I.
      induction I.
      -
        constructor.
      -
        cbn.
        repeat break_let; subst_max.
        constructor; [| assumption].
        destruct d, d0;
          inv H; inv H1.
        all: now constructor.
    Qed.

    Lemma heq_mem_block_mem_add
          (heq : CT.t → CT'.t → Prop)
          (n n' : nat)
          (mb : L.mem_block)
          (mb' : L'.mem_block)
          (t : CT.t)
          (t' : CT'.t)
      :
        heq_mem_block heq mb mb' ->
        n = n' ->
        heq t t' ->
        heq_mem_block heq
                   (LE.mem_add n t mb)
                   (LE'.mem_add n' t' mb').
    Proof.
      intros M N MB.
      invc N; rename n' into k'.
      intros k.
      unfold LE.mem_lookup, LE.mem_add.
      unfold LE'.mem_lookup, LE'.mem_add.
      destruct (NM.E.eq_dec k' k).
      -
        rewrite !NP.F.add_eq_o by assumption.
        now constructor.
      -
        rewrite !NP.F.add_neq_o by assumption.
        apply M.
    Qed.

    Lemma heq_memory_memory_set
          (heq : CT.t → CT'.t → Prop)
          (n n' : nat)
          (mb : L.mem_block)
          (mb' : L'.mem_block)
          (m : LE.memory) 
          (m' : memory)
      :
        heq_memory heq m m' ->
        n = n' ->
        heq_mem_block heq mb mb' ->
        heq_memory heq
                   (LE.memory_set m n mb)
                   (LE'.memory_set m' n' mb').
    Proof.
      intros M N MB.
      invc N; rename n' into k'.
      intros k.
      unfold LE.memory_lookup, LE.memory_set.
      unfold LE'.memory_lookup, LE'.memory_set.
      destruct (NM.E.eq_dec k' k).
      -
        rewrite !NP.F.add_eq_o by assumption.
        now constructor.
      -
        rewrite !NP.F.add_neq_o by assumption.
        apply M.
    Qed.

    Lemma heq_memory_mem_block_exists
          (heq : CT.t → CT'.t → Prop)
          (m : L.memory)
          (m' : L'.memory)
      :
        heq_memory heq m m' ->
        (forall k, LE.mem_block_exists k m <-> LE'.mem_block_exists k m').
    Proof.
      intros.
      rewrite LE.mem_block_exists_exists, LE'.mem_block_exists_exists.
      specialize (H k).
      invc H.
      - split; intros [? C]; discriminate C.
      - split; intros; now eexists.
    Qed.

    (* analogous to [memory_next_key_struct] *)
    Lemma heq_memory_memory_next_key
          (heq : CT.t → CT'.t → Prop)
          (m : L.memory)
          (m' : L'.memory)
      :
        heq_memory heq m m' ->
        LE.memory_next_key m = LE'.memory_next_key m'.
    Proof.
      intros T.
      assert (H : forall k, LE.mem_block_exists k m <-> LE'.mem_block_exists k m')
        by now eapply heq_memory_mem_block_exists.
      clear T.

      unfold LE.memory_next_key, LE'.memory_next_key.
      destruct (NS.max_elt (LE.memory_keys_set m)) as [k1|] eqn:H1;
        destruct (NS.max_elt (LE'.memory_keys_set m')) as [k2|] eqn:H2.
      -
        f_equiv.
        enough (¬ k1 < k2 /\ ¬ k2 < k1)
          by (clear - H0; cbv in *; lia).
        split.
        +
          apply (NS.max_elt_2 H1), LE.memory_keys_set_In, H.
          apply NS.max_elt_1, memory_keys_set_In in H2.
          apply H2.
        +
          apply (NS.max_elt_2 H2), memory_keys_set_In, H.
          apply NS.max_elt_1, LE.memory_keys_set_In in H1.
          apply H1.
      - exfalso.
        apply NS.max_elt_1 in H1.
        apply NS.max_elt_3 in H2.
        apply LE.memory_keys_set_In in H1.
        apply H in H1.
        apply memory_keys_set_In in H1.
        apply  NSP.empty_is_empty_1 in H2.
        rewrite H2 in H1.
        apply NSP.FM.empty_iff in H1.
        tauto.
      - exfalso.
        apply NS.max_elt_1 in H2.
        apply NS.max_elt_3 in H1.
        apply memory_keys_set_In in H2.
        apply H in H2.
        apply LE.memory_keys_set_In in H2.
        apply  NSP.empty_is_empty_1 in H1.
        rewrite H1 in H2.
        apply NSP.FM.empty_iff in H2.
        tauto.
      -
        reflexivity.
    Qed.

    Lemma heq_memory_memory_remove
          (heq : CT.t → CT'.t → Prop)
          (m : L.memory)
          (m' : L'.memory)
          (k k' : nat)
      :
        heq_memory heq m m' ->
        k = k' ->
        heq_memory heq
                   (LE.memory_remove m k)
                   (LE'.memory_remove m' k').
    Proof.
      intros M K.
      invc K.
      intros k.
      unfold LE.memory_lookup, LE.memory_remove.
      unfold LE'.memory_lookup, LE'.memory_remove.
      destruct (NM.E.eq_dec k' k).
      -
        rewrite !NP.F.remove_eq_o by assumption.
        now constructor.
      -
        rewrite !NP.F.remove_neq_o by assumption.
        apply M.
    Qed.

  End Semantic_Translation_Correctness.

  Section ControlFlow_Translation_Correctness.

    Context `{NTT: NTranslationOp}.

    Lemma translateNExpr_syntax
          (n : L.NExpr)
          (n' : L'.NExpr)
      :
        translateNExpr n = inr n' ->
        heq_NExpr n n'.
    Proof.
      generalize dependent n'.
      induction n;
        intros n' TN.
      all: destruct n'.
      all: cbn in *.
      all: repeat break_match.
      all: try inl_inr; repeat inl_inr_inv.
      all: inv TN.
      (* inductive cases *)
      3-9: constructor;
        [apply IHn1 | apply IHn2]; now f_equiv.
      (* base cases *)
      -
        now constructor.
      -
        constructor.
        symmetry in H1.
        pose proof heq_NType_proper t0 t0.
        autospecialize H; [reflexivity |].
        specialize (H t1 t2 H1).
        apply H.
        clear - Heqs.
        apply heq_NType_translateNTypeConst_compat.
        rewrite Heqs; reflexivity.
    Qed.

    Lemma translatePExpr_syntax
          (p : L.PExpr)
          (p' : L'.PExpr)
      :
        translatePExpr p = p' ->
        heq_PExpr p p'.
    Proof.
      intros TP.
      destruct p, p'.
      invc TP.
      now constructor.
    Qed.

    Lemma translateMExpr_syntax
          (m : L.MExpr)
          (m' : L'.MExpr)
      :
        translateMExpr m = inr m' ->
        heq_MExpr trivial2 m m'.
    Proof.
      intros M.
      destruct m.
      -
        cbn in M.
        inl_inr_inv.
        destruct m'; invc M.
        constructor.
        now apply translatePExpr_syntax.
      -
        simpl in M.
        repeat break_match; try inl_inr; inl_inr_inv.
        destruct m'; invc M.
        constructor.
        +
          apply heq_NType_translateNTypeConst_compat.
          rewrite Heqs0.
          now f_equiv.
        +
          apply translate_mem_block_same_indices.
          rewrite Heqs.
          now f_equiv.
    Qed.

    Lemma translateAExpr_syntax
          (a : L.AExpr)
          (a' : L'.AExpr)
      :
        translateAExpr a = inr a' ->
        heq_AExpr trivial2 a a'.
    Proof.
      generalize dependent a'.
      induction a;
        intros a' TA.
      all: destruct a'.
      all: cbn in *.
      all: repeat break_match.
      all: try inl_inr; repeat inl_inr_inv.
      all: inv TA.
      (* inductive cases *)
      5-10: constructor;
        [apply IHa1 | apply IHa2]; now f_equiv.
      4: constructor; apply IHa; now f_equiv.
      (* base cases *)
      -
        now constructor.
      -
        now repeat constructor.
      -
        constructor.
        +
          apply translateMExpr_syntax.
          rewrite Heqs.
          now f_equiv.
        +
          apply translateNExpr_syntax.
          rewrite Heqs0.
          now f_equiv.
    Qed.

    Lemma translation_syntax_always_correct {op op'} :
      translate op = inr op' -> heq_DSHOperator trivial2 op op'.
    Proof.
      generalize dependent op'.
      induction op.
      all: intros op' TE.
      all: cbn in *.
      all: repeat break_match;
        try inl_inr; repeat inl_inr_inv.
      all: destruct op'; invc TE.
      -
        constructor.
      -
        unfold translateMemRef in *.
        cbn in *.
        repeat break_match; invc Heqs; invc Heqs0.
        constructor.
        +
          apply translateNExpr_syntax.
          rewrite Heqs2; now f_equiv.
        +
          apply translateNExpr_syntax.
          rewrite Heqs1; now f_equiv.
        +
          now apply translatePExpr_syntax.
        +
          now apply translatePExpr_syntax.
      -
        cbv in H4; subst n0.
        constructor;
          try now apply translatePExpr_syntax.
        +
          constructor.
          destruct (heq_NType_from_nat n);
            try inl_inr.
          invc Heqs; invc Heqs0.
          now constructor.
        +
          apply translateAExpr_syntax.
          rewrite Heqs1.
          now f_equiv.
      -
        cbv in H4; subst n0.
        constructor;
          try now apply translatePExpr_syntax.
        +
          constructor.
          destruct (heq_NType_from_nat n);
            try inl_inr.
          invc Heqs; invc Heqs0.
          now constructor.
        +
          apply translateAExpr_syntax.
          rewrite Heqs1.
          now f_equiv.
      -
        cbv in H5; subst n0.
        constructor;
          try now apply translatePExpr_syntax.
        +
          constructor.
          destruct (heq_NType_from_nat n);
            try inl_inr.
          invc Heqs; invc Heqs0.
          now constructor.
        +
          apply translateAExpr_syntax.
          rewrite Heqs1.
          now f_equiv.
      -
        destruct src as (osrc_p, osrc_n), dst as (odst_p, odst_n).
        cbn in Heqs2, Heqs3.
        repeat break_match; try inl_inr; repeat inl_inr_inv.
        subst_max.
        constructor;
          try now apply translatePExpr_syntax.
        +
          apply translateNExpr_syntax.
          rewrite Heqs1.
          now f_equiv.
        +
          apply translateNExpr_syntax.
          rewrite Heqs5.
          now f_equiv.
        +
          apply translateNExpr_syntax.
          rewrite Heqs4.
          now f_equiv.
        +
          apply translateAExpr_syntax.
          rewrite Heqs.
          now f_equiv.
        +
          constructor.
      -
        cbv in H2; subst n0.
        constructor.
        +
          constructor.
          destruct (heq_NType_from_nat n);
            try inl_inr.
          invc Heqs; invc Heqs0.
          now constructor.
        +
          eapply IHop; now f_equiv.
      -
        constructor.
        +
          apply heq_NType_translateNTypeConst_compat.
          rewrite Heqs0.
          now f_equiv.
        +
          eapply IHop; now f_equiv.
      -
        constructor.
        now apply translatePExpr_syntax.
        constructor.
      -
        constructor.
        eapply IHop1; now f_equiv.
        eapply IHop2; now f_equiv.
    Qed.

    Ltac autospecialize_closure_equiv H σ σ' :=
      specialize (H σ σ');
      full_autospecialize H;
      [apply LE.evalContext_in_own_range
      |apply LE'.evalContext_in_own_range
      |assumption
      |assumption
      | ].

    Ltac assert_assert_NT_heq H1 H2 :=
      eapply heq_NType_heq_assert_NT_lt in H1;
      [| eapply H2].

    (* NOTE: Here, replacing [trivial2] with [heq_CType]
       will result in an (unprvoable without CTranslationProps)
       statement of semantic preservation *)
    Lemma heq_AExpr_heq_evalAExpr
          (σ : LE.evalContext)
          (σ' : evalContext)
          (m : L.memory)
          (m' : L'.memory)
          (a : L.AExpr)
          (a' : L'.AExpr)
      :
        heq_memory trivial2 m m' ->
        heq_evalContext trivial2 σ σ' ->
        heq_AExpr trivial2 a a' ->
        evalNExpr_closure_trace_equiv trivial2
          (LE.evalAExpr_NatClosures_σ σ a)
          (LE'.evalAExpr_NatClosures_σ σ' a') ->
        herr_c trivial2
               (LE.evalAExpr m σ a)
               (LE'.evalAExpr m' σ' a').
    Proof.
      intros M Σ AE TE.
      induction AE.
      all: cbn in *.
      (* All inductive cases *)
      5-10: apply evalNExpr_closure_trace_equiv_app_inv in TE;
          [| eapply evalAExpr_NatClosures_length; eassumption].
      5-10: autospecialize IHAE1; [tauto |].
      5-10: autospecialize IHAE2; [tauto |].
      5-10: inv IHAE1; inv IHAE2; repeat constructor.
      (* base cases *)
      - (* AVar *)
        invc H.
        eapply heq_evalContext_heq_context_lookup
          with (n:=x') in Σ.
        invc Σ;
          rewrite <-H0, <-H.
        now constructor.
        repeat break_match;
          invc H1; invc H3;
            now constructor.
      - (* ANth *)
        inv TE; clear TE.
        clear H6.
        rename m0 into me, m'0 into me'.
        rename H into ME, H0 into N, H4 into CNE.
        cbn in CNE.
        autospecialize_closure_equiv CNE σ σ'.
        inv CNE; [constructor |].
        eapply heq_MExpr_heq_evalMExpr in ME;
          [| eassumption | eassumption].
        inv ME; [constructor |].
        repeat break_let; subst.
        inv H4.
        assert_assert_NT_heq H6 H1.
        inv H6.
        erewrite <-H8, <-H9; constructor.
        erewrite <-H7, <-H8.
        apply heq_mem_block_heq_mem_lookup_err.
        now apply heq_NType_to_nat'.
        eassumption.
      - (* AAbs *)
        apply IHAE in TE.
        invc TE;
          repeat constructor.
      - (* AConst *)
        repeat constructor.
    Qed.

    Lemma heq_DSHOperator_heq_evalDSHOperator
          (op : LE.DSHOperator)
          (op' : LE'.DSHOperator)
          (fuel fuel' : nat)
          (σ : LE.evalContext)
          (σ' : LE'.evalContext)
          (imem : L.memory)
          (imem' : L'.memory)
      :
        heq_DSHOperator trivial2 op op' ->
        heq_evalContext trivial2 σ σ' ->
        heq_memory trivial2 imem imem' ->
        hopt (herr (evalNExpr_closure_trace_equiv trivial2))
                   (LE.intervalEvalDSHOperator_σ σ op nil fuel)
                   (LE'.intervalEvalDSHOperator_σ σ' op' nil fuel') ->

        (* replace [trivial2] -> [heq_CType] for total semantic preservation *)
        hopt_r (herr_c (heq_memory trivial2))
               (LE.evalDSHOperator σ op imem fuel)
               (LE'.evalDSHOperator σ' op' imem' fuel').
    Proof.

      intros HEQ_OP.
      move HEQ_OP before op'.

      (* generalize trace accumulator for induction *)
      assert (T0E : evalNExpr_closure_trace_equiv trivial2 nil nil)
        by constructor.
      generalize dependent (@nil LE.evalNatClosure).
      generalize dependent (@nil LE'.evalNatClosure).

      intros σn0' σn0;
        move σn0' before σ';
        move σn0 before σ'.
      revert_until HEQ_OP.
      unfold LE.intervalEvalDSHOperator_σ, LE'.intervalEvalDSHOperator_σ.
      induction HEQ_OP;
        intros *; (* intros reverted *)
        intros T0E; (* intros asserted accumulator equivalence *)
        intros HEQ_Σ HEQ_MEMORY NTR_EQUIV'.

      (* assert sufficient fuel, simplify NExpr trace equivalence hyp *)
      (* base cases: *)
      1-6,9: destruct fuel, fuel';
        inversion NTR_EQUIV' as [_ _ [tσn tσn' NTR_EQUIV]];
        clear NTR_EQUIV'; subst_max.

      (* more careful in inductive cases: *)
      Opaque LE.intervalEvalDSHOperator LE'.intervalEvalDSHOperator.
      8-10: destruct fuel, fuel';
        inversion NTR_EQUIV' as [_ _ [tσn tσn' NTR_EQUIV]];
        clear NTR_EQUIV'; subst_max.
      Transparent LE.intervalEvalDSHOperator LE'.intervalEvalDSHOperator.

      - (* NOP *)
        now repeat constructor.
      - (* Assign *)
        cbn.
        rename H into HEQ_SRCN, H0 into HEQ_DSTN.
        rename H1 into HEQ_SRCP, H2 into HEQ_DSTP.
        eapply heq_PExpr_heq_evalPExpr in HEQ_SRCP, HEQ_DSTP;
          try eassumption.
        invc HEQ_SRCP; invc HEQ_DSTP.
        all: repeat break_let; subst.
        all: repeat constructor.
        invc H1; invc H4.
        invc H5; invc H1.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        pose proof HEQ_MEMORY as HEQ_MEMORY''.
        remember_string.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n1)
               (n':=n1)
          in HEQ_MEMORY';
          [| reflexivity].
        inv HEQ_MEMORY'; [constructor |].
        remember_string.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n2)
               (n':=n2)
          in HEQ_MEMORY'';
          [| reflexivity].
        inv HEQ_MEMORY''; [constructor |].

        invc NTR_EQUIV; invc H16; clear H18.
        cbn in H14, H15.
        autospecialize_closure_equiv H14 σ σ'.
        autospecialize_closure_equiv H15 σ σ'.
        inv H14; [constructor |].
        inv H15; [constructor |].

        assert_assert_NT_heq H7 H18.
        inv H7; [rewrite <-H20, <-H21; constructor |].
        rewrite <-H19, <-H20.
        remember_string.
        apply heq_mem_block_heq_mem_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=NT.to_nat a1)
               (n':=NT'.to_nat b1)
          in H5;
          [| apply heq_NType_to_nat'; assumption].
        inversion H5.
        constructor.
        repeat constructor.
        eapply heq_memory_memory_set;
          [assumption | reflexivity |].
        eapply heq_mem_block_mem_add.
        assumption.
        now apply heq_NType_to_nat'.
        constructor.
      - (* IMap *)
        admit.
      - (* BinOp *)
        admit.
      - (* MemMap2 *)
        admit.
      - (* Power *)
        admit.
      - (* MemInit *)
        admit.
      - (* Loop *)
        rename H0 into TΣN, H1 into TΣN';
          symmetry in TΣN, TΣN'.
        copy_apply heq_NT_nat_eq H;
          invc H0; rename n' into n.
        revert_until IHHEQ_OP.
        induction n;
          intros * T0E HEQ_Σ HEQ_MEMORY;
          intros * NTR_EQUIV TΣN TΣN'.
        +
          now repeat constructor.
        +
          cbn; cbn in TΣN, TΣN'.
          destruct (NT.from_nat) eqn:SN, (NT'.from_nat) eqn:SN';
            try (inv TΣN; fail); try (inv TΣN'; fail).
          repeat break_match_hyp;
            invc TΣN; invc TΣN'.
          rename l0 into bσn0, l into bσn0',
          H1 into BΣN, H2 into BΣN',
          Heqo0 into BΣN0, Heqo into BΣN0',
          t0 into sn, t1 into sn'.
          destruct fuel, fuel';
            try (inv BΣN; fail);
            try (inv BΣN'; fail).

          autospecialize IHn;
            [now apply heq_NT_nat_S |].

          specialize (IHn fuel fuel' σ σ' σn0 σn0' imem imem').
          specialize (IHn T0E HEQ_Σ HEQ_MEMORY).
          specialize (IHn bσn0 bσn0'). (* <- inductive *)

          (* for use in multiple places later *)
          assert (HEQ_BΣN0 : evalNExpr_closure_trace_equiv trivial2 bσn0 bσn0').
          {
            eapply heq_DSHOperator_evalNExpr_closure_trace_equiv_inv.
            3: rewrite BΣN, BΣN'.
            -
              eassumption.
            -
              repeat constructor.
              +
                pose proof heq_NType_from_nat n as FN.
                invc FN; congruence.
              +
                eapply heq_evalContext_heq_evalNatContext.
                eassumption.
            -
              now repeat constructor.
          }

          move IHn at bottom.
          full_autospecialize IHn;
            try assumption;
            try congruence.

          Opaque LE.evalDSHOperator LE'.evalDSHOperator.
          inv IHn; [constructor |].
          Transparent LE.evalDSHOperator LE'.evalDSHOperator.

          invc H2;
            [now repeat constructor |].
          rename a0 into loop_mem, b0 into loop_mem',
          H0 into LMEM, H1 into LMEM',
          H3 into HEQ_LOOP_MEM.
          symmetry in LMEM, LMEM'.
          eapply IHHEQ_OP;
            try reflexivity;
            try eassumption.
          *
            constructor; [| assumption].
            cbn.
            intuition.
            constructor.
            pose proof heq_NType_from_nat n as FN.
            invc FN; congruence.
          *
            unfold LE.evalNatContext_of_evalContext.
            unfold LE'.evalNatContext_of_evalContext.
            rewrite !map_cons.
            fold LE.evalNatContext_of_evalContext.
            fold LE'.evalNatContext_of_evalContext.
            cbn [LE.DSHIndexRange_of_DSHVal LE'.DSHIndexRange_of_DSHVal].
            rewrite BΣN, BΣN'.
            now repeat constructor.
      - (* Alloc *)
        rename H0 into TΣN, H1 into TΣN';
          symmetry in TΣN, TΣN'.
        cbn.
        match goal with
        | [ |- context [LE.evalDSHOperator ?σ ?op ?mem ?fuel] ] =>
          remember (LE.evalDSHOperator σ op mem fuel) as eop
        end.
        match goal with
        | [ |- context [LE'.evalDSHOperator ?σ ?op ?mem ?fuel] ] =>
          remember (LE'.evalDSHOperator σ op mem fuel) as eop'
        end.
        enough (hopt_r (herr_c (heq_memory trivial2)) eop eop').
        {
          invc H0; [constructor |].
          invc H1; [repeat constructor |].
          repeat constructor.
          eapply heq_memory_memory_remove.
          assumption.
          eapply heq_memory_memory_next_key.
          eassumption.
        }
        subst.
        assert (HEQ_ΣN0 : evalNExpr_closure_trace_equiv trivial2 σn0 σn0').
        {
          eapply heq_DSHOperator_evalNExpr_closure_trace_equiv_inv.
          3: rewrite TΣN, TΣN'.
          econstructor; eassumption.
          eapply heq_evalContext_heq_evalNatContext; eassumption.
          now repeat constructor.
        }
        eapply IHHEQ_OP;
          try reflexivity;
          try eassumption.
        +
          constructor; [| assumption].
          cbn.
          intuition.
          constructor; [| assumption].
          eapply heq_memory_memory_next_key.
          eassumption.
        +
          eapply heq_memory_memory_set.
          assumption.
          eapply heq_memory_memory_next_key.
          eassumption.
          constructor.
        +
          unfold LE.evalNatContext_of_evalContext.
          unfold LE'.evalNatContext_of_evalContext.
          rewrite !map_cons.
          fold LE.evalNatContext_of_evalContext.
          fold LE'.evalNatContext_of_evalContext.
          cbn [LE.DSHIndexRange_of_DSHVal LE'.DSHIndexRange_of_DSHVal].
          cbn in TΣN, TΣN'.
          rewrite TΣN, TΣN'.
          now repeat constructor.
      - (* Seq *)
        rename H into TΣN, H0 into TΣN';
          symmetry in TΣN, TΣN'.
        cbn; cbn in TΣN, TΣN'.
        repeat break_match_hyp;
          inv TΣN; inv TΣN'.
        clear H1 H0.
        rename l0 into fσn, l into fσn'.
        rename Heqo0 into FΣN, Heqo into FΣN'.
        assert (HEQ_FΣN : evalNExpr_closure_trace_equiv trivial2 fσn fσn').
        {
          eapply heq_DSHOperator_evalNExpr_closure_trace_equiv_inv.
          3: rewrite TΣN, TΣN'.
          eassumption.
          eapply heq_evalContext_heq_evalNatContext; eassumption.
          now repeat constructor.
        }
        assert (HEQF : hopt_r (herr_c (heq_memory trivial2))
                              (LE.evalDSHOperator σ f imem fuel)
                              (evalDSHOperator σ' f' imem' fuel')).
        {
          eapply IHHEQ_OP1.
          4: rewrite FΣN, FΣN'.
          all: try assumption.
          now repeat constructor.
        }

        invc HEQF; [constructor |].
        invc H1; [repeat constructor |].
        eapply IHHEQ_OP2.
        4: rewrite TΣN, TΣN'.
        all: try assumption.
        now repeat constructor.
    Admitted.

  End ControlFlow_Translation_Correctness.

End MDHCOLTypeTranslator.
