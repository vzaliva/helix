(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.DSigmaHCOL.NType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
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

    (* This should use [NM_sequence] directly,
       making [NM_err_sequence] unecessary,
       but we run into universe inconsistency *)
    Definition translate_mem_block (m:L.mem_block) : err L'.mem_block
      := NM_err_sequence (NM.map translateCTypeValue m).

    Definition translate_memory (m:L.memory): err L'.memory :=
      NM_err_sequence (NM.map translate_mem_block m).

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

    Context `{CTT: CTranslationOp} `{CTP: @CTranslationProps CTT}
            `{NTT: NTranslationOp} `{NTP: @NTranslationProps NTT}.

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
      fun m m' => forall k : nat, hopt_r heq_CType (LE.mem_lookup k m) (LE'.mem_lookup k m').

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
          heq_CType ini ini' ->
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
          heq_CType v v' ->
          heq_DSHOperator (L.DSHMemInit p v) (L'.DSHMemInit p' v')
    | heq_DSHSeq:
        forall f f' g g',
          heq_DSHOperator f f' ->
          heq_DSHOperator g g' ->
          heq_DSHOperator (L.DSHSeq f g) (L'.DSHSeq f' g').


    Lemma translation_syntax_always_correct {x x'}:
      translate x = inr x' -> heq_DSHOperator x x'.
    Proof.
      (*
      intros x x' H.
      destruct x, x'; try constructor; try (cbn in H; inversion H); try inl_inr.

      all: repeat  match goal with
          | [|- context[L.DSHAssign ?s ?d]] => destruct s,d
           | [|- context[L.DSHPower _ ?s ?d _ _]] => destruct s,d
           | [H: context[translateMemRef ?s] |- _ ] =>
             destruct s; unfold translateMemRef in H; cbn in H; repeat break_match_hyp
               end.

      all: try inl_inr.
      all: try inl_inr_inv.
      all: try constructor.
      all:crush.
       *)
    Admitted.


    Inductive heq_DSHVal: LE.DSHVal -> LE'.DSHVal -> Prop :=
    | heq_DSHnatVal: forall x x', heq_NType x x' -> heq_DSHVal (LE.DSHnatVal x) (LE'.DSHnatVal x')
    | heq_DSHCTypeVal: forall x x', heq_CType x x' -> heq_DSHVal (LE.DSHCTypeVal x) (LE'.DSHCTypeVal x')
    | heq_DSHPtrVal: forall a a' s s', a=a' -> heq_NType s s' -> heq_DSHVal (LE.DSHPtrVal a s) (LE'.DSHPtrVal a' s').

    Instance heq_DSHVal_proper:
      Proper ((=) ==> (=) ==> iff) heq_DSHVal.
    Proof.
      intros a a' Ea b b' Eb; split; intros H.
      -
        destruct a,b,a',b'; invc H; inv Eb; inv Ea; constructor.
        + eapply heq_NType_proper; eauto; crush.
        + eapply heq_CType_proper; eauto; crush.
        + crush.
        + eapply heq_NType_proper; eauto; crush.
      -
        destruct a,b,a',b'; invc H; inv Eb; inv Ea; constructor.
        + eapply heq_NType_proper; eauto; crush.
        + eapply heq_CType_proper; eauto; crush.
        + crush.
        + eapply heq_NType_proper; eauto; crush.
    Qed.

    Definition heq_evalContextElem : (LE.DSHVal * bool) -> (LE'.DSHVal * bool) -> Prop :=
      fun '(x,p) '(x',p') => p=p' /\ heq_DSHVal x x'.

    Definition heq_evalContext: LE.evalContext -> LE'.evalContext -> Prop :=
      List.Forall2 heq_evalContextElem.

    Definition heq_memory: L.memory -> L'.memory -> Prop :=
      fun m m' => forall k : nat, hopt_r heq_mem_block
                               (LE.memory_lookup m k)
                               (LE'.memory_lookup m' k).

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
          eapply heq_CType_proper;try symmetry; eauto.
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
          eapply heq_CType_proper;try symmetry; eauto.
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

    Lemma translateEvalContext_heq_evalContext_eq
          (σ: LE.evalContext) (σ': LE'.evalContext)
      :
        translateEvalContext σ ≡ inr σ' ->
        heq_evalContext σ σ'.
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

    (* TODO: Move to list setoid *)
    Lemma cons_equiv_inv `{Ae:Equiv A}:
      forall x xs y ys, x::xs = y::ys -> x=y /\ xs=ys.
    Proof.
      intros x xs y ys E.
      unfold equiv, ListSetoid.List_equiv in E.
      inv E.
      auto.
    Qed.

    (* TODO: Move to list setoid *)
    Lemma cons_nequiv_nil `{Ae:Equiv A}:
      forall x xs, @nil A ≠ cons x xs.
    Proof.
      intros x xs H.
      unfold equiv, ListSetoid.List_equiv in H.
      inv H.
    Qed.

    (* Todo: move somewhere *)
    Lemma tuple_equiv_inv `{Ae:Equiv A} `{Be:Equiv B}:
      forall (x x':A) (y y':B), (x,y) = (x',y') -> x=x' /\ y=y'.
    Proof.
      intros x x' y y' E.
      unfold equiv, products.prod_equiv in E.
      crush.
    Qed.

    Lemma translateEvalContext_heq_evalContext
          (σ: LE.evalContext) (σ': LE'.evalContext)
      :
        translateEvalContext σ = inr σ' ->
        heq_evalContext σ σ'.
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

    (* NOTE: the other direction does not hold *)
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

    Definition map_app {A B : Type} (f : A → B) :=
      fun k v m_acc => NM.add k (f v) m_acc.

    Lemma NM_map_fold
       `{EQa : Equiv A}
       `{EQb : Equiv B}
       `{EQva : Equivalence A EQa}
       `{EQvb : Equivalence B EQb}
       (f : A → B)
       (m : NM.t A)
      :
        NM.map f m = NM.fold (map_app f) m (NM.empty B).
    Proof.
      apply NP.fold_rec.
      -
        intros e E k.
        rewrite NP.F.map_o.
        eapply NM_Empty_find in E.
        now rewrite E.
      -
        intros k v m_acc m' m''.
        intros _; clear m.
        intros NI ADD MP.

        intro k'.
        specialize (ADD k').
        rewrite NP.F.map_o.
        cbv [map_app].
        destruct (NM.E.eq_dec k k').
        +
          rewrite NP.F.add_eq_o in * by assumption.
          rewrite ADD.
          reflexivity.
        +
          rewrite NP.F.add_neq_o in * by assumption.
          rewrite ADD.
          specialize (MP k').
          rewrite NP.F.map_o in MP.
          rewrite MP.
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

    Lemma map_add
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


    Lemma map_add_inv
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

    Lemma map_inr_all_OK
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
            eapply map_inr_all_OK in OK.
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
            eapply map_add.
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
              eapply map_add_inv in NI.
              4: apply NP_Add_NM_add.
              all: try eassumption.
              intros; now inl_inr_inv.
    Qed.


    Lemma translate_mem_block_heq_mem_block
          (m:L.mem_block) (m':L'.mem_block):
      translate_mem_block m = inr m' ->
      heq_mem_block m m'.
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
      remember (NM.find k (NM.map translateCTypeValue m)) as te eqn:TE; symmetry in TE.
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
      heq_memory m m'.
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
      remember (NM.find k (NM.map translate_mem_block m)) as te eqn:TE; symmetry in TE.

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

    Lemma Forall2_nth_error
          `{EQa : Equiv A}
          `{EQb : Equiv B}
          `{EQva : Equivalence A EQa}
          `{EQvb : Equivalence B EQb}
          (n : nat)
          (P : A -> B -> Prop)
          (l1 : list A)
          (l2 : list B)
      :
        Forall2 P l1 l2 ->
        hopt_r P (nth_error l1 n) (nth_error l2 n).
    Proof.
      revert l2.
      induction l1;
        intros l2 F.
      -
        admit.
      -
        inversion F; subst.
        rename a into e1', y into e2', l' into l2.
        admit.
    Admitted.

    Ltac autospecialize_closure_equiv H σ σ' :=
      specialize (H σ σ');
      full_autospecialize H;
      [apply LE.evalContext_in_own_range
      |apply LE'.evalContext_in_own_range
      |assumption
      |assumption
      | ].

    Definition heq_evalPExpr : nat * NT.t -> nat * NT'.t -> Prop :=
      fun '(v, size) '(v', size') => v = v' /\ heq_NType size size'.

    Definition heq_evalMExpr
      : LE.mem_block * NT.t -> LE'.mem_block * NT'.t -> Prop :=
      fun '(mb, size) '(mb', size') => heq_mem_block mb mb' /\ heq_NType size size'.

    Lemma heq_PExpr_heq_evalPExpr :
      forall σ σ' p p',
        heq_evalContext σ σ' ->
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
          (msg msg' : string)
          (n n' : nat)
          (m : L.memory)
          (m' : L'.memory)
      :
        n = n' ->
        heq_memory m m' ->
        herr_c heq_mem_block
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
          (msg msg' : string)
          (n n' : nat)
          (mb : L.mem_block)
          (mb' : L'.mem_block)
      :
        n = n' ->
        heq_mem_block mb mb' ->
        herr_c heq_CType
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

    Lemma heq_MExpr_heq_evalMExpr :
      forall m m' σ σ' e e',
        heq_memory m m' ->
        heq_evalContext σ σ' ->
        heq_MExpr e e' ->
        herr_c heq_evalMExpr
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

    Lemma heq_NType_heq_assert_NT_lt
          (a : NT.t)
          (a' : t)
          (b : NT.t)
          (b' : t)
          (msg msg' : string)
      :
        heq_NType a a' ->
        heq_NType b b' ->
        herr_c equiv
               (LE.assert_NT_lt msg a b)
               (LE'.assert_NT_lt msg' a' b').
    Proof.
      intros A B.
      unfold LE.assert_NT_lt, LE'.assert_NT_lt, assert_true_to_err.
      apply heq_NType_to_from_nat in A, B.
      cbv in A, B.
      rewrite A, B.
      break_if;
        now constructor.
    Qed.

    Ltac assert_assert_NT_heq H1 H2 :=
      eapply heq_NType_heq_assert_NT_lt in H1;
      [| eapply H2].

    Lemma heq_AExpr_heq_evalAExpr :
      forall σ σ' σn σn' m m' a a',
        heq_memory m m' ->
        heq_evalContext σ σ' ->
        heq_AExpr a a' ->
        LE.evalNatContext_of_evalContext σ ≡ σn ->
        LE'.evalNatContext_of_evalContext σ' ≡ σn' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures σn a)
          (LE'.evalAExpr_NatClosures σn' a') ->
        herr_c heq_CType
               (LE.evalAExpr m σ a)
               (LE'.evalAExpr m' σ' a').
    Proof.
      intros * M Σ AE ΣN ΣN' TE.
      inversion AE; clear AE; subst.
      all: cbn in *.
      - (* AVar *)
        invc H.
        rename x' into x.
        admit.
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
        now apply heq_NType_to_from_nat.
        assumption.
      - (* AAbs *)
        admit.
      - (* AConst *)
        admit.
      - (* APlus *)
        admit.
      - (* AMinus *)
        admit.
      - (* AMult *)
        admit.
      - (* AMin *)
        admit.
      - (* AMax *)
        admit.
      - (* AZless *)
        admit.
    Admitted.

    Lemma heq_DSHOperator_same_fuel
          (op : L.DSHOperator)
          (op' : L'.DSHOperator)
      :
        heq_DSHOperator op op' ->
        LE.estimateFuel op = LE'.estimateFuel op'.
    Admitted.

    (*
    Lemma from_nat_of_to_nat (nt : NT.t) :
      NT.from_nat (NT.to_nat nt) = inr nt.
    Admitted.
     *)

    (* TODO: this is currently unprovable.
       Either [heq_NT_nat] must be changed,
       or some assumption about [from_nat] must be made *)
    Lemma heq_NT_nat_eq :
      forall n n',
        heq_NT_nat n n' -> n = n'.
    Admitted.

    Lemma to_nat_of_from_nat (n : nat) (nt : NT.t) :
      NT.from_nat n = inr nt ->
      NT.to_nat nt = n.
    Admitted.

    Lemma to_nat_of_from_nat' (n : nat) (nt : NT'.t) :
      NT'.from_nat n = inr nt ->
      NT'.to_nat nt = n.
    Admitted.

    Lemma from_nat_of_same_nat (n : nat) :
      herr_c heq_NType (NT.from_nat n) (NT'.from_nat n).
    Admitted.

    Lemma heq_NT_nat_S (n n' : nat) :
      heq_NT_nat (S n) (S n') ->
      heq_NT_nat n n'.
    Proof.
      intros SE.
      invc SE; constructor.
      invc H.
      rename H2 into SNTEQ,
             a into nt, b into nt',
             H0 into FN, H1 into FN'.

      symmetry in FN, FN'.
      apply err_equiv_eq in FN, FN'.

      copy_apply to_nat_of_from_nat FN; rename H into FNT.
      copy_apply to_nat_of_from_nat' FN'; rename H into FNT'.
      copy_apply heq_NType_to_from_nat SNTEQ; rename H into TN.
      rewrite FNT, FNT' in TN.
      invc TN.
      (* doable *)
    Admitted.

    Inductive heq_DSHIndexRange : LE.DSHIndexRange -> LE'.DSHIndexRange -> Prop :=
    | heq_DSHIndex : forall t t', heq_NType t t' ->
                             heq_DSHIndexRange (LE.DSHIndex t) (LE'.DSHIndex t')
    | heq_DSHOtherVar : heq_DSHIndexRange LE.DSHOtherVar LE'.DSHOtherVar.

    Definition heq_evalNatContext: LE.evalNatContext -> LE'.evalNatContext -> Prop :=
      List.Forall2 heq_DSHIndexRange.

    (*
    (*  Unprovable ? *)
    Lemma heq_DSHOperator_evalNExpr_closure_trace_equiv
          (op : L.DSHOperator)
          (op' : L'.DSHOperator)
          (σ : LE.evalNatContext)
          (σ' : evalNatContext)
          (σn0 : list LE.evalNatClosure)
          (σn0' : list evalNatClosure)
          (fuel fuel' : nat)
      :
        heq_DSHOperator op op' ->
        heq_evalNatContext σ σ' ->
        evalNExpr_closure_trace_equiv σn0 σn0' ->
        hopt_r (herr_c evalNExpr_closure_trace_equiv)
               (LE.intervalEvalDSHOperator σ op σn0 fuel)
               (LE'.intervalEvalDSHOperator σ' op' σn0' fuel').
    Abort.
    *)

    Lemma heq_DSHOperator_evalNExpr_closure_trace_equiv_inv
          (op : L.DSHOperator)
          (op' : L'.DSHOperator)
          (σ : LE.evalNatContext)
          (σ' : evalNatContext)
          (σn0 : list LE.evalNatClosure)
          (σn0' : list evalNatClosure)
          (fuel fuel' : nat)
      :
        heq_DSHOperator op op' -> (* NOTE: this might not be necessary *)
        heq_evalNatContext σ σ' -> (* NOTE: this might not be necessary *)
        hopt (herr evalNExpr_closure_trace_equiv)
               (LE.intervalEvalDSHOperator σ op σn0 fuel)
               (LE'.intervalEvalDSHOperator σ' op' σn0' fuel') ->
        evalNExpr_closure_trace_equiv σn0 σn0'.
    Admitted.

    Lemma heq_evalContext_heq_evalNatContext
          (σ : LE.evalContext)
          (σ' : evalContext)
      :
        heq_evalContext σ σ' ->
        heq_evalNatContext
          (LE.evalNatContext_of_evalContext σ)
          (LE'.evalNatContext_of_evalContext σ').
    Admitted.

    Lemma heq_DSHOperator_heq_evalDSHOperator
          (op : LE.DSHOperator)
          (op' : DSHOperator)
          (fuel fuel' : nat)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (σn : LE.evalNatContext)
          (σn' : evalNatContext)
          (tσn : list LE.evalNatClosure)
          (tσn' : list evalNatClosure)
          (imem : L.memory)
          (imem' : L'.memory)
          (ΣN : LE.evalNatContext_of_evalContext σ ≡ σn)
          (ΣN' : LE'.evalNatContext_of_evalContext σ' ≡ σn')
      :
        heq_DSHOperator op op' ->
        heq_evalContext σ σ' ->
        heq_memory imem imem' ->
        LE.intervalEvalDSHOperator σn op nil fuel ≡ Some (inr tσn) ->
        LE'.intervalEvalDSHOperator σn' op' nil fuel' ≡ Some (inr tσn') ->
        evalNExpr_closure_trace_equiv tσn tσn' ->
        hopt_r (herr_c heq_memory)
               (LE.evalDSHOperator σ op imem fuel)
               (LE'.evalDSHOperator σ' op' imem' fuel').
    Proof.
      intros HEQ_OP.
      move HEQ_OP before op'.

      (* generalize trace accumulator for induction *)
      assert (T0E : evalNExpr_closure_trace_equiv nil nil)
        by constructor.
      generalize dependent (@nil LE.evalNatClosure).
      generalize dependent (@nil LE'.evalNatClosure).

      intros σn0' σn0;
        move σn0' before σ';
        move σn0 before σ'.
      revert_until HEQ_OP.
      induction HEQ_OP;
        intros * ΣN ΣN'; (* intros reverted *)
        intros T0E; (* intros asserted accumulator equivalence *)
        intros HEQ_Σ HEQ_MEMORY TΣN TΣN' NTR_EQIV.
      all: destruct fuel, fuel'; try (cbv in TΣN; cbv in TΣN'; some_none).
      1-6: cbn in TΣN, TΣN';
        repeat some_inv; repeat inl_inr_inv;
          subst.
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
        apply heq_memory_heq_memory_lookup_err
          with (msg:="Error looking up 'x' in DSHAssign")
               (msg':="Error looking up 'x' in DSHAssign")
               (n:=n1)
               (n':=n1)
          in HEQ_MEMORY';
          [| reflexivity].
        inv HEQ_MEMORY'; [constructor |].
        apply heq_memory_heq_memory_lookup_err
          with (msg:="Error looking up 'y' in DSHAssign")
               (msg':="Error looking up 'y' in DSHAssign")
               (n:=n2)
               (n':=n2)
          in HEQ_MEMORY;
          [| reflexivity].
        inv HEQ_MEMORY; [constructor |].

        invc NTR_EQIV; invc H16; clear H18.
        cbn in H14, H15.
        autospecialize_closure_equiv H14 σ σ'.
        autospecialize_closure_equiv H15 σ σ'.
        inv H14; [constructor |].
        inv H15; [constructor |].

        assert_assert_NT_heq H7 H18.
        inv H7; [rewrite <-H20, <-H21; constructor |].
        rewrite <-H19, <-H20.
        apply heq_mem_block_heq_mem_lookup_err
          with (msg:="Error looking up 'v' in DSHAssign")
               (msg':="Error looking up 'v' in DSHAssign")
               (n:=NT.to_nat a1)
               (n':=NT'.to_nat b1)
          in H5;
          [| now apply heq_NType_to_from_nat; assumption].
        inversion H5.
        constructor.
        constructor.
        remember (to_nat b2) as bk.
        replace (NT.to_nat a2) with bk by admit.
        admit.
      - (* IMap *)
        admit.
      - (* BinOp *)
        admit.
      - (* MemMap2 *)
        admit.
      - (* Power *)
        admit.
      - (* Loop *)
        copy_apply heq_NT_nat_eq H;
          invc H0; rename n' into n.
        revert_until IHHEQ_OP.
        induction n;
          intros * T0E HEQ_Σ HEQ_MEMORY TΣN TΣN' NTR_EQIV.
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

          specialize (IHn fuel fuel' σ σ' σn0 σn0').
          specialize (IHn bσn0 bσn0'). (* <- inductive *)
          specialize (IHn imem imem').

          (* for use in multiple places later *)
          assert (HEQ_BΣN0 : evalNExpr_closure_trace_equiv bσn0 bσn0').
          {
            eapply heq_DSHOperator_evalNExpr_closure_trace_equiv_inv.
            3: {
              rewrite BΣN, BΣN'.
              now repeat constructor.
            }
            -
              assumption.
            -
              repeat constructor.
              +
                pose proof from_nat_of_same_nat n as FN.
                invc FN; congruence.
              +
                now apply heq_evalContext_heq_evalNatContext.
          }

          full_autospecialize IHn;
            try assumption.

          move IHn at bottom.
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
          constructor; [| assumption].
          cbn.
          intuition.
          constructor.
          pose proof from_nat_of_same_nat n as FN.
          invc FN; congruence.
      - (* Alloc *)
        admit.
      - (* MemInit *)
        admit.
      - (* Seq *)
        admit.
    Admitted.

  End Relations.

End MDHCOLTypeTranslator.
