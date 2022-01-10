(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Psatz.

Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.MSigmaHCOL.MemSetoid.
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

  (* Heterogeneous equivalence on values before and after translation *)
  Class CTranslation_heq :=
    {
      heq_CType : CT.t -> CT'.t -> Prop ;
      heq_CType_proper : Proper ((=) ==> (=) ==> iff) heq_CType;
    }.

  Class NTranslation_heq :=
    {
      heq_NType : NT.t -> NT'.t -> Prop ;
      heq_NType_proper : Proper ((=) ==> (=) ==> iff) heq_NType;
    }.

  Class CTranslationOp `{CHE : CTranslation_heq} :=
    {
      (* Partial mapping of [CT.t] values to [CT'.t] *)
      translateCTypeValue : CT.t -> err CT'.t ;

      translateCTypeValue_proper : Proper ((=) ==> (=)) translateCTypeValue;

      (* Value mapping should result in "equal" values *)
      translateCTypeValue_heq_CType :
      forall x x', translateCTypeValue x = inr x' -> heq_CType x x';


      (* Ensure [translateCTypeConst] is compatible with [translateCTypeValue] *)
      translateCTypeConst_translateCTypeValue_compat :
      forall x x', translateCTypeConst x = inr x' ->
              translateCTypeValue x = inr x';

      (* Surjectivity: all values in CT't should have correspoding CT.t values
         Not sure if we need this
         translate_surj :
         forall (x' : CT'.t), exists x,
         translateCTypeValue x = inr x';
       *)
    }.

  Class CTranslationOp_strict `{CTO : CTranslationOp} :=
    {
      heq_CType_translateCTypeValue :
      forall x x', heq_CType x x' -> translateCTypeValue x = inr x';
    }.

  (* TODO: [translateNTypeValue] vs [translateNTypeConst].
     Why even have the first one? *)
  Class NTranslationOp `{NHE : NTranslation_heq} :=
    {
      (* Partial mapping of [NT.t] values to [NT'.t] *)
      translateNTypeValue : NT.t -> err NT'.t ;

      translateNTypeValue_proper : Proper ((=) ==> (=)) translateNTypeValue;

      (* Value mapping should result in "equal" values *)
      translateNTypeValue_heq_NType :
      forall x x', translateNTypeValue x = inr x' -> heq_NType x x';

      (* Ensure [translateNTypeConst] is compatible with [translateNTypeValue] *)
      translateNTypeConst_translateNTypeValue_compat :
      forall x x', translateNTypeConst x = inr x' ->
              translateNTypeValue x = inr x';
    }.

  Class NTranslationProps `{NHE : NTranslation_heq} :=
    {
      heq_NType_to_nat :
      forall x x', heq_NType x x' -> NT.to_nat x = NT'.to_nat x';

      heq_NType_from_nat :
      forall n,
        herr_f heq_NType (NT.from_nat n) (NT'.from_nat n);
    }.

  Class NBinOpTranslation
        `{NHE : NTranslation_heq}
        (f: NT.t -> NT.t -> NT.t)
        (f': NT'.t -> NT'.t -> NT'.t)
    :=
      {
        nbinop_translate_compat: forall x x' y y',
          heq_NType x x' ->
          heq_NType y y' ->
          heq_NType (f x y) (f' x' y')
      }.

  Class NOpTranslationProps `{NTT: NTranslation_heq} :=
    {
      NTypeDiv_translation   : NBinOpTranslation NT.NTypeDiv   NT'.NTypeDiv  ;
      NTypeMod_translation   : NBinOpTranslation NT.NTypeMod   NT'.NTypeMod  ;
      NTypePlus_translation  : NBinOpTranslation NT.NTypePlus  NT'.NTypePlus ;
      NTypeMinus_translation : NBinOpTranslation NT.NTypeMinus NT'.NTypeMinus;
      NTypeMult_translation  : NBinOpTranslation NT.NTypeMult  NT'.NTypeMult ;
      NTypeMin_translation   : NBinOpTranslation NT.NTypeMin   NT'.NTypeMin  ;
      NTypeMax_translation   : NBinOpTranslation NT.NTypeMax   NT'.NTypeMax  ;
    }.

  Class CBinOpTranslation
        `{CHE : CTranslation_heq}
        (f: CT.t -> CT.t -> CT.t)
        (f': CT'.t -> CT'.t -> CT'.t)
    :=
      {
        cbinop_translate_compat: forall x x' y y',
          heq_CType x x' ->
          heq_CType y y' ->
          heq_CType (f x y) (f' x' y')
      }.

  Class CUnOpTranslation
        `{CHE : CTranslation_heq}
        (f: CT.t -> CT.t)
        (f': CT'.t -> CT'.t)
    :=
      {
        cunop_translate_compat: forall x x',
          heq_CType x x' ->
          heq_CType (f x) (f' x')
      }.

  Class COpTranslationProps `{CHE : CTranslation_heq} :=
    {
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

    Context `{CTT: CTranslationOp} `{NTT: NTranslationOp}.

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

    Instance translateCTypeConst_proper :
      Proper ((=) ==> (=)) translateCTypeConst.
    Proof.
      intros c1 c2 C.
      unfold translateCTypeConst.
      repeat break_if;
        repeat constructor;
        try reflexivity.
      all: exfalso.
      (* poor man's congruence x6 *)
      -
        clear - C e n.
        contradict n.
        now rewrite <-C.
      -
        clear - C e n.
        contradict n.
        now rewrite <-C.
      -
        clear - C n e0.
        contradict n.
        now rewrite C.
      -
        clear - C e n1.
        contradict n1.
        now rewrite <-C.
      -
        clear - C n e.
        contradict n.
        now rewrite C.
      -
        clear - C n0 e.
        contradict n0.
        now rewrite C.
    Qed.

    (* TODO: ideally this would be moved to MemSetoid *)
    Instance NM_err_sequence_proper
             `{EA : Equiv A} `{EQA : Equivalence A EA}
             (OP : Proper ((@err_equiv _ EA) ==> (=)) is_OK_bool) :
      Proper ((=) ==> (=)) (@NM_err_sequence A).
    Proof.
      intros nm1 nm2 NM.
      destruct NM_err_sequence eqn:S1 at 1;
        destruct NM_err_sequence eqn:S2 at 1;
        try constructor.
      -
        exfalso.

        eassert (NOK : is_OK_bool (inl s) = false) by reflexivity.
        rewrite <-S1 in NOK.
        apply NM_err_sequence_not_OK in NOK.

        eassert (OK : is_OK_bool (inr t0) = true) by reflexivity.
        rewrite <-S2 in OK.
        apply NM_err_sequence_OK in OK.

        clear - OP NM OK NOK.

        unfold NP.for_all_range in *.
        apply NP_for_all_false_iff in NOK;
          [| intros _ _ _ x x' X; now subst].
        cbv [equiv bool.bool_eq] in OK.
        rewrite NP.for_all_iff in OK;
          [| intros _ _ _ x x' X; now subst].

        destruct NOK as (k & e & M1 & F).
        specialize (NM k).
        apply NP.F.find_mapsto_iff in M1.
        rewrite M1 in NM.
        destruct NM.find eqn:M2 in NM; [some_inv | some_none].
        specialize (OK k s).
        autospecialize OK;
          [now apply NP.F.find_mapsto_iff |].
        apply OP in NM.
        congruence.
      -
        exfalso.

        eassert (NOK : is_OK_bool (inl s) = false) by reflexivity.
        rewrite <-S2 in NOK.
        apply NM_err_sequence_not_OK in NOK.

        eassert (OK : is_OK_bool (inr t0) = true) by reflexivity.
        rewrite <-S1 in OK.
        apply NM_err_sequence_OK in OK.

        clear - OP NM OK NOK.

        unfold NP.for_all_range in *.
        apply NP_for_all_false_iff in NOK;
          [| intros _ _ _ x x' X; now subst].
        cbv [equiv bool.bool_eq] in OK.
        rewrite NP.for_all_iff in OK;
          [| intros _ _ _ x x' X; now subst].

        destruct NOK as (k & e & M1 & F).
        specialize (NM k).
        apply NP.F.find_mapsto_iff in M1.
        rewrite M1 in NM.
        destruct NM.find eqn:M2 in NM; [some_inv | some_none].
        specialize (OK k s).
        autospecialize OK;
          [now apply NP.F.find_mapsto_iff |].
        apply OP in NM.
        congruence.
      -
        apply err_equiv_eq in S1, S2.
        apply NM_err_sequence_inr_fun_spec in S1, S2.
        rewrite <-S1, <-S2 in NM.
        clear - NM.
        rename t0 into m1, t1 into m2.
        intros k.
        specialize (NM k).
        rewrite !NP.F.map_o in NM.
        unfold option_map in *.
        repeat break_match;
          try some_none; constructor.
        invc NM.
        invc H1.
        assumption.
    Qed.

    Instance translate_runtime_mem_block_proper :
      Proper ((=) ==> (=)) translate_runtime_mem_block.
    Proof.
      intros mb1 mb2 MB.
      unfold translate_runtime_mem_block.
      eapply NM_err_sequence_proper;
        [intros x1 x2 X; destruct x1, x2; now invc X |].
      intros k.
      specialize (MB k).
      rewrite !NP.F.map_o.
      unfold option_map.
      repeat break_match; try some_none.
      f_equiv.
      apply translateCTypeValue_proper.
      now some_inv.
    Qed.

    Instance translate_mem_block_proper :
      Proper ((=) ==> (=)) translate_mem_block.
    Proof.
      intros mb1 mb2 MB.
      eapply NM_err_sequence_proper;
        [intros x1 x2 X; destruct x1, x2; now invc X |].
      intros k.
      specialize (MB k).
      rewrite !NP.F.map_o.
      unfold option_map.
      repeat break_match; try some_none.
      f_equiv.
      f_equiv.
      now some_inv.
    Qed.

    Instance translate_runtime_memory_proper :
      Proper ((=) ==> (=)) translate_runtime_memory.
    Proof.
      intros m1 m2 M.
      unfold translate_runtime_memory.
      eapply NM_err_sequence_proper;
        [intros x1 x2 X; destruct x1, x2; now invc X |].
      intros k.
      specialize (M k).
      rewrite !NP.F.map_o.
      unfold option_map.
      repeat break_match; try some_none.
      do 2 f_equiv.
      now some_inv.
    Qed.

    Instance translateNTypeConst_proper :
      Proper ((=) ==> (=)) translateNTypeConst.
    Proof.
      intros c1 c2 C.
      unfold translateNTypeConst.
      f_equiv.
      now apply NT.to_nat_proper.
    Qed.

    Instance translateNExpr_proper :
      Proper ((=) ==> (=)) translateNExpr.
    Proof.
      intros n1 n2 N.
      induction N; cbn.

      (* inductive cases *)
      3-9: repeat break_match;
           invc IHN1; invc IHN2;
           now repeat constructor.

      (* base cases *)
      -
        cbn.
        now repeat constructor.
      -
        cbn.
        apply translateNTypeConst_proper in H.
        repeat break_match; invc H;
          now repeat constructor.
    Qed.

    Instance translatePExpr_proper :
      Proper ((=) ==> (=)) translatePExpr.
    Proof.
      intros p1 p2 P.
      destruct P.
      cbv in H.
      subst.
      reflexivity.
    Qed.

    Instance translateMExpr_proper :
      Proper ((=) ==> (=)) translateMExpr.
    Proof.
      intros m1 m2 M.
      destruct M.
      -
        cbn.
        repeat constructor.
        now rewrite H.
      -
        simpl.
        destruct H as [AB SZ].
        eapply translate_mem_block_proper in AB.
        eapply translateNTypeConst_proper in SZ.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
    Qed.

    Instance translateAExpr_proper :
      Proper ((=) ==> (=)) translateAExpr.
    Proof.
      intros a1 a2 A.
      induction A; cbn.

      (* inductive cases *)
      4-10: repeat break_match;
            try inl_inr; repeat inl_inr_inv;
            now repeat constructor.

      (* base cases *)
      -
        cbv in H.
        subst.
        reflexivity.
      -
        apply translateCTypeConst_proper in H.
        repeat break_match; invc H;
          now repeat constructor.
      -
        apply translateNExpr_proper in H.
        apply translateMExpr_proper in H0.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
    Qed.

    Instance translate_proper :
      Proper ((=) ==> (=)) translate.
    Proof.
      intros op1 op2 OP.
      induction OP;
        try reflexivity.
      -
        apply translateNExpr_proper in H, H0.
        apply translatePExpr_proper in H1, H2.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        cbv in H; subst n'.
        apply translatePExpr_proper in H0, H1.
        apply translateAExpr_proper in H2.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        cbv in H; subst n'.
        apply translatePExpr_proper in H0, H1.
        apply translateAExpr_proper in H2.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        cbv in H; subst n'.
        apply translatePExpr_proper in H0, H1, H2.
        apply translateAExpr_proper in H3.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        apply translateNExpr_proper in H, H0, H1.
        apply translatePExpr_proper in H2, H3.
        apply translateAExpr_proper in H4.
        apply translateCTypeConst_proper in H5.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        cbv in H; subst n'.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        apply translateNTypeConst_proper in H.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        apply translatePExpr_proper in H.
        apply translateCTypeConst_proper in H0.
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        cbn.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
    Qed.

    Instance translateDSHVal_proper :
      Proper ((=) ==> (=)) translateDSHVal.
    Proof.
      intros v1 v2 V.
      destruct V; cbn.
      -
        apply translateNTypeValue_proper in H.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        apply translateCTypeValue_proper in H.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
      -
        destruct H.
        invc H0.
        apply translateNTypeValue_proper in H.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
    Qed.

    Instance translateEvalContext_proper :
      Proper ((=) ==> (=)) translateEvalContext.
    Proof.
      intros σ1 σ2 Σ.
      induction Σ.
      -
        reflexivity.
      -
        cbn.
        repeat break_let; subst_max.
        invc H; cbn in *.
        apply translateDSHVal_proper in H0.
        repeat break_match;
          try inl_inr; repeat inl_inr_inv;
          now repeat constructor.
    Qed.

  End EvalTranslations.

  Section Relations.

    Context `{NHE : NTranslation_heq}
            `{CHE : CTranslation_heq}.

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

    Inductive heq_DSHVal: LE.DSHVal -> LE'.DSHVal -> Prop :=
    | heq_DSHnatVal: forall x x', heq_NType x x' -> heq_DSHVal (LE.DSHnatVal x) (LE'.DSHnatVal x')
    | heq_DSHCTypeVal: forall x x', heq_CType x x' -> heq_DSHVal (LE.DSHCTypeVal x) (LE'.DSHCTypeVal x')
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
          eapply heq_CType_proper; try symmetry; eauto.
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
          eapply heq_CType_proper; try symmetry; eauto.
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

    Instance heq_NExpr_proper :
      Proper ((=) ==> (=) ==> (iff)) heq_NExpr.
    Proof.
      intros n1 n2 N n1' n2' N'.
      split; intros E.
      -
        generalize dependent n2.
        generalize dependent n2'.
        induction E;
          intros.
        all: invc N; invc N'.
        (* inductive cases *)
        3-9: constructor;
               [eapply IHE1 | eapply IHE2];
               eassumption.

        (* base cases *)
        +
          constructor.
          cbv [equiv peano_naturals.nat_equiv] in *.
          congruence.
        +
          constructor.
          eapply heq_NType_proper in H2;
            [| eassumption].
          tauto.
      -
        generalize dependent n1.
        generalize dependent n1'.
        induction E;
          intros.
        all: invc N; invc N'.
        (* inductive cases *)
        3-9: constructor;
               [eapply IHE1 | eapply IHE2];
               eassumption.

        (* base cases *)
        +
          constructor.
          cbv [equiv peano_naturals.nat_equiv] in *.
          congruence.
        +
          constructor.
          eapply heq_NType_proper in H3;
            [| eassumption].
          tauto.
    Qed.

    Instance evalNExpr_closure_equiv_proper :
      Proper ((=) ==> (=) ==> (iff)) evalNExpr_closure_equiv.
    Proof.
      intros (σn1, n1) (σn2, n2) NC (σn1', n1') (σn2', n2') NC'.
      unfold evalNExpr_closure_equiv.
      destruct NC as [ΣN N],
          NC' as [ΣN' N'];
        cbn in *.
      split; intros E * ΣR ΣR' Σ NN'.
      -
        specialize (E σ σ').
        full_autospecialize E;
          [now rewrite ΣN
          |now rewrite ΣN'
          |assumption
          |now rewrite N, N'
          |
          ].

        invc E.
        +
          symmetry in H0, H.
          eapply herr_c_proper.
          eapply heq_NType_proper.
          rewrite <-N, H0; reflexivity.
          rewrite <-N', H; reflexivity.
          now constructor.
        +
          symmetry in H0, H.
          eapply herr_c_proper.
          eapply heq_NType_proper.
          rewrite <-N, H; reflexivity.
          rewrite <-N', H0; reflexivity.
          now constructor.
      -
        specialize (E σ σ').
        full_autospecialize E;
          [now rewrite <-ΣN
          |now rewrite <-ΣN'
          |assumption
          |now rewrite <-N, <-N'
          |
          ].

        invc E.
        +
          symmetry in H0, H.
          eapply herr_c_proper.
          eapply heq_NType_proper.
          rewrite N, H0; reflexivity.
          rewrite N', H; reflexivity.
          now constructor.
        +
          symmetry in H0, H.
          eapply herr_c_proper.
          eapply heq_NType_proper.
          rewrite N, H; reflexivity.
          rewrite N', H0; reflexivity.
          now constructor.
    Qed.

    Instance evalNExpr_closure_trace_equiv_proper :
      Proper ((=) ==> (=) ==> (iff)) evalNExpr_closure_trace_equiv.
    Proof.
      intros σnc1 σnc2 ΣNC σn1 σn2 ΣN.
      unfold evalNExpr_closure_trace_equiv.
      now apply Forall2_proper.
    Qed.

  End Relations.

  (* TODO: this section needs cleanup *)
  Section Necessary_NT_Props.

    Context `{NHE: NTranslation_heq}.
    Context `{NTP: @NTranslationProps NHE}.

    (* TODO: move to module? *)
    Lemma from_nat_of_to_nat (nt : NT.t) :
      NT.from_nat (NT.to_nat nt) = inr nt.
    Proof.
      now apply NT.to_nat_from_nat.
    Qed.

    Lemma from_nat_of_to_nat' (nt' : NT'.t) :
      NT'.from_nat (NT'.to_nat nt') = inr nt'.
    Proof.
      now apply NT'.to_nat_from_nat.
    Qed.

    Lemma to_nat_of_from_nat (n : nat) (nt : NT.t) :
      NT.from_nat n = inr nt ->
      NT.to_nat nt = n.
    Proof.
      apply NT.to_nat_from_nat.
    Qed.

    Lemma to_nat_of_from_nat' (n : nat) (nt : NT'.t) :
      NT'.from_nat n = inr nt ->
      NT'.to_nat nt = n.
    Proof.
      apply NT'.to_nat_from_nat.
    Qed.

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
      apply to_nat_from_nat in TN.
      cbv in TN.
      assert (NN' : herr_f heq_NType
                     (NT.from_nat (NT.to_nat n))
                     (from_nat (to_nat n')))
        by (rewrite TN; apply heq_NType_from_nat).
      pose proof from_nat_of_to_nat' n' as N'.
      pose proof from_nat_of_to_nat n as N.
      invc NN'.
      -
        now rewrite <-H0 in N.
      -
        now rewrite <-H1 in N'.
      -
        rewrite <-H in N; rewrite <-H0 in N'.
        repeat inl_inr_inv.
        symmetry in N, N'.
        eapply heq_NType_proper;
          eassumption.
    Qed.

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
      apply heq_NType_to_nat.
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
        apply heq_NType_to_nat in SE.
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

      clear - FN FN' NTP.
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
      apply heq_NType_to_nat in A, B.
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
      apply heq_NType_to_nat in A, B.
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

  Section TranslationOp_Correctness.

    Context `{NTO : NTranslationOp} `{CTO : CTranslationOp}.

    Fact heq_CType_zero_one_wd:
      heq_CType CT.CTypeZero CT'.CTypeZero /\
      heq_CType CT.CTypeOne CT'.CTypeOne.
    Proof.
      split;
        apply translateCTypeValue_heq_CType;
        apply translateCTypeConst_translateCTypeValue_compat;
        cbv.
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
              apply translateNTypeValue_heq_NType.
              rewrite Heqs1.
              reflexivity.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              constructor.
              apply translateCTypeValue_heq_CType.
              rewrite Heqs1.
              reflexivity.
            --
              break_match.
              inl_inr.
              inl_inr_inv.
              constructor.
              reflexivity.
              apply translateNTypeValue_heq_NType.
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
              destruct d0; invc TD.
              constructor.
              apply translateNTypeValue_heq_NType.
              rewrite Heqs1.
              now constructor.
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
              destruct d0; invc H1.
              constructor.
              apply translateCTypeValue_heq_CType.
              rewrite Heqs1.
              now constructor.
            --
              break_match.
              inl_inr.
              inl_inr_inv.


              clear H2.
              apply cons_equiv_inv in H.
              destruct H as [H2 H3].
              apply tuple_equiv_inv in H2.
              destruct H2 as [H2 H4].
              destruct d0; invc H1; invc H2.
              constructor.
              tauto.
              apply translateNTypeValue_heq_NType.
              rewrite Heqs1.
              now constructor.
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

          apply CTO.
          apply translateCTypeConst_translateCTypeValue_compat.
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

    (* TODO: rename *)
    Lemma translate_runtime_mem_block_same_indices
          (mb : L.mem_block)
          (mb' : L'.mem_block)
      :
        translate_runtime_mem_block mb = inr mb' ->
        heq_mem_block mb mb'.
    Proof.
      intros M.
      apply NM_err_sequence_inr_fun_spec in M.

      intros k.
      specialize (M k).
      unfold LE.mem_lookup, LE'.mem_lookup.
      rewrite !NP.F.map_o in M.
      unfold option_map in M.
      repeat break_match; invc M;
        constructor.
      apply CTO.
      now symmetry.
    Qed.

    Lemma heq_mem_block_translate_runtime_mem_block
          `{CTOS : CTranslationOp_strict}
          (mb : L.mem_block)
          (mb' : L'.mem_block)
      :
        heq_mem_block mb mb' ->
        translate_runtime_mem_block mb = inr mb'.
    Proof.
      intros E.
      apply NM_err_sequence_inr_fun_spec.

      intros k.
      specialize (E k).
      unfold LE.mem_lookup, LE'.mem_lookup in E.
      rewrite !NP.F.map_o.
      unfold option_map.
      repeat break_match; invc E;
        constructor.
      apply heq_CType_translateCTypeValue in H1.
      rewrite H1.
      reflexivity.
    Qed.

    (* TODO: rename *)
    Lemma translate_runtime_memory_same_indices
          (m : L.memory)
          (m' : L'.memory)
      :
        translate_runtime_memory m = inr m' ->
        heq_memory m m'.
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
      now symmetry.
    Qed.

    Lemma heq_memory_translate_runtime_memory
          `{CTOS : CTranslationOp_strict}
          (m : L.memory)
          (m' : L'.memory)
      :
        heq_memory m m' ->
        translate_runtime_memory m = inr m'.
    Proof.
      intros E.
      unfold translate_runtime_memory.
      apply NM_err_sequence_inr_fun_spec.

      intros k.
      specialize (E k).
      unfold LE.memory_lookup, LE'.memory_lookup in E.
      rewrite !NP.F.map_o.
      unfold option_map.
      repeat break_match; invc E;
        constructor.
      apply heq_mem_block_translate_runtime_mem_block in H1.
      rewrite H1.
      reflexivity.
    Qed.

    Lemma translateDSHVal_heq
          (d : L.DSHVal)
          (d' : L'.DSHVal)
      :
        translateDSHVal d = inr d' ->
        heq_DSHVal d d'.
    Proof.
      (* NOTE: this lemma must not rely on TranslationProps *)
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
        clear - Heqs NTO.
        apply translateNTypeValue_heq_NType.
        now rewrite Heqs.
      -
        constructor.
        apply CTO.
        rewrite Heqs.
        now f_equiv.
      -
        destruct H0.
        constructor.
        assumption.
        apply translateNTypeValue_heq_NType.
        rewrite Heqs; now f_equiv.
    Qed.

    (* TODO: rename *)
    Lemma translateEvalContext_same_indices
          (σ : LE.evalContext)
          (σ' : evalContext)
      :
        translateEvalContext σ = inr σ' ->
        heq_evalContext σ σ'.
    Proof.
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
          clear - H Heqs NTO.
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

  End TranslationOp_Correctness.

  Section Syntactic_Translation_Correctness.

    Context `{NTO : NTranslationOp} `{CTO : CTranslationOp}.

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
        clear - Heqs NTO.
        apply NTO.
        apply NTO.
        now rewrite Heqs.
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
        heq_MExpr m m'.
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
          apply NTO, NTO.
          rewrite Heqs0.
          now f_equiv.
        +
          apply translate_mem_block_heq_mem_block.
          rewrite Heqs.
          now f_equiv.
    Qed.

    Lemma translateAExpr_syntax
          (a : L.AExpr)
          (a' : L'.AExpr)
      :
        translateAExpr a = inr a' ->
        heq_AExpr a a'.
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
        constructor.
        apply translateCTypeValue_heq_CType,
          translateCTypeConst_translateCTypeValue_compat.
        rewrite Heqs.
        now f_equiv.
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

    Theorem translation_syntax_always_correct
            `{NTP : @NTranslationProps NHE}
            {op op'}
      :
        translate op = inr op' ->
        heq_DSHOperator op op'.
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
                  apply translateCTypeValue_heq_CType,
          translateCTypeConst_translateCTypeValue_compat.
          rewrite Heqs0.
          now f_equiv.
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
        apply translateCTypeValue_heq_CType,
          translateCTypeConst_translateCTypeValue_compat.
        rewrite Heqs.
        now f_equiv.
      -
        constructor.
        eapply IHop1; now f_equiv.
        eapply IHop2; now f_equiv.
    Qed.

  End Syntactic_Translation_Correctness.

  Section Semantic_Translation_Correctness.

    Context `{NHE : NTranslation_heq} `{CHE : CTranslation_heq}.
    Context `{NTP : @NTranslationProps NHE}.

    Lemma heq_PExpr_heq_evalPExpr
          (σ : LE.evalContext)
          (σ' : evalContext)
          (p : L.PExpr)
          (p' : L'.PExpr)
      :
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

    Lemma heq_MExpr_heq_evalMExpr
          (m : L.memory)
          (m' : L'.memory)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (e : L.MExpr)
          (e' : L'.MExpr)
      :
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

    Lemma heq_evalContext_heq_context_lookup
          (σ : LE.evalContext)
          (σ' : evalContext)
          (msg msg' : string)
          (n : LE.var_id)
      :
        heq_evalContext σ σ' ->
        herr_c heq_evalContextElem
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
          (f : LE.AExpr)
          (f' : LE'.AExpr)
          (σ : LE.evalNatContext)
          (σ' : evalNatContext)
      :
        heq_AExpr f f' ->
        length (LE.evalAExpr_NatClosures σ f) =
        length (LE'.evalAExpr_NatClosures σ' f').
    Proof.
      intros AE.
      induction AE; cbn.
      all: try rewrite !app_length.
      all: congruence.
    Qed.

    Lemma evalNExpr_closure_trace_equiv_cons_inv
          (x : LE.evalNatClosure)
          (x' : evalNatClosure)
          (l : list LE.evalNatClosure)
          (l' : list evalNatClosure)
      :
        evalNExpr_closure_trace_equiv (x :: l) (x' :: l') ->
        evalNExpr_closure_equiv x x'
        /\ evalNExpr_closure_trace_equiv l l'.
    Proof.
      intro.
      now invc H.
    Qed.

    Lemma evalNExpr_closure_trace_equiv_app_inv
          (l1 l2 : list LE.evalNatClosure)
          (l1' l2' : list LE'.evalNatClosure)
      :
        length l1 = length l1' ->
        evalNExpr_closure_trace_equiv (l1 ++ l2) (l1' ++ l2') ->
        evalNExpr_closure_trace_equiv l1 l1'
        /\ evalNExpr_closure_trace_equiv l2 l2'.
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
          (σ : LE.evalContext)
          (σ' : evalContext)
      :
        heq_evalContext σ σ' ->
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
          (n n' : nat)
          (mb : L.mem_block)
          (mb' : L'.mem_block)
          (t : CT.t)
          (t' : CT'.t)
      :
        heq_mem_block mb mb' ->
        n = n' ->
        heq_CType t t' ->
        heq_mem_block
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
          (n n' : nat)
          (mb : L.mem_block)
          (mb' : L'.mem_block)
          (m : LE.memory)
          (m' : memory)
      :
        heq_memory m m' ->
        n = n' ->
        heq_mem_block mb mb' ->
        heq_memory
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
          (m : L.memory)
          (m' : L'.memory)
      :
        heq_memory m m' ->
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
          (m : L.memory)
          (m' : L'.memory)
      :
        heq_memory m m' ->
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
          (m : L.memory)
          (m' : L'.memory)
          (k k' : nat)
      :
        heq_memory m m' ->
        k = k' ->
        heq_memory
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

    Lemma heq_mem_block_heq_mem_union
          (mb1 mb2 : L.mem_block)
          (mb1' mb2' : L'.mem_block)
      :
        heq_mem_block mb1 mb1' ->
        heq_mem_block mb2 mb2' ->
        heq_mem_block
          (LE.mem_union mb1 mb2)
          (LE'.mem_union mb1' mb2').
    Proof.
      intros MB1 MB2.
      intros k;
        specialize (MB1 k); specialize (MB2 k).
      unfold LE.mem_lookup, LE.mem_union in *.
      unfold LE'.mem_lookup, LE'.mem_union in *.
      rewrite !NP.F.map2_1bis by reflexivity.
      invc MB1; invc MB2;
        now constructor.
    Qed.

    Lemma heq_mem_const_block
          (n n' : nat)
          (v : CT.t)
          (v' : CT'.t)
      :
        n = n' ->
        heq_CType v v' ->
        heq_mem_block
          (LE.mem_const_block n v)
          (LE'.mem_const_block n' v').
    Proof.
      intros N V.
      cbv in N; subst n'.
      intros k.
      destruct (NatUtil.lt_ge_dec k n).
      -
        rewrite LE.mem_const_block_find, LE'.mem_const_block_find
          by assumption.
        now constructor.
      -
        rewrite LE.mem_const_block_find_oob, LE'.mem_const_block_find_oob
          by assumption.
        constructor.
    Qed.


    (** * ******** *)

    (*
    Context `{NTT: NTranslationOp}.
    Context `{NTP: NTranslationProps}.
     *)

    Context `{COP : @COpTranslationProps CHE}.

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

    Lemma heq_AExpr_heq_evalAExpr
          (σ : LE.evalContext)
          (σ' : evalContext)
          (m : L.memory)
          (m' : L'.memory)
          (a : L.AExpr)
          (a' : L'.AExpr)
      :
        heq_memory m m' ->
        heq_evalContext σ σ' ->
        heq_AExpr a a' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures_σ σ a)
          (LE'.evalAExpr_NatClosures_σ σ' a') ->
        herr_c heq_CType
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
      5-10: inv IHAE1; inv IHAE2; repeat constructor; now apply COP.
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
        now apply heq_NType_to_nat.
        eassumption.
      - (* AAbs *)
        apply IHAE in TE.
        invc TE;
          constructor.
        now apply COP.
      - (* AConst *)
        now constructor.
    Qed.

    Lemma heq_AExpr_heq_evalIUnCType
          (m : L.memory)
          (m' : L'.memory)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (nt : NT.t)
          (nt' : NT'.t)
          (ct : CT.t)
          (ct' : CT'.t)
      :
        heq_memory m m' ->
        heq_evalContext σ σ' ->
        heq_AExpr f f' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures
             (LE.DSHOtherVar :: LE.DSHIndex nt :: LE.evalNatContext_of_evalContext σ)
             f)
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHIndex nt' :: evalNatContext_of_evalContext σ')
             f') ->
        heq_NType nt nt' ->
        heq_CType ct ct' ->
        herr_c heq_CType
               (LE.evalIUnCType m σ f nt ct)
               (LE'.evalIUnCType m' σ' f' nt' ct').
    Proof.
      intros M Σ F FT NT CT.
      unfold LE.evalIUnCType, LE'.evalIUnCType.
      eapply heq_AExpr_heq_evalAExpr in M.
      inversion M as [? ? B1 B2 | ? ? ? B1 B2];
        rewrite <-B1, <-B2; [constructor |].
      all: repeat constructor.
      all: assumption.
    Qed.

    Lemma heq_AExpr_heq_evalIBinCType
          (m : L.memory)
          (m' : L'.memory)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (nt : NT.t)
          (nt' : NT'.t)
          (ct1 ct2 : CT.t)
          (ct1' ct2' : CT'.t)
      :
        heq_memory m m' ->
        heq_evalContext σ σ' ->
        heq_AExpr f f' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures
             (LE.DSHOtherVar :: LE.DSHOtherVar :: LE.DSHIndex nt
                             :: LE.evalNatContext_of_evalContext σ)
             f)
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHOtherVar :: DSHIndex nt'
                          :: evalNatContext_of_evalContext σ')
             f') ->
        heq_NType nt nt' ->
        heq_CType ct1 ct1' ->
        heq_CType ct2 ct2' ->
        herr_c heq_CType
               (LE.evalIBinCType m σ f nt ct1 ct2)
               (LE'.evalIBinCType m' σ' f' nt' ct1' ct2').
    Proof.
      intros M Σ F FT NT CT1 CT2.
      unfold LE.evalIBinCType, LE'.evalIBinCType.
      eapply heq_AExpr_heq_evalAExpr in M.
      inversion M as [? ? B1 B2 | ? ? ? B1 B2];
        rewrite <-B1, <-B2; [constructor |].
      all: repeat constructor.
      all: try assumption.
    Qed.

    Lemma heq_AExpr_heq_evalBinCType
          (m : L.memory)
          (m' : L'.memory)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (ct1 ct2 : CT.t)
          (ct1' ct2' : CT'.t)
      :
        heq_memory m m' ->
        heq_evalContext σ σ' ->
        heq_AExpr f f' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures
             (LE.DSHOtherVar :: LE.DSHOtherVar
                             :: LE.evalNatContext_of_evalContext σ)
             f)
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHOtherVar
                          :: evalNatContext_of_evalContext σ')
             f') ->
        heq_CType ct1 ct1' ->
        heq_CType ct2 ct2' ->
        herr_c heq_CType
               (LE.evalBinCType m σ f ct1 ct2)
               (LE'.evalBinCType m' σ' f' ct1' ct2').
    Proof.
      intros M Σ F FT CT1 CT2.
      unfold LE.evalBinCType, LE'.evalBinCType.
      eapply heq_AExpr_heq_evalAExpr in M.
      inversion M as [? ? B1 B2 | ? ? ? B1 B2];
        rewrite <-B1, <-B2; [constructor |].
      all: repeat constructor.
      all: assumption.
    Qed.

    Lemma evalNExpr_closure_equiv_monotone
          (σn : LE.evalNatContext)
          (σn' : LE'.evalNatContext)
          (σsn : LE.evalNatContext)
          (σsn' : LE'.evalNatContext)
          (n : LE.NExpr)
          (n' : LE'.NExpr)
      :
        LE.evalNatContext_in_range σn σsn ->
        LE'.evalNatContext_in_range σn' σsn' ->
        evalNExpr_closure_equiv (σsn, n) (σsn', n') ->
        evalNExpr_closure_equiv (σn, n) (σn', n').
    Proof.
      intros ΣN ΣN' E.
      unfold evalNExpr_closure_equiv in *.
      intros * ΣR ΣR' Σ N.
      specialize (E σ σ').
      full_autospecialize E;
        try assumption.
      eapply LE.evalNatContext_in_range_trans; eassumption.
      eapply LE'.evalNatContext_in_range_trans; eassumption.
    Qed.

    Lemma AExpr_NatClosures_equiv_monotone
          (σn : LE.evalNatContext)
          (σn' : LE'.evalNatContext)
          (σsn : LE.evalNatContext)
          (σsn' : LE'.evalNatContext)
          (f : LE.AExpr)
          (f' : LE'.AExpr)
      :
        heq_AExpr f f' ->
        LE.evalNatContext_in_range σn σsn ->
        LE'.evalNatContext_in_range σn' σsn' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures σsn f)
          (LE'.evalAExpr_NatClosures σsn' f') ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures σn f)
          (LE'.evalAExpr_NatClosures σn' f').
    Proof.
      intros F Σ Σ' ES.
      induction F;
        cbn in *.
      (* inductive cases *)
      5-10: apply evalNExpr_closure_trace_equiv_app_inv in ES;
        [| eapply evalAExpr_NatClosures_length; eassumption].
      5-10: apply Forall2_app; tauto.
      (* base cases *)
      -
        assumption.
      -
        inv ES.
        constructor.
        eapply evalNExpr_closure_equiv_monotone; eassumption.
        eassumption.
      -
        apply IHF.
        assumption.
      -
        assumption.
    Qed.

    Lemma heq_protect_evalContext
          (σ : LE.evalContext)
          (σ' : evalContext)
          (p : L.PExpr)
          (p' : L'.PExpr)
      :
        heq_PExpr p p' ->
        heq_evalContext σ σ' ->
        heq_evalContext (LE.protect_p σ p) (protect_p σ' p').
    Proof.
      intros P Σ.
      destruct p, p'.
      invc P; invc H1.
      rename v0 into n.
      cbn.
      generalize dependent n.
      induction Σ;
        intros.
      -
        destruct n; constructor.
      -
        destruct n.
        +
          cbn.
          repeat break_let; subst.
          invc H; invc H0.
          constructor.
          constructor.
          reflexivity.
          assumption.
          assumption.
        +
          unfold LE.protect, LE'.protect in *.
          cbn.
          specialize (IHΣ n).
          repeat break_match.
          all: constructor; tauto.
    Qed.

    Lemma heq_evalDSHIMap
          (m : L.memory)
          (m' : L'.memory)
          (n n' : nat)
          (nt : NT.t)
          (nt' : NT'.t)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (x : L.mem_block)
          (x' : L'.mem_block)
          (y : L.mem_block)
          (y' : L'.mem_block)
      :
        heq_memory m m' ->

        (* NOTE: this is equivalent to [heq_NT_nat n n'],
           but we need to bind nt, nt' later *)
        NT.from_nat n = inr nt ->
        NT'.from_nat n' = inr nt' ->
        heq_NType nt nt' ->

        heq_AExpr f f' ->

        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures
             (LE.DSHOtherVar :: LE.DSHIndex nt :: LE.evalNatContext_of_evalContext σ)
             f)
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHIndex nt' :: evalNatContext_of_evalContext σ')
             f') ->
        heq_evalContext σ σ' ->
        heq_mem_block x x' ->
        heq_mem_block y y' ->
        herr_c heq_mem_block
               (LE.evalDSHIMap m n f σ x y)
               (LE'.evalDSHIMap m' n' f' σ' x' y').
    Proof.
      intros M NT NT' NTE F FT Σ X Y.
      assert (N : heq_NT_nat n n').
      {
        constructor.
        destruct (NT.from_nat n), (NT'.from_nat n');
          invc NT; invc NT'.
        constructor.
        eapply heq_NType_proper;
          eassumption.
      }
      copy_apply heq_NT_nat_eq N;
        cbv in H; subst n'.
      revert NT NT' NTE FT Y.
      revert nt nt' y y'.
      induction n;
        cbn; intros.
      -
        constructor.
        assumption.
      -
        remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err str str n n x x'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].
        apply heq_NT_nat_S in N.
        inv N.
        invc H2.
        pose proof
             heq_AExpr_heq_evalIUnCType m m' σ σ' f f' a0 b0 a b
          as EU.

        (* for use in multiple places later *)
        assert (AB : evalNExpr_closure_trace_equiv
                  (LE.evalAExpr_NatClosures
                     (LE.DSHOtherVar :: LE.DSHIndex a0 ::
                                     LE.evalNatContext_of_evalContext σ)
                     f)
                  (evalAExpr_NatClosures
                     (DSHOtherVar :: DSHIndex b0 ::
                                  evalNatContext_of_evalContext σ')
                     f')).
        {
          eapply AExpr_NatClosures_equiv_monotone.
          4: eassumption.
          -
            assumption.
          -
            cbn.
            repeat constructor.
            erewrite !to_nat_of_from_nat.
            3: rewrite H3; reflexivity.
            2: eassumption.
            lia.
            apply LE.evalNatContext_in_range_refl.
          -
            cbn.
            repeat constructor.
            erewrite !to_nat_of_from_nat'.
            3: rewrite H4; reflexivity.
            2: eassumption.
            lia.
            apply LE'.evalNatContext_in_range_refl.
        }
        full_autospecialize EU;
          try assumption.
        invc EU; [constructor |].
        autospecialize IHn; [assumption |].
        specialize (IHn a0 b0).
        eapply IHn;
          try assumption.
        rewrite H3; reflexivity.
        rewrite H4; reflexivity.
        now apply heq_mem_block_mem_add.
    Qed.

    Lemma heq_evalDSHBinOp
          (m : L.memory)
          (m' : L'.memory)
          (n n' off off' : nat)
          (nt : NT.t)
          (nt' : NT'.t)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (x : L.mem_block)
          (x' : L'.mem_block)
          (y : L.mem_block)
          (y' : L'.mem_block)
      :
        heq_memory m m' ->

        (* NOTE: this is equivalent to [heq_NT_nat n n'],
           but we need to bind nt, nt' later *)
        NT.from_nat n = inr nt ->
        NT'.from_nat n' = inr nt' ->
        heq_NType nt nt' ->

        off = off' ->
        heq_AExpr f f' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures
             (LE.DSHOtherVar :: LE.DSHOtherVar :: LE.DSHIndex nt
                             :: LE.evalNatContext_of_evalContext σ)
             f)
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHOtherVar :: DSHIndex nt'
                          :: evalNatContext_of_evalContext σ')
             f') ->
        heq_evalContext σ σ' ->
        heq_mem_block x x' ->
        heq_mem_block y y' ->
        herr_c heq_mem_block
               (LE.evalDSHBinOp m n off f σ x y)
               (LE'.evalDSHBinOp m' n' off' f' σ' x' y').
    Proof.
      intros M NT NT' NTE OFF F FT Σ X Y.
      assert (N : heq_NT_nat n n').
      {
        constructor.
        destruct (NT.from_nat n), (NT'.from_nat n');
          invc NT; invc NT'.
        constructor.
        eapply heq_NType_proper;
          eassumption.
      }
      copy_apply heq_NT_nat_eq N;
        cbv in H; subst n'.
      cbv in OFF; subst off'.

      revert NT NT' NTE FT Y.
      revert nt nt' y y'.
      induction n;
        cbn; intros.
      -
        constructor.
        assumption.
      -
        remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err str str n n x x'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].

        remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err
             str str (n + off) (n + off) x x'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].

        apply heq_NT_nat_S in N.
        inv N; invc H5.

        pose proof
             heq_AExpr_heq_evalIBinCType m m' σ σ' f f' a1 b1 a a0 b b0
          as EU.

        (* for use in multiple places later *)
        assert (AB : evalNExpr_closure_trace_equiv
                       (LE.evalAExpr_NatClosures
                          (LE.DSHOtherVar :: LE.DSHOtherVar :: LE.DSHIndex a1 ::
                                          LE.evalNatContext_of_evalContext σ)
                          f)
                       (evalAExpr_NatClosures
                          (DSHOtherVar :: DSHOtherVar :: DSHIndex b1 ::
                                       evalNatContext_of_evalContext σ')
                          f')).
        {
          eapply AExpr_NatClosures_equiv_monotone.
          4: eassumption.
          -
            assumption.
          -
            cbn.
            repeat constructor.
            erewrite !to_nat_of_from_nat.
            3: rewrite H6; reflexivity.
            2: eassumption.
            lia.
            apply LE.evalNatContext_in_range_refl.
          -
            cbn.
            repeat constructor.
            erewrite !to_nat_of_from_nat'.
            3: rewrite H7; reflexivity.
            2: eassumption.
            lia.
            apply LE'.evalNatContext_in_range_refl.
        }
        full_autospecialize EU;
          try assumption.
        invc EU; [constructor |].
        autospecialize IHn; [assumption |].
        specialize (IHn a1 b1).
        eapply IHn;
          try assumption.
        rewrite H6; reflexivity.
        rewrite H7; reflexivity.
        now apply heq_mem_block_mem_add.
    Qed.

    Lemma heq_evalDSHMap2
          (m : L.memory)
          (m' : L'.memory)
          (n n' : nat)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (x0 x1 : L.mem_block)
          (x0' x1' : L'.mem_block)
          (y : L.mem_block)
          (y' : L'.mem_block)
      :
        heq_memory m m' ->
        heq_NT_nat n n' ->
        heq_AExpr f f' ->
        evalNExpr_closure_trace_equiv
          (LE.evalAExpr_NatClosures
             (LE.DSHOtherVar :: LE.DSHOtherVar
                             :: LE.evalNatContext_of_evalContext σ)
             f)
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHOtherVar
                          :: evalNatContext_of_evalContext σ')
             f') ->
        heq_evalContext σ σ' ->
        heq_mem_block x0 x0' ->
        heq_mem_block x1 x1' ->
        heq_mem_block y y' ->
        herr_c heq_mem_block
               (LE.evalDSHMap2 m n f σ x0 x1 y)
               (LE'.evalDSHMap2 m' n' f' σ' x0' x1' y').
    Proof.
      intros M N F FT Σ X0 X1 Y.
      copy_apply heq_NT_nat_eq N;
        cbv in H; subst n'.

      generalize dependent y'.
      generalize dependent y.
      induction n;
        intros.
      -
        constructor.
        assumption.
      -
        cbn.
        repeat remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err str str1 n n x0 x0'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].

        repeat remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err str str0 n n x1 x1'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].

        pose proof
             heq_AExpr_heq_evalBinCType m m' σ σ' f f' a a0 b b0
          as EU.

        full_autospecialize EU;
          try assumption.
        invc EU; [constructor |].
        autospecialize IHn; [now apply heq_NT_nat_S |].
        eapply IHn;
          try assumption.
        now apply heq_mem_block_mem_add.
    Qed.

    Lemma heq_evalDSHPower
          (m : L.memory)
          (m' : L'.memory)
          (n n' xoff xoff' yoff yoff' : nat)
          (f : L.AExpr)
          (f' : L'.AExpr)
          (σ : LE.evalContext)
          (σ' : evalContext)
          (x : L.mem_block)
          (x' : L'.mem_block)
          (y : L.mem_block)
          (y' : L'.mem_block)
      :
        heq_memory m m' ->
        heq_NT_nat n n' ->
        heq_NT_nat xoff xoff' ->
        heq_NT_nat yoff yoff' ->
        heq_AExpr f f' ->
        evalNExpr_closure_trace_equiv
          ((LE.evalAExpr_NatClosures
              (LE.DSHOtherVar :: LE.DSHOtherVar
                              :: LE.evalNatContext_of_evalContext σ)
              f))
          (evalAExpr_NatClosures
             (DSHOtherVar :: DSHOtherVar
                          :: evalNatContext_of_evalContext σ')
             f') ->
        heq_evalContext σ σ' ->
        heq_mem_block x x' ->
        heq_mem_block y y' ->
        herr_c heq_mem_block
               (LE.evalDSHPower m σ n f x y xoff yoff)
               (LE'.evalDSHPower m' σ' n' f' x' y' xoff' yoff').
    Proof.
      intros M NTE XTE YTE F FT Σ X Y.

      copy_apply heq_NT_nat_eq NTE;
        cbv in H; subst n'.
      copy_apply heq_NT_nat_eq XTE;
        cbv in H; subst xoff'.
      copy_apply heq_NT_nat_eq YTE;
        cbv in H; subst yoff'.

      generalize dependent y'.
      generalize dependent y.

      induction n;
        cbn; intros.
      -
        constructor.
        assumption.
      -
        remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err str str xoff xoff x x'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].

        remember_string.
        pose proof
             heq_mem_block_heq_mem_lookup_err str str yoff yoff y y'
          as ME.
        full_autospecialize ME;
          [reflexivity | assumption |].
        invc ME; [constructor |].

        pose proof
             heq_AExpr_heq_evalBinCType m m' σ σ' f f' a0 a b0 b
          as EU.

        full_autospecialize EU;
          try assumption.
        invc EU; [constructor |].
        eapply IHn.
        now apply heq_NT_nat_S.
        now apply heq_mem_block_mem_add.
    Qed.

    Theorem translation_semantics_correct
          (op : LE.DSHOperator)
          (op' : LE'.DSHOperator)
          (fuel fuel' : nat)
          (σ : LE.evalContext)
          (σ' : LE'.evalContext)
          (imem : L.memory)
          (imem' : L'.memory)
      :
        heq_DSHOperator op op' ->
        heq_evalContext σ σ' ->
        heq_memory imem imem' ->
        hopt (herr evalNExpr_closure_trace_equiv)
             (LE.intervalEvalDSHOperator_σ σ op nil fuel)
             (LE'.intervalEvalDSHOperator_σ σ' op' nil fuel') ->
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
        remember_string.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n1)
               (n':=n1)
          in HEQ_MEMORY';
          [| reflexivity].
        invc HEQ_MEMORY'; [constructor |].

        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        remember_string.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n2)
               (n':=n2)
          in HEQ_MEMORY';
          [| reflexivity].
        invc HEQ_MEMORY'; [constructor |].

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
          [| apply heq_NType_to_nat; assumption].
        inversion H5.
        constructor.
        repeat constructor.
        eapply heq_memory_memory_set;
          [assumption | reflexivity |].
        eapply heq_mem_block_mem_add.
        assumption.
        now apply heq_NType_to_nat.
        assumption.
      - (* IMap *)
        repeat break_match; invc H3; invc H4.
        rename t1 into nt, t0 into nt'.
        rename Heqs0 into NT, Heqs into NT'.
        rename H into HEQN.
        rename H0 into HEQXP, H1 into HEQYP.
        rename H2 into HEQA.

        copy_apply heq_NT_nat_eq HEQN;
          cbv in H; subst n'.
        constructor; cbn.

        rewrite NT, NT'.

        pose proof HEQXP as HEQXP'.
        pose proof HEQYP as HEQYP'.
        eapply heq_PExpr_heq_evalPExpr in HEQXP', HEQYP';
          try eassumption.
        invc HEQXP'; invc HEQYP'.
        all: repeat break_let; subst.
        all: repeat constructor.

        remember_string.
        pose proof heq_assert_nat_neq str str n0 n2 n1 n3 as T.
        full_autospecialize T;
          try (invc H1; invc H4; congruence).
        invc T; [constructor |].

        remember_string.
        pose proof heq_NType_heq_assert_NT_le str str nt nt' t1 t3 as T.
        full_autospecialize T;
          [pose proof heq_NType_from_nat n; inv H8; congruence
          |now inv H4
          |].
        invc T; [constructor |].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n0)
               (n':=n2)
          in HEQ_MEMORY'; [| now invc H1].
        invc HEQ_MEMORY'; [constructor | ].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n1)
               (n':=n3)
          in HEQ_MEMORY'; [| now invc H4].
        invc HEQ_MEMORY'; [constructor |].

        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        eapply heq_evalDSHIMap in HEQ_MEMORY'.
        inversion HEQ_MEMORY' as [? ? I I' | ? ? ? I I'];
          erewrite <-I, <-I'; [constructor |].
        all: try eassumption.
        +
          constructor.
          eapply heq_memory_memory_set;
            [assumption | now invc H4 | assumption].
        + rewrite NT; reflexivity.
        + rewrite NT'; reflexivity.
        + pose proof (heq_NType_from_nat n) as T.
          inv T; try congruence; assumption.
        +
          rewrite LE.evalNatContext_of_protect_evalContext;
            rewrite LE'.evalNatContext_of_protect_evalContext.
          apply evalNExpr_closure_trace_equiv_app_inv in NTR_EQUIV;
            [| eapply evalAExpr_NatClosures_length; eassumption ].
          tauto.
        +
          apply heq_protect_evalContext; assumption.
      - (* BinOp *)
        repeat break_match; invc H3; invc H4.
        rename t1 into nt, t0 into nt'.
        rename Heqs0 into NT, Heqs into NT'.
        rename H into HEQN.
        rename H0 into HEQXP, H1 into HEQYP.
        rename H2 into HEQA.

        copy_apply heq_NT_nat_eq HEQN;
          cbv in H; subst n'.
        constructor; cbn.

        rewrite NT, NT'.

        pose proof HEQXP as HEQXP'.
        pose proof HEQYP as HEQYP'.
        eapply heq_PExpr_heq_evalPExpr in HEQXP', HEQYP';
          try eassumption.
        invc HEQXP'; invc HEQYP'.
        all: repeat break_let; subst.
        all: repeat constructor.

        remember_string.
        pose proof heq_assert_nat_neq str str n0 n2 n1 n3 as T.
        full_autospecialize T;
          try (invc H1; invc H4; congruence).
        invc T; [constructor |].

        remember_string.
        pose proof heq_NType_heq_assert_NT_le str str nt nt' t1 t3 as T.
        full_autospecialize T;
          [pose proof heq_NType_from_nat n; inv H8; congruence
          |now inv H4
          |].
        invc T; [constructor |].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n0)
               (n':=n2)
          in HEQ_MEMORY'; [| now invc H1].
        invc HEQ_MEMORY'; [constructor | ].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n1)
               (n':=n3)
          in HEQ_MEMORY'; [| now invc H4].
        invc HEQ_MEMORY'; [constructor |].

        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        eapply heq_evalDSHBinOp in HEQ_MEMORY'.
        inversion HEQ_MEMORY' as [? ? I I' | ? ? ? I I'];
          erewrite <-I, <-I'; [constructor |].
        all: try eassumption.
        +
          constructor.
          eapply heq_memory_memory_set;
            [assumption | now invc H4 | assumption].
        + rewrite NT; reflexivity.
        + rewrite NT'; reflexivity.
        + pose proof (heq_NType_from_nat n) as T.
          inv T; try congruence; assumption.
        + reflexivity.
        +
          rewrite LE.evalNatContext_of_protect_evalContext;
            rewrite LE'.evalNatContext_of_protect_evalContext.
          apply evalNExpr_closure_trace_equiv_app_inv in NTR_EQUIV;
            [| eapply evalAExpr_NatClosures_length; eassumption ].
          tauto.
        +
          apply heq_protect_evalContext; assumption.
      - (* MemMap2 *)
        repeat break_match; invc H4; invc H5.
        rename t1 into nt, t0 into nt'.
        rename Heqs0 into NT, Heqs into NT'.
        rename H into HEQN.
        rename H0 into HEQXP0, H1 into HEQXP1.
        rename H2 into HEQYP.
        rename H3 into HEQA.

        copy_apply heq_NT_nat_eq HEQN;
          cbv in H; subst n'.
        constructor; cbn.

        rewrite NT, NT'.

        pose proof HEQXP0 as HEQXP0'.
        pose proof HEQXP1 as HEQXP1'.
        pose proof HEQYP as HEQYP'.
        eapply heq_PExpr_heq_evalPExpr in HEQXP0', HEQXP1', HEQYP';
          try eassumption.
        invc HEQXP0'; invc HEQXP1'; invc HEQYP'.
        all: repeat break_let; subst.
        all: repeat constructor.

        remember_string.
        pose proof heq_NType_heq_assert_NT_le str str nt nt' t2 t5 as T.
        full_autospecialize T;
          [pose proof heq_NType_from_nat n; inv H8; congruence
          |now inv H7
          |].
        invc T; [constructor |].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n0)
               (n':=n3)
          in HEQ_MEMORY'; [| now invc H1].
        invc HEQ_MEMORY'; [constructor | ].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n1)
               (n':=n4)
          in HEQ_MEMORY'; [| now invc H4].
        invc HEQ_MEMORY'; [constructor | ].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n2)
               (n':=n5)
          in HEQ_MEMORY'; [| now invc H7].
        invc HEQ_MEMORY'; [constructor |].

        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        eapply heq_evalDSHMap2 in HEQ_MEMORY'.
        inversion HEQ_MEMORY' as [? ? I I' | ? ? ? I I'];
          erewrite <-I, <-I'; [constructor |].
        all: try eassumption.
        +
          constructor.
          eapply heq_memory_memory_set;
            [assumption | now invc H7 | assumption].
        +
          rewrite LE.evalNatContext_of_protect_evalContext;
            rewrite LE'.evalNatContext_of_protect_evalContext.
          apply evalNExpr_closure_trace_equiv_app_inv in NTR_EQUIV;
            [| eapply evalAExpr_NatClosures_length; eassumption ].
          tauto.
        +
          apply heq_protect_evalContext; assumption.
      - (* Power *)
        rename H5 into INI.
        rename H into HEQN.
        rename H0 into HEQ_SRCN, H1 into HEQ_DSTN.
        rename H2 into HEQ_SRCP, H3 into HEQ_DSTP.
        rename H4 into HEQA.
        cbn; constructor.

        pose proof HEQ_SRCP as HEQ_SRCP'.
        pose proof HEQ_DSTP as HEQ_DSTP'.
        eapply heq_PExpr_heq_evalPExpr in HEQ_SRCP', HEQ_DSTP';
          try eassumption.
        invc HEQ_SRCP'; invc HEQ_DSTP'.
        all: repeat break_let; subst.
        all: repeat constructor.

        remember_string.
        pose proof heq_assert_nat_neq str str n0 n2 n1 n3 as T.
        full_autospecialize T;
          try (invc H1; invc H4; congruence).
        invc T; [constructor |].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n0)
               (n':=n2)
          in HEQ_MEMORY'; [| now invc H1].
        invc HEQ_MEMORY'; [constructor | ].

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n1)
               (n':=n3)
          in HEQ_MEMORY'; [| now invc H4].
        invc HEQ_MEMORY'; [constructor |].

        inv NTR_EQUIV; invc H19; invc H21; clear H22.
        cbn in H17, H18, H19.
        autospecialize_closure_equiv H17 σ σ'.
        autospecialize_closure_equiv H18 σ σ'.
        autospecialize_closure_equiv H19 σ σ'.
        inv H17; [constructor |].
        inv H18; [constructor |].
        inv H19; [constructor |].

        remember_string.
        pose proof heq_NType_heq_assert_NT_lt str str a4 b4 t1 t3 as T.
        full_autospecialize T;
          [rewrite <-H23, <-H24 in *; now invc H19
          |now inv H4
          |].
        invc T; [constructor |].

        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        eapply heq_evalDSHPower in HEQ_MEMORY'.
        inversion HEQ_MEMORY' as [? ? I I' | ? ? ? I I'];
          erewrite <-I, <-I'; [constructor |].
        all: try eassumption.
        +
          constructor.
          eapply heq_memory_memory_set;
            [assumption | now invc H4 | assumption].
        +
          (* poor man's proper *)
          clear - H16.
          constructor.
          pose proof (from_nat_of_to_nat a2).
          pose proof (from_nat_of_to_nat' b2).
          destruct NT.from_nat, NT'.from_nat;
            invc H; invc H0; constructor.
          eapply heq_NType_proper; eassumption.
        +
          (* poor man's proper *)
          clear - H22.
          constructor.
          pose proof (from_nat_of_to_nat a3).
          pose proof (from_nat_of_to_nat' b3).
          destruct NT.from_nat, NT'.from_nat;
            invc H; invc H0; constructor.
          eapply heq_NType_proper; eassumption.
        +
          (* poor man's proper *)
          clear - H25.
          constructor.
          pose proof (from_nat_of_to_nat a4).
          pose proof (from_nat_of_to_nat' b4).
          destruct NT.from_nat, NT'.from_nat;
            invc H; invc H0; constructor.
          eapply heq_NType_proper; eassumption.
        +
          rewrite LE.evalNatContext_of_protect_evalContext;
            rewrite LE'.evalNatContext_of_protect_evalContext.
          do 3 (apply evalNExpr_closure_trace_equiv_cons_inv in NTR_EQUIV;
                destruct NTR_EQUIV as [_ NTR_EQUIV]).
          apply evalNExpr_closure_trace_equiv_app_inv in NTR_EQUIV;
            [| eapply evalAExpr_NatClosures_length; eassumption ].
          tauto.
        +
          apply heq_protect_evalContext; assumption.
        +
          apply heq_mem_block_mem_add.
          assumption.
          apply heq_NType_to_nat; assumption.
          assumption.
      - (* MemInit *)
        rename H0 into V.
        rename p into y_p, p' into y_p', H into HEQYP.
        cbn.
        constructor.

        pose proof HEQYP as HEQYP'.
        eapply heq_PExpr_heq_evalPExpr in HEQYP';
          try eassumption.
        invc HEQYP'.
        all: repeat break_let; subst.
        all: repeat constructor.

        remember_string.
        pose proof HEQ_MEMORY as HEQ_MEMORY'.
        apply heq_memory_heq_memory_lookup_err
          with (msg:=str)
               (msg':=str)
               (n:=n)
               (n':=n0)
          in HEQ_MEMORY'; [| now invc H1].
        invc HEQ_MEMORY'; [constructor | ].
        constructor.
        eapply heq_memory_memory_set.
        assumption.
        now inv H1.
        apply heq_mem_block_heq_mem_union;
          [| assumption].
        apply heq_mem_const_block.
        apply heq_NType_to_nat; now invc H1.
        assumption.
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
          assert (HEQ_BΣN0 : evalNExpr_closure_trace_equiv bσn0 bσn0').
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
        enough (hopt_r (herr_c heq_memory) eop eop').
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
        assert (HEQ_ΣN0 : evalNExpr_closure_trace_equiv σn0 σn0').
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
        assert (HEQ_FΣN : evalNExpr_closure_trace_equiv fσn fσn').
        {
          eapply heq_DSHOperator_evalNExpr_closure_trace_equiv_inv.
          3: rewrite TΣN, TΣN'.
          eassumption.
          eapply heq_evalContext_heq_evalNatContext; eassumption.
          now repeat constructor.
        }
        assert (HEQF : hopt_r (herr_c heq_memory)
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
    Qed.

  End Semantic_Translation_Correctness.

  Section Semantic_Translation_Correctness_strict.

    Context `{NHE : NTranslation_heq} `{CHE : CTranslation_heq}.
    Context `{NTP : @NTranslationProps NHE}
            `{NOP : @NOpTranslationProps NHE}
            `{COP : @COpTranslationProps CHE}.

    Lemma heq_NType_NTypeEquiv_compat
          (n1 n2 : NT.t)
          (n1' n2' : NT'.t)
      :
        heq_NType n1 n1' ->
        heq_NType n2 n2' ->
        (n1 = n2 <-> n1' = n2').
    Admitted.

    Lemma heq_NExpr_heq_evalNExpr
          (n : L.NExpr)
          (n' : L'.NExpr)
          (σ : LE.evalContext)
          (σ' : evalContext)
      :
        heq_NExpr n n' ->
        heq_evalContext σ σ' ->
        herr_c heq_NType
               (LE.evalNExpr σ n)
               (LE'.evalNExpr σ' n').
    Proof.
      intros N Σ.
      induction N.
      (* base cases *)
      {
        cbn.
        invc H.
        eapply heq_evalContext_heq_context_lookup with (n:=x') in Σ.
        inv Σ; rewrite <-H, <-H0.
        constructor.
        repeat break_match; invc H1; invc H3.
        all: now constructor.
      }
      {
        now constructor.
      }
      (* inductive cases *)
      all: cbn.
      all: invc IHN1; invc IHN2.
      all: repeat break_if; repeat constructor.
      all: try now apply NOP.
      (* division by zero *)
      all: exfalso.
      all: clear Heqd Heqd0; contradict n.
      all: eapply heq_NType_NTypeEquiv_compat; try eassumption.
    Admitted.

    Lemma evalNExpr_closure_equiv_tauto
          (c : LE.evalNatClosure)
          (c' : LE'.evalNatClosure)
      :
        evalNExpr_closure_equiv c c'.
    Proof.
      unfold evalNExpr_closure_equiv.
      repeat break_let.
      intros.
      now apply heq_NExpr_heq_evalNExpr.
    Qed.
      
    Lemma evalNatClosure_traces_equiv
          (σnc : list LE.evalNatClosure)
          (σnc' : list LE'.evalNatClosure)
      :
        length σnc = length σnc' ->
        evalNExpr_closure_trace_equiv σnc σnc'.
    Proof.
      unfold evalNExpr_closure_trace_equiv.
      revert σnc'.
      induction σnc;
        intros * L.
      -
        destruct σnc';
          invc L.
        constructor.
      -
        destruct σnc';
          invc L.
        constructor.
        apply evalNExpr_closure_equiv_tauto.
        now apply IHσnc.
    Qed.

    (* TODO: move *)
    Fact intervalEvalDSHOperator_fuel_monotone2 :
      forall fuel0 fuel fuel0' fuel' R σn op σnc σn' op' σnc',
        fuel0 <= fuel ->
        fuel0' <= fuel' ->
        hopt (herr R)
             (LE.intervalEvalDSHOperator σn op σnc fuel0)
             (LE'.intervalEvalDSHOperator σn' op' σnc' fuel0') ->
        hopt (herr R)
             (LE.intervalEvalDSHOperator σn op σnc fuel)
             (LE'.intervalEvalDSHOperator σn' op' σnc' fuel').
    Proof.
      intros * F F' OK.
      invc OK; invc H1.
      symmetry in H, H0.
      eapply LE.intervalEvalDSHOperator_fuel_monotone in H;
        [| eassumption].
      eapply LE'.intervalEvalDSHOperator_fuel_monotone in H0;
        [| eassumption].
      rewrite H, H0.
      now repeat constructor.
    Qed.

    Lemma intervalEvalDSHOperator_σ_length
          (op : LE.DSHOperator)
          (op' : LE'.DSHOperator)
          (σ : LE.evalContext)
          (σ' : LE'.evalContext)
        :
          heq_DSHOperator op op' ->
          hopt (herr (fun σnc σnc' => length σnc = length σnc'))
               (LE.intervalEvalDSHOperator_σ σ op nil (LE.estimateFuel op))
               (LE'.intervalEvalDSHOperator_σ σ' op' nil (LE'.estimateFuel op')).
    Proof.
      intros O.
      assert (length (@nil LE.evalNatClosure) = length (@nil LE'.evalNatClosure))
        by reflexivity.
      generalize dependent (@nil LE.evalNatClosure).
      generalize dependent (@nil LE'.evalNatClosure).
      revert σ σ'.
      induction O;
        intros σ σ' σnc' σnc LΣNC.
      -
        repeat constructor.
        assumption.
      -
        repeat constructor.
        cbn.
        now rewrite LΣNC.
      -
        cbn.
        invc H; invc H3.
        repeat constructor.
        rewrite !app_length.
        rewrite LΣNC.
        f_equiv.
        apply evalAExpr_NatClosures_length.
        assumption.
      -
        cbn.
        invc H; invc H3.
        repeat constructor.
        rewrite !app_length.
        rewrite LΣNC.
        f_equiv.
        apply evalAExpr_NatClosures_length.
        assumption.
      -
        cbn.
        invc H; invc H4.
        repeat constructor.
        rewrite !app_length.
        rewrite LΣNC.
        f_equiv.
        apply evalAExpr_NatClosures_length.
        assumption.
      -
        repeat constructor.
        cbn.
        do 3 f_equiv.
        rewrite !app_length.
        rewrite LΣNC.
        f_equiv.
        apply evalAExpr_NatClosures_length.
        assumption.
      -
        copy_apply heq_NT_nat_eq H.
        cbv in H0; subst n'.
        dependent induction n.
        +
          repeat constructor.
          assumption.
        +
          cbn.
          apply heq_NT_nat_S in H.
          inv H; inv H0.
          specialize (IHn body body' H O IHO σ σ').
          eapply intervalEvalDSHOperator_fuel_monotone2 in IHn.
          invc IHn; invc H6.
          rewrite <-H4, <-H5.
          2: {
            cbn.
            enough (1 <= LE.estimateFuel body) by lia.
            induction body; cbv; lia.
          }
          2: {
            cbn.
            enough (1 <= LE'.estimateFuel body') by lia.
            induction body'; cbv; lia.
          }
          specialize (IHO ((LE.DSHnatVal a, false) :: σ)
                          ((LE'.DSHnatVal b, false) :: σ')).
          unfold LE.intervalEvalDSHOperator_σ,
            LE'.intervalEvalDSHOperator_σ in IHO.
          cbn in IHO.
          eapply intervalEvalDSHOperator_fuel_monotone2 in IHO.
          eapply IHO.
          lia.
          lia.
          assumption.
          assumption.
      -
        cbn.
        specialize (IHO ((LE.DSHCTypeVal CT.CTypeZero, false) :: σ)
                        ((LE'.DSHCTypeVal CT'.CTypeZero, false) :: σ')).
        unfold LE.intervalEvalDSHOperator_σ,
          LE'.intervalEvalDSHOperator_σ in IHO.
        cbn in IHO.
        eapply IHO.
        assumption.
      -
        repeat constructor.
        assumption.
      -
        unfold LE.intervalEvalDSHOperator_σ,
          LE'.intervalEvalDSHOperator_σ in *.
        cbn in *.

        specialize (IHO1 σ σ' σnc' σnc LΣNC).
        eapply intervalEvalDSHOperator_fuel_monotone2 in IHO1.
        invc IHO1; invc H1.
        rewrite <-H, <-H0.
        2,3: lia.

        specialize (IHO2 σ σ' b0 a0 H2).
        eapply intervalEvalDSHOperator_fuel_monotone2 in IHO2.
        eapply IHO2.
        lia.
        lia.
    Qed.

    Lemma heq_DSHOperator_closure_trace_equiv
          (op : LE.DSHOperator)
          (op' : LE'.DSHOperator)
          (σ : LE.evalContext)
          (σ' : LE'.evalContext)
      :
        heq_DSHOperator op op' ->
        hopt (herr evalNExpr_closure_trace_equiv)
             (LE.intervalEvalDSHOperator_σ σ op nil (LE.estimateFuel op))
             (LE'.intervalEvalDSHOperator_σ σ' op' nil (LE'.estimateFuel op')).
    Proof.
      intros OP.
      apply intervalEvalDSHOperator_σ_length with (σ:=σ) (σ':=σ') in OP.
      invc OP; invc H1.
      repeat constructor.
      apply evalNatClosure_traces_equiv.
      assumption.
    Qed.

    (* A direct consequence of [translation_semantics_correct]
       and [heq_DSHOperator_closure_trace_equiv] *)
    Corollary translation_semantics_correct_strict
          (op : LE.DSHOperator)
          (op' : LE'.DSHOperator)
          (fuel fuel' : nat)
          (σ : LE.evalContext)
          (σ' : LE'.evalContext)
          (imem : L.memory)
          (imem' : L'.memory)
      :
        heq_DSHOperator op op' ->
        heq_evalContext σ σ' ->
        heq_memory imem imem' ->
        hopt_r (herr_c heq_memory)
               (LE.evalDSHOperator σ op imem (LE.estimateFuel op))
               (LE'.evalDSHOperator σ' op' imem' (LE'.estimateFuel op')).
    Proof.
      intros O Σ M.
      now apply translation_semantics_correct,
        heq_DSHOperator_closure_trace_equiv.
    Qed.
    
  End Semantic_Translation_Correctness_strict.

End MDHCOLTypeTranslator.
