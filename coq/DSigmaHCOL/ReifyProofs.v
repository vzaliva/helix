Require Import Omega.

Require Import Helix.HCOL.CarrierType.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

(* When proving concrete functions we need to use some implementation defs from this packages *)
Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.VecUtil.

Require Import MathClasses.misc.util.
Require Import MathClasses.interfaces.canonical_names.

Require Import Helix.Util.OptionSetoid.
Require Import Helix.Tactics.HelixTactics.

Open Scope list_scope.

(* Shows relations of cells before ([b]) and after ([a]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [d] *)
Inductive MemOpDelta (b a d: option CarrierA) : Prop :=
| MemPreserved: is_None d -> b = a -> MemOpDelta b a d (* preserving memory state *)
| MemExpected: is_Some d -> a = d -> MemOpDelta b a d (* expected results *).

(* Shows relations of memory blocks before ([mb]) and after ([ma]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [md] *)
Definition SHCOL_DSHCOL_mem_block_equiv (mb ma md: mem_block) : Prop :=
  forall i,
    MemOpDelta
      (mem_lookup i mb)
      (mem_lookup i ma)
      (mem_lookup i md).

Require Import CoLoR.Util.Relation.RelUtil.

(* option predicate. None is not allowed
TODO: move
*)
Section opt_p.

  Variables (A : Type) (P : A -> Prop).

  Inductive opt_p : (option A) -> Prop :=
  | opt_p_intro : forall x, P x -> opt_p (Some x).

End opt_p.
Arguments opt_p {A} P.

(* Extension to [option _] of a heterogenous relation on [A] [B]
TODO: move
*)
Section hopt.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Reflexive on [None]. *)
  Inductive hopt_r : (option A) -> (option B) -> Prop :=
  | hopt_r_None : hopt_r None None
  | hopt_r_Some : forall a b, R a b -> hopt_r (Some a) (Some b).

  (** Non-Reflexive on [None]. *)
  Inductive hopt : (option A) -> (option B) -> Prop :=
  | hopt_Some : forall a b, R a b -> hopt (Some a) (Some b).

  (** implication-like. *)
  Inductive hopt_i : (option A) -> (option B) -> Prop :=
  | hopt_i_None_None : hopt_i None None
  | hopt_i_None_Some : forall a, hopt_i None (Some a)
  | hopt_i_Some : forall a b, R a b -> hopt_i (Some a) (Some b).

End hopt.
Arguments hopt {A B} R.
Arguments hopt_r {A B} R.
Arguments hopt_i {A B} R.


(* Given MSHCOL and DSHCOL operators are quivalent, if wrt [x_i] and
  input memory block addres and [y_i] as output.

  It is assumed that we know what memory blocks are used as input
  [x_i] and output [y_i], of the operator. They both must exists (be
  allocated) prior to execution.

  We do not require input block to be structurally correct, because
  [mem_op] will just return an error in this case.

  Note: DSCHOL operators are implemented in more permissive manner and
  not necesseraly return error on invalid input.  *)
Class MSH_DSH_compat
      {i o: nat}
      (mop: @MSHOperator i o)
      (dop: DSHOperator)
      (x_i y_i: mem_block_id)
  := {

      mfacts
      :
        MSHOperator_Facts mop;

      eval_equiv
      :
        forall (σ: evalContext) (m: memory) (mx mb: mem_block),
          (memory_lookup m x_i ≡ Some mx) (* input exists *) ->
          (memory_lookup m y_i ≡ Some mb) (* output before *) ->

          (hopt_i (fun md (* memory diff *) m' (* memory state after execution *) =>
                     opt_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md
                           ) (memory_lookup m' y_i)
                  ) (mem_op mop mx) (evalDSHOperator σ dop m (estimateFuel dop)));

      eval_equiv':
        forall (σ: evalContext) (m: memory) (mx mb: mem_block),
          (memory_lookup m x_i ≡ Some mx) (* input exists *) ->
          (memory_lookup m y_i ≡ Some mb) (* output before *) ->

          match mem_op mop mx, evalDSHOperator σ dop m (estimateFuel dop) with
          | Some md, (* memory diff *) Some m' (* memory state after execution *) =>
            match memory_lookup m' y_i with
            | Some ma => SHCOL_DSHCOL_mem_block_equiv mb ma md
            | None => False (* out memory block dissapeared *)
            end
          | None, _ => True (* assume they are equal on *invalid* inputs [see note above] *)
          | _, _ => False
          end
    }.

Inductive context_pos_typecheck: evalContext -> var_id -> DSHType -> Prop :=
| context0_tc {v: DSHVal} {t: DSHType}: DSHValType v t -> context_pos_typecheck [v] 0 t
| contextS_tc {v: DSHVal} {t: DSHType} (n:nat) (cs:evalContext):
    context_pos_typecheck cs n t ->
    DSHValType v t -> context_pos_typecheck (v::cs) (S n) t.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive NExpr_typecheck: NExpr -> evalContext -> Prop :=
| NVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHnat ->  NExpr_typecheck (NVar n) σ
| NConst_tc (σ: evalContext) {a}: NExpr_typecheck (NConst a) σ
| NDiv_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NDiv a b) σ
| NMod_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMod a b) σ
| NPlus_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NPlus a b) σ
| NMinus_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMinus a b) σ
| NMult_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMult a b) σ
| NMin_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMin a b) σ
| NMax_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMax a b) σ.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive MExpr_typecheck: MExpr -> evalContext -> Prop :=
| MVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHMemBlock -> MExpr_typecheck (MVar n) σ
| MConst_tc (σ: evalContext) {a}: MExpr_typecheck (MConst a) σ.

(* Check if [AExpr] is properly typed in given evaluation context *)
Inductive AExpr_typecheck: AExpr -> evalContext -> Prop
  :=
  | AVar_tc (σ: evalContext) (n:var_id):
      context_pos_typecheck σ n DSHCarrierA ->  AExpr_typecheck (AVar n) σ
  | AConst_tc (σ: evalContext) {a}: AExpr_typecheck (AConst a) σ
  | ANth_tc (σ: evalContext) (me:MExpr) (ne:NExpr) :
      MExpr_typecheck me σ ->
      NExpr_typecheck ne σ ->
      AExpr_typecheck (ANth me ne) σ
  | AAbs_tc (σ: evalContext) (e:AExpr):
      AExpr_typecheck e σ -> AExpr_typecheck (AAbs e) σ
  | APlus_tc  (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (APlus  a b) σ
  | AMinus_tc (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMinus a b) σ
  | AMult_tc  (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMult  a b) σ
  | AMin_tc   (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMin   a b) σ
  | AMax_tc   (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMax   a b) σ
  | AZless_tc (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AZless a b) σ.

Class MSH_DSH_BinCarrierA_compat
      {o: nat}
      (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
      (df : DSHIBinCarrierA) :=
  {
    ibin_equiv:
      forall σ nc a b,
        AExpr_typecheck df (DSHCarrierAVal b :: DSHCarrierAVal a :: DSHnatVal (proj1_sig nc) :: σ) ->
        evalIBinCarrierA σ df (proj1_sig nc) a b = Some (f nc a b)
  }.

(* From dynwin example *)
Global Instance Abs_MSH_DSH_BinCarrierA_compat
  :
    MSH_DSH_BinCarrierA_compat
      (λ i (a b : CarrierA),
       IgnoreIndex abs i
                   (HCOL.Fin1SwapIndex2 (n:=2)
                                        jf
                                        (IgnoreIndex2 sub) i a b))

      (AAbs (AMinus (AVar 1) (AVar 0))).
Proof.
  intros jf.
  split.
  intros σ nc a b H.
  unfold evalIBinCarrierA.
  f_equiv.
Qed.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Lemma evalDSHBinOp_mem_lookup_mx
      {o : nat}
      {df : DSHIBinCarrierA}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (E: evalDSHBinOp o o df σ mx mb ≡ Some ma)
      (k: nat)
      (kc:k<o+o):
  ∃ a : CarrierA, mem_lookup k mx ≡ Some a.
Proof.
Admitted.

Lemma evalDSHBinOp_nth
      {o : nat}
      {df : DSHIBinCarrierA}
      {σ : evalContext}
      {mx mb ma : mem_block}
      {k: nat}
      {kc:k<o+o}
      {a b : CarrierA}:
  (mem_lookup k mx ≡ Some a) ->
  (mem_lookup (k + o)%nat mx ≡ Some b) ->
  (evalDSHBinOp o o df σ mx mb ≡ Some ma) ->
  (mem_lookup k ma = evalIBinCarrierA σ df k a b).
Proof.
Admitted.

Global Instance BinOp_MSH_DSH_compat
       {o: nat}
       (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
       `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
       (x_i y_i : mem_block_id)
       (df : DSHIBinCarrierA)
       `{MSH_DSH_BinCarrierA_compat _ f df}
  :
    @MSH_DSH_compat _ _ (MSHBinOp f) (DSHBinOp o x_i y_i df) x_i y_i.
Proof.
  split.
  -
    typeclasses eauto.
  -
    intros σ m mx mb MX MB.
    simpl.
    destruct (mem_op_of_hop (HCOL.HBinOp f) mx) as [md|] eqn:MD.
    +
      repeat break_match; try some_none.
      *
        constructor.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_eq_o by reflexivity.
        constructor.
        clear Heqo0 Heqo1 m x_i y_i.
        rename Heqo2 into ME.
        some_inv.
        some_inv.
        subst m1.
        subst m0.
        rename m2 into ma.
        clear pF.
        intros k.

        unfold mem_op_of_hop in MD.
        break_match_hyp; try some_none.
        inversion_clear MD. clear md.
        rename t into vx.

        unfold avector_to_mem_block.

        avector_to_mem_block_to_spec md HD OD.
        destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
        --
          (* k<o, which is normal *)
          clear OD.
          simpl in *.
          rewrite HD with (ip:=kc).
          clear HD md.
          apply MemExpected.
          ++
            unfold is_Some.
            tauto.
          ++
            inversion_clear H as [F].
            specialize (F σ (FinNat.mkFinNat kc)).

            assert (k < o + o)%nat as kc1 by omega.
            assert (k + o < o + o)%nat as kc2 by omega.
            rewrite HBinOp_nth with (jc1:=kc1) (jc2:=kc2).

            pose proof (evalDSHBinOp_mem_lookup_mx ME k kc1) as [a A].
            pose proof (evalDSHBinOp_mem_lookup_mx ME (k+o) kc2) as [b B].

            rewrite (evalDSHBinOp_nth A B ME (kc:=kc1)).
            simpl in F.
            rewrite F.

            assert(MVA: mem_lookup k mx ≡ Some (Vnth vx kc1)). admit.
            assert(MVB: mem_lookup (k+o) mx ≡ Some (Vnth vx kc2)). admit.

            repeat f_equiv.
            apply Some_inj_eq; rewrite <- A; apply MVA.
            apply Some_inj_eq; rewrite <- B; apply MVB.

            (* HERE: typecheck should go into assumption, but in value-less form
               IDEA: it may follow from ME?
             *)
            admit.
        --
          simpl in *.
          rewrite OD by assumption.
          apply MemPreserved.
          ++
            unfold is_None.
            tauto.
          ++
            clear OD HD md t Heqo3 mx.
            admit.
      *
        (* mem_op succeeded with [Some md] while evaluation of DHS failed *)
        exfalso.
        clear m Heqo0 Heqo1.
        repeat some_inv.
        subst m1. subst m0.
        rename Heqo2 into E.
        rename MD into M.

        unfold mem_op_of_hop, HCOL.HBinOp, HCOLImpl.BinOp, Basics.compose in M.
        repeat break_match_hyp; try some_none.
        some_inv.
        rename H1 into M.
        (* env! *)
        admit.
    +
      repeat break_match; try some_none.
      *
        constructor.
      *
        constructor.
Qed.



  (*
  Instance SHCompose_SHCOL_DSHCOL
        {i1 o2 o3: nat}
        {svalue: CarrierA}
        {fm}
        {op1: @SHOperator fm o2 o3 svalue}
        {op2: @SHOperator fm i1 o2 svalue}
        {compat: Included _ (in_index_set fm op1) (out_index_set fm op2)}
        `{facts1 : !SHOperator_Facts fm op1}
        `{facts2 : !SHOperator_Facts fm op2}
        `{Meq1: !@SHOperator_Mem fm o2 o3 svalue op1 facts1}
        `{Meq2: !@SHOperator_Mem fm i1 o2 svalue op2 facts2}
        {σ: evalContext}
        {d1 d2: DSHOperator}
        {m: memory}
        {t_i x_i y_i: mem_block_id}
    :
      (@SHCOL_DSHCOL_equiv _ _ _ _ op1 facts1 Meq1 d1 σ (* TODO: add t_i to m *) m t_i y_i) ->
      (@SHCOL_DSHCOL_equiv _ _ _ _ op2 facts2 Meq2 d2 σ (* TODO: add t_i to m *) m x_i t_i) ->

      @SHCOL_DSHCOL_equiv i1 o3 svalue _ (SHCompose fm op1 op2)
                          (SHCompose_Facts fm svalue op1 op2 compat)
                          (SHCompose_Mem fm op1 op2 compat )
                          (DSHSeq (DSHAlloc o2 t_i) (DSHSeq d1 d2)) σ m x_i y_i.
  Proof.
    intros E1 E2.
    unfold SHCompose.
    constructor.
    destruct E1 as [E1].
    destruct E2 as [E2].
    unfold mem_op in *.
    unfold SHCompose_Mem, option_compose.
    destruct Meq1, Meq2.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    simpl in *.
    repeat break_match; intros; subst; auto.
  Admitted.

  (* High-level equivalence *)
  Instance dynwin_SHCOL_DSHCOL
           (a: vector CarrierA 3):
    @SHCOL_DSHCOL_equiv _ _ _ _ (dynwin_SHCOL1 a) _
                        (DynWinSigmaHCOL1_Mem a)
                        dynwin_DSHCOL1
                        [DSHvecVal a]
                        (* assuming reification uses [x_i=0] and [y_i=1] *)
                        (NM.add 1 mem_empty
                                (NM.add 0 mem_empty (NM.empty mem_block)))
                        0 1.
  Proof.
    unfold dynwin_DSHCOL1, dynwin_SHCOL1.
    unfold DynWinSigmaHCOL1_Mem, DynWinSigmaHCOL1_Facts.

    (* Normalize by unfolding [@zero] instances: *)
    unfold zero in *.
    (* Normalize dimensionality in DHSCOL. Due to refication,
       for example [o2:=1+1] in SHCOL is replaced with [2] in DHSCOL: *)
    (* simpl in *. *)


    Typeclasses eauto := 1.
    unfold In.
    eapply SHCompose_SHCOL_DSHCOL.
    eapply SafeCast_SHCOL_DSHCOL.


    match goal with
    | [|-  SHCOL_DSHCOL_equiv
            (facts:=?facts)
            (SHCompose ?fm ?op1 ?op2 (o2:=?o2))
            (DSHSeq (DSHAlloc ?o2 ?t_i) (DSHSeq ?d1 ?d2))
            ?σ ?m ?x_i ?y_i] =>
      unshelve eapply (SHCompose_SHCOL_DSHCOL 0 1
                                     (fm:=fm)
                                     (op1:=op1)
                                     (op2:=op2)
                                     (m:=m)
                                     (d1:=d1)
                                     (d2:=d2)
                                     (t_i:=t_i)
                                     (σ:=σ)
                                     (facts:=facts)

             )

    end.


    apply SafeCast_SHCOL_DSHCOL.
  Qed.



     "@SHCOL_DSHCOL_equiv (1 + (2 + 2)) 1 0 Monoid_RthetaFlags
    (?op1 ⊚ ?op2) ?facts
    (@SHCompose_Mem Monoid_RthetaFlags 0 (1 + (2 + 2)) ?o2 1
       ?op1 ?op2 ?compat ?facts1 ?Meq1 ?facts2 ?Meq2 ?facts)
    (DSHAlloc ?o2 ?t_i; ?d1; ?d2) [@DSHvecVal 3 a] ?m 0 1" with

    eapply (SHCompose_SHCOL_DSHCOL 0 1
                                   (i1:=1 + (2 + 2))
                                   (o3:=1)
                                   (svalue:=zero)
                                   (fm:=Monoid_RthetaFlags)
                                   (σ:=[DSHvecVal a])
           ).
    apply SafeCast_SHCOL_DSHCOL.
  Qed.

   *)

(* Heterogenous relation of semantic equivalence of structurally correct SHCOL and DSHCOL operators *)

(*
Open Scope list_scope.
Definition SHCOL_DSHCOL_equiv {i o:nat} {svalue:CarrierA} {fm}
           (σ: evalContext)
           (s: @SHOperator fm i o svalue)
           `{facts: !SHOperator_Facts fm s}
           `{SHM: !SHOperator_Mem  s}
           (d: DSHOperator) (x_i y_i: nat): Prop
  := forall (Γ: evalContext) (x:svector fm i),

    let Γ := σ ++ in

    (List.nth_error Γ' x_i = Some (svector_to_mem_block x)) ->
    match evalDSHOperator Γ' d (estimateFuel d), mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end.


    let xm := svector_to_mem_block x in (* input as mem_block *)
    let ym := mem_empty in (* placeholder for output *)
    let x_i := List.length (σ ++ Γ) in
    let y_i := x_i + 1 in
    let Γ := σ ++ Γ ++ [DSHmemVal xm ; DSHmemVal ym]  in (* add them to context *)
    let fuel := estimateFuel d in
    match evalDSHOperator Γ d fuel, mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end
    | None, None  => True
    | _, _ => False
    end.
*)

(*
Theorem SHCompose_DSHCompose
        {i1 o2 o3} {svalue} {fm}
        (σ: evalContext)
        (f: @SHOperator fm o2 o3 svalue)
        (g: @SHOperator fm i1 o2 svalue)
        (df: DSHOperator o2 o3)
        (dg: DSHOperator i1 o2)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    SHCOL_DSHCOL_equiv σ
                       (SHCompose fm f g)
                       (DSHCompose df dg).
Proof.
  intros Ef Eg.
  intros Γ x.
  simpl.
  break_match.
  -
    unfold compose.
    specialize (Eg Γ x).
    specialize (Ef Γ (op fm g x)).
    rewrite Ef.
    apply evalDSHOperator_arg_proper.
    apply Some_inj_equiv.
    rewrite <- Heqo.
    apply Eg.
  -
    specialize (Eg Γ x).
    rewrite Heqo in Eg.
    some_none.
Qed.

Theorem SHCOL_DSHCOL_equiv_SafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaSafeFlags i o svalue)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.SafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rvector2rsvector _ x)).
  rewrite densify_rvector2rsvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHCOL_DSHCOL_equiv_UnSafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaFlags i o svalue)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.UnSafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rsvector2rvector _ x)).
  rewrite densify_rsvector2rvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHBinOp_DSHBinOp
        {o: nat}
        {svalue: CarrierA}
        {fm}
        (σ: evalContext)
        (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (df: DSHIBinCarrierA)
  :
    (forall (Γ: evalContext) j a b, Some (f j a b) = evalIBinCarrierA
                                                       (σ ++ Γ)
                                                       df (proj1_sig j) a b) ->
    @SHCOL_DSHCOL_equiv (o+o) o svalue fm σ
                        (@SHBinOp fm svalue o f pF)
                        (DSHBinOp df).
Proof.
  intros H.
  intros Γ x.
  simpl.
  unfold evalDSHBinOp.
  unfold SHBinOp'.
  break_let.
  rename t into x0, t0 into x1.

  unfold densify.
  rewrite Vmap_Vbuild.

  break_let.
  unfold vector2pair in *.

  apply Vbreak_arg_app in Heqp.
  subst x.
  rewrite Vmap_app in Heqp0.
  apply Vbreak_arg_app in Heqp0.
  apply Vapp_eq in Heqp0.
  destruct Heqp0 as [H0 H1].
  subst t. subst t0.
  setoid_rewrite Vnth_map.

  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  rewrite Vmap_Vbuild with (fm:=Some).

  vec_index_equiv j jc.
  rewrite 2!Vbuild_nth.
  rewrite evalWriter_Rtheta_liftM2.
  symmetry.
  specialize (H Γ (mkFinNat jc)).
  rewrite H.
  reflexivity.
Qed.

Theorem HTSUMUnion_DSHHTSUMUnion
        {i o: nat}
        {svalue: CarrierA}
        {fm}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (ddot: DSHBinCarrierA)
        (σ: evalContext)
        (f g: @SHOperator fm i o svalue)
        (df dg: DSHOperator i o)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    (forall (Γ:evalContext) a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@HTSUMUnion fm i o svalue dot dot_mor scompat f g)
                       (DSHHTSUMUnion ddot df dg).
Proof.
  intros Ef Eg Edot.
  intros Γ x.
  specialize (Ef Γ).
  specialize (Eg Γ).
  specialize (Edot Γ).
  simpl.
  repeat break_match.
  -
    rewrite Vmap2_as_Vbuild.
    symmetry.
    apply vsequence_Vbuild_equiv_Some.
    unfold HTSUMUnion', Vec2Union.
    unfold densify.
    rewrite Vmap_map.
    rewrite Vmap2_as_Vbuild.
    rewrite Vmap_Vbuild.
    unfold Union.

    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    rewrite evalWriter_Rtheta_liftM2.
    symmetry.

    specialize (Ef x). specialize (Eg x).
    rewrite Heqo0 in Ef; clear Heqo0; some_inv.
    rewrite Heqo1 in Eg; clear Heqo1; some_inv.
    rewrite Edot; clear Edot.
    apply evalBinCarrierA_proper; try reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Ef.
    rewrite <- Ef.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Eg.
    rewrite <- Eg.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.
  -
    specialize (Eg x).
    rewrite Heqo1 in Eg.
    some_none.
  -
    specialize (Ef x).
    rewrite Heqo0 in Ef.
    some_none.
Qed.

Theorem eUnion_DSHeUnion
        {fm}
        (σ: evalContext)
        {o b:nat}
        (bc: b < o)
        (svalue: CarrierA)
        (db: NExpr)
  :
    (forall Γ, Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ (svalue:=svalue)
                       (eUnion fm bc)
                       (DSHeUnion db svalue).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
  break_match; some_inv; repeat nat_equiv_to_eq; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.

    apply castWriter_equiv.
    unfold eUnion'.
    repeat rewrite Vbuild_nth.
    break_if.
    +
      subst.
      rewrite Vhead_Vmap.
      apply castWriter_mkValue_evalWriter.
    +
      apply castWriter_mkStruct.
  -
    destruct n0; auto.
Qed.

 *)

               (*
Definition SHOperatorFamily_DSHCOL_equiv
           {i o n:nat}
           {svalue: CarrierA}
           {fm}
           (Γ: evalContext)
           (op_family: @SHOperatorFamily fm i o n svalue)
           {op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc))}
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
           (d: DSHOperator) : Prop :=
  forall (j:nat) (jc:j<n), SHCOL_DSHCOL_equiv (DSHnatVal j :: Γ)
                                       (op_family (mkFinNat jc))
                                       d.
                *)

(*
Section Expr_NVar_subst_S.

  Local Ltac twoarg := simpl;
                       repeat break_match; auto; try some_none;
                       f_equiv;
                       repeat some_inv;
                       crush.

  Fact NExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : NExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalNexp Γs exp =
    evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      break_if.
      +
        (* accessing variable at pos *)
        subst n.
        simpl.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity; try some_none.
        *
          some_inv.
          inversion H0. inversion H1. subst.
          f_equiv.
          repeat nat_equiv_to_eq; subst.
          apply peano_naturals.S_nat_plus_1.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

  Fact VExpr_NVar_subst_S
       {d: nat}
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : VExpr d)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalVexp Γs exp =
    evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n0 pos).
      +
        (* accessing variable at pos *)
        subst n0.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H0.
        * inversion H0.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n0 n1).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        repeat break_match; try reflexivity.
        subst.
        symmetry.
        compute.
        f_equiv.
        apply H3.
    -
      reflexivity.
  Qed.

  Fact AExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : AExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalAexp Γs exp =
    evalAexp Γ (AExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n pos).
      +
        (* accessing variable at pos *)
        subst n.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0. subst. inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    -
      rename n0 into ne.
      simpl.
      assert(V:evalVexp Γs v = evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) v)) by (apply VExpr_NVar_subst_S with (j0:=j); auto).
      unfold listsDiffByOneElement, isNth in *.
      assert (C: evalNexp Γs ne = evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) ne)) by (apply NExpr_NVar_subst_S with (j:=j); auto).
      twoarg.
      repeat nat_equiv_to_eq.
      subst.
      replace l0 with l by apply proof_irrelevance; clear l0.
      apply Vnth_proper, V.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

End Expr_NVar_subst_S.

Fact evalDiamond_NVar_subst_S:
  ∀ (i o n : nat) (dot : DSHBinCarrierA) (initial : CarrierA)
    (dop_family : DSHOperator i o) (y : vector CarrierA i)
    (j : nat), (∀ (y0 : vector CarrierA i) (pos : nat) (Γ Γs : evalContext),
                   listsDiffByOneElement Γ Γs pos
                   → isNth Γ pos (DSHnatVal j)
                   → isNth Γs pos (DSHnatVal (S j))
                   → evalDSHOperator Γs dop_family y0 =
                     evalDSHOperator Γ
                                     (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1))
                                                            dop_family) y0)
               → ∀ (pos : nat) (Γ Γs : evalContext), listsDiffByOneElement Γ Γs pos
                                                     → isNth Γ pos (DSHnatVal j)
                                                     → isNth Γs pos (DSHnatVal (S j))
                                                     →
                                                     evalDiamond
                                                       (evalBinCarrierA Γs dot)
                                                       initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γs)
                                                             dop_family y)) =
                                                     evalDiamond
                                                       (evalBinCarrierA Γ
                                                                        (AExpr_natvar_subst
                                                                           (pos + 2)
                                                                           (NPlus
                                                                              (if
                                                                                  PeanoNat.Nat.eq_dec pos pos
                                                                                then NVar (pos + 2)
                                                                                else NVar pos)
                                                                              (NConst 1)) dot)) initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γ)
                                                             (DSHOperator_NVar_subt
                                                                (S pos)
                                                                (NPlus
                                                                   (if
                                                                       PeanoNat.Nat.eq_dec pos pos
                                                                     then NVar (S pos)
                                                                     else NVar pos)
                                                                   (NConst 1)) dop_family) y)).
Proof.
  intros i o n dot initial dop_family y j IHdop_family pos Γ Γs L L0 L1.


  dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

  replace (pos+2)%nat with (S (S pos)).
  2:{
    rewrite <- 2!plus_n_Sm.
    rewrite PeanoNat.Nat.add_0_r.
    reflexivity.
  }

  assert(D: evalBinCarrierA Γs dot =
            evalBinCarrierA Γ
                            (AExpr_natvar_subst (S (S pos))
                                                (NPlus (NVar (S (S pos)))
                                                       (NConst 1)) dot)).
  {
    unfold evalBinCarrierA.
    intros a a' Ea b b' Eb.
    apply AExpr_NVar_subst_S with (j:=j).
    apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
    apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
    apply L.
    -- apply L0.
    -- apply L1.
  }

  induction n.
  + reflexivity.
  +
    unfold evalDiamond in *.
    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.
    apply optDot_proper.
    *
      apply D.
    *
      eapply Vfold_left_rev_proper.
      --
        apply optDot_proper.
        unfold evalBinCarrierA.
        intros a a' Ea b b' Eb.

        apply AExpr_NVar_subst_S with (j:=j).
        ++
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
          apply L.
        ++ apply L0.
        ++ apply L1.
      --
        reflexivity.
      --
        vec_index_equiv j jc.
        rewrite 2!Vbuild_nth.
        apply IHdop_family.
        apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
        apply L.
        apply L0.
        apply L1.
    *
      apply IHdop_family.
      apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
      apply L.
      apply L0.
      apply L1.
Qed.

Fact DSHOperator_NVar_subst_S
     {i o : nat}
     (Γ Γs : evalContext)
     (dop_family : DSHOperator i o)
     (pos:nat)
     (y : vector CarrierA i)
     (j : nat):
  listsDiffByOneElement Γ Γs pos ->
  isNth Γ pos (DSHnatVal j) ->
  isNth Γs pos (DSHnatVal (S j)) ->
  evalDSHOperator Γs dop_family y =
  evalDSHOperator Γ
                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family) y.
Proof.
  revert Γ Γs.
  revert pos.
  induction dop_family; intros pos Γ Γs L L0 L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    reflexivity.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    replace l0 with l by apply proof_irrelevance.
    reflexivity.
  -
    simpl.
    unfold evalDSHPointwise, evalIUnCarrierA.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros t tc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    unfold evalDSHBinOp, evalIBinCarrierA.
    break_let.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros m mc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+3)%nat with (S (S (S pos))).
    2:{
      rewrite <- 3!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos n j) as Hn.
    specialize (Hn L L0 L1).

    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      destruct a ; destruct b
    end; try some_none; try reflexivity.


    some_inv.
    nat_equiv_to_eq.
    subst n0.
    generalize (Vhead y); intros y'; clear y; rename y' into y.

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b)
    end.
    {
      induction n1.
      * reflexivity.
      *
        rewrite 2!evalDSHInductor_Sn.
        Opaque evalDSHInductor. simpl.
        repeat break_match; try reflexivity.
        unfold evalBinCarrierA.
        apply AExpr_NVar_subst_S with (j:=j).
        Transparent evalDSHInductor.
        --
          some_inv.
          apply listsDiffByOneElement_Sn; try reflexivity.
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply IHn1).
          apply L.
        -- apply L0.
        -- apply L1.
        -- some_none.
        -- some_none.
    }

    repeat break_match; try some_none; try reflexivity.
    f_equiv.
    f_equiv.
    some_inv.
    apply C.
  -
    simpl.
    apply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    eapply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b) by (apply IHdop_family2; auto)
    end.
    repeat break_match; try reflexivity; try some_none.
    some_inv.
    rewrite <- C.
    eapply IHdop_family1; auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C0: a = b) by (apply IHdop_family1; auto)
    end.

    assert(C1: evalDSHOperator Γs dop_family2 y = evalDSHOperator Γ
                                                                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family2) y) by (apply IHdop_family2; auto).

    repeat break_match; try reflexivity; try some_none; try contradiction.
    repeat some_inv.
    rewrite C0, C1.
    apply vsequence_option_proper.
    rewrite 2!Vmap2_as_Vbuild.
    apply Vbuild_proper.
    intros m mc.
    unfold evalBinCarrierA.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    --
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    -- apply L0.
    -- apply L1.
Qed.

Theorem IReduction_DSHIReduction
        {i o n: nat}
        {svalue: CarrierA}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n svalue)
        (ddot: DSHBinCarrierA)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    (forall Γ a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@IReduction svalue i o n dot pdot scompat op_family)
                       (@DSHIReduction i o n ddot svalue dop_family).
Proof.
  intros Hdot Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaSafeFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn pdot Hdot ddot x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaSafeFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaSafeFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaSafeFlags)) x))
      with
        (Some
           (densify Monoid_RthetaSafeFlags
                    (op Monoid_RthetaSafeFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    setoid_rewrite <- Hdot.
    clear ddot Hdot Γ σ.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply pdot.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

Theorem SHPointwise_DSHPointwise
        {fm}
        {svalue: CarrierA}
        {n: nat}
        (f: FinNat n -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (df: DSHIUnCarrierA)
        (σ: evalContext)
  :
    (forall Γ j a, Some (f j a) = evalIUnCarrierA (σ++Γ) df (proj1_sig j) a) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHPointwise fm svalue  n f pF)
                       (DSHPointwise df).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  unfold evalDSHPointwise.
  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  unfold densify.
  rewrite Vmap_map.
  simpl.
  unfold SHPointwise'.
  rewrite Vmap_Vbuild.
  apply Vbuild_proper.
  intros j jc.
  rewrite Vnth_map.
  rewrite evalWriter_Rtheta_liftM.
  specialize (H (mkFinNat jc)).
  rewrite <- H.
  reflexivity.
Qed.

Lemma evalDSHInductor_not_None
      (n : nat)
      (initial : CarrierA)
      (df : DSHBinCarrierA)
      (σ Γ : evalContext)
      (Edot: forall a b : CarrierA, is_Some (evalBinCarrierA (σ ++ Γ) df a b)) :
  forall x : CarrierA, is_Some (evalDSHInductor (σ ++ Γ) n df initial x).
Proof.
  intros x.
  induction n.
  -
    crush.
  -
    simpl.
    break_match; crush.
Qed.

Theorem SHInductor_DSHInductor
        {fm}
        {svalue: CarrierA}
        (n:nat)
        (f: CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (initial: CarrierA)
        (dn:NExpr)
        (df: DSHBinCarrierA)
        (σ: evalContext)
  :
    (forall Γ, Some n = evalNexp (σ++Γ) dn) ->
    (forall  Γ a b, Some (f a b) = evalBinCarrierA (σ++Γ) df a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHInductor fm svalue n f pF initial)
                       (DSHInductor dn df initial).
Proof.
  intros E Edot.
  intros Γ x.
  specialize (E Γ).
  specialize (Edot Γ).
  simpl evalDSHOperator.
  break_match; try some_none.
  apply Some_inj_equiv in E.
  unfold equiv, peano_naturals.nat_equiv in E.
  subst n0.

  simpl op.
  unfold SHInductor', Lst, Vconst, densify.
  rewrite Vmap_cons.
  rewrite evalWriter_Rtheta_liftM.
  simpl.
  dep_destruct x.
  simpl.
  clear x0 x.
  generalize (WriterMonadNoT.evalWriter h). intros x. clear h.

  break_match.
  -
    f_equiv.
    apply Vcons_proper; try reflexivity.
    clear dn Heqo.
    dependent induction n.
    +
      crush.
    +
      simpl.
      specialize (IHn f pF initial df σ Γ Edot).
      simpl in Heqo0.
      break_match.
      *
        rewrite IHn with (x:=x) (c:=c0).
        specialize (Edot c0 x).
        rewrite Heqo0 in Edot.
        some_inv; auto.
        auto.
      *
        some_none.
  -
    contradict Heqo0.
    apply is_Some_ne_None.
    apply evalDSHInductor_not_None.
    intros a b.
    specialize (Edot a b).
    symmetry in Edot.
    apply equiv_Some_is_Some in Edot.
    apply Edot.
Qed.

Theorem eT_DSHeT
        {fm}
        {svalue: CarrierA}
        {i b:nat}
        (bc: b < i)
        (db: NExpr)
        (σ: evalContext)
  :
    (forall (Γ:evalContext), Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ
                       (@eT fm svalue i b bc)
                       (@DSHeT i (db:NExpr)).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
  break_match; some_inv; unfold equiv, peano_naturals.nat_equiv in H; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.
    dep_destruct jc;try inversion x0.
    rewrite Vnth_cons.
    break_match. inversion l0.
    apply castWriter_equiv.
    simpl.
    rewrite Vnth_map.
    replace l with bc by apply proof_irrelevance.
    apply castWriter_mkValue_evalWriter.
  -
    destruct n0; auto.
Qed.

Theorem ISumUnion_DSHISumUnion
        {i o n: nat}
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n zero)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@ISumUnion i o n op_family)
                       (@DSHIUnion i o n (APlus (AVar 1) (AVar 0)) 0 dop_family).
Proof.
  (* significant code duplication with `IReduction_DSHIReduction` *)
  intros Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaFlags)) x))
      with
        (Some
           (densify Monoid_RthetaFlags
                    (op Monoid_RthetaFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    assert(Hdot: forall Γ a b, Some (CarrierAplus a b) = evalBinCarrierA (σ++Γ) (APlus (AVar 1) (AVar 0))  a b) by reflexivity.

    setoid_rewrite <- Hdot.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply CarrierAPlus_proper.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

(* Attemts to solve evaluation lemmas on DSHCOL Aexpr *)
Ltac solve_evalAexp :=
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ H: FinNat _ |- _ ] => destruct H
         | [ |- evalAexp _ _ = Some _] =>
           unfold Fin1SwapIndex, const, mult_by_nth; simpl;
           try (repeat break_match; try some_none; try congruence)
         | [H: Some ?A ≡ Some ?b |- _ ] => inversion H; clear H
         | [H: Some ?A = Some ?b |- _ ] => apply Some_inj_equiv in H
         | [ |- ?a _ = ?a _ ] => f_equiv
         | [ |- Vnth ?a _ ≡ Vnth ?a _] => try apply Vnth_eq
         | [ |- _ ] => auto
         end.

(* Solves obligations generated by `reifySHCOL` *)
Ltac solve_reifySHCOL_obligations E :=
  intros ;
  unfold E ;
  match goal with
  | [ |- SHCOL_DSHCOL_equiv _ _ ?d] => unfold d
  end ;
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ |- SHCOL_DSHCOL_equiv _ (SHCompose _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_SafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (UnSafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_UnSafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (SHBinOp _ _) (DSHBinOp _) ] => apply SHBinOp_DSHBinOp
         | [ |- SHCOL_DSHCOL_equiv _ (HTSUMUnion _ _ _ _) (DSHHTSUMUnion _ _ _) ] => apply HTSUMUnion_DSHHTSUMUnion
         | [ |- SHCOL_DSHCOL_equiv _ (eUnion _ _) (DSHeUnion _ _)] => apply eUnion_DSHeUnion
         | [  |- SHCOL_DSHCOL_equiv _ (IReduction _ _) (DSHIReduction _ _ _ _)] => apply IReduction_DSHIReduction
         | [ |- SHOperatorFamily_DSHCOL_equiv _ _ _ ] => unfold SHOperatorFamily_DSHCOL_equiv
         | [ |- SHCOL_DSHCOL_equiv _ (SHFamilyOperatorCompose _ _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SHPointwise _ _) (DSHPointwise _) ] =>  apply SHPointwise_DSHPointwise
         | [ |- SHCOL_DSHCOL_equiv _ (SHInductor _ _ _ _) (DSHInductor _ _ _)] => apply SHInductor_DSHInductor
         | [ |- SHCOL_DSHCOL_equiv _ (eT _ _) (DSHeT _)] => apply eT_DSHeT
         | [ |- SHCOL_DSHCOL_equiv _(ISumUnion _) (DSHIUnion _ _ _ _) ] => apply ISumUnion_DSHISumUnion
         | [ |- Some _ = evalIUnCarrierA _ _ _ _ ] => unfold evalIUnCarrierA; symmetry; solve_evalAexp
         | [ |- _ ] => try reflexivity
         end.
*)
