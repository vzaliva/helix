From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.LLVMAst
     Syntax.Traversal
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.CFG
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Semantics.TopLevel
     Handlers.Handlers
     Theory.Refinement
     Theory.DenotationTheory
     Theory.InterpreterCFG.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List.

Require Import Ceres.Ceres.
Import BinInt.
Import ListNotations.
Import ITree.Basics.Basics.Monads.

From Vellvm Require Import Util.
Require Import State.

(* TODOYZ: This is weird, I need to import again this file for the rewriting to work.
   A bit unsure as to why this happen, but somehow some subsequent import breaks it.
 *)
Require Import ITree.Eq.Eq.

Section MemoryModel.

  Lemma get_logical_block_of_add_to_frame :
    forall (m : memory_stack) k x, get_logical_block (add_to_frame m k) x = get_logical_block m x.
  Proof.
    intros. destruct m. cbn. destruct m.
    destruct f; unfold get_logical_block; cbn; reflexivity.
  Qed.

  Lemma get_logical_block_of_add_logical_frame_ineq :
    forall x m k mv, m <> x ->
                get_logical_block (add_logical_block m k mv) x = get_logical_block mv x.
  Proof.
    intros.
    cbn in *.
    unfold get_logical_block, get_logical_block_mem in *.
    unfold add_logical_block. destruct mv. cbn.
    unfold add_logical_block_mem. destruct m0.
    Opaque lookup. Opaque add.
    cbn in *.
    rewrite lookup_add_ineq; auto.
  Qed.

End MemoryModel.

Section ValuePred.

  (* TODOYZ: Double check how useful those are *)
  Definition int64_dvalue_rel (n : Int64.int) (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I64 i => BinInt.Z.eq (Int64.intval n) (unsigned i)
    | _ => False
    end.

  Definition nat_dvalue_rel (n : nat) (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I64 i => Z.eq (Z.of_nat n) (unsigned i)
    | _ => False
    end.

  Definition int64_concrete_uvalue_rel (n : Int64.int) (uv : uvalue) : Prop :=
    match uvalue_to_dvalue uv with
    | inr dv => int64_dvalue_rel n dv
    | _ => False
    end.

  Definition nat_concrete_uvalue_rel (n : nat) (uv : uvalue) : Prop :=
    match uvalue_to_dvalue uv with
    | inr dv => nat_dvalue_rel n dv
    | _ => False
    end.

End ValuePred.

Section TLE_To_Modul.

  Definition opt_first {T: Type} (o1 o2: option T): option T :=
    match o1 with | Some x => Some x | None => o2 end.

  Definition modul_app {T X} (m1 m2: @modul T X): @modul T X :=
    let (name1, target1, layout1, tdefs1, globs1, decls1, defs1) := m1 in
    let (name2, target2, layout2, tdefs2, globs2, decls2, defs2) := m2 in
    {|
      m_name := opt_first name1 name2;
      m_target := opt_first target1 target2;
      m_datalayout := opt_first layout1 layout2;
      m_type_defs := tdefs1 ++ tdefs2;
      m_globals := globs1 ++ globs2;
      m_declarations := decls1 ++ decls2;
      m_definitions := defs1 ++ defs2
    |}.

  Lemma modul_of_toplevel_entities_cons:
    forall {T X} tle tles, 
      @modul_of_toplevel_entities T X (tle :: tles) = modul_app (modul_of_toplevel_entities [tle]) (modul_of_toplevel_entities tles).
  Proof.
    intros.
    unfold modul_of_toplevel_entities; cbn; f_equal;
      try ((break_match_goal; reflexivity) || (rewrite <- !app_nil_end; reflexivity)).
  Qed.

  Lemma modul_of_toplevel_entities_app:
    forall {T X} tle1 tle2, 
    @modul_of_toplevel_entities T X (tle1 ++ tle2) = modul_app (modul_of_toplevel_entities tle1) (modul_of_toplevel_entities tle2).
  Proof.
    induction tle1 as [| tle tle1 IH]; intros; cbn; [reflexivity |].
    rewrite modul_of_toplevel_entities_cons, IH; cbn.
    f_equal;
      try ((break_match_goal; reflexivity) || (rewrite <- !app_nil_end, app_assoc; reflexivity)).
  Qed.

  Infix "@" := (modul_app) (at level 60).

  Open Scope list.
  Lemma m_definitions_app: forall {T X} (p1 p2 : @modul T X),
      m_definitions (p1 @ p2) = m_definitions p1 ++ m_definitions p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_name_app: forall {T X} (p1 p2 : @modul T X),
      m_name (p1 @ p2) = opt_first (m_name p1) (m_name p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_target_app: forall {T X} (p1 p2 : @modul T X),
      m_target (p1 @ p2) = opt_first (m_target p1) (m_target p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_datalayout_app: forall {T X} (p1 p2 : @modul T X),
      m_datalayout (p1 @ p2) = opt_first (m_datalayout p1) (m_datalayout p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_type_defs_app: forall {T X} (p1 p2 : @modul T X),
      m_type_defs (p1 @ p2) = m_type_defs p1 ++ m_type_defs p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_globals_app: forall {T X} (p1 p2 : @modul T X),
      m_globals (p1 @ p2) = m_globals p1 ++ m_globals p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_declarations_app: forall {T X} (p1 p2 : @modul T X),
      m_declarations (p1 @ p2) = m_declarations p1 ++ m_declarations p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma map_option_cons_inv: forall {A B} (f : A -> option B) (a : A) (l : list A) (r : list B),
      map_option f (a :: l) = Some r ->
       exists b r',
        f a = Some b /\
        map_option f l = Some r' /\
        r = b :: r'.
  Proof.      
    intros.
    (* YZ TODO : Test on 8.11 if cbn also behaves annoyingly here *)
    simpl in H; do 2 (break_match_hyp; try inv_option). 
    do 2 eexists; repeat split; auto.
  Qed.

  Lemma map_option_cons: forall {A B} (f : A -> option B) (a : A) (b : B) (l : list A) (r : list B),
        f a = Some b ->
        map_option f l = Some r ->
        map_option f (a :: l) = Some (b :: r).
  Proof.      
    intros * EQ1 EQ2; simpl; rewrite EQ1, EQ2; reflexivity.
  Qed.

  Lemma map_option_app_inv: forall {A B} (f : A -> option B) (l1 l2 : list A) (r : list B),
      map_option f (l1 ++ l2) = Some r ->
      exists r1 r2,
        map_option f l1 = Some r1 /\
        map_option f l2 = Some r2 /\
        r = r1 ++ r2.
  Proof.
    induction l1 as [| x l1 IH]; intros * EQ.
    - do 2 eexists; repeat split; try reflexivity; auto. 
    - generalize EQ; intros EQ'; apply map_option_cons_inv in EQ'; destruct EQ' as (b & ? & EQ1 & EQ2 & ->). 
      apply IH in EQ2; destruct EQ2 as (r1 & r2 & EQ2 & EQ3 & ->).
      exists (b::r1), r2; repeat split; auto. 
      apply map_option_cons; auto.
  Qed.

  Lemma mcfg_of_app_modul: forall {T} (p1 p2 : @modul T _), 
      mcfg_of_modul (p1 @ p2) = mcfg_of_modul p1 @ mcfg_of_modul p2.
  Proof.
    intros; cbn.
    unfold mcfg_of_modul.
    rewrite  m_name_app, m_target_app, m_datalayout_app, m_type_defs_app, m_globals_app, m_declarations_app; f_equal; try reflexivity. 
    rewrite m_definitions_app, map_app; reflexivity.
  Qed.

  (* YZ TODO :  A bit annoying but should not be an issue.
     Actually: requires some assumptions to be able to split the environment in two.
     Some well-formedness/closedness of the respective mcfg under the respective environments.
   *)
  Lemma convert_typ_mcfg_app:
    forall mcfg1 mcfg2 : modul (cfg typ),
      convert_typ (m_type_defs mcfg1 ++ m_type_defs mcfg2) (mcfg1 @ mcfg2) =
      convert_typ (m_type_defs mcfg1) mcfg1 @ convert_typ (m_type_defs mcfg2) mcfg2.
  Proof.
    intros mcfg1 mcfg2.
    remember (m_type_defs mcfg1) as l1; remember (m_type_defs mcfg2) as l2.
    revert l1 Heql1.
    induction l1 as [| τ1 l1 IH]; cbn; intros EQ.
    - rewrite <- !EQ; cbn.
      destruct mcfg1, mcfg2; cbn; subst; cbn in *.
      rewrite <- !EQ; cbn.
      unfold convert_typ, ConvertTyp_mcfg, Traversal.fmap, Traversal.Fmap_mcfg.
      cbn.
      f_equal; try (unfold endo, Endo_option; cbn; repeat flatten_goal; now intuition).
      + unfold Fmap_list'.
  Admitted.

  Lemma convert_types_app_mcfg : forall mcfg1 mcfg2,
      convert_types (modul_app mcfg1 mcfg2) =
                    modul_app (convert_types mcfg1) (convert_types mcfg2).
  Proof.
    unfold convert_types.
    intros.
    rewrite m_type_defs_app,convert_typ_mcfg_app.
    reflexivity.
  Qed.

  Lemma mcfg_of_tle_app : forall x y, convert_types (mcfg_of_tle (x ++ y)) =
                                 modul_app (convert_types (mcfg_of_tle x)) (convert_types (mcfg_of_tle y)).
  Proof.
    intros ? ?.
    unfold mcfg_of_tle.
    rewrite modul_of_toplevel_entities_app.
    rewrite mcfg_of_app_modul.
    rewrite convert_types_app_mcfg.
    reflexivity.
  Qed.

  Lemma mcfg_of_tle_cons : forall x y, convert_types (mcfg_of_tle (x :: y)) =
                                  modul_app (convert_types  (mcfg_of_tle [x])) (convert_types  (mcfg_of_tle y)).
  Proof.
    intros; rewrite list_cons_app; apply mcfg_of_tle_app.
  Qed.

End TLE_To_Modul.

(* Infix "@" := (modul_app) (at level 60). *)

From Vellvm Require Import Utils.AListFacts.

Import Traversal.

(* YZ: Should they be Opaque or simpl never? *)
Global Opaque D.denote_ocfg.
Global Opaque assoc.
Global Opaque D.denote_instr.
Global Opaque D.denote_terminator.
Global Opaque D.denote_phi.
Global Opaque D.denote_code.

Lemma typ_to_dtyp_I : forall s i, typ_to_dtyp s (TYPE_I i) = DTYPE_I i.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma typ_to_dtyp_D : forall s, typ_to_dtyp s TYPE_Double = DTYPE_Double.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma typ_to_dtyp_D_array : forall n s, typ_to_dtyp s (TYPE_Array n TYPE_Double) = DTYPE_Array n DTYPE_Double.
Proof.
  intros.
  rewrite typ_to_dtyp_equation.
  rewrite typ_to_dtyp_D.
  reflexivity.
Qed.

From Paco Require Import paco.
Lemma eutt_mon {E R1 R2} (RR RR' : R1 -> R2 -> Prop)
      (LERR: RR <2= RR') :
  @eutt E R1 R2 RR <2= eutt RR'.
Proof.
  eapply eqit_mon; eauto.
Qed.

From Vellvm Require Import Syntax.Scope.

Lemma blk_id_map_convert_typ : forall env bs,
    map blk_id (convert_typ env bs) = map blk_id bs.
Proof.
  induction bs as [| b bs IH]; cbn; auto.
  f_equal; auto.
Qed.

Lemma wf_ocfg_bid_convert_typ :
  forall env (bs : ocfg typ),
    wf_ocfg_bid bs ->
    wf_ocfg_bid (convert_typ env bs).
Proof.
  induction bs as [| b bs IH]; intros NOREP.
  - cbn; auto.
  - cbn.
    apply Coqlib.list_norepet_cons. 
    + cbn.
      apply wf_ocfg_bid_cons_not_in in NOREP.
     rewrite blk_id_map_convert_typ; auto.
    + eapply IH, wf_ocfg_bid_cons; eauto. 
Qed.

(* Enforcing these definitions to be unfolded systematically by [cbn] *)
Arguments endo /.
Arguments Endo_id /.
Arguments Endo_ident /.

Lemma free_in_convert_typ :
  forall env (bs : list (LLVMAst.block typ)) id,
  free_in_cfg bs id ->
  free_in_cfg (convert_typ env bs) id.
Proof.
  induction bs as [| b bs IH]; intros * FR.
  - red; cbn; auto.
  - cbn.
    intros abs.
    eapply FR.
    destruct (Eqv.eqv_dec_p (blk_id b) id).
    left; rewrite e; auto.
    destruct abs.
    + cbn in H.
      exfalso; apply n; rewrite H; reflexivity.
    + apply IH in H; intuition.
      eapply free_in_cfg_cons; eauto.
Qed.

Arguments find_block : simpl never.

From Vellvm Require Import Theory.SymbolicInterpreter.

Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.

Import D. 
Module VIR_denotation_Notations.
  (* Notation "'ℐ' '(' t ')' g l m" := (interp_cfg_to_L3 _ t g l m) (only printing, at level 10). *)
  Notation "'global.' g 'local.' l 'memory.' m 'ℐ' t" :=
    (interp_cfg_to_L3 _ t g l m)
      (only printing, at level 10,
       format "'global.'  g '//' 'local.'  l '//' 'memory.'  m '//' 'ℐ'  t").
  
  Notation "⟦ c ⟧" := (denote_code c) (only printing, at level 10).
  Notation "⟦ i ⟧" := (denote_instr i) (only printing, at level 10).
  Notation "⟦ t ⟧" := (denote_terminator t) (only printing, at level 10).
  Notation "⟦ e ⟧" := (denote_exp None e) (only printing, at level 10).
  Notation "⟦ τ e ⟧" := (denote_exp (Some τ) e) (only printing, at level 10).
  Notation "x" := (translate exp_E_to_instr_E x) (only printing, at level 10).

  Notation "'λ' a b c d ',' k" := (fun '(a,(b,(c,d))) => k) (only printing, at level 0, format "'λ'  a  b  c  d ',' '[' '//' k ']'").

End VIR_denotation_Notations.

Import ITreeNotations.

From Vellvm Require Import InstrLemmas ExpLemmas.

Ltac vred_r :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred_C3;
        subst X; subst R.

Ltac vred_l :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_right_named X; vred_C3;
        subst X; subst R.

Ltac vstep := vstep3.

Ltac tred := autorewrite with itree.

Arguments denote_exp : simpl never.
(* TODO: fmap (mk_block _ _ _ _ _) does not reduce, although we would like.
   However if I do the following to force the unfolding, then fmap always
   unfolds even in many other cases where we don't want it to do so.
   Solution?
 *)
(* Arguments fmap /. *)
(* Arguments Fmap_block /. *)
Arguments denote_phis : simpl never.
Arguments denote_code : simpl never.
Arguments denote_terminator : simpl never.
Arguments denote_block : simpl never.

Lemma Name_inj : forall s1 s2,
    Name s1 = Name s2 ->
    s1 = s2.
Proof.
  intros * EQ; inv EQ; auto.
Qed.

Lemma write_different_blocks :
  forall m m2 p p' v v2 dv2 τ τ',
    write m p v = inr m2 ->
    read m p' τ = inr v2 ->
    fst p <> fst p' ->
    uvalue_to_dvalue v2 = inr dv2 ->
    dvalue_has_dtyp dv2 τ ->
    dvalue_has_dtyp v τ' ->
    read m2 p' τ = inr v2.
Proof.
  intros m m2 p p' v v2 dv2 τ τ' WRITE READ NEQ UVDV TYP1 TYP2.
  erewrite write_untouched; eauto.
  unfold no_overlap_dtyp.
  unfold no_overlap.
  left. auto.
Qed.

Lemma read_in_mem_block_type :
  forall bytes a τ v,
    read_in_mem_block bytes a τ = v ->
    uvalue_has_dtyp v τ.
Proof.
Admitted.

Lemma read_type :
  forall m p τ v,
    read m p τ = inr v ->
    uvalue_has_dtyp v τ.
Proof.
  intros m p τ v READ.
  unfold read in *.
  break_match; inversion READ.
  clear H0.
  break_match; subst.
  inversion READ.
  eapply read_in_mem_block_type; eauto.
Qed.

Infix "⊍" := Coqlib.list_disjoint (at level 60).

Lemma Forall_disjoint :
  forall {A} (l1 l2 : list A) (P1 P2 : A -> Prop),
    Forall P1 l1 ->
    Forall P2 l2 ->
    (forall x, P1 x -> ~(P2 x)) ->
    l1 ⊍ l2.
Proof.
  induction l1;
    intros l2 P1 P2 L1 L2 P1NP2.
  - intros ? ? CONTRA. inversion CONTRA.
  - apply Coqlib.list_disjoint_cons_l.
    + eapply IHl1; eauto using Forall_inv_tail.
    + apply Forall_inv in L1.
      apply P1NP2 in L1.
      intros IN.
      eapply Forall_forall in L2; eauto.
Qed.

Lemma inputs_convert_typ : forall σ bks,
    inputs (convert_typ σ bks) = inputs bks.
Proof.
  induction bks as [| bk bks IH]; cbn; auto.
  f_equal; auto.
Qed.
