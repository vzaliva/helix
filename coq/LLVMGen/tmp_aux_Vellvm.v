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

  (* Definition get_logical_block (mem: memory) (ptr: Addr.addr): option logical_block := *)
  (*   let '(b,a) := ptr in *)
  (*   get_logical_block_mem b mem. *)

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

Infix "@" := (modul_app) (at level 60).

(** Facts about [alist] proved in our compiler example for itrees. Should still go to ExtLib **)

From ExtLib Require Import
     Core.RelDec
     Data.Map.FMapAList.
Section alistFacts.

  (* Generic facts about alists. To eventually move to ExtLib. *)

  Arguments alist_find {_ _ _ _}.

  Definition alist_In {K R RD V} k m v := @alist_find K R RD V k m = Some v.

  Arguments alist_add {_ _ _ _}.
  Arguments alist_find {_ _ _ _}.
  Arguments alist_remove {_ _ _ _}. 

  Context {K V: Type}.
  Context {RR : @RelDec K (@eq K)}.
  Context {RRC : @RelDec_Correct K (@eq K) RR}.
  
  Lemma In_add_eq:
    forall k v (m: alist K V),
      alist_In k (alist_add k v m) v.
  Proof.
    intros; unfold alist_add, alist_In; simpl; flatten_goal; [reflexivity | rewrite <- neg_rel_dec_correct in Heq; tauto]. 
  Qed.

  (* A removed key is not contained in the resulting map *)
  Lemma not_In_remove:
    forall (m : alist K V) (k : K) (v: V),
      ~ alist_In k (alist_remove k m) v.
  Proof.
    induction m as [| [k1 v1] m IH]; intros.
    - simpl; intros abs; inv abs. 
    - simpl; flatten_goal.
      + unfold alist_In; simpl.
        rewrite Bool.negb_true_iff in Heq; rewrite Heq.
        intros abs; eapply IH; eassumption.
      + rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
        intros abs; eapply IH; eauto. 
  Qed.

  (* Removing a key does not alter other keys *)
  Lemma In_In_remove_ineq:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_remove k' m) v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' ineq IN; [inversion IN |].
    simpl.
    flatten_goal.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_true_iff, <- neg_rel_dec_correct in Heq.
      flatten_goal; auto.
    - unfold alist_In in *; simpl in *.
      rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
      flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto | eapply IH; eauto].
  Qed.       

  Lemma In_remove_In_ineq:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      alist_In k (alist_remove k' m) v ->
      alist_In k m v.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k ?v ?k' IN; [inversion IN |].
    simpl in IN; flatten_hyp IN.
    - unfold alist_In in *; simpl in *.
      flatten_all; auto.
      eapply IH; eauto.
    -rewrite Bool.negb_false_iff, rel_dec_correct in Heq; subst.
     unfold alist_In; simpl. 
     flatten_goal; [rewrite rel_dec_correct in Heq; subst |].
     exfalso; eapply not_In_remove; eauto.
     eapply IH; eauto.
  Qed.       

  Lemma In_remove_In_ineq_iff:
    forall (m : alist K V) (k : K) (v : V) (k' : K),
      k <> k' ->
      alist_In k (alist_remove k' m) v <->
      alist_In k m v.
  Proof.
    intros; split; eauto using In_In_remove_ineq, In_remove_In_ineq.
  Qed.       

  (* Adding a value to a key does not alter other keys *)
  Lemma In_In_add_ineq:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k m v ->
      alist_In k (alist_add k' v' m) v.
  Proof.
    intros.
    unfold alist_In; simpl; flatten_goal; [rewrite rel_dec_correct in Heq; subst; tauto |].
    apply In_In_remove_ineq; auto.
  Qed.

  Lemma In_add_In_ineq:
    forall k v k' v' (m: alist K V),
      k <> k' ->
      alist_In k (alist_add k' v' m) v ->
      alist_In k m v. 
  Proof.
    intros k v k' v' m ineq IN.
    unfold alist_In in IN; simpl in IN; flatten_hyp IN; [rewrite rel_dec_correct in Heq; subst; tauto |].
    eapply In_remove_In_ineq; eauto.
  Qed.

  Lemma In_add_ineq_iff: 
    forall m (v v' : V) (k k' : K),
      k <> k' ->
      alist_In k m v <-> alist_In k (alist_add k' v' m) v.
  Proof.
    intros; split; eauto using In_In_add_ineq, In_add_In_ineq.
  Qed.

  (* alist_find fails iff no value is associated to the key in the map *)
  Lemma alist_find_None:
    forall k (m: alist K V),
      (forall v, ~ In (k,v) m) <-> alist_find k m = None.
  Proof.
    induction m as [| [k1 v1] m IH]; [simpl; easy |].
    simpl; split; intros H. 
    - flatten_goal; [rewrite rel_dec_correct in Heq; subst; exfalso | rewrite <- neg_rel_dec_correct in Heq].
      apply (H v1); left; reflexivity.
      apply IH; intros v abs; apply (H v); right; assumption.
    - intros v; flatten_hyp H; [inv H | rewrite <- IH in H].
      intros [EQ | abs]; [inv EQ; rewrite <- neg_rel_dec_correct in Heq; tauto | apply (H v); assumption]. 
  Qed.

  Lemma alist_In_add_eq : forall m (k:K) (v n:V), alist_In k (alist_add k n m) v -> n = v.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - unfold alist_add in H.
      unfold alist_In in H. simpl in H.
      destruct (k ?[ eq ] k); inversion H; auto.
    - unfold alist_add in H.
      unfold alist_In in H.
      simpl in H.
      destruct (k ?[ eq ] k). inversion H; auto.
      pose proof (@not_In_remove ((k1,v1)::m)).
      unfold alist_In in H0. simpl in H0.
      apply H0 in H.
      contradiction.
  Qed.

  Lemma In__alist_In :
    forall {R : K -> K -> Prop} {RD : @RelDec K (@Logic.eq K)} {RDC : RelDec_Correct RD} (k : K) (v : V) l,
      In (k,v) l ->
      exists v', alist_In k l v'.
  Proof.
    intros R RD RDC k v l IN.
    induction l; inversion IN.
    - exists v. subst. unfold alist_In.
      cbn.
      assert (k ?[ Logic.eq ] k = true) as Hk.
      eapply rel_dec_correct; auto.
      rewrite Hk.
      reflexivity.
    - destruct a. inversion IN.
      + injection H0; intros; subst.
        exists v. unfold alist_In.
        cbn.
        assert (k ?[ Logic.eq ] k = true) as Hk.
        eapply rel_dec_correct; auto.
        rewrite Hk.
        reflexivity.
      + unfold alist_In.
        cbn.
        destruct (k ?[ Logic.eq ] k0) eqn:Hkk0.
        * exists v0; auto.
        * auto.
  Qed.

  Lemma alist_find_remove_none:
    forall (m : list (K*V)) (k1 k2 : K), k2 <> k1 -> alist_find k1 (alist_remove k2 m) = None -> alist_find k1 m = None.
  Proof.
    induction m as [| [? ?] m IH]; intros ?k1 ?k2 ineq HF; simpl in *.
    - reflexivity.
    - destruct (rel_dec_p k1 k).
      + subst. eapply rel_dec_neq_false in ineq; eauto. rewrite ineq in HF. simpl in HF.
        assert (k = k) by reflexivity.
        apply rel_dec_correct in H. rewrite H in HF. inversion HF.
      + destruct (rel_dec_p k2 k); simpl in *.
        apply rel_dec_correct in e. rewrite e in HF. simpl in HF.
        eapply rel_dec_neq_false in n; eauto. rewrite n. eapply IH. apply ineq. assumption.
        eapply rel_dec_neq_false in n0; eauto. rewrite n0 in HF. simpl in HF.
        eapply rel_dec_neq_false in n; eauto. rewrite n in *. eapply IH. apply ineq. assumption.
  Qed.
    
  Lemma alist_find_add_none:
    forall m (k r :K) (v:V), 
    alist_find k (alist_add r v m) = None ->
    alist_find k m = None.
  Proof.
    destruct m as [| [k1 v1]]; intros.
    - reflexivity.
    - simpl in *.
      remember (k ?[ eq ] r) as x.
      destruct x.  inversion H.
      remember (r ?[ eq] k1) as y.
      destruct y. simpl in *. symmetry in Heqy. rewrite rel_dec_correct in Heqy. subst.
      rewrite <- Heqx.
      apply (alist_find_remove_none _ k k1); auto.
      rewrite rel_dec_sym in Heqx; eauto.
      apply neg_rel_dec_correct. symmetry in Heqx. assumption.
      simpl in H.
      destruct (k ?[ eq ] k1); auto.
      apply (alist_find_remove_none _ k r); auto.
      rewrite rel_dec_sym in Heqx; eauto.
      apply neg_rel_dec_correct. symmetry in Heqx. assumption.
  Qed.      

  Lemma alist_find_neq : forall m (k r:K) (v:V), k <> r -> alist_find k (alist_add r v m) = alist_find k m.
  Proof.
    intros.
    remember (alist_find k (alist_add r v m)) as x.
    destruct x.
    - symmetry in Heqx. apply In_add_In_ineq in Heqx; auto.
    - symmetry in Heqx. symmetry. eapply alist_find_add_none. apply Heqx.
  Qed.
  
  Definition alist_fresh (k : K) (m : alist K V) := alist_find k m = None.

  Lemma add_fresh_lu : forall m (k1 k2 : K) (v1 v2 : V),
      alist_fresh k2 m ->
      alist_In k1 m v1 ->
      alist_In k1 (alist_add k2 v2 m) v1.
  Proof.
    intros; apply In_add_ineq_iff; auto.
    unfold alist_fresh, alist_In in *; intros ->.
    rewrite H in H0; inv H0.
  Qed.

  Lemma alist_fresh_nil : forall k,
      alist_fresh k [].
  Proof.
    intros; reflexivity.
  Qed.

  Lemma alist_find_cons_neq
        (k k0 : K)
        (v0 : V)
        (xs: alist K V)
    :
      (k <> k0) ->
      alist_find k ((k0,v0)::xs) = alist_find k xs.
  Proof.
    intros H.
    cbn.
    destruct (rel_dec k k0) eqn:E.
    -
      exfalso.
      rewrite rel_dec_correct in E.
      congruence.
    -
      reflexivity.
  Qed.

  Lemma alist_find_cons_eq
        (k k0 : K)
        (v0 : V)
        (xs: alist K V)
    :
      (k = k0) ->
      alist_find k ((k0,v0)::xs) = Some v0.
  Proof.
    intros H.
    cbn.
    destruct (rel_dec k k0) eqn:E.
    -
      reflexivity.
    -
      exfalso.
      apply rel_dec_correct in H.
      congruence.
  Qed.

  Definition alist_extend (l1 l2 : alist K V) : Prop :=
    forall id v, alist_In id l1 v -> exists v', alist_In id l2 v'.

  Global Instance alist_extend_Reflexive : Reflexive alist_extend.
  Proof.
    unfold Reflexive.
    intros x.
    unfold alist_extend.
    intros id v H.
    exists v.
    auto.
  Qed.

  Global Instance alist_extend_Transitive : Transitive alist_extend.
  Proof.
    unfold Transitive.
    intros x.
    unfold alist_extend.
    intros y z Hy Hz id v IN.
    apply Hy in IN as (v' & IN).
    apply Hz in IN as (v'' & IN).
    exists v''; auto.
  Qed.

  Lemma alist_extend_add :
    forall l k v,
      alist_extend l (alist_add k v l).
  Proof.
    intros l k v.
    unfold alist_extend.
    unfold alist_In.
    intros id v0 H.
    destruct (rel_dec_p k id).
    - exists v. subst; apply In_add_eq.
    - exists v0. apply In_In_add_ineq; eauto.
  Qed.

End alistFacts.
Arguments alist_find {_ _ _ _}.
Arguments alist_add {_ _ _ _}.
Arguments alist_find {_ _ _ _}.
Arguments alist_remove {_ _ _ _}.
Arguments alist_fresh {_ _ _}.

Lemma Forall2_Nth_left : forall {A B:Type} n l1 l2 R (a:A),
    Nth l1 n a ->
    Forall2 R l1 l2 ->
    exists (b:B), (Nth l2 n b) /\ R a b.
Proof.
  induction n as [| n IH]; cbn; intros.
  destruct l1; inv H0; inv_option.
  eexists; eauto.
  destruct l1; inv H0; try inv_option.
  edestruct IH; eauto.
Qed.

Lemma Forall2_Nth_right : forall {A B:Type} n l1 l2 R (b:B),
    Nth l2 n b ->
    Forall2 R l1 l2 ->
    exists (a:A), (Nth l1 n a) /\ R a b.
Proof.
  induction n as [| n IH]; cbn; intros.
  destruct l1; inv H0; inv_option.
  eexists; eauto.
  destruct l1; inv H0; try inv_option.
  edestruct IH; eauto.
Qed.

Lemma Forall2_Nth : forall {A B:Type} n l1 l2 R (a:A) (b : B),
    Nth l1 n a ->
    Nth l2 n b ->
    Forall2 R l1 l2 ->
    R a b.
Proof.
  induction n as [| n IH]; cbn; intros.
  destruct l1; inv H1; repeat inv_option; auto.
  destruct l1; inv H1; repeat inv_option; auto.
  eapply IH; eauto.
Qed.

(* TODO YZ : Move to itrees *)
(* Simple specialization of [eqit_Ret] to [eutt] so that users of the library do not need to know about [eqit] *)
(* TODO move to Vellvm/Tactics *)
Ltac ret_bind_l_left v :=
  match goal with
    |- eutt _ ?t _ =>
    rewrite <- (bind_ret_l v (fun _ => t))
  end.

(* TODO MOVE *)
Lemma convert_typ_app : forall (a b : code typ) env, (convert_typ env (a ++ b) = convert_typ env a ++ convert_typ env b)%list.
Proof.
  induction a as [| [] a IH]; cbn; intros; auto.
  rewrite IH; reflexivity.
Qed.

(* TODO YZ : move to Vellvm *)
Ltac simpl_match_hyp h :=
  match type of h with
    context[match ?x with | _ => _ end] =>
    match goal with
    | EQ: x = _ |- _ => rewrite EQ in h
    | EQ: _ = x |- _ => rewrite <- EQ in h
    end
  end.
Tactic Notation "simpl_match" "in" hyp(h) := simpl_match_hyp h.

Ltac destruct_unit :=
  match goal with
  | x : unit |- _ => destruct x
  end.

(* YZ TODO : Move to Vellvm? *)
Section WithDec.

  Context {K V : Type}.
  Context {RD:RelDec (@eq K)} {RDC:RelDec_Correct RD}.

  Notation "m '@' x" := (alist_find x m).
  Definition sub_alist (ρ1 ρ2 : alist K V): Prop :=
    forall (id : K) (v : V), alist_In id ρ1 v -> alist_In id ρ2 v.
  Notation "m '⊑' m'" := (sub_alist m m') (at level 45).

  Global Instance sub_alist_refl : Reflexive sub_alist.
  Proof.
    repeat intro; auto.
  Qed.

  Global Instance sub_alist_trans : Transitive sub_alist.
  Proof.
    repeat intro; auto.
  Qed.

  Lemma sub_alist_add :
    forall k v (m : alist K V),
      alist_fresh k m ->
      m ⊑ (alist_add k v m).
  Proof.
    repeat intro.
    unfold alist_In, alist_fresh in *.
    destruct (rel_dec_p k id).
    subst; rewrite H in H0; inversion H0.
    apply In_In_add_ineq; auto.
  Qed.

  Lemma lookup_alist_add_eq :
    forall k v (m : alist K V),
      Maps.lookup k (alist_add k v m) = Some v.
  Proof.
    intros; cbn.
    rewrite eq_dec_eq; reflexivity.
  Qed.

  Lemma lookup_alist_add_ineq :
    forall k k' v (m : alist K V),
      k <> k' ->
      Maps.lookup k (alist_add k' v m) = Maps.lookup k m.
  Proof.
    cbn; intros.
    rewrite eq_dec_neq; auto.
    rewrite remove_neq_alist; auto.
    typeclasses eauto.
  Qed.

  Lemma alist_find_eq_dec : 
    forall {RDV:RelDec (@Logic.eq V)} {RDCV:RelDec_Correct RDV}
                               k (m1 m2 : alist K V),
    {m2 @ k = m1 @ k} + {m2 @ k <> m1 @ k}.
  Proof.
    intros.
    destruct (m2 @ k) eqn:EQ2, (m1 @ k) eqn:EQ1.
    - destruct (rel_dec v v0) eqn:H.
      rewrite rel_dec_correct in H; subst; auto. 
      rewrite <- neg_rel_dec_correct in H; right; intros abs; apply H; inv abs; auto.
    - right; intros abs; inv abs.
    - right; intros abs; inv abs.
    - left; auto.
  Qed.

  Lemma alist_find_add_eq : 
    forall {K V : Type} {RD:RelDec (@Logic.eq K)} {RDC:RelDec_Correct RD}
      k v (m : alist K V),
      (alist_add k v m) @ k = Some v.
  Proof.
    intros.
    cbn. rewrite eq_dec_eq; reflexivity.
  Qed.

  Lemma alist_In_dec :
    forall {RDV:RelDec (@Logic.eq V)} {RDCV:RelDec_Correct RDV}
      (id : K) (l : alist K V) (v : V),
      {alist_In id l v} + {~(alist_In id l v)}.
  Proof.
    intros.
    destruct (l @ id) eqn:EQ.
    - destruct (rel_dec v v0) eqn:H.
      rewrite rel_dec_correct in H; subst; auto. 
      rewrite <- neg_rel_dec_correct in H.
      right; intros abs; red in abs; rewrite EQ in abs; inv abs; auto.
    - right; intros abs; red in abs; rewrite EQ in abs; inv abs. 
  Qed.

End WithDec.

Notation "m '@' x" := (alist_find x m).
Notation "m '⊑' m'" := (sub_alist m m') (at level 45).

Global Instance eq_dec_dvalue: RelDec (@Logic.eq uvalue).
Admitted.
Global Instance eq_dec_uvalue_correct: @RelDec_Correct uvalue (@Logic.eq uvalue) _.
Admitted.

Lemma alist_find_eq_dec_local_env : 
  forall k (m1 m2 : local_env),
    {m2 @ k = m1 @ k} + {m2 @ k <> m1 @ k}.
Proof.
  intros; eapply alist_find_eq_dec.
Qed.

Global Instance ConvertTyp_list {A} `{Traversal.Fmap A}: ConvertTyp (fun T => list (A T)) :=
  fun env => Traversal.fmap (typ_to_dtyp env).

From Vellvm Require Import Traversal.

Lemma fmap_list_app: forall U V H H' c1 c2 f,
    @fmap code (@Fmap_code H H') U V f (c1 ++ c2) =
          fmap f c1  ++ fmap f c2.
Proof.
  induction c1 as [| [] c1 IH]; cbn; intros; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

Ltac focus_single_step_v :=
  match goal with
    |- eutt _ _ (ITree.bind _ ?x) => remember x
  end.

Ltac focus_single_step_h :=
  match goal with
    |- eutt _ (ITree.bind _ ?x) _ => remember x
  end.

Ltac focus_single_step :=
  match goal with
    |- eutt _ (ITree.bind _ ?x) (ITree.bind _ ?y) => remember x; remember y
  end.

(* YZ: Should they be Opaque or simpl never? *)
Global Opaque D.denote_bks.
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

Ltac inv_eqs :=
  repeat 
    match goal with
    | h : ?x = ?x |- _ => clear h
    | h : _ = ?x |- _ => subst x
    | h : ?x = ?x /\ _ |- _ => destruct h as [_ ?]
    | h : _ = _ /\ _ |- _ => (destruct h as [<- ?] || destruct h as [?EQ ?])
    end.

Import D.
Variant hidden_cfg  (T: Type) : Type := boxh_cfg (t: T).
Variant visible_cfg (T: Type) : Type := boxv_cfg (t: T).
Ltac hide_cfg :=
  match goal with
  | h : visible_cfg _ |- _ =>
    let EQ := fresh "VG" in
    destruct h as [EQ];
    apply boxh_cfg in EQ
  | |- context[denote_bks ?cfg _] =>
    remember cfg as G eqn:VG;
    apply boxh_cfg in VG
  end.
Ltac show_cfg :=
  match goal with
  | h: hidden_cfg _ |- _ =>
    let EQ := fresh "HG" in
    destruct h as [EQ];
    apply boxv_cfg in EQ
  end.
Notation "'hidden' G" := (hidden_cfg (G = _)) (only printing, at level 10).

(* All labels in a list of blocks are distinct *)
Definition wf_cfg {T} (bks : list (LLVMAst.block T)) :=
  Coqlib.list_norepet (map blk_id bks).

Lemma wf_cfg_nil:
  forall T, wf_cfg (T := T) []. 
Proof.
  intros; apply Coqlib.list_norepet_nil.
Qed.

Lemma wf_cfg_cons :
  forall T (b : LLVMAst.block T) bs,
    wf_cfg (b :: bs) ->
    wf_cfg bs.
Proof.
  intros * NOREP; inv NOREP; eauto.
Qed.

Lemma wf_cfg_cons_not_in :
  forall T (b : LLVMAst.block T) bs,
    wf_cfg (b :: bs) ->
    not (In (blk_id b) (map blk_id bs)).
Proof.
  intros * NOREP; inv NOREP; eauto.
Qed.

Lemma wf_cfg_app_r :
  forall T (bs1 bs2 : list (LLVMAst.block T)), 
wf_cfg (bs1 ++ bs2) ->
wf_cfg bs2.
Proof.
  intros * NR.
  eapply Coqlib.list_norepet_append_right.
  unfold wf_cfg in NR.
  rewrite map_app in NR.
  eauto.
Qed.

Lemma wf_cfg_app_l :
  forall T (bs1 bs2 : list (LLVMAst.block T)), 
wf_cfg (bs1 ++ bs2) ->
wf_cfg bs1.
Proof.
  intros * NR.
  eapply Coqlib.list_norepet_append_left.
  unfold wf_cfg in NR.
  rewrite map_app in NR.
  eauto.
Qed.

Lemma blk_id_convert_typ : forall env b,
    blk_id (convert_typ env b) = blk_id b.
Proof.
  intros ? []; reflexivity.
Qed.

Lemma blk_id_map_convert_typ : forall env bs,
    map blk_id (convert_typ env bs) = map blk_id bs.
Proof.
  induction bs as [| b bs IH]; cbn; auto.
  f_equal; auto.
Qed.

Lemma wf_cfg_convert_typ :
  forall env (bs : list (LLVMAst.block typ)),
    wf_cfg bs ->
    wf_cfg (convert_typ env bs).
Proof.
  induction bs as [| b bs IH]; intros NOREP.
  - cbn; auto.
  - cbn.
    apply Coqlib.list_norepet_cons. 
    + cbn.
      apply wf_cfg_cons_not_in in NOREP.
     rewrite blk_id_map_convert_typ; auto.
    + eapply IH, wf_cfg_cons; eauto. 
Qed.
(** [break_inner_match' t] tries to destruct the innermost [match] it
    find in [t]. *)
Ltac break_inner_match' t :=
 match t with
   | context[match ?X with _ => _ end] =>
     break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

(** [break_inner_match_goal] tries to destruct the innermost [match] it
    find in your goal. *)
Ltac break_inner_match_goal :=
 match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

(** [break_inner_match_hyp] tries to destruct the innermost [match] it
    find in a hypothesis. *)
Ltac break_inner_match_hyp :=
 match goal with
   | [ H : context[match ?X with _ => _ end] |- _ ] =>
     break_inner_match' X
 end.

(** [break_inner_match] tries to destruct the innermost [match] it
    find in your goal or a hypothesis. *)
Ltac break_inner_match := break_inner_match_goal || break_inner_match_hyp.


Lemma find_block_app_r_wf :
  forall (T : Set) (x : block_id) (b : LLVMAst.block T) (bs1 bs2 : list (LLVMAst.block T)),
    wf_cfg (bs1 ++ bs2)  ->
    find_block T bs2 x = Some b ->
    find_block T (bs1 ++ bs2) x = Some b.
Proof.
  intros T x b; induction bs1 as [| hd bs1 IH]; intros * NOREP FIND.
  - rewrite app_nil_l; auto.
  - cbn; break_inner_match_goal.
    + cbn in *.
      apply wf_cfg_cons_not_in in NOREP.
      exfalso; apply NOREP.
      rewrite e.
      apply find_some in FIND as [FIND EQ].
      clear - FIND EQ.
      rewrite map_app; eapply in_or_app; right.
      break_match; [| intuition].
      rewrite <- e.
      eapply in_map; auto.
    + cbn in NOREP; apply wf_cfg_cons in NOREP.
      apply IH; eauto.
Qed.

Lemma find_block_app_l_wf :
  forall (T : Set) (x : block_id) (b : LLVMAst.block T) (bs1 bs2 : list (LLVMAst.block T)),
    wf_cfg (bs1 ++ bs2)  ->
    find_block T bs1 x = Some b ->
    find_block T (bs1 ++ bs2) x = Some b.
Proof.
  intros T x b; induction bs1 as [| hd bs1 IH]; intros * NOREP FIND.
  - inv FIND.
  - cbn in FIND |- *.
    break_inner_match; auto.
    apply IH; eauto.
    eapply wf_cfg_cons, NOREP.
Qed.

Lemma find_block_tail_wf :
  forall (T : Set) (x : block_id) (b b' : LLVMAst.block T) (bs : list (LLVMAst.block T)),
    wf_cfg (b :: bs)  ->
    find_block T bs x = Some b' ->
    find_block T (b :: bs) x = Some b'.
Proof.
  intros.
  rewrite list_cons_app.
  apply find_block_app_r_wf; auto.
Qed.

Definition fresh_in_cfg {T} (cfg : list (LLVMAst.block T)) (id : block_id) : Prop :=
  not (In id (map blk_id cfg)).

Lemma fresh_in_cfg_cons:
  forall {T} b (bs : list (LLVMAst.block T)) id,
    fresh_in_cfg (b::bs) id ->
    fresh_in_cfg bs id .
Proof.
  intros * FR abs; apply FR; cbn.
  destruct (Eqv.eqv_dec_p (blk_id b) id); [rewrite e; auto | right; auto].
Qed.

Lemma find_block_fresh_id :
  forall {T} (cfg : list (LLVMAst.block T)) id,
    fresh_in_cfg cfg id ->
    find_block T cfg id = None.
Proof.
  induction cfg as [| b bs IH]; cbn; intros * FRESH; auto.
  break_inner_match_goal.
  + exfalso; eapply FRESH.
    cbn; rewrite e; auto.
  + apply IH.
    apply fresh_in_cfg_cons in FRESH; auto.
Qed.

(* Enforcing these definitions to be unfolded systematically by [cbn] *)
Arguments endo /.
Arguments Endo_id /.
Arguments Endo_ident /.

Lemma fresh_in_convert_typ :
  forall env (bs : list (LLVMAst.block typ)) id,
  fresh_in_cfg bs id ->
  fresh_in_cfg (convert_typ env bs) id.
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
      eapply fresh_in_cfg_cons; eauto.
Qed.

Arguments find_block : simpl never.

Ltac solve_find_block :=
  cbn;
  match goal with
    | |- find_block _ [_] _ = _ => apply find_block_eq; reflexivity
    | h: wf_cfg _ |- find_block _ (_ :: _) _ = _ =>
      first [apply find_block_eq; reflexivity |
             apply find_block_tail_wf; [eassumption | apply wf_cfg_cons in h; solve_find_block]]
    | h: wf_cfg _ |- find_block _ (_ ++ _) _ = _ =>
      first [apply find_block_app_l_wf; [eassumption | apply wf_cfg_app_l in h; solve_find_block] |
             apply find_block_app_r_wf; [eassumption | apply wf_cfg_app_r in h; solve_find_block]]
  end.

Lemma convert_typ_block_app : forall (a b : list (LLVMAst.block typ)) env, (convert_typ env (a ++ b) = convert_typ env a ++ convert_typ env b)%list.
Proof.
  induction a as [| [] a IH]; cbn; intros; auto.
  rewrite IH; reflexivity.
Qed.

Ltac vjmp :=
  rewrite denote_bks_unfold_in; cycle 1;
  [match goal with
   | h: hidden_cfg _ |- _ => inv h
   | h: visible_cfg _ |- _ => inv h
   | _ => idtac
   end;
   cbn; rewrite ?convert_typ_block_app;
   try solve_find_block |].

Ltac vjmp_out :=
  rewrite denote_bks_unfold_not_in; cycle 1;
  [apply find_block_fresh_id; eauto |]. 

Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.

Module VIR_Notations.
  (* We define print-only surface syntax for VIR *)

  (* Identifiers *)
  Notation "'%'" := ID_Local (only printing).
  Notation "'@'" := ID_Global (only printing).

  (* Expressions *)
  Notation "e" := (EXP_Integer e) (at level 10,only printing). 
  Notation "i" := (EXP_Ident i) (at level 10,only printing). 
  Notation "'add' e f"  := (OP_IBinop (LLVMAst.Add _ _) _ e f) (at level 10, only printing).
  Notation "'sub' e f"  := (OP_IBinop (Sub _ _) _ e f) (at level 10, only printing).
  Notation "'mul' e f"  := (OP_IBinop (Mul _ _) _ e f) (at level 10, only printing).
  Notation "'shl' e f"  := (OP_IBinop (Shl _ _) _ e f) (at level 10, only printing).
  Notation "'udiv' e f" := (OP_IBinop (UDiv _) _ e f)  (at level 10, only printing).
  Notation "'sdiv' e f" := (OP_IBinop (SDiv _) _ e f)  (at level 10, only printing).
  Notation "'lshr' e f" := (OP_IBinop (LShr _) _ e f)  (at level 10, only printing).
  Notation "'ashr' e f" := (OP_IBinop (AShr _) _ e f)  (at level 10, only printing).
  Notation "'urem' e f" := (OP_IBinop URem _ e f)      (at level 10, only printing).
  Notation "'srem' e f" := (OP_IBinop SRem _ e f)      (at level 10, only printing).
  Notation "'and' e f"  := (OP_IBinop And _ e f)       (at level 10, only printing).
  Notation "'or' e f"   := (OP_IBinop Or _ e f)        (at level 10, only printing).
  Notation "'xor' e f"  := (OP_IBinop Xor _ e f)       (at level 10, only printing).
  Notation "'eq' e f"   := (OP_ICmp Eq _ e f)       (at level 10, only printing).
  Notation "'ne' e f"   := (OP_ICmp Ne _ e f)       (at level 10, only printing).
  Notation "'ugt' e f"   := (OP_ICmp Ugt _ e f)       (at level 10, only printing).
  Notation "'uge' e f"   := (OP_ICmp Uge _ e f)       (at level 10, only printing).
  Notation "'ult' e f"   := (OP_ICmp Ult _ e f)       (at level 10, only printing).
  Notation "'ule' e f"   := (OP_ICmp Ule _ e f)       (at level 10, only printing).
  Notation "'sgt' e f"   := (OP_ICmp Sgt _ e f)       (at level 10, only printing).
  Notation "'sge' e f"   := (OP_ICmp Sge _ e f)       (at level 10, only printing).
  Notation "'slt' e f"   := (OP_ICmp Slt _ e f)       (at level 10, only printing).
  Notation "'sle' e f"   := (OP_ICmp Sle _ e f)       (at level 10, only printing).

  (* Instructions *)
  Notation "r '←' 'op' x" := ((IId r, INSTR_Op x)) (at level 10, only printing).
  Notation "r '←' 'call' x args" := ((IId r, INSTR_Call x args)) (at level 10, only printing).
  Notation "'call' x args" := ((IVoid, INSTR_Call x args)) (at level 10, only printing).
  Notation "r '←' 'alloca' t" := ((IId r, INSTR_Alloca t _ _)) (at level 10, only printing).
  Notation "r '←' 'load' t ',' e" := ((IId r, INSTR_Load _ t e _)) (at level 10, only printing).
  Notation "r '←' 'store' e ',' f" := ((IId r, INSTR_Store _ e f _)) (at level 10, only printing).

  (* Terminators *)
  Notation "'ret' τ e" := (TERM_Ret (τ, e)) (at level 10, only printing).
  Notation "'ret' 'void'" := (TERM_Ret_void) (at level 10, only printing).
  Notation "'br' c ',' 'label' e ',' 'label' f" := (TERM_Br c e f) (at level 10, only printing).
  Notation "'br' 'label' e" := (TERM_Br_1 e) (at level 10, only printing).

  (* Phi-nodes *)
  Notation "x ← 'Φ' xs" := (x,Phi _ xs) (at level 10,only printing).

  (* Types *)
  Notation "'ι' x" := (DTYPE_I x) (at level 10,only printing, format "'ι' x").
  Notation "⋆" := (DTYPE_Pointer) (at level 10,only printing).
  Notation "x" := (convert_typ _ x) (at level 10, only printing).
  Notation "x" := (typ_to_dtyp _ x) (at level 10, only printing).
  Notation "x" := (fmap (typ_to_dtyp _) x) (at level 10, only printing).
  Notation "'ι' x" := (TYPE_I x) (at level 10,only printing, format "'ι' x").
  Notation "⋆" := (TYPE_Pointer) (at level 10,only printing).
 
End VIR_Notations.

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

Lemma denote_block_unfold_cont :
  forall {R} id phis c t s origin (k : _ -> itree _ R),
    denote_block (mk_block id phis c t s) origin >>= k
                 ≈
                 denote_phis origin phis;;
    denote_code c;;
    translate exp_E_to_instr_E (denote_terminator (snd t)) >>= k.
Proof.
  intros; cbn; repeat setoid_rewrite bind_bind.
  reflexivity.
Qed.

Lemma denote_block_unfold :
  forall id phis c t s origin,
    denote_block (mk_block id phis c t s) origin
                 ≈
                 denote_phis origin phis;;
    denote_code c;;
    translate exp_E_to_instr_E (denote_terminator (snd t)). 
Proof.
  intros; cbn; reflexivity.
Qed.

From Vellvm Require Import InstrLemmas ExpLemmas.

Ltac vred_any :=
  (* Reduce annoying type conversion *)
  rewrite ?typ_to_dtyp_equation;
  match goal with
  | |- context[denote_block] =>
    (* Structural handling: block case *)
    first [rewrite denote_block_unfold_cont; cbn | rewrite denote_block_unfold; cbn];
    idtac "Reduced block"
  | |- context[denote_phis _ _]  =>
    (* Structural handling: phi case *)
    first [rewrite denote_no_phis];
    idtac "Reduced phis"
  | |- context[denote_code] =>
    (* Structural handling: code case *)
    first [rewrite denote_code_nil |
           rewrite denote_code_singleton |
           rewrite denote_code_cons |
           rewrite ?convert_typ_app, ?fmap_list_app, denote_code_app];
    idtac "Reduced code"
  | |- context[denote_terminator] =>
    (* Structural handling: code case *)
    first [rewrite denote_term_br_1];
    idtac "Reduced direct jump"
   | |- context[denote_exp] => 
    (* Structural handling: expression case *)
    first [rewrite translate_trigger; (rewrite lookup_E_to_exp_E_Local || rewrite lookup_E_to_exp_E_Global);
           rewrite subevent_subevent, translate_trigger;
           (rewrite exp_E_to_instr_E_Local || rewrite exp_E_to_instr_E_Global); rewrite subevent_subevent];
    idtac "Reduced exp"
  | |- _ => idtac "no progress made"
  end;
  (* clean up *)
  rewrite 1?interp_cfg_to_L3_ret, 1?bind_ret_l;
  rewrite 1?interp_cfg_to_L3_bind, 1?bind_bind.

Ltac vbranch_l := rewrite denote_term_br_l;
                 [rewrite 1?interp_cfg_to_L3_ret, 1?bind_ret_l, 1?interp_cfg_to_L3_bind, 1?bind_bind |];
                 cycle 1.
Ltac vbranch_r := rewrite denote_term_br_r;
                 [rewrite 1?interp_cfg_to_L3_ret, 1?bind_ret_l, 1?interp_cfg_to_L3_bind, 1?bind_bind |];
                 cycle 1.

Ltac eutt_hide_left_named H :=
  match goal with
    |- eutt _ ?t _ => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_left" ident(hypname) :=
  eutt_hide_left_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_left" :=
  let H := fresh "EL" in
  eutt_hide_left_named H.

Ltac eutt_hide_right_named H :=
  match goal with
    |- eutt _ _ ?t => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_right" ident(hypname) :=
  eutt_hide_right_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_right" :=
  let H := fresh "ER" in
  eutt_hide_right_named H.

Ltac eutt_hide_rel_named H :=
  match goal with
    |- eutt ?t _ _ => remember t as H
  end.

Ltac vred_r :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred_any;
        subst X; subst R.

Ltac vred_l :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_right_named X; vred_any;
        subst X; subst R.

Ltac expstep :=
first [rewrite denote_exp_LR; cycle 1 |
         rewrite denote_exp_GR; cycle 1 |
         rewrite denote_exp_i64 |
         rewrite denote_exp_i64_repr |
         rewrite denote_exp_double |
         rewrite denote_ibinop_concrete; cycle 1; try reflexivity |
         rewrite denote_fbinop_concrete; cycle 1; try reflexivity |
         rewrite denote_icmp_concrete; cycle 1; try reflexivity |
         rewrite denote_fcmp_concrete; cycle 1; try reflexivity |
         rewrite denote_conversion_concrete; cycle 1 |
         idtac].

Ltac instrstep :=
  first [rewrite denote_instr_load; eauto; cycle 1 |
         rewrite denote_instr_intrinsic; cycle 1; try reflexivity |
         rewrite denote_instr_op; cycle 1 |
         idtac
        ].

Ltac vstep :=
  first [progress expstep | instrstep];
  rewrite 1?interp_cfg_to_L3_ret, 1?bind_ret_l;
  rewrite 1?interp_cfg_to_L3_bind, 1?bind_bind.

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

Ltac forwardr H H' :=
  match type of H with
  | ?P -> _ => assert P as H'; [| specialize (H H')]
  end.
Tactic Notation "forwardr" ident(H) ident(H') := forwardr H H'.

Definition block_ids {T : Set} (b : list ((LLVMAst.block T))) :=
  map (@blk_id T) b.

(* TODO: Show symmetric case *)
Lemma wf_cfg_app_not_in_l :
  forall (T : Set) id (bs bs' : list (LLVMAst.block T)), In id (block_ids bs) ->
    wf_cfg (bs' ++ bs) ->
    not (In id (block_ids bs')).
Proof.
  intros. destruct bs.
  inversion H.
  inv H.
  apply wf_cfg_cons_not_in.
  unfold wf_cfg in *.
  rewrite map_app in H0.
  rewrite map_cons. rewrite map_cons in H0.
  rewrite list_cons_app in H0.
  rewrite app_assoc in H0.
  apply Coqlib.list_norepet_append_left in H0.
  rewrite list_cons_app.
  rewrite Coqlib.list_norepet_app in *.
  intuition. apply Coqlib.list_disjoint_sym. auto.
  unfold wf_cfg in H0.
  rewrite map_app in H0. rewrite map_cons in H0. rewrite list_cons_app in H0.
  apply Coqlib.list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
  apply Coqlib.list_norepet_append_right in H0.
  rewrite Coqlib.list_norepet_app in H0.
  destruct H0 as (? & ? & ?).
  red in H2. intro. eapply H2; eauto.
Qed.

(* TODO: Show symmetric case *)
Lemma wf_cfg_app_not_in_r :
  forall (T : Set) id (bs bs' : list (LLVMAst.block T)), In id (block_ids bs) ->
    wf_cfg (bs' ++ bs) ->
    not (In id (block_ids bs')).
Proof.
  intros. destruct bs.
  inversion H.
  inv H.
  apply wf_cfg_cons_not_in.
  unfold wf_cfg in *.
  rewrite map_app in H0.
  rewrite map_cons. rewrite map_cons in H0.
  rewrite list_cons_app in H0.
  rewrite app_assoc in H0.
  apply Coqlib.list_norepet_append_left in H0.
  rewrite list_cons_app.
  rewrite Coqlib.list_norepet_app in *.
  intuition. apply Coqlib.list_disjoint_sym. auto.
  unfold wf_cfg in H0.
  rewrite map_app in H0. rewrite map_cons in H0. rewrite list_cons_app in H0.
  apply Coqlib.list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
  apply Coqlib.list_norepet_append_right in H0.
  rewrite Coqlib.list_norepet_app in H0.
  destruct H0 as (? & ? & ?).
  red in H2. intro. eapply H2; eauto.
Qed.

Ltac match_rewrite :=
  match goal with
  | H : (?X = ?v) |-
    context [ match ?X with | _ => _ end] =>
    rewrite H
  end.

Lemma denote_bks_prefix :
  forall (prefix bks' postfix bks : list (LLVMAst.block dtyp)) (from to: block_id),
    bks = (prefix ++ bks' ++ postfix) ->
    wf_cfg bks ->
    denote_bks bks (from, to) ≈
               ITree.bind (denote_bks bks' (from, to))
               (fun x => match x with
                      | inl x => denote_bks bks x
                      | inr x => ret (inr x)
                      end
               ).
Proof.
  intros * ->; revert from to.
  einit.
  ecofix CIH.
  clear CIH0.
  intros * WF.
  destruct (find_block dtyp bks' to) as [bk |] eqn:EQ.
  - unfold denote_bks at 1 3.
    rewrite 2 KTreeFacts.unfold_iter_ktree.
    cbn; rewrite !bind_bind.
    assert (find_block dtyp (prefix ++ bks' ++ postfix) to = Some bk).
    {
      erewrite find_block_app_r_wf; eauto.
      erewrite find_block_app_l_wf; eauto.
      eapply wf_cfg_app_r; eauto.
    }
    do 2 match_rewrite.
    rewrite !bind_bind.
    eapply euttG_bind; econstructor; [reflexivity | intros [] ? <-].
    + rewrite !bind_ret_l; cbn.
      rewrite bind_tau; etau.
    + rewrite !bind_ret_l.
      reflexivity.
  - edrop.
    rewrite (denote_bks_unfold_not_in bks'); auto.
    rewrite bind_ret_l.
    reflexivity.
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
  eapply sizeof_dvalue_pos; eauto.
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


(* Definition def_sites_instr_id (id : instr_id) : list raw_id := *)
(*   match id with *)
(*   | IId id => [id] *)
(*   | _ => [] *)
(*   end. *)

(* Definition def_sites_code {T} (c : code T) : list raw_id := *)
(*   List.fold_left (fun acc '(id,_) => match id with | IId id => id :: acc | _ => acc end) c []. *)

(* From Vellvm Require Import PostConditions. *)
(* From Vellvm Require Import NoFailure. *)

(* Lemma def_sites_modified_instr : forall defs id (i : instr _) g l m, *)
(*     interp_cfg_to_L3 defs (denote_instr (id,i)) g l m ⤳ (fun '(_,(l',_)) => forall k, l' @ k <> l @ k -> In k (def_sites_instr_id id)). *)
(* Proof. *)
(*   intros.  *)
(*   destruct i; cbn. *)
(*   - rewrite denote_instr_comment; apply eutt_Ret; intros; intuition. *)
(*   - destruct id. *)
(*     + admit. *)
(*     + Transparent denote_instr. *)
(*       cbn. *)
      

(*       has_failure *)
(*       unfold has_post. *)
(*       rewrite denote_instr_op. apply eutt_Ret; intros; intuition. *)

(* Lemma def_sites_modified_code : forall defs (c : code _) g l m, *)
(*     interp_cfg_to_L3 defs (denote_code c) g l m ⤳ (fun '(_,(l',_)) => forall k, l' @ k <> l @ k -> In k (def_sites_code c)). *)
(* Proof. *)
(*   induction c as [| i c IH]; intros. *)
(*   - cbn. *)
(*     rewrite denote_code_nil, interp_cfg_to_L3_ret. *)
(*     apply eutt_Ret. *)
(*     intros; auto. *)
(*   - cbn. *)
(*     rewrite denote_code_cons, interp_cfg_to_L3_bind. *)
(*     eapply has_post_bind_strong. *)
    
(*     apply eutt_Ret. *)
(*     intros ? abs; auto. *)


