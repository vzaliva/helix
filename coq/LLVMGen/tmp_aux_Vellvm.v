From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Tactics
     Util
     AstLib
     LLVMEvents
     DynamicTypes
     DynamicValues
     CFG
     Handlers.Memory
     Refinement
     TopLevel
     LLVMAst
     TypToDtyp
     Handlers.Handlers.

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

Section Translations.

  (** TODOYZ : MOVE (Vellvm)  *)
  (* Technicality: translations by [lookup_E_to_exp_E] and [exp_E_to_instr_E] leave these events unphased *)
  Lemma lookup_E_to_exp_E_Global : forall {X} (e : LLVMGEnvE X),
      lookup_E_to_exp_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Global : forall {X} (e : LLVMGEnvE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma lookup_E_to_exp_E_Local : forall {X} (e : LLVMEnvE X),
      lookup_E_to_exp_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Local : forall {X} (e : LLVMEnvE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Memory : forall {X} (e : MemoryE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.
  
End Translations.

From Vellvm Require Import Util.
Require Import State.

(* TODOYZ: This is weird, I need to import again this file for the rewriting to work.
   A bit unsure as to why this happen, but somehow some subsequent import breaks it.
 *)
Require Import ITree.Eq.Eq.

Section MemoryModel.

  Definition get_logical_block (mem: memory) (ptr: Addr.addr): option logical_block :=
    let '(b,a) := ptr in
    get_logical_block_mem b mem.

End MemoryModel.

Section Integers.

  (* NOTEYZ: I doubt that the following is true, unless proof irrelevance is assumed *)
  Lemma repr_intval (i: int64):
    DynamicValues.Int64.repr (Int64.intval i) = i.
  Proof.
  Admitted.

End Integers.

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

(** ** Event elimination
    This is a pure [itree] feature.

    We want to be able to express that a computation does not contain a particular event,
    and eliminate it safely from the signature if that is so.
 *)
From Paco Require Import paco.
Section ElimEvent.

  (* Since we cannot test equality of event, I rely on the exact order for now.
     As usual, the generalization of subevent may help with that?
   *)

  Definition helim_l {E F}: E +' F ~> itree F :=
    fun _ e => match e with
            | inl1 _ => ITree.spin
            | inr1 e => trigger e
            end.

  Definition helim_r {E F}: E +' F ~> itree E :=
    fun _ e => match e with
            | inr1 _ => ITree.spin
            | inl1 e => trigger e
            end.

  Definition elim_l {E F}: itree (E +' F) ~> itree F := interp helim_l. 
  Definition elim_r {E F}: itree (E +' F) ~> itree E := interp helim_r. 

  Variant no_left_eventF {E F X} (R: itree (E +' F) X -> Prop): itree (E +' F) X -> Prop :=
  | no_left_event_ret: forall (x: X), no_left_eventF R (ret x)
  | no_left_event_tau: forall t, R t -> no_left_eventF R (Tau t)
  | no_left_event_vis: forall {Y} (e: F Y) k, (forall x, R (k x)) -> no_left_eventF R (Vis (inr1 e) k).

  Definition no_left_event {E F X} := paco1 (@no_left_eventF E F X) bot1. 

  (* Lemma safe_helim_l: *)
  (*   forall {E F X} (t: itree (E +' F) X) (NOL: no_left_event t) (h: E ~> itree F), *)
  (*     elim_l _ t ≈  interp (case_ h ((fun _ e => trigger e): Handler F F)) t. *)

End ElimEvent.

Section TLE_To_Modul.

  Definition opt_first {T: Type} (o1 o2: option T): option T :=
    match o1 with | Some x => Some x | None => o2 end.

  Definition modul_app {T X} (m1 m2: modul T X): modul T X :=
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
      @modul_of_toplevel_entities T X (tle :: tles) = modul_app (modul_of_toplevel_entities T [tle]) (modul_of_toplevel_entities T tles).
  Proof.
    intros.
    unfold modul_of_toplevel_entities; cbn; f_equal;
      try ((break_match_goal; reflexivity) || (rewrite <- !app_nil_end; reflexivity)).
  Qed.

  Lemma modul_of_toplevel_entities_app:
    forall {T X} tle1 tle2, 
    @modul_of_toplevel_entities T X (tle1 ++ tle2) = modul_app (modul_of_toplevel_entities T tle1) (modul_of_toplevel_entities T tle2).
  Proof.
    induction tle1 as [| tle tle1 IH]; intros; cbn; [reflexivity |].
    rewrite modul_of_toplevel_entities_cons, IH; cbn.
    f_equal;
      try ((break_match_goal; reflexivity) || (rewrite <- !app_nil_end, app_assoc; reflexivity)).
  Qed.

  Infix "@" := (modul_app) (at level 60).

  Open Scope list.
  Lemma m_definitions_app: forall {T X} (p1 p2 : modul T X),
      m_definitions (p1 @ p2) = m_definitions p1 ++ m_definitions p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_name_app: forall {T X} (p1 p2 : modul T X),
      m_name (p1 @ p2) = opt_first (m_name p1) (m_name p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_target_app: forall {T X} (p1 p2 : modul T X),
      m_target (p1 @ p2) = opt_first (m_target p1) (m_target p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_datalayout_app: forall {T X} (p1 p2 : modul T X),
      m_datalayout (p1 @ p2) = opt_first (m_datalayout p1) (m_datalayout p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_type_defs_app: forall {T X} (p1 p2 : modul T X),
      m_type_defs (p1 @ p2) = m_type_defs p1 ++ m_type_defs p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_globals_app: forall {T X} (p1 p2 : modul T X),
      m_globals (p1 @ p2) = m_globals p1 ++ m_globals p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_declarations_app: forall {T X} (p1 p2 : modul T X),
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

  Lemma mcfg_of_app_modul: forall {T} (p1 p2 : modul T _), 
      mcfg_of_modul _ (p1 @ p2) = mcfg_of_modul _ p1 @ mcfg_of_modul _ p2.
  Proof.
    intros; cbn.
    unfold mcfg_of_modul.
    rewrite  m_name_app, m_target_app, m_datalayout_app, m_type_defs_app, m_globals_app, m_declarations_app; f_equal; try reflexivity. 
    rewrite m_definitions_app, map_app; reflexivity.
  Qed.

  (* YZ TODO :  A bit annoying but should not be an issue. *)
  Lemma convert_typ_mcfg_app:
    forall mcfg1 mcfg2 : modul typ (cfg typ),
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
      f_equal; try (unfold Endo_option; cbn; repeat flatten_goal; now intuition).
      + 
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

  Lemma mcfg_of_tle_app : forall x y, mcfg_of_tle (x ++ y) = modul_app (mcfg_of_tle x) (mcfg_of_tle y).
  Proof.
    intros ? ?.
    unfold mcfg_of_tle.
    rewrite modul_of_toplevel_entities_app.
    rewrite mcfg_of_app_modul.
    rewrite convert_types_app_mcfg.
    reflexivity.
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

(* TODO YZ : Move to itrees *)
(* Specialization of [eutt_clo_bind] to the case where the intermediate predicate introduced is the same as the current one *)
Lemma eutt_bind_inv :
  forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E R1) (t2 : itree E R2)
    (k1 : R1 -> itree E R1) (k2 : R2 -> itree E R2),
    eutt RR t1 t2 -> 
    (forall (r1 : R1) (r2 : R2), RR r1 r2 -> eutt RR (k1 r1) (k2 r2)) ->
    eutt RR (ITree.bind t1 (fun x : R1 => k1 x)) (ITree.bind t2 (fun x : R2 => k2 x)).
Proof.
  intros; apply eutt_clo_bind with (UU := RR); auto.
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
  Admitted.

  Lemma lookup_alist_add_ineq :
    forall k k' v (m : alist K V),
      k <> k' ->
      Maps.lookup k (alist_add k' v m) = Maps.lookup k m.
  Proof.
  Admitted.

End WithDec.

Notation "m '@' x" := (alist_find x m).
Notation "m '⊑' m'" := (sub_alist m m') (at level 45).

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

