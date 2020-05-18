From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
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

End Translations.

From Vellvm Require Import Util.
Require Import State.

(* TODOYZ: This is weird, I need to import again this file for the rewriting to work.
   A bit unsure as to why this happen, but somehow some subsequent import breaks it.
 *)
Require Import ITree.Eq.Eq.

Section Denotation.
Import CatNotations.

Lemma denote_bks_nil: forall s, D.denote_bks [] s ≈ ret (inl s).
Proof.
  intros s; unfold D.denote_bks.
  unfold loop.
  cbn. rewrite bind_ret_l.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  repeat (cbn; (rewrite bind_bind || rewrite bind_ret_l)).
  reflexivity.
Qed.

Lemma denote_bks_singleton :
  forall (b : LLVMAst.block dtyp) (bid : block_id) (nextblock : block_id),
    blk_id b = bid ->
    (snd (blk_term b)) = (TERM_Br_1 nextblock) ->
    (blk_id b) <> nextblock ->
    eutt (Logic.eq) (D.denote_bks [b] bid) (D.denote_block b).
Proof.
  intros b bid nextblock Heqid Heqterm Hneq.
  cbn.
  rewrite bind_ret_l.
  rewrite KTreeFacts.unfold_iter_ktree.
  cbn.
  destruct (Eqv.eqv_dec_p (blk_id b) bid) eqn:Heq'; try contradiction.
  repeat rewrite bind_bind.
  rewrite Heqterm.
  cbn.
  setoid_rewrite translate_ret.
  setoid_rewrite bind_ret_l.
  destruct (Eqv.eqv_dec_p (blk_id b) nextblock); try contradiction.
  repeat setoid_rewrite bind_ret_l. unfold Datatypes.id.
  reflexivity.
Qed.

Lemma denote_code_app :
  forall a b,
    D.denote_code (a ++ b)%list ≈ ITree.bind (D.denote_code a) (fun _ => D.denote_code b).
Proof.
  induction a; intros b.
  - cbn. rewrite bind_ret_l.
    reflexivity.
  - cbn. rewrite bind_bind. setoid_rewrite IHa.
    reflexivity.
Qed.

Lemma denote_code_cons :
  forall a l,
    D.denote_code (a::l) ≈ ITree.bind (D.denote_instr a) (fun _ => D.denote_code l).
Proof.
  cbn; reflexivity.
Qed.

End Denotation.

(** 
Section NormalizeTypes.

Lemma normalize_types_block_bid :
  forall (env : list (ident * typ)) (b: LLVMAst.block typ),
    blk_id (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env) b) = blk_id b.
Proof.
  intros env b.
  destruct b. reflexivity.
Qed.

Lemma normalize_types_block_term :
  forall (env : list (ident * typ)) (b: LLVMAst.block typ) (nextblock : block_id),
    snd (blk_term b) = TERM_Br_1 nextblock ->
    snd (blk_term (TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b)) = TERM_Br_1 nextblock.
Proof.
  intros env b nextblock Hterm.
  destruct b. cbn in *. rewrite Hterm.
  reflexivity.
Qed.

Definition normalize_types_blocks (env: list _) (bks: list (LLVMAst.block typ))
  : list (LLVMAst.block DynamicTypes.dtyp) :=
  List.map
    (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env)) bks.

(* NOTEYZ: [TypeUtil.normalize_type_dtyp] seems unusable as is.
   Need to look into it.
 *)
  Lemma normalize_IntType :
    forall env,
      TypeUtil.normalize_type_dtyp env (TYPE_I 64%Z) = DTYPE_I 64.
  Proof.
  Admitted.

End NormalizeTypes.
**)

Section MemoryModel.

  Definition get_logical_block (mem: memory) (ptr: Addr.addr): option logical_block :=
    let '(b,a) := ptr in
    lookup_logical b mem.

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

(* I want an Ltac library for Vellvm. Here are a few first elementary pieces *)
(* TODO YZ : do it right, learn Ltac(2) *)

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac inv H := inversion H; try subst; clear H.

Global Tactic Notation "intros !" := repeat intro.

(* inv by name of the Inductive relation *)
Ltac invn f :=
    match goal with
    | [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

(* destruct by name of the Inductive relation *)
Ltac destructn f :=
    match goal with
    | [ id: f |- _ ] => destruct id
    | [ id: f _ |- _ ] => destruct id
    | [ id: f _ _ |- _ ] => destruct id
    | [ id: f _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => destruct id
    end.

(* apply by name of the Inductive relation *)
Ltac appn f :=
    match goal with
    | [ id: f |- _ ] => apply id
    | [ id: f _ |- _ ] => apply id
    | [ id: f _ _ |- _ ] => apply id
    | [ id: f _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => apply id
    end.

(* eapply by name of the Inductive relation *)
Ltac eappn f :=
    match goal with
    | [ id: f |- _ ] => eapply id
    | [ id: f _ |- _ ] => eapply id
    | [ id: f _ _ |- _ ] => eapply id
    | [ id: f _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => eapply id
    end.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac break_match := break_match_goal || break_match_hyp.

Ltac inv_option :=
  match goal with
  | h: Some _ = Some _ |-  _ => inv h
  | h: None   = Some _ |-  _ => inv h
  | h: Some _ = None   |-  _ => inv h
  | h: None   = None   |-  _ => inv h
  end.

Ltac inv_sum :=
  match goal with
  | h: inl _ = inl _ |-  _ => inv h
  | h: inr _ = inr _ |-  _ => inv h
  | h: inl _ = inr _ |-  _ => inv h
  | h: inr _ = inl _ |-  _ => inv h
  end.

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

  Lemma mcfg_of_app_modul: forall {T} (p1 p2 : modul T _) (m : mcfg T),
      mcfg_of_modul _ (p1 @ p2) = mcfg_of_modul _ p1 @ mcfg_of_modul _ p2.
  Proof.
    intros; cbn.
    unfold mcfg_of_modul.
    rewrite  m_name_app, m_target_app, m_datalayout_app, m_type_defs_app, m_globals_app, m_declarations_app; f_equal; try reflexivity. 
    rewrite m_definitions_app, map_app; reflexivity.
  Qed.
   
End TLE_To_Modul.

Infix "@" := (modul_app) (at level 60).
