Require Import Helix.Util.OptionSetoid.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.CType.

Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.
Require Import MathClasses.misc.util.
Require Import MathClasses.implementations.bool.
Require Import CoLoR.Util.List.ListUtil.

Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Util.ListSetoid.

Section NM_Equiv_instances.
  Context `{Aequiv: Equiv A}
          `{Aequivalence: Equivalence A Aequiv}.

  Global Instance NM_Equiv : Equiv (NM.t A)
    := fun m m' => forall k : NM.key, NM.find k m = NM.find k m'.

  Global Instance NM_Equiv_Reflexive:
    Reflexive (NM_Equiv).
  Proof.
    unfold NM_Equiv.
    unfold Reflexive.
    reflexivity.
  Qed.

  Global Instance NM_Equiv_Symmetric:
    Symmetric (NM_Equiv).
  Proof.
    unfold NM_Equiv.
    unfold Symmetric.
    intros x y H k.
    specialize (H k).
    auto.
  Qed.

  Global Instance NM_Equiv_Transitive:
    Transitive (NM_Equiv).
  Proof.
    unfold NM_Equiv.
    unfold Transitive.
    intros x y z H0 H1 k.
    specialize (H0 k).
    specialize (H1 k).
    auto.
  Qed.

  Global Instance NM_Equiv_Equivalence:
    Equivalence (NM_Equiv).
  Proof.
    split; typeclasses eauto.
  Qed.

End NM_Equiv_instances.


Module Type MMemSetoid (CT : CType).

  Include Memory.MBasic CT.
  Ltac mem_index_equiv k :=
    unfold equiv, NM_Equiv;
    intros k.

  Instance mem_lookup_proper:
    Proper ((eq) ==> (=) ==> (=)) (mem_lookup).
  Proof.
    simpl_relation.
    apply H0.
  Qed.

  Lemma MapsTo_In (k:nat) {A:Type} (e:A) (m:NatMap A):
    NM.MapsTo k e m -> NM.In k m.
  Proof.
    intros H.
    apply NP.F.in_find_iff.
    apply NM.find_1 in H.
    congruence.
  Qed.

  Lemma In_MapsTo (k:nat) {A:Type} (m:NatMap A):
    NM.In k m -> exists e, NM.MapsTo k e m.
  Proof.
    intros H.
    apply NP.F.in_find_iff in H.
    destruct (NM.find k m) as [e |] eqn:D.
    -
      eexists e.
      apply NM.find_2.
      apply D.
    -
      congruence.
  Qed.

  Lemma not_maps_to_find {A:Type}  {k v m}:
    ¬ (NM.MapsTo k v m) -> NM.find (elt:=A) k m <> Some v.
  Proof.
    intros H.
    destruct (is_Some_dec (NM.find (elt:=A) k m)) as [S | N].
    -
      intros F.
      apply NM.find_2 in F.
      congruence.
    -
      unfold is_Some, not in N.
      break_match_hyp ; try some_none.
      tauto.
  Qed.

  Instance mem_in_proper:
    Proper ((eq) ==> (=) ==> iff) (mem_in).
  Proof.
    simpl_relation.
    unfold mem_in.
    split.
    -
      intros H.
      apply NP.F.in_find_iff in H.
      apply NP.F.in_find_iff.
      apply None_nequiv_neq in H.
      apply None_nequiv_neq.
      rewrite <- H0.
      auto.
    -
      intros H.
      apply NP.F.in_find_iff in H.
      apply NP.F.in_find_iff.
      apply None_nequiv_neq.
      rewrite H0.
      apply None_nequiv_neq in H.
      auto.
  Qed.

  Instance mem_add_proper:
    Proper ((eq) ==> (equiv) ==> (equiv) ==> (equiv)) (mem_add).
  Proof.
    simpl_relation.
    rename y into k'.
    unfold mem_add.
    unfold equiv, NM_Equiv in H1.
    specialize (H1 k).
    destruct_opt_r_equiv.
    -
      apply Some_inj_equiv.
      rewrite <- Ha, <- Hb; clear Ha Hb.
      destruct (PeanoNat.Nat.eq_dec k k').
      +
        rewrite 2!NP.F.add_eq_o by auto.
        f_equiv.
        apply H0.
      +
        rewrite 2!NP.F.add_neq_o by auto.
        apply H1.
    -
      destruct (PeanoNat.Nat.eq_dec k k').
      +
        rewrite NP.F.add_eq_o in Hb by auto.
        some_none.
      +
        rewrite NP.F.add_neq_o in Ha by auto.
        rewrite NP.F.add_neq_o in Hb by auto.
        rewrite Ha in H1.
        rewrite Hb in H1.
        some_none.
    -
      destruct (PeanoNat.Nat.eq_dec k k').
      +
        rewrite NP.F.add_eq_o in Ha by auto.
        some_none.
      +
        rewrite NP.F.add_neq_o in Ha by auto.
        rewrite NP.F.add_neq_o in Hb by auto.
        rewrite Ha in H1.
        rewrite Hb in H1.
        some_none.
  Qed.

  Instance memory_lookup_proper:
    Proper ((=) ==> (eq) ==> (=)) (memory_lookup).
  Proof.
    simpl_relation.
    apply H.
  Qed.

  Instance mem_block_exists_proper:
    Proper ((eq) ==> (=) ==> iff) (mem_block_exists).
  Proof.
    simpl_relation.
    unfold mem_block_exists, memory, mem_block in *.
    split.
    -
      intros H.
      apply NP.F.in_find_iff in H.
      apply NP.F.in_find_iff.
      apply None_nequiv_neq.
      apply None_nequiv_neq in H.
      unfold equiv, NM_Equiv in H0.
      rewrite <- H0.
      apply H.
    -
      intros H.
      apply NP.F.in_find_iff in H.
      apply NP.F.in_find_iff.
      apply None_nequiv_neq.
      unfold equiv, NM_Equiv in H0.
      rewrite H0.
      apply None_nequiv_neq in H.
      auto.
  Qed.

  Lemma mem_block_exists_exists_equiv (m:memory) (k:nat):
    mem_block_exists k m <-> exists y : mem_block, memory_lookup m k = Some y.
  Proof.
    split; intros H.
    -
      apply NP.F.in_find_iff, is_Some_ne_None, is_Some_equiv_def in H.
      eauto.
    -
      apply NP.F.in_find_iff, is_Some_ne_None, is_Some_equiv_def.
      eauto.
  Qed.

  Lemma mem_union_mem_empty : forall x, mem_union mem_empty x = x.
  Proof.
    intros x.
    unfold equiv, NM_Equiv.
    intros k.
    unfold mem_empty, mem_union.
    rewrite NP.F.map2_1bis; [|reflexivity].
    rewrite NP.F.empty_o.
    reflexivity.
  Qed.

  Lemma mem_union_mem_add_commut :
    forall i value x,
      mem_union (mem_add i value (mem_const_block i value)) x =
      mem_add i value (mem_union (mem_const_block i value) x).
  Proof.
    intros i value x.
    unfold equiv, NM_Equiv.
    intros k.
    unfold mem_add, mem_union.
    destruct (PeanoNat.Nat.eq_dec i k).
    -
      subst.
      rewrite NP.F.add_eq_o; [|reflexivity].
      rewrite NP.F.map2_1bis; [|reflexivity].
      rewrite NP.F.add_eq_o; [|reflexivity].
      reflexivity.
    -
      rewrite NP.F.add_neq_o; [|assumption].
      repeat (rewrite NP.F.map2_1bis; [|reflexivity]).
      rewrite NP.F.add_neq_o; [|assumption].
      reflexivity.
  Qed.

End MMemSetoid.

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
  := NM.fold NM_err_seq_step
       mv
       (inr (@NM.empty A)).

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

Lemma NM_map_inr_all_OK
      `{EQ : Equiv A}
  :
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
    NP.for_all_range is_OK_bool em = true
    <->
    is_OK_bool (NM_err_sequence em) = true.
Proof.
  enough (T : NP.for_all_range is_OK_bool em = true
              <->
              exists vm, NM_err_sequence em = inr vm).
  {
    split; intros H.
    -
      apply T in H.
      destruct H.
      destruct NM_err_sequence; now inv H.
    -
      apply T.
      destruct NM_err_sequence;
        inv H.
      eexists; reflexivity.
  }
    
  split.
  -
    intro OK.
    unfold NP.for_all_range, NP.for_all in OK.
    unfold NM_err_sequence.

    rewrite NM.fold_1 in *.
    match goal with
    | [ |- context [List.fold_left ?f _ _]] => remember f as acc
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
      | [ _ : context [List.fold_left ?f _ _] |- _] => remember f as acc
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

(* Corollary of [NM_err_sequence_OK] *)
Lemma NM_err_sequence_not_OK
      `{EQ : Equiv A}
      `{EQv : Equivalence A EQ}
      (em: NM.t (err A))
  :
    NP.for_all_range is_OK_bool em = false
    <->
    is_OK_bool (NM_err_sequence em) = false.
Proof.
  split; intros.
  all: apply Bool.not_true_iff_false;
       apply Bool.not_true_iff_false in H.
  all: intros C; contradict H.
  all: now apply NM_err_sequence_OK.
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
        assert (OK' : exists vm, NM_err_sequence em' = inr vm)
          by (destruct NM_err_sequence; inv OK; eexists; reflexivity).
        clear OK; destruct OK' as [vm OK].
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

Lemma NP_for_all_false_iff
      (elt : Type)
      (f : NM.key → elt → bool)
      {PF : Proper (eq ==> eq ==> eq) f}
      (m : NM.t elt)
  :
    NP.for_all f m = false
    ↔
    (exists k e, NM.MapsTo k e m /\ f k e ≡ false).
Proof.
  split; intros.
  -
    unfold NP.for_all in H.
    rewrite NM.fold_1 in H.
    eapply ListUtil.fold_left_emergence2
      with (P:=fun x => x ≡ false)
           (Q:=fun p => f (fst p) (snd p) ≡ false)
      in H.
    2: {
      clear; intros.
      break_if; tauto.
    }
    destruct H; [inv H |].
    destruct H as [[k e] [F I]].
    exists k, e.
    split; [clear F | assumption].
    apply NP.F.elements_mapsto_iff.
    apply In_InA_eq in I.
    eapply InA_eqA_equiv.
    2: eassumption.
    clear; intros.
    subst; reflexivity.
  -
    destruct H as (k & e & KE & F).
    apply Bool.not_true_iff_false.
    apply Bool.not_true_iff_false in F.
    intros C; contradict F.
    eapply NP.for_all_iff in C.
    all: eassumption.
Qed.
