(*
  Simple memory model. Inspired by Vellvm

  Memory cells all have the same type: `CarrierA`.
 *)

From Coq.FSets Require Import
     FSetAVL
     FSetInterface
     FSetFacts
     FSetProperties
     FSetToFiniteSet
     FMapAVL
     FMapInterface
     FMapFacts.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.Tactics.HelixTactics.

Import MonadNotation.
Open Scope monad_scope.

Definition addr := (nat * nat) % type.
Definition null := (0, 0).

Open Scope nat_scope.

Lemma addr_dec : forall (a b : addr), {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2].
  destruct (eq_nat_dec a1 b1);
    destruct (eq_nat_dec a2 b2); subst.
  - left; reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
Qed.

Module NM := FMapAVL.Make(Nat_as_OT).
Module Import NP := FMapFacts.WProperties_fun(Nat_as_OT)(NM).
Definition NatMap := NM.t.

Module NS := FSetAVL.Make(Nat_as_OT).
Module Import NSP := FSetProperties.WProperties_fun(Nat_as_OT)(NS).
Definition NatSet := NS.t.
Module Import NE := FSetToFiniteSet.WS_to_Finite_set(Nat_as_OT)(NS).

Definition mem_add k (v:CarrierA) := NM.add k v.
Definition mem_delete k (m:NatMap CarrierA) := NM.remove k m.
Definition mem_member k (m:NatMap CarrierA) := NM.mem k m.
Definition mem_in     k (m:NatMap CarrierA) := NM.In k m.
Definition mem_lookup k (m:NatMap CarrierA) := NM.find k m.
Definition mem_empty := @NM.empty CarrierA.
Definition mem_mapsto k (v:CarrierA) (m:NatMap CarrierA) := @NM.MapsTo CarrierA k v m.

Definition mem_block := NatMap CarrierA.

Definition mem_keys (m:NatMap CarrierA): list nat
  := List.map fst (NM.elements m).

Definition mem_keys_lst (m:NatMap CarrierA): list nat :=
  List.map fst (NM.elements m).

Definition mem_keys_set (m: mem_block): NatSet :=
    NSP.of_list (mem_keys_lst m).

(* forcefull union of two memory blocks. conflicts are resolved by
   giving preference to elements of the 1st block *)
Definition mem_union (m1 m2 : mem_block) : mem_block
  := NM.map2 (fun mx my =>
                match mx with
                | Some x => Some x
                | None => my
                end) m1 m2.

Definition is_disjoint (a b: NatSet) : bool :=
  NS.is_empty (NS.inter a b).

Definition mem_merge (a b: mem_block) : option mem_block
  :=
    let kx := mem_keys_set a in
    let ky := mem_keys_set b in
    if is_disjoint kx ky
    then Some (mem_union a b)
    else None.

(* merge two memory blocks in (0..n-1) using given operation to combine values *)
Definition mem_merge_with (f: CarrierA -> CarrierA -> CarrierA): mem_block -> mem_block -> mem_block
  :=
    NM.map2 (fun a b =>
               match a,b with
               | None, None => None
               | Some x, None => Some x
               | None, Some y => Some y
               | Some x, Some y => Some (f x y)
               end).

(* block of memory with indices (0..n-1) set to `v` *)
Fixpoint mem_const_block (n:nat) (v: CarrierA) : mem_block
  :=
    match n with
    | O => mem_add n v (mem_empty)
    | S n' => mem_add n v (mem_const_block n' v)
    end.

Definition memory := NatMap mem_block.

Definition mem_block_equiv:= NM.Equal (elt:=CarrierA).

(* ------------------ Proofs below ------------------- *)

Lemma NF_eqb_eq {a b: nat}:
  NP.F.eqb a b = true -> a = b.
Proof.
  intros H.
  unfold NP.F.eqb in H.
  break_if.
  - auto.
  - inversion H.
Qed.

Lemma NF_eqb_neq {a b: nat}:
  NP.F.eqb a b = false -> a <> b.
Proof.
  intros H.
  unfold NP.F.eqb in H.
  break_if.
  - inversion H.
  - auto.
Qed.

Lemma mem_keys_set_In (k:NM.key) (m:mem_block):
  NM.In k m <-> NS.In k (mem_keys_set m).
Proof.
  pose proof (NM.elements_3w m) as U.
  split; intros H.
  -
    rewrite <- NP.of_list_3 with (s:=m) in H.
    unfold mem_keys_set, mem_keys_lst.
    unfold NP.of_list, NP.to_list in H.
    generalize dependent (NM.elements m). intros l U H.
    induction l.
    +
      simpl in H.
      apply NP.F.empty_in_iff in H.
      tauto.
    +
      destruct a as [k' v].
      simpl in *.
      destruct (eq_nat_dec k k') as [K|NK].
      *
        (* k=k' *)
        apply NS.add_1.
        auto.
      *
        (* k!=k' *)
        apply NSP.FM.add_neq_iff; try auto.
        apply IHl.
        --
          inversion U.
          auto.
        --
          eapply NP.F.add_neq_in_iff with (x:=k').
          auto.
          apply H.
  -
    rewrite <- NP.of_list_3 with (s:=m).
    unfold mem_keys_set, mem_keys_lst in H.
    unfold NP.of_list, NP.to_list.
    generalize dependent (NM.elements m). intros l U H.
    induction l.
    +
      simpl in H.
      apply NSP.FM.empty_iff in H.
      tauto.
    +
      destruct a as [k' v].
      simpl in *.
      destruct (eq_nat_dec k k') as [K|NK].
      *
        (* k=k' *)
        apply NP.F.add_in_iff.
        auto.
      *
        (* k!=k' *)
        apply NP.F.add_neq_in_iff; auto.
        apply IHl.
        --
          inversion U.
          auto.
        --
          apply NS.add_3 in H; auto.
Qed.

Lemma mem_keys_set_in_union_dec
      (m0 m1 : mem_block)
      (k : NM.key):
  NS.In k (mem_keys_set (mem_union m0 m1)) ->
  {NS.In k (mem_keys_set m1)}+{NS.In k (mem_keys_set m0)}.
Proof.
  intros H.
  unfold mem_union in H.
  apply mem_keys_set_In, NM.map2_2 in H.
  rewrite 2!NP.F.mem_in_iff in H.
  apply orb_true_intro, orb_true_elim in H.
  inversion H; [right|left] ;
    apply mem_keys_set_In, NP.F.mem_in_iff;
    auto.
Qed.

Lemma mem_merge_key_dec
      (m m0 m1 : mem_block)
      (MM : mem_merge m0 m1 = Some m)
  :
    forall k, NM.In k m -> {NM.In k m0}+{NM.In k m1}.
Proof.
  intros k H.
  rename m into mm.
  destruct (NP.F.In_dec m1 k) as [M1 | M1], (NP.F.In_dec m0 k) as [M0|M0]; auto.
  exfalso. (* Could not be in neither. *)
  unfold mem_merge in MM.
  break_if; inversion MM.
  subst mm. clear MM.
  rewrite mem_keys_set_In in M0, M1.
  clear Heqb.
  apply mem_keys_set_In, mem_keys_set_in_union_dec in H.
  destruct H; auto.
Qed.

Lemma mem_merge_key_not_in
      (m m0 m1 : mem_block)
      (MM : mem_merge m0 m1 = Some m)
  :
    forall k, (not (NM.In k m)) -> (not (NM.In k m0)) /\ (not (NM.In k m1)).
Proof.
  intros k H.
  unfold mem_merge in MM.
  break_if; inversion MM.
  clear MM Heqb.
  subst m.
  unfold mem_union in H.
  remember
    (fun mx my : option CarrierA =>
       match mx with
       | Some x => Some x
       | None => my
       end) as f.

  pose proof (F.map2_1bis) as F.
  assert(FN: f None None = None) by (subst f; reflexivity).
  specialize (F _ _ CarrierA m0 m1 k f FN). clear FN.
  apply F.not_find_in_iff in H.
  rewrite F in H. clear F.
  subst f.
  break_match.
  inversion H.
  split.
  apply F.not_find_in_iff in Heqo; auto.
  apply F.not_find_in_iff in H; auto.
Qed.

Lemma decidable_mem_in (k:NM.key) (m:mem_block): decidable (mem_in k m).
Proof.
  unfold decidable.
  destruct (NP.F.In_dec m k); auto.
Qed.

