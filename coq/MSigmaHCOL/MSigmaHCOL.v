(* Memory-based implementations of SHCOL operators *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Coq.Sets.Ensembles.
Require Import Psatz.
Require Import Omega.

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Util.ListSetoid.

Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.CarrierType.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.MSigmaHCOL.MemoryOfCarrierA.
Import MMemoryOfCarrierA.

Require Import Helix.Tactics.HelixTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.util.
Require Import MathClasses.implementations.peano_naturals.

Import Monoid.

Module MMSHCOL'
       (CT:CType with Definition t:=CarrierA
         with Definition CTypeEquiv := CarrierAe
         with Definition CTypeSetoid := CarrierAsetoid
       )
       (Import CM:MMemSetoid CT).


  Open Scope nat_scope.

  Import VectorNotations.
  Open Scope vector_scope.

  Import MonadNotation.
  Open Scope monad_scope.


  (* Conversion between memory block and dense vectors *)

  (* After folding starting from 'j' attempts to lookup lower indices will fail *)
  Lemma find_fold_right_indexed_oob
        (n i j: nat)
        {A B: Type}
        (v : vector A n)
        (P: A -> Prop)
        `{Pdec: forall x, sumbool (P x) (not (P x))}
        (f: A -> B)
  :
    j>i ->
    NM.find (elt:=B) i (Vfold_right_indexed' j
                                             (fun (k : nat) (r : A) (m : NM.t B) =>
                                                if Pdec r
                                                then
                                                  NM.add k (f r) m
                                                else m)
                                             v (@NM.empty B)) ≡ None.
  Proof.
    revert i j.
    induction n; intros.
    -
      dep_destruct v.
      reflexivity.
    -
      dep_destruct v; clear v.
      simpl.
      break_if.
      +
        rewrite NP.F.add_neq_o by omega.
        apply IHn.
        lia.
      +
        apply IHn.
        lia.
  Qed.

  Lemma find_fold_right_indexed'_off_P
        (n i off: nat)
        {A B: Type}
        (v : vector A n)
        (P: A -> Prop)
        `{Pdec: forall x, sumbool (P x) (not (P x))}
        (f: A -> B)
    :
      NM.find (elt:=B) (i+off) (Vfold_right_indexed' (0+off)
                                                     (fun (k : nat) (r : A) (m : NM.t B) =>
                                                        if Pdec r
                                                        then
                                                          NM.add k (f r) m
                                                        else m)
                                                     v (@NM.empty B)) ≡
              NM.find (elt:=B) i (Vfold_right_indexed' 0
                                                       (fun (k : nat) (r : A) (m : NM.t B) =>
                                                          if Pdec r
                                                          then
                                                            NM.add k (f r) m
                                                          else m)
                                                       v (@NM.empty B)).
  Proof.
    revert i off.
    induction n; intros.
    -
      dep_destruct v.
      reflexivity.
    -
      dep_destruct v; clear v.
      simpl.
      break_if.
      +
        destruct i.
        *
          rewrite NP.F.add_eq_o by reflexivity.
          rewrite NP.F.add_eq_o by reflexivity.
          reflexivity.
        *
          rewrite NP.F.add_neq_o by omega.
          rewrite NP.F.add_neq_o by omega.
          replace (S i + off) with (i + S off) by lia.
          replace (S off) with (0 + S off) by lia.
          rewrite IHn.
          symmetry.
          replace (1) with (0+1) by lia.
          replace (S i) with (i+1) by lia.
          apply IHn.
      +
        destruct i.
        *
          rewrite 2!find_fold_right_indexed_oob by lia.
          reflexivity.
        *
          replace (S i + off) with (i + S off) by lia.
          replace (S off) with (0 + S off) by lia.
          rewrite IHn.
          symmetry.
          replace (1) with (0+1) by lia.
          replace (S i) with (i+1) by lia.
          apply IHn.
  Qed.

  Lemma find_fold_right_indexed'_S_P
        (n i : nat)
        {A B: Type}
        (v : vector A n)
        (P: A -> Prop)
        `{Pdec: forall x, sumbool (P x) (not (P x))}
        (f: A -> B)
    :
      NM.find (elt:=B) (S i) (Vfold_right_indexed' 1
                                                   (fun (k : nat) (r : A) (m : NM.t B) =>
                                                      if Pdec r
                                                      then
                                                        NM.add k (f r) m
                                                      else m)
                                                   v (@NM.empty B)) ≡
              NM.find (elt:=B) i (Vfold_right_indexed' 0
                                                       (fun (k : nat) (r : A) (m : NM.t B) =>
                                                          if Pdec r
                                                          then
                                                            NM.add k (f r) m
                                                          else m)
                                                       v (@NM.empty B)).
  Proof.
    replace (1) with (0+1) by lia.
    replace (S i) with (i+1) by lia.
    apply find_fold_right_indexed'_off_P.
  Qed.

  Lemma find_fold_right_indexed'_cons_P
        (n i : nat)
        {A B: Type}
        (x : vector A n)
        (h: A)
        (P: A -> Prop)
        `{Pdec: forall x, sumbool (P x) (not (P x))}
        (f: A -> B):
    NM.find (elt:=B) (S i)
            (Vfold_right_indexed' 0
                                  (fun (k : nat) (r : A) (m : NM.t B) =>
                                     if Pdec r
                                     then
                                       NM.add k (f r) m
                                     else m)
                                  (h :: x) (NM.empty B))
            ≡
            NM.find (elt:=B) (S i)
            (Vfold_right_indexed' 1
                                  (fun (k : nat) (r : A) (m : NM.t B) =>
                                     if Pdec r
                                     then
                                       NM.add k (f r) m
                                     else m)
                                  x (NM.empty B)).
  Proof.
    destruct n.
    -
      dep_destruct x.
      simpl.
      break_if; reflexivity.
    -
      simpl.
      break_if.
      +
        rewrite NP.F.add_neq_o by omega.
        reflexivity.
      +
        reflexivity.
  Qed.

  Lemma find_fold_right_indexed'_off:
    forall (n i : nat) (off:nat) (x : vector CarrierA n),
      NM.find (elt:=CarrierA) (i+off) (Vfold_right_indexed' (0+off) mem_add x mem_empty) ≡
              NM.find (elt:=CarrierA) i (Vfold_right_indexed' 0 mem_add x mem_empty).
  Proof.
    intros n i off v.

    remember (@Basics.const Prop CarrierA True) as P.
    assert(Pdec: forall x, sumbool (P x) (not (P x)))
      by (intros x; left; subst P; unfold Basics.const;  tauto).
    remember (@id CarrierA) as f.
    unfold mem_empty.
    replace mem_add with
        (fun (k : nat) (r : CarrierA) (m : NM.t CarrierA) =>
           if Pdec r
           then
             NM.add k (f r) m
           else m).
    apply find_fold_right_indexed'_off_P.

    extensionality k.
    extensionality r.
    extensionality m.
    break_if.
    + subst f; unfold id; reflexivity.
    + subst P; unfold Basics.const, not  in *; crush.
  Qed.

  Lemma find_fold_right_indexed'_S:
    forall (n i : nat) (v : vector CarrierA n),
      NM.find (elt:=CarrierA) (S i) (Vfold_right_indexed' 1 mem_add v mem_empty) ≡
              NM.find (elt:=CarrierA) i (Vfold_right_indexed' 0 mem_add v mem_empty).
  Proof.
    intros n i v.

    replace (1) with (0+1) by lia.
    replace (S i) with (i+1) by lia.
    apply find_fold_right_indexed'_off.
  Qed.

  Definition mem_block_to_avector {n} (m: mem_block): option (vector CarrierA n)
    := vsequence (Vbuild (fun i (ic:i<n) => mem_lookup i m)).

  Program Definition avector_to_mem_block_spec
          {n : nat}
          (v : avector n):
    { m : mem_block | forall i (ip : i < n), mem_lookup i m ≡ Some (Vnth v ip)}
    := Vfold_right_indexed' 0 mem_add v mem_empty.
  Next Obligation.
    unfold mem_lookup.
    revert i ip; induction n; intros.
    -
      nat_lt_0_contradiction.
    -
      dep_destruct v;clear v.
      simpl.
      destruct i.
      +
        unfold Vfold_right_indexed, mem_add.
        apply NP.F.add_eq_o.
        reflexivity.
      +
        rewrite NP.F.add_neq_o; auto.
        assert (N: i<n) by apply Lt.lt_S_n, ip.
        specialize (IHn x i N).
        replace (Lt.lt_S_n ip) with N by apply le_unique. clear ip.
        rewrite <- IHn; clear IHn.
        apply find_fold_right_indexed'_S.
  Qed.

  Definition avector_to_mem_block {n:nat} (v:avector n) : mem_block := proj1_sig (avector_to_mem_block_spec v).

  Lemma avector_to_mem_block_key_oob {n:nat} {v: avector n}:
    forall (k:nat) (kc:ge k n), mem_lookup k (avector_to_mem_block v) ≡ None.
  Proof.
    intros k kc.
    unfold avector_to_mem_block.
    simpl.
    revert k kc; induction v; intros.
    -
      reflexivity.
    -
      unfold mem_lookup.
      simpl.
      rewrite NP.F.add_neq_o by omega.
      destruct k.
      +
        omega.
      +
        rewrite find_fold_right_indexed'_S.
        rewrite IHv.
        reflexivity.
        omega.
  Qed.

  Lemma mem_block_to_avector_eq_None {n m}:
    @mem_block_to_avector n m ≡ None ->
    exists j (jc:j<n), mem_lookup j m ≡ None.
  Proof.
    intros H.
    apply vsequence_Vbuild_eq_None.
    apply H.
  Qed.

  Lemma mem_lookup_avector_to_mem_block
        {n:nat}
        {v: avector n}:
    forall (k:nat) (kc:lt k n), mem_lookup k (avector_to_mem_block v) ≡ Some (Vnth v kc).
  Proof.
    intros k kc.
    unfold avector_to_mem_block.
    destruct (avector_to_mem_block_spec v) as [m H0].
    apply H0.
  Qed.

  Lemma mem_lookup_avector_to_mem_block_equiv
        {n:nat}
        {v: avector n}:
    forall (k:nat) (kc:lt k n), mem_lookup k (avector_to_mem_block v) = Some (Vnth v kc).
  Proof.
    intros k kc.
    unfold avector_to_mem_block.
    destruct (avector_to_mem_block_spec v) as [m H0].
    apply Option_equiv_eq.
    apply H0.
  Qed.


  Lemma mem_block_avector_id {n} {v:avector n}:
    (mem_block_to_avector (avector_to_mem_block v)) ≡ Some v.
  Proof.
    unfold mem_block_to_avector.
    apply vsequence_Vbuild_eq_Some.
    vec_index_equiv i ip.
    rewrite Vbuild_nth.
    rewrite Vnth_map.
    unfold avector_to_mem_block.
    destruct (avector_to_mem_block_spec v) as [m H].
    apply H.
  Qed.


  Instance mem_block_to_avector_proper {n:nat}:
    Proper ((equiv) ==> (equiv)) (@mem_block_to_avector n).
  Proof.
    simpl_relation.
    unfold mem_block_to_avector.
    destruct_opt_r_equiv.
    -
      apply vsequence_Vbuild_eq_Some in Ha.
      apply vsequence_Vbuild_eq_Some in Hb.
      rewrite Vmap_as_Vbuild in Ha.
      rewrite Vmap_as_Vbuild in Hb.
      vec_index_equiv j jc.
      apply Vnth_arg_eq with (ip:=jc) in Ha.
      apply Vnth_arg_eq with (ip:=jc) in Hb.
      rewrite 2!Vbuild_nth in Ha.
      rewrite 2!Vbuild_nth in Hb.
      apply Some_inj_equiv.
      rewrite <- Ha, <- Hb.
      rewrite H.
      reflexivity.
    -
      apply vsequence_Vbuild_eq_None in Hb.
      apply eq_Some_is_Some in Ha.
      rewrite vsequence_Vbuild_is_Some in Ha.
      destruct Hb as [j [jc Hb]].
      specialize (Ha j jc).
      apply is_Some_ne_None in Ha.
      apply None_nequiv_neq in Ha.
      apply None_equiv_eq in Hb.
      rewrite H in Ha.
      some_none.
    -
      apply vsequence_Vbuild_eq_None in Ha.
      apply eq_Some_is_Some in Hb.
      rewrite vsequence_Vbuild_is_Some in Hb.
      destruct Ha as [j [jc Ha]].
      specialize (Hb j jc).
      apply is_Some_ne_None in Hb.
      apply None_nequiv_neq in Hb.
      apply None_equiv_eq in Ha.
      rewrite H in Ha.
      some_none.
  Qed.

  Instance avector_to_mem_block_proper {n:nat}:
    Proper ((equiv) ==> (equiv)) (@avector_to_mem_block n).
  Proof.
    simpl_relation.
    unfold avector_to_mem_block.
    simpl.
    destruct_opt_r_equiv.
    -
      rename c into a, c0 into b.
      apply Some_inj_equiv.
      unfold CT.t.
      rewrite <- Ha, <- Hb.
      rewrite H.
      reflexivity.
    -
      assert(C: NM.find (elt:=CarrierA) k (Vfold_right_indexed' 0 mem_add x mem_empty)
                = NM.find (elt:=CarrierA) k (Vfold_right_indexed' 0 mem_add y mem_empty)).
      {
        rewrite H.
        reflexivity.
      }
      rewrite Ha, Hb in C.
      some_none.
    -
      assert(C: NM.find (elt:=CarrierA) k (Vfold_right_indexed' 0 mem_add x mem_empty)
                = NM.find (elt:=CarrierA) k (Vfold_right_indexed' 0 mem_add y mem_empty)).
      {
        rewrite H.
        reflexivity.
      }
      rewrite Ha, Hb in C.
      some_none.
  Qed.


  Ltac avector_to_mem_block_to_spec m H0 H1 :=
    match goal with
    | [ |- context[avector_to_mem_block_spec ?v]] =>
      pose proof (avector_to_mem_block_key_oob (v:=v)) as H1;
      unfold avector_to_mem_block in H1 ;
      destruct (avector_to_mem_block_spec v) as [m H0]

    | [ H: context[avector_to_mem_block_spec ?v] |- _] =>
      pose proof (avector_to_mem_block_key_oob (v:=v)) as H1;
      unfold avector_to_mem_block in H1 ;
      destruct (avector_to_mem_block_spec v) as [m H0]
    end.


  (* HOperator (on dense vector) mapping to memory operator *)
  Definition mem_op_of_hop {i o: nat} (op: vector CarrierA i -> vector CarrierA o)
    : mem_block -> option mem_block
    := fun x => match mem_block_to_avector x with
             | None => None
             | Some x' => Some (avector_to_mem_block (op x'))
             end.

  Lemma mem_out_some_mem_op_of_hop
        (i o : nat)
        {m: mem_block}
        (g : vector CarrierA i → vector CarrierA o)
        (H: forall (j : nat) (jc : j < i), Full_set (FinNat i) (mkFinNat jc) → mem_in j m):
    is_Some (mem_op_of_hop g m).
  Proof.
    unfold mem_op_of_hop.
    break_match.
    * simpl; tauto.
    *
      exfalso.
      rename Heqo0 into M.
      unfold mem_block_to_avector in M.
      apply vsequence_eq_None in M.
      destruct M as [j [jc M]].
      rewrite Vbuild_nth in M.
      specialize (H j jc).
      assert(P: Full_set (FinNat i) (mkFinNat jc)) by apply Full_intro.
      apply H in P.
      unfold mem_lookup, mem_in in *.
      apply NP.F.not_find_in_iff in M.
      congruence.
  Qed.

  (* The fomulation of this lemma is little odd, with `Full_set (FinNat o) (mkFinNat jc)`
     being always True. It is designed to match `mem_fill_pattern` field
     of `SHOperator_facts` typeclass for operators defined via `mem_op_of_hop` wrapper.
   *)
  Fact out_mem_fill_pattern_mem_op_of_hop
       {i o : nat}
       {g : vector CarrierA i → vector CarrierA o}
       {m0 m: mem_block}
    :
      (mem_op_of_hop g m0 ≡ Some m)
      ->
      ((∀ (j : nat) (jc : j < o), Full_set (FinNat o) (mkFinNat jc) <-> mem_in j m)
       ∧ (∀ j : nat, j ≥ o → ¬ mem_in j m)).
  Proof.
    intros H.
    unfold mem_op_of_hop in H.
    break_match_hyp; try some_none.
    some_inv.
    subst.
    rename Heqo0 into H.
    split; intros j jc.
    -
      split.
      +
        intros F.
        unfold avector_to_mem_block.
        avector_to_mem_block_to_spec m2 H2 O2.
        clear O2. simpl in *.
        specialize (H2 j jc).
        unfold mem_in, mem_lookup in *.
        apply NM.find_2, MapsTo_In in H2.
        apply H2.
      +
        intros I.
        apply Full_intro.
    -
      intros C.
      unfold avector_to_mem_block in C.
      avector_to_mem_block_to_spec m2 H2 O2.
      simpl in *.
      specialize (O2 j jc).
      unfold mem_in, mem_lookup in *.
      apply NP.F.not_find_in_iff in O2.
      congruence.
  Qed.

  Instance mem_op_of_hop_proper
           {i o: nat}:
    Proper (((=) ==> (=)) ==> (=)) (@mem_op_of_hop i o).
  Proof.
    intros a b E mx my Em.
    unfold mem_op_of_hop.
    repeat break_match;
      apply Option_equiv_eq in Heqo0;
      apply Option_equiv_eq in Heqo1;
      rewrite Em in Heqo0;
      rewrite Heqo0 in Heqo1.
    -
      some_inv.
      f_equiv.
      f_equiv.
      apply E.
      apply Heqo1.
    -
      some_none.
    -
      some_none.
    -
      reflexivity.
  Qed.


  (* y[j] := x[i] *)
  Definition map_mem_block_elt (x:mem_block) (i:nat) (y:mem_block) (j:nat)
    : option mem_block :=
    match mem_lookup i x with
    | None => None
    | Some v => Some (mem_add j v y)
    end.


  (* AKA: "embed" *)
  Definition Embed_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x 0 (mem_empty) b.

  (* AKA "pick" *)
  Definition Pick_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x b (mem_empty) 0.

  (** Apply family of mem functions to same mem_block and return list of results *)
  Definition Apply_mem_Family
             {n: nat}
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block) :
    option (list mem_block) :=
    monadic_Lbuild _ (λ (j:nat) (jc:j<n), (op_family_f j jc) x).

  Definition HTSUMUnion_mem
             (op1 op2: mem_block -> option mem_block)
    : mem_block -> option mem_block
    := fun x => (liftM2 mem_union) (op2 x) (op1 x).

  (* Old version *)
  Definition IReduction_mem'
             {n: nat}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block): option mem_block
    :=
      x' <- (Apply_mem_Family op_family_f x) ;;
         ret (fold_left_rev (mem_merge_with_def dot initial) mem_empty x').

  (* new version *)
  Definition IReduction_mem
             {n: nat}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block): option mem_block
    :=
      x' <- (Apply_mem_Family op_family_f x) ;;
         ret (List.fold_left (mem_merge_with_def dot initial) x' mem_empty).

  Definition IUnion_mem
             {n: nat}
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block): option mem_block
    :=
      x' <- (Apply_mem_Family op_family_f x) ;;
         ret (fold_left_rev mem_union mem_empty x').


  Instance mem_keys_set_proper:
    Proper ((=) ==> NS.Equal) (mem_keys_set).
  Proof.
    simpl_relation.
    rename H into E.
    rewrite <- 2!mem_keys_set_In.
    apply mem_in_proper; auto.
  Qed.

  Instance mem_union_proper:
    Proper (equiv ==> equiv ==> equiv) (mem_union).
  Proof.
    intros m0 m0' Em0 m1 m1' Em1.
    unfold mem_union.
    mem_index_equiv k.
    rewrite 2!NP.F.map2_1bis by auto.
    unfold equiv, mem_block_Equiv in Em0.
    unfold equiv, mem_block_Equiv in Em1.
    specialize (Em0 k).
    specialize (Em1 k).
    repeat break_match; try some_none; auto.
  Qed.


  Instance mem_merge_proper:
    Proper (equiv ==> equiv ==> equiv) (mem_merge).
  Proof.
    intros m0 m0' Em0 m1 m1' Em1.
    unfold mem_merge.
    repeat break_if; try some_none.
    -
      f_equiv.
      rewrite Em0, Em1.
      reflexivity.
    -
      unfold is_disjoint in *.
      rewrite Em0, Em1 in Heqb.
      congruence.
    -
      unfold is_disjoint in *.
      rewrite Em0, Em1 in Heqb.
      congruence.
  Qed.

  Instance mem_merge_with_proper
    : Proper ((equiv ==> equiv ==> equiv)
                ==> equiv ==> equiv ==> equiv) (mem_merge_with).
  Proof.
    intros f g Efg m0 m0' Em0 m1 m1' Em1.
    unfold mem_merge_with.
    unfold equiv, mem_block_Equiv in *.
    intros k.
    specialize (Em0 k).
    specialize (Em1 k).
    rewrite 2!NP.F.map2_1bis by auto.

    repeat break_match; try some_none; auto.
    repeat some_inv.
    f_equiv.
    apply Efg; auto.
  Qed.

  Instance mem_merge_with_def_proper
    : Proper ((equiv ==> equiv ==> equiv) ==> equiv ==> equiv ==> equiv ==> equiv) (mem_merge_with_def).
  Proof.
    intros f g Efg d d' Ed m0 m0' Em0 m1 m1' Em1.
    unfold mem_merge_with_def.
    unfold equiv, mem_block_Equiv in *.
    intros k.
    specialize (Em0 k).
    specialize (Em1 k).
    rewrite 2!NP.F.map2_1bis by auto.
    repeat break_match; try some_none; auto;
      repeat some_inv; f_equiv; try apply Efg; auto.
  Qed.

  Global Instance mem_merge_with_def_Comm
         (dot : CarrierA → CarrierA → CarrierA)
         (initial : CarrierA)
         (dot_commut: Commutative dot)
    : Commutative (mem_merge_with_def dot initial).
  Proof.
    intros x y k.
    unfold mem_merge_with_def.
    rewrite 2!NP.F.map2_1bis by reflexivity.
    repeat break_match; f_equiv; apply dot_commut.
  Qed.

  Global Instance mem_merge_with_def_Assoc
         (dot : CarrierA → CarrierA → CarrierA)
         (initial : CarrierA)

        `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
         (dot_assoc : Associative dot)
         (dot_left_id: LeftIdentity dot initial)
         (dot_right_id: RightIdentity dot initial)
    :
    Associative (mem_merge_with_def dot initial).
  Proof.
    intros x y z k.
    unfold Associative,HeteroAssociative in dot_assoc.
    unfold LeftIdentity in dot_left_id.
    unfold RightIdentity in dot_right_id.

    unfold mem_merge_with_def.
    rewrite 4!NP.F.map2_1bis by reflexivity.
    repeat break_match; try some_none;
      f_equiv; repeat some_inv; try apply dot_assoc.

    rewrite 2!dot_right_id; reflexivity.
    rewrite 2!dot_left_id; reflexivity.
  Qed.

  Lemma IReduction_mem_old_new
        {n: nat}
        `{dot: SgOp CarrierA}
        `{initial: MonUnit CarrierA}
        (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
        (x: mem_block)

        (* CM includes: Proper, left/right identity, commutativity, and associativity *)
        `{CM: @CommutativeMonoid _ _ dot initial}
    :
      IReduction_mem dot initial op_family_f x = IReduction_mem' dot initial op_family_f x.
  Proof.
    unfold IReduction_mem, IReduction_mem'.
    cbn.
    break_match; [|reflexivity].
    f_equiv.
    symmetry.
    apply fold_left_fold_left_rev_equiv.
    -
      apply mem_merge_with_def_proper; apply CM.
    -
      apply mem_merge_with_def_Comm, CM.
    -
      apply mem_merge_with_def_Assoc; apply CM.
  Qed.

  Instance Embed_mem_proper
           {b:nat}
    : Proper (equiv ==> equiv) (Embed_mem b).
  Proof.
    simpl_relation.
    unfold Embed_mem.
    unfold map_mem_block_elt.
    destruct_opt_r_equiv; repeat break_match; try some_none.
    -
      repeat some_inv.
      unfold mem_block_Equiv.
      intros k.
      unfold mem_lookup in *.
      destruct (eq_nat_dec k b).
      +
        rewrite 2!NP.F.add_eq_o by auto.
        rewrite <- Heqo0, <- Heqo.
        rewrite H.
        reflexivity.
      +
        rewrite 2!NP.F.add_neq_o by auto.
        reflexivity.
    -
      some_inv.
      assert(C: mem_lookup 0 x = mem_lookup 0 y).
      {
        rewrite H.
        reflexivity.
      }
      rewrite Heqo0, Heqo in C.
      some_none.
    -
      some_inv.
      assert(C: mem_lookup 0 x = mem_lookup 0 y).
      {
        rewrite H.
        reflexivity.
      }
      rewrite Heqo0, Heqo in C.
      some_none.
  Qed.

  Instance Pick_mem_proper
           {b:nat}
    : Proper (equiv ==> equiv) (Pick_mem b).
  Proof.
    simpl_relation.
    unfold Pick_mem.
    unfold map_mem_block_elt.
    destruct_opt_r_equiv; repeat break_match; try some_none.
    -
      repeat some_inv.
      unfold mem_block_Equiv.
      intros k.
      unfold mem_lookup in *.
      destruct (eq_nat_dec k 0).
      +
        rewrite 2!NP.F.add_eq_o by auto.
        rewrite <- Heqo0, <- Heqo.
        rewrite H.
        reflexivity.
      +
        rewrite 2!NP.F.add_neq_o by auto.
        reflexivity.
    -
      some_inv.
      assert(C: mem_lookup b x = mem_lookup b y).
      {
        rewrite H.
        reflexivity.
      }
      rewrite Heqo0, Heqo in C.
      some_none.
    -
      some_inv.
      assert(C: mem_lookup b x = mem_lookup b y).
      {
        rewrite H.
        reflexivity.
      }
      rewrite Heqo0, Heqo in C.
      some_none.
  Qed.

  Instance HTSUMUnion_mem_proper:
    Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> equiv ==> equiv) (HTSUMUnion_mem).
  Proof.
    intros op0 op0' Eop0 op1 op1' Eop1 x y E.
    specialize (Eop0 x y E).
    specialize (Eop1 x y E).
    unfold HTSUMUnion_mem.
    repeat break_match; try some_none; try reflexivity.
    repeat some_inv.
    simpl.
    repeat break_match; try some_none.
    f_equiv.
    apply mem_union_proper; apply Some_inj_equiv; auto.
  Qed.

  Record MSHOperator {i o: nat} : Type
    := mkMSHOperator {
           (* -- implementation on memory blocks -- *)
           mem_op: mem_block -> option mem_block;
           mem_op_proper: Proper ((=) ==> (=)) mem_op;

           m_in_index_set: FinNatSet i;
           m_out_index_set: FinNatSet o;
         }.

  Class MSHOperator_Facts
        {i o: nat}
        (mop: @MSHOperator i o)
    :=
      {
        (* -- Structural properties for [mem_op] -- *)

        (* sufficiently (values in right places, no info on empty
         spaces) filled input memory block guarantees that `mem_op`
         will not fail.  *)
        mem_out_some: forall m,
          (forall j (jc:j<i), m_in_index_set mop (mkFinNat jc) -> mem_in j m)
          ->
          is_Some (mem_op mop m);

        (* Output memory block always have values in right places, and
             does not have value in sparse positions *)
        out_mem_fill_pattern: forall m0 m,
            mem_op mop m0 ≡ Some m
            ->
            forall j (jc:j<o), m_out_index_set mop (mkFinNat jc) <-> mem_in j m;

        (* Do not write memory outside of bounds *)
        out_mem_oob: forall m0 m,
            mem_op mop m0 ≡ Some m -> forall j (jc:j>=o), not (mem_in j m);
      }.


  Definition MSHOperatorFamily {i o n: nat} := FinNat n -> @MSHOperator i o.

  Definition cast_m_op_family
             {i o n m: nat}
             (op_family: @MSHOperatorFamily i o m)
             (E: m≡n)
    :
      @MSHOperatorFamily i o n
    :=
      match E in _ ≡ p return (@MSHOperatorFamily i o p) with
      | eq_refl => op_family
      end.

  Lemma cast_mem_op_eq
        {i o n m : nat}
        (t t': nat)
        (Et: t ≡ t')
        {tm: t<m}
        {tn: t'<n}
        {op_family: @MSHOperatorFamily i o m}
        (E: m≡n)
    :
      (mem_op (cast_m_op_family op_family E (mkFinNat tn)))
        ≡ (mem_op  (op_family (mkFinNat tm))).
  Proof.
    subst.
    replace tm with tn by apply NatUtil.lt_unique.
    reflexivity.
  Qed.

  Lemma cast_m_out_index_set_eq
        {i o n m : nat}
        (t: nat)
        {tm: t<m}
        {tn: t<n}
        {op_family: @MSHOperatorFamily i o m}
        (E: m≡n)
    :
      m_out_index_set (op_family (mkFinNat tm))
                      ≡
                      m_out_index_set
                      (cast_m_op_family op_family E (mkFinNat tn)).
  Proof.
    subst.
    replace tm with tn by apply NatUtil.lt_unique.
    reflexivity.
  Qed.

  Lemma cast_m_in_index_set_eq
        {i o n m : nat}
        (t: nat)
        {tm: t<m}
        {tn: t<n}
        {op_family: @MSHOperatorFamily i o m}
        (E: m≡n)
    :
      m_in_index_set (op_family (mkFinNat tm))
                     ≡
                     m_in_index_set (cast_m_op_family op_family E (mkFinNat tn)).
  Proof.
    subst.
    replace tm with tn by apply NatUtil.lt_unique.
    reflexivity.
  Qed.

  Definition get_family_mem_op
             {i o n: nat}
             (op_family: @MSHOperatorFamily i o n)
    : forall j (jc:j<n), mem_block -> option mem_block
    := fun j (jc:j<n) => mem_op (op_family (mkFinNat jc)).

  Instance get_family_mem_op_proper
           {i o n: nat}
           (j: nat) (jc: j<n)
           (op_family: @MSHOperatorFamily i o n)
    :
      Proper ((=) ==> (=)) (get_family_mem_op op_family j jc).
  Proof.
    intros x y E.
    unfold get_family_mem_op.
    apply mem_op_proper, E.
  Qed.

  Lemma Apply_mem_Family_length
        {i o k: nat}
        {op_family: @MSHOperatorFamily i o k}
        {m: mem_block}
        {l: list mem_block}
    :
      Apply_mem_Family (get_family_mem_op op_family) m ≡ Some l ->
      length l = k.
  Proof.
    unfold Apply_mem_Family.
    apply monadic_Lbuild_opt_length.
  Qed.

  Lemma Apply_mem_Family_eq_Some
        {i o k : nat}
        {op_family: @MSHOperatorFamily i o k}
        {m : NatMap CarrierA}
        {l: list mem_block}
    :
      (Apply_mem_Family (get_family_mem_op op_family) m ≡ Some l)
      -> (forall (j : nat) (jc : j < k), List.nth_error l j ≡ get_family_mem_op op_family j jc m).
  Proof.
    unfold Apply_mem_Family.
    apply monadic_Lbuild_op_eq_Some.
  Qed.

  (* Shrink family by removing the last member *)
  Definition shrink_m_op_family
             {i o n}
             (op_family: @MSHOperatorFamily i o (S n)): @MSHOperatorFamily i o n := fun jf => op_family (mkFinNat (@le_S (S (proj1_sig jf)) n (proj2_sig jf))).

  Fixpoint m_family_in_index_set
           {i o n}
           (op_family: @MSHOperatorFamily i o n): FinNatSet i
    :=
      match n as y return (y ≡ n -> @MSHOperatorFamily i o y -> FinNatSet i) with
      | O => fun _ _ => (Empty_set _)
      | S j => fun E f => Ensembles.Union _
                                          (m_in_index_set (op_family (mkFinNat (S_j_lt_n E))))
                                          (m_family_in_index_set (shrink_m_op_family f))
      end (eq_refl n) op_family.

  (* Shrink family by removing first memeber *)
  Definition shrink_m_op_family_up
             {i o n}
             (op_family: @MSHOperatorFamily i o (S n)): @MSHOperatorFamily i o n
    := fun jf => op_family (mkFinNat (lt_n_S (proj2_sig jf))).

  Definition shrink_m_op_family_up_n
             {i o n: nat}
             (d: nat)
             (op_family: @MSHOperatorFamily i o (n+d)): @MSHOperatorFamily i o n
    := fun jf => op_family (mkFinNat
                              (Plus.plus_lt_compat_r _ _ _ (proj2_sig jf))).

  Definition shrink_m_op_family_facts
             {i o k : nat}
             (op_family : MSHOperatorFamily )
             (facts: ∀ (j : nat) (jc : j < S k),
                 @MSHOperator_Facts i o (op_family (mkFinNat jc))):
    (forall (j : nat) (jc : j < k),
        @MSHOperator_Facts i o ((shrink_m_op_family op_family) (mkFinNat jc)))
    := fun j jc => facts j (le_S jc).

  Definition shrink_m_op_family_facts_up
             {i o k : nat}
             (op_family : MSHOperatorFamily)
             (facts: ∀ (j : nat) (jc : j < S k),
                 @MSHOperator_Facts i o (op_family (mkFinNat jc))):
    (forall (j : nat) (jc : j < k),
        @MSHOperator_Facts i o ((shrink_m_op_family_up op_family) (mkFinNat jc)))
    := fun j jc => facts (S j) (lt_n_S jc).

  Definition shrink_m_op_family_facts_up_n
             {i o k: nat}
             (d: nat)
             (op_family : MSHOperatorFamily)
             (facts: ∀ (j : nat) (jc : j < (k+d)),
                 @MSHOperator_Facts i o (op_family (mkFinNat jc)))
    :
      (forall (j : nat) (jc : j < k),
          @MSHOperator_Facts i o
                             ((shrink_m_op_family_up_n d op_family) (mkFinNat jc))
      )
    := fun j jc => facts (j+d) (Plus.plus_lt_compat_r _ _ _ jc).

  Lemma cast_m_op_family_facts
        {i o n m: nat}
        {op_family: @MSHOperatorFamily i o m}
        (op_family_facts : forall (j: nat) (jc: j < m),
            MSHOperator_Facts
              (op_family (mkFinNat jc)))
        (E: m≡n):
    forall (j : nat) (jc : j < n),
      MSHOperator_Facts (cast_m_op_family op_family E (mkFinNat jc)).
  Proof.
    intros j jc.
    crush.
    (* TODO: better proof. *)
  Defined.

  Lemma Apply_mem_Family_cons
        {i o k: nat}
        (op_family: @MSHOperatorFamily i o (S k))
        (m m0:mem_block)
        (ms: list mem_block)
    :
      Apply_mem_Family (get_family_mem_op op_family) m ≡ Some (List.cons m0 ms) ->
      get_family_mem_op op_family _ (Nat.lt_0_succ k) m ≡ Some m0 /\
      Apply_mem_Family (
          get_family_mem_op
            (shrink_m_op_family_up op_family)
        ) m ≡ Some ms.
  Proof.
    intros H.
    unfold Apply_mem_Family in H.
    rewrite monadic_Lbuild_cons in H.
    unfold liftM2 in H.
    simpl in H.
    repeat break_match_hyp; try some_none.
    inversion H.
    subst.
    auto.
  Qed.

  (* Alternative definitoin of [family_in_index_set], shrinking up. Good for induction on n *)
  Fixpoint m_family_in_index_set'
           {i o n}
           (op_family: @MSHOperatorFamily i o n): FinNatSet i
    :=
      match n as y return (y ≡ n -> @MSHOperatorFamily i o y -> FinNatSet i) with
      | O => fun _ _ => (Empty_set _)
      | S j => fun E f => Ensembles.Union _
                                          (m_in_index_set (op_family (mkFinNat (S_j_lt_0 E))))
                                          (m_family_in_index_set' (shrink_m_op_family_up f))
      end (eq_refl n) op_family.

  Lemma m_family_in_set_includes_members:
    forall (i o k : nat)
           (op_family : @MSHOperatorFamily i o k)
           (j : nat) (jc : j < k),
      Included (FinNat i)
               (m_in_index_set (op_family (mkFinNat jc)))
               (m_family_in_index_set op_family).
  Proof.
    intros i o k op_family j jc.
    unfold Included.
    intros x H.

    induction k.
    - inversion jc.
    -
      simpl.
      destruct (eq_nat_dec j k) as [E | NE].
      +
        left.
        subst.
        replace (S_j_lt_n _) with jc by apply NatUtil.lt_unique.
        apply H.
      +
        right.
        assert(jc1: j<k) by omega.
        apply IHk with (jc:=jc1). clear IHk.
        unfold shrink_m_op_family, mkFinNat, proj2_sig in *.
        simpl in *.
        replace (le_S jc1) with jc by apply NatUtil.lt_unique.
        apply H.
  Qed.

  Lemma m_family_in_set'_includes_members:
    forall (i o k : nat)
           (op_family : @MSHOperatorFamily i o k)
           (j : nat) (jc : j < k),
      Included (FinNat i)
               (m_in_index_set (op_family (mkFinNat jc)))
               (m_family_in_index_set' op_family).
  Proof.
    intros i o k op_family j jc.
    intros x H.

    dependent induction k.
    - inversion jc.
    -
      simpl.
      destruct (eq_nat_dec j 0) as [E | NE].
      +
        left.
        subst.
        replace (zero_lt_Sn k) with jc by apply NatUtil.lt_unique.
        apply H.
      +
        right.
        dep_destruct j.
        congruence.
        assert(jc1: x0<k) by omega.
        unshelve eapply IHk with (jc:=jc1).
        unfold shrink_m_op_family_up, mkFinNat, proj2_sig in *.
        simpl in *.
        replace (lt_n_S jc1) with jc by apply NatUtil.lt_unique.
        eapply H.
  Qed.


  Lemma m_family_in_set_implies_members
        (i o k : nat)
        (op_family : @MSHOperatorFamily i o k)
        (j : nat) (jc : j < i):

    m_family_in_index_set op_family (mkFinNat jc) ->
    ∃ (t : nat) (tc : t < k),
      m_in_index_set (op_family (mkFinNat tc))
                     (mkFinNat jc).
  Proof.
    intros H.
    induction k.
    -
      inversion H.
    -
      simpl in H.
      inversion_clear H as [H0 | H1].
      +
        unfold Ensembles.In in H1.
        exists k, (le_n (S k)).
        replace (le_n (S k)) with (@S_j_lt_n (S k) k (@eq_refl nat (S k)))
          by apply NatUtil.lt_unique.
        apply H1.
      +
        specialize (IHk (shrink_m_op_family op_family) H0).
        destruct IHk as [t [tc  IHk]].
        exists t.
        assert(tc1: t < S k) by omega.
        exists tc1.

        unfold shrink_m_op_family, mkFinNat, proj2_sig.
        simpl in *.
        replace tc1 with (le_S tc)
          by apply NatUtil.lt_unique.
        apply IHk.
  Qed.

  Lemma m_family_in_set'_implies_members
        (i o k : nat)
        (op_family : @MSHOperatorFamily i o k)
        (j : nat) (jc : j < i):

    m_family_in_index_set' op_family (mkFinNat jc) ->
    ∃ (t : nat) (tc : t < k),
      m_in_index_set (op_family (mkFinNat tc))
                     (mkFinNat jc).
  Proof.
    intros H.
    induction k.
    -
      inversion H.
    -
      simpl in H.
      inversion_clear H as [H0 | H1].
      +
        exists 0.
        exists (zero_lt_Sn k).
        apply H1.
      +
        specialize (IHk (shrink_m_op_family_up op_family) H0).
        destruct IHk as [t [tc  IHk]].
        exists (S t).
        assert(tc1: S t < S k) by omega.
        exists tc1.

        unfold shrink_m_op_family_up, mkFinNat, proj2_sig in IHk.
        simpl in *.
        replace tc1 with (lt_n_S tc)
          by apply NatUtil.lt_unique.
        apply IHk.
  Qed.

  Lemma m_family_in_index_set_eq
        {i o n}
        (op_family: @MSHOperatorFamily i o n)
    :
      m_family_in_index_set op_family ≡ m_family_in_index_set' op_family.
  Proof.
    dependent induction n.
    +
      simpl.
      reflexivity.
    +
      apply Extensionality_Ensembles.
      simpl.
      split.
      *
        generalize (@S_j_lt_n (S n) n (@eq_refl nat (S n))), (zero_lt_Sn n).
        intros nc zc.
        intros x H.
        destruct H.
        --
          (* last *)
          destruct n.
          ++
            left.
            replace zc with nc by apply NatUtil.lt_unique.
            apply H.
          ++
            right.
            rewrite <- IHn; clear IHn.
            assert(nc1: n < S n) by lia.
            apply (m_family_in_set_includes_members _ _ _ (shrink_m_op_family_up op_family) _ nc1).
            unfold shrink_m_op_family_up.
            simpl.
            replace (lt_n_S nc1) with nc by apply le_unique.
            apply H.
        --
          (* all but last *)
          clear nc.
          unfold Ensembles.In in H.
          destruct x as [x xc].
          apply m_family_in_set_implies_members in H.
          destruct H as [t [tc H]].

          destruct (eq_nat_dec t 0).
          ++
            subst.
            left.
            unfold Ensembles.In.
            unfold shrink_m_op_family in H.
            simpl in H.
            replace zc with (le_S tc) by apply NatUtil.lt_unique.
            apply H.
          ++
            right; clear zc.
            destruct t.
            congruence.

            rewrite <- IHn.
            assert(tc1: t<n) by omega.
            apply (m_family_in_set_includes_members _ _ _
                                                    (shrink_m_op_family_up op_family) _
                                                    tc1).
            unfold mkFinNat.
            unfold shrink_m_op_family_up.
            simpl.
            unfold shrink_m_op_family in H.
            simpl in H.
            replace (lt_n_S tc1) with (le_S tc) by apply NatUtil.lt_unique.
            apply H.
      *
        generalize (@S_j_lt_n (S n) n (@eq_refl nat (S n))), (zero_lt_Sn n).
        intros nc zc.
        intros x H.
        destruct H.
        --
          (* first *)
          destruct n.
          ++
            left.
            replace nc with zc by apply NatUtil.lt_unique.
            apply H.
          ++
            right.
            assert(zc1: 0 < S n) by lia.
            apply m_family_in_set_includes_members with (jc:=zc1).
            unfold shrink_m_op_family.
            simpl.
            replace (le_S zc1) with zc by apply le_unique.
            apply H.
        --
          (* all but first *)
          clear zc.
          destruct x as [x xc].
          apply m_family_in_set'_implies_members in H.
          destruct H as [t [tc H]].

          unfold shrink_m_op_family_up in H.
          simpl in H.
          destruct (eq_nat_dec (S t) n).
          ++
            left.
            subst.
            simpl in H.
            replace nc with (lt_n_S tc) by apply NatUtil.lt_unique.
            apply H.
          ++
            (* H: not first, nor last *)
            right.
            rewrite IHn.
            assert(tc1: S t < n) by omega.
            eapply m_family_in_set'_includes_members with (jc:=tc1).
            unfold shrink_m_op_family.
            simpl.
            replace (mkFinNat (le_S tc1)) with (mkFinNat (lt_n_S tc)).
            apply H.
            f_equiv.
            apply NatUtil.lt_unique.
  Qed.

  Fixpoint m_family_out_index_set
           {i o n}
           (op_family: @MSHOperatorFamily i o n): FinNatSet o
    :=
      match n as y return (y ≡ n -> @MSHOperatorFamily i o y -> FinNatSet o) with
      | O => fun _ _ => (Empty_set _)
      | S j => fun E f => Ensembles.Union _
                                          (m_out_index_set (op_family (mkFinNat (S_j_lt_n E))))
                                          (m_family_out_index_set (shrink_m_op_family f))
      end (eq_refl n) op_family.


  (* A version of [family_out_index_set] which uses [shrink_op_family_up] instead of
       [shrink_op_family]. This one is more suitable for inductive proofs *)
  Fixpoint m_family_out_index_set'
           {i o n}
           (op_family: @MSHOperatorFamily i o n): FinNatSet o
    :=
      match n as y return (y ≡ n -> @MSHOperatorFamily i o y -> FinNatSet o) with
      | O => fun _ _ => (Empty_set _)
      | S j => fun E f => Ensembles.Union _
                                          (m_out_index_set (op_family (mkFinNat (S_j_lt_0 E))))
                                          (m_family_out_index_set' (shrink_m_op_family_up f))
      end (eq_refl n) op_family.

  Lemma m_family_out_set_includes_members:
    ∀ (i o k : nat)
      (op_family : @MSHOperatorFamily i o k)
      (j : nat) (jc : j < k),
      Included (FinNat o)
               (m_out_index_set (op_family (mkFinNat jc)))
               (m_family_out_index_set op_family).
  Proof.
    intros i o k op_family j jc.
    unfold Included, Ensembles.In.
    intros x H.

    induction k.
    - inversion jc.
    -
      simpl.
      destruct (eq_nat_dec j k) as [E | NE].
      +
        left.
        subst.
        replace (S_j_lt_n _) with jc
          by apply NatUtil.lt_unique.
        apply H.
      +
        right.
        assert(jc1: j<k) by omega.
        apply IHk with (jc:=jc1).
        unfold shrink_m_op_family, mkFinNat, proj2_sig.
        simpl in *.
        replace (le_S jc1) with jc
          by apply NatUtil.lt_unique.
        apply H.
  Qed.

  Lemma m_family_out_set'_includes_members:
    ∀ (i o k : nat)
      (op_family : @MSHOperatorFamily i o k)
      (j : nat) (jc : j < k),
      Included (FinNat o)
               (m_out_index_set (op_family (mkFinNat jc)))
               (m_family_out_index_set' op_family).
  Proof.
    intros i o k op_family j jc.
    unfold Included, Ensembles.In.
    intros x H.

    dependent induction k.
    - inversion jc.
    -
      simpl.
      destruct (eq_nat_dec j 0) as [E | NE].
      +
        left.
        subst.
        replace (zero_lt_Sn k) with jc by apply NatUtil.lt_unique.
        apply H.
      +
        right.
        dep_destruct j.
        congruence.
        assert(jc1: x0<k) by omega.
        unshelve eapply IHk with (jc:=jc1).
        unfold shrink_m_op_family_up, mkFinNat, proj2_sig in *.
        simpl in *.
        replace (lt_n_S jc1) with jc by apply NatUtil.lt_unique.
        eapply H.
  Qed.

  Lemma m_family_out_set_implies_members
        (i o k : nat)
        (op_family : @MSHOperatorFamily i o k)
        (j : nat) (jc : j < o):

    m_family_out_index_set op_family (mkFinNat jc) <->
    ∃ (t : nat) (tc : t < k),
      m_out_index_set (op_family (mkFinNat tc))
                      (mkFinNat jc).
  Proof.
    split.
    - intros H.
      induction k.
      +
        inversion H.
      +
        simpl in H.
        inversion_clear H as [H0 | H1].
        *
          subst.
          unfold Ensembles.In in H1.
          exists k, (le_n (S k)).
          replace (S_j_lt_n _) with (le_n (S k)) in H1 by apply le_unique.
          apply H1.
        *
          subst.
          specialize (IHk (shrink_m_op_family op_family) H0).
          destruct IHk as [t [tc  IHk]].
          exists t.
          assert(tc1: t < S k) by omega.
          exists tc1.

          unfold shrink_m_op_family, mkFinNat, proj2_sig in *.
          simpl in *.
          replace (le_S tc) with tc1 in IHk by apply le_unique.
          apply IHk.
    -
      intros H.
      destruct H as [x [xc H]].
      apply m_family_out_set_includes_members in H.
      auto.
  Qed.

  Lemma m_family_out_set'_implies_members
        (i o k : nat)
        (op_family : @MSHOperatorFamily i o k)
        (j : nat) (jc : j < o):

    m_family_out_index_set' op_family (mkFinNat jc) ->
    ∃ (t : nat) (tc : t < k),
      m_out_index_set (op_family (mkFinNat tc))
                      (mkFinNat jc).
  Proof.
    intros H.
    induction k.
    -
      inversion H.
    -
      simpl in H.
      inversion_clear H as [H0 | H1].
      +
        exists 0.
        exists (zero_lt_Sn k).
        apply H1.
      +
        specialize (IHk (shrink_m_op_family_up op_family) H0).
        destruct IHk as [t [tc  IHk]].
        exists (S t).
        assert(tc1: S t < S k) by omega.
        exists tc1.

        unfold shrink_m_op_family_up, mkFinNat, proj2_sig in IHk.
        simpl in *.
        replace tc1 with (lt_n_S tc)
          by apply NatUtil.lt_unique.
        apply IHk.
  Qed.


  Lemma m_family_out_index_set_eq
        {i o n}
        (op_family: @MSHOperatorFamily i o n)
    :
      m_family_out_index_set op_family ≡ m_family_out_index_set' op_family.
  Proof.
    dependent induction n.
    +
      simpl.
      reflexivity.
    +
      apply Extensionality_Ensembles.
      simpl.
      split.
      *
        generalize (@S_j_lt_n (S n) n (@eq_refl nat (S n))), (zero_lt_Sn n).
        intros nc zc.
        intros x H.
        destruct H.
        --
          (* last *)
          destruct n.
          ++
            left.
            replace zc with nc by apply NatUtil.lt_unique.
            apply H.
          ++
            right.
            rewrite <- IHn; clear IHn.
            assert(nc1: n < S n) by lia.
            apply (m_family_out_set_includes_members _ _ _
                                                     (shrink_m_op_family_up op_family) _
                                                     nc1).
            unfold shrink_m_op_family_up.
            simpl.
            replace (lt_n_S nc1) with nc by apply le_unique.
            apply H.
        --
          (* all but last *)
          clear nc.
          unfold Ensembles.In in H.
          destruct x as [x xc].
          apply m_family_out_set_implies_members in H.
          destruct H as [t [tc H]].

          destruct (eq_nat_dec t 0).
          ++
            subst.
            left.
            unfold Ensembles.In.
            unfold shrink_m_op_family in H.
            simpl in H.
            replace zc with (le_S tc) by apply NatUtil.lt_unique.
            apply H.
          ++
            right; clear zc.
            destruct t.
            congruence.
            rewrite <- IHn.
            assert(tc1: t<n) by omega.
            apply (m_family_out_set_includes_members _ _ _
                                                     (shrink_m_op_family_up op_family) _
                                                     tc1).
            unfold mkFinNat.
            unfold shrink_m_op_family_up.
            simpl.
            unfold shrink_m_op_family in H.
            simpl in H.
            replace (lt_n_S tc1) with (le_S tc) by apply NatUtil.lt_unique.
            apply H.
      *
        generalize (@S_j_lt_n (S n) n (@eq_refl nat (S n))), (zero_lt_Sn n).
        intros nc zc.
        intros x H.
        destruct H.
        --
          (* first *)
          destruct n.
          ++
            left.
            replace nc with zc by apply NatUtil.lt_unique.
            apply H.
          ++
            right.
            assert(zc1: 0 < S n) by lia.
            apply m_family_out_set_includes_members with (jc:=zc1).
            unfold shrink_m_op_family.
            simpl.
            replace (le_S zc1) with zc by apply le_unique.
            apply H.
        --
          (* all but first *)
          clear zc.
          destruct x as [x xc].
          apply m_family_out_set'_implies_members in H.
          destruct H as [t [tc H]].

          unfold shrink_m_op_family_up in H.
          simpl in H.
          destruct (eq_nat_dec (S t) n).
          ++
            left.
            subst.
            simpl in H.
            replace nc with (lt_n_S tc) by apply NatUtil.lt_unique.
            apply H.
          ++
            (* H: not first, nor last *)
            right.
            rewrite IHn.
            assert(tc1: S t < n) by omega.
            eapply m_family_out_set'_includes_members with (jc:=tc1).
            unfold shrink_m_op_family.
            simpl.
            replace (mkFinNat (le_S tc1)) with (mkFinNat (lt_n_S tc)).
            apply H.
            f_equiv.
            apply NatUtil.lt_unique.
  Qed.

  (* Note: We only define MSHCOL operators for final subset of SHCOL *)

  Program Definition MSHCompose
          {i1 o2 o3}
          (mop1: @MSHOperator o2 o3)
          (mop2: @MSHOperator i1 o2)
    := @mkMSHOperator i1 o3
                      (option_compose (mem_op mop1)
                                      (mem_op mop2))
                      _
                      (m_in_index_set mop2)
                      (m_out_index_set mop1).
  Next Obligation.
    apply option_compose_proper; [ apply mop1 | apply mop2].
  Qed.

  Definition MSHPointwise
             {n: nat}
             (f: FinNat n -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    := @mkMSHOperator n n
                      (mem_op_of_hop (HPointwise f))
                      _
                      (Full_set _)
                      (Full_set _).

  Definition MSHEmbed
             {o b: nat}
             (bc: b < o)
    := @mkMSHOperator 1 o
                      (Embed_mem b)
                      Embed_mem_proper
                      (Full_set _)
                      (FinNatSet.singleton b).

  Definition MSHPick
             {i b: nat}
             (bc: b < i)
    := @mkMSHOperator i 1 (Pick_mem b)
                      Pick_mem_proper
                      (FinNatSet.singleton b)
                      (Full_set _).

  Definition MSHBinOp
             {o: nat}
             (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    := @mkMSHOperator (o+o) o
                      (mem_op_of_hop (HBinOp f))
                      _
                      (Full_set _)
                      (Full_set _).

  Definition Inductor_mem
             (n:nat)
             (f: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA):
             mem_block -> option mem_block
    :=
      match n with
      | O => fun _ =>
              (* For [n=0] it always succeeds and do not event attempt
                 to read input vector *)
              Some (avector_to_mem_block (Lst initial))
      | _ => mem_op_of_hop (HInductor n f initial)
      end.

  Global Instance Inductor_mem_proper
         (n:nat)
         (f: CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=)) f}
         (initial: CarrierA)
    :
      Proper (equiv ==> equiv) (Inductor_mem n f initial).
  Proof.
    destruct n.
    -
      cbn.
      simpl_relation.
    -
      cbn.
      typeclasses eauto.
  Qed.

  Definition MSHInductor
             (n:nat)
             (f: CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (initial: CarrierA)
    := @mkMSHOperator 1 1
                      (Inductor_mem n f initial)
                      _
                      (Full_set _)
                      (Full_set _).

  Program Definition MHTSUMUnion {i o}
          (dot: CarrierA -> CarrierA -> CarrierA)
          (* Surprisingly, the following is not required:
                `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot} *)
          (mop1 mop2: @MSHOperator i o)
    :=
      @mkMSHOperator i o
                     (HTSUMUnion_mem (mem_op mop1) (mem_op mop2))
                     _
                     (Ensembles.Union _ (m_in_index_set mop1) (m_in_index_set mop2))
                     (Ensembles.Union _ (m_out_index_set mop1) (m_out_index_set mop2)).
  Next Obligation.
    apply HTSUMUnion_mem_proper; [apply mop1 | apply mop2].
  Qed.

  (* Probably could be proven more generally for any monad with with some properties *)
  Instance monadic_Lbuild_opt_proper
           {A: Type}
           `{Ae: Equiv A}
           `{Equivalence A Ae}
           (n : nat):
    Proper ((forall_relation
               (fun i => pointwise_relation (i < n)%nat equiv)) ==> equiv) (@monadic_Lbuild A option OptionMonad.Monad_option n).
  Proof.
    intros f g E.
    unfold forall_relation, pointwise_relation in E.
    revert E.
    dependent induction n.
    -
      reflexivity.
    -
      intros E.
      simpl in *.

      match goal with
        [|- match ?a with  _ => _ end  = match ?b with  _ => _ end]
        => destruct a eqn:MA ,b eqn:MB
      end; try some_none;
        pose E as C;
        specialize (C 0 (Nat.lt_0_succ n));
        setoid_rewrite MA in C;
        setoid_rewrite MB in C;
        try some_none.

      match goal with
        [|- match ?a with  _ => _ end  = match ?b with  _ => _ end]
        => destruct a eqn:FA ,b eqn:FB
      end; try some_none;

        match goal with
        | [FA: monadic_Lbuild _ ?f ≡ _,
               FB: monadic_Lbuild _ ?g ≡ _
           |- _] => specialize (IHn f g)
        end;
        rewrite FA,FB in IHn.
      +
        f_equiv.
        constructor.
        *
          some_inv;apply C.
        *
          apply Some_inj_equiv.
          apply IHn.
          intros a1 a2.
          apply E.
      +
        assert(P: (forall (a : nat) (a0 : a < n),
                      f (S a)
                        (strictly_order_preserving S a n a0) =
                      g (S a)
                        (strictly_order_preserving S a n a0))).
        {
          intros a1 a2.
          apply E.
        }
        specialize (IHn P).
        some_none.
      +
        assert(P: (forall (a : nat) (a0 : a < n),
                      f (S a) (strictly_order_preserving S a n a0)
                      =
                      g (S a) (strictly_order_preserving S a n a0))).
        {
          intros a1 a2.
          apply E.
        }
        specialize (IHn P).
        some_none.
  Qed.

  Instance Apply_mem_Family_proper
           {i o n: nat}
           (op_family: @MSHOperatorFamily i o n)
    :
      Proper ((=) ==> (=)) (Apply_mem_Family (get_family_mem_op op_family)).
  Proof.
    intros x y E.
    unfold Apply_mem_Family.
    apply monadic_Lbuild_opt_proper.
    intros j jc.
    rewrite E.
    reflexivity.
  Qed.

  Instance IReduction_mem_proper
           {i o n: nat}
           (initial: CarrierA)
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           (op_family: @MSHOperatorFamily i o n)
    :
      Proper (equiv ==> equiv) (IReduction_mem dot initial (get_family_mem_op op_family)).
  Proof.
    intros x y E.
    unfold IReduction_mem.
    simpl.
    repeat break_match.
    -
      f_equiv.
      apply Option_equiv_eq in Heqo0.
      apply Option_equiv_eq in Heqo1.
      rewrite E in Heqo0.
      rewrite Heqo0 in Heqo1.
      some_inv.
      rewrite Heqo1.
      reflexivity.
    -
      apply Option_equiv_eq in Heqo0.
      apply Option_equiv_eq in Heqo1.
      rewrite E in Heqo0.
      rewrite Heqo0 in Heqo1.
      some_none.
    -
      apply Option_equiv_eq in Heqo0.
      apply Option_equiv_eq in Heqo1.
      rewrite E in Heqo0.
      rewrite Heqo0 in Heqo1.
      some_none.
    -
      reflexivity.
  Qed.

  Definition MSHIReduction
             {i o n: nat}
             (initial: CarrierA)
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (op_family: @MSHOperatorFamily i o n)
    :=
      @mkMSHOperator i o
                     (IReduction_mem dot initial (get_family_mem_op op_family))
                     (IReduction_mem_proper initial dot op_family)
                     (m_family_in_index_set op_family)
                     (m_family_out_index_set op_family) (* All scatters must be [Full_set] but we do not enforce it here. However if they are the same, the union will equal to any of them, so it is legit to use union here *).


  Instance IUnion_mem_proper
           {i o n: nat}
           (op_family: @MSHOperatorFamily i o n)
    :
      Proper (equiv ==> equiv) (IUnion_mem (get_family_mem_op op_family)).
  Proof.
    intros x y E.
    unfold IUnion_mem.
    simpl.
    repeat break_match.
    -
      f_equiv.
      apply fold_left_rev_proper.
      apply mem_union_proper.
      apply Some_inj_equiv.
      rewrite <- Heqo0, <- Heqo1.
      rewrite E.
      reflexivity.
    -
      apply Option_equiv_eq in Heqo0.
      apply Option_equiv_eq in Heqo1.
      rewrite E in Heqo0.
      rewrite Heqo0 in Heqo1.
      some_none.
    -
      apply Option_equiv_eq in Heqo0.
      apply Option_equiv_eq in Heqo1.
      rewrite E in Heqo0.
      rewrite Heqo0 in Heqo1.
      some_none.
    -
      reflexivity.
  Qed.

  Definition MSHIUnion
             {i o n: nat}
             (op_family: @MSHOperatorFamily i o n)
    :=
      @mkMSHOperator i o
                     (IUnion_mem (get_family_mem_op op_family))
                     (IUnion_mem_proper op_family)
                     (m_family_in_index_set op_family)
                     (m_family_out_index_set op_family).



  Instance SHCompose_MFacts
           {i1 o2 o3: nat}
           (op1: @MSHOperator o2 o3)
           (op2: @MSHOperator i1 o2)
           (compat: Included _ (m_in_index_set op1) (m_out_index_set op2))
           `{Mfacts1: !MSHOperator_Facts op1}
           `{Mfacts2: !MSHOperator_Facts op2}
    : MSHOperator_Facts
        (MSHCompose op1 op2).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros m H.
      unfold is_Some, option_compose in *.
      simpl in *.
      unfold option_compose.
      repeat break_match; try some_none; try auto.
      +
        contradict Heqo.
        apply is_Some_ne_None.
        apply mem_out_some.
        pose proof (out_mem_fill_pattern m _ Heqo0) as P.
        intros j jc H0.
        specialize (P j jc).
        apply P.
        apply compat.
        apply H0.
      +
        clear Heqo.
        pose proof (@mem_out_some _ _ _ _ _ H) as C.
        unfold is_Some in C.
        break_match; [ some_none | tauto].
    -
      (* out_mem_fill_pattern *)
      intros m0 m H.
      split.
      +
        simpl in *.
        unfold option_compose in H.
        break_match_hyp; try some_none.
        pose proof (out_mem_fill_pattern  m1 _ H) as P1.
        apply P1; auto.
      +
        simpl in *.
        unfold option_compose in H.
        break_match_hyp; try some_none.
        pose proof (out_mem_fill_pattern m1 _ H) as P2.
        apply P2; auto.
    -
      (* mem_out_oob *)
      intros m0 m H.
      unfold MSHCompose in H.
      unfold option_compose in H.
      simpl in H.
      break_match_hyp; try some_none.
      pose proof (out_mem_oob  m1 _ H) as P2.
      apply P2; auto.
  Qed.

  Instance Embed_MFacts
           {o b: nat}
           (bc: b < o)
    : MSHOperator_Facts (MSHEmbed bc).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros m H.
      unfold is_Some, MSHEmbed, Embed_mem, map_mem_block_elt, mem_lookup. simpl.
      repeat break_match; try some_none; try tauto.
      clear Heqo0. rename Heqo1 into M.
      simpl in *.
      assert(P: Full_set (FinNat 1) (mkFinNat Nat.lt_0_1)) by apply Full_intro.
      apply H in P.
      unfold mem_lookup, mem_in in *.
      apply NP.F.not_find_in_iff in M.
      congruence.
    -
      (* out_mem_fill_pattern *)
      intros m0 m H.
      split.
      +
        simpl in *.
        unfold Embed_mem, map_mem_block_elt, mem_lookup, mem_in, mem_add, mem_empty in *.
        break_match_hyp; try some_none.
        some_inv.
        subst m.
        intros O.
        destruct (eq_nat_dec j b).
        --
          apply NP.F.in_find_iff.
          rewrite NP.F.add_eq_o; auto.
          some_none.
        --
          unfold FinNatSet.singleton, mkFinNat in O.
          simpl in O.
          congruence.
      +
        simpl in *.
        unfold Embed_mem, map_mem_block_elt, mem_lookup, mem_in, mem_add, mem_empty in *.
        break_match_hyp; try some_none.
        some_inv.
        subst m.
        intros I.
        unfold FinNatSet.singleton, mkFinNat.
        destruct (eq_nat_dec j b); auto.
        exfalso.
        apply NP.F.in_find_iff in I.
        rewrite NP.F.add_neq_o in I ; auto.
    -
      intros m0 m H j jc C.
      simpl in H.
      unfold Embed_mem, map_mem_block_elt, mem_lookup, mem_in in *. simpl in *.
      break_match; try some_none.
      some_inv.
      subst m.
      unfold mem_add, mem_empty in C.
      destruct (eq_nat_dec j b); try omega.
      apply NP.F.in_find_iff in C.
      rewrite NP.F.add_neq_o in C; auto.
  Qed.

  Instance Pick_MFacts
           {i b: nat}
           (bc: b<i)
    : MSHOperator_Facts (MSHPick bc).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros v H.
      unfold is_Some, MSHPick, Pick_mem, map_mem_block_elt, mem_lookup. simpl.
      repeat break_match; try some_none; try tauto.
      clear Heqo. rename Heqo0 into M.
      simpl in *.
      assert(P: FinNatSet.singleton b (mkFinNat bc)).
      {
        unfold FinNatSet.singleton, mkFinNat.
        auto.
      }
      apply H in P.
      unfold mem_lookup, mem_in in *.
      apply NP.F.not_find_in_iff in M.
      congruence.
    -
      (* out_mem_fill_pattern *)
      intros m0 m H.
      simpl in *.
      unfold Pick_mem, map_mem_block_elt, mem_lookup, mem_in in *.
      destruct j; try omega.
      split.
      +
        intros F.
        break_match_hyp; try some_none.
        some_inv.
        subst m.
        unfold mem_add, mem_empty.
        apply NP.F.in_find_iff.
        rewrite NP.F.add_eq_o.
        some_none.
        reflexivity.
      +
        intros I.
        apply Full_intro.
      +
        crush.
    -
      intros m0 m H.
      simpl in *.
      unfold Pick_mem, map_mem_block_elt, mem_lookup, mem_in in *.

      intros j jc.
      unfold not.
      intros C.
      break_match_hyp; try some_none.
      some_inv.
      subst m.
      unfold mem_add, mem_empty in *.
      destruct (eq_nat_dec j 0) as [z | nz].
      +
        lia.
      +
        apply NP.F.add_neq_in_iff in C.
        apply NP.F.empty_in_iff in C.
        tauto.
        auto.
  Qed.

  Instance SHPointwise_MFacts
           {n: nat}
           (f: FinNat n -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    : MSHOperator_Facts (MSHPointwise f).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros v H.
      apply mem_out_some_mem_op_of_hop, H.
    -
      intros m0 m H.
      apply (out_mem_fill_pattern_mem_op_of_hop H).
    -
      intros m0 m H.
      apply (out_mem_fill_pattern_mem_op_of_hop H).
  Qed.

  Instance SHInductor_MFacts
           (n:nat)
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial: CarrierA):
    MSHOperator_Facts (MSHInductor n f initial).
  Proof.
    destruct n.
    -
      split.
      +
        intros.
        cbn.
        trivial.
      +
        intros.
        cbn in *.
        some_inv.
        destruct j;[|crush]. (* [lia] should work here instead of [crush] but it does not *)
        split; intros.
        *
          apply NP.F.add_in_iff.
          auto.
        *
          apply NP.F.add_in_iff in H.
          destruct H; constructor.
      +
        intros.
        cbn in *.
        some_inv. clear H1 m.
        intros C.
        apply NP.F.add_in_iff in C.
        destruct C.
        lia.
        apply NP.F.empty_in_iff in H.
        trivial.
    -
      split.
      +
        (* mem_out_some *)
        intros v H.
        apply mem_out_some_mem_op_of_hop, H.
      +
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
      +
        intros m0 m H.
        apply (out_mem_fill_pattern_mem_op_of_hop H).
  Qed.

  Instance SHBinOp_MFacts
           {o: nat}
           (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : MSHOperator_Facts (MSHBinOp f).
  Proof.
    split.
    -
      intros v H.
      apply mem_out_some_mem_op_of_hop, H.
    -
      intros m0 m H.
      apply (out_mem_fill_pattern_mem_op_of_hop H).
    -
      intros m0 m H.
      apply (out_mem_fill_pattern_mem_op_of_hop H).
  Qed.

  Fact HTSUMUnion_mem_out_fill_pattern
       {i o : nat}
       {dot : SgOp CarrierA}
       (op1 op2: @MSHOperator i o)
       `{facts1: MSHOperator_Facts _ _ op1}
       `{facts2: MSHOperator_Facts _ _ op2}:
    forall (m0 m : mem_block),
      HTSUMUnion_mem (mem_op op1) (mem_op op2) m0 ≡ Some m
      → forall (j : nat) (jc : j < o),
        m_out_index_set (i:=i)
                        (MHTSUMUnion dot op1 op2) (mkFinNat jc) ↔
                        mem_in j m.
  Proof.
    intros m0 m E.
    split; intros H.
    +
      simpl in *.
      unfold HTSUMUnion_mem in E. simpl in E.
      repeat break_match_hyp; try some_none.
      inversion E as [EE]; clear E. rename EE into E.
      eapply mem_union_as_Union.
      eauto.
      apply Constructive_sets.Union_inv in H.
      destruct H.
      *
        right.
        eapply (out_mem_fill_pattern _ _ Heqo1); eauto.
      *
        left.
        eapply (out_mem_fill_pattern _ _ Heqo0); eauto.
    +
      simpl in *.
      unfold HTSUMUnion_mem in E. simpl in E.
      repeat break_match_hyp; try some_none.
      inversion E as [EE]; clear E. rename EE into E.
      apply mem_union_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
      destruct E as [E0 E1].
      specialize (E0 H). clear H E1.
      destruct E0 as [M1 | M2].
      *
        right.
        eapply (out_mem_fill_pattern _ _ Heqo0); eauto.
      *
        left.
        eapply (out_mem_fill_pattern _ _ Heqo1); eauto.
  Qed.

  Instance HTSUMUnion_MFacts
           {i o: nat}
           `{dot: SgOp CarrierA}
           (op1 op2: @MSHOperator i o)
           (compat: Disjoint _
                             (m_out_index_set op1)
                             (m_out_index_set op2))
           `{facts1: MSHOperator_Facts _ _ op1}
           `{facts2: MSHOperator_Facts _ _ op2}
    : MSHOperator_Facts
        (MHTSUMUnion dot op1 op2).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros m H.
      unfold is_Some, MHTSUMUnion, HTSUMUnion_mem in *.
      simpl in *.
      repeat break_match; try some_none; try auto.
      +
        clear Heqo0.
        contradict Heqo2.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H0.
        specialize (H j jc).
        apply H.
        left.
        apply H0.
      +
        clear Heqo0.
        contradict Heqo1.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H0.
        specialize (H j jc).
        apply H.
        right.
        apply H0.
    -
      (* out_mem_fill_pattern *)
      eapply HTSUMUnion_mem_out_fill_pattern;
        typeclasses eauto.
    -
      intros m0 m E j jc H.
      simpl in *.
      unfold HTSUMUnion_mem in E; simpl in E.
      repeat break_match_hyp; try some_none.
      inversion E as [EE]; clear E. rename EE into E.
      apply mem_union_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
      destruct E as [E0 E1].
      specialize (E0 H). clear H E1.
      destruct E0 as [M0 | M1].
      --
        eapply (out_mem_oob _ _ Heqo0); eauto.
      --
        eapply (out_mem_oob _ _ Heqo1); eauto.
  Qed.

  Instance IReduction_MFacts
           {i o k: nat}
           (initial: CarrierA)
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
           (op_family: @MSHOperatorFamily i o k)
           (op_family_facts: forall j (jc:j<k), MSHOperator_Facts (op_family (mkFinNat jc)))
           (compat: forall j (jc:j<k),
               Ensembles.Same_set _
                                  (m_out_index_set (op_family (mkFinNat jc)))
                                  (Full_set _))
    : MSHOperator_Facts (@MSHIReduction i o k initial dot pdot op_family).
  Proof.
    split.
    -
      (* mem_out_some *)
      clear compat.
      intros m H.
      unfold MSHIReduction, IReduction_mem, is_Some.
      simpl.
      repeat break_match; try tauto.
      +
        some_none.
      +
        (* [Apply_mem_Family] could not be [None] *)
        clear Heqo0.
        rename Heqo1 into A.
        unfold Apply_mem_Family in A.

        induction k.
        *
          simpl in A.
          some_none.
        *
          simpl in A.
          repeat break_match_hyp; try some_none; clear A.
          --
            specialize (IHk
                          (shrink_m_op_family_up op_family)
                          (shrink_m_op_family_facts_up op_family op_family_facts)
                       ).

            assert (∀ (j : nat) (jc : j < i), m_in_index_set
                                                (MSHIReduction initial _                                                                     (shrink_m_op_family_up op_family)) (mkFinNat jc) →
                                              mem_in j m) as P.
            {
              clear IHk Heqo1.
              intros j jc H0.
              simpl in H0.
              specialize (H j jc).
              Opaque m_family_in_index_set.
              simpl in H.
              rewrite m_family_in_index_set_eq in H.
              rewrite m_family_in_index_set_eq in H0.
              Transparent m_family_in_index_set.
              simpl in H.
              apply H.
              apply Union_intror.
              unfold Ensembles.In.
              apply H0.
            }
            specialize (IHk P). clear P.
            contradict IHk.
            unfold get_family_mem_op in *.
            rewrite <- Heqo1.
            unfold shrink_m_op_family_up, shrink_m_op_family_facts_up.
            f_equiv.
            extensionality j.
            extensionality jc.
            replace (@strictly_order_preserving nat nat nat_equiv nat_lt nat_equiv nat_lt S
                                                _ j k jc)
              with (@lt_n_S j k jc) by apply NatUtil.lt_unique.
            reflexivity.
          --
            clear IHk.
            contradict Heqo0.
            apply is_Some_ne_None.
            apply op_family_facts.
            Opaque m_family_in_index_set.
            simpl in H.
            rewrite m_family_in_index_set_eq in H.
            Transparent m_family_in_index_set.
            simpl in H.
            intros j jc H0.
            specialize (H j jc).
            apply H. clear H.
            apply Union_introl.
            unfold Ensembles.In.
            replace (zero_lt_Sn k) with (Nat.lt_0_succ k) by apply NatUtil.lt_unique.
            apply H0.
    -
      (* out_mem_fill_pattern *)
      intros m0 m H j jc.
      unfold MSHIReduction, IReduction_mem in H.
      simpl in *.
      break_match_hyp ; try some_none.
      some_inv.
      clear H1 m.
      split.
      +
        intros H.
        rewrite m_family_out_index_set_eq in H.
        revert l Heqo0.
        induction k; intros l Heqo0.
        *
          simpl in *.
          inversion H.
        *
          rename Heqo0 into A.
          assert(length l = S k) as L by apply (Apply_mem_Family_length A).
          destruct l as [| l0]; try inversion L.

          apply Apply_mem_Family_cons in A.
          destruct A as [A0 A].

          simpl.
          apply mem_merge_with_def_as_Union.

          simpl in H.
          dep_destruct H.
          --
            clear IHk A.
            right.
            unfold Ensembles.In in H.
            eapply (out_mem_fill_pattern _ _ A0) with (jc:=jc).
            replace (Nat.lt_0_succ k) with (zero_lt_Sn k)
              by apply NatUtil.lt_unique.
            auto.
          --
            clear A0.
            specialize (IHk
                          (shrink_m_op_family_up op_family)
                          (shrink_m_op_family_facts_up _ op_family_facts)
                       ).
            left; auto.

            apply IHk; auto.
            intros.
            apply compat.
      +
        intros H.

        rename Heqo0 into A.
        assert(length l = k) as L by apply (Apply_mem_Family_length A).
        destruct k.
        *
          simpl in *.
          dep_destruct l; try inversion L.
          simpl in H.
          apply NP.F.empty_in_iff in H.
          tauto.
        *
          unshelve eapply m_family_out_set_includes_members.
          exact 0.
          apply zero_lt_Sn.
          apply compat.
          apply Full_intro.
    -
      (* out_mem_oob *)
      intros m0 m H j jc.
      clear compat.
      unfold MSHIReduction, IReduction_mem in H.
      simpl in *.
      break_match_hyp ; try some_none.
      some_inv.
      clear H1 m.
      rename Heqo0 into A.
      revert l A.
      induction k; intros l A.
      +
        unfold Apply_mem_Family in A.
        simpl in A.
        some_inv.
        subst l.
        simpl.
        unfold mem_in.
        intros C.
        apply NP.F.empty_in_iff in C.
        tauto.
      +
        assert(length l = S k) as L by apply (Apply_mem_Family_length A).
        destruct l as [| l0]; try inversion L.
        simpl.
        apply Apply_mem_Family_cons in A.
        destruct A as [A0 A].
        intros C.
        apply mem_merge_with_def_as_Union in C.
        destruct C.
        --
          apply (IHk
                   (shrink_m_op_family_up op_family)
                   (shrink_m_op_family_facts_up _ op_family_facts)
                   _
                   A).
          assumption.
        --
          apply out_mem_oob with (j0:=j) in A0; auto.
  Qed.

  Lemma mem_keys_set_to_m_out_index_set
        (i o: nat)
        (xop: @MSHOperator i o )
        `{mop: MSHOperator_Facts _ _ xop}
        (m m0: mem_block)
    :
      (mem_op xop m0 ≡ Some m)
      ->
      FinNatSet_to_natSet (m_out_index_set xop) ≡ NE.mkEns (mem_keys_set m).
  Proof.
    intros H.
    pose proof (out_mem_fill_pattern _ _ H) as H1.
    pose proof (out_mem_oob _ _ H) as H2.
    clear H.
    unfold mem_in in *.
    apply Extensionality_Ensembles.
    unfold Same_set.
    split.
    -
      unfold Ensembles.Included.
      intros k H.
      destruct (NatUtil.lt_ge_dec k o) as [kc | nkc].
      +
        clear H2.
        specialize (H1 k kc).
        apply mem_keys_set_In.
        apply H1. clear H1.
        unfold Ensembles.In in *.
        generalize dependent (m_out_index_set xop).
        intros s H.
        unfold FinNatSet_to_natSet in H.
        break_match_hyp; try contradiction.
        replace l with kc in H by apply NatUtil.lt_unique.
        apply H.
      +
        exfalso.
        clear H1.
        specialize (H2 k nkc).
        (* H is false, as k is out of range *)
        unfold Ensembles.In in H.
        unfold FinNatSet_to_natSet in H.
        break_match_hyp; try omega.
    -
      unfold Ensembles.Included.
      intros k H.
      unfold Ensembles.In in *.
      destruct (NatUtil.lt_ge_dec k o) as [kc | nkc].
      +
        clear H2.
        specialize (H1 k kc).
        unfold FinNatSet_to_natSet.
        break_match; try omega.
        replace l with kc by apply NatUtil.lt_unique.
        apply H1.
        apply mem_keys_set_In.
        apply H.
      +
        apply mem_keys_set_In in H.
        specialize (H2 k nkc).
        congruence.
  Qed.

  Fact IUnion_mem_step_disjoint
       {i o n : nat}
       (d: nat)
       (op_family: @MSHOperatorFamily i o (n+d))
       (op_family_facts: forall j (jc:j<(n+d)), MSHOperator_Facts (op_family (mkFinNat jc)))

       (compat : ∀ (m0 : nat) (mc : m0 < (n+d)) (n0 : nat) (nc : n0 < (n+d)),
           m0 ≢ n0
           → Disjoint (FinNat o)
                      (@m_out_index_set i o (op_family (mkFinNat mc)))
                      (@m_out_index_set i o (op_family (mkFinNat nc))))

       (m m0 m1 : mem_block)
       (l: list mem_block)
       (A : Apply_mem_Family
              (get_family_mem_op
                 (shrink_m_op_family_up_n d op_family)) m
              ≡ Some l)

       (t:nat)
       (tc: t<d)
       (tc1: t<n+d)
       (H0: get_family_mem_op op_family _ tc1 m ≡ Some m0)

       (H1: monadic_fold_left_rev mem_merge mem_empty l ≡ Some m1)
    :
      Disjoint nat
               (NE.mkEns (mem_keys_set m1))
               (NE.mkEns (mem_keys_set m0)).
  Proof.
    pose proof (Apply_mem_Family_length A) as L.
    dependent induction n.
    -
      destruct l. 2:inversion L.
      simpl in *.
      some_inv.
      subst.
      unfold mem_empty, mem_keys_set.
      simpl.
      apply Disjoint_intro.
      intros x C.
      unfold Ensembles.In in C.
      destruct C.
      inversion H.
    -
      destruct l as [| m1h m1t];  inversion L.
      apply Apply_mem_Family_cons in A.
      destruct A as [A0 A].
      simpl in H1.
      break_match_hyp; try some_none.
      apply Disjoint_Symmetric.
      apply (Disjoint_of_mem_merge H1 (m0:=m0)).
      +
        apply Disjoint_Symmetric.
        assert(K: (Init.Nat.add (S n) d) ≡ (Init.Nat.add n (S d))) by lia.

        assert(tc2: S t <= n + S d).
        {
          rewrite <- K.
          apply tc1.
          (* (eq_ind (S n + d) (λ n0 : nat, S t <= n0) tc1 (n + S d) K) *)
        }
        specialize IHn with (d:=(S d))
                            (m:=m)
                            (m0:=m0)
                            (l:=m1t)
                            (t:=t)
                            (tc1:=tc2)
                            (op_family:=cast_m_op_family op_family K).
        specialize (IHn (cast_m_op_family_facts op_family_facts K)).


        eapply IHn; eauto.
        *
          intros m0' mc' n0' nc' H.
          assert(mc'': m0' < S n + d) by lia.
          assert(nc'': n0' < S n + d) by lia.
          specialize (compat m0' mc'' n0' nc'' H).

          erewrite <- cast_m_out_index_set_eq.
          erewrite <- cast_m_out_index_set_eq.
          apply compat.
        *
          rewrite <- A.
          unfold
            shrink_m_op_family_up, shrink_m_op_family_facts_up,
          shrink_m_op_family,
          shrink_m_op_family_up_n, shrink_m_op_family_facts_up_n.
          clear.
          f_equiv.
          unfold get_family_mem_op.
          extensionality j.
          extensionality jc.
          simpl.
          apply cast_mem_op_eq.
          lia.
        *
          rewrite <- H0.
          clear.
          unfold get_family_mem_op.
          apply equal_f.
          apply cast_mem_op_eq; auto.
      +
        clear IHn A Heqo0.
        unfold get_family_mem_op in A0, H0.
        unfold
          shrink_m_op_family_up, shrink_m_op_family_facts_up,
        shrink_m_op_family,
        shrink_m_op_family_up_n, shrink_m_op_family_facts_up_n
          in *.
        simpl in *.
        specialize (compat t tc1).
        specialize (compat d (Plus.plus_lt_compat_r O (S n) d (Nat.lt_0_succ n))).
        apply Disjoint_FinNat_to_nat in compat.
        rewrite (mem_keys_set_to_m_out_index_set _ _ _ _ _ H0) in compat.
        rewrite (mem_keys_set_to_m_out_index_set _ _ _ _ _ A0) in compat.
        apply compat.
        lia.
  Qed.

  Fact IUnion_mem_1_step_disjoint
       {i o n : nat}
       (op_family: @MSHOperatorFamily i o (S n))
       (op_family_facts: ∀ (j : nat) (jc : j < (S n)),
           MSHOperator_Facts (op_family (@mkFinNat (S n) j jc)))

       (compat : ∀ (m0 : nat) (mc : m0 < (S n)) (n0 : nat) (nc : n0 < (S n)),
           m0 ≢ n0
           → Disjoint (FinNat o)
                      (@m_out_index_set i o (op_family (mkFinNat mc)))
                      (@m_out_index_set i o (op_family (mkFinNat nc))))

       (m m0 m1 : mem_block)
       (l: list mem_block)
       (A : Apply_mem_Family
              (get_family_mem_op
                 (shrink_m_op_family_up op_family)) m
              ≡ Some l)

       (t:nat)
       (H0: get_family_mem_op op_family _ (Nat.lt_0_succ n) m ≡ Some m0)

       (H1: monadic_fold_left_rev mem_merge mem_empty l ≡ Some m1)
    :
      Disjoint nat
               (NE.mkEns (mem_keys_set m1))
               (NE.mkEns (mem_keys_set m0)).
  Proof.
    (* same as [IUnion_mem_step_disjoint] with [d:=1] *)
    assert(E: S n ≡ n + 1) by lia.
    assert(zc2: 0 < n + 1) by lia.
    eapply IUnion_mem_step_disjoint with
        (d:=1)
        (t0:=0)
        (tc1:=zc2)
        (m2:=m).
    -
      exact (cast_m_op_family_facts op_family_facts E).
    -
      intros m0' mc' n0' nc' H.
      assert(mc'': m0' < S n ) by lia.
      assert(nc'': n0' < S n ) by lia.
      specialize (compat m0' mc'' n0' nc'' H).
      erewrite <- cast_m_out_index_set_eq.
      erewrite <- cast_m_out_index_set_eq.
      apply compat.
    -
      rewrite <- A.
      unfold
        shrink_m_op_family_up, shrink_m_op_family_facts_up,
      shrink_m_op_family,
      shrink_m_op_family_up_n, shrink_m_op_family_facts_up_n.
      clear.
      f_equiv.
      unfold get_family_mem_op.
      extensionality j.
      extensionality jc.
      apply cast_mem_op_eq.
      lia.
    -
      auto.
    -
      rewrite <- H0.
      clear.
      unfold get_family_mem_op.
      apply equal_f.
      apply cast_mem_op_eq; auto.
    -
      auto.
  Qed.

  Instance IUnion_MFacts
           {i o k: nat}
           (op_family: @MSHOperatorFamily i o k)
           (op_family_facts: forall j (jc:j<k), MSHOperator_Facts (op_family (mkFinNat jc)))
           (compat: forall m (mc:m<k) n (nc:n<k), m ≢ n -> Disjoint _
                                                              (m_out_index_set (op_family (mkFinNat mc)))
                                                              (m_out_index_set (op_family (mkFinNat nc))))
    :  MSHOperator_Facts (MSHIUnion op_family).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros m H.
      unfold MSHIUnion, IUnion_mem, is_Some.
      simpl.
      repeat break_match; auto.
      some_none.
      clear Heqo0.
      (* [Apply_mem_Family] could not be [None] *)
      rename Heqo1 into A.
      unfold Apply_mem_Family in A.
      induction k.
      +
        simpl in A.
        some_none.
      +
        simpl in A.
        repeat break_match_hyp; try some_none; clear A.
        *
          specialize (IHk
                        (shrink_m_op_family_up op_family)
                        (shrink_m_op_family_facts_up _ op_family_facts)
                     ).

          assert (∀ (j : nat) (jc : j < i), m_in_index_set
                                            (MSHIUnion
                                               (shrink_m_op_family_up op_family)) (mkFinNat jc) →
                                          mem_in j m) as P.
          {
            clear IHk Heqo1.
            intros j jc H0.
            simpl in H0.
            specialize (H j jc).
            Opaque m_family_in_index_set.
            simpl in H.
            rewrite m_family_in_index_set_eq in H.
            rewrite m_family_in_index_set_eq in H0.
            Transparent m_family_in_index_set.
            simpl in H.
            apply H.
            apply Union_intror.
            unfold Ensembles.In.
            apply H0.
          }
          assert(compat':
                   ∀ (m : nat) (mc : m < k) (n : nat) (nc : n < k),
                     m ≢ n
                     → Disjoint
                         (FinNat o)
                         (m_out_index_set (shrink_m_op_family_up op_family (mkFinNat mc)))
                         (m_out_index_set (shrink_m_op_family_up op_family (mkFinNat nc)))).
          {
            intros m1 mc n nc H0.
            apply compat.
            auto.
          }
          specialize (IHk compat' P). clear P compat'.
          contradict IHk.
          unfold get_family_mem_op in *.
          rewrite <- Heqo1.
          unfold shrink_m_op_family_up, shrink_m_op_family_facts_up.
          f_equiv.
          extensionality j.
          extensionality jc.
          replace (@strictly_order_preserving _ _ _ _ _ _ _ _ j k jc)
            with (@lt_n_S j k jc) by apply NatUtil.lt_unique.
          reflexivity.
        *
          clear IHk.
          contradict Heqo0.
          apply is_Some_ne_None.
          apply op_family_facts.
          Opaque m_family_in_index_set.
          simpl in H.
          rewrite m_family_in_index_set_eq in H.
          Transparent m_family_in_index_set.
          simpl in H.
          intros j jc H0.
          specialize (H j jc).
          apply H. clear H.
          apply Union_introl.
          unfold Ensembles.In.
          replace (zero_lt_Sn k) with (Nat.lt_0_succ k) by apply NatUtil.lt_unique.
          apply H0.
    -
      (* out_mem_fill_pattern *)
      intros m0 m H j jc.
      unfold MSHIUnion, IUnion_mem in H.
      simpl in *.
      break_match_hyp ; try some_none.
      rename Heqo0 into A.
      split.
      +
        rewrite m_family_out_index_set_eq.
        dependent induction k; intros.
        *
          simpl in *.
          inversion H0.
        *
          assert(length l = S k) as L by apply (Apply_mem_Family_length A).
          destruct l as [| l0]; try inversion L.

          apply Apply_mem_Family_cons in A.
          destruct A as [A0 A].
          simpl in H.
          apply Some_inj_eq in H.
          apply (mem_union_as_Union _ _ _ H).
          simpl in *.
          dependent destruction H0.
          --
            clear IHk A.
            right.
            unfold Ensembles.In in H0.
            eapply (out_mem_fill_pattern _ _ A0) with (jc:=jc).
            replace (Nat.lt_0_succ k) with (zero_lt_Sn k)
              by apply NatUtil.lt_unique.
            auto.
          --
            clear A0.
            left.

            specialize (IHk
                          (shrink_m_op_family_up op_family)
                          (shrink_m_op_family_facts_up _ op_family_facts)
                       ).
            eapply IHk;eauto.
      +
        assert(length l = k) as L by apply (Apply_mem_Family_length A).
        rewrite m_family_out_index_set_eq.
        dependent induction k; intros.
        *
          simpl in *.
          dep_destruct l; try inversion L.
          simpl in H.
          some_inv.
          subst m.
          unfold mem_in, mem_empty in H0.
          apply NP.F.empty_in_iff in H0.
          tauto.
        *
          destruct l as [| l0]; try inversion L.
          apply Apply_mem_Family_cons in A.
          destruct A as [A0 A].
          simpl in *.
          apply Some_inj_eq in H.
          apply (mem_union_as_Union _ _ _ H) in H0.
          dependent destruction H0.
          --
            clear A0.
            right.

            specialize (IHk
                          (shrink_m_op_family_up op_family)
                          (shrink_m_op_family_facts_up _ op_family_facts)
                       ).
            eapply IHk;eauto.
          --
            clear IHk A.
            left.
            unfold Ensembles.In.
            unfold get_family_mem_op in A0.
            eapply out_mem_fill_pattern with (jc0:=jc) in A0.
            replace (Nat.lt_0_succ k) with (zero_lt_Sn k) in A0
              by apply NatUtil.lt_unique.
            apply A0.
            auto.
    -
      (* out_mem_oob *)
      intros m0 m H j jc.
      unfold MSHIUnion, IUnion_mem in H.
      simpl in *.
      break_match_hyp ; try some_none.
      rename Heqo0 into A.
      dependent induction k.
      +
        unfold Apply_mem_Family in A.
        simpl in A.
        repeat some_inv.
        subst l.
        simpl in *.
        unfold mem_in, mem_empty.
        intros C.
        apply NP.F.empty_in_iff in C.
        tauto.
      +
        assert(length l = S k) as L by apply (Apply_mem_Family_length A).
        destruct l as [| l0]; try inversion L.
        simpl.
        apply Apply_mem_Family_cons in A.
        destruct A as [A0 A].
        intros C.
        simpl in *.
        apply Some_inj_eq in H.
        apply (mem_union_as_Union _ _ _ H) in C.
        destruct C.
        --
          clear A0.
          specialize (IHk
                        (shrink_m_op_family_up op_family)
                        (shrink_m_op_family_facts_up _ op_family_facts)
                     ).
          eapply IHk;eauto.
        --
          apply out_mem_oob with (j0:=j) in A0; auto.
  Qed.


End MMSHCOL'.


(* There will be only one instance of MMSCHOL', as it is always
   defined on [CarrierA]. *)
Module Export MMSCHOL := MMSHCOL'(CarrierAasCT)(MMemoryOfCarrierA).
