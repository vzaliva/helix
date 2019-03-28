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
Require Import Helix.Util.WriterMonadNoT.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.VecSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.MemSetoid.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.

Import Monoid.

Global Open Scope nat_scope.
Set Implicit Arguments.

Import VectorNotations.
Open Scope vector_scope.


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

Section Avector.

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

  (* alternative, propositional spec. *)
  Lemma avector_to_mem_block_spec'
        (n : nat)
        (v : avector n)
        (i: nat)
        (ip : i < n)
    : mem_mapsto i (Vnth v ip) (avector_to_mem_block v).
  Proof.
    unfold avector_to_mem_block.
    destruct (avector_to_mem_block_spec v) as [x SP].
    apply NM.find_2, SP.
  Qed.

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

  Definition mem_block_to_avector {n} (m: mem_block): option (vector CarrierA n)
    := vsequence (Vbuild (fun i (ic:i<n) => mem_lookup i m)).

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

End Avector.

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

Section Avector_Setoid.

  Global Instance mem_block_to_avector_proper {n:nat}:
    Proper ((equiv) ==> (eq)) (@mem_block_to_avector n).
  Proof.
    simpl_relation.
    unfold mem_block_to_avector.
    f_equal.
    vec_index_equiv i ip.
    rewrite 2!Vbuild_nth.
    apply H.
  Qed.

  Global Instance avector_to_mem_block_proper {n:nat}:
    Proper ((eq) ==> (equiv)) (@avector_to_mem_block n).
  Proof.
    simpl_relation.
  Qed.

End Avector_Setoid.

Section SVector.

  Variable fm:Monoid RthetaFlags.

  Program Definition svector_to_mem_block_spec
          {n : nat}
          (v : svector fm n):
    { m : mem_block |
      (
        (forall i (ip : i < n), Is_Val (Vnth v ip) <-> NM.MapsTo i (evalWriter (Vnth v ip)) m)
        /\
        (forall i (ip : i < n), NM.In i m <-> Is_Val (Vnth v ip))
      )
    }
    := Vfold_right_indexed' 0
                            (fun k r m =>
                               if Is_Val_dec r then mem_add k (evalWriter r) m
                               else m
                            )
                            v mem_empty.
  Next Obligation.
    unfold mem_lookup, mem_add, mem_empty.
    split.
    -
      (* Is_Val <-> MapsTo *)
      split.
      +
        (* Is_Val -> MapsTo *)
        revert ip. revert i.
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v;clear v.
          simpl.
          destruct i.
          --
            destruct (Is_Val_dec h).
            ++
              apply NM.add_1.
              reflexivity.
            ++
              simpl in H.
              crush.
          --
            destruct (Is_Val_dec h).
            ++
              apply NM.add_2; auto.
              assert (N: i<n) by apply Lt.lt_S_n, ip.
              simpl in H.
              replace (Lt.lt_S_n ip) with N by apply le_unique.
              assert(V: Is_Val (Vnth x N)).
              {
                replace N with (lt_S_n ip) by apply le_unique.
                apply H.
              }
              specialize (IHn x i N V).
              apply NM.find_1 in IHn.
              apply NM.find_2.
              rewrite <- IHn; clear IHn.
              rewrite find_fold_right_indexed'_S_P.
              reflexivity.
            ++
              simpl in H.
              assert (N: i<n) by apply Lt.lt_S_n, ip.
              replace (Lt.lt_S_n ip) with N by apply le_unique.
              assert(V: Is_Val (Vnth x N)).
              {
                replace N with (lt_S_n ip) by apply le_unique.
                apply H.
              }
              specialize (IHn x i N V).
              apply NM.find_1 in IHn.
              apply NM.find_2.
              rewrite find_fold_right_indexed'_S_P.
              apply IHn.
      +
        (* MapsTo -> Is_Val *)
        revert i ip.
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v; clear v.
          simpl.
          destruct i.
          --
            clear IHn.
            apply NM.find_1 in H.
            simpl in H.
            destruct (Is_Val_dec h); auto.
            rewrite find_fold_right_indexed_oob in H.
            some_none.
            auto.
          --
            apply IHn; clear IHn.
            apply NM.find_1 in H.
            apply NM.find_2.
            simpl (Some _) in H.
            assert (N: i<n) by apply Lt.lt_S_n, ip.
            replace (Lt.lt_S_n ip) with N in * by apply le_unique.
            rewrite <- H; clear H ip.
            rewrite <- find_fold_right_indexed'_S_P.
            symmetry.
            apply find_fold_right_indexed'_cons_P.
    -
      split.
      +
        revert i ip.
        (* In -> Is_Val *)
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v; clear v.
          simpl.
          destruct i.
          --
            clear IHn.
            simpl in H.
            destruct (Is_Val_dec h); auto.
            apply In_MapsTo in H.
            destruct H as [e H].
            apply NP.F.find_mapsto_iff in H.
            rewrite find_fold_right_indexed_oob in H.
            some_none.
            auto.
          --
            apply IHn; clear IHn.
            apply In_MapsTo in H.
            destruct H as [e H].
            apply NP.F.find_mapsto_iff in H.
            apply MapsTo_In with (e:=e).
            apply NP.F.find_mapsto_iff.
            rewrite <- H. clear H ip.
            rewrite <- find_fold_right_indexed'_S_P.
            symmetry.
            apply find_fold_right_indexed'_cons_P.
      +
        (* Is_Val -> NM.In *)
        revert i ip.
        (* In -> Is_Val *)
        induction n; intros.
        *
          nat_lt_0_contradiction.
        *
          dep_destruct v; clear v.
          simpl.
          destruct i.
          --
            clear IHn.
            simpl.
            break_if.
            ++
              apply NP.F.add_in_iff.
              auto.
            ++
              exfalso.
              contradict H.
              simpl.
              auto.
          --
            break_if.
            ++
              apply NP.F.add_neq_in_iff; auto.
              simpl in *.
              apply IHn in H. clear IHn.
              apply In_MapsTo in H.
              destruct H as [e H].
              apply NP.F.find_mapsto_iff in H.
              apply MapsTo_In with (e:=e).
              apply NP.F.find_mapsto_iff.
              rewrite <- H. clear H ip.
              rewrite <- find_fold_right_indexed'_S_P.
              reflexivity.
            ++
              simpl in H.
              apply IHn in H. clear IHn.
              apply In_MapsTo in H.
              destruct H as [e H].
              apply NP.F.find_mapsto_iff in H.
              apply MapsTo_In with (e:=e).
              apply NP.F.find_mapsto_iff.
              rewrite <- H. clear H ip.
              rewrite <- find_fold_right_indexed'_S_P.
              reflexivity.
  Qed.

  Definition svector_to_mem_block {n} (v: svector fm n) := proj1_sig (svector_to_mem_block_spec v).

  (* this could only be proven wrt @eq on input vectors, not @equiv! *)
  Global Instance svector_to_mem_block_proper
         {n: nat}:
    Proper ((eq) ==> (=)) (@svector_to_mem_block n).
  Proof.
    solve_proper.
  Qed.

  Lemma svector_to_mem_block_key_oob {n:nat} {v: svector fm n}:
    forall (k:nat) (kc:ge k n), mem_lookup k (svector_to_mem_block v) ≡ None.
  Proof.
    intros k kc.
    unfold svector_to_mem_block.
    simpl.
    revert k kc; induction v; intros.
    -
      reflexivity.
    -
      unfold mem_lookup.
      simpl.
      destruct k.
      +
        omega.
      +
        break_if.
        *
          rewrite NP.F.add_neq_o by omega.
          rewrite find_fold_right_indexed'_S_P.
          rewrite IHv.
          reflexivity.
          omega.
        *
          rewrite find_fold_right_indexed'_S_P.
          rewrite IHv.
          reflexivity.
          omega.
  Qed.

  Definition mem_block_to_svector {n} (m: mem_block): svector fm n
    := Vbuild (fun i (ic:i<n) =>
                 match mem_lookup i m with
                 | None => mkSZero (* maybe other structural value? *)
                 | Some x => mkValue x
                 end
              ).

  (* proving stronger @eq equality here.
 Probably could be proven for @equiv as well *)
  Global Instance mem_block_to_svector_proper
         {n: nat}:
    Proper ((=) ==> (eq)) (@mem_block_to_svector n).
  Proof.
    simpl_relation.
    unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal in H.
    unfold mem_block_to_svector.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    specialize (H j).
    unfold mem_lookup.
    break_match; break_match; try some_none; try reflexivity.
    some_inv.
    reflexivity.
  Qed.

End SVector.

Ltac svector_to_mem_block_to_spec m H0 H1 H2 :=
  match goal with
  | [ |- context[svector_to_mem_block_spec ?v]] =>
    pose proof (svector_to_mem_block_key_oob (v:=v)) as H2;
    unfold svector_to_mem_block in H2 ;
    destruct (svector_to_mem_block_spec v) as [m [H0 H1]]

  | [ H: context[svector_to_mem_block_spec ?v] |- _ ] =>
    pose proof (svector_to_mem_block_key_oob (v:=v)) as H2;
    unfold svector_to_mem_block in H2 ;
    destruct (svector_to_mem_block_spec v) as [m [H0 H1]]
  end.

Lemma find_svector_to_mem_block_some (n k:nat) (kc:k<n) {fm} (x:svector fm n)
  :
    NM.In (elt:=CarrierA) k (svector_to_mem_block x) ->
    NM.find (elt:=CarrierA) k (svector_to_mem_block x)
            ≡ Some (evalWriter (Vnth x kc)).
Proof.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m' H0 H1 I2.
  intros H.
  simpl in *.
  unfold mem_lookup in *.
  apply NM.find_1.
  apply H0, H1, H.
Qed.

Lemma svector_to_mem_block_In
      {n:nat}
      {fm}
      (x: svector fm n)
      (j:nat)
      (jc:j<n):
  Is_Val (Vnth x jc) -> mem_in j (svector_to_mem_block x).
Proof.
  intros H.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m0 I0 H1 O0.
  simpl in *.
  specialize (H1 j jc).
  apply H1, H.
Qed.

(* y[j] := x[i] *)
Definition map_mem_block_elt (x:mem_block) (i:nat) (y:mem_block) (j:nat)
  : option mem_block :=
  match mem_lookup i x with
  | None => None
  | Some v => Some (mem_add j v y)
  end.

Section Wrappers.

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

  Global Instance mem_op_of_hop_proper
         {i o: nat}:
    Proper ((eq) ==> (=)) (@mem_op_of_hop i o).
  Proof.
    intros a b E.
    unfold mem_op_of_hop.
    unfold equiv, ext_equiv.
    intros mx my Em.
    repeat break_match;
      rewrite Em in Heqo0;
      rewrite Heqo0 in Heqo1.
    -
      inversion Heqo1.
      subst.
      f_equiv.
    -
      some_none.
    -
      some_none.
    -
      reflexivity.
  Qed.

  Definition mem_op_of_op {fm} {i o: nat} (op: svector fm i -> svector fm o)
    : mem_block -> option mem_block
    := fun x => Some (svector_to_mem_block (op (mem_block_to_svector fm x))).

  (* this could only be proven wrt @eq on operators, not ((=)==>(=)). *)
  Global Instance mem_op_of_op_proper
         {fm}
         {i o: nat}:
    Proper ((eq) ==> (=)) (@mem_op_of_op fm i o).
  Proof.
    intros f g E.
    unfold equiv, ext_equiv.
    intros mx my Em.
    unfold mem_op_of_op.
    f_equiv.
    f_equiv.
    rewrite_clear E.
    f_equiv.
    rewrite Em.
    reflexivity.
  Qed.

End Wrappers.

Section Operators.
  (* AKA: "embed" *)
  Definition eUnion_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x 0 (mem_empty) b.

  (* AKA "pick" *)
  Definition eT_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x b (mem_empty) 0.

  (* This is defined for n>0 *)
  Fixpoint IUnion_mem_aux
           {n: nat}
           (j: nat) (jc: j<n)
           (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
           (x: mem_block) {struct j}: option mem_block :=
    let oy := op_family_f j jc x in
    match j return j<n -> option mem_block with
    | O => fun _ => oy
    | S j' => fun jc' =>
               match oy, IUnion_mem_aux (Nat.lt_succ_l j' n jc') op_family_f x with
               | Some y, Some ys => mem_merge y ys
               | _, _ => None
               end
    end jc.

  (* This is defined for n>=0 *)
  Definition IUnion_mem
             {n: nat}
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block): option mem_block
    :=
      match n as m return n=m -> option mem_block with
      | 0 => fun _ => Some (mem_empty) (* empty loop is no-op *)
      | S n' => fun E => IUnion_mem_aux
                       (eq_ind_r _ (Nat.lt_succ_diag_r n') E)
                       op_family_f x
      end eq_refl.

  (* This is defined for n>0 *)
  Fixpoint IReduction_mem_aux
           {n: nat}
           (j: nat) (jc: j<n)

           (dot: CarrierA -> CarrierA -> CarrierA)
           (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
           (x:mem_block): option mem_block
    :=
      let oy := op_family_f j jc x in
      match j return j<n -> option mem_block with
      | O => fun _ => oy
      | S j' => fun jc' =>
                 match oy, IReduction_mem_aux (Nat.lt_succ_l j' n jc') dot op_family_f x with
                 | Some y, Some ys => Some (mem_merge_with dot y ys)
                 | _, _ => None
                 end
      end jc.

  (* This is defined for n>=0 *)
  Definition IReduction_mem
             {n: nat}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x:mem_block): option mem_block
    :=
      match n as m return n=m -> option mem_block with
      | 0 => fun _ => Some (mem_empty) (* empty loop is no-op *)
      | S n' => fun E => IReduction_mem_aux
                       (eq_ind_r _ (Nat.lt_succ_diag_r n') E)
                       dot
                       op_family_f x
      end eq_refl.

  Definition HTSUMUnion_mem
             (op1 op2: mem_block -> option mem_block)
    : mem_block -> option mem_block
    := fun x =>
         match op1 x, op2 x with
         | Some a, Some b => mem_merge a b
         | _, _ => None
         end.

End Operators.

Section Morphisms.

  Global Instance eUnion_mem_proper
         {b:nat}
  : Proper (equiv ==> equiv) (eUnion_mem b).
  Proof.
    simpl_relation.
    unfold eUnion_mem.
    unfold map_mem_block_elt.
    break_match; break_match;
      rewrite H in Heqo; rewrite Heqo in Heqo0.
    - some_inv; reflexivity.
    - some_none.
    - some_none.
    - reflexivity.
  Qed.

  Global Instance eT_mem_proper
         {b:nat}
    : Proper (equiv ==> equiv) (eT_mem b).
  Proof.
    simpl_relation.
    unfold eT_mem.
    unfold map_mem_block_elt.
    break_match; break_match;
      rewrite H in Heqo; rewrite Heqo in Heqo0.
    - some_inv; reflexivity.
    - some_none.
    - some_none.
    - reflexivity.
  Qed.

  (* TODO: may need Proper for `op_family_f` *)
  Global Instance IUnion_mem_proper
         {n: nat}
         (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
    :
      Proper (equiv ==> equiv) (IUnion_mem op_family_f).
  Proof.
  Admitted.

  (* TODO: may need Proper for `op_family_f` *)
  Global Instance IReduction_mem_proper
         {n: nat}
         (dot: CarrierA -> CarrierA -> CarrierA)
         (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
    :
      Proper (equiv ==> equiv) (IReduction_mem dot op_family_f).
  Proof.
  Admitted.


  Global Instance HTSUMUnion_mem_proper:
    Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> equiv ==> equiv) (HTSUMUnion_mem).
  Proof.
  Admitted.


End Morphisms.
