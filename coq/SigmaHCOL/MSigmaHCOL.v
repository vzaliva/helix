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
Require Import Helix.Util.ListSetoid.

Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.CarrierType.

Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.MemSetoid.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.

Require Import Helix.Tactics.HelixTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.util.
Require Import MathClasses.implementations.peano_naturals.

Import Monoid.

Global Open Scope nat_scope.
Set Implicit Arguments.

Import VectorNotations.
Open Scope vector_scope.

Import MonadNotation.
Open Scope monad_scope.

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
    Proper ((equiv) ==> (equiv)) (@mem_block_to_avector n).
  Proof.
    simpl_relation.
    unfold mem_block_to_avector.
    destruct_opt_r_equiv.
    -
      rename t into a, t0 into b.
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

  Global Instance mem_add_Proper:
    Proper ((eq) ==> (equiv) ==> (equiv) ==> (equiv)) (mem_add).
  Proof.
    simpl_relation.
    rename y into k'.
    unfold mem_add.
    unfold equiv, mem_block_Equiv in H1.
    specialize (H1 k).
    destruct_opt_r_equiv.
    -
      rename c into a, c0 into b.
      apply Some_inj_equiv.
      rewrite <- Ha, <- Hb; clear Ha Hb.
      destruct (eq_nat_dec k k').
      +
        rewrite 2!NP.F.add_eq_o by auto.
        f_equiv.
        apply H0.
      +
        rewrite 2!NP.F.add_neq_o by auto.
        apply H1.
    -
      destruct (eq_nat_dec k k').
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
      destruct (eq_nat_dec k k').
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

  Global Instance avector_to_mem_block_proper {n:nat}:
    Proper ((equiv) ==> (equiv)) (@avector_to_mem_block n).
  Proof.
    simpl_relation.
    unfold avector_to_mem_block.
    simpl.
    destruct_opt_r_equiv.
    -
      rename c into a, c0 into b.
      apply Some_inj_equiv.
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

  (* This could be only proven for [eq] in for svectors, as their
     structural properites are affecting the result. *)
  Global Instance svector_to_mem_block_proper
         {n: nat}:
    Proper ((eq) ==> (equiv)) (@svector_to_mem_block n).
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

  Global Instance mem_block_to_svector_proper
         {n: nat}:
    Proper ((=) ==> (=)) (@mem_block_to_svector n).
  Proof.
    intros a b H.
    unfold equiv, mem_block_Equiv in H.
    unfold mem_block_to_svector.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    specialize (H j).
    unfold mem_lookup.
    break_match; break_match; try some_none; try reflexivity.
    some_inv.
    f_equiv.
    apply H.
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

Lemma svector_to_mem_block_Vconst_mkStruct
      {fm}
      {fml : MonoidLaws fm}
      (n : nat)
      (v : CarrierA):
  svector_to_mem_block (Vconst (mkStruct (fm:=fm) v) n) = mem_empty.
Proof.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  simpl in *.
  mem_index_equiv k.
  rewrite NP.F.empty_o.
  destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
  -
    apply None_equiv_eq.
    apply NP.F.not_find_in_iff.

    specialize (I0 k kc).
    apply not_iff_compat in I0.
    apply I0.
    rewrite Vnth_const.
    apply Is_Val_mkStruct.
  -
    apply None_equiv_eq.
    apply O0, kc.
Qed.

Lemma svector_to_mem_block_rvector2rsvector
      {n x}:
  svector_to_mem_block (rvector2rsvector n x) = svector_to_mem_block x.
Proof.
  unfold svector_to_mem_block, rvector2rsvector, Rtheta2RStheta.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  svector_to_mem_block_to_spec m1 H1 I1 O1.
  simpl in *.
  mem_index_equiv k.
  destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
  -
    clear O0 O1.
    specialize (H0 k kc).
    specialize (H1 k kc).
    unfold equiv, option_Equiv.
    rewrite Vnth_map in H0.
    unfold Is_Val,compose in H0.
    rewrite execWriter_castWriter in H0.
    unfold Is_Val, compose in H1.
    rewrite evalWriter_castWriter in H0.

    specialize (I0 k kc).
    specialize (I1 k kc).
    rewrite Vnth_map in I0.
    unfold Is_Val,compose in I0.
    rewrite execWriter_castWriter in I0.
    unfold Is_Val, compose in I1.

    destruct (IsVal_dec (execWriter (Vnth x kc))) as [V|NV].
    +
      destruct H0 as [H0 _].
      destruct H1 as [H1 _].
      apply NM.find_1 in H0; auto.
      apply NM.find_1 in H1; auto.
      rewrite H0, H1.
      reflexivity.
    +
      unfold Rtheta in *.
      generalize dependent (Vnth x kc).
      intros r H0 I0 H1 I1 NV.
      apply not_iff_compat in I0.
      apply not_iff_compat in I1.
      destruct I0 as [_ I0].
      destruct I1 as [_ I1].
      specialize (I0 NV).
      specialize (I1 NV).
      clear NV.
      apply NP.F.not_find_in_iff in I0.
      apply NP.F.not_find_in_iff in I1.
      rewrite I0, I1.
      reflexivity.
  -
    rewrite O0 by assumption.
    rewrite O1 by assumption.
    reflexivity.
Qed.


Lemma svector_to_mem_block_rsvector2rvector
      {n x}:
  svector_to_mem_block (rsvector2rvector n x) = svector_to_mem_block x.
Proof.
  unfold svector_to_mem_block, rsvector2rvector, RStheta2Rtheta.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  svector_to_mem_block_to_spec m1 H1 I1 O1.
  simpl in *.
  mem_index_equiv k.
  destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
  -
    clear O0 O1.
    specialize (H0 k kc).
    specialize (H1 k kc).
    unfold equiv, option_Equiv.
    rewrite Vnth_map in H0.
    unfold Is_Val,compose in H0.
    rewrite execWriter_castWriter in H0.
    unfold Is_Val, compose in H1.
    rewrite evalWriter_castWriter in H0.

    specialize (I0 k kc).
    specialize (I1 k kc).
    rewrite Vnth_map in I0.
    unfold Is_Val,compose in I0.
    rewrite execWriter_castWriter in I0.
    unfold Is_Val, compose in I1.

    destruct (IsVal_dec (execWriter (Vnth x kc))) as [V|NV].
    +
      destruct H0 as [H0 _].
      destruct H1 as [H1 _].
      apply NM.find_1 in H0; auto.
      apply NM.find_1 in H1; auto.
      rewrite H0, H1.
      reflexivity.
    +
      unfold RStheta in *.
      generalize dependent (Vnth x kc).
      intros r H0 I0 H1 I1 NV.
      apply not_iff_compat in I0.
      apply not_iff_compat in I1.
      destruct I0 as [_ I0].
      destruct I1 as [_ I1].
      specialize (I0 NV).
      specialize (I1 NV).
      clear NV.
      apply NP.F.not_find_in_iff in I0.
      apply NP.F.not_find_in_iff in I1.
      rewrite I0, I1.
      reflexivity.
  -
    rewrite O0 by assumption.
    rewrite O1 by assumption.
    reflexivity.
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

  Definition mem_op_of_op {fm} {i o: nat} (op: svector fm i -> svector fm o)
    : mem_block -> option mem_block
    := fun x => Some (svector_to_mem_block (op (mem_block_to_svector fm x))).

(*
  (* this could only be proven wrt [@eq] on operators, not [((=)==>(=))].
     because [svector_to_mem_block] is used underneath.
 *)
  Global Instance mem_op_of_op_proper
         {fm}
         {i o: nat}:
    Proper ((eq) ==> (=)) (@mem_op_of_op fm i o).
  Proof.
    intros f g E mx my Em.
    unfold mem_op_of_op.
    f_equiv.
    f_equiv.
    apply equal_f with (x:=mem_block_to_svector fm mx) in E.
    rewrite_clear E.
    Seems to be tricky to prove. Let's postpone to see when it is needed.

    f_equiv.
    rewrite Em.
    reflexivity.
  Qed.


 *)

End Wrappers.

Section Operators.
  (* AKA: "embed" *)
  Definition eUnion_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x 0 (mem_empty) b.

  (* AKA "pick" *)
  Definition eT_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x b (mem_empty) 0.

  (* TODO: move to Util *)
  Fixpoint fold_left_rev
           {A B : Type}
           (f : A -> B -> A) (a : A) (l : list B)
    : A
    := match l with
       | List.nil => a
       | List.cons b l => f (fold_left_rev f a l) b
       end.

  Global Instance fold_left_rev_proper
         {A B : Type}
         `{Eb: Equiv B}
         `{Ae: Equiv A}
         `{Equivalence A Ae}
         (f : A -> B -> A)
         `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
         (a : A)
    :
      Proper ((=) ==> (=)) (fold_left_rev f a).
  Proof.
    intros x y E.
    induction E.
    -
      reflexivity.
    -
      simpl.
      apply f_mor; auto.
  Qed.

  Program Fixpoint Lbuild {A: Type}
          (n : nat)
          (gen : forall i, i < n -> A) {struct n}: list A :=
    match n with
    | 0 => List.nil
    | S p =>
      let gen' := fun i ip => gen (S i) _ in
      List.cons (gen 0 _) (@Lbuild A p gen')
    end.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

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
    := fun x =>
         match op1 x, op2 x with
         | Some a, Some b => mem_merge a b
         | _, _ => None
         end.

  Definition IReduction_mem
             {n: nat}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block): option mem_block
    :=
      x' <- (Apply_mem_Family op_family_f x) ;;
         ret (fold_left_rev (mem_merge_with_def dot initial) mem_empty x').

  Definition IUnion_mem
             {n: nat}
             (op_family_f: forall k (kc:k<n), mem_block -> option mem_block)
             (x: mem_block): option mem_block
    :=
      x' <- (Apply_mem_Family op_family_f x) ;;
         monadic_fold_left_rev mem_merge mem_empty x'.

End Operators.

Section Morphisms.

  Global Instance mem_keys_set_Proper:
    Proper ((=) ==> NS.Equal) (mem_keys_set).
  Proof.
    simpl_relation.
    rename H into E.
    rewrite <- 2!mem_keys_set_In.
    apply mem_in_proper; auto.
  Qed.

  Global Instance mem_union_proper:
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


  Global Instance mem_merge_proper:
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

  Global Instance mem_merge_with_proper
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

  Global Instance mem_merge_with_def_proper
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
      repeat some_inv; f_equiv; apply Efg; auto.
  Qed.

  Global Instance eUnion_mem_proper
         {b:nat}
    : Proper (equiv ==> equiv) (eUnion_mem b).
  Proof.
    simpl_relation.
    unfold eUnion_mem.
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

  Global Instance eT_mem_proper
         {b:nat}
    : Proper (equiv ==> equiv) (eT_mem b).
  Proof.
    simpl_relation.
    unfold eT_mem.
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

  Global Instance HTSUMUnion_mem_proper:
    Proper ((equiv ==> equiv) ==> (equiv ==> equiv) ==> equiv ==> equiv) (HTSUMUnion_mem).
  Proof.
    intros op0 op0' Eop0 op1 op1' Eop1 x y E.
    specialize (Eop0 x y E).
    specialize (Eop1 x y E).
    unfold HTSUMUnion_mem.
    repeat break_match; try some_none; try reflexivity.
    repeat some_inv.
    apply mem_merge_proper; auto.
  Qed.

End Morphisms.

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

Section MFamilies.

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

  Global Instance get_family_mem_op_proper
         {i o n: nat}
         (j: nat) (jc: j<n)
         (op_family: @MSHOperatorFamily i o n)
    :
      Proper ((=) ==> (=)) (get_family_mem_op op_family jc).
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
      -> (forall (j : nat) (jc : j < k), List.nth_error l j ≡ get_family_mem_op op_family jc m).
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
      get_family_mem_op op_family (Nat.lt_0_succ k) m ≡ Some m0 /\
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
            apply (m_family_in_set_includes_members (shrink_m_op_family_up op_family) nc1).
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
            apply (m_family_in_set_includes_members
                     (shrink_m_op_family_up op_family)
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
            apply (m_family_out_set_includes_members
                     (shrink_m_op_family_up op_family)
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
            apply (m_family_out_set_includes_members
                     (shrink_m_op_family_up op_family)
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

End MFamilies.

(* Note: We only define MSHCOL operators for final subset of SHCOL *)
Section MSHOperator_Definitions.

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

  Definition MSHeUnion
             {o b: nat}
             (bc: b < o)
    := @mkMSHOperator 1 o
                      (eUnion_mem b)
                      eUnion_mem_proper
                      (Full_set _)
                      (FinNatSet.singleton b).

  Definition MSHeT
             {i b: nat}
             (bc: b < i)
    := @mkMSHOperator i 1 (eT_mem b)
                      eT_mem_proper
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

  Definition MSHInductor
             (n:nat)
             (f: CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (initial: CarrierA)
    := @mkMSHOperator 1 1
                      (mem_op_of_hop (HInductor n f initial))
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
  Global Instance monadic_Lbuild_opt_proper
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

  Global Instance Apply_mem_Family_proper
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

  Global Instance IReduction_mem_proper
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


  Global Instance IUnion_mem_proper
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
      apply monadic_fold_left_rev_opt_proper.
      apply mem_merge_proper.
      apply Option_equiv_eq in Heqo0.
      apply Option_equiv_eq in Heqo1.
      rewrite E in Heqo0.
      rewrite Heqo0 in Heqo1.
      some_inv.
      apply Heqo1.
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


End MSHOperator_Definitions.

Section MSHOperator_Facts_instances.

  Global Instance SHCompose_MFacts
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
        pose proof (out_mem_fill_pattern m Heqo0) as P.
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
        pose proof (out_mem_fill_pattern  m1 H) as P1.
        apply P1; auto.
      +
        simpl in *.
        unfold option_compose in H.
        break_match_hyp; try some_none.
        pose proof (out_mem_fill_pattern m1 H) as P2.
        apply P2; auto.
    -
      (* mem_out_oob *)
      intros m0 m H.
      unfold MSHCompose in H.
      unfold option_compose in H.
      simpl in H.
      break_match_hyp; try some_none.
      pose proof (out_mem_oob  m1 H) as P2.
      apply P2; auto.
  Qed.

  Global Instance eUnion_MFacts
         {o b: nat}
         (bc: b < o)
    : MSHOperator_Facts (MSHeUnion bc).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros m H.
      unfold is_Some, MSHeUnion, eUnion_mem, map_mem_block_elt, mem_lookup. simpl.
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
        unfold eUnion_mem, map_mem_block_elt, mem_lookup, mem_in, mem_add, mem_empty in *.
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
        unfold eUnion_mem, map_mem_block_elt, mem_lookup, mem_in, mem_add, mem_empty in *.
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
      unfold eUnion_mem, map_mem_block_elt, mem_lookup, mem_in in *. simpl in *.
      break_match; try some_none.
      some_inv.
      subst m.
      unfold mem_add, mem_empty in C.
      destruct (eq_nat_dec j b); try omega.
      apply NP.F.in_find_iff in C.
      rewrite NP.F.add_neq_o in C; auto.
  Qed.

  Global Instance eT_MFacts
         {i b: nat}
         (bc: b<i)
    : MSHOperator_Facts (MSHeT bc).
  Proof.
    split.
    -
      (* mem_out_some *)
      intros v H.
      unfold is_Some, MSHeT, eT_mem, map_mem_block_elt, mem_lookup. simpl.
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
      unfold eT_mem, map_mem_block_elt, mem_lookup, mem_in in *.
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
      unfold eT_mem, map_mem_block_elt, mem_lookup, mem_in in *.

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

  Global Instance SHPointwise_MFacts
         {n: nat}
         (f: FinNat n -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    : MSHOperator_Facts (MSHPointwise (pF:=pF)).
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

  Global Instance SHInductor_MFacts
         (n:nat)
         (f: CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=)) f}
         (initial: CarrierA):
    MSHOperator_Facts (MSHInductor n initial (pF:=pF)).
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

  Global Instance SHBinOp_MFacts
         {o: nat}
         (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : MSHOperator_Facts (MSHBinOp (pF:=pF)).
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
      unfold HTSUMUnion_mem in E.
      repeat break_match_hyp; try some_none.
      apply mem_merge_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
      destruct E as [E0 E1].
      dependent destruction H; apply E1.
      *
        left.
        eapply (out_mem_fill_pattern _ Heqo0); eauto.
      *
        right.
        eapply (out_mem_fill_pattern _ Heqo1); eauto.
    +
      simpl in *.
      unfold HTSUMUnion_mem in E.
      repeat break_match_hyp; try some_none.
      apply mem_merge_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
      destruct E as [E0 E1].
      specialize (E0 H). clear H E1.
      destruct E0 as [M1 | M2].
      *
        apply Union_introl.
        eapply (out_mem_fill_pattern _ Heqo0); eauto.
      *
        right.
        eapply (out_mem_fill_pattern _ Heqo1); eauto.
  Qed.

  Global Instance HTSUMUnion_MFacts
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
        contradict Heqo0.
        clear H.
        apply mem_merge_is_Some.
        pose proof (out_mem_fill_pattern m Heqo1) as P1.
        pose proof (out_mem_oob m Heqo1) as NP1.
        pose proof (out_mem_fill_pattern m Heqo2) as P2.
        pose proof (out_mem_oob m Heqo2) as NP2.

        apply Disjoint_intro.
        intros j.
        destruct (NatUtil.lt_ge_dec j o) as [jc | jc].
        *
          clear NP1 NP2.
          specialize (P1 j jc).
          specialize (P2 j jc).
          destruct compat as [compat].
          specialize (compat (mkFinNat jc)).
          intros C.
          unfold Ensembles.In, not  in *.
          destruct C as [j H0 H1].

          apply NE.In_In, mem_keys_set_In, P1 in H0. clear P1.
          apply NE.In_In, mem_keys_set_In, P2 in H1. clear P2.
          destruct compat.
          apply Intersection_intro; auto.
        *
          specialize (NP1 j jc).
          intros C.
          destruct C as [j H0 _].
          apply NE.In_In, mem_keys_set_In in H0.
          unfold mem_in in NP1.
          congruence.
      +
        clear Heqo0.
        contradict Heqo2.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H0.
        specialize (H j jc).
        apply H.
        apply Union_intror.
        apply H0.
      +
        clear Heqo0.
        contradict Heqo1.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H0.
        specialize (H j jc).
        apply H.
        apply Union_introl.
        apply H0.
    -
      (* out_mem_fill_pattern *)
      eapply HTSUMUnion_mem_out_fill_pattern;
        typeclasses eauto.
    -
      intros m0 m E j jc H.
      simpl in *.
      unfold HTSUMUnion_mem in E.
      repeat break_match_hyp; try some_none.
      apply mem_merge_key_dec with (m0:=m1) (m1:=m2) (k:=j) in E.
      destruct E as [E0 E1].
      specialize (E0 H). clear H E1.
      destruct E0 as [M0 | M1].
      --
        eapply (out_mem_oob _ Heqo0); eauto.
      --
        eapply (out_mem_oob _ Heqo1); eauto.
  Qed.

  Global Instance IReduction_MFacts
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
                                                (MSHIReduction initial                                                                      (shrink_m_op_family_up op_family)) (mkFinNat jc) →
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
            eapply (out_mem_fill_pattern _ A0) with (jc:=jc).
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
    pose proof (out_mem_fill_pattern _ H) as H1.
    pose proof (out_mem_oob _ H) as H2.
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
       (H0: get_family_mem_op op_family tc1 m ≡ Some m0)

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
        rewrite (mem_keys_set_to_m_out_index_set _ H0) in compat.
        rewrite (mem_keys_set_to_m_out_index_set _ A0) in compat.
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
       (H0: get_family_mem_op op_family (Nat.lt_0_succ n) m ≡ Some m0)

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

  Global Instance IUnion_Mem
         {i o k: nat}
         `{svalue: MonUnit CarrierA}
         `{dot: SgOp CarrierA}
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         `{af_mon: @MathClasses.interfaces.abstract_algebra.Monoid CarrierA CarrierAe dot svalue}
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
      repeat break_match; try tauto.
      +
        contradict Heqo0.
        rename Heqo1 into A.
        pose proof (Apply_mem_Family_eq_Some A) as F.
        pose proof (Apply_mem_Family_length A) as L.
        revert l A F L.
        induction k; intros.
        *
          simpl in *.
          dep_destruct l. 2: inversion L.
          simpl.
          some_none.
        *
          dep_destruct l. inversion L.
          simpl.
          break_match.
          --
            clear IHk.
            apply mem_merge_is_Some.
            apply Apply_mem_Family_cons in A.
            destruct A as [A0 A].
            simpl in *.
            inversion L; clear l L; rename H1 into L, x into l.
            eapply IUnion_mem_1_step_disjoint; eauto.
          --
            contradict Heqo0.
            specialize (IHk
                          (shrink_m_op_family_up op_family)
                          (shrink_m_op_family_facts_up _ op_family_facts)
                       ).
            apply IHk; clear IHk.
            ++
              intros m1 mc n nc H0.
              apply compat.
              simpl.
              crush.
            ++
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
            ++
              apply Apply_mem_Family_cons in A.
              apply A.
            ++
              intros j jc.
              specialize (F (S j) (lt_n_S jc)).
              auto.
            ++
              crush.
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
          break_match_hyp; try some_none.

          apply (mem_merge_as_Union _ _ _ _ H).
          simpl in *.
          dependent destruction H0.
          --
            clear IHk A.
            right.
            unfold Ensembles.In in H0.
            eapply (out_mem_fill_pattern _ A0) with (jc:=jc).
            replace (Nat.lt_0_succ k) with (zero_lt_Sn k)
              by apply NatUtil.lt_unique.
            auto.
          --
            clear A0.
            left.

            specialize (IHk
                          _
                          dot
                          pdot
                          _
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
          simpl in H.
          break_match_hyp; try some_none.
          simpl in *.
          apply (mem_merge_as_Union _ _ _ _ H) in H0.
          dependent destruction H0.
          --
            clear A0.
            right.

            specialize (IHk
                          _
                          dot
                          pdot
                          _
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
        some_inv.
        subst l.
        simpl in *.
        some_inv.
        unfold mem_in,  mem_empty.
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
        break_match_hyp ; try some_none.
        apply (mem_merge_as_Union _ _ _ _ H) in C.
        destruct C.
        --
          clear A0.
          specialize (IHk
                        _
                        dot
                        pdot
                        _
                        (shrink_m_op_family_up op_family)
                        (shrink_m_op_family_facts_up _ op_family_facts)
                     ).
          eapply IHk;eauto.
        --
          apply out_mem_oob with (j0:=j) in A0; auto.
  Qed.


End MSHOperator_Facts_instances.
