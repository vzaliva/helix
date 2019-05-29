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

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.util.

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

  Fixpoint monadic_fold_left_rev
           {A B : Type}
           {m : Type -> Type}
           {M : Monad m}
           (f : A -> B -> m A) (a : A) (l : list B)
    : m A
    := match l with
       | List.nil => ret a
       | List.cons b l => a' <- monadic_fold_left_rev f a l ;;
                    f a' b
       end.

  Program Fixpoint monadic_Lbuild
          {A: Type}
          {m : Type -> Type}
          {M : Monad m}
          (n : nat)
          (gen : forall i, i < n -> m A) {struct n}: m (list A) :=
    match n with
    | 0 => ret (List.nil)
    | S p =>
      let gen' := fun i ip => gen (S i) _ in
      liftM2 List.cons (gen 0 (lt_O_Sn p)) (@monadic_Lbuild A m M p gen')
    end.
  Next Obligation. apply lt_n_S, ip. Qed.

  Lemma monadic_Lbuild_cons
        {A: Type}
        {m : Type -> Type}
        {M : Monad m}
        (n : nat)
        (gen : forall i, i < S n -> m A)
    :
      monadic_Lbuild gen ≡
      liftM2 List.cons (gen 0 (lt_O_Sn n)) (monadic_Lbuild (fun i ip => gen (S i) (lt_n_S ip))).
  Proof.
    simpl.
    f_equiv.
    f_equiv.
    extensionality i.
    extensionality ip.
    f_equiv.
    apply NatUtil.lt_unique.
  Qed.

  Lemma monadic_Lbuild_opt_length
        {A: Type}
        (n : nat)
        (gen : forall i, i < n -> option A)
        (l: list A)
    :
      monadic_Lbuild gen ≡ Some l → Datatypes.length l ≡ n.
  Proof.
    intros H.
    dependent induction n.
    -
      simpl in H.
      some_inv.
      reflexivity.
    -
      destruct l.
      +
        exfalso.
        simpl in *.
        repeat break_match_hyp; try some_none.
        inversion H.
      +
        simpl.
        f_equiv.
        apply IHn with (gen:=fun i ip => gen (S i) (lt_n_S ip)).
        simpl in H.
        repeat break_match_hyp; try some_none.
        inversion H.
        subst.
        rewrite <- Heqo0.
        f_equiv.
        extensionality i.
        extensionality ip.
        f_equiv.
        apply NatUtil.lt_unique.
  Qed.

  (* Could be proven <-> *)
  Lemma monadic_Lbuild_op_eq_None
        {A: Type}
        (n : nat)
        (gen : forall i, i < n -> option A):

    monadic_Lbuild gen ≡ None -> exists i ic, gen i ic ≡ None.
  Proof.
    intros H.
    dependent induction n.
    -
      simpl in H.
      some_none.
    -
      simpl in H.
      repeat break_match_hyp; try some_none; clear H.
      +
        remember (λ (i : nat) (ip : i < n), gen (S i)
                                              (monadic_Lbuild_obligation_1 A option gen
                                                                           eq_refl ip))
          as gen' eqn:G.
        specialize (IHn gen' Heqo0).
        subst gen'.
        destruct IHn as [i [ic IHn]].
        eexists; eexists; eapply IHn.
      +
        eexists; eexists; eapply Heqo.
  Qed.

  Lemma monadic_Lbuild_op_eq_Some
        {A: Type}
        (n : nat)
        (gen : forall i, i < n -> option A)
        (l: list A)
    :

    monadic_Lbuild gen ≡ Some l -> (forall i ic, List.nth_error l i ≡ gen i ic).
  Proof.
    intros H i ic.
    pose proof (monadic_Lbuild_opt_length gen H).
    dependent induction n.
    -
      inversion ic.
    -
      destruct l as [| l0 l].
      inversion H0.
      simpl in H.
      destruct i.
      +
        repeat break_match_hyp; simpl in *; try some_none.
        inversion H.
        subst.
        rewrite <- Heqo.
        f_equiv.
        apply NatUtil.lt_unique.
      +
        simpl.
        specialize (IHn (fun i ip => gen (S i) (lt_n_S ip))).
        assert(ic1: i<n) by lia.
        rewrite IHn with (ic:=ic1); clear IHn.
        *
          f_equiv.
          apply NatUtil.lt_unique.
        *
          repeat break_match_hyp; simpl in *; try some_none.
          inversion H.
          subst.
          rewrite <- Heqo0.
          f_equiv.
          extensionality j.
          extensionality jc.
          f_equiv.
          apply NatUtil.lt_unique.
        *
          simpl in H0.
          auto.
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
    monadic_Lbuild (λ (j:nat) (jc:j<n), (op_family_f j jc) x).

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
