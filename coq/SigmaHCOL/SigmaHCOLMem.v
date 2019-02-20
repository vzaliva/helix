(* Memory-based implementations of SHCOL operators *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.
Require Import Omega.

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.Tactics.HelixTactics.

Global Open Scope nat_scope.
Set Implicit Arguments.

(* TODO: move somewhere, like FMapUtil.v *)
Section FMapUtil.

  Lemma NM_find_add_1:
    forall (elt:Type) (m : NM.t elt) (x y : NM.key) (e: elt),
      x = y ->
      NM.find y (NM.add x e m) = Some e.
  Proof.
    intros elt m x y e H.
    apply NM.find_1.
    apply NM.add_1.
    apply H.
  Qed.

  Lemma NM_find_add_3:
    forall (elt:Type) (m : NM.t elt) (x y : NM.key) (e: elt),
      x <> y ->
      NM.find y (NM.add x e m) = NM.find y m.
  Proof.
    intros elt m x y e H.
    match goal with
    | [ |- ?l = ?r ] => remember l as L; remember r as R
    end.
    destruct L, R; auto.
    -
      symmetry in HeqL.
      apply NM.find_2, NM.add_3, NM.find_1 in HeqL.
      rewrite <- HeqL, HeqR.
      reflexivity.
      apply H.
    -
      symmetry in HeqL.
      apply NM.find_2, NM.add_3, NM.find_1 in HeqL.
      rewrite <- HeqL, HeqR.
      reflexivity.
      apply H.
    -
      symmetry in HeqR.
      apply NM.find_2, NM.add_2 with (x:=x) (e':=e), NM.find_1  in HeqR.
      congruence.
      apply H.
  Qed.

End FMapUtil.

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
                                             v (@NM.empty B)) = None.
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
      rewrite NM_find_add_3 by omega.
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
                                                   v (@NM.empty B)) =
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
        rewrite NM_find_add_1 by reflexivity.
        rewrite NM_find_add_1 by reflexivity.
        reflexivity.
      *
        rewrite NM_find_add_3 by omega.
        rewrite NM_find_add_3 by omega.
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
                                                 v (@NM.empty B)) =
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
  =
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
      rewrite NM_find_add_3 by omega.
      reflexivity.
    +
      reflexivity.
Qed.

Lemma find_fold_right_indexed'_off:
  forall (n i : nat) (off:nat) (x : vector CarrierA n),
    NM.find (elt:=CarrierA) (i+off) (Vfold_right_indexed' (0+off) mem_add x mem_empty) =
    NM.find (elt:=CarrierA) i (Vfold_right_indexed' 0 mem_add x mem_empty).
Proof.
  intros n i off v.

  Let P := @Basics.const Prop CarrierA True.
  assert(Pdec: forall x, sumbool (P x) (not (P x)))
    by (intros x; left; unfold P, Basics.const;  tauto).
  Let f := @id CarrierA.
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
  + unfold f, id; reflexivity.
  + unfold P, Basics.const, not  in *; crush.
Qed.

Lemma find_fold_right_indexed'_S:
  forall (n i : nat) (v : vector CarrierA n),
    NM.find (elt:=CarrierA) (S i) (Vfold_right_indexed' 1 mem_add v mem_empty) =
    NM.find (elt:=CarrierA) i (Vfold_right_indexed' 0 mem_add v mem_empty).
Proof.
  intros n i v.

  replace (1) with (0+1) by lia.
  replace (S i) with (i+1) by lia.
  apply find_fold_right_indexed'_off.
Qed.

Program Definition avector_to_mem_block_spec
        {n : nat}
        (v : avector n):
  { m : mem_block | forall i (ip : i < n), mem_lookup i m = Some (Vnth v ip)}
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
      apply NM_find_add_1.
      reflexivity.
    +
      rewrite NM_find_add_3; auto.
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
  forall (k:nat) (kc:ge k n), mem_lookup k (avector_to_mem_block v) = None.
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
    rewrite NM_find_add_3 by omega.
    destruct k.
    +
      omega.
    +
      rewrite find_fold_right_indexed'_S.
      rewrite IHv.
      reflexivity.
      omega.
Qed.

Ltac avector_to_mem_block_to_spec m H0 H1 :=
  match goal with
    [ |- context[avector_to_mem_block_spec ?v]] =>
    pose proof (avector_to_mem_block_key_oob (v:=v)) as H1;
    unfold avector_to_mem_block in H1 ;
    destruct (avector_to_mem_block_spec v) as [m H0]
  end.


Definition mem_block_to_avector {n} (m: mem_block): option (vector CarrierA n)
  := vsequence (Vbuild (fun i (ic:i<n) => mem_lookup i m)).

Lemma mem_block_avector_id {n} {v:avector n}:
  (mem_block_to_avector (avector_to_mem_block v)) = Some v.
Proof.
  unfold mem_block_to_avector.
  apply vsequence_Vbuild_eq_Some.
  apply Veq_nth.
  intros i ip.
  rewrite Vbuild_nth.
  rewrite Vnth_map.
  unfold avector_to_mem_block.
  destruct (avector_to_mem_block_spec v) as [m H].
  apply H.
Qed.

(* HOperator (on dense vector) mapping to memory operator *)
Definition mem_op_of_hop {i o: nat} (op: vector CarrierA i -> vector CarrierA o)
  : mem_block -> option mem_block
  := fun x => match mem_block_to_avector x with
           | None => None
           | Some x' => Some (avector_to_mem_block (op x'))
           end.

(* y[j] := x[i] *)
Definition map_mem_block_elt (x:mem_block) (i:nat) (y:mem_block) (j:nat)
  : option mem_block :=
  match mem_lookup i x with
  | None => None
  | Some v => Some (mem_add j v y)
  end.

(* AKA: "embed" *)
Definition eUnion_mem (b: nat) (x:mem_block): option mem_block :=
  map_mem_block_elt x 0 (mem_empty) b.

(* AKA "pick" *)
Definition eT_mem (b: nat) (x:mem_block): option mem_block :=
  map_mem_block_elt x b (mem_empty) 0.

Fixpoint Gather_mem
         {i o: nat}
         (f: index_map o i)
         (x: mem_block) : option mem_block
  :=
    let i' := ⟦ f ⟧ o in
    let map_one ys := map_mem_block_elt x i' ys o in
    match o return (index_map o i) -> option mem_block with
    | O => fun _ => map_one (mem_empty)
    | S o' => fun f' =>
               match Gather_mem (shrink_index_map_domain f') x with
               | None => None
               | Some ys => map_one ys
               end
    end f.

Definition Scatter_mem {i o: nat} (f: index_map i o)
  : mem_block -> option mem_block
  :=
    let fix Scatter_mem'
            (j: nat)
            (fi: inverse_index_map f)
            (x: mem_block) : option mem_block
        :=
        let o' := inverse_index_f f fi j in
        let map_one ys := map_mem_block_elt x j ys o' in
        match j with
        | O => map_one (mem_empty)
        | S j' => match Scatter_mem' j' fi x with
                 | None => None
                 | Some ys => map_one ys
                 end
        end
    in
    Scatter_mem' i (build_inverse_index_map f).

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
