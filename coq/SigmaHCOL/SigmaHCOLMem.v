(* Memory-based implementations of SHCOL operators *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Lt.

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.Tactics.HelixTactics.

Global Open Scope nat_scope.

Set Implicit Arguments.

Definition avector_to_mem_block {n:nat} (v: avector n): mem_block
  := Vfold_right_indexed (fun i _ => mem_add i) v mem_empty.

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

(*
Program Definition avector_to_mem_block_spec
        {n : nat}
        (v : avector n):
  { m : mem_block | forall i (ip : i < n), mem_lookup i m = Some (Vnth v ip)}
  :=
    let fix loop
            {n':nat}
            (f : forall j, j < n' -> CarrierA -> mem_block -> mem_block)
            (v': avector n') : mem_block
        :=
        match v', n' as m return n'=m -> mem_block with
        | Vnil, _ => fun _ => mem_empty
        | Vcons x xs, n'' =>
          fun E =>
            let f' := fun i ip => f (S i) _  in
            f 0 _ x (loop f' xs)

        end eq_refl
    in
    loop (fun i (_:i<n) => mem_add i) v.
  Next Obligation. apply lt_n_S, ip. Qed.
  Next Obligation. apply zero_lt_Sn. Qed.
  Next Obligation.
  Proof.
    unfold mem_lookup.
    revert i ip; induction n; intros.
    -
      nat_lt_0_contradiction.
    -
      dep_destruct v;clear v.
      simpl.
      destruct i.
      +
        unfold avector_to_mem_block, mem_add.
        apply NM_find_add_1.
        reflexivity.
      +
        simpl.
        assert (N: i<n) by apply Lt.lt_S_n, ip.
        specialize (IHn x i N).
        replace (Lt.lt_S_n ip) with N by apply le_unique. clear ip.
        rewrite <- IHn; clear IHn.
  Defined.

Lemma avector_to_mem_block_spec_cons
      {n:nat}
      {i:nat} (ip: i<n)
      (x: CarrierA)
      (xs : vector CarrierA n):
  mem_lookup (S i) (avector_to_mem_block (x :: xs)) =
  mem_lookup i (avector_to_mem_block xs).
Proof.
  unfold mem_lookup, avector_to_mem_block, mem_add, NM.key.
  simpl.
  rewrite NM_find_add_3 by auto.
  clear x. rename xs into v.
Admitted.
 *)


Require Import Coq.Program.Equality. (* for `dependent induction` *)
Require Import Coq.FSets.FMapFacts.
Module Import F:=WFacts_fun Coq.Structures.OrderedTypeEx.Nat_as_OT NM.

Lemma avector_to_mem_block_spec
      (n : nat)
      (v : avector n)
      (i: nat)
      (ip : i < n)
  : mem_mapsto i (Vnth v ip) (avector_to_mem_block v).
Proof.
  unfold mem_mapsto.
  apply NM.find_2.
  revert i ip; induction n; intros.
  -
    nat_lt_0_contradiction.
  -
    dep_destruct v;clear v.
    simpl.
    induction i.
    +
      intros.
      unfold avector_to_mem_block, mem_add.
      simpl.
      apply NM_find_add_1.
      reflexivity.
    +
      simpl.
      assert (N: i<n) by apply Lt.lt_S_n, ip.
      specialize (IHn x i N).
      replace (Lt.lt_S_n ip) with N by apply le_unique. clear ip.
      rewrite <- IHn; clear IHn.
      apply avector_to_mem_block_spec_cons, N.
Qed.

Definition mem_block_to_avector {n} (m: mem_block): option (vector CarrierA n)
  := vsequence (Vbuild (fun i (ic:i<n) => mem_lookup i m)).

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
