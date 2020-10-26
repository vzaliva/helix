Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.LidBound.

(** ** New freshness invariant *)
Record state_invariant (σ : evalContext) (sinvs : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
  {
  mem_is_inv : memory_invariant σ sinvs memH configV ;
  IRState_is_WF : WF_IRState σ sinvs 
  }.

(* Definition freshness (s1 s2 : IRState) (l1 : local_env) : config_cfg -> Prop := *)
(*   fun '(_, (l2, _)) => *)
(*     alist_extend l1 l2 /\ *)
(*     (forall id v, alist_In id l1 v -> ~(lid_bound_between s1 s2 id)) /\ *)
(*     (forall id v, alist_In id l2 v -> ~(alist_In id l1 v) -> lid_bound_between s1 s2 id). *)

(*
Lemma freshness_local_count :
  forall (s1 s2 : IRState) (ρ : local_env) (memV : memoryV) (g : global_env),
    local_count s1 ≡ local_count s2 ->
    freshness s1 s2 ρ (memV, (ρ, g)).
Proof.
  intros s1 s2 ρ memV g COUNT.
  unfold freshness.
  split; try reflexivity.
  split.
  - intros id v H.
    intros B.
    unfold lid_bound_between in B.
    unfold state_bound_between in B.
    destruct B as (name & s' & s'' & NENDW & COUNT1 & COUNT2 & NAME).
    lia.
  - intros id v H.
    intros B.
    contradiction.
Qed.

Lemma freshness_ss_ρ :
  forall (s : IRState) (ρ : local_env) (memV : memoryV) (g : global_env),
    freshness s s ρ (memV, (ρ, g)).
Proof.
  intros s ρ memV g.
  apply freshness_local_count; auto.
Qed.

Lemma freshness_local_count_extend :
  forall (s1 s2 s3 : IRState) (ρ1 ρ2 : local_env) (memV : memoryV) (g : global_env),
    freshness s1 s2 ρ1 (memV, (ρ2, g)) ->
    local_count s2 ≡ local_count s3 ->
    freshness s1 s3 ρ1 (memV, (ρ2, g)).
Proof.
  intros s1 s2 s3 ρ1 ρ2 memV g [SUB [NIN IN]] COUNT.
  unfold freshness.
  split; auto.
  split; unfold lid_bound_between, state_bound_between in *; rewrite COUNT in *; auto.
Qed.

Lemma alist_In_dec :
  forall {K V} `{RelDec K} `{RelDec v} (id : K) (l : alist K V) (v : V),
    {alist_In id l v} + {~(alist_In id l v)}.
Proof.
Admitted.

Lemma freshness_split :
  forall (s1 s2 s3 : IRState)
    (l1 l2 l3 : local_env)
    (g1 g2 : global_env)
    (memV1 memV2 : memoryV),
    freshness s2 s3 l1 (memV1, (l2, g1)) ->
    freshness s1 s2 l2 (memV2, (l3, g2)) ->
    (local_count s1 <= local_count s2)%nat ->
    (local_count s3 ≥ local_count s2)%nat ->
    freshness s1 s3 l1 (memV2, (l3, g2)).
Proof.
  intros s1 s2 s3 l1 l2 l3 g1 g2 memV1 memV2 FRESH1 FRESH2 COUNTS1S2 COUNTS3S2.
  unfold freshness.
  destruct FRESH1 as (L1L2 & NBOUND1 & BOUND1).
  destruct FRESH2 as (L2L3 & NBOUND2 & BOUND2).
  split.
  - rewrite L1L2. auto.
  - split.
    + intros id v IN.
      intros B.

      (* If id is in l1, then it should be bound before s1 *)
      (* destruct FRESH3 as (L1L1 & NBOUND3 & BOUND3). *)

      (* can't be between s2 and s3 *)
      pose proof (NBOUND1 _ _ IN).
      
      (* l2 extends l1, and nothing in l2 can be bound between s1 and s2 *)
      eapply L1L2 in IN as (v' & IN).
      pose proof (NBOUND2 _ _ IN).

      (* Thus any id in l1 can't be bound between s1 and s3... *)
      eapply not_state_bound_between_split; eauto.
    + intros id v IN NIN.
      pose proof (alist_In_dec id l2 v) as [INL2 | NINL2].
      * eapply state_bound_between_shrink.
        eapply BOUND1.
        all: eauto.
      * eapply state_bound_between_shrink.
        eapply BOUND2.
        all: eauto.
Qed.

*)
(* (* sinvs is the state used for the invariants, whereas s1 and s2 are used for freshness. *) *)
(* Record new_state_invariant (σ : evalContext) (s1 s2 sinvs : IRState) (l1 : local_env) (memH : memoryH) (configV : config_cfg) : Prop := *)
(*   { *)
(*   mem_is_inv : memory_invariant σ sinvs memH configV ; *)
(*   IRState_is_WF : WF_IRState σ sinvs ; *)
(*   incLocal_is_fresh : freshness s1 s2 l1 configV *)
(*   }. 

Lemma freshness_no_lu :
  forall s1 s2 s3 l1 l2 id x g memH memV τ dv,
  incLocal s2 ≡ inr (s3, id) ->
  freshness s1 s3 l1 (memH, (l2, g)) ->
  in_local_or_global_scalar l2 g memV x dv τ ->
  x ≢ ID_Local id.
Proof.
  intros s1 s2 s3 l1 l2 id x g memH memV τ dv INC (L1L2 & NIN & IN) INLG.
  destruct x as [id' | id']; cbn in INLG.
  - intros CONTRA.
    discriminate CONTRA.
  - (* alist_In id' l2 (dvalue_to_uvalue dv) *)
    assert (alist_In id' l2 (dvalue_to_uvalue dv)) as INl2 by auto.
    epose proof (alist_In_dec id' l1 (dvalue_to_uvalue dv)) as [INl1 | NINl1].
    + (* id' is not bound between s1 and s2... *)
      pose proof (NIN _ _  INl1).

      (* I actually don't have enough to know that it would not be
      bound between s2 and s3 *)
      admit.
    + pose proof (IN _ _ INl2 NINl1).
Admitted.
 *)

(* Lemma lid_bound_later_fresh : *)
(*   forall s1 s2 s3 (l : local_env) m g id, *)
(*     freshness s1 s2 l (m, (l, g)) -> *)
(*     lid_bound s3 id -> *)
(*     (local_count s3 >= local_count s2)%nat -> *)
(*     (local_count s2 >= local_count s1)%nat -> *)
(*     l @ id ≡ None. *)
(* Proof. *)
(*   intros s1 s2 s3 l m g id (LL & NIN & IN) (name & s' & s'' & NEND & COUNT & GEN) COUNTS3S2 COUNTS2S1. *)
(*   apply alist_find_None. *)
(*   intros v IN'. *)
(*   eapply In__alist_In in IN'. *)
(*   destruct IN'. *)
(*   apply NIN in H. *)
(*   apply H. *)
(*   esplit; auto. *)
(*   eexists. eexists. *)
(*   repeat split. *)
(*   4: eauto. *)
(*   eauto. *)
(*   symmetry in GEN. apply incLocalNamed_local_count in GEN. *)
(*   lia. *)

(*   lia. *)
(*   apply name. *)
(*   epose proof alist_In_dec id l x as [INL1 | NINL1]. *)
(*   -  *)



(* (* Since id is in l1, we know that it can't be bound in s3 *)

(*        Because it would have had to be bound earlier. *)

(*        HOWEVER, we don't actually have a high water mark for this... *)

(*        Freshness does not allow me to conclude that something in l1 is *)
(*        earlier, only that it was not bound between the two states. *)

(*      *) *)
(* Admitted. *)

(* TODO: Move this *)
(* Lemma memory_invariant_Γ : *)
(*   forall σ s1 s2 memH memV ρ g, *)
(*     memory_invariant σ s1 memH (memV, (ρ, g)) -> *)
(*     Γ s1 ≡ Γ s2 -> *)
(*     memory_invariant σ s2 memH (memV, (ρ, g)). *)
(* Proof. *)
(*   intros σ s1 s2 memH memV ρ g MINV GAMMA. *)
(*   unfold memory_invariant in *. *)
(*   rewrite <- GAMMA. *)
(*   auto. *)
(* Qed. *)

(* Hint Resolve mem_is_inv IRState_is_WF : core. *)

(*
Lemma freshness_pre_extend :
  forall σ s1 s2 s3 memH memV l1 l2 g,
    state_invariant σ s1 s2 s2 l1 memH (memV, (l2, g)) ->
    Γ s2 ≡ Γ s3 ->
    local_count s2 ≡ local_count s3 ->
    state_invariant σ s1 s3 s3 l1 memH (memV, (l2, g)).
Proof.
  intros σ s1 s2 s3 memH memV l1 l2 g [MINV WF FRESH] COUNT.
  split.
  - eapply memory_invariant_Γ; eauto.
  - eapply WF_IRState_Γ; eauto.
  - eapply freshness_local_count_extend; eauto.
Qed.

Lemma state_invariant_shrink :
  forall σ s1 s1' s2 s2' sinv l memH memV g,
    state_invariant σ s1 s2 sinv l memH (memV, (l, g)) ->
    (local_count s1 <= local_count s1')%nat ->
    (local_count s2' <= local_count s2)%nat ->
    state_invariant σ s1' s2' sinv l memH (memV, (l, g)).
Proof.
  intros σ s1 s1' s2 s2' sinv l memH memV g SINV COUNT1 COUNT2.
  destruct SINV as [MINV WF FRESH].
  destruct FRESH as (EXT & NIN & IN).
  repeat (split; auto).
  - intros id v AIN BOUND.
    apply NIN in AIN.
    apply AIN.
    eapply state_bound_between_shrink; eauto.
  - intros id v AIN ANIN.
    contradiction.
Qed.
 *)


(*
Lemma freshness_add_between :
  forall (s1 s2 : IRState) (l1 l2 : local_env) (memV : memoryV) (g : global_env) id v,
    freshness s1 s2 l1 (memV, (l2, g)) ->
    lid_bound_between s1 s2 id ->
    freshness s1 s2 l1 (memV, (alist_add id v l2, g)).
Proof.
  intros s1 s2 l1 l2 memV g id v (EXT & NIN & IN) BETWEEN.
  repeat split; eauto.
  - rewrite EXT. apply alist_extend_add.
  - intros id0 v0 AIN ANIN.
    assert ({id0 ≡ id} + {id0 ≢ id}) as [IDEQ | IDNEQ] by apply rel_dec_p.
    + subst; auto.
    + apply In_add_In_ineq in AIN; eauto.
Qed.
 *)

(*
Lemma new_state_invariant_weaken_local_env :
  forall σ s1 s2 s3 s2' s3' sinv l1 l2 memH memV g,
    new_state_invariant σ s1 s2 sinv l1 memH (memV, (l2, g)) ->
    freshness s2' s3' l1 (memV, (l1, g)) ->
    s2' <<= s2 ->
    s3 << s3' ->
    new_state_invariant σ s2 s3 sinv l2 memH (memV, (l2, g)).
Proof.
  intros σ s1 s2 s3 s2' s3' sinv l1 l2 memH memV g [MINV WF FRESH1] FRESH2 LT1 LT2.
  split; auto.
  repeat split.
  - reflexivity.
  - intros id v AIN.
    intros BOUND.
    destruct (alist_In_dec id l1 v).
    + destruct FRESH2 as (_ & NIN & _).
      apply (NIN _ _ a).
      eapply (state_bound_between_shrink _ _ BOUND); solve_local_count.
    + destruct FRESH1 as (_ & _ & IN).
      pose proof (IN _ _ AIN n).
      eapply state_bound_between_separate.
      2: apply H.
      2: apply BOUND.
      apply incLocalNamed_count_gen_injective.
      solve_local_count.
      reflexivity.
  - intros id v AIN ANIN.
    contradiction.
Qed.
*)
 
