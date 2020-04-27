Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Omega.
Require Import Psatz.
Require Import CoLoR.Util.Nat.NatUtil.

Require Import Helix.HCOL.CarrierType.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.MSigmaHCOL.MemoryOfCarrierA.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.

(* When proving concrete functions we need to use
   some implementation defs from this packages *)
Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.FinNat.

Require Import MathClasses.misc.util.
Require Import MathClasses.misc.decision.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.Tactics.HelixTactics.

Open Scope string_scope.
Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Import DSHCOLOnCarrierA.

(* TODO: move to Memory.v *)
(* problem: some of these depend on MemSetoid.v, which depends on Memory.v *)
Section memory_aux.

  (* [m_sub] ⊆ [m_sup] *)
  Definition memory_subset (m_sub m_sup : memory) :=
    forall k b, memory_mapsto m_sub k b -> memory_mapsto m_sup k b.

  (* Two memory locations equivalent on all addresses except one
     TODO: make `e` 1st parameter to make this relation.
   *)
  Definition memory_equiv_except (m m': memory) (e:mem_block_id)
    := forall k, k ≢ e -> memory_lookup m k = memory_lookup m' k.

  (* Relation between memory location defined as:
     1. All addresses except [e] from 1st memory must map to same memory blocks in the 2nd one.
     2. If 1st memory block has [e] initialized it also must be initialized in the 2nd one but not necessary with the same value.
   *)
  Definition memory_subset_except (e : mem_block_id) (m_sub m_sup : memory) :=
    forall k v,
      memory_lookup m_sub k = Some v ->
      exists v', (memory_lookup m_sup k = Some v' /\ (k ≢ e -> v = v')).

  Global Instance memory_subset_except_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) memory_subset_except.
  Proof.
    intros e e' Ee m_sub m_sub' ESUB m_sup m_sup' ESUP.
    unfold equiv, NatAsNT.MNatAsNT.NTypeEquiv, nat_equiv in Ee.
    subst e'.
    unfold memory_subset_except.
    split; intros.
    -
      rewrite <- ESUB in H0.
      specialize (H k v H0).
      destruct H as [v' H].
      exists v'.
      rewrite <- ESUP.
      apply H.
    -
      rewrite ESUB in H0.
      specialize (H k v H0).
      destruct H as [v' H].
      exists v'.
      rewrite ESUP.
      apply H.
  Qed.

  Lemma memory_equiv_except_memory_set {m m' b k}:
    m' ≡ memory_set m k b -> memory_equiv_except m m' k.
  Proof.
    intros H.
    subst.
    intros k' kc.
    unfold memory_set.
    unfold memory_lookup.
    rewrite NP.F.add_neq_o.
    reflexivity.
    auto.
  Qed.
  
  Lemma memory_equiv_except_trans {m m' m'' k}:
    memory_equiv_except m m' k ->
    memory_equiv_except m' m'' k ->
    memory_equiv_except m m'' k.
  Proof.
    intros H H0.
    intros k' kc.
    specialize (H0 k' kc).
    rewrite <- H0. clear H0.
    apply H.
    apply kc.
  Qed.

  Lemma mem_add_comm
        (k1 k2: NM.key)
        (v1 v2: CarrierA)
        (N: k1≢k2)
        (m: mem_block):
    mem_add k1 v1 (mem_add k2 v2 m) = mem_add k2 v2 (mem_add k1 v1 m).
  Proof.
    intros y.
    unfold mem_add.
    destruct (Nat.eq_dec y k1) as [K1| NK1].
    -
      subst.
      rewrite NP.F.add_eq_o by reflexivity.
      rewrite NP.F.add_neq_o by auto.
      symmetry.
      apply Option_equiv_eq.
      apply NP.F.add_eq_o.
      reflexivity.
    -
      rewrite NP.F.add_neq_o by auto.
      destruct (Nat.eq_dec y k2) as [K2| NK2].
      subst.
      rewrite NP.F.add_eq_o by reflexivity.
      rewrite NP.F.add_eq_o by reflexivity.
      reflexivity.
      rewrite NP.F.add_neq_o by auto.
      rewrite NP.F.add_neq_o by auto.
      rewrite NP.F.add_neq_o by auto.
      reflexivity.
  Qed.

  Lemma mem_add_overwrite
        (k : NM.key)
        (v1 v2 : CarrierA)
        (m : NM.t CarrierA) :
    mem_add k v2 (mem_add k v1 m) = mem_add k v2 m.
  Proof.
    intros.
    unfold mem_add, equiv, mem_block_Equiv.
    intros.
    destruct (Nat.eq_dec k k0).
    -
      repeat rewrite NP.F.add_eq_o by assumption.
      reflexivity.
    -
      repeat rewrite NP.F.add_neq_o by assumption.
      reflexivity.
  Qed.

  Lemma mem_block_to_avector_nth
        {n : nat}
        {mx : mem_block}
        {vx : vector CarrierA n}
        (E: mem_block_to_avector mx ≡ Some vx)
        {k: nat}
        {kc: (k < n)%nat}:
    mem_lookup k mx ≡ Some (Vnth vx kc).
  Proof.
    unfold mem_block_to_avector in E.
    apply vsequence_Vbuild_eq_Some in E.
    apply Vnth_arg_eq with (ip:=kc) in E.
    rewrite Vbuild_nth in E.
    rewrite Vnth_map in E.
    apply E.
  Qed.
  
  Lemma mem_op_of_hop_x_density
        {i o: nat}
        {op: vector CarrierA i -> vector CarrierA o}
        {x: mem_block}
    :
      is_Some (mem_op_of_hop op x) -> (forall k (kc:k<i), is_Some (mem_lookup k x)).
  Proof.
    intros H k kc.
    unfold mem_op_of_hop in H.
    break_match_hyp; try some_none.
    apply mem_block_to_avector_nth with (kc0:=kc) in Heqo0.
    apply eq_Some_is_Some in Heqo0.
    apply Heqo0.
  Qed.

  Lemma memory_lookup_err_inr_is_Some {s : string} (m : memory) (mbi : mem_block_id) :
    forall mb, memory_lookup_err s m mbi ≡ inr mb → is_Some (memory_lookup m mbi).
  Proof.
    intros.
    unfold memory_lookup_err, trywith in H.
    break_match.
    reflexivity.
    inversion H.
  Qed.

  Lemma memory_subset_except_next_keys m_sub m_sup e:
    memory_subset_except e m_sub m_sup ->
    (memory_next_key m_sup) >= (memory_next_key m_sub).
  Proof.
    intros H.
    destruct (memory_next_key m_sub) eqn:E.
    -
      lia.
    -
      rename m into k.
      apply memory_next_key_S in E.
      apply memory_is_set_is_Some in E.
      apply util.is_Some_def in E.
      destruct E as [v E].
      specialize (H k).
      cut (memory_next_key m_sup > k).
      {
        clear.
        intros G.
        lia.
      }
      apply mem_block_exists_next_key_gt.
      destruct (Nat.eq_dec k e) as [EK|NEK].
      +
        (* excluded element *)
        subst.
        specialize (H v).
        eq_to_equiv_hyp.
        apply H in E.
        destruct E as [v' [E _]].
        apply mem_block_exists_exists_equiv.
        exists v'.
        apply E.
      +
        eq_to_equiv_hyp.
        specialize (H v E).
        destruct H as [v' [H  V]].
        apply mem_block_exists_exists_equiv.
        exists v'.
        apply H.
  Qed.

End memory_aux.

(* This relations represents consistent memory/envirnment combinations.
   That means all pointer variables should resolve to existing memory blocks *)
Inductive EnvMemoryConsistent: evalContext -> memory -> Prop :=
| EmptyEnvConsistent: forall m, EnvMemoryConsistent [] m
| DSHPtrValConsistent: forall σ m a n,
    mem_block_exists a m ->
    EnvMemoryConsistent σ m ->
    EnvMemoryConsistent (DSHPtrVal a n :: σ) m

(* the remaining case does not depend on memory and just recurses over environment *)
| DSHnatValConsistent : forall σ m n, EnvMemoryConsistent σ m ->
                                 EnvMemoryConsistent (DSHnatVal n :: σ) m
| DSHCTypeValConsistent: forall σ m a, EnvMemoryConsistent σ m ->
                                  EnvMemoryConsistent (DSHCTypeVal a :: σ) m.

Lemma EnvMemoryConsistent_inv (a : DSHVal) (σ : evalContext) (mem : memory) :
  EnvMemoryConsistent (a :: σ) mem -> EnvMemoryConsistent σ mem.
Proof.
  intros; inversion H; auto.
Qed.

Lemma EnvMemoryConsistent_memory_lookup
      {σ : evalContext}
      {mem : memory}
      {EC : EnvMemoryConsistent σ mem}
      (v : var_id)
      (a : mem_block_id)
      (n : nat) :
  List.nth_error σ v = Some (DSHPtrVal a n) →
  is_Some (memory_lookup mem a).
Proof.
  intros.
  dependent induction σ; [destruct v; inversion H |].
  destruct v.
  -
    clear IHσ.
    cbn in H; some_inv.
    destruct a; inversion H; clear H; subst.
    inversion EC; subst.
    apply memory_is_set_is_Some.
    destruct H1.
    rewrite <-H0.
    assumption.
  -
    eapply IHσ.
    eapply EnvMemoryConsistent_inv; eassumption.
    cbn in H; eassumption.
Qed.

(* Shows relations of cells before ([b]) and after ([a]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [d] *)
Inductive MemOpDelta (b a d: option CarrierA) : Prop :=
| MemPreserved: is_None d -> b = a -> MemOpDelta b a d (* preserving memory state *)
| MemExpected: is_Some d -> a = d -> MemOpDelta b a d (* expected results *).

Global Instance MemOpDelta_proper:
  Proper ((=) ==> (=) ==> (=) ==> (iff)) MemOpDelta.
Proof.
  intros b b' Eb a a' Ea d d' Ed.
  split; intros H.
  -
    destruct H.
    +
      apply is_None_def in H.
      subst d.
      inversion_clear Ed.
      apply MemPreserved.
      *
        some_none.
      *
        rewrite <- Eb, <- Ea.
        assumption.
    +
      norm_some_none.
      subst d.
      rewrite Ea in H0. clear Ea a.
      dep_destruct d'; try some_none.
      apply MemExpected.
      *
        some_none.
      *
        rewrite H0.
        assumption.
  -
    destruct H.
    +
      apply is_None_def in H.
      subst d'.
      inversion_clear Ed.
      apply MemPreserved.
      *
        some_none.
      *
        rewrite Eb, Ea.
        assumption.
    +
      norm_some_none.
      subst d'.
      rewrite <-Ea in H0. clear Ea a'.
      dep_destruct d; try some_none.
      apply MemExpected.
      *
        some_none.
      *
        rewrite H0.
        symmetry.
        assumption.
Qed.

(* Shows relations of memory blocks before ([mb]) and after ([ma]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [md] *)
Definition SHCOL_DSHCOL_mem_block_equiv (mb ma md: mem_block) : Prop :=
  forall i,
    MemOpDelta
      (mem_lookup i mb)
      (mem_lookup i ma)
      (mem_lookup i md).

Require Import CoLoR.Util.Relation.RelUtil.

Definition lookup_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  a <- evalPexp σ p ;;
    memory_lookup_err "block_id not found" m a.

(*
Definition valid_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  err_p (fun k => mem_block_exists k m) (evalPexp σ p).

(* Simplified version. Uses [equiv] only for memory. Could be proven more generally *)
Global Instance valid_Pexp_proper:
  Proper ((eq) ==> (=) ==> (eq) ==> iff) (valid_Pexp).
Proof.
  intros s0 s1 Es m0 m1 Em p0 p1 Ep.
  subst.
  split; intros H.
  -
    unfold valid_Pexp in *.
    destruct (evalPexp s1 p1).
    +
      inversion H.
    +
      inversion H.
      subst.
      constructor.
      rewrite <- Em.
      apply H1.
  -
    unfold valid_Pexp in *.
    destruct (evalPexp s1 p1).
    +
      inversion H.
    +
      inversion H.
      subst.
      constructor.
      rewrite Em.
      apply H1.
Qed.

Lemma valid_Pexp_incrPVar
      (p : PExpr)
      (m : memory)
      (σ : evalContext)
      (foo: DSHVal)
  :
    valid_Pexp σ m p  -> valid_Pexp (foo :: σ) m (incrPVar 0 p).
Proof.
  unfold valid_Pexp.
  intros H.
  inversion H. clear H.
  rewrite <- evalPexp_incrPVar with (foo:=foo) in H0.
  rewrite <- H0.
  constructor.
  apply H1.
Qed.
*)

(*
   - [evalPexp σ p] must not to fail
   - [memory_lookup] must succeed
 *)
Definition blocks_equiv_at_Pexp (σ0 σ1:evalContext) (p:PExpr): rel (memory)
  := fun m0 m1 =>
       herr (fun a b => (opt equiv (memory_lookup m0 a) (memory_lookup m1 b)))
           (evalPexp σ0 p) (evalPexp σ1 p).

(* DSH expression as a "pure" function by enforcing the memory
   invariants guaranteeing that it depends only input memory block and
   modifies only output memory block.

   It is assumed that the memory and envirnment are consistent and
   [PExp] successfuly resolve to valid memory locations for [x_p] and
   [y_p] which must be allocated.

 *)
Class DSH_pure
      (d: DSHOperator)
      (y_p: PExpr)
  := {

      (* does not free or allocate any memory *)
      mem_stable: forall σ m m' fuel,
        evalDSHOperator σ d m fuel = Some (inr m') ->
        forall k, mem_block_exists k m <-> mem_block_exists k m';

      (* modifies only [y_p], which must be valid in [σ] *)
      mem_write_safe: forall σ m m' fuel,
          evalDSHOperator σ d m fuel = Some (inr m') ->
          (forall y_i , evalPexp σ y_p = inr y_i ->
                   memory_equiv_except m m' y_i)
    }.

(** Given MSHCOL and DSHCOL operators are quivalent, if wrt [x_i] and
    input memory block addres and [y_i] as output.

    It is assumed that we know what memory blocks are used as input
    [x_i] and output [y_i], of the operator. They both must exists (be
    allocated) prior to execution.

    We do not require input block to be structurally correct, because
    [mem_op] will just return an error in this case.  *)
Class MSH_DSH_compat
      {i o: nat}
      (mop: @MSHOperator i o)
      (dop: DSHOperator)
      (σ: evalContext)
      (m: memory)
      (x_p y_p: PExpr)
      `{DSH_pure dop y_p}
  := {
      eval_equiv
      :
        forall (mx mb: mem_block),
          (lookup_Pexp σ m x_p = inr mx) (* input exists *) ->
          (lookup_Pexp σ m y_p = inr mb) (* output before *) ->

          (* [md] - memory diff *) 
          (* [m'] - memory state after execution *) 
          (h_opt_opterr_c
             (fun md m' => err_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md)
                              (lookup_Pexp σ m' y_p))
             (mem_op mop mx)
             (evalDSHOperator σ dop m (estimateFuel dop)));
    }.

Inductive context_pos_typecheck: evalContext -> var_id -> DSHType -> Prop :=
| context0_tc {v: DSHVal} {t: DSHType} (cs:evalContext):
    DSHValType v t -> context_pos_typecheck (v::cs) 0 t
| contextS_tc {v: DSHVal} {t: DSHType} (n:nat) (cs:evalContext):
    context_pos_typecheck cs n t ->
    DSHValType v t -> context_pos_typecheck (v::cs) (S n) t.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive NExpr_typecheck: NExpr -> evalContext -> Prop :=
| NVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHnat ->  NExpr_typecheck (NVar n) σ
| NConst_tc (σ: evalContext) {a}: NExpr_typecheck (NConst a) σ
| NDiv_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NDiv a b) σ
| NMod_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMod a b) σ
| NPlus_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NPlus a b) σ
| NMinus_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMinus a b) σ
| NMult_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMult a b) σ
| NMin_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMin a b) σ
| NMax_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMax a b) σ.

(* Check if [PExpr] is properly typed in given evaluation context *)
Inductive PExpr_typecheck: PExpr -> evalContext -> Prop :=
| PVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHPtr -> PExpr_typecheck (PVar n) σ.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive MExpr_typecheck: MExpr -> evalContext -> Prop :=
| MPtrDeref_tc (σ: evalContext) (n:var_id):
    PExpr_typecheck (PVar n) σ -> MExpr_typecheck (MPtrDeref (PVar n)) σ
| MConst_tc (σ: evalContext) {a}: MExpr_typecheck (MConst a) σ.

(* Check if [AExpr] is properly typed in given evaluation context *)
Inductive AExpr_typecheck: AExpr -> evalContext -> Prop
  :=
  | AVar_tc (σ: evalContext) (n:var_id):
      context_pos_typecheck σ n DSHCType ->  AExpr_typecheck (AVar n) σ
  | AConst_tc (σ: evalContext) {a}: AExpr_typecheck (AConst a) σ
  | ANth_tc (σ: evalContext) (me:MExpr) (ne:NExpr) :
      MExpr_typecheck me σ ->
      NExpr_typecheck ne σ ->
      AExpr_typecheck (ANth me ne) σ
  | AAbs_tc (σ: evalContext) (e:AExpr):
      AExpr_typecheck e σ -> AExpr_typecheck (AAbs e) σ
  | APlus_tc  (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (APlus  a b) σ
  | AMinus_tc (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMinus a b) σ
  | AMult_tc  (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMult  a b) σ
  | AMin_tc   (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMin   a b) σ
  | AMax_tc   (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMax   a b) σ
  | AZless_tc (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AZless a b) σ.

Section BinCarrierA.

  Class MSH_DSH_BinCarrierA_compat
        (f : CarrierA -> CarrierA -> CarrierA)
        (σ : evalContext)
        (df : AExpr)
        (mem : memory)
    :=
      {
        bin_equiv:
          forall a b, evalBinCType mem σ df a b = inr (f a b)
      }.

  Class MSH_DSH_IUnCarrierA_compat
        {o: nat}
        (f: {n:nat|n<o} -> CarrierA -> CarrierA)
        (σ: evalContext)
        (df : AExpr)
        (mem : memory)
    :=
      {
        iun_equiv:
          forall nc a, evalIUnCType mem σ df (proj1_sig nc) a = inr (f nc a)
      }.

  Class MSH_DSH_IBinCarrierA_compat
        {o: nat}
        (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
        (σ: evalContext)
        (df : AExpr)
        (mem : memory)
    :=
      {
        ibin_equiv:
          forall nc a b, evalIBinCType mem σ df (proj1_sig nc) a b = inr (f nc a b)
      }.
  
  Instance Abs_MSH_DSH_IBinCarrierA_compat
    :
      forall σ mem,
        MSH_DSH_IBinCarrierA_compat
          (λ i (a b : CarrierA),
           IgnoreIndex abs i
                       (HCOL.Fin1SwapIndex2 (n:=2)
                                            jf
                                            (IgnoreIndex2 sub) i a b))
          σ
          (AAbs (AMinus (AVar 1) (AVar 0))) mem.
  Proof.
    split.
    intros nc a b.
    unfold evalIBinCType.
    f_equiv.
  Qed.

  Lemma evalDSHIMap_mem_lookup_mx
        {n: nat}
        {df : AExpr}
        {σ : evalContext}
        {mem : memory}
        {mx mb ma : mem_block}
        (E: evalDSHIMap mem n df σ mx mb = inr ma)
        (k: nat)
        (kc:k<n):
    is_Some (mem_lookup k mx).
  Proof.
    apply inr_is_OK in E.
    revert mb E k kc.
    induction n; intros.
    -
      inversion kc.
    -
      destruct (Nat.eq_dec k n).
      +
        subst.
        cbn in *.
        unfold mem_lookup_err, trywith in *.
        repeat break_match_hyp; try inl_inr.
        split; reflexivity.
      +
        simpl in *.
        repeat break_match_hyp; try inl_inr.
        apply eq_inr_is_OK in Heqs. rename Heqs into H1.
        apply eq_inr_is_OK in Heqs0. rename Heqs0 into H2.
        apply IHn with (mb:=mem_add n c0 mb); clear IHn.
        *
          apply E.
        *
          lia.
  Qed.

  Lemma evalDSHBinOp_mem_lookup_mx
        {n off: nat}
        {df : AExpr}
        {σ : evalContext}
        {mem : memory}
        {mx mb ma : mem_block}
        (E: evalDSHBinOp mem n off df σ mx mb = inr ma)
        (k: nat)
        (kc:k<n):
    is_Some (mem_lookup k mx) /\ is_Some (mem_lookup (k+off) mx).
  Proof.
    apply inr_is_OK in E.
    revert mb E k kc.
    induction n; intros.
    -
      inversion kc.
    -
      destruct (Nat.eq_dec k n).
      +
        subst.
        cbn in *.
        unfold mem_lookup_err, trywith in *.
        repeat break_match_hyp; try inl_inr.
        split; reflexivity.
      +
        simpl in *.
        repeat break_match_hyp; try inl_inr.
        apply eq_inr_is_OK in Heqs. rename Heqs into H1.
        apply eq_inr_is_OK in Heqs0. rename Heqs0 into H2.
        clear Heqs1 c c0.
        apply IHn with (mb:=mem_add n c1 mb); clear IHn.
        *
          apply E.
        *
          lia.
  Qed.

  Fact evalDSHIMap_preservation
       {n k: nat}
       {kc: k>=n}
       {df : AExpr}
       {σ : evalContext}
       {mem : memory}
       {mx ma mb : mem_block}
       {c : CarrierA}:
    evalDSHIMap mem n df σ mx (mem_add k c mb) = inr ma
    → mem_lookup k ma = Some c.
  Proof.
    revert mb k kc.
    induction n; intros mb k kc E.
    -
      simpl in *.
      inl_inr_inv.
      unfold mem_lookup, mem_add in *.
      rewrite <- E.
      apply Option_equiv_eq.
      apply NP.F.add_eq_o.
      reflexivity.
    -
      simpl in E.
      repeat break_match_hyp; try inl_inr.
      apply IHn with (mb:=mem_add n c1 mb).
      lia.
      rewrite mem_add_comm by auto.
      apply E.
  Qed.

  Fact evalDSHBinOp_preservation
       {n off k: nat}
       {kc: k>=n}
       {df : AExpr}
       {σ : evalContext}
       {mem : memory}
       {mx ma mb : mem_block}
       {c : CarrierA}:
    evalDSHBinOp mem n off df σ mx (mem_add k c mb) = inr ma
    → mem_lookup k ma = Some c.
  Proof.
    revert mb k kc.
    induction n; intros mb k kc E.
    -
      simpl in *.
      inl_inr_inv.
      unfold mem_lookup, mem_add in *.
      rewrite <- E.
      apply Option_equiv_eq.
      apply NP.F.add_eq_o.
      reflexivity.
    -
      simpl in E.
      repeat break_match_hyp; try inl_inr.
      apply IHn with (mb:=mem_add n c2 mb).
      lia.
      rewrite mem_add_comm by auto.
      apply E.
  Qed.

  Lemma evalDSHIMap_nth
        {n: nat}
        {df : AExpr}
        {σ : evalContext}
        {mx mb ma : mem_block}
        (mem : memory)
        (k: nat)
        (kc: k<n)
        {a: CarrierA}:
    (mem_lookup k mx = Some a) ->
    (evalDSHIMap mem n df σ mx mb = inr ma) ->
    h_opt_err_c (=) (mem_lookup k ma) (evalIUnCType mem σ df k a).
  Proof.
    intros A E.
    revert mb a A E.
    induction n; intros.
    -
      inversion kc.
    -
      simpl in *.
      repeat break_match_hyp; try some_none; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        clear IHn.
        subst k.
        unfold mem_lookup_err, trywith in *.
        repeat break_match; try inl_inr.
        repeat some_inv; repeat inl_inr_inv; subst.
        eq_to_equiv_hyp.
        err_eq_to_equiv_hyp.
        rewrite A in *; clear A c.

        assert (mem_lookup n ma = Some c0).
        {
          eapply evalDSHIMap_preservation.
          eassumption.
          Unshelve.
          reflexivity.
        }
        rewrite Heqs0, H.
        constructor.
        reflexivity.
      +
        apply IHn with (mb:=mem_add n c0 mb); auto.
        lia.
  Qed.

  Lemma evalDSHBinOp_nth
        {n off: nat}
        {df : AExpr}
        {σ : evalContext}
        {mx mb ma : mem_block}
        (mem : memory)
        (k: nat)
        (kc: k<n)
        {a b : CarrierA}:
    (mem_lookup k mx = Some a) ->
    (mem_lookup (k + off) mx = Some b) ->
    (evalDSHBinOp mem n off df σ mx mb = inr ma) ->
    h_opt_err_c (=) (mem_lookup k ma) (evalIBinCType mem σ df k a b).
  Proof.
    intros A B E.
    revert mb a b A B E.
    induction n; intros.
    -
      inversion kc.
    -
      simpl in *.
      repeat break_match_hyp; try some_none; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        clear IHn.
        subst k.
        unfold mem_lookup_err, trywith in *.
        repeat break_match; try inl_inr.
        repeat some_inv; repeat inl_inr_inv; subst.
        eq_to_equiv_hyp.
        err_eq_to_equiv_hyp.
        rewrite A in *; clear A c.
        rewrite B in *; clear B c0.

        assert (mem_lookup n ma = Some c1).
        {
          eapply evalDSHBinOp_preservation.
          eassumption.
          Unshelve.
          reflexivity.
        }

        clear - Heqs1 H.
        rewrite Heqs1, H.
        constructor.
        reflexivity.
      +
        apply IHn with (mb:=mem_add n c1 mb); auto.
        lia.
  Qed.

  Lemma evalDSHIMap_oob_preservation
        {n: nat}
        {df : AExpr}
        {σ : evalContext}
        {mx mb ma : mem_block}
        (mem : memory)
        (ME: evalDSHIMap mem n df σ mx mb = inr ma):
    ∀ (k : NM.key) (kc:k>=n), mem_lookup k mb = mem_lookup k ma.
  Proof.
    intros k kc.
    revert mb ME.
    induction n; intros.
    -
      inversion kc; simpl in ME; inl_inr_inv; rewrite ME; reflexivity.
    -
      simpl in *.
      repeat break_match_hyp; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        apply IHn; lia.
      +
        replace (mem_lookup k mb) with
            (mem_lookup k (mem_add n c0 mb)).
        apply IHn. clear IHn.
        lia.
        apply ME.
        apply NP.F.add_neq_o.
        auto.
  Qed.

  Lemma evalDSHBinOp_oob_preservation
        {n off: nat}
        {df : AExpr}
        {σ : evalContext}
        {mx mb ma : mem_block}
        (mem : memory)
        (ME: evalDSHBinOp mem n off df σ mx mb = inr ma):
    ∀ (k : NM.key) (kc:k>=n), mem_lookup k mb = mem_lookup k ma.
  Proof.
    intros k kc.
    revert mb ME.
    induction n; intros.
    -
      inversion kc; simpl in ME; inl_inr_inv; rewrite ME; reflexivity.
    -
      simpl in *.
      repeat break_match_hyp; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        apply IHn; lia.
      +
        replace (mem_lookup k mb) with
            (mem_lookup k (mem_add n c1 mb)).
        apply IHn. clear IHn.
        lia.
        apply ME.
        apply NP.F.add_neq_o.
        auto.
  Qed.
  
  
  (* This is generalized version of [evalDSHBinOp_nth]
     TODO see if we can replace [evalDSHBinOp_nth] with it
     or at lease simplify its proof using this lemma.
  *)
  Lemma evalDSHBinOp_equiv_inr_spec
        {off n: nat}
        {df : AExpr}
        {σ : evalContext}
        {mem : memory}
        {mx mb ma : mem_block}:
    (evalDSHBinOp mem n off df σ mx mb = inr ma)
    ->
    (∀ k (kc: k < n),
        ∃ a b,
          (mem_lookup k mx = Some a /\
           mem_lookup (k+off) mx = Some b /\
           (exists c,
               mem_lookup k ma = Some c /\
               evalIBinCType mem σ df k a b = inr c))
    ).
  Proof.
    intros E k kc.
    pose proof (evalDSHBinOp_mem_lookup_mx E) as [A B] ; eauto.
    apply is_Some_equiv_def in A.
    destruct A as [a A].
    apply is_Some_equiv_def in B.
    destruct B as [b B].
    exists a.
    exists b.
    repeat split; auto.
  
    revert mb a b A B E.
    induction n; intros.
    -
      inversion kc.
    -
      simpl in *.
      repeat break_match_hyp; try some_none; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        clear IHn.
        subst k.
        unfold mem_lookup_err, trywith in *.
        repeat break_match; try inl_inr.
        repeat some_inv; repeat inl_inr_inv; subst.
        eq_to_equiv_hyp.
        err_eq_to_equiv_hyp.
        rewrite A in *; clear A c.
        rewrite B in *; clear B c0.
        exists c1.

        assert (mem_lookup n ma = Some c1).
        {
          eapply evalDSHBinOp_preservation.
          eassumption.
          Unshelve.
          reflexivity.
        }

        rewrite Heqs1, H.
        auto.
      +
        apply IHn with (mb:=mem_add n c1 mb); auto.
        lia.
  Qed.

  (* TODO: generalize this (look like Proper) *)
  Lemma is_OK_evalDSHIMap_mem_equiv
        (n: nat)
        (df : AExpr)
        (σ : evalContext)
        (mem : memory)
        (mx ma mb : mem_block) :
    ma = mb ->
    is_OK (evalDSHIMap mem n df σ mx ma) <->
    is_OK (evalDSHIMap mem n df σ mx mb).
  Proof.
    intros.
    pose proof evalDSHIMap_proper mem n df σ mx mx.
    unfold Proper, respectful in H0.
    assert (T : mx = mx) by reflexivity;
      specialize (H0 T ma mb H); clear T.
    unfold is_Some.
    repeat break_match; try reflexivity; inversion H0.
    split; constructor.
    split; intros C; inversion C.
  Qed.
  
  (* TODO: generalize this (look like Proper) *)
  Lemma is_OK_evalDSHBinOp_mem_equiv
        (n off : nat)
        (df : AExpr)
        (σ : evalContext)
        (mem : memory)
        (mx ma mb : mem_block) :
    ma = mb ->
    is_OK (evalDSHBinOp mem n off df σ mx ma) <->
    is_OK (evalDSHBinOp mem n off df σ mx mb).
  Proof.
    intros.
    pose proof evalDSHBinOp_proper mem n off df σ mx mx.
    unfold Proper, respectful in H0.
    assert (T : mx = mx) by reflexivity;
      specialize (H0 T ma mb H); clear T.
    unfold is_Some.
    repeat break_match; try reflexivity; inversion H0.
    split; constructor.
    split; intros C; inversion C.
  Qed.

  Lemma is_OK_evalDSHIMap_mem_add
        (n : nat)
        (df : AExpr)
        (mem : memory)
        (σ : evalContext)
        (mx mb : mem_block)
        (k : NM.key)
        (v : CarrierA) :
    is_OK (evalDSHIMap mem n df σ mx (mem_add k v mb)) <->
    is_OK (evalDSHIMap mem n df σ mx mb).
  Proof.
    dependent induction n; [split; constructor |].
    cbn.
    repeat break_match; try reflexivity.
    destruct (Nat.eq_dec n k).
    -
      subst.
      apply is_OK_evalDSHIMap_mem_equiv.
      apply mem_add_overwrite.
    -
      rewrite is_OK_evalDSHIMap_mem_equiv
        with (ma := mem_add n c0 (mem_add k v mb)).
      apply IHn.
      apply mem_add_comm.
      assumption.
  Qed.

  Lemma is_OK_evalDSHBinOp_mem_add
        (n off : nat)
        (df : AExpr)
        (mem : memory)
        (σ : evalContext)
        (mx mb : mem_block)
        (k : NM.key)
        (v : CarrierA) :
    is_OK (evalDSHBinOp mem n off df σ mx (mem_add k v mb)) <->
    is_OK (evalDSHBinOp mem n off df σ mx mb).
  Proof.
    dependent induction n; [split; constructor |].
    cbn.
    repeat break_match; try reflexivity.
    destruct (Nat.eq_dec n k).
    -
      subst.
      apply is_OK_evalDSHBinOp_mem_equiv.
      apply mem_add_overwrite.
    -
      rewrite is_OK_evalDSHBinOp_mem_equiv
        with (ma := mem_add n c1 (mem_add k v mb))
             (mb := mem_add k v (mem_add n c1 mb)).
      apply IHn.
      apply mem_add_comm.
      assumption.
  Qed.

  Lemma evalIUnCarrierA_value_independent
        (mem : memory)
        (σ : evalContext)
        (df : AExpr)
        (n : nat) :
    (exists a, is_OK (evalIUnCType mem σ df n a)) ->
    forall b, is_OK (evalIUnCType mem σ df n b).
  Proof.
    intros.
    destruct H as [a H].
    induction df; cbn in *.

    (* base case 1 *)
    {
      destruct v.
      constructor.
      apply H.
    }

    (* base case 2 *)
    trivial.

    (* base case 3 *)
    {
      repeat break_match; try some_none; try inl_inr; exfalso.
      -
        apply err_equiv_eq in Heqs.
        contradict Heqs.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs0.
        clear - Heqs0; rename Heqs0 into H.
        destruct m; cbn in *.
        +
          destruct p.
          destruct v; [| destruct v].
          inversion H.
          inversion H.
          apply H.
        +
          trivial.
      -
        apply err_equiv_eq in Heqs.
        contradict Heqs.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs0.
        clear - Heqs0; rename Heqs0 into H.
        destruct m; cbn in *.
        +
          destruct p.
          destruct v; [| destruct v].
          inversion H.
          inversion H.
          apply H.
        +
          trivial.
      -
        apply err_equiv_eq in Heqs0.
        contradict Heqs0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs2.
        clear - Heqs2; rename Heqs2 into H,
                                 n0 into e.
        induction e; cbn in *.
        (* base 1 *)
        destruct v; [| destruct v].
        inversion H.
        inversion H.
        apply H.
        (* base 2 *)
        trivial.
        (* inductive *)
        all: repeat break_match; try reflexivity; try some_none; try inl_inr.
        all: try apply IHe; try apply IHe1; try apply IHe2.
        all: constructor.
      -
        apply err_equiv_eq in Heqs0.
        contradict Heqs0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs2.
        clear - Heqs2; rename Heqs2 into H,
                                 n0 into e.
        induction e; cbn in *.
        (* base 1 *)
        destruct v; [| destruct v].
        inversion H.
        inversion H.
        apply H.
        (* base 2 *)
        trivial.
        (* inductive *)
        all: repeat break_match; try reflexivity; try some_none; try inl_inr.
        all: try apply IHe; try apply IHe1; try apply IHe2.
        all: constructor.
    }

    (* inductive cases *)
    all: unfold evalIUnCType in *.
    all: repeat break_match; try reflexivity; try some_none; try inl_inr.
    all: try apply IHdf; try apply IHdf1; try apply IHdf2.
    all: constructor.
  Qed.

  Lemma evalIBinCarrierA_value_independent
        (mem : memory)
        (σ : evalContext)
        (df : AExpr)
        (n : nat) :
    (exists a b, is_OK (evalIBinCType mem σ df n a b)) ->
    forall c d, is_OK (evalIBinCType mem σ df n c d).
  Proof.
    intros.
    destruct H as [a [b H]].
    induction df; cbn in *.
    
    (* base case 1 *)
    {
      destruct v.
      constructor.
      destruct v.
      constructor.
      apply H.
    }
    
    (* base case 2 *)
    trivial.
    
    (* base case 3 *)
    {
      repeat break_match; try some_none; try inl_inr; exfalso.
      -
        apply err_equiv_eq in Heqs.
        contradict Heqs.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs0.
        clear - Heqs0; rename Heqs0 into H.
        destruct m; cbn in *.
        +
          destruct p.
          destruct v; [| destruct v].
          inversion H.
          inversion H.
          apply H.
        +
          trivial.
      -
        apply err_equiv_eq in Heqs.
        contradict Heqs.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs0.
        clear - Heqs0; rename Heqs0 into H.
        destruct m; cbn in *.
        +
          destruct p.
          destruct v; [| destruct v].
          inversion H.
          inversion H.
          apply H.
        +
          trivial.
      -
        apply err_equiv_eq in Heqs0.
        contradict Heqs0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs2.
        clear - Heqs2; rename Heqs2 into H,
                       n0 into e.
        induction e; cbn in *.
        (* base 1 *)
        destruct v; [| destruct v].
        inversion H.
        inversion H.
        apply H.
        (* base 2 *)
        trivial.
        (* inductive *)
        all: repeat break_match; try reflexivity; try some_none; try inl_inr.
        all: try apply IHe; try apply IHe1; try apply IHe2.
        all: constructor.
      -
        apply err_equiv_eq in Heqs0.
        contradict Heqs0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqs2.
        clear - Heqs2; rename Heqs2 into H,
                       n0 into e.
        induction e; cbn in *.
        (* base 1 *)
        destruct v; [| destruct v].
        inversion H.
        inversion H.
        apply H.
        (* base 2 *)
        trivial.
        (* inductive *)
        all: repeat break_match; try reflexivity; try some_none; try inl_inr.
        all: try apply IHe; try apply IHe1; try apply IHe2.
        all: constructor.
    }
    
    (* inductive cases *)
    all: unfold evalIBinCType in *.
    all: repeat break_match; try reflexivity; try some_none; try inl_inr.
    all: try apply IHdf; try apply IHdf1; try apply IHdf2.
    all: constructor.
  Qed.

  Lemma evalDSHIMap_is_OK_inv
        {mem : memory}
        {n: nat}
        {df : AExpr}
        {σ : evalContext}
        {mx mb: mem_block}:
    (∀ k (kc: k < n),
        ∃ a, (mem_lookup k mx = Some a /\
              is_OK (evalIUnCType mem σ df k a)))
    -> (is_OK (evalDSHIMap mem n df σ mx mb)).
  Proof.
    intros H.
    induction n; [constructor |].
    simpl.
    repeat break_match.
    1-2: exfalso.
    -
      assert (T : n < S n) by omega.
      specialize (H n T).
      destruct H as [a [L1 S]].
      unfold mem_lookup_err, trywith in Heqs.
      break_match; try inversion Heqs; try some_none.
    -
      err_eq_to_equiv_hyp.
      contradict Heqs0.
      assert (T : n < S n) by omega.
      specialize (H n T).
      apply is_OK_neq_inl.
      apply evalIUnCarrierA_value_independent.
      destruct H as [a H].
      exists a.
      apply H.
    -
      rewrite is_OK_evalDSHIMap_mem_add.
      apply IHn.
      intros.
      apply H.
      lia.
  Qed.

  Lemma evalDSHBinOp_is_OK_inv
        {mem : memory}
        {off n: nat}
        {df : AExpr}
        {σ : evalContext}
        {mx mb: mem_block}:
    (∀ k (kc: k < n),
        ∃ a b,
          (mem_lookup k mx = Some a /\
           mem_lookup (k+off) mx = Some b /\
           is_OK (evalIBinCType mem σ df k a b)
          )
    ) -> (is_OK (evalDSHBinOp mem n off df σ mx mb)).
  Proof.
    intros H.
    induction n; [constructor |].
    simpl.
    repeat break_match.
    1-3: exfalso.
    -
      assert (T : n < S n) by omega.
      specialize (H n T).
      destruct H as [a [b [L1 [L2 S]]]].
      unfold mem_lookup_err, trywith in Heqs.
      break_match; try inversion Heqs; try some_none.
    -
      assert (T : n < S n) by omega.
      specialize (H n T).
      destruct H as [a [b [L1 [L2 S]]]].
      unfold mem_lookup_err, trywith in Heqs0.
      break_match; try inversion Heqs0; try some_none.
    -
      err_eq_to_equiv_hyp.
      contradict Heqs1.
      assert (T : n < S n) by omega.
      specialize (H n T).
      apply is_OK_neq_inl.
      apply evalIBinCarrierA_value_independent.
      destruct H as [a [b H]].
      exists a, b.
      apply H.
    -
      rewrite is_OK_evalDSHBinOp_mem_add.
      apply IHn.
      intros.
      apply H.
      lia.
  Qed.

  Lemma evalDSHIMap_is_Err
        (mem : memory)
        (n: nat)
        (nz: n≢0)
        (df : AExpr)
        (σ : evalContext)
        (mx mb : mem_block):
    (exists k (kc:k<n), is_None (mem_lookup k mx))
    ->
    is_Err (evalDSHIMap mem n df σ mx mb).
  Proof.
    revert mb.
    induction n; intros mb DX.
    +
      lia.
    +
      destruct DX as [k [kc DX]].
      destruct (Nat.eq_dec k n).
      *
        clear IHn.
        subst k.
        simpl.
        repeat break_match; try constructor.
        unfold is_None in DX.
        break_match; inversion DX.
        unfold mem_lookup_err in Heqs, Heqs0.
        try rewrite Heqo in Heqs; try rewrite Heqo in Heqs0.
        cbn in *; inl_inr.
      *
        simpl.
        repeat break_match; try constructor.
        apply IHn.
        lia.
        exists k.
        assert(k < n) as kc1 by lia.
        exists kc1.
        apply DX.
  Qed.

  Lemma evalDSHBinOp_is_Err
        (mem : memory)
        (off n: nat)
        (nz: n≢0)
        (df : AExpr)
        (σ : evalContext)
        (mx mb : mem_block):
    (exists k (kc:k<n),
        is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx))
    ->
    is_Err (evalDSHBinOp mem n off df σ mx mb).
  Proof.
    revert mb.
    induction n; intros mb DX.
    +
      lia.
    +
      destruct DX as [k [kc DX]].
      destruct (Nat.eq_dec k n).
      *
        clear IHn.
        subst k.
        simpl.
        repeat break_match; try constructor.
        destruct DX.
        all: unfold is_None in H.
        all: break_match; inversion H.
        all: unfold mem_lookup_err in Heqs, Heqs0.
        all: try rewrite Heqo in Heqs; try rewrite Heqo in Heqs0.
        all: cbn in *; inl_inr.
      *
        simpl.
        repeat break_match; try constructor.
        apply IHn.
        lia.
        exists k.
        assert(k < n) as kc1 by lia.
        exists kc1.
        apply DX.
  Qed.
  
End BinCarrierA.

(* Simple wrapper. *)
Definition memory_alloc_empty m i :=
  memory_set m i (mem_empty).

Lemma blocks_equiv_at_Pexp_incrVar
      (p : PExpr)
      (σ0 σ1 : evalContext)
      (m0 m1: memory)
      {foo0 foo1: DSHVal}
  : blocks_equiv_at_Pexp σ0 σ1 p m0 m1 <->
    blocks_equiv_at_Pexp (foo0::σ0) (foo1::σ1) (incrPVar 0 p) m0 m1.
Proof.
  split.
  -
    intros H.
    unfold blocks_equiv_at_Pexp.
    rewrite 2!evalPexp_incrPVar.
    apply H.
  -
    intros H.
    unfold blocks_equiv_at_Pexp in *.
    setoid_rewrite evalPexp_incrPVar in H.
    apply H; exact (DSHnatVal 0).
Qed.

Lemma blocks_equiv_at_Pexp_remove
      (y_p : PExpr)
      (σ0 σ1 : evalContext)
      (t0_i t1_i : mem_block_id)
      (m0'' m1'' : memory)
      (NY0: evalPexp σ0 y_p ≢ inr t0_i)
      (NY1: evalPexp σ1 y_p ≢ inr t1_i):
  blocks_equiv_at_Pexp σ0 σ1 y_p m0'' m1''
  → blocks_equiv_at_Pexp σ0 σ1 y_p (memory_remove m0'' t0_i) (memory_remove m1'' t1_i).
Proof.
  intros EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 y_p), (evalPexp σ1 y_p); try (inversion EE; fail).
  constructor.
  inversion_clear EE.
  rewrite inr_neq in NY0.
  rewrite inr_neq in NY1.
  unfold memory_lookup, memory_remove in *.
  rewrite 2!NP.F.remove_neq_o; auto.
Qed.

Lemma blocks_equiv_at_Pexp_add_mem
      (p : PExpr)
      (σ0 σ1 : evalContext)
      (m0 m1 : memory)
      (t0 t1 : mem_block_id)
      (foo0 foo1: mem_block)
  :
    evalPexp σ0 p ≢ inr t0 ->
    evalPexp σ1 p ≢ inr t1 ->
    blocks_equiv_at_Pexp σ0 σ1 p m0 m1 ->
    blocks_equiv_at_Pexp σ0 σ1 p
                         (memory_set m0 t0 foo0)
                         (memory_set m1 t1 foo1).
Proof.
  intros E0 E1 EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 p), (evalPexp σ1 p); try (inversion EE; fail).
  constructor.
  inversion_clear EE.
  inversion H. clear H.
  symmetry in H0, H1.
  rewrite inr_neq in E0.
  rewrite inr_neq in E1.
  unfold memory_lookup, memory_set in *.
  rewrite 2!NP.F.add_neq_o; auto.
  rewrite H0, H1.
  constructor.
  apply H2.
Qed.

(* Also could be proven in other direction *)
Lemma SHCOL_DSHCOL_mem_block_equiv_mem_empty {a b: mem_block}:
  SHCOL_DSHCOL_mem_block_equiv mem_empty a b -> a = b.
Proof.
  intros H.
  unfold SHCOL_DSHCOL_mem_block_equiv in H.
  intros k.
  specialize (H k).
  unfold mem_lookup, mem_empty in H.
  rewrite NP.F.empty_o in H.
  inversion H.
  -
    rewrite <- H1.
    apply is_None_def in H0.
    rewrite H0.
    reflexivity.
  -
    assumption.
Qed.

Lemma SHCOL_DSHCOL_mem_block_equiv_comp (m0 m1 m2 d01 d12 : mem_block) :
  SHCOL_DSHCOL_mem_block_equiv m0 m1 d01 →
  SHCOL_DSHCOL_mem_block_equiv m1 m2 d12 →
  SHCOL_DSHCOL_mem_block_equiv m0 m2 (MMemoryOfCarrierA.mem_union d12 d01).
Proof.
  intros D01' D12'.
  unfold SHCOL_DSHCOL_mem_block_equiv in *.
  intro k.
  specialize (D01' k); specialize (D12' k).
  unfold mem_lookup, MMemoryOfCarrierA.mem_union in *.
  rewrite NP.F.map2_1bis by reflexivity.
  inversion_clear D01' as [D01 E01| D01 E01];
  inversion_clear D12' as [D12 E12| D12 E12].
  all: try apply is_None_def in D01.
  all: try apply is_None_def in D12.
  all: try apply is_Some_def in D01.
  all: try apply is_Some_def in D12.
  -
    constructor 1.
    rewrite D01, D12; reflexivity.
    rewrite E01, E12; reflexivity.
  -
    destruct D12 as [x D12].
    constructor 2.
    rewrite D01, D12; reflexivity.
    rewrite E12, D12; reflexivity.
  -
    destruct D01 as [x D01].
    constructor 2.
    rewrite D12, D01; reflexivity.
    rewrite D12, <-E01, E12; reflexivity.
  -
    destruct D01 as [x1 D01].
    destruct D12 as [x2 D12].
    constructor 2.
    rewrite D12; reflexivity.
    rewrite D12, E12, D12; reflexivity.
Qed.

Definition compose2 {A B C D : Type} (g : C -> D) (f : A -> B -> C) : A -> B -> D :=
  fun a b => g (f a b).

Fact eq_equiv_option_CarrierA (a1 a2 : option CarrierA) :
  a1 = a2 <-> a1 ≡ a2.
Proof.
  split; intros.
  -
    unfold equiv, option_Equiv in H.
    inversion H; [reflexivity |].
    f_equal.
    rewrite H0.
    reflexivity.
  -
    rewrite H.
    reflexivity.
Qed.

Lemma memory_lookup_err_inl_None
      (msg msg' : string)
      (mem : memory)
      (n : mem_block_id)
  :
    memory_lookup_err msg mem n = inl msg' <->
    memory_lookup mem n = None.
Proof.
  unfold memory_lookup_err, trywith.
  split; intros.
  all: break_match.
  all: inversion H.
  all: constructor.
Qed.

Lemma memory_lookup_err_inr_Some
      (msg : string)
      (mem : memory)
      (n : mem_block_id)
      (mb : mem_block)
  :
    memory_lookup_err msg mem n = inr mb <->
    memory_lookup mem n = Some mb.
Proof.
  unfold memory_lookup_err, trywith.
  split; intros.
  all: break_match.
  all: inversion H.
  all: rewrite H2.
  all: reflexivity.
Qed.


(** * MSHEmbed, MSHPick **)

Global Instance Assign_DSH_pure
       {x_n y_n : NExpr}
       {x_p y_p : PExpr}
  :
    DSH_pure (DSHAssign (x_p, x_n) (y_p, y_n)) y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; repeat some_inv; try inl_inr.
    inl_inr_inv; rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqs2.
      assumption.
  -
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    unfold equiv, memory_Equiv, memory_set, mem_add in H.
    specialize (H k).
    rewrite <-H.
    destruct (Nat.eq_dec m1 k), (Nat.eq_dec n0 k);
        try (rewrite NP.F.add_eq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_eq_o with (x := n0) by assumption);
        try (rewrite NP.F.add_neq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_neq_o with (x := n0) by assumption).
    all: subst.
    all: try congruence.
    all: reflexivity.
Qed.

Global Instance Embed_MSH_DSH_compat
       {o b: nat}
       {bc: b < o}
       {σ: evalContext}
       {y_n : NExpr}
       {x_p y_p : PExpr}
       {m : memory}
       (Y: evalNexp σ y_n = inr b)
       (BP : DSH_pure (DSHAssign (x_p, NConst 0) (y_p, y_n)) y_p)
  :
    @MSH_DSH_compat _ _ (MSHEmbed bc) (DSHAssign (x_p, NConst 0) (y_p, y_n)) σ m x_p y_p BP.
Proof.
  constructor; intros mx mb MX MB.
  destruct mem_op as [md |] eqn:MD, evalDSHOperator as [fma |] eqn:FMA; try constructor.
  2: exfalso.
  all: unfold lookup_Pexp in MX, MB.
  all: cbn in *.
  all: destruct evalPexp eqn:XP in MX; try some_none; try inl_inr; rewrite XP in *.
  all: destruct evalPexp eqn:YP in MB; try some_none; try inl_inr; rewrite YP in *.
  all: unfold Embed_mem,
              map_mem_block_elt,
              MMemoryOfCarrierA.mem_lookup,
              MMemoryOfCarrierA.mem_add,
              MMemoryOfCarrierA.mem_empty
         in MD.
  all: unfold memory_lookup_err, trywith in *.
  all: repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: try (inversion MX; fail).
  all: try (inversion MB; fail).
  all: subst.
  -
    exfalso.
    unfold mem_lookup_err, trywith in *.
    break_match; try inl_inr.
    enough (None = Some c) by some_none.
    rewrite <-Heqo2, <-Heqo3.
    unfold mem_lookup.
    inversion MX.
    apply H1.
  -
    repeat constructor.
    inversion Y; subst; clear Y.
    unfold SHCOL_DSHCOL_mem_block_equiv,
      memory_lookup, memory_set, mem_add, mem_lookup.
    rewrite NP.F.add_eq_o by reflexivity.
    constructor.
    intros.
    destruct (Nat.eq_dec b i);
      [ repeat rewrite NP.F.add_eq_o by assumption
      | repeat rewrite NP.F.add_neq_o by assumption ].
    +
      constructor 2; [reflexivity |].
      unfold mem_lookup_err, trywith in Heqs2.
      break_match_hyp; try inl_inr; inl_inr_inv; subst.
      rewrite <-Heqo2, <-Heqo3.
      unfold mem_lookup.
      inversion MX.
      apply H1.
    +
      constructor 1; [reflexivity |].
      symmetry.
      inversion MB.
      apply H1.
  -
    constructor.
  -
    exfalso.
    unfold mem_lookup_err, trywith in Heqs2.
    break_match; try inl_inr.
    enough (Some c0 = None) by some_none.
    rewrite <-Heqo2, <-Heqo3.
    unfold mem_lookup.
    inversion MX.
    apply H1.
Qed.

Global Instance Pick_MSH_DSH_compat
       {i b: nat}
       {bc: b < i}
       {σ: evalContext}
       {x_n : NExpr}
       {x_p y_p : PExpr}
       {m : memory}
       (X: evalNexp σ x_n = inr b)
       (BP : DSH_pure (DSHAssign (x_p, x_n) (y_p, NConst 0)) y_p)
  :
    @MSH_DSH_compat _ _ (MSHPick bc) (DSHAssign (x_p, x_n) (y_p, NConst 0)) σ m x_p y_p BP.
Proof.
  constructor; intros mx mb MX MB.
  destruct mem_op as [md |] eqn:MD, evalDSHOperator as [fma |] eqn:FMA; try constructor.
  2: exfalso.
  all: unfold lookup_Pexp in MX, MB.
  all: cbn in *.
  all: destruct evalPexp eqn:XP in MX; try some_none; try inl_inr; rewrite XP in *.
  all: destruct evalPexp eqn:YP in MB; try some_none; try inl_inr; rewrite YP in *.
  all: unfold Pick_mem,
              map_mem_block_elt,
              MMemoryOfCarrierA.mem_lookup,
              MMemoryOfCarrierA.mem_add,
              MMemoryOfCarrierA.mem_empty
         in MD.
  all: unfold memory_lookup_err, trywith in *.
  all: repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: try (inversion MX; fail).
  all: try (inversion MB; fail).
  all: subst.
  all: repeat constructor.
  1,3: exfalso.
  -
    enough (None = Some c) by some_none.
    unfold mem_lookup_err, trywith in Heqs2.
    break_match; try inl_inr.
    rewrite <-Heqo1, <-Heqo2.
    unfold mem_lookup.
    rewrite X.
    inversion MX.
    apply H1.
  -
    unfold mem_lookup_err, trywith in Heqs2.
    break_match; try inl_inr.
    enough (Some c0 = None) by some_none.
    rewrite <-Heqo1, <-Heqo2.
    unfold mem_lookup.
    rewrite X.
    inversion MX.
    apply H1.
  -
    unfold SHCOL_DSHCOL_mem_block_equiv,
      memory_lookup, memory_set, mem_add, mem_lookup.
    rewrite NP.F.add_eq_o by reflexivity.
    constructor.
    intros.
    destruct (Nat.eq_dec 0 i0);
      [ repeat rewrite NP.F.add_eq_o by assumption
      | repeat rewrite NP.F.add_neq_o by assumption ].
    +
      constructor 2; [reflexivity |].
      unfold mem_lookup_err, trywith in Heqs2.
      break_match; try inl_inr.
      inversion Heqs2; subst.
      rewrite <-Heqo2, <-Heqo1.
      inversion MX.
      rewrite X.
      apply H1.
    +
      constructor 1; [reflexivity |].
      symmetry.
      inversion MB.
      apply H1.
Qed.


(** * MSHPointwise  *)

Global Instance IMap_DSH_pure
       {nn : nat}
       {x_p y_p : PExpr}
       {a : AExpr}
  :
    DSH_pure (DSHIMap nn x_p y_p a) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; repeat some_inv; try inl_inr.
    inl_inr_inv; rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqs2.
      assumption.
  -
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    unfold equiv, memory_Equiv, memory_set, mem_add in H.
    specialize (H k).
    rewrite <-H.
    cbv in H0; subst.
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Global Instance Pointwise_MSH_DSH_compat
       {n: nat}
       {f: FinNat n -> CarrierA -> CarrierA}
       {pF: Proper ((=) ==> (=) ==> (=)) f}
       {df : AExpr}
       {x_p y_p : PExpr}
       {σ : evalContext}
       {m : memory}
       (FDF : MSH_DSH_IUnCarrierA_compat f σ df m)
       (P : DSH_pure (DSHIMap n x_p y_p df) y_p)
  :
    @MSH_DSH_compat _ _ (@MSHPointwise n f pF) (DSHIMap n x_p y_p df) σ m x_p y_p P.
Proof.
  split.
  intros mx mb MX MB.
  simpl.
  destruct (mem_op_of_hop (HPointwise f) mx) as [md|] eqn:MD.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match;
      try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv;
          subst.
    +
      clear - MX Heqs1.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MX in Heqs1.
      some_none.
    +
      clear - MB Heqs2.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MB in Heqs2.
      some_none.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqs1, <-Heqs2 in *.
      clear Heqs1 Heqs2 m2 m3.

      rename Heqs3 into E.

      apply equiv_Some_is_Some in MD.
      pose proof (mem_op_of_hop_x_density MD) as DX.
      clear MD pF.

      inversion_clear FDF as [FV].

      contradict E.
      apply is_OK_neq_inl.

      eapply evalDSHIMap_is_OK_inv.

      intros k kc.

      specialize (DX k kc).
      apply is_Some_equiv_def in DX.
      destruct DX as [a DX].
      exists a.
      repeat split; eauto.

      specialize (FV (FinNat.mkFinNat kc) a).
      cbn in FV.
      eapply inr_is_OK.
      eassumption.
    +
      constructor.
      unfold memory_lookup_err, trywith, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      constructor.
      repeat some_inv.

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqs1, <-Heqs2 in *.
      clear Heqs1 Heqs2 m2 m3.

      rename Heqs3 into ME.
      intros k.

      unfold mem_op_of_hop in MD.
      break_match_hyp; try some_none.
      some_inv.
      rewrite <- MD.
      clear MD md.
      rename t into vx.

      unfold avector_to_mem_block.
      avector_to_mem_block_to_spec md HD OD.
      destruct (NatUtil.lt_ge_dec k n) as [kc | kc].
      *
        (* k<n, which is normal *)
        clear OD.
        simpl in *.
        unfold MMemoryOfCarrierA.mem_lookup in HD.
        unfold mem_lookup.
        rewrite HD with (ip:=kc).
        clear HD md.
        apply MemExpected.
        --
          unfold is_Some.
          tauto.
        --
          inversion_clear FDF as [FV].

          rewrite HPointwise_nth with (jc:=kc).

          pose proof (evalDSHIMap_mem_lookup_mx ME k kc) as A.

          apply is_Some_equiv_def in A. destruct A as [a A].

          specialize FV with (nc:=mkFinNat kc) (a:=a).
          cbn in FV.

          pose proof (evalDSHIMap_nth m k kc A ME) as T.
          inversion T; [rewrite <-H in FV; inl_inr | clear T].
          unfold mem_lookup in H.
          rewrite <-H.
          rewrite <-H0 in FV.
          inversion FV.
          subst.

          pose proof (mem_block_to_avector_nth Heqo (kc:=kc)) as MVA.
          rewrite MVA in *.
          repeat some_inv.
          rewrite A.
          rewrite <-H4.
          rewrite H1.
          reflexivity.
      *
        (* k >= 0 *)
        simpl in *.
        clear HD.
        rewrite OD by assumption.
        apply MemPreserved.
        --
          unfold is_None.
          tauto.
        --
          specialize (OD k kc).
          apply (evalDSHIMap_oob_preservation m ME), kc.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match;
      try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
    all: try constructor.
    exfalso.


    eq_to_equiv_hyp; err_eq_to_equiv_hyp.
    rewrite memory_lookup_err_inr_Some in *.
    rewrite MB, MX in *.
    repeat some_inv.
    rewrite <-Heqs1, <-Heqs2 in *.
    clear Heqs1 Heqs2 m2 m3.

    apply Some_nequiv_None in MX.
    contradict MX.

    unfold mem_op_of_hop in MD.
    break_match_hyp; try some_none.
    clear MD.
    rename Heqo into MX.
    unfold mem_block_to_avector in MX.
    apply vsequence_Vbuild_eq_None in MX.
    apply is_None_equiv_def; [typeclasses eauto |].
    destruct n.
    *
      destruct MX as [k [kc MX]].
      inversion kc.
    *
      contradict Heqs3.
      enough (T : is_Err (evalDSHIMap m (S n) df σ mx mb))
        by (destruct (evalDSHIMap m (S n) df σ mx mb);
            [intros C; inl_inr | inversion T ]).
      apply evalDSHIMap_is_Err; try typeclasses eauto.
      lia.
      destruct MX as [k MX].
      destruct (NatUtil.lt_ge_dec k (S n)) as [kc1 | kc2].
      --
        exists k.
        exists kc1.
        destruct MX as [kc MX].
        apply is_None_def in MX.
        eapply MX.
      --
        destruct MX as [kc MX].
        lia.
Qed.

(** * MSHBinOp  *)

Global Instance BinOp_DSH_pure
       {o : nat}
       {x_p y_p : PExpr}
       {a: AExpr}
  :
    DSH_pure (DSHBinOp o x_p y_p a) y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqs2.
      assumption.
  -
    intros σ m m' fuel E y_i P.
    destruct fuel; cbn in E; [some_none |].

    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    err_eq_to_equiv_hyp.
    rewrite P in Heqs0, Heqs2, E.
    clear P m1.
    rename m0 into x_i, m2 into x, m3 into y, m4 into y'.

    intros k NKY.
    rewrite <- E.
    clear E m'.
    unfold memory_lookup, memory_set in *.
    rewrite NP.F.add_neq_o by auto.
    reflexivity.    
Qed.

Global Instance BinOp_MSH_DSH_compat
       {o: nat}
       {f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA}
       {pF: Proper ((=) ==> (=) ==> (=) ==> (=)) f}
       {x_p y_p : PExpr}
       {df : AExpr}
       {σ: evalContext}
       (m: memory)
       (FDF : MSH_DSH_IBinCarrierA_compat f σ df m)
       (BP: DSH_pure (DSHBinOp o x_p y_p df) y_p)
  :
    @MSH_DSH_compat _ _ (MSHBinOp f) (DSHBinOp o x_p y_p df) σ m x_p y_p BP.
Proof.
  split.
  intros mx mb MX MB.
  simpl.
  destruct (mem_op_of_hop (HCOL.HBinOp f) mx) as [md|] eqn:MD.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv;
      subst.
    1-3: exfalso.
    +
      clear - MX Heqs1.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MX in Heqs1.
      some_none.
    +
      clear - MB Heqs2.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MB in Heqs2.
      some_none.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqs1, <-Heqs2 in *.
      clear Heqs1 Heqs2 m2 m3.

      rename Heqs3 into E.

      apply equiv_Some_is_Some in MD.
      pose proof (mem_op_of_hop_x_density MD) as DX.
      clear MD pF.

      inversion_clear FDF as [FV].

      contradict E.
      apply is_OK_neq_inl.

      eapply evalDSHBinOp_is_OK_inv.

      intros k kc.

      assert(DX1:=DX).
      assert(kc1: k < o + o) by lia.
      specialize (DX k kc1).
      apply is_Some_equiv_def in DX.
      destruct DX as [a DX].

      assert(kc2: k + o < o + o) by lia.
      specialize (DX1 (k+o) kc2).
      apply is_Some_equiv_def in DX1.
      destruct DX1 as [b DX1].
      exists a.
      exists b.
      repeat split; eauto.

      specialize (FV (FinNat.mkFinNat kc) a b).
      cbn in FV.
      eapply inr_is_OK.
      eassumption.
    +
      constructor.
      unfold memory_lookup_err, trywith, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      constructor.
      repeat some_inv.

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqs1, <-Heqs2 in *.
      clear Heqs1 Heqs2 m2 m3.

      rename Heqs3 into ME.
      intros k.

      unfold mem_op_of_hop in MD.
      break_match_hyp; try some_none.
      some_inv.
      rewrite <- MD.
      clear MD md.
      rename t into vx.

      unfold avector_to_mem_block.

      avector_to_mem_block_to_spec md HD OD.
      destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
      *
        (* k<o, which is normal *)
        clear OD.
        simpl in *.
        unfold MMemoryOfCarrierA.mem_lookup in HD.
        unfold mem_lookup.
        rewrite HD with (ip:=kc).
        clear HD md.
        apply MemExpected.
        --
          unfold is_Some.
          tauto.
        --
          inversion_clear FDF as [FV].

          assert (k < o + o)%nat as kc1 by omega.
          assert (k + o < o + o)%nat as kc2 by omega.
          rewrite HBinOp_nth with (jc1:=kc1) (jc2:=kc2).

          pose proof (evalDSHBinOp_mem_lookup_mx ME k kc) as [A B].

          apply is_Some_equiv_def in A. destruct A as [a A].
          apply is_Some_equiv_def in B. destruct B as [b B].


          specialize FV with (nc:=mkFinNat kc) (a:=a) (b:=b).
          cbn in FV.

          pose proof (evalDSHBinOp_nth m k kc A B ME) as T.
          inversion T; [rewrite <-H in FV; inl_inr | clear T].
          unfold mem_lookup in H.
          rewrite <-H.
          rewrite <-H0 in FV.
          inversion FV.
          subst.
          
          pose proof (mem_block_to_avector_nth Heqo0 (kc:=kc1)) as MVA.
          pose proof (mem_block_to_avector_nth Heqo0 (kc:=kc2)) as MVB.
          rewrite MVA, MVB in *.
          repeat some_inv.
          rewrite A, B.
          rewrite <-H4.
          rewrite H1.
          reflexivity.
      *
        (* k >= 0 *)
        simpl in *.
        clear HD.
        rewrite OD by assumption.
        apply MemPreserved.
        --
          unfold is_None.
          tauto.
        --
          specialize (OD k kc).
          apply (evalDSHBinOp_oob_preservation m ME), kc.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    all: try constructor.
    exfalso.


    eq_to_equiv_hyp; err_eq_to_equiv_hyp.
    rewrite memory_lookup_err_inr_Some in *.
    rewrite MB, MX in *.
    repeat some_inv.
    rewrite <-Heqs1, <-Heqs2 in *.
    clear Heqs1 Heqs2 m2 m3.

    apply Some_nequiv_None in MX.
    contradict MX.

    unfold mem_op_of_hop in MD.
    break_match_hyp; try some_none.
    clear MD.
    rename Heqo0 into MX.
    unfold mem_block_to_avector in MX.
    apply vsequence_Vbuild_eq_None in MX.
    apply is_None_equiv_def; [typeclasses eauto |].
    destruct o.
    *
      destruct MX as [k [kc MX]].
      inversion kc.
    *
      contradict Heqs3.
      enough (T : is_Err (evalDSHBinOp m (S o) (S o) df σ mx mb))
        by (destruct (evalDSHBinOp m (S o) (S o) df σ mx mb);
            [intros C; inl_inr | inversion T ]).
      apply evalDSHBinOp_is_Err; try typeclasses eauto.
      lia.
      destruct MX as [k MX].
      destruct (NatUtil.lt_ge_dec k (S o)) as [kc1 | kc2].
      --
        exists k.
        exists kc1.
        left.
        destruct MX as [kc MX].
        apply is_None_def in MX.
        eapply MX.
      --
        exists (k-(S o)).
        destruct MX as [kc MX].
        assert(kc3: k - S o < S o) by lia.
        exists kc3.
        right.
        apply is_None_def in MX.
        replace (k - S o + S o) with k.
        apply MX.
        lia.
Qed.

(** * MSHInductor *)

Global Instance Power_DSH_pure
       {n : NExpr}
       {x_n y_n : NExpr}
       {x_p y_p : PExpr}
       {a : AExpr}
       {initial : CarrierA}
  :
    DSH_pure (DSHPower n (x_p, x_n) (y_p, y_n) a initial) y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqs2.
      assumption.
  -
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    unfold equiv, memory_Equiv, memory_set, mem_add in H.
    specialize (H k).
    rewrite <-H.
    destruct (Nat.eq_dec m1 k), (Nat.eq_dec n0 k);
        try (rewrite NP.F.add_eq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_eq_o with (x := n0) by assumption);
        try (rewrite NP.F.add_neq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_neq_o with (x := n0) by assumption).
    all: subst.
    all: try congruence.
    all: reflexivity.
Qed.

Global Instance evalDSHPower_Proper :
  Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalDSHPower.
Proof.
  unfold Proper, respectful.
  intros m m' M σ σ' Σ n n' N
         f f' F x x' X y y' Y
         xo xo' XO yo yo' YO.
  inversion_clear N; inversion_clear XO; inversion_clear YO.
  clear n xo yo.
  rename n' into n, xo' into xo, yo' into yo.
  generalize dependent y.
  generalize dependent y'.
  induction n; intros.
  -
    cbn.
    rewrite Y.
    reflexivity.
  -
    cbn.
    repeat break_match; try constructor.
    all: err_eq_to_equiv_hyp.

    (* memory lookups *)
    all: try rewrite X in Heqs.
    all: try rewrite Y in Heqs0.
    all: try rewrite Heqs in *.
    all: try rewrite Heqs0 in *.
    all: try inl_inr; repeat inl_inr_inv.
    all: rewrite Heqs2 in *.
    all: rewrite Heqs3 in *.

    (* AExp evaluation (evalBinCType *)
    all: rewrite M, Σ, F in Heqs1.
    all: rewrite Heqs1 in Heqs4.
    all: try inl_inr; repeat inl_inr_inv.

    eapply IHn.
    rewrite Y, Heqs4.
    reflexivity.
Qed.

Lemma memory_lookup_err_inr_Some_eq
      (msg : string)
      (m : memory)
      (k : mem_block_id)
      (mb : mem_block)
  :
    memory_lookup_err msg m k ≡ inr mb <->
    memory_lookup m k ≡ Some mb.
Proof.
  unfold memory_lookup_err, trywith.
  split; intros.
  break_match; try inl_inr.
  inversion H.
  reflexivity.
  rewrite H.
  reflexivity.
Qed.

Lemma memory_lookup_err_inl_None_eq
      (msg msg' : string)
      (m : memory)
      (k : mem_block_id)
  :
    memory_lookup_err msg m k ≡ inl msg' ->
    memory_lookup m k ≡ None.
Proof.
  unfold memory_lookup_err, trywith.
  intros.
  break_match; try inl_inr.
  reflexivity.
Qed.

Ltac memory_lookup_err_to_option :=
  repeat
    match goal with
    | [ H: memory_lookup_err _ _ _ = inr _ |- _] =>
      apply memory_lookup_err_inr_Some in H
    | [ H: memory_lookup_err _ _ _ = inl _ |- _] =>
      apply memory_lookup_err_inl_None in H
    | [ H: memory_lookup_err _ _ _ ≡ inr _ |- _] =>
      apply memory_lookup_err_inr_Some_eq in H
    | [ H: memory_lookup_err _ _ _ ≡ inl _ |- _] =>
      apply memory_lookup_err_inl_None_eq in H
    end.

Global Instance Inductor_MSH_DSH_compat
       {σ : evalContext}
       {n : nat}
       {nx : NExpr}
       {N : evalNexp σ nx = inr n}
       {m : memory}
       {f : CarrierA -> CarrierA -> CarrierA}
       {PF : Proper ((=) ==> (=) ==> (=)) f}
       {init : CarrierA}
       {a : AExpr}
       {x_p y_p : PExpr}
       (FA : MSH_DSH_BinCarrierA_compat f σ a m)
       (PD : DSH_pure (DSHPower nx (x_p, NConst 0) (y_p, NConst 0) a init) y_p)
  :
    @MSH_DSH_compat _ _
                    (MSHInductor n f init)
                    (DSHPower nx (x_p, NConst 0) (y_p, NConst 0) a init)
                    σ m x_p y_p PD.
Proof.
  constructor; intros x_m y_m X_M Y_M.
  assert (T : evalNexp σ nx ≡ inr n)
    by (inversion N; inversion H1; reflexivity);
    clear N; rename T into N.
  destruct mem_op as [mma |] eqn:MOP.
  all: destruct evalDSHOperator as [r |] eqn:DOP; [destruct r as [msg | dma] |].
  all: repeat constructor.
  2:{
    unfold lookup_Pexp; cbn.
    cbn in DOP.
    unfold NatAsNT.MNatAsNT.to_nat in *.
    destruct (evalPexp σ x_p) as [| x_id] eqn:X;
      [unfold lookup_Pexp in X_M; rewrite X in X_M; inversion X_M |].
    destruct (evalPexp σ y_p) as [| y_id] eqn:Y;
      [unfold lookup_Pexp in Y_M; rewrite Y in Y_M; inversion Y_M |].
    destruct (memory_lookup dma y_id) as [y_dma |] eqn:Y_DMA.
    unfold memory_lookup_err.
    +
      rewrite Y_DMA.
      constructor.
      unfold SHCOL_DSHCOL_mem_block_equiv.
      intro k.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      unfold memory_lookup_err, trywith in *.

      destruct (memory_lookup m x_id) eqn:X_M'; inversion X_M; subst;
        clear X_M; rename m0 into x_m', H1 into XME.
      destruct (memory_lookup m y_id) eqn:Y_M'; inversion Y_M; subst;
        clear Y_M; rename m0 into y_m', H1 into YME.

      (* simplify DOP down to evalDSHPower *)
      cbn in DOP; some_inv; rename H0 into DOP.
      rewrite N in DOP.
      repeat break_match; try inl_inr.
      inl_inr_inv.
      rename m0 into pm, Heqs into PM,
      H0 into DMA.
      rewrite <-DMA in *.
      unfold memory_lookup, memory_set in Y_DMA.
      rewrite NP.F.add_eq_o in Y_DMA by reflexivity.
      replace pm with y_dma in * by congruence; clear Y_DMA; rename PM into Y_DMA.

      (* make use of MOP *)
      destruct n as [|n'].
      {
        cbn in *.
        some_inv; inl_inr_inv.
        destruct (Nat.eq_dec 0 k).
        -
          subst.
          unfold mem_lookup, mem_add, MMemoryOfCarrierA.mem_add.
          repeat rewrite NP.F.add_eq_o by reflexivity.
          constructor 2; reflexivity.
        -
          unfold mem_lookup, mem_add, MMemoryOfCarrierA.mem_add.
          repeat rewrite NP.F.add_neq_o by assumption.
          constructor 1; [reflexivity |].
          rewrite YME.
          reflexivity.
      }
      cbn in MOP.
      remember (S n') as n; clear Heqn.
      unfold mem_op_of_hop in MOP.
      break_match; try some_none.
      some_inv.
      rename t into x_v, Heqo into X_V.

      destruct (Nat.eq_dec k 0) as [KO | KO].
      * (* the changed part of the block*)
        subst.
        cbn.
        constructor 2; [reflexivity |].
        destruct (mem_lookup 0 y_dma) as [ydma0 |] eqn:YDMA0.
        --
          clear N PD.
          err_eq_to_equiv_hyp.
          generalize dependent y_dma.
          generalize dependent init.
          induction n; intros.
          ++ (* induction base *)
            cbn in Y_DMA.
            inl_inr_inv.
            rewrite <-YDMA0.
            clear ydma0 YDMA0.
            rewrite <-Y_DMA; clear Y_DMA.
            unfold mem_lookup, mem_add.
            rewrite NP.F.add_eq_o by reflexivity.
            reflexivity.
          ++ (* inductive step *)

            (* simplify Y_DMA *)
            cbn in Y_DMA.
            unfold mem_lookup_err in Y_DMA.
            replace (mem_lookup 0 (mem_add 0 init y_m'))
              with (Some init)
              in Y_DMA
              by (unfold mem_lookup, mem_add;
                  rewrite NP.F.add_eq_o by reflexivity;
                  reflexivity).
            cbn in Y_DMA.
            destruct (mem_lookup 0 x_m') as [xm'0|] eqn:XM'0;
              cbn in Y_DMA; try inl_inr.
            inversion FA; clear FA;
              rename bin_equiv0 into FA; specialize (FA init xm'0 ).
            destruct (evalBinCType m σ a init xm'0 ) as [|df] eqn:DF;
              try inl_inr; inl_inr_inv.
            (* abstract: this gets Y_DMA to "the previous step" for induction *)
            rewrite mem_add_overwrite in Y_DMA.

            apply mem_block_to_avector_nth with (kc:=le_n 1) (k := 0) in X_V.
            rewrite Vnth_1_Vhead in X_V.
            assert (T : xm'0 = Vhead x_v).
            {
              enough (Some xm'0 = Some (Vhead x_v)) by (some_inv; assumption).
              rewrite <-X_V, <-XM'0, XME; reflexivity.
            }
            rewrite T in FA; clear T.

            (* applying induction hypothesis *)
            apply IHn in Y_DMA; [| assumption].

            rewrite Y_DMA, FA.

            unfold HCOLImpl.Inductor.
            rewrite nat_rect_succ_r.
            reflexivity.
        --
          clear - Y_DMA YDMA0.
          eq_to_equiv_hyp.
          err_eq_to_equiv_hyp.
          contradict YDMA0.
          generalize dependent init.
          induction n; cbn in *.
          ++
            intros.
            inversion Y_DMA; subst.
            rewrite <-H1.
            unfold mem_lookup, mem_add.
            rewrite NP.F.add_eq_o by reflexivity.
            intros C; inversion C.
          ++
            intros.
            repeat break_match; try inl_inr.
            eapply IHn.
            rewrite <-Y_DMA.
            f_equiv.
            rewrite mem_add_overwrite.
            reflexivity.
      * (* the preserved part of the block *)
        constructor 1;
          [cbn; break_match; try reflexivity;
           contradict KO; rewrite e; reflexivity |].
        inversion PD; clear PD mem_stable0; rename mem_write_safe0 into MWS.
        specialize (MWS σ m dma).

        clear - Y_DMA KO YME.
        err_eq_to_equiv_hyp.
        rewrite YME in Y_DMA.
        clear YME y_m'.

        assert(mem_lookup k y_m = mem_lookup k (mem_add 0 init y_m)) as P.
        {
          unfold mem_lookup, mem_add.
          rewrite NP.F.add_neq_o by auto.
          reflexivity.
        }
        revert Y_DMA P.
        generalize (mem_add 0 init y_m) as m0.
        induction n; intros.
        --
          cbn in *.
          inl_inr_inv.
          rewrite <- Y_DMA.
          apply P.
        --
          cbn in Y_DMA.
          repeat break_match_hyp; try inl_inr.
          eapply IHn.
          eauto.
          unfold mem_lookup, mem_add.
          rewrite NP.F.add_neq_o by auto.
          apply P.
    +
      exfalso.
      repeat break_match_hyp; try inl_inr; try some_inv; try some_none.
      repeat inl_inr_inv; subst.
      unfold memory_lookup, memory_set in Y_DMA.
      rewrite NP.F.add_eq_o in Y_DMA by reflexivity.
      some_none.
  }
  -
    exfalso.
    (*
       [mem_op] suceeds
       [evalDSHOperator] fails
     *)
    destruct (evalPexp σ x_p) as [| x_id] eqn:X;
      [unfold lookup_Pexp in X_M; rewrite X in X_M; inversion X_M |].
    destruct (evalPexp σ y_p) as [| y_id] eqn:Y;
      [unfold lookup_Pexp in Y_M; rewrite Y in Y_M; inversion Y_M |].

    cbn in X_M; rewrite X in X_M.
    cbn in Y_M; rewrite Y in Y_M.

    unfold memory_lookup_err, trywith in *.

    destruct (memory_lookup m x_id) eqn:X_M'; inversion X_M; subst;
      clear X_M; rename m0 into x_m', H1 into XME.
    destruct (memory_lookup m y_id) eqn:Y_M'; inversion Y_M; subst;
      clear Y_M; rename m0 into y_m', H1 into YME.

    destruct n.
    +
      cbn in DOP.
      unfold NatAsNT.MNatAsNT.to_nat in *.
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqs1.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqs2.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        unfold memory_lookup_err, trywith in *.
        rewrite X_M' in Heqs1.
        rewrite Y_M' in Heqs2.
        repeat inl_inr_inv.
        subst.
        cbn in Heqs4.
        inl_inr.
    +
      cbn in MOP.
      unfold mem_op_of_hop in MOP.
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.

      (* [x_m] is dense *)
      rename Heqo into XD.
      assert(0<1) as jc by lia.
      apply mem_block_to_avector_nth with (kc:=jc) in XD.

      cbn in DOP.
      unfold NatAsNT.MNatAsNT.to_nat in *.
      rewrite N in DOP.
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqs1.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqs2.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        unfold memory_lookup_err, trywith in *.
        rewrite X_M' in Heqs1.
        rewrite Y_M' in Heqs2.
        repeat inl_inr_inv.
        subst.

        rename Heqs3 into EV.
        clear -EV XD XME FA.
        apply eq_Some_is_Some in XD.
        err_eq_to_equiv_hyp.
        rewrite XME in EV.
        clear m2 XME t.
        revert x_m XD EV.
        remember (mem_add 0 init m3) as y_m.
        assert(is_Some (mem_lookup 0 y_m)) as YD.
        {
          subst y_m.
          unfold mem_lookup, mem_add.
          rewrite NP.F.add_eq_o.
          some_none.
          reflexivity.
        }
        clear Heqy_m m3.
        revert y_m YD.

        induction n; intros.
        --
          cbn in *.
          repeat break_match_hyp; try inl_inr;
            repeat inl_inr_inv; repeat some_inv; try some_none; subst.
          ++
            unfold mem_lookup_err,trywith in Heqs.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            unfold mem_lookup_err,trywith in Heqs0.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            destruct FA.
            specialize (bin_equiv0 c0 c).
            rewrite Heqs1 in bin_equiv0.
            inl_inr.
        --
          revert IHn EV.
          generalize (S n) as z.
          intros z IHn EV.
          cbn in EV.
          repeat break_match_hyp; try inl_inr;
            repeat inl_inr_inv; repeat some_inv; try some_none; subst.
          ++
            unfold mem_lookup_err,trywith in Heqs.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            unfold mem_lookup_err,trywith in Heqs0.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            destruct FA.
            specialize (bin_equiv0 c0 c).
            rewrite Heqs1 in bin_equiv0.
            inl_inr.
          ++
            eapply IHn in EV; eauto.
            unfold mem_lookup, mem_add.
            rewrite NP.F.add_eq_o.
            some_none.
            reflexivity.
  -
    exfalso.
    (*
      [mem_op] suceeds
      [evalDSHOperator] out of fuel
     *)
    contradict DOP.
    apply is_Some_ne_None.
    apply evalDSHOperator_estimateFuel.
  -
    exfalso.
    (*
       [mem_op] fails
       [evalDSHOperator] suceeds
     *)
    destruct (evalPexp σ x_p) as [| x_id] eqn:X;
      [unfold lookup_Pexp in X_M; rewrite X in X_M; inversion X_M |].
    destruct (evalPexp σ y_p) as [| y_id] eqn:Y;
      [unfold lookup_Pexp in Y_M; rewrite Y in Y_M; inversion Y_M |].

    cbn in X_M; rewrite X in X_M.
    cbn in Y_M; rewrite Y in Y_M.

    unfold memory_lookup_err, trywith in *.

    destruct (memory_lookup m x_id) eqn:X_M'; inversion X_M; subst;
      clear X_M; rename m0 into x_m', H1 into XME.
    destruct (memory_lookup m y_id) eqn:Y_M'; inversion Y_M; subst;
      clear Y_M; rename m0 into y_m', H1 into YME.

    (* simplify DOP down to evalDSHPower *)
    cbn in DOP; unfold NatAsNT.MNatAsNT.to_nat in *; some_inv; rename H0 into DOP.
    rewrite N in DOP.
    repeat break_match; try inl_inr.

    destruct n;[cbn in MOP;some_none|].
    cbn in MOP.
    unfold mem_op_of_hop in MOP.
    repeat break_match_hyp; try inl_inr;
      repeat inl_inr_inv; repeat some_inv; try some_none; subst.

    rename Heqs3 into EV.

    unfold memory_lookup_err, trywith in *.
    rewrite X_M' in Heqs1.
    rewrite Y_M' in Heqs2.
    repeat inl_inr_inv; subst.

    (* [x_m] is not dense *)
    rename Heqo into XD.
    apply mem_block_to_avector_eq_None in XD.
    clear -EV XD XME.

    destruct XD as (j & jc & XD).
    destruct j; [clear jc|lia].

    eq_to_equiv_hyp.
    err_eq_to_equiv_hyp.
    rewrite XME in EV.
    clear m2 XME.
    revert x_m XD EV.
    generalize (mem_add 0 init m3) as m0.
    clear_all.

    induction n; intros.
    *
      cbn in *.
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.
      unfold mem_lookup_err,trywith in Heqs.
      break_match_hyp; try inl_inr.
      eq_to_equiv_hyp.
      some_none.
    *
      revert IHn EV.
      generalize (S n) as z.
      intros z IHn EV.
      cbn in EV.
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.
      eapply IHn; eauto.
Qed.


(** * MSHIUnion *)

Global Instance Loop_DSH_pure
       {n : nat}
       {dop : DSHOperator}
       {y_p : PExpr}
       (P : DSH_pure dop (incrPVar 0 y_p))

  :
    DSH_pure (DSHLoop n dop) y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    generalize dependent fuel.
    generalize dependent m'.
    induction n.
    +
      intros.
      cbn in *.
      some_inv; inl_inr_inv.
      rewrite H; reflexivity.
    +
      intros.
      cbn in H.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      destruct fuel; [inversion Heqo |].
      eq_to_equiv_hyp.
      apply IHn in Heqo.
      rewrite Heqo.
      clear - P H.
      inversion P.
      eapply mem_stable0.
      eassumption.
  -
    intros.
    destruct fuel; [inversion H |].
    generalize dependent fuel.
    generalize dependent m'.
    induction n.
    +
      intros.
      cbn in *.
      some_inv; inl_inr_inv.
      unfold memory_equiv_except.
      intros.
      rewrite H.
      reflexivity.
    +
      intros.
      cbn in H.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      destruct fuel; [inversion Heqo |].
      eq_to_equiv_hyp.
      apply IHn in Heqo.
      unfold memory_equiv_except in *.
      intros.
      rewrite Heqo by assumption.
      inversion P.
      unfold memory_equiv_except in *.
      eapply mem_write_safe0.
      eassumption.
      rewrite evalPexp_incrPVar.
      eassumption.
      assumption.
Qed.

(* TODO: move *)
Global Instance mem_union_associative :
  Associative MMemoryOfCarrierA.mem_union.
Proof.
  intros b1 b2 b3.
  unfold equiv, mem_block_Equiv, MMemoryOfCarrierA.mem_union.
  intro k.
  repeat rewrite NP.F.map2_1bis by reflexivity.
  repeat break_match; try some_none.
  reflexivity.
Qed.

(* TODO: move *)
(* This is generalizeable to associtive functions on some types *)
Lemma IUnion_mem_append (l : list mem_block) (mb : mem_block) :
  ListUtil.fold_left_rev MMemoryOfCarrierA.mem_union
                         MMemoryOfCarrierA.mem_empty
                         (l ++ [mb])
  =
  MMemoryOfCarrierA.mem_union
    mb
    (ListUtil.fold_left_rev MMemoryOfCarrierA.mem_union
                            MMemoryOfCarrierA.mem_empty
                            l).
Proof.
  induction l; cbn.
  -
    unfold equiv, mem_block_Equiv, MMemoryOfCarrierA.mem_union, MMemoryOfCarrierA.mem_empty.
    intro k.
    repeat rewrite NP.F.map2_1bis by reflexivity.
    repeat break_match; try some_none.
    inversion Heqo.
  -
    rewrite IHl.
    pose proof mem_union_associative.
    unfold Associative, HeteroAssociative in H.
    rewrite H.
    reflexivity.
Qed.

Lemma nth_error_nil_None {A : Type} (n : nat) :
  List.nth_error [] n ≡ @None A.
Proof.
  destruct n; reflexivity.
Qed.

(* TODO: move *)
Lemma List_nth_nth_error {A : Type} (l1 l2 : list A) (n : nat) (d : A) :
  List.nth_error l1 n ≡ List.nth_error l2 n ->
  List.nth n l1 d ≡ List.nth n l2 d.
Proof.
  generalize dependent l2.
  generalize dependent l1.
  induction n.
  -
    intros.
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv.
    reflexivity.
    reflexivity.
  -
    intros.
    destruct l1, l2; cbn in *.
    +
      reflexivity.
    +
      specialize (IHn [] l2).
      rewrite nth_error_nil_None in IHn.
      specialize (IHn H).
      rewrite <-IHn.
      destruct n; reflexivity.
    +
      specialize (IHn l1 []).
      rewrite nth_error_nil_None in IHn.
      specialize (IHn H).
      rewrite IHn.
      destruct n; reflexivity.
    +
      apply IHn.
      assumption.
Qed.

Lemma IUnion_step {i o n : nat} (mb : mem_block) (S_opf : @MSHOperatorFamily i o (S n)) :
  let opf := shrink_m_op_family S_opf in
  let fn := mkFinNat (Nat.lt_succ_diag_r n) in
  mem_op (MSHIUnion S_opf) mb = mb' <- mem_op (MSHIUnion opf) mb ;;
                                mbn <- mem_op (S_opf fn) mb ;;
                                Some (MMemoryOfCarrierA.mem_union mbn mb').
Proof.
  simpl.
  unfold IUnion_mem.
  simpl.
  unfold Apply_mem_Family in *.
  repeat break_match;
    try discriminate; try reflexivity.
  all: repeat some_inv; subst.
  -
    rename l into S_lb, l0 into lb.

    (* poor man's apply to copy and avoid evars *)
    assert (S_LB : ∀ (j : nat) (jc : (j < S n)%mc),
               List.nth_error S_lb j ≡ get_family_mem_op S_opf j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).
    assert (LB : ∀ (j : nat) (jc : (j < n)%mc),
               List.nth_error lb j ≡ get_family_mem_op (shrink_m_op_family S_opf) j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).

    apply ListSetoid.monadic_Lbuild_opt_length in Heqo0; rename Heqo0 into S_L.
    apply ListSetoid.monadic_Lbuild_opt_length in Heqo3; rename Heqo3 into L.
    rename m0 into mbn, Heqo2 into MBN.

    unfold get_family_mem_op in *.
    assert (H : forall j, j < n -> List.nth_error lb j ≡ List.nth_error S_lb j)
      by (intros; erewrite S_LB, LB; reflexivity).
    Unshelve. 2: assumption.

    assert (N_MB : is_Some (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) mb)).
    {
      apply is_Some_ne_None.
      intro C.
      rewrite <-S_LB in C.
      apply List.nth_error_None in C.
      lia.
    }
    apply is_Some_def in N_MB.
    destruct N_MB as [n_mb N_MB].

    assert (H1 : S_lb ≡ lb ++ [n_mb]).
    {
      apply list_eq_nth;
        [rewrite List.app_length; cbn; lia |].
      intros k KC.
      (* extensionality *)
      enough (forall d, List.nth k S_lb d ≡ List.nth k (lb ++ [n_mb]) d)
        by (apply Logic.FunctionalExtensionality.functional_extensionality; assumption).
      rewrite S_L in KC.
      destruct (Nat.eq_dec k n).
      -
        subst k.
        intros.
        apply List_nth_nth_error.
        replace n with (0 + Datatypes.length lb).
        rewrite ListNth.nth_error_length.
        cbn.
        rewrite L.
        rewrite S_LB with (jc := (Nat.lt_succ_diag_r n)).
        rewrite <-N_MB.
        reflexivity.
      -
        assert (k < n) by lia; clear KC n0.
        intros.
        apply List_nth_nth_error.
        rewrite <-H by lia.
        rewrite List.nth_error_app1 by lia.
        reflexivity.
    }

    rewrite H1.
    rewrite IUnion_mem_append.

    rewrite MBN in N_MB; some_inv.
    reflexivity.
  -
    rename l into S_lb, l0 into lb.

    (* poor man's apply to copy and avoid evars *)
    assert (S_LB : ∀ (j : nat) (jc : (j < S n)%mc),
               List.nth_error S_lb j ≡ get_family_mem_op S_opf j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).
    apply ListSetoid.monadic_Lbuild_opt_length in Heqo0; rename Heqo0 into S_L.

    assert (N_MB : is_Some (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) mb)).
    {
      apply is_Some_ne_None.
      intro C.
      unfold get_family_mem_op in *.
      rewrite <-S_LB in C.
      apply List.nth_error_None in C.
      lia.
    }

    rewrite Heqo2 in N_MB.
    some_none.
  -
    exfalso; clear Heqo1.

    pose proof Heqo0 as L; apply ListSetoid.monadic_Lbuild_opt_length in L.

    apply ListSetoid.monadic_Lbuild_op_eq_None in Heqo2.
    destruct Heqo2 as [k [KC N]].
    apply ListSetoid.monadic_Lbuild_op_eq_Some
      with (i0:=k) (ic:=le_S KC)
      in Heqo0.
    unfold get_family_mem_op, shrink_m_op_family in *.
    cbn in *.
    rewrite N in Heqo0.
    apply ListNth.nth_error_length_ge in Heqo0.
    assert (k < n) by assumption.
    lia.
  -
    exfalso.

    pose proof Heqo3 as S_L; apply ListSetoid.monadic_Lbuild_opt_length in S_L.

    apply ListSetoid.monadic_Lbuild_op_eq_None in Heqo0.
    destruct Heqo0 as [k [KC N]].
    destruct (Nat.eq_dec k n).
    +
      subst k.
      unfold get_family_mem_op in *.
      assert (KC ≡ (Nat.lt_succ_diag_r n)) by (apply lt_unique).
      rewrite <-H, N in Heqo2.
      some_none.
    +
      assert (k < n) by (assert (k < S n) by assumption; lia); clear n0.
      apply ListSetoid.monadic_Lbuild_op_eq_Some
        with (i0:=k) (ic:=H)
        in Heqo3.
      unfold get_family_mem_op, shrink_m_op_family in *.
      cbn in Heqo3.
      assert (le_S H ≡ KC) by (apply lt_unique).
      rewrite H0, N in Heqo3.
      apply ListNth.nth_error_length_ge in Heqo3.
      rewrite S_L in Heqo3.
      omega.
Qed.

Global Instance SHCOL_DSHCOL_mem_block_equiv_proper :
  Proper ((=) ==> (=) ==> (=) ==> iff) SHCOL_DSHCOL_mem_block_equiv.
Proof.
  intros mb mb' MBE ma ma' MAE md md' MDE.
  unfold SHCOL_DSHCOL_mem_block_equiv.
  split; intros.
  all: specialize (H i).
  -
    rewrite MBE, MAE, MDE in H.
    assumption.
  -
    rewrite <-MBE, <-MAE, <-MDE in H.
    assumption.
Qed.

Global Instance lookup_Pexp_proper :
  Proper ((=) ==> (=) ==> (=) ==> (=)) lookup_Pexp.
Proof.
  intros σ σ' Σ m m' M p p' P.
  unfold lookup_Pexp, memory_lookup_err, trywith.
  cbn.
  repeat break_match.
  all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
  all: try rewrite Σ in *.
  all: try rewrite M in *.
  all: try rewrite P in *.
  all: try constructor.
  all: rewrite Heqs in *.
  all: try inl_inr; inl_inr_inv.
  all: rewrite Heqs0 in *.
  all: rewrite Heqo in *.
  all: inversion Heqo0.
  assumption.
Qed.

Lemma lookup_Pexp_incrPVar (foo : DSHVal) (σ : evalContext) (m : memory) (p : PExpr) :
  lookup_Pexp (foo :: σ) m (incrPVar 0 p) ≡
  lookup_Pexp σ m p.
Proof.
  unfold lookup_Pexp.
  rewrite evalPexp_incrPVar.
  reflexivity.
Qed.

Lemma estimateFuel_positive (dop : DSHOperator) :
  1 <= estimateFuel dop.
Proof.
  induction dop.
  all: try (cbn; constructor; fail).
  all: cbn; lia.
Qed.

Global Instance IUnion_MSH_DSH_compat
       {i o n : nat}
       {dop : DSHOperator}
       {x_p y_p : PExpr}
       {σ : evalContext}
       {m : memory}
       {XY : evalPexp σ x_p <> evalPexp σ y_p}
       {opf : MSHOperatorFamily}
       {DP : DSH_pure dop (incrPVar 0 y_p)}
       {LP : DSH_pure (DSHLoop n dop) y_p}
       (FC : forall t m' y_i,
           evalPexp σ y_p ≡ inr y_i ->
           memory_equiv_except m m' y_i ->
           @MSH_DSH_compat _ _ (opf t) dop
                           ((DSHnatVal (proj1_sig t)) :: σ)
                           m' (incrPVar 0 x_p) (incrPVar 0 y_p) DP)
  :
    @MSH_DSH_compat _ _ (@MSHIUnion i o n opf) (DSHLoop n dop) σ m x_p y_p LP.
Proof.
  constructor.
  intros x_m y_m X_M Y_M.

  generalize dependent m.
  induction n.
  -
    intros.
    cbn in *.
    constructor.
    break_match; try inl_inr.
    destruct memory_lookup_err; try inl_inr; inl_inr_inv.
    constructor.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    intros k.
    constructor 1.
    reflexivity.
    rewrite Y_M.
    reflexivity.
  -
    intros.
    simpl evalDSHOperator.
    repeat break_match; subst.
    +
      (* evalDSHOperator errors *)
      pose (opf' := shrink_m_op_family opf).
      assert (T1 : DSH_pure (DSHLoop n dop) y_p) by (apply Loop_DSH_pure; assumption).
      assert (T2: (∀ t m' y_i,
                      evalPexp σ y_p ≡ inr y_i ->
                      memory_equiv_except m m' y_i ->
                      MSH_DSH_compat (opf' t) dop (DSHnatVal (` t) :: σ) m'
                                     (incrPVar 0 x_p) (incrPVar 0 y_p))).
      {
        clear - FC.
        subst opf'.
        intros.
        unfold shrink_m_op_family.
        specialize (FC (mkFinNat (le_S (proj2_sig t))) m' y_i H H0).
        enough (T : (` (mkFinNat (le_S (proj2_sig t)))) ≡ (` t))
          by (rewrite T in FC; assumption).
        cbv.
        repeat break_match; congruence.
      }
      specialize (IHn opf' T1 m T2 X_M Y_M); clear T1 T2.
      rewrite evalDSHOperator_estimateFuel_ge in Heqo0
        by (pose proof estimateFuel_positive dop; cbn; lia).
      rewrite Heqo0 in IHn; clear Heqo0.
      rename opf into S_opf, opf' into opf.

      subst opf.
      remember (λ (md : mem_block) (m' : memory),
             err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
               (lookup_Pexp σ m' y_p))
        as R.
      assert (RP : Proper (equiv ==> equiv ==> iff) R).
      {
        subst; clear.
        intros m1 m2 E1 m3 m4 E2.
        split; intros H; inversion H; clear H; err_eq_to_equiv_hyp.
        -
          assert (Proper ((=) ==> iff)
                         (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m2))
            by (intros m m' ME; rewrite ME; reflexivity).
          rewrite <-E2.
          rewrite <-H0.
          constructor.
          rewrite <-E1.
          assumption.
        -
          assert (Proper ((=) ==> iff)
                         (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m1))
            by (intros m m' ME; rewrite ME; reflexivity).
          rewrite E2.
          rewrite <-H0.
          constructor.
          rewrite E1.
          assumption.
      }

      rewrite IUnion_step.
      clear RP.

      inversion IHn; clear IHn; subst.
      simpl.
      rewrite <-H0.
      constructor.
    +
      rename m0 into loop_m.
      
      pose (opf' := shrink_m_op_family opf).
      assert (T1 : DSH_pure (DSHLoop n dop) y_p) by (apply Loop_DSH_pure; assumption).
      assert (T2: (∀ t m' y_i,
                      evalPexp σ y_p ≡ inr y_i ->
                      memory_equiv_except m m' y_i ->
                      MSH_DSH_compat (opf' t) dop (DSHnatVal (` t) :: σ) m'
                                     (incrPVar 0 x_p) (incrPVar 0 y_p))).
      {
        clear - FC.
        subst opf'.
        intros.
        unfold shrink_m_op_family.
        specialize (FC (mkFinNat (le_S (proj2_sig t))) m' y_i H H0).
        enough (T : (` (mkFinNat (le_S (proj2_sig t)))) ≡ (` t))
          by (rewrite T in FC; assumption).
        cbv.
        repeat break_match; congruence.
      }
      specialize (IHn opf' T1 m T2 X_M Y_M); clear T1 T2.
      rewrite evalDSHOperator_estimateFuel_ge in Heqo0
        by (pose proof estimateFuel_positive dop; cbn; lia).
      rewrite Heqo0 in IHn.
      rename opf into S_opf, opf' into opf.

      subst opf.
      remember (λ (md : mem_block) (m' : memory),
             err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
               (lookup_Pexp σ m' y_p))
        as R.
      assert (RP : Proper (equiv ==> equiv ==> iff) R).
      {
        subst; clear.
        intros m1 m2 E1 m3 m4 E2.
        split; intros H; inversion H; clear H; err_eq_to_equiv_hyp.
        -
          assert (Proper ((=) ==> iff)
                         (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m2))
            by (intros m m' ME; rewrite ME; reflexivity).
          rewrite <-E2.
          rewrite <-H0.
          constructor.
          rewrite <-E1.
          assumption.
        -
          assert (Proper ((=) ==> iff)
                         (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m1))
            by (intros m m' ME; rewrite ME; reflexivity).
          rewrite E2.
          rewrite <-H0.
          constructor.
          rewrite E1.
          assumption.
      }

      rewrite IUnion_step.
      clear RP.

      inversion IHn; clear IHn; subst.
      inversion H1; clear H1; subst.
      cbn [mem_op MSHIUnion].
      rewrite <-H.
      simpl.
      rename a into mm, H into MM, x into y_lm, H0 into Y_LM, H2 into LE.
      symmetry in MM, Y_LM.

      destruct (evalPexp σ y_p) as [|y_i] eqn:YI;
        [unfold lookup_Pexp in Y_M; rewrite YI in Y_M; cbn in Y_M; inl_inr |].
      assert (T : memory_equiv_except m loop_m y_i).
      {
        clear - Heqo0 DP YI.
        assert (LP : DSH_pure (DSHLoop n dop) y_p)
         by (apply Loop_DSH_pure; assumption).
        inversion_clear LP as [T S]; clear T.
        err_eq_to_equiv_hyp; eq_to_equiv_hyp.
        apply S with (y_i:=y_i) in Heqo0.
        assumption.
        assumption.
      }
      specialize (FC (mkFinNat (Nat.lt_succ_diag_r n)) loop_m y_i eq_refl T); clear T.
      cbn in FC.
      inversion_clear FC as [F].

      assert (T1 : lookup_Pexp (DSHnatVal n :: σ) loop_m (incrPVar 0 x_p) = inr x_m).
      {
        rewrite lookup_Pexp_incrPVar.
        clear - Heqo0 DP Y_M X_M XY YI.
        pose proof @Loop_DSH_pure n dop y_p DP.
        inversion_clear H as [T C]; clear T.
        err_eq_to_equiv_hyp; eq_to_equiv_hyp.
        specialize (C σ m loop_m (estimateFuel (DSHLoop n dop)) Heqo0 y_i YI).
        unfold memory_equiv_except in *.
        clear - X_M C XY.
        unfold lookup_Pexp, memory_lookup_err in *; cbn in *.
        destruct (evalPexp σ x_p); try inl_inr.
        assert (m0 ≢ y_i)
          by (intros T; contradict XY; f_equal; assumption).
        specialize (C m0 H).
        rewrite <-C.
        assumption.
      }
      
      assert (T2 : lookup_Pexp (DSHnatVal n :: σ) loop_m (incrPVar 0 y_p) = inr y_lm)
        by (rewrite lookup_Pexp_incrPVar, Y_LM; reflexivity).
      specialize (F x_m y_lm T1 T2); clear T1 T2.

      rewrite evalDSHOperator_estimateFuel_ge by nia.
      remember (evalDSHOperator (DSHnatVal n :: σ) dop loop_m (estimateFuel dop)) as dm;
        clear Heqdm.
      remember (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) x_m) as mmb;
        clear Heqmmb.

      inversion F; clear F; try constructor.
      subst.
      inversion H; clear H.
      rewrite lookup_Pexp_incrPVar in H0.
      rewrite <-H0.
      constructor.
      clear - H1 LE.

      eapply SHCOL_DSHCOL_mem_block_equiv_comp; eassumption.
    +
      exfalso; clear - Heqo0.
      contradict Heqo0.
      apply is_Some_ne_None.
      rewrite evalDSHOperator_estimateFuel_ge
        by (pose proof estimateFuel_positive dop; cbn; lia).
      apply evalDSHOperator_estimateFuel.
Qed.


(** * MSHCompose *)

Global Instance Compose_DSH_pure
         {n: nat}
         {y_p: PExpr}
         {dop1 dop2: DSHOperator}
         (P2: DSH_pure dop2 (PVar 0))
         (P1: DSH_pure dop1 (incrPVar 0 y_p))
  : DSH_pure (DSHAlloc n (DSHSeq dop2 dop1)) y_p.
Proof.
  split.
  - (* mem_stable *)
    intros σ m m' fuel H k.
    destruct P1 as [MS1 _].
    destruct P2 as [MS2 _].
    destruct fuel; simpl in *; try some_none.
    repeat break_match_hyp; try some_none.
    inversion H; inversion H2.
    destruct fuel; simpl in *; try some_none.
    break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename Heqo into D1, Heqs0 into D2.
    inl_inr_inv. rewrite <- H. clear m' H.
    remember (memory_next_key m) as k'.

    destruct(Nat.eq_dec k k') as [E|NE].
    +
      break_match; [inversion D1 |].
      subst.
      split; intros H.
      *
        contradict H.
        apply mem_block_exists_memory_next_key.
      *
        contradict H.
        apply mem_block_exists_memory_remove.
    +
      break_match; [inversion D1 |].
      subst.
      rename Heqo0 into D2.
      apply Option_equiv_eq in D1.
      apply Option_equiv_eq in D2.
      apply MS2 with (k:=k) in D2.
      apply MS1 with (k:=k) in D1.
      clear MS1 MS2.
      split; intros H.
      *
        eapply mem_block_exists_memory_set in H.
        apply D2 in H.
        apply D1 in H.
        erewrite <- mem_block_exists_memory_remove_neq; eauto.
      *
        eapply mem_block_exists_memory_set_neq.
        eauto.
        eapply D2.
        eapply D1.
        eapply mem_block_exists_memory_remove_neq; eauto.
  -
    (* mem_write_safe *)
    intros σ m0 m4 fuel H y_i H0.
    destruct fuel; simpl in *; try some_none.
    repeat break_match_hyp;
      try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
    destruct fuel; simpl in *; try some_none.
    repeat break_match_hyp;
      try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
    subst.
    rename m1 into m2, m into m3.
    rename Heqo into E1, Heqo0 into E2.
    remember (memory_next_key m0) as t_i.
    remember (memory_set m0 t_i mem_empty) as m1.
    remember (DSHPtrVal t_i n :: σ) as σ'.
    intros k ky.


    destruct (Nat.eq_dec k t_i) as [kt|kt].
    1:{

      subst k.
      pose proof (mem_block_exists_memory_next_key m0) as H1.
      rewrite <- Heqt_i in H1.

      unfold mem_block_exists in H1.
      apply NP.F.not_find_in_iff in H1.
      unfold memory_lookup.
      rewrite_clear H1.
      symmetry.

      pose proof (mem_block_exists_memory_remove t_i m3) as H4.
      unfold mem_block_exists in H4.
      apply NP.F.not_find_in_iff in H4.
      unfold equiv, memory_Equiv in H.
      rewrite <- H.
      rewrite H4.
      reflexivity.
    }

    destruct P1 as [P1p P1w].
    destruct P2 as [P2p P2w].
    apply Option_equiv_eq in E1.
    apply Option_equiv_eq in E2.
    specialize (P1p _ _ _ _ E1).
    specialize (P1w _ _ _ _ E1).
    specialize (P2p _ _ _ _ E2).
    specialize (P2w _ _ _ _ E2).

    destruct(decidable_mem_block_exists k m0) as [F0|NF0]; symmetry.
    2:{

      assert(¬ mem_block_exists k m1) as NF1.
      {
        revert NF0.
        apply not_iff_compat.
        subst m1.
        symmetry.
        apply mem_block_exists_memory_set_neq.
        apply kt.
      }

      specialize (P2p k).
      apply not_iff_compat in P2p.
      apply P2p in NF1.

      specialize (P1p k).
      apply not_iff_compat in P1p.
      apply P1p in NF1.

      assert(¬ mem_block_exists k m4) as NF4.
      {
        rewrite <- H.
        erewrite <- mem_block_exists_memory_remove_neq; eauto.
      }

      unfold mem_block_exists in NF4.
      apply NP.F.not_find_in_iff in NF4.
      unfold memory_lookup.
      rewrite NF4.

      unfold mem_block_exists in NF0.
      apply NP.F.not_find_in_iff in NF0.
      rewrite NF0.
      reflexivity.
    }

    assert (V := F0).
    apply NP.F.in_find_iff, is_Some_ne_None, is_Some_def in V.
    destruct V as [v V].
    unfold memory_lookup.
    rewrite V.

    cut(NM.find (elt:=mem_block) k m3 = Some v).
    intros F3.
    unfold equiv, memory_Equiv in H.
    rewrite <- H.
    unfold memory_remove.
    rewrite NP.F.remove_neq_o; auto.

    cut(NM.find (elt:=mem_block) k m2 = Some v).
    intros F2.
    unfold memory_equiv_except, memory_lookup in P1w.
    specialize (P1w y_i).
    erewrite <- P1w; auto.
    subst σ'.
    rewrite evalPexp_incrPVar.
    assumption.

    cut(NM.find (elt:=mem_block) k m1 = Some v).
    intros F1.
    unfold memory_equiv_except, memory_lookup in P2w.
    specialize (P2w t_i).
    erewrite <- P2w; auto.
    subst σ'.
    reflexivity.

    unfold equiv, memory_Equiv in Heqm1.
    rewrite Heqm1.
    unfold memory_set.
    rewrite NP.F.add_neq_o; auto.
    rewrite V.
    reflexivity.
Qed.

Global Instance Compose_MSH_DSH_compat
         {i1 o2 o3: nat}
         {mop1: @MSHOperator o2 o3}
         {mop2: @MSHOperator i1 o2}
         {σ: evalContext}
         {m: memory}
         {dop1 dop2: DSHOperator}
         {x_p y_p: PExpr}
         (P: DSH_pure (DSHAlloc o2 (DSHSeq dop2 dop1)) y_p)
         (P2: DSH_pure dop2 (PVar 0))
         (P1: DSH_pure dop1 (incrPVar 0 y_p))
         (C2: @MSH_DSH_compat _ _ mop2 dop2
                              (DSHPtrVal (memory_next_key m) o2 :: σ)
                              (memory_alloc_empty m (memory_next_key m))
                              (incrPVar 0 x_p) (PVar 0)
                              P2
          )
         (C1: forall m'', memory_equiv_except m m'' (memory_next_key m) ->
                      @MSH_DSH_compat _ _ mop1 dop1
                                     (DSHPtrVal (memory_next_key m) o2 :: σ)
                                     m''
                                     (PVar 0) (incrPVar 0 y_p) P1)
  :
    @MSH_DSH_compat _ _
      (MSHCompose mop1 mop2)
      (DSHAlloc o2 (DSHSeq dop2 dop1))
      σ m x_p y_p P.
Proof.
  split.
  intros mx mb MX MB.
  simpl.

  remember (memory_next_key m) as t_i.
  remember (DSHPtrVal t_i o2 :: σ) as σ'.
  unfold memory_alloc_empty in *.
  remember (memory_set m t_i mem_empty) as m'.

  destruct (option_compose (mem_op mop1) (mem_op mop2) mx) as [md|] eqn:MD;
    repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv;
    repeat constructor.

  -
    exfalso.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    unfold memory_lookup, memory_remove.

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs1.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2.
  -
    exfalso.
    rename m0 into m''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs3.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2; subst a b; clear C2; rename H3 into C2.

    assert(mem_block_exists t_i m') as ET'.
    {
      subst m'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    assert(mem_block_exists t_i m'') as ET''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
    symmetry in MT''.

    apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
    apply err_equiv_eq in MT''.
    rewrite C2 in MT''.
    clear C2 mt'.

    specialize (C1 m'').
    destruct C1 as [C1].

    1:{
      eapply memory_equiv_except_trans.
      eapply memory_equiv_except_memory_set.
      eapply Heqm'.
      intros.
      destruct P2.
      eapply mem_write_safe0.
      rewrite E2.
      reflexivity.
      subst σ'.
      reflexivity.
    }

    specialize (C1 mt mb MT'').
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs1.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        assert (memory_lookup m y_i = Some mb).
        {
         clear - MB.
         unfold memory_lookup_err, trywith in MB.
         break_match; inversion MB.
         rewrite H1; reflexivity.
        }

        rewrite <-H1.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      enough (T : memory_lookup m'' y_i = Some mb)
        by (unfold memory_lookup_err; rewrite T; reflexivity).
      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1.
  -
    rename m1 into m''.
    rename m0 into m'''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    simpl.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    unfold memory_lookup_err, memory_lookup, memory_remove.
    rewrite NP.F.remove_neq_o by assumption.

    assert(mem_block_exists y_i m) as EY.
    {
      apply mem_block_exists_exists_equiv.
      eexists.
      unfold memory_lookup_err, trywith in MB.
      break_match_hyp; inversion MB.
      constructor.
      apply H3.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    assert(mem_block_exists y_i m''') as EY'''.
    {
      destruct P1.
      eapply (mem_stable0  _ m'' m''').
      apply Option_equiv_eq in E1.
      eapply E1.
      assumption.
    }

    destruct (NM.find (elt:=mem_block) y_i m''') as [ma|] eqn:MA .
    2:{
      apply memory_is_set_is_Some, is_Some_ne_None in EY'''.
      unfold memory_lookup in EY'''.
      congruence.
    }
    constructor.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    intros k.

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs3.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2; subst a b; clear C2 ; rename H3 into C2.

    assert(mem_block_exists t_i m') as ET'.
    {
      subst m'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    assert(mem_block_exists t_i m'') as ET''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
    symmetry in MT''.

    apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
    apply err_equiv_eq in MT''.
    rewrite C2 in MT''.
    clear C2 mt'.

    specialize (C1 m'').
    destruct C1 as [C1].

    1:{
      eapply memory_equiv_except_trans.
      eapply memory_equiv_except_memory_set.
      eapply Heqm'.
      intros.
      destruct P2.
      eapply mem_write_safe0.
      rewrite E2.
      reflexivity.
      subst σ'.
      reflexivity.
    }

    specialize (C1 mt mb MT'').
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs2.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        unfold memory_lookup_err, trywith in MB.
        break_match_hyp; inversion MB; subst.
        rewrite <-H3.
        rewrite <-Heqo.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }


      unfold memory_lookup_err.
      enough (T : memory_lookup m'' y_i = Some mb) by (rewrite T; reflexivity).
      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1 as [ | | ab bm HC1 HA HB];
      clear C1; rename HC1 into C1;
        subst ab; subst bm.

    assert(MA''': lookup_Pexp σ' m''' (incrPVar 0 y_p) = inr ma).
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs2.
      unfold memory_lookup_err.
      enough (T : memory_lookup m''' y_i = Some ma) by (rewrite T; reflexivity).
      unfold memory_lookup.
      rewrite MA.
      reflexivity.
    }

    assert(PC1: Proper ((=) ==> iff)
                       (λ z : mem_block, SHCOL_DSHCOL_mem_block_equiv mb z md)).
    {
      unfold SHCOL_DSHCOL_mem_block_equiv.
      simpl_relation.
      split.
      -
        intros H4 i.
        specialize (H4 i).
        rewrite <- H1.
        auto.
      -
        intros H4 i.
        specialize (H4 i).
        rewrite H1.
        auto.
    }
    rewrite MA''' in C1.
    inversion C1.
    auto.
  -
    exfalso.
    rename m0 into m''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs2.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2; subst a b; clear C2; rename H3 into C2.

    assert(mem_block_exists t_i m') as ET'.
    {
      subst m'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    assert(mem_block_exists t_i m'') as ET''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
    symmetry in MT''.

    apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
    apply err_equiv_eq in MT''.
    rewrite C2 in MT''.
    clear C2 mt'.

    specialize (C1 m'').
    destruct C1 as [C1].

    1:{
      eapply memory_equiv_except_trans.
      eapply memory_equiv_except_memory_set.
      eapply Heqm'.
      intros.
      destruct P2.
      eapply mem_write_safe0.
      rewrite E2.
      reflexivity.
      subst σ'.
      reflexivity.
    }

    specialize (C1 mt mb MT'').
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs1.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        assert (memory_lookup m y_i = Some mb).
        {
         clear - MB.
         unfold memory_lookup_err, trywith in MB.
         break_match; inversion MB.
         rewrite H1; reflexivity.
        }

        rewrite <-H1.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      enough (T : memory_lookup m'' y_i = Some mb)
        by (unfold memory_lookup_err; rewrite T; reflexivity).
      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1.
  -
    exfalso.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename m1 into x_i, m0 into y_i.
    clear Heqo.
    rename Heqo0 into E2.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    unfold memory_lookup, memory_remove.

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs0.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2.
  -
    exfalso.
    rename m1 into m''.
    rename m0 into m'''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    assert(mem_block_exists y_i m''') as EY'''.
    {
      destruct P1.
      eapply (mem_stable0  _ m'' m''').
      apply Option_equiv_eq in E1.
      eapply E1.
      assumption.
    }

    destruct (NM.find (elt:=mem_block) y_i m''') as [ma|] eqn:MA .
    2:{
      apply memory_is_set_is_Some, is_Some_ne_None in EY'''.
      unfold memory_lookup in EY'''.
      congruence.
    }

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    unfold option_compose in MD.

    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.
    +
      (* mop2 = Some, mop1 = None *)
      assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqs3.
        subst m'.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        apply MX.
        auto.
      }
      specialize (C2 MX').

      assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        subst m'.
        simpl.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_eq_o; reflexivity.
      }
      specialize (C2 MT').

      rewrite E2 in C2.
      inversion C2; subst a b; clear C2; rename H3 into C2.

      assert(mem_block_exists t_i m') as ET'.
      {
        subst m'.
        apply mem_block_exists_memory_set_eq.
        reflexivity.
      }

      assert(mem_block_exists t_i m'') as ET''.
      {
        destruct P2.
        eapply (mem_stable0  _ m' m'').
        apply Option_equiv_eq in E2.
        eapply E2.
        assumption.
      }

      inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
      symmetry in MT''.

      apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
      apply err_equiv_eq in MT''.
      rewrite C2 in MT''.
      clear C2 mt'.

      specialize (C1 m'').
      destruct C1 as [C1].

      1:{
        eapply memory_equiv_except_trans.
        eapply memory_equiv_except_memory_set.
        eapply Heqm'.
        intros.
        destruct P2.
        eapply mem_write_safe0.
        rewrite E2.
        reflexivity.
        subst σ'.
        reflexivity.
      }

      specialize (C1 mt mb MT'').
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqs2.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        assert (memory_lookup m y_i = Some mb).
        {
         clear - MB.
         unfold memory_lookup_err, trywith in MB.
         break_match; inversion MB.
         rewrite H1; reflexivity.
        }

        rewrite <-H1.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      enough (T : memory_lookup m'' y_i = Some mb)
        by (unfold memory_lookup_err; rewrite T; reflexivity).
      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

      specialize (C1 MB'').
      rewrite MD, E1 in C1.

      inversion C1.
    +
      (* mop2 = None, no mop1 *)

      assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqs3.
        subst m'.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        apply MX.
        auto.
      }
      specialize (C2 MX').

      assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        subst m'.
        simpl.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_eq_o; reflexivity.
      }
      specialize (C2 MT').

      rewrite E2 in C2.
      inversion C2; subst a b; clear C2; rename H4 into C2.
Qed.


(** * MHTSUMUnioin *)

Global Instance HTSUMUnion_MSH_DSH_compat
         {i o : nat}
         {mop1: @MSHOperator i o}
         {mop2: @MSHOperator i o}
         {m: memory}
         {σ: evalContext}
         {dop1 dop2: DSHOperator}
         {x_p y_p : PExpr}
         (P: DSH_pure (DSHSeq dop1 dop2) y_p)
         (D : herr_f nat nat (compose2 not equiv) (evalPexp σ x_p) (evalPexp σ y_p))
         (P1: DSH_pure dop1 y_p)
         (P2: DSH_pure dop2 y_p)
         (C1: @MSH_DSH_compat _ _ mop1 dop1 σ m x_p y_p P1)
         (C2: forall m', lookup_Pexp σ m x_p = lookup_Pexp σ m' x_p ->
                      @MSH_DSH_compat _ _ mop2 dop2 σ m' x_p y_p P2)
  :
    @MSH_DSH_compat _ _
      (MHTSUMUnion dot mop1 mop2)
      (DSHSeq dop1 dop2)
      σ m x_p y_p P.
Proof.
  constructor; intros x_m y_m X_M Y_M.

  destruct (evalPexp σ x_p) as [| x_id] eqn:X;
    [unfold lookup_Pexp in X_M; rewrite X in X_M; inversion X_M |].
  destruct (evalPexp σ y_p) as [| y_id] eqn:Y;
    [unfold lookup_Pexp in Y_M; rewrite Y in Y_M; inversion Y_M |].
  assert (XY : x_id <> y_id).
  {
    clear - D.
    cbv in D.
    inversion D.
    intros C.
    apply H1 in C.
    inversion C.
  }

  destruct mem_op as [mma |] eqn:MOP.
  all: destruct evalDSHOperator as [r |] eqn:DOP; [destruct r as [msg | dma] |].
  all: repeat constructor.

  1,3,4: exfalso.
  -
    cbn in MOP.
    destruct (mem_op mop2 x_m) as [mma2 |] eqn:MOP2; [| some_none].
    destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1; [| some_none].
    some_inv; subst.

    cbn in DOP.
    destruct evalDSHOperator as [r |] eqn:DOP1 in DOP; [| some_none];
      destruct r as [msg1 | dma1]; inversion DOP; subst; clear DOP.
    +
      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1.
    +
      rename H0 into DOP2.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2.
  -
    cbn in MOP.
    destruct (mem_op mop2 x_m) as [mma2 |] eqn:MOP2; [| some_none].
    destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1; [| some_none].
    some_inv; subst.

    cbn in DOP.
    destruct evalDSHOperator as [r |] eqn:DOP1 in DOP.
    +
      destruct r as [| dma1]; inversion DOP; subst; clear DOP.
      rename H0 into DOP2.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2.
    +
      clear DOP.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1.
  -
    cbn in DOP.
    destruct evalDSHOperator as [r |] eqn:DOP1 in DOP; [| some_none].
    destruct r as [| dma1]; [some_inv; inl_inr |].
    rename DOP into DOP2.
    
    cbn in MOP.
    destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1.
    +
      destruct (mem_op mop2 x_m) eqn:MOP2; [some_none |].
      clear MOP.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.
      
      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2.
    +
      clear MOP.
      
      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.
      
      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1.
  -
    unfold lookup_Pexp; cbn.
    rewrite Y.
    unfold memory_lookup_err.
    destruct (memory_lookup dma y_id) as [y_dma |] eqn:Y_DMA.
    +
      constructor.
      unfold SHCOL_DSHCOL_mem_block_equiv.
      intro k.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      unfold memory_lookup_err, trywith in X_M, Y_M.
      assert (X_M' : memory_lookup m x_id = Some x_m)
        by (clear - X_M; break_match; inversion X_M; rewrite H1; reflexivity).
      assert (Y_M' : memory_lookup m y_id = Some y_m)
        by (clear - Y_M; break_match; inversion Y_M; rewrite H1; reflexivity).
      clear X_M Y_M; rename X_M' into X_M, Y_M' into Y_M.


      cbn in MOP.
      destruct (mem_op mop2 x_m) as [mma2 |] eqn:MOP2; [| some_none].
      destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1; [| some_none].
      some_inv; subst.

      cbn in DOP.
      destruct evalDSHOperator as [r |] eqn:DOP1 in DOP; [| some_none].
      destruct r as [| dma1]; [some_inv; inl_inr |].
      rename DOP into DOP2.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2; subst.
      inversion H1; clear C2 H1.
      rename x into y_dma2, H into Y_DMA2, H0 into C2; symmetry in Y_DMA2.
      replace y_dma2 with y_dma in *.
      2: {
        clear - Y Y_DMA Y_DMA2.
        unfold lookup_Pexp, memory_lookup_err in Y_DMA2.
        rewrite Y in Y_DMA2.
        cbn in Y_DMA2.
        rewrite Y_DMA in Y_DMA2.
        inversion Y_DMA2.
        reflexivity.
      }
      clear y_dma2 Y_DMA2.

      eapply SHCOL_DSHCOL_mem_block_equiv_comp; eassumption.
    +
      exfalso.
      clear - P DOP Y Y_M Y_DMA.

      rewrite <-mem_block_not_exists_exists in Y_DMA.
      contradict Y_DMA.

      inversion P; clear mem_write_safe0; rename mem_stable0 into MS.
      apply Option_equiv_eq in DOP.
      apply MS with (k := y_id) in DOP; clear MS.

      apply DOP, mem_block_exists_exists_equiv.
      exists y_m.
      unfold lookup_Pexp in Y_M.
      rewrite Y in Y_M.
      cbn in Y_M.
      unfold memory_lookup_err, trywith in Y_M.
      break_match; inversion Y_M.
      rewrite H1; reflexivity.
Qed.


(** * MSHIReduction *)

(* TODO: move *)
Lemma memory_set_overwrite (m : memory) (k k' : mem_block_id) (mb mb' : mem_block) :
  k = k' ->
  memory_set (memory_set m k mb) k' mb' = memory_set m k' mb'.
Proof.
  intros E; cbv in E; subst k'.
  unfold memory_set, equiv, memory_Equiv.
  intros j.
  destruct (Nat.eq_dec k j).
  -
    repeat rewrite NP.F.add_eq_o by assumption.
    reflexivity.
  -
    repeat rewrite NP.F.add_neq_o by assumption.
    reflexivity.
Qed.

Global Instance memory_remove_proper :
  Proper ((=) ==> (=) ==> (=)) memory_remove.
Proof.
  intros m1 m2 ME k1 k2 KE.
  unfold memory_remove, equiv, memory_Equiv.
  intros k.
  destruct (Nat.eq_dec k1 k).
  -
    assert (k2 ≡ k) by (unfold equiv, nat_equiv in KE; congruence).
    repeat rewrite NP.F.remove_eq_o by assumption.
    reflexivity.
  -
    assert (k2 ≢ k) by (unfold equiv, nat_equiv in KE; congruence).
    repeat rewrite NP.F.remove_neq_o by assumption.
    apply ME.
Qed.

Lemma memory_remove_memory_set_eq (m : memory) (k k' : mem_block_id) (mb : mem_block) :
  k = k' ->
  memory_remove (memory_set m k mb) k' = memory_remove m k.
Proof.
  intros; cbv in H; subst k'.
  unfold memory_remove, memory_set, equiv, memory_Equiv.
  intros j.
  destruct (Nat.eq_dec k j).
  -
    repeat rewrite NP.F.remove_eq_o by assumption.
    reflexivity.
  -
    repeat rewrite NP.F.remove_neq_o by assumption.
    rewrite NP.F.add_neq_o by assumption.
    reflexivity.
Qed.

Lemma memory_remove_nonexistent_key (m : memory) (k : mem_block_id) :
  not (mem_block_exists k m) -> memory_remove m k = m.
Proof.
  intros.
  unfold mem_block_exists, memory_remove in *.
  intros j.
  rewrite NP.F.remove_o.
  break_match; try reflexivity.
  subst.
  apply NP.F.not_find_in_iff in H.
  rewrite H.
  reflexivity.
Qed.

Global Instance Seq_DSH_pure
       {dop1 dop2 : DSHOperator}
       {y_p : PExpr}
       (P1: DSH_pure dop1 y_p)
       (P2: DSH_pure dop2 y_p)
  :
    DSH_pure (DSHSeq dop1 dop2) y_p.
Proof.
  split.
  -
    intros σ m0 m2 fuel M2 k.

    destruct fuel; [inversion M2 |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    rename m into m1, Heqo into M1.
    eq_to_equiv_hyp.

    inversion P1; clear P1 mem_write_safe;
      rename mem_stable into P1.
    apply P1 with (k:=k) in M1; clear P1.
    inversion P2; clear P2 mem_write_safe;
      rename mem_stable into P2.
    apply P2 with (k:=k) in M2; clear P2.
    rewrite M1, M2.
    reflexivity.
  -
    intros σ m0 m2 fuel M2 y_i Y.

    destruct fuel; [inversion M2 |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    rename m into m1, Heqo into M1.
    eq_to_equiv_hyp.

    inversion P1; clear P1 mem_stable;
      rename mem_write_safe into P1.
    eapply P1 with (y_i := y_i) in M1; [| assumption].
    inversion P2; clear P2 mem_stable;
      rename mem_write_safe into P2.
    eapply P2 with (y_i := y_i) in M2; [| assumption].
    clear - M1 M2.
    eapply memory_equiv_except_trans; eassumption.
Qed.

Global Instance MemMap2_DSH_pure
       {x0_p x1_p y_p : PExpr}
       {n : nat}
       {a : AExpr}
  :
    DSH_pure (DSHMemMap2 n x0_p x1_p y_p a) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    rewrite <-H; clear H m'.

    split; [apply mem_block_exists_memory_set | intros].
    apply mem_block_exists_memory_set_inv in H.
    destruct H; [assumption | subst].
    apply memory_is_set_is_Some.
    rewrite Heqo.
    reflexivity.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    cbv in H0.
    subst.

    unfold memory_equiv_except; intros.
    rewrite <-H; clear H m'.
    unfold memory_lookup, memory_set.
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Global Instance Alloc_DSH_pure
       {size : nat}
       {dop : DSHOperator}
       {y_p : PExpr}
       (P : DSH_pure dop (incrPVar 0 y_p))
  :
  DSH_pure (DSHAlloc size dop) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    rewrite <-H; clear H m'.

    inversion_clear P as [S T]; clear T.
    eq_to_equiv_hyp.
    apply S with (k:=k) in Heqo; clear S.
    destruct (Nat.eq_dec k (memory_next_key m)) as [EQ | NEQ].
    +
      subst.
      clear.
      split; intros.
      *
        contradict H.
        apply mem_block_exists_memory_next_key.
      *
        contradict H.
        apply mem_block_exists_memory_remove.
    +
      split; intros.
      *
        rewrite <-mem_block_exists_memory_remove_neq by assumption.
        apply Heqo.
        apply mem_block_exists_memory_set.
        assumption.
      *
        enough (T : mem_block_exists k (memory_set m (memory_next_key m) mem_empty))
          by (apply mem_block_exists_memory_set_inv in T; destruct T; congruence).
        apply Heqo.
        erewrite mem_block_exists_memory_remove_neq.
        eassumption.
        assumption.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    unfold memory_equiv_except.
    intros.
    rewrite <-H; clear H m'.

    inversion_clear P as [T S]; clear T.
    eq_to_equiv_hyp.
    apply S with (y_i:=y_i) in Heqo; clear S;
      [| rewrite evalPexp_incrPVar; assumption].

    unfold memory_equiv_except in Heqo.
    specialize (Heqo k H1).
    destruct (Nat.eq_dec k (memory_next_key m)) as [EQ | NEQ].
    +
      subst.
      unfold memory_lookup, memory_remove, memory_set in *.
      rewrite NP.F.add_eq_o in Heqo by reflexivity.
      rewrite NP.F.remove_eq_o by reflexivity.
      pose proof memory_lookup_memory_next_key_is_None m.
      apply is_None_def in H.
      rewrite <-H.
      reflexivity.
    +
      unfold memory_lookup, memory_remove, memory_set in *.
      rewrite NP.F.add_neq_o in Heqo by congruence.
      rewrite NP.F.remove_neq_o by congruence.
      assumption.
Qed.

Global Instance MemInit_DSH_pure
       {size : nat}
       {y_p : PExpr}
       {init : CarrierA}
  :
    DSH_pure (DSHMemInit size y_p init) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    rewrite <-H; clear H m'.

    split; [apply mem_block_exists_memory_set | intros].
    apply mem_block_exists_memory_set_inv in H.
    destruct H; [assumption | subst].
    apply memory_is_set_is_Some.
    rewrite Heqo.
    reflexivity.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    cbv in H0.
    subst.

    unfold memory_equiv_except; intros.
    rewrite <-H; clear H m'.
    unfold memory_lookup, memory_set.
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Lemma memory_lookup_memory_set_eq (m : memory) (k k' : mem_block_id) (mb : mem_block) :
  k = k' ->
  memory_lookup (memory_set m k mb) k' ≡ Some mb.
Proof.
  intros.
  rewrite H; clear H.
  unfold memory_lookup, memory_set.
  rewrite NP.F.add_eq_o by reflexivity.
  reflexivity.
Qed.

Lemma memory_lookup_memory_set_neq (m : memory) (k k' : mem_block_id) (mb : mem_block) :
  k <> k' ->
  memory_lookup (memory_set m k mb) k' ≡ memory_lookup m k'.
Proof.
  intros.
  unfold memory_lookup, memory_set.
  rewrite NP.F.add_neq_o by assumption.
  reflexivity.
Qed.

Lemma memory_lookup_memory_remove_eq (m : memory) (k k' : mem_block_id) :
  k = k' ->
  memory_lookup (memory_remove m k) k' = None.
Proof.
  intros.
  rewrite <-H; clear H.
  unfold memory_lookup, memory_remove.
  rewrite NP.F.remove_eq_o; reflexivity.
Qed.

Lemma memory_lookup_memory_remove_neq (m : memory) (k k' : mem_block_id) :
  k <> k' ->
  memory_lookup (memory_remove m k) k' = memory_lookup m k'.
Proof.
  intros.
  unfold memory_lookup, memory_remove.
  rewrite NP.F.remove_neq_o.
  reflexivity.
  assumption.
Qed.

Ltac eq_to_equiv := err_eq_to_equiv_hyp; eq_to_equiv_hyp.

Ltac simplify_memory_hyp :=
  match goal with
  | [ H : memory_lookup (memory_set _ _ _) _ = _ |- _ ] =>
    try rewrite memory_lookup_memory_set_neq in H by congruence;
    try rewrite memory_lookup_memory_set_eq in H by congruence
  | [H : memory_lookup (memory_remove _ _) _ = _ |- _ ] =>
    try rewrite memory_lookup_memory_remove_neq in H by congruence;
    try rewrite memory_lookup_memory_remove_eq in H by congruence
  | [H : memory_set (memory_set _ _ _) _ _ = _ |- _] =>
    try rewrite memory_set_overwrite in H by congruence
  | [H : memory_remove (memory_set _ _ _) _ = _ |- _] =>
    try rewrite memory_remove_memory_set_eq in H by congruence
  end.

Global Instance NOP_DSH_pure
       {y_p : PExpr}
  :
    DSH_pure DSHNop y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    some_inv; inl_inr_inv.
    rewrite H.
    reflexivity.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    some_inv; inl_inr_inv.
    intros k NE.
    rewrite H.
    reflexivity.
Qed.

Global Instance IReduction_DSH_pure
       {no nn : nat}
       {y_p y_p'': PExpr}
       {init : CarrierA}
       {rr : DSHOperator}
       {df : AExpr}
       (Y: y_p'' ≡ incrPVar 0 (incrPVar 0 y_p))
       (P: DSH_pure rr (PVar 1))
  :
    DSH_pure
      (DSHSeq
         (DSHMemInit no y_p init)
         (DSHAlloc no
                   (DSHLoop nn
                            (DSHSeq
                               rr
                               (DSHMemMap2 no y_p''
                                           (PVar 1)
                                           y_p''
                                           df)))))
      y_p.
Proof.
  subst.
  apply Seq_DSH_pure.
  apply MemInit_DSH_pure.

  (* we don't care what operator it is so long as it's pure *)
  remember (DSHMemMap2 no (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
                (incrPVar 0 (incrPVar 0 y_p)) df)
    as dop.
  assert (DSH_pure dop (incrPVar 0 (incrPVar 0 y_p)))
    by (subst; apply MemMap2_DSH_pure).
  clear Heqdop.

  constructor; intros.
  -
    generalize dependent m'.
    induction nn.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in *.
      some_inv; inl_inr_inv.
      eq_to_equiv; simplify_memory_hyp.
      rewrite memory_remove_nonexistent_key in H0
        by (apply mem_block_exists_memory_next_key).
      rewrite H0.
      reflexivity.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in H0.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      rename m1 into loop_m, m0 into step_m.
      specialize (IHnn (memory_remove loop_m (memory_next_key m))).
      full_autospecialize IHnn.
      *
        remember (S fuel) as t; cbn; subst t. (* poor man's partial unfold *)
        apply evalDSHOperator_fuel_ge with (f' := S fuel) in Heqo0;
          [| constructor; reflexivity].
        rewrite Heqo0.
        reflexivity.
      *
        rewrite <-H0.
        clear Heqo0 H0 m'.
        destruct fuel; cbn in *; try some_none.
        repeat break_match;
          try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
        subst.
        rename m0 into rr_m.
        eq_to_equiv.
        inversion_clear P as [S T]; clear T.
        apply S with (k:=k) in Heqo0; clear S.
        inversion_clear H as [S T]; clear T.
        apply S with (k:=k) in Heqo; clear S.
        rewrite IHnn.
        destruct (Nat.eq_dec k (memory_next_key m)).
        --
          rewrite <-e in *.
          pose proof mem_block_exists_memory_remove k loop_m.
          pose proof mem_block_exists_memory_remove k step_m.
          intuition.
        --
          repeat rewrite <-mem_block_exists_memory_remove_neq by congruence.
          rewrite Heqo0, Heqo.
          reflexivity.
  -
    generalize dependent m'.
    induction nn.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in *.
      some_inv; inl_inr_inv.
      eq_to_equiv; simplify_memory_hyp.
      rewrite memory_remove_nonexistent_key in H0
        by (apply mem_block_exists_memory_next_key).
      unfold memory_equiv_except.
      intros.
      rewrite H0.
      reflexivity.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in H0.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      rename m1 into loop_m, m0 into step_m.
      specialize (IHnn (memory_remove loop_m (memory_next_key m))).
      full_autospecialize IHnn.
      *
        remember (S fuel) as t; cbn; subst t. (* poor man's partial unfold *)
        apply evalDSHOperator_fuel_ge with (f' := S fuel) in Heqo0;
          [| constructor; reflexivity].
        rewrite Heqo0.
        reflexivity.
      *
        unfold memory_equiv_except.
        intros.
        rewrite <-H0.
        clear Heqo0 H0 m'.
        destruct fuel; cbn in Heqo; try some_none.
        repeat break_match;
          try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
        subst.
        rename m0 into rr_m.
        eq_to_equiv.
        inversion_clear P as [T S]; clear T.
        apply S with (y_i:=memory_next_key m) in Heqo0; clear S; [| reflexivity].
        inversion_clear H as [T S]; clear T.
        apply S with (y_i:=y_i) in Heqo; clear S;
          [| repeat rewrite evalPexp_incrPVar; assumption].
        rewrite IHnn by assumption.
        destruct (Nat.eq_dec k (memory_next_key m)).
        --
          rewrite <-e in *.
          repeat rewrite memory_lookup_memory_remove_eq by reflexivity.
          reflexivity.
        --
          repeat rewrite memory_lookup_memory_remove_neq by congruence.
          rewrite Heqo0 by congruence.
          rewrite Heqo by congruence.
          reflexivity.
Qed.

Instance MSH_DSH_compat_R_proper {σ : evalContext} {mb : mem_block} {y_p : PExpr} :
  Proper ((=) ==> (=) ==> iff)
             (fun md m' => err_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md)
                              (lookup_Pexp σ m' y_p)).
Proof.
  intros md1 md2 MDE m1' m2' ME.
  assert (P : forall md, Proper ((=) ==> iff)
                       (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv mb ma md)).
  {
    intros md ma1 ma2 MAE.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    split; intros.
    -
      specialize (H i).
      inversion H;
        [constructor 1 | constructor 2].
      assumption.
      rewrite <-MAE.
      assumption.
      assumption.
      rewrite <-MAE.
      assumption.
    -
      specialize (H i).
      inversion H;
        [constructor 1 | constructor 2].
      assumption.
      rewrite MAE.
      assumption.
      assumption.
      rewrite MAE.
      assumption.
  }
  split; intros.
  -
    inversion H; clear H.
    eq_to_equiv.
    rewrite ME in H0.
    rewrite <-H0.
    constructor.
    rewrite <-MDE.
    assumption.
  -
    inversion H; clear H.
    eq_to_equiv.
    rewrite <-ME in H0.
    rewrite <-H0.
    constructor.
    rewrite MDE.
    assumption.
Qed.

Lemma memory_lookup_not_next_equiv (m : memory) (k : mem_block_id) (mb : mem_block) :
  memory_lookup m k = Some mb -> k <> memory_next_key m.
Proof.
  intros S C.
  subst.
  pose proof memory_lookup_memory_next_key_is_None m.
  unfold is_None in H.
  break_match.
  trivial.
  some_none.
Qed.

Global Instance IReduction_MSH_DSH_compat_O
       {i o : nat}
       {init : CarrierA}
       {dot : CarrierA -> CarrierA -> CarrierA}
       {pdot : Proper ((=) ==> (=) ==> (=)) dot}
       {op_family : @MSHOperatorFamily i o 0}
       {df : AExpr}
       {x_p y_p : PExpr}
       {rr : DSHOperator}
       {σ : evalContext}
       {m : memory}
       {DP}
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i o 0 init dot pdot op_family)
      DSHNop
      σ m x_p y_p DP.
Proof.
  constructor.
  intros.
  cbn.
  constructor.
  break_match.
  all: unfold lookup_Pexp in H0.
  all: rewrite Heqs in H0.
  all: cbn in H0.
  1: inl_inr.
  destruct memory_lookup_err; try inl_inr; inl_inr_inv.
  repeat constructor.
  rewrite H0.
  reflexivity.
Qed.

Lemma memory_next_key_struct
      (m m' : memory):
  (forall k, mem_block_exists k m <-> mem_block_exists k m') ->
       memory_next_key m = memory_next_key m'.
Proof.
  intros H.
  unfold memory_next_key.
  destruct (NS.max_elt (memory_keys_set m)) as [k1|] eqn:H1;
    destruct (NS.max_elt (memory_keys_set m')) as [k2|] eqn:H2.
  -
    f_equiv.
    cut(¬ k1 < k2 /\ ¬ k2 < k1);[lia|].
    split.
    +
      apply (NS.max_elt_2 H1), memory_keys_set_In, H.
      apply NS.max_elt_1, memory_keys_set_In in H2.
      apply H2.
    +
      apply (NS.max_elt_2 H2), memory_keys_set_In, H.
      apply NS.max_elt_1, memory_keys_set_In in H1.
      apply H1.
  - exfalso.
    apply NS.max_elt_1 in H1.
    apply NS.max_elt_3 in H2.
    apply memory_keys_set_In in H1.
    apply H in H1.
    apply memory_keys_set_In in H1.
    apply  NSP.empty_is_empty_1 in H2.
    rewrite H2 in H1.
    apply NSP.FM.empty_iff in H1.
    tauto.
  - exfalso.
    apply NS.max_elt_1 in H2.
    apply NS.max_elt_3 in H1.
    apply memory_keys_set_In in H2.
    apply H in H2.
    apply memory_keys_set_In in H2.
    apply  NSP.empty_is_empty_1 in H1.
    rewrite H1 in H2.
    apply NSP.FM.empty_iff in H2.
    tauto.
  -
    reflexivity.
Qed.

Lemma memory_next_key_override (k : mem_block_id) (m : memory) (mb : mem_block) :
  mem_block_exists k m ->
  memory_next_key (memory_set m k mb) = memory_next_key m.
Proof.
  intros H.
  apply memory_next_key_struct.
  intros k0.
  split; intros.
  -
    destruct (Nat.eq_dec k k0).
    +
      subst k0.
      assumption.
    +
      apply mem_block_exists_memory_set_neq in H0; auto.
  -
    apply mem_block_exists_memory_set.
    assumption.
Qed.

Global Instance memory_set_proper :
  Proper ((=) ==> (=) ==> (=)) memory_set.
Proof.
  intros mem1 mem2 ME k k' KE mb1 mb2 BE.
  cbv in KE; subst k'.
  intros j.
  unfold memory_set.
  destruct (Nat.eq_dec j k).
  repeat rewrite NP.F.add_eq_o by congruence; rewrite BE; reflexivity.
  repeat rewrite NP.F.add_neq_o by congruence; apply ME.
Qed.

Global Instance evalIUnCType_mem_proper :
  Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalIUnCType.
Proof.
  intros mem1 mem2 ME σ' σ ΣE f' f FE i' i IE a' a AE.
  unfold evalIUnCType.
  enough (T : DSHCTypeVal a' :: DSHnatVal i' :: σ' = DSHCTypeVal a :: DSHnatVal i :: σ)
         by (rewrite T, ME, FE; reflexivity).
  f_equiv.
  constructor 2.
  assumption.
  rewrite IE, ΣE.
  reflexivity.
Qed.

Global Instance evalDSHIMap_mem_proper :
  Proper ((=) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (=)) evalDSHIMap.
Proof.
  intros mem1 mem2 ME n' n NE f' f FE σ' σ Σ xb' xb XBE yb' yb YBE.
  subst.
  generalize dependent yb.
  induction n; [reflexivity |].
  intros.
  cbn.
  repeat break_match; try (repeat constructor; fail).
  all: eq_to_equiv.
  all: rewrite ME in *.
  all: rewrite Heqs0 in Heqs1; try inl_inr; inl_inr_inv.
  rewrite Heqs1.
  apply IHn.
Qed.

Global Instance evalIBinCType_proper :
  Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalIBinCType.
Proof.
  intros mem1 mem2 ME σ' σ ΣE f' f FE i' i IE a' a AE b' b BE.
  unfold evalIBinCType.
  enough (T : DSHCTypeVal b' :: DSHCTypeVal a' :: DSHnatVal i' :: σ' =
              DSHCTypeVal b  :: DSHCTypeVal a  :: DSHnatVal i  :: σ)
    by (rewrite ME, T, FE; reflexivity).
  f_equiv.
  constructor; assumption.
  f_equiv.
  constructor; assumption.
  rewrite IE, ΣE.
  reflexivity.
Qed.

Global Instance evalDSHBinOp_mem_proper :
  Proper ((=) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (=)) evalDSHBinOp.
Proof.
  intros mem1 mem2 ME n' n NE off' off OFFE f' f FE σ' σ ΣE x' x XE y' y YE.
  subst.
  generalize dependent y.
  induction n; [reflexivity |].
  intros.
  cbn.
  repeat break_match; try (repeat constructor; fail).
  all: eq_to_equiv; rewrite ME in *; try some_none.
  all: rewrite Heqs1 in Heqs2; try inl_inr; inl_inr_inv.
  rewrite Heqs2.
  apply IHn.
Qed.

Lemma mem_lookup_err_inl_None:
  ∀ (msg msg' : string) (mb : mem_block) (n : NM.key),
    mem_lookup_err msg n mb = inl msg' ↔ mem_lookup n mb = None.
Proof.
  intros.
  unfold mem_lookup_err, trywith.
  break_match.
  split; intros C; inversion C.
  split; intros C; constructor.
Qed.
  
Lemma mem_lookup_err_inr_Some:
  ∀ (msg : string) (mb : mem_block) (n : NM.key) (a : CarrierA),
    mem_lookup_err msg n mb = inr a ↔ mem_lookup n mb = Some a.
Proof.
  intros.
  unfold mem_lookup_err, trywith.
  break_match.
  split; intros H; inversion H; rewrite H2; reflexivity.
  split; intros C; inversion C.
Qed.

Global Instance evalDSHMap2_proper :
  Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalDSHMap2.
Proof.
  intros m1 m2 M n1 n2 N df1 df2 DF σ1 σ2 Σ l1 l2 L r1 r2 R y1 y2 Y.
  cbv in N; subst; rename n2 into n.
  generalize dependent y2.
  generalize dependent y1.
  induction n.
  -
    intros.
    cbn.
    rewrite Y.
    reflexivity.
  -
    intros.
    cbn [evalDSHMap2].
    generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys r1)%string.
    generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys r2)%string.
    generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys l1)%string.
    generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys l2)%string.
    intros.
    cbn.
    assert (mem_lookup_err s0 n l1 = mem_lookup_err s n l2).
    {
      clear - L.
      unfold mem_lookup_err, trywith.
      repeat break_match; try constructor.
      all: eq_to_equiv.
      all: rewrite L in *.
      all: rewrite Heqo in Heqo0; try some_none.
      some_inv.
      assumption.
    }
    assert (mem_lookup_err s2 n r1 = mem_lookup_err s1 n r2).
    {
      clear - R.
      unfold mem_lookup_err, trywith.
      repeat break_match; try constructor.
      all: eq_to_equiv.
      all: rewrite R in *.
      all: rewrite Heqo in Heqo0; try some_none.
      some_inv.
      assumption.
    }
    repeat break_match; try inl_inr; repeat inl_inr_inv; try constructor.
    +
      eq_to_equiv.
      rewrite H, H0, DF, M, Σ in Heqs1.
      inl_inr.
    +
      eq_to_equiv.
      rewrite H, H0, DF, M, Σ in Heqs1.
      inl_inr.
    +
      apply IHn.
      eq_to_equiv.
      rewrite H, H0, DF, M, Σ in Heqs1.
      rewrite Heqs1 in Heqs5.
      inl_inr_inv.
      rewrite Heqs5, Y.
      reflexivity.
Qed.

Global Instance evalDSHOperator_mem_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (≡) ==> (=)) evalDSHOperator.
Proof.
  intros σ' σ ΣE dop' dop DE mem1 mem2 ME fuel' fuel FE.
  subst.

  generalize dependent mem2.
  generalize dependent mem1.
  generalize dependent fuel.
  generalize dependent σ.
  induction dop.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat f_equiv.
    assumption.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat (break_match; try (repeat constructor; fail)).
    all: memory_lookup_err_to_option.
    all: eq_to_equiv; rewrite ME in *; try some_none.
    all: rewrite Heqs1 in Heqs6; some_inv.
    all: rewrite Heqs6 in Heqs5.
    all: rewrite Heqs5 in Heqs8.
    all: try inl_inr; inl_inr_inv.
    rewrite Heqs8.
    rewrite Heqs2 in Heqs7; some_inv.
    rewrite Heqs7.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat (break_match; try (repeat constructor; fail)).
    all: memory_lookup_err_to_option.
    all: eq_to_equiv; rewrite ME in *; try some_none.
    all: rewrite Heqs1 in Heqs4; some_inv; rewrite Heqs4 in *.
    all: rewrite Heqs2 in Heqs5; some_inv; rewrite Heqs5 in *.
    all: rewrite Heqs3 in Heqs6; try inl_inr; inl_inr_inv.
    do 2 f_equiv.
    rewrite Heqs6.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat (break_match; try (repeat constructor; fail)).
    all: memory_lookup_err_to_option.
    all: eq_to_equiv; rewrite ME in *; try some_none.
    all: rewrite Heqs1 in Heqs4; some_inv; rewrite Heqs4 in *.
    all: rewrite Heqs2 in Heqs5; some_inv; rewrite Heqs5 in *.
    all: rewrite Heqs3 in Heqs6; try inl_inr; inl_inr_inv.
    do 2 f_equiv.
    rewrite Heqs6.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat (break_match; try (repeat constructor; fail)).
    all: memory_lookup_err_to_option.
    all: eq_to_equiv; rewrite ME in *; try some_none.
    all: rewrite Heqs2 in Heqs6; some_inv; rewrite Heqs6 in *.
    all: rewrite Heqs3 in Heqs7; some_inv; rewrite Heqs7 in *.
    all: rewrite Heqs4 in Heqs8; some_inv; rewrite Heqs8 in *.
    all: rewrite Heqs5 in Heqs9; try inl_inr; inl_inr_inv.
    do 2 f_equiv.
    rewrite Heqs9.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat (break_match; try (repeat constructor; fail)).
    all: unfold NatAsNT.MNatAsNT.to_nat in *.
    all: memory_lookup_err_to_option.
    all: eq_to_equiv; rewrite ME in *; try some_none.
    all: rewrite Heqs1 in Heqs7; some_inv; rewrite Heqs7 in *.
    all: rewrite Heqs2 in Heqs8; some_inv; rewrite Heqs8 in *.
    all: rewrite Heqs6 in Heqs9; try inl_inr; inl_inr_inv.
    do 2 f_equiv.
    rewrite Heqs9.
    reflexivity.
  -
    intros.

    generalize dependent fuel.
    induction n.
    +
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      rewrite ME.
      reflexivity.
    +
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      specialize (IHn fuel).
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      repeat constructor.
      apply IHdop.
      assumption.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    replace (memory_next_key mem1) with (memory_next_key mem2).
    2: {
      apply memory_next_key_struct.
      intros.
      repeat rewrite memory_is_set_is_Some.
      assert (memory_lookup mem1 k = memory_lookup mem2 k) by apply ME.
      unfold is_Some.
      repeat break_match; try some_none; intuition.
    }

    assert (evalDSHOperator (DSHPtrVal (memory_next_key mem2) size :: σ) dop
                            (memory_set mem1 (memory_next_key mem2) mem_empty) fuel =
            evalDSHOperator (DSHPtrVal (memory_next_key mem2) size :: σ) dop
                            (memory_set mem2 (memory_next_key mem2) mem_empty) fuel)
      by (apply IHdop; rewrite ME; reflexivity).

    destruct evalDSHOperator eqn:D1 at 1;
      destruct evalDSHOperator eqn:D2 at 1;
      rewrite D1, D2 in *; try some_none; some_inv.
    repeat break_match; try inl_inr. 
    repeat constructor.
    do 2 f_equiv.
    inl_inr_inv.
    rewrite H.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat break_match; try (repeat constructor; fail).
    all: eq_to_equiv.
    all: memory_lookup_err_to_option.
    all: rewrite ME in *; try some_none.
    rewrite Heqs0 in Heqs1; some_inv.
    rewrite Heqs1.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    repeat break_match; try (repeat constructor; fail).
    all: eq_to_equiv.
    all: memory_lookup_err_to_option.
    all: rewrite ME in *; try some_none.
    rewrite Heqs1 in Heqs3; some_inv; rewrite Heqs3 in *.
    rewrite Heqs2 in Heqs4; some_inv; rewrite Heqs4 in *.
    reflexivity.
  -
    intros.
    destruct fuel; [reflexivity |].
    cbn.
    assert (evalDSHOperator σ dop1 mem1 fuel = evalDSHOperator σ dop1 mem2 fuel)
      by (apply IHdop1; assumption).
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    repeat constructor.
    apply IHdop2.
    assumption.
Qed.

Lemma lookup_Pexp_eval_lookup (σ : evalContext) (m : memory) (x : PExpr) (mb : mem_block) :
  lookup_Pexp σ m x = inr mb ->
  exists x_id, evalPexp σ x = inr x_id /\ memory_lookup m x_id = Some mb.
Proof.
  intros.
  unfold lookup_Pexp, memory_lookup_err, trywith in H.
  cbn in *.
  repeat break_match; try inl_inr; inl_inr_inv.
  exists m0.
  intuition.
  rewrite Heqo, H.
  reflexivity.
Qed.

Lemma evalDSHMap2_rest_preserved
      (x1 x2 y y' : mem_block)
      (m : memory)
      (df : AExpr)
      (σ : evalContext)
      (n : nat)
  :
    evalDSHMap2 m n df σ x1 x2 y = inr y' ->
    forall k, n <= k -> mem_lookup k y' = mem_lookup k y.
Proof.
  intros.

  generalize dependent k.
  generalize dependent y.
  induction n.
  -
    intros.
    cbn in *.
    inl_inr_inv.
    rewrite H.
    reflexivity.
  -
    intros.
    cbn [evalDSHMap2] in H.
    remember ("Error reading 1st arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x1)%string as t1;
      clear Heqt1.
    remember ("Error reading 2nd arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x2)%string as t2;
      clear Heqt2.
    cbn in *.
    repeat break_match; try inl_inr.
    rewrite IHn with (y := mem_add n c1 y); [| assumption | lia].
    unfold mem_lookup, mem_add.
    rewrite NP.F.add_neq_o by lia.
    reflexivity.
Qed.

Lemma evalDSHMap2_result
      (x1 x2 y y' : mem_block)
      (m : memory)
      (df : AExpr)
      (σ : evalContext)
      (n : nat)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (DF : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    evalDSHMap2 m n df σ x1 x2 y = inr y' ->
    forall k, k < n -> exists a1 a2,
        mem_lookup k x1 = Some a1 /\
        mem_lookup k x2 = Some a2 /\
        mem_lookup k y' = Some (dot a1 a2).
Proof.
  intros.

  generalize dependent k.
  generalize dependent y.
  induction n.
  -
    lia.
  -
    intros.
    cbn [evalDSHMap2] in H.
    remember ("Error reading 1st arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x1)%string as t1;
      clear Heqt1.
    remember ("Error reading 2nd arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x2)%string as t2;
      clear Heqt2.
    cbn in *.
    repeat break_match; try inl_inr.
    destruct (Nat.eq_dec k n).
    +
      subst; clear H0.
      exists c, c0.
      split; [| split].
      1,2: unfold mem_lookup_err, trywith in *.
      1,2: repeat break_match; try inl_inr; repeat inl_inr_inv.
      1,2: reflexivity.
      apply evalDSHMap2_rest_preserved with (k:=n) in H; [| reflexivity].
      rewrite H.
      unfold mem_lookup, mem_add.
      rewrite NP.F.add_eq_o by reflexivity.
      inversion_clear DF as [D].
      eq_to_equiv.
      rewrite D in Heqs1.
      inl_inr_inv.
      rewrite Heqs1.
      reflexivity.
    +
      eapply IHn.
      eassumption.
      lia.
Qed.

Lemma MemMap2_rest_preserved
      (o : nat)
      (σ : evalContext)
      (m rm : memory)
      (x1_p x2_p y_p : PExpr)
      (df : AExpr)
      (y_m y_rm : mem_block)
      (Y_M : lookup_Pexp σ m y_p = inr y_m)
      (Y_RM : lookup_Pexp σ rm y_p = inr y_rm)
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr rm) ->
    ∀ k : nat, o <= k → mem_lookup k y_rm = mem_lookup k y_m.
Proof.
  intros.
  cbn in H.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  memory_lookup_err_to_option.
  rename m0 into x1_id, m1 into x2_id, m2 into y_id.
  rename m3 into x1_m, m4 into x2_m, m5 into y_m'.
  unfold lookup_Pexp, memory_lookup_err in *.
  rewrite Heqs1 in *.
  cbn in *.
  rewrite Heqs4 in Y_M.
  rewrite <-H in *.
  rewrite memory_lookup_memory_set_eq in * by reflexivity.
  cbn in *.
  repeat inl_inr_inv.
  eq_to_equiv.
  rewrite Y_M, Y_RM in *; clear Y_M Y_RM.
  eapply evalDSHMap2_rest_preserved in Heqs5; [| eassumption].
  assumption.
Qed.

Lemma MemMap2_result_fill
      (o : nat)
      (σ : evalContext)
      (m rm : memory)
      (x1_p x2_p y_p : PExpr)
      (df : AExpr)
      (y_rm : mem_block)
      (Y_RM : lookup_Pexp σ rm y_p = inr y_rm)
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr rm) ->
    ∀ k, k < o → mem_in k y_rm.
Proof.
  intros.
  cbn in H.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  memory_lookup_err_to_option.
  rename m0 into x1_id, m1 into x2_id, m2 into y_id.
  rename m3 into x1_m, m4 into x2_m, m5 into y_m'.
  unfold lookup_Pexp, memory_lookup_err in Y_RM.
  rewrite Heqs1 in Y_RM.
  cbn in Y_RM.
  rewrite <-H in Y_RM.
  rewrite memory_lookup_memory_set_eq in Y_RM by reflexivity.
  cbn in Y_RM.
  inl_inr_inv.
  eq_to_equiv.
  rewrite Y_RM in *; clear Y_RM m6.
  clear - Heqs5 H0.
  rename Heqs5 into M, H0 into KO.

  generalize dependent k.
  generalize dependent y_m'.
  generalize dependent y_rm.
  induction o; [lia |].
  intros.
  cbn [evalDSHMap2] in M.
  remember ("Error reading 1st arg memory in evalDSHMap2 @" ++
    Misc.string_of_nat o ++ " in " ++ string_of_mem_block_keys x1_m)%string as t1;
    clear Heqt1.
  remember ("Error reading 2nd arg memory in evalDSHMap2 @" ++
    Misc.string_of_nat o ++ " in " ++ string_of_mem_block_keys x2_m)%string as t2;
    clear Heqt2.
  cbn in *.
  repeat break_match; try inl_inr.
  destruct (Nat.eq_dec k o).
  +
    subst; clear KO.
    apply evalDSHMap2_rest_preserved with (k:=o) in M; [| reflexivity].
    unfold mem_in, mem_lookup, mem_add in *.
    rewrite NP.F.add_eq_o in M by reflexivity.
    apply NP.F.in_find_iff.
    intros C.
    rewrite C in M.
    some_none.
  +
    eapply IHo.
    eassumption.
    lia.
Qed.

Lemma mem_in_mem_lookup (k : NM.key) (mb : mem_block) :
  mem_in k mb <-> is_Some (mem_lookup k mb).
Proof.
  unfold mem_in, mem_lookup.
  rewrite is_Some_ne_None, NP.F.in_find_iff.
  reflexivity.
Qed.

Lemma DSHMap2_succeeds 
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m : mem_block)
      (σ : evalContext)
      (m : memory)
      (df : AExpr)
      (o : nat)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (LY : lookup_Pexp σ m y_p = inr y_m)
      (D1 : forall k, k < o -> mem_in k x1_m)
      (D2 : forall k, k < o -> mem_in k x2_m)

      (dot : CarrierA -> CarrierA -> CarrierA)
      (DC : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    exists m', evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m').
Proof.
  apply lookup_Pexp_eval_lookup in LX1.
  destruct LX1 as [x1_id [X1_ID X1_M]].
  apply lookup_Pexp_eval_lookup in LX2.
  destruct LX2 as [x2_id [X2_ID X2_M]].
  apply lookup_Pexp_eval_lookup in LY.
  destruct LY as [y_id [Y_ID Y_M]].
  cbn.
  unfold memory_lookup_err, trywith.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: eq_to_equiv.
  all: rewrite X1_ID, X2_ID, Y_ID in *; clear X1_ID X2_ID Y_ID m0 m1 m2.
  all: rename Heqs into X1_ID, Heqs0 into X2_ID, Heqs1 into Y_ID.
  all: try some_none.
  all: subst.
  all: rewrite Heqo2, Heqo1, Heqo0 in *; repeat some_inv.
  all: rewrite X1_M, X2_M, Y_M in *; clear X1_M X2_M Y_M m3 m4 m5.
  all: rename Heqo2 into X1_M, Heqo1 into X2_M, Heqo0 into Y_M.
  all: rename Heqs5 into M.
  - (* evalDSHMap2 fails *)
    exfalso.
    contradict M; generalize s; apply is_OK_neq_inl.

    clear Y_M.
    generalize dependent y_m.
    induction o.
    +
      cbn [evalDSHMap2].
      generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat 0 ++ " in " ++ string_of_mem_block_keys x2_m)%string.
      generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat 0 ++ " in " ++ string_of_mem_block_keys x1_m)%string.
      intros.
      cbn.
      constructor.
    +
      autospecialize IHo; [intros; apply D1; lia |].
      autospecialize IHo; [intros; apply D2; lia |].
      cbn [evalDSHMap2].
      generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat o ++ " in " ++ string_of_mem_block_keys x1_m)%string.
      generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat o ++ " in " ++ string_of_mem_block_keys x2_m)%string.
      specialize (D1 o); autospecialize D1; [lia |].
      specialize (D2 o); autospecialize D2; [lia |].
      rewrite mem_in_mem_lookup in *.
      rewrite is_Some_def in D1, D2.
      destruct D1 as [x1_mb D1], D2 as [x2_mb D2].
      unfold mem_lookup_err.
      rewrite D1, D2.
      intros.
      cbn.

      inversion_clear DC as [D].
      pose proof D x1_mb x2_mb as D'.
      break_match; try inl_inr.
      apply IHo.
  -
    eexists.
    reflexivity.
Qed.

Lemma mem_merge_with_def_empty_const
      (dot : CarrierA -> CarrierA -> CarrierA)
      (init : CarrierA)
      (mb : mem_block)
      (o : nat)
      (MD : forall k, k < o -> mem_in k mb)
  :
    forall k, k < o ->
    mem_lookup k (mem_merge_with_def dot init mem_empty mb) =
    mem_lookup k (mem_merge_with_def dot init (mem_const_block o init) mb).
Proof.
  intros.
  unfold mem_lookup, mem_merge_with_def.
  repeat rewrite NP.F.map2_1bis by reflexivity.
  rewrite mem_const_block_find by assumption.
  cbn.
  break_match; try reflexivity.
  exfalso.
  specialize (MD k H).
  apply mem_in_mem_lookup in MD.
  unfold mem_lookup in MD.
  rewrite Heqo0 in MD.
  some_none.
Qed.

Definition mem_firstn (n : nat) (mb : mem_block) :=
  NP.filter_dom (elt:=CarrierA) (fun k => Nat.ltb k n) mb.

Lemma MemMap2_merge_with_def
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m y_m': mem_block)
      (σ : evalContext)
      (m m' : memory)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (PF : Proper ((=) ==> (=) ==> (=)) dot)
      (df : AExpr)
      (init : CarrierA)
      (o : nat)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (LY : lookup_Pexp σ m y_p = inr y_m)

      (DC : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m') ->
    lookup_Pexp σ m' y_p = inr y_m' ->
    forall k, k < o -> mem_lookup k y_m' =
                 mem_lookup k (mem_merge_with_def dot init x1_m x2_m).
Proof.
  apply lookup_Pexp_eval_lookup in LX1.
  destruct LX1 as [x1_id [X1_ID X1_M]].
  apply lookup_Pexp_eval_lookup in LX2.
  destruct LX2 as [x2_id [X2_ID X2_M]].
  apply lookup_Pexp_eval_lookup in LY.
  destruct LY as [y_id [Y_ID Y_M]].
  cbn [evalDSHOperator estimateFuel].
  remember evalDSHMap2 as t1; remember mem_lookup as t2;
    cbn; subst t1 t2. (* poor man's selective cbv *)

  unfold memory_lookup_err, trywith.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: eq_to_equiv.
  all: rewrite X1_ID, X2_ID, Y_ID in *; clear X1_ID X2_ID Y_ID m0 m1 m2.
  all: rename Heqs into X1_ID, Heqs0 into X2_ID, Heqs1 into Y_ID.
  all: try some_none.
  all: intros; try some_none; repeat some_inv; try inl_inr; inl_inr_inv.
  all: inversion H3; clear H3.
  subst.
  rewrite Heqo3, Heqo2, Heqo1 in *; repeat some_inv.
  rewrite H7 in *; clear H7 m7.
  rewrite X1_M, X2_M, Y_M in *; clear X1_M X2_M Y_M m3 m4 m5.
  rename Heqo3 into X1_M, Heqo2 into X2_M, Heqo1 into Y_M.
  rename Heqs5 into M.
  rewrite <-H in Heqo0.
  rewrite memory_lookup_memory_set_eq in Heqo0 by reflexivity.
  some_inv.
  rewrite Heqo0 in *; clear Heqo0 m6.
  
  apply evalDSHMap2_result with (k:=k) (dot:=dot) in M; try assumption.
  destruct M as [a1 [a2 [X1 [X2 Y]]]].
  unfold mem_lookup in Y.
  rewrite Y.
  unfold mem_lookup, mem_merge_with_def.
  repeat rewrite NP.F.map2_1bis by reflexivity.
  unfold mem_lookup in X1, X2.
  repeat break_match; try some_none; repeat some_inv.
  rewrite X1, X2.
  reflexivity.
Qed.

Lemma mem_firstn_def (k n : nat) (mb : mem_block) (a : CarrierA) :
  mem_lookup k (mem_firstn n mb) = Some a <-> k < n /\ mem_lookup k mb = Some a.
Proof.
  split; intros.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct NM.find eqn:F in H; try some_none; some_inv.
    apply NP.F.find_mapsto_iff, NP.filter_iff in F.
    2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
    destruct F.
    rewrite <-H; clear H.
    apply Nat.ltb_lt in H1.
    intuition.
    apply NM.find_1 in H0.
    rewrite H0; reflexivity.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct H as [H1 H2].
    destruct (NM.find (elt:=CarrierA) k
                      (NP.filter (λ (k0 : NM.key) (_ : CarrierA), k0 <? n) mb)) eqn:F.
    +
      apply NP.F.find_mapsto_iff, NP.filter_iff in F.
      2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      destruct F.
      apply NM.find_1 in H.
      rewrite H in H2.
      assumption.
    +
      destruct NM.find eqn:H in H2; try some_none; some_inv.
      contradict F.
      apply is_Some_ne_None, is_Some_def.
      eexists.
      apply NP.F.find_mapsto_iff, NP.filter_iff.
      1: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      split.
      2: apply Nat.ltb_lt; assumption.
      instantiate (1:=c).
      apply NP.F.find_mapsto_iff.
      assumption.
Qed.

Lemma mem_firstn_def_eq (k n : nat) (mb : mem_block) (a : CarrierA) :
  mem_lookup k (mem_firstn n mb) ≡ Some a <-> k < n /\ mem_lookup k mb ≡ Some a.
Proof.
  split; intros.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct NM.find eqn:F in H; try some_none; some_inv.
    apply NP.F.find_mapsto_iff, NP.filter_iff in F.
    2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
    destruct F.
    subst.
    apply Nat.ltb_lt in H0.
    intuition.
    apply NM.find_1.
    assumption.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct H as [H1 H2].
    destruct (NM.find (elt:=CarrierA) k
                      (NP.filter (λ (k0 : NM.key) (_ : CarrierA), k0 <? n) mb)) eqn:F.
    +
      apply NP.F.find_mapsto_iff, NP.filter_iff in F.
      2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      destruct F.
      apply NM.find_1 in H.
      rewrite H in H2.
      assumption.
    +
      destruct NM.find eqn:H in H2; try some_none; some_inv.
      subst.
      contradict F.
      apply is_Some_ne_None, is_Some_def.
      eexists.
      apply NP.F.find_mapsto_iff, NP.filter_iff.
      1: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      split.
      2: apply Nat.ltb_lt; assumption.
      eapply NP.F.find_mapsto_iff.
      eassumption.
Qed.

Lemma mem_firstn_lookup (k n : nat) (mb : mem_block) :
  k < n ->
  mem_lookup k (mem_firstn n mb) ≡ mem_lookup k mb.
Proof.
  intros.
  destruct (mem_lookup k mb) eqn:L.
  -
    rewrite mem_firstn_def_eq.
    auto.
  -
    apply is_None_def.
    enough (not (is_Some (mem_lookup k (mem_firstn n mb))))
      by (unfold is_None, is_Some in *; break_match; auto).
    intros C.
    apply is_Some_def in C.
    destruct C as [mb' MB].
    apply mem_firstn_def_eq in MB.
    destruct MB; some_none.
Qed.

Lemma mem_firstn_lookup_oob (k n : nat) (mb : mem_block) :
  n <= k ->
  mem_lookup k (mem_firstn n mb) ≡ None.
Proof.
  intros.
  apply is_None_def.
  enough (not (is_Some (mem_lookup k (mem_firstn n mb))))
    by (unfold is_None, is_Some in *; break_match; auto).
  intros C.
  apply is_Some_def in C.
  destruct C as [mb' MB]; eq_to_equiv.
  apply mem_firstn_def in MB.
  lia.
Qed.

Lemma firstn_mem_const_block_union (o : nat) (init : CarrierA) (mb : mem_block) :
  mem_firstn o (mem_union (mem_const_block o init) mb) = mem_const_block o init.
Proof.
  intros k.
  destruct (le_lt_dec o k).
  -
    rewrite mem_firstn_lookup_oob, mem_const_block_find_oob by assumption.
    reflexivity.
  -
    rewrite mem_firstn_lookup by assumption.
    unfold mem_union, mem_lookup.
    rewrite NP.F.map2_1bis by reflexivity.
    rewrite mem_const_block_find; auto.
Qed.

Lemma MemMap2_merge_with_def_firstn
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m : mem_block)
      (σ : evalContext)
      (m : memory)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (PF : Proper ((=) ==> (=) ==> (=)) dot)
      (df : AExpr)
      (init : CarrierA)
      (o : nat)
      (y_id : nat)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (Y_ID : evalPexp σ y_p = inr y_id)
      (YID_M : memory_lookup m y_id = Some y_m)
      (D1 : forall k, k < o -> mem_in k x1_m)
      (D2 : forall k, k < o -> mem_in k x2_m)

      (DC : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df))
    = Some (inr
              (memory_set m y_id (mem_union (mem_merge_with_def dot init
                                                                (mem_firstn o x1_m)
                                                                (mem_firstn o x2_m))
                                            y_m))).
Proof.
  assert (exists m', evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                  (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m')).
  {
    eapply DSHMap2_succeeds; try eassumption.
    cbn.
    break_match; try inl_inr.
    inl_inr_inv.
    rewrite Y_ID.
    unfold memory_lookup_err.
    rewrite YID_M.
    cbn.
    reflexivity.
  }
  destruct H as [ma MA].
  rewrite MA.
  do 2 f_equiv.
  intros b_id.
  destruct (Nat.eq_dec b_id y_id).
  -
    subst b_id.
    unfold memory_set.
    rewrite NP.F.add_eq_o by reflexivity.
    assert (exists y_ma, lookup_Pexp σ ma y_p = inr y_ma).
    {
      apply equiv_Some_is_Some, memory_is_set_is_Some,
      (mem_stable _ _ _ _ MA), mem_block_exists_exists in YID_M.
      destruct YID_M as [y_ma H].
      exists y_ma.
      cbn.
      break_match; try inl_inr.
      apply memory_lookup_err_inr_Some.
      inv Y_ID.
      rewrite H2, H.
      reflexivity.
    }
    destruct H as [y_ma Y_MA].
    assert (T : NM.find (elt:=mem_block) y_id ma = Some y_ma).
    {
      unfold lookup_Pexp, memory_lookup_err, trywith, memory_lookup in Y_MA.
      cbn in Y_MA.
      repeat break_match; try inl_inr; repeat inl_inr_inv.
      rewrite <-Y_ID, <-Y_MA, Heqo0.
      reflexivity.
    }
    rewrite T; clear T.
    f_equiv.
    intros k.
    destruct (le_lt_dec o k).
    +
      unfold mem_union.
      rewrite NP.F.map2_1bis by reflexivity.
      assert (NM.find (elt:=CarrierA) k
                      (mem_merge_with_def dot init (mem_firstn o x1_m)
                                          (mem_firstn o x2_m)) = None).
      {
        unfold mem_merge_with_def.
        rewrite NP.F.map2_1bis by reflexivity.
        repeat rewrite mem_firstn_lookup_oob by assumption; reflexivity.
      }
      break_match; try some_none.
      clear Heqo0 H.
      eapply MemMap2_rest_preserved in MA; eauto.
      unfold lookup_Pexp, memory_lookup_err, trywith.
      cbn.
      repeat break_match; try inl_inr; repeat inl_inr_inv.
      all: eq_to_equiv.
      all: rewrite Y_ID in Heqo0.
      all: rewrite Heqo0 in YID_M.
      all: try some_none; some_inv.
      rewrite YID_M.
      reflexivity.
    +
      erewrite MemMap2_merge_with_def.
      7: eapply MA.
      all: try eassumption.
      2: {
        unfold lookup_Pexp, memory_lookup_err, trywith.
        cbn.
        repeat break_match; try some_none; try inl_inr.
        all: inl_inr_inv.
        all: eq_to_equiv.
        all: rewrite Y_ID in Heqo0.
        all: rewrite Heqo0 in YID_M.
        all: try some_none; some_inv.
        rewrite YID_M.
        reflexivity.
      }
      instantiate (1:=init).
      unfold mem_lookup, mem_union, mem_merge_with_def.
      repeat rewrite NP.F.map2_1bis by reflexivity.
      assert (exists k_x1m, mem_lookup k x1_m = Some k_x1m).
      {
        specialize (D1 k l).
        apply mem_in_mem_lookup in D1.
        apply is_Some_def in D1.
        destruct D1.
        exists x; rewrite H; reflexivity.
      }
      destruct H as [k_x1m K_X1M].
      assert (exists k_x2m, mem_lookup k x2_m = Some k_x2m).
      {
        specialize (D2 k l).
        apply mem_in_mem_lookup in D2.
        apply is_Some_def in D2.
        destruct D2.
        exists x; rewrite H; reflexivity.
      }
      destruct H as [k_x2m K_X2M].
      repeat rewrite mem_firstn_lookup by assumption.
      unfold mem_lookup in *.
      repeat break_match; try some_none.
  -
    unfold memory_set.
    rewrite NP.F.add_neq_o by congruence.
    eapply mem_write_safe in MA; [| eassumption].
    specialize (MA b_id n).
    rewrite MA.
    reflexivity.
Qed.


Global Instance eq_equiv_subrelation `{Equivalence A EqA} :
  subrelation (@eq A) (@equiv A EqA).
Proof.
  intros a b E.
  subst.
  reflexivity.
Qed.

Lemma is_OK_def {A : Type} {e : err A} :
  is_OK e <-> exists a, e ≡ inr a.
Proof.
  split; intros.
  -
    destruct e; inversion H.
    exists a.
    reflexivity.
  -
    destruct H.
    subst.
    constructor.
Qed.

Lemma memory_set_same (m : memory) (k : mem_block_id) (mb : mem_block) :
  memory_lookup m k = Some mb ->
  memory_set m k mb = m.
Proof.
  intros H k'.
  unfold memory_set, memory_lookup in *.
  destruct (Nat.eq_dec k k').
  -
    subst.
    rewrite NP.F.add_eq_o by congruence.
    auto.
  -
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Lemma evalDSHOperator_fuel_ge_equiv
      (f f' : nat)
      (σ : evalContext)
      (op : DSHOperator)
      (m : memory)
      (res : err memory)
  :
    f' ≥ f →
    evalDSHOperator σ op m f = Some res →
    evalDSHOperator σ op m f' = Some res.
Proof.
  intros.
  destruct (evalDSHOperator σ op m f) eqn:D,
           (evalDSHOperator σ op m f') eqn:D';
    try some_none.
  all: apply evalDSHOperator_fuel_ge with (f':=f') in D; [| assumption].
  all: rewrite D in D'; some_inv; subst.
  assumption.
  some_none.
Qed.

Lemma IReduction_Some_family_inv
      (i o n : nat)
      (op_family: @MSHOperatorFamily i o n)
      (init : CarrierA)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (pdot: Proper ((=) ==> (=) ==> (=)) dot)
      (mb : mem_block)
  :
    is_Some (mem_op (@MSHIReduction i o n init dot pdot op_family) mb) ->
    forall t, is_Some (mem_op (op_family t) mb).
Proof.
  intros.
  cbn in H.
  unfold Apply_mem_Family, get_family_mem_op in H.
  break_match; try some_none.
  clear H; rename Heqo0 into H.
  destruct t as [t tc].
  pose proof H as H1.
  apply ListSetoid.monadic_Lbuild_opt_length in H.
  apply ListSetoid.monadic_Lbuild_op_eq_Some with (i0:=t) (ic:=tc) in H1.
  assert ((t ↾ tc) ≡ mkFinNat tc) by reflexivity.
  rewrite H0; clear H0.
  rewrite <-H1; clear H1.
  clear - H tc.

  generalize dependent t.
  generalize dependent n.
  induction l.
  -
    intros.
    cbn in H; subst.
    inversion tc.
  -
    intros.
    destruct t; [reflexivity |].
    destruct n; [discriminate |].
    apply IHl with (n:=n).
    cbn in H; lia.
    lia.
Qed.

Lemma fold_left_rev_invariant
      {A : Type}
      (f : A -> A -> A)
      (init : A)
      (l : list A)
      (P : A -> Prop)
  :
    (forall a b, P a \/ P b -> P (f a b)) ->
    (exists a, P a /\ List.In a l) ->
    P (ListUtil.fold_left_rev f init l).
Proof.
  intros.
  destruct H0 as [x [Px XL]].
  induction l; [inversion XL |].
  cbn in *.
  destruct XL as [AX | XX]; subst; auto.
Qed.

Lemma mem_not_in_mem_lookup (k : NM.key) (mb : mem_block) :
  not (mem_in k mb) <-> is_None (mem_lookup k mb).
Proof.
  rewrite is_None_def.
  apply NP.F.not_find_in_iff.
Qed.

Lemma SHCOL_DSHCOL_mem_block_equiv_keys_union (ma mb md : mem_block) :
  SHCOL_DSHCOL_mem_block_equiv mb ma md ->
  forall k, mem_in k mb \/ mem_in k md <-> mem_in k ma.
Proof.
  intros.
  specialize (H k).
  inversion H.
  all: repeat rewrite mem_in_mem_lookup in *.
  all: repeat rewrite mem_not_in_mem_lookup in *.
  all: unfold is_None, is_Some in *.
  all: repeat break_match; try some_none.
  all: intuition.
Qed.

Lemma IReduction_MSH_step
      {i o n : nat}
      (mb : mem_block)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (pdot : Proper ((=) ==> (=) ==> (=)) dot)
      (init : CarrierA)
      (S_opf : @MSHOperatorFamily i o (S n))
  :
    let opf := shrink_m_op_family S_opf in
    let fn := mkFinNat (Nat.lt_succ_diag_r n) in
    mem_op (MSHIReduction init dot S_opf) mb =
    mb' <- mem_op (MSHIReduction init dot opf) mb ;;
    mbn <- mem_op (S_opf fn) mb ;;
    Some (mem_merge_with_def dot init mb' mbn).
Proof.
  simpl.
  unfold IReduction_mem.
  simpl.
  unfold Apply_mem_Family in *.
  repeat break_match;
    try discriminate; try reflexivity.
  all: repeat some_inv; subst.
  -
    rename l into S_lb, l0 into lb.

    (* poor man's apply to copy and avoid evars *)
    assert (S_LB : ∀ (j : nat) (jc : (j < S n)%mc),
               List.nth_error S_lb j ≡ get_family_mem_op S_opf j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).
    assert (LB : ∀ (j : nat) (jc : (j < n)%mc),
               List.nth_error lb j ≡ get_family_mem_op (shrink_m_op_family S_opf) j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).

    apply ListSetoid.monadic_Lbuild_opt_length in Heqo0; rename Heqo0 into S_L.
    apply ListSetoid.monadic_Lbuild_opt_length in Heqo3; rename Heqo3 into L.
    rename m0 into mbn, Heqo2 into MBN.

    unfold get_family_mem_op in *.
    assert (H : forall j, j < n -> List.nth_error lb j ≡ List.nth_error S_lb j)
      by (intros; erewrite S_LB, LB; reflexivity).
    Unshelve. 2: assumption.

    assert (N_MB : is_Some (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) mb)).
    {
      apply is_Some_ne_None.
      intro C.
      rewrite <-S_LB in C.
      apply List.nth_error_None in C.
      lia.
    }
    apply is_Some_def in N_MB.
    destruct N_MB as [n_mb N_MB].

    assert (H1 : S_lb ≡ lb ++ [n_mb]).
    {
      apply list_eq_nth;
        [rewrite List.app_length; cbn; lia |].
      intros k KC.
      (* extensionality *)
      enough (forall d, List.nth k S_lb d ≡ List.nth k (lb ++ [n_mb]) d)
        by (apply Logic.FunctionalExtensionality.functional_extensionality; assumption).
      rewrite S_L in KC.
      destruct (Nat.eq_dec k n).
      -
        subst k.
        intros.
        apply List_nth_nth_error.
        replace n with (0 + Datatypes.length lb).
        rewrite ListNth.nth_error_length.
        cbn.
        rewrite L.
        rewrite S_LB with (jc := (Nat.lt_succ_diag_r n)).
        rewrite <-N_MB.
        reflexivity.
      -
        assert (k < n) by lia; clear KC n0.
        intros.
        apply List_nth_nth_error.
        rewrite <-H by lia.
        rewrite List.nth_error_app1 by lia.
        reflexivity.
    }

    rewrite H1.
    rewrite List.fold_left_app.
    cbn.

    rewrite MBN in N_MB; some_inv.
    reflexivity.
  -
    rename l into S_lb, l0 into lb.

    (* poor man's apply to copy and avoid evars *)
    assert (S_LB : ∀ (j : nat) (jc : (j < S n)%mc),
               List.nth_error S_lb j ≡ get_family_mem_op S_opf j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).
    apply ListSetoid.monadic_Lbuild_opt_length in Heqo0; rename Heqo0 into S_L.

    assert (N_MB : is_Some (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) mb)).
    {
      apply is_Some_ne_None.
      intro C.
      unfold get_family_mem_op in *.
      rewrite <-S_LB in C.
      apply List.nth_error_None in C.
      lia.
    }

    rewrite Heqo2 in N_MB.
    some_none.
  -
    exfalso; clear Heqo1.

    pose proof Heqo0 as L; apply ListSetoid.monadic_Lbuild_opt_length in L.

    apply ListSetoid.monadic_Lbuild_op_eq_None in Heqo2.
    destruct Heqo2 as [k [KC N]].
    apply ListSetoid.monadic_Lbuild_op_eq_Some
      with (i0:=k) (ic:=le_S KC)
      in Heqo0.
    unfold get_family_mem_op, shrink_m_op_family in *.
    cbn in *.
    rewrite N in Heqo0.
    apply ListNth.nth_error_length_ge in Heqo0.
    assert (k < n) by assumption.
    lia.
  -
    exfalso.

    pose proof Heqo3 as S_L; apply ListSetoid.monadic_Lbuild_opt_length in S_L.

    apply ListSetoid.monadic_Lbuild_op_eq_None in Heqo0.
    destruct Heqo0 as [k [KC N]].
    destruct (Nat.eq_dec k n).
    +
      subst k.
      unfold get_family_mem_op in *.
      assert (KC ≡ (Nat.lt_succ_diag_r n)) by (apply lt_unique).
      rewrite <-H, N in Heqo2.
      some_none.
    +
      assert (k < n) by (assert (k < S n) by assumption; lia); clear n0.
      apply ListSetoid.monadic_Lbuild_op_eq_Some
        with (i0:=k) (ic:=H)
        in Heqo3.
      unfold get_family_mem_op, shrink_m_op_family in *.
      cbn in Heqo3.
      assert (le_S H ≡ KC) by (apply lt_unique).
      rewrite H0, N in Heqo3.
      apply ListNth.nth_error_length_ge in Heqo3.
      rewrite S_L in Heqo3.
      omega.
Qed.

Lemma MemInit_simpl
      (o : nat)
      (σ : evalContext)
      (m : memory)
      (dop : DSHOperator)
      (init : CarrierA)
      (y_p : PExpr)
      (y_id : mem_block_id)
      (y_m : mem_block)
      (Y_ID : evalPexp σ y_p = inr y_id)
      (YID_M : memory_lookup m y_id = Some y_m)
  :
  evalDSHOperator σ (DSHSeq (DSHMemInit o y_p init) dop) m
                  (estimateFuel (DSHSeq (DSHMemInit o y_p init) dop)) =
  evalDSHOperator σ dop (memory_set m y_id (mem_union (mem_const_block o init) y_m))
                  (estimateFuel dop).
Proof.
  cbn.
  pose proof estimateFuel_positive dop.
  repeat break_match; try nia.
  -
    cbn in Heqo0.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    memory_lookup_err_to_option.
    eq_to_equiv.
    rewrite Y_ID in Heqs2.
    some_none.
  -
    subst.
    cbn in Heqo0.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    memory_lookup_err_to_option.
    eq_to_equiv.
    rewrite Y_ID in *.
    rewrite Heqs0 in YID_M.
    some_inv.
    rewrite YID_M in *.
    reflexivity.
  -
    cbn in Heqo0.
    some_none.
Qed.

Lemma Alloc_Loop_step
      (o n : nat)
      (body : DSHOperator)
      (m loopN_m iterSN_m : memory)
      (σ : evalContext)
      (t_id : mem_block_id)
      (T_ID : t_id ≡ memory_next_key m)
      (LoopN : evalDSHOperator (DSHPtrVal t_id o :: σ) (DSHLoop n body)
                               (memory_set m t_id mem_empty)
                               (estimateFuel (DSHLoop n body))
               = Some (inr loopN_m))
      (IterSN : evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                body
                                loopN_m
                                (estimateFuel body) = Some (inr iterSN_m))
  :
    evalDSHOperator σ (DSHAlloc o (DSHLoop (S n) body)) m
                  (estimateFuel (DSHAlloc o (DSHLoop (S n) body))) = 
    Some (inr (memory_remove iterSN_m t_id)).
Proof.
  cbn.
  rewrite <-T_ID.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; cbn; nia).
  destruct (evalDSHOperator (DSHPtrVal t_id o :: σ) (DSHLoop n body)
                            (memory_set m t_id mem_empty) (estimateFuel (DSHLoop n body)))
           as [t|] eqn:LoopN'; [destruct t as [|loopN_m'] |];
    try some_none; some_inv; try inl_inr; inl_inr_inv.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; cbn; nia).
  rewrite <-LoopN in *; clear LoopN loopN_m.
  repeat break_match; try some_none; some_inv; try inl_inr; inl_inr_inv.
  rewrite IterSN.
  reflexivity.
Qed.

Lemma Alloc_Loop_error1
      (o n : nat)
      (body : DSHOperator)
      (m : memory)
      (σ : evalContext)
      (t_id : mem_block_id)
      (T_ID : t_id ≡ memory_next_key m)
      (msg : string)
      (LoopN : evalDSHOperator (DSHPtrVal t_id o :: σ) (DSHLoop n body)
                               (memory_set m t_id mem_empty)
                               (estimateFuel (DSHLoop n body))
               = Some (inl msg))
  :
    evalDSHOperator σ (DSHAlloc o (DSHLoop (S n) body)) m
                  (estimateFuel (DSHAlloc o (DSHLoop (S n) body))) = 
    Some (inl msg).
Proof.
  cbn.
  rewrite <-T_ID.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; cbn; lia).
  destruct (evalDSHOperator (DSHPtrVal t_id o :: σ) (DSHLoop n body)
                            (memory_set m t_id mem_empty) (estimateFuel (DSHLoop n body)))
           as [t|] eqn:LoopN'; [destruct t as [|loopN_m'] |].
  - repeat constructor.
  - some_inv; inl_inr.
  - some_none.
Qed.

Lemma Alloc_Loop_error2
      (o n : nat)
      (body : DSHOperator)
      (m loopN_m : memory)
      (σ : evalContext)
      (t_id : mem_block_id)
      (T_ID : t_id ≡ memory_next_key m)
      (msg : string)
      (LoopN : evalDSHOperator (DSHPtrVal t_id o :: σ) (DSHLoop n body)
                               (memory_set m t_id mem_empty)
                               (estimateFuel (DSHLoop n body))
               = Some (inr loopN_m))
      (IterSN : evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                body
                                loopN_m
                                (estimateFuel body) = Some (inl msg))
  :
    evalDSHOperator σ (DSHAlloc o (DSHLoop (S n) body)) m
                  (estimateFuel (DSHAlloc o (DSHLoop (S n) body))) = 
    Some (inl msg).
Proof.
  cbn.
  rewrite <-T_ID.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; cbn; nia).
  destruct (evalDSHOperator (DSHPtrVal t_id o :: σ) (DSHLoop n body)
                            (memory_set m t_id mem_empty) (estimateFuel (DSHLoop n body)))
           as [t|] eqn:LoopN'; [destruct t as [|loopN_m'] |];
    try some_none; some_inv; try inl_inr; inl_inr_inv.
  rewrite evalDSHOperator_estimateFuel_ge by nia.
  rewrite <-LoopN in *; clear LoopN loopN_m.
  repeat break_match; try some_none; repeat some_inv; try inl_inr.
  repeat constructor.
Qed.

(* [body] here corresponds to IReduction's [seq rr memmap2] *)
Lemma IReduction_DSH_step
      (o n : nat)
      (body : DSHOperator)
      (m loopN_m iterSN_m : memory)
      (σ : evalContext)
      (t_id : mem_block_id)
      (T_ID : t_id ≡ memory_next_key m)
      (body_mem_stable : ∀ σ m m' fuel,
          evalDSHOperator σ body m fuel = Some (inr m')
          → ∀ k, mem_block_exists k m ↔ mem_block_exists k m')

      (LoopN : evalDSHOperator σ
                               (DSHAlloc o (DSHLoop n body)) m
                               (estimateFuel (DSHAlloc o (DSHLoop n body)))
               = Some (inr loopN_m))
      (IterSN : evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                body
                                (memory_set loopN_m t_id mem_empty)
                                (estimateFuel body) = Some (inr iterSN_m))

      (* execution of [body] does not depend on block under [t_id] *)
      (BS : forall mb, evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                  body
                                  (memory_set loopN_m t_id mb)
                                  (estimateFuel body) =
                  evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                  body
                                  (memory_set loopN_m t_id mem_empty)
                                  (estimateFuel body))
  :
    evalDSHOperator σ (DSHAlloc o (DSHLoop (S n) body)) m
                  (estimateFuel (DSHAlloc o (DSHLoop (S n) body))) = 
    Some (inr (memory_remove iterSN_m t_id)).
Proof.
  cbn.
  remember (DSHLoop n body) as loop_n.
  cbn in LoopN.
  rewrite <-T_ID in *.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; subst; cbn; lia).
  destruct (evalDSHOperator (DSHPtrVal t_id o :: σ) loop_n
                            (memory_set m t_id mem_empty) (estimateFuel loop_n))
           as [t|] eqn:LoopN'; [destruct t as [|loopN_m'] |];
    try some_none; some_inv; try inl_inr; inl_inr_inv.
  assert (T : exists t_loopN_m', memory_lookup loopN_m' t_id = Some t_loopN_m');
    [| destruct T as [t_loopN_m' T_loopN_m']].
  {
    subst loop_n.
    clear - LoopN' body_mem_stable.
    enough (loopn_mem_stable : ∀ σ m m' fuel,
               evalDSHOperator σ (DSHLoop n body) m fuel = Some (inr m')
               → ∀ k, mem_block_exists k m ↔ mem_block_exists k m').
    {
      apply is_Some_equiv_def.
      apply memory_is_set_is_Some.
      eq_to_equiv.
      apply loopn_mem_stable with (k:=t_id) in LoopN'.
      apply LoopN'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    clear - body_mem_stable.
    intros.
    destruct fuel; [inversion H |].
    generalize dependent m'.
    induction n.
    -
      intros.
      cbn in H.
      some_inv; inl_inr_inv.
      rewrite H.
      reflexivity.
    -
      intros.
      cbn in H.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      specialize (IHn m0).
      apply evalDSHOperator_fuel_ge with (f':=S fuel) in Heqo; [| auto].
      eq_to_equiv.
      apply IHn in Heqo; clear IHn.
      rewrite Heqo.
      eapply body_mem_stable.
      eassumption.
  }
  assert (loopN_m' = memory_set loopN_m t_id t_loopN_m').
  {
    clear - T_loopN_m' LoopN.
    intros k.
    destruct (Nat.eq_dec k t_id).
    -
      subst.
      unfold memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      apply T_loopN_m'.
    -
      unfold memory_set.
      rewrite NP.F.add_neq_o by congruence.
      specialize (LoopN k).
      unfold memory_remove in LoopN.
      rewrite NP.F.remove_neq_o in LoopN by congruence.
      assumption.
  }

  specialize (BS t_loopN_m').
  rewrite <-H in BS.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; subst; cbn; nia).
  rewrite IterSN in BS.
  destruct (evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ) body
                            loopN_m' (estimateFuel body))
           as [t|] eqn:IterSN'; [destruct t as [|iterSN_m'] |];
    try some_none; some_inv; try inl_inr; inl_inr_inv.
  repeat f_equiv.
  assumption.
Qed.

Instance SHCOL_DSHCOL_mem_block_equiv_err_p_proper {mb md} :
  Proper ((=) ==> iff) (err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv mb ma md)).
Proof.
  intros.
  intros m1 m2 ME.
  destruct m1, m2; try inl_inr; repeat inl_inr_inv.
  all: split; intros C; inversion C; subst.
  all: constructor.
  rewrite <-ME; assumption.
  rewrite ME; assumption.
Qed.

Lemma DSHAlloc_inv
      (σ : evalContext)
      (m rm : memory)
      (o : nat)
      (dop : DSHOperator)
      (t_id : NM.key)
      (T_ID : t_id ≡ memory_next_key m)
  :
    evalDSHOperator σ (DSHAlloc o dop) m (estimateFuel (DSHAlloc o dop)) = Some (inr rm) ->
    exists m', evalDSHOperator (DSHPtrVal t_id o :: σ) dop (memory_set m t_id mem_empty)
                          (estimateFuel dop) = Some (inr m') /\
          rm = memory_remove m' t_id.
Proof.
  intros.
  cbn in H.
  repeat break_match; try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
  subst.
  exists m0.
  eq_to_equiv.
  intuition.
Qed.

Definition mem_stable' (dop : DSHOperator) := 
  ∀ (σ : evalContext) (m m' : memory) (fuel : nat),
    evalDSHOperator σ dop m fuel = Some (inr m') →
    ∀ k : mem_block_id, mem_block_exists k m ↔ mem_block_exists k m'.

Lemma DSHSeq_mem_stable (dop1 dop2 : DSHOperator) :
  mem_stable' dop1 ->
  mem_stable' dop2 ->
  mem_stable' (DSHSeq dop1 dop2).
Proof.
  intros.
  unfold mem_stable' in *.
  cbn in *.
  intros.
  destruct fuel; [inversion H1|].
  cbn in H1.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  subst.
  rename m0 into m1, m' into m2, m into m0.
  eq_to_equiv.
  apply H with (k:=k) in Heqo.
  apply H0 with (k:=k) in H1.
  rewrite Heqo, H1.
  reflexivity.
Qed.

Lemma DSHLoop_mem_stable (dop : DSHOperator) :
  mem_stable' dop ->
  forall n, mem_stable' (DSHLoop n dop).
Proof.
  unfold mem_stable'.
  intros.
  generalize dependent m'.
  generalize dependent fuel.
  induction n.
  -
    intros.
    destruct fuel; [inversion H0 |].
    cbn in H0.
    some_inv; inl_inr_inv.
    rewrite H0; reflexivity.
  -
    intros.
    destruct fuel; [inversion H0 |].
    cbn in H0.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    eq_to_equiv.
    apply IHn in Heqo.
    apply H with (k:=k) in H0.
    rewrite Heqo, H0.
    reflexivity.
Qed.

Lemma DSH_pure_mem_stable (dop : DSHOperator) (y_p : PExpr) :
  DSH_pure dop y_p -> mem_stable' dop.
Proof.
  intros.
  unfold mem_stable'.
  apply mem_stable.
Qed.

Lemma memory_subset_except_transitive (k : mem_block_id) (m1 m2 m3 : memory) :
  memory_subset_except k m1 m2 ->
  memory_subset_except k m2 m3 ->
  memory_subset_except k m1 m3.
Proof.
  unfold memory_subset_except.
  intros S12 S23 j v1 V1.
  specialize (S12 j v1 V1).
  destruct S12 as [v2 [V2 VE2]].
  specialize (S23 j v2 V2).
  destruct S23 as [v3 [V3 VE3]].
  exists v3.
  split; [assumption |].
  intros.
  rewrite VE2, VE3 by assumption.
  reflexivity.
Qed.

Lemma DSHLoop_invariant
      (σ : evalContext)
      (body : DSHOperator)
      (n : nat)
      (m rm: memory)
      (P : memory -> Prop)
      (PP : Proper ((=) ==> iff) P)
      (body_inv : forall n m m', P m ->
                            evalDSHOperator (DSHnatVal n :: σ) body m
                                            (estimateFuel body) = Some (inr m') ->
                            P m')
  :
    P m ->
    evalDSHOperator σ (DSHLoop n body) m (estimateFuel (DSHLoop n body)) = Some (inr rm) ->
    P rm.
Proof.
  intros.
  pose proof (estimateFuel_positive body) as FB.
  generalize dependent rm.
  induction n.
  -
    intros.
    cbn in H0.
    some_inv; inl_inr_inv.
    rewrite <-H0.
    assumption.
  -
    intros.
    cbn in H0.
    rewrite evalDSHOperator_estimateFuel_ge in H0 by (cbn; lia).
    repeat break_match; try some_none; repeat some_inv; try inl_inr.
    subst.
    specialize (IHn m0).
    autospecialize IHn; [reflexivity |].
    eapply body_inv.
    apply IHn.
    rewrite evalDSHOperator_estimateFuel_ge in H0 by (cbn; nia).
    eapply H0.
Qed.

Lemma DSHLoop_invariant'
      (σ : evalContext)
      (body : DSHOperator)
      (n : nat)
      (m rm: memory)
      (P : memory -> Prop)
      (PP : Proper ((=) ==> iff) P)
      (body_inv : forall m m' n, evalDSHOperator (DSHnatVal n :: σ) body m
                                       (estimateFuel body) = Some (inr m') ->
                       P m')
  :
    P m ->
    evalDSHOperator σ (DSHLoop n body) m (estimateFuel (DSHLoop n body)) = Some (inr rm) ->
    P rm.
Proof.
  eapply DSHLoop_invariant.
  assumption.
  intros.
  eapply body_inv; eassumption.
Qed.

Global Instance IReduction_MSH_DSH_compat_S
       {i o n: nat}
       {init : CarrierA}
       {dot: CarrierA -> CarrierA -> CarrierA}
       {pdot: Proper ((=) ==> (=) ==> (=)) dot}
       {op_family: @MSHOperatorFamily i o (S n)}
       {df : AExpr}
       {σ : evalContext}
       {x_p y_p y_p'': PExpr}
       {XY : evalPexp σ x_p <> evalPexp σ y_p}
       {Y : y_p'' ≡ incrPVar 0 (incrPVar 0 y_p)}
       {rr : DSHOperator}
       {m : memory}
       {DP}
       (P: DSH_pure rr (PVar 1))
       (DC : forall m' y_id d1 d2,
           evalPexp σ y_p ≡ inr y_id ->
           memory_subset_except y_id m m'  ->
           MSH_DSH_BinCarrierA_compat dot (d1 :: d2 :: σ) df m')
       (FC : forall m' tmpk t y_id mb,
           evalPexp σ y_p ≡ inr y_id ->
           memory_subset_except y_id m m'  ->
           tmpk ≡ memory_next_key m ->
           @MSH_DSH_compat _ _ (op_family t) rr
                           (DSHnatVal (proj1_sig t) :: DSHPtrVal tmpk o :: σ)
                           (memory_set m' tmpk mb)
                           (incrPVar 0 (incrPVar 0 x_p)) (PVar 1) P)

       (MF : MSHOperator_Facts (@MSHIReduction i o (S n) init dot _ op_family))
       (FMF : ∀ (j : nat) (jc : j < (S n)), MSHOperator_Facts (op_family (mkFinNat jc)))
       (FD : ∀ (j : nat) (jc : j < (S n)),
           Same_set (FinNat o) (m_out_index_set (op_family (mkFinNat jc)))
                    (Full_set (FinNat o)))
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i o (S n) init dot pdot op_family)
      (DSHSeq
         (DSHMemInit o y_p init)
         (DSHAlloc o
                   (DSHLoop (S n)
                            (DSHSeq
                               rr
                               (DSHMemMap2 o y_p''
                                           (PVar 1)
                                           y_p''
                                           df)))))
      σ m x_p y_p DP.
Proof.
  subst.
  constructor.
  intros x_m y_m X_M Y_M.

  (** * prepare context and memory lookups *)
  destruct (evalPexp σ x_p) as [| x_id] eqn:X_ID;
    [unfold lookup_Pexp in X_M; rewrite X_ID in X_M; inversion X_M |].
  destruct (evalPexp σ y_p) as [| y_id] eqn:Y_ID;
    [unfold lookup_Pexp in Y_M; rewrite Y_ID in Y_M; inversion Y_M |].
  assert (XID_M : memory_lookup m x_id = Some x_m)
    by (unfold lookup_Pexp in X_M; rewrite X_ID in X_M;
        cbn in X_M; memory_lookup_err_to_option; assumption).
  assert (YID_M : memory_lookup m y_id = Some y_m)
    by (unfold lookup_Pexp in Y_M; rewrite Y_ID in Y_M;
        cbn in Y_M; memory_lookup_err_to_option; assumption).
  assert (T : x_id ≢ y_id) by (intros C; contradict XY; rewrite C; reflexivity);
    clear XY; rename T into XY.

  induction n.
  -
    (** * go through init *)
    remember (DSHLoop (S 0)
                  (DSHSeq rr
                     (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1) 
                                 (incrPVar 0 (incrPVar 0 y_p)) df)))
      as loop eqn:LOOP.
    remember (DSHAlloc o loop) as dop.
    cbn [evalDSHOperator estimateFuel].
    rewrite evalDSHOperator_estimateFuel_ge by (subst; cbn; lia).
    cbn [evalDSHOperator estimateFuel].
    simpl bind.
    rewrite Y_ID.
    unfold memory_lookup_err.
    destruct (memory_lookup m y_id) eqn:YID_M'; try some_none.
    replace (trywith "Error looking up 'y' in DSHMemInit" (Some m0))
      with (@inr string mem_block m0)
      by reflexivity.
    rewrite evalDSHOperator_estimateFuel_ge by (subst; cbn; lia).
    some_inv.
    rename m0 into y_m'.
    remember (memory_set m y_id
                         (mem_union (mem_const_block (NatAsNT.MNatAsNT.to_nat o) init)
                                    y_m'))
      as init_m eqn:INIT_M; symmetry in INIT_M.
    remember (memory_next_key init_m) as t_id eqn:T_ID; symmetry in T_ID.
    subst dop.
  
    (** * deal with y_m and y_m' (get rid of one) *)
    remember (λ (md : mem_block) (m' : memory),
              err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
                    (lookup_Pexp σ m' y_p))
      as Rel'.
    rename y_m' into t, y_m into y_m';
      rename t into y_m, YID_M into YM_YM', YID_M' into YID_M.
    rewrite <-YM_YM' in Y_M.
    remember (λ (md : mem_block) (m' : memory),
               err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
                     (lookup_Pexp σ m' y_p)) as Rel.
    assert (T : forall omb oem, h_opt_opterr_c Rel omb oem <-> h_opt_opterr_c Rel' omb oem);
      [| apply T; clear T HeqRel' Rel' YM_YM' y_m'].
    {
      assert (forall mb m, Rel' mb m <-> Rel mb m).
      {
        subst; clear - YM_YM'.
        split; intros.
        all: inversion H; constructor.
        all: rewrite YM_YM' in *; assumption.
      }
      clear - H.
      split; intros.
      all: inversion H0; try constructor.
      all: apply H.
      all: assumption.
    }
  
    
    (** * useful facts about init *)
    assert (T_next_M : memory_next_key m ≡ t_id).
    {
      subst.
      rewrite memory_next_key_override.
      reflexivity.
      apply mem_block_exists_exists_equiv.
      eexists.
      eq_to_equiv.
      eassumption.
    }
    assert (TX_neq : t_id <> x_id)
      by (apply memory_lookup_not_next_equiv in XID_M; congruence).
    assert (TY_neq : t_id <> y_id)
      by (eq_to_equiv; apply memory_lookup_not_next_equiv in YID_M; congruence).
    rename XY into T; assert (XY_neq : x_id <> y_id) by congruence; clear T.
    assert (INIT_equiv_M : memory_equiv_except init_m m y_id)
      by (intros k H; subst init_m;
          rewrite memory_lookup_memory_set_neq by congruence; reflexivity).
    assert (RP : Proper (equiv ==> equiv ==> iff) Rel).
    {
      subst; clear.
      intros m1 m2 E1 m3 m4 E2.
      split; intros H; inversion H; clear H; err_eq_to_equiv_hyp.
      -
        assert (Proper ((=) ==> iff)
                       (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m2))
          by (intros m m' ME; rewrite ME; reflexivity).
        rewrite <-E2.
        rewrite <-H0.
        constructor.
        rewrite <-E1.
        assumption.
      -
        assert (Proper ((=) ==> iff)
                       (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m1))
          by (intros m m' ME; rewrite ME; reflexivity).
        rewrite E2.
        rewrite <-H0.
        constructor.
        rewrite E1.
        assumption.
    }

    (** * specialize FC *)
    remember (Nat.lt_0_succ 0) as o1 eqn:O1.
    specialize (FC init_m t_id (mkFinNat o1) y_id mem_empty).
    full_autospecialize FC; try congruence.
    {
      intros k v L.
      subst init_m.
      destruct (Nat.eq_dec k y_id).
      -
        rewrite memory_lookup_memory_set_eq by congruence.
        eexists.
        split.
        reflexivity.
        congruence.
      -
        exists v.
        rewrite memory_lookup_memory_set_neq by congruence.
        intuition.
    }
    cbn in FC.
    inversion_clear FC as [T]; rename T into FC.
    specialize (FC x_m mem_empty).
    full_autospecialize FC.
    {
      repeat rewrite lookup_Pexp_incrPVar.
      unfold lookup_Pexp.
      rewrite X_ID.
      cbn.
      unfold memory_lookup_err.
      subst init_m.
      repeat rewrite memory_lookup_memory_set_neq by congruence.
      rewrite XID_M.
      reflexivity.
    }
    {
      cbn.
      unfold memory_lookup_err.

      rewrite memory_lookup_memory_set_eq by congruence.
      reflexivity.
    }

    
    cbn in FC.
    inversion FC as [M D | msg M D | mm dm R M D ]; clear FC.
    + (* DSH runs out of fuel *)
      exfalso; clear - D.
      symmetry in D.
      contradict D.
      apply is_Some_ne_None.
      apply evalDSHOperator_estimateFuel.
    + (* both MSH and DSH fail *)
      cbn.

      (* simplify mem_op to None *)
      unfold get_family_mem_op.
      rewrite <-O1.
      destruct mem_op; try some_none.

      (* simplify dop *)
      subst loop.
      cbn.
      rewrite T_ID.
      rewrite evalDSHOperator_estimateFuel_ge by lia.
      rewrite <-D.
      constructor.
    +
      (** * both MSH and DSH succeed *)
      cbn.

      (* simplify mem_op down to fold *)
      unfold get_family_mem_op.
      rewrite <-O1.
      destruct mem_op as [m'|] eqn:MM; 
        [some_inv; subst m' | some_none].
      cbn.

      (* simplify dop down to MemMap2*)
      subst loop.
      cbn.
      rewrite T_ID.
      rewrite evalDSHOperator_estimateFuel_ge by lia.
      rewrite <-D.
      rewrite evalDSHOperator_estimateFuel_ge
        by (cbn; pose proof estimateFuel_positive rr; lia).

      (* asserts to be used by MemMap2_merge_with_def *)
      assert (M_subs_DM : memory_subset_except y_id m dm).
      {
        clear - P D T_next_M INIT_M TY_neq.
        subst init_m.
        unfold memory_subset_except; intros.
        assert (KT_neq : k <> t_id)
          by (apply memory_lookup_not_next_equiv in H; congruence).
        clear T_next_M.
        inversion_clear P as [T S]; clear T.
        symmetry in D; eq_to_equiv.
        apply S with (y_i:=t_id) in D; [| reflexivity]; clear S.
        specialize (D k KT_neq).
        destruct (Nat.eq_dec k y_id).
        -
          eexists.
          rewrite <-D; clear D.
          rewrite memory_lookup_memory_set_neq by congruence.
          rewrite memory_lookup_memory_set_eq by congruence.
          split.
          reflexivity.
          congruence.
        -
          eexists.
          rewrite <-D; clear D.
          repeat rewrite memory_lookup_memory_set_neq by congruence.
          split.
          eassumption.
          reflexivity.
      }
      assert (T : exists t_dm,
                   lookup_Pexp (DSHnatVal 0 :: DSHPtrVal t_id o :: σ) dm (PVar 1) = inr t_dm);
        [| destruct T as [t_dm T_DM]].
      {
        cbn.
        intros.
        clear - D P.
        inversion_clear P as [S T]; clear T.
        symmetry in D; eq_to_equiv.
        apply S with (k:=t_id) in D; clear S.
        assert (mem_block_exists t_id (memory_set init_m t_id mem_empty))
          by (apply mem_block_exists_memory_set_eq; reflexivity).
        apply D in H; clear D.
        apply memory_is_set_is_Some in H.
        apply is_Some_def in H.
        destruct H.
        exists x.
        unfold memory_lookup_err.
        rewrite H.
        constructor.
        reflexivity.
      }
      assert (YID_DM : memory_lookup dm y_id =
                      Some (mem_union (mem_const_block o init) y_m)).
      {
        clear - D P INIT_M TY_neq.
        subst init_m.
        inversion_clear P as [T S]; clear T.
        symmetry in D; eq_to_equiv.
        apply S with (y_i:=t_id) in D; [| reflexivity]; clear S.
        unfold memory_equiv_except in D.
        rewrite <-D by congruence; clear D.
        rewrite memory_lookup_memory_set_neq by congruence.
        rewrite memory_lookup_memory_set_eq by congruence.
        reflexivity.
      }
      assert (Y_ID_in_dm : evalPexp (DSHnatVal 0 :: DSHPtrVal t_id 0 :: σ)
                                    (incrPVar 0 (incrPVar 0 y_p)) = inr y_id)
        by (repeat rewrite evalPexp_incrPVar; rewrite Y_ID; reflexivity).
      assert (Y_DM : lookup_Pexp (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
                               dm (incrPVar 0 (incrPVar 0 y_p)) =
                     inr (mem_union (mem_const_block o init) y_m)).
      {
        clear - YID_DM Y_ID.
        repeat rewrite lookup_Pexp_incrPVar.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite Y_ID.
        cbn.
        rewrite YID_DM.
        reflexivity.
      }
      assert (Dot_compat_dm : MSH_DSH_BinCarrierA_compat dot
                                               (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
                                               df dm);
        [| clear DC].
      {
        eapply DC.
        reflexivity.
        assumption.
      }
      assert (T_DM_dense : ∀ k : nat, k < o → mem_in k t_dm).
      {
        intros.
        inversion R.
        assert (x = t_dm)
          by (eq_to_equiv; rewrite T_DM in H0; inl_inr_inv; assumption).
        rewrite H2 in H1.
        eapply SHCOL_DSHCOL_mem_block_equiv_keys_union.
        eassumption.
        right.
        clear - MM FMF FD H.
        specialize (FMF 0 o1); specialize (FD 0 o1).
        inversion_clear FMF as [T1 FILL T2]; clear T1 T2.
        apply FILL with (jc:=H) (m0:=x_m).
        assumption.
        unfold Same_set, Included in FD.
        destruct FD as [T FD]; clear T.
        apply FD.
        constructor.
      }
      assert (IY_dense : ∀ k : nat, k < o → mem_in k (mem_union (mem_const_block o init) y_m)).
      {
        intros.
        eapply mem_union_as_Union.
        reflexivity.
        left.
        apply mem_in_mem_lookup.
        erewrite mem_const_block_find.
        constructor.
        assumption.
      }
      
      repeat break_match.
      * (* Map2 fails *)
        exfalso.
        eq_to_equiv.
        enough (exists m', evalDSHOperator (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
            (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
               (incrPVar 0 (incrPVar 0 y_p)) df) dm
            (estimateFuel
               (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1) 
                  (incrPVar 0 (incrPVar 0 y_p)) df)) = Some (inr m'))
          by (destruct H; rewrite H in Heqo0; some_inv; inl_inr).
        eapply DSHMap2_succeeds; eassumption.
      * (* Map2 succeeds *)
        rename m0 into ma, Heqo0 into MA; clear Heqs0 s.
        constructor.
        subst Rel.

        destruct (lookup_Pexp σ (memory_remove ma t_id) y_p) eqn:Y_MA.
        {
          (* [y_p] disappeared in [ma] - not pure behavior *)
          exfalso.
          pose proof @MemMap2_DSH_pure
               (incrPVar 0 (incrPVar 0 y_p)) (PVar 1) (incrPVar 0 (incrPVar 0 y_p)) o df.
          eq_to_equiv.
          cbn in Y_MA.
          unfold memory_lookup_err, trywith in Y_MA.
          repeat break_match; try inl_inr; repeat inl_inr_inv.
          1: inversion Y_MA.
          eq_to_equiv.
          rewrite Y_ID in Heqo0.
          rewrite memory_lookup_memory_remove_neq in Heqo0 by congruence.
          clear - Heqo0 MA H YID_DM.
          inversion_clear H as [S T]; clear T.
          apply S with (k:=y_id) in MA; clear S.
          contradict Heqo0.
          apply is_Some_nequiv_None.
          repeat rewrite memory_is_set_is_Some in *.
          apply MA.
          unfold is_Some; break_match; try some_none.
          trivial.
        }
        constructor.

        apply Option_equiv_eq in MA.
        apply err_equiv_eq in Y_MA.
        rewrite MemMap2_merge_with_def_firstn with (init:=init) in MA; try eassumption.
        2:  repeat rewrite evalPexp_incrPVar; rewrite Y_ID; reflexivity.
        some_inv; inl_inr_inv.
        rewrite <-MA in Y_MA; clear MA ma.
        assert (m0 = mem_union (mem_merge_with_def dot init
                                 (mem_firstn o (mem_union (mem_const_block o init) y_m))
                                 (mem_firstn o t_dm))
                               (mem_union (mem_const_block o init) y_m)).
        {
          eq_to_equiv.
          unfold lookup_Pexp, memory_lookup_err in Y_MA.
          assert (evalPexp σ y_p ≡ inr y_id)
            by (destruct (evalPexp σ y_p); try inl_inr; inl_inr_inv;
                cbv in Y_ID; rewrite Y_ID; reflexivity).
          rewrite H in Y_MA.
          simpl in Y_MA.
          rewrite memory_lookup_memory_remove_neq in Y_MA by congruence.
          rewrite memory_lookup_memory_set_eq in Y_MA by congruence.
          unfold trywith in Y_MA.
          inversion Y_MA; subst.
          rewrite H2.
          reflexivity.
        }
        rewrite H.
        clear Y_MA H m0.
        intros k.
        destruct (le_lt_dec o k).
        --
          constructor 1.
          ++
            apply mem_not_in_mem_lookup.
            rewrite <-mem_merge_with_def_as_Union.
            unfold MMemoryOfCarrierA.mem_empty, mem_in.
            rewrite NP.F.empty_in_iff.
            enough (not (mem_in k mm)) by intuition.
            eapply out_mem_oob; eassumption.
          ++
            unfold mem_lookup, mem_union, mem_merge_with_def.
            repeat rewrite NP.F.map2_1bis by reflexivity.
            repeat rewrite mem_firstn_lookup_oob by assumption.
            rewrite mem_const_block_find_oob by assumption.
            reflexivity.
        --
          constructor 2.
          ++
            apply mem_in_mem_lookup.
            rewrite <-mem_merge_with_def_as_Union.
            right.
            eapply out_mem_fill_pattern.
            eassumption.
            instantiate (1:=l).
            apply FD.
            constructor.
          ++
            rewrite firstn_mem_const_block_union.
            unfold mem_lookup, mem_union, mem_merge_with_def.
            unfold MMemoryOfCarrierA.mem_merge_with_def.
            repeat rewrite NP.F.map2_1bis by reflexivity.
            rewrite mem_const_block_find by assumption.
            rewrite mem_firstn_lookup by assumption.
            specialize (T_DM_dense k l).
            apply mem_in_mem_lookup, is_Some_def in T_DM_dense.
            destruct T_DM_dense as [k_tdm K_TDM].
            rewrite K_TDM.
            cbn.

            inversion R.
            assert (exists k_mm, mem_lookup k mm = Some k_mm).
            {
              apply is_Some_equiv_def.
              apply mem_in_mem_lookup.
              eapply out_mem_fill_pattern.
              eassumption.
              instantiate (1:=l).
              apply FD.
              constructor.
            }
            eq_to_equiv; symmetry in H; memory_lookup_err_to_option.
            assert (T : x = t_dm); [| rewrite T in *; clear T x].
            {
              clear - H T_DM.
              cbn in T_DM.
              memory_lookup_err_to_option.
              rewrite H in T_DM; some_inv.
              assumption.
            }
            destruct H1 as [k_mm K_MM].
            break_match.
            all: eq_to_equiv; rewrite K_MM in Heqo0.
            all: try some_none; some_inv.
            rewrite <-Heqo0 in *; clear c Heqo0.
            
            specialize (H0 k).
            rewrite K_MM, K_TDM in H0.
            inversion H0; try some_none.
            some_inv.
            rewrite H2.
            reflexivity.
      * (* Map2 runs out of fuel *)
        clear - Heqo0.
        assert (is_Some (evalDSHOperator (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
            (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
               (incrPVar 0 (incrPVar 0 y_p)) df) dm
            (estimateFuel
               (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
                           (incrPVar 0 (incrPVar 0 y_p)) df))))
          by apply evalDSHOperator_estimateFuel.
        unfold is_Some in H.
        break_match; try some_none.
        contradiction.
  -
    (** * MSH step *)
    (* done immediately to get [opf] *)
    rewrite IReduction_MSH_step.

    (** * renaming *)
    rename n into n'; remember (S n') as n.
    remember (Nat.lt_succ_diag_r n) as nSn.
    rename op_family into S_opf; remember (shrink_m_op_family S_opf) as opf.

    (** * specialize IHn *)
    specialize (IHn opf).
    full_autospecialize IHn.
    {
      apply IReduction_DSH_pure; auto.
    }
    {
      intros.
      subst opf.
      unfold shrink_m_op_family.
      eapply FC.
      all: eassumption.
    }
    {
      subst.
      unfold shrink_m_op_family.
      apply IReduction_MFacts.
      -
        intros.
        apply FMF.
      -
        intros.
        apply FD.
    }
    {
      subst opf.
      unfold shrink_m_op_family.
      intros.
      apply FMF.
    }
    {
      subst opf.
      unfold shrink_m_op_family.
      intros.
      apply FD.
    }

    (** * cases by [opf] and [loopN] *)
    remember (evalDSHOperator σ
               (DSHSeq (DSHMemInit o y_p init)
                  (DSHAlloc o
                     (DSHLoop n
                        (DSHSeq rr
                           (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) 
                              (PVar 1) (incrPVar 0 (incrPVar 0 y_p)) df))))) m
               (estimateFuel
                  (DSHSeq (DSHMemInit o y_p init)
                     (DSHAlloc o
                        (DSHLoop n
                           (DSHSeq rr
                              (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) 
                                 (PVar 1) (incrPVar 0 (incrPVar 0 y_p)) df)))))))
      as d.
    inversion IHn; subst d; clear IHn.
    +
      (* [loopN] ran out of fuel *)
      exfalso; clear - H1; symmetry in H1; contradict H1.
      apply is_Some_ne_None.
      apply evalDSHOperator_estimateFuel.
    +
      (* both [MSHIReduction opf] and [loopN] failed *)
      replace (mem_op (MSHIReduction init dot opf) x_m) with (@None mem_block).
      simpl bind.

      eq_to_equiv.
      rewrite MemInit_simpl in *; try eassumption.
      symmetry in H1.
      remember (DSHLoop n
                        (DSHSeq rr
                                (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
                                            (incrPVar 0 (incrPVar 0 y_p)) df))) as t.
      cbn in H1.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      rewrite Alloc_Loop_error1.
      constructor.
      reflexivity.
      eq_to_equiv.
      rewrite <-Heqt.
      apply Heqo0.
    +
      (* both [MSHIReduction opf] and [loopN] succeeded *)
      symmetry in H, H1.
      rename a into opf_mm, H into OPF_MM, b into loopN_m, H1 into LoopN_M.
      rename H0 into OPF_LoopN.

      apply Option_equiv_eq in LoopN_M.

      (** * lookups in [loopN_m] *)
      assert (M_LoopNM_E : memory_equiv_except m loopN_m y_id).
      {
        eapply mem_write_safe with (y_i:=y_id) in LoopN_M.
        assumption.
        erewrite Y_ID.
        reflexivity.
        Unshelve.
        apply IReduction_DSH_pure; auto.
      }
      assert (M_LoopNM_K : forall k, mem_block_exists k m ↔ mem_block_exists k loopN_m).
      {
        intros.
        unshelve eapply mem_stable with (k:=k) in LoopN_M.
        exact y_p.
        apply IReduction_DSH_pure; auto.
        eassumption.
      }
      assert (X_LoopNM : lookup_Pexp σ loopN_m x_p = inr x_m).
      {
        unfold lookup_Pexp, memory_lookup_err, trywith.
        rewrite X_ID.
        cbn.
        specialize (M_LoopNM_E x_id XY).
        rewrite XID_M in M_LoopNM_E.
        break_match; try some_none.
        some_inv; rewrite M_LoopNM_E; reflexivity.
      }
      assert (T : exists y_loopNm, lookup_Pexp σ loopN_m y_p = inr y_loopNm);
        [| destruct T as [y_loopNm Y_LoopNM]].
      {
        unfold lookup_Pexp, memory_lookup_err, trywith.
        rewrite Y_ID.
        cbn.
        break_match; [eexists; reflexivity |].
        enough (T : is_Some (memory_lookup loopN_m y_id)) by (rewrite Heqo0 in T; some_none).
        apply memory_is_set_is_Some.
        apply M_LoopNM_K.
        apply memory_is_set_is_Some.
        apply is_Some_equiv_def; eexists; eassumption.
      }

      (** * lookups in [init_m] *)
      rewrite MemInit_simpl in * by (eq_to_equiv; eassumption).
      remember (memory_set m y_id (mem_union (mem_const_block o init) y_m)) as init_m.
      assert (M_InitM_E : memory_equiv_except m init_m y_id).
      {
        intros k YK.
        subst init_m.
        rewrite memory_lookup_memory_set_neq by congruence.
        reflexivity.
      }
      assert (M_InitM_K : forall k, mem_block_exists k m <-> mem_block_exists k init_m).
      {
        intros.
        subst init_m.
        repeat rewrite memory_is_set_is_Some.
        destruct (Nat.eq_dec k y_id).
        -
          subst.
          rewrite memory_lookup_memory_set_eq by congruence.
          cbn.
          unfold is_Some.
          break_match; try some_none.
          reflexivity.
        -
          rewrite memory_lookup_memory_set_neq by congruence.
          reflexivity.
      }
      assert (X_InitM : lookup_Pexp σ init_m x_p = inr x_m).
      {
        subst init_m.
        unfold lookup_Pexp, memory_lookup_err, trywith.
        rewrite X_ID.
        simpl.
        rewrite memory_lookup_memory_set_neq by congruence.
        break_match; try some_none; some_inv; f_equiv; assumption.
      }
      remember (mem_union (mem_const_block o init) y_m) as y_initm.
      assert (Y_InitM : lookup_Pexp σ init_m y_p = inr y_initm).
      {
        subst init_m.
        unfold lookup_Pexp, memory_lookup_err, trywith.
        rewrite Y_ID.
        simpl.
        rewrite memory_lookup_memory_set_eq by congruence.
        reflexivity.
      }
      assert (INIT_equiv_M : memory_equiv_except init_m m y_id)
        by (intros k H; subst init_m;
            rewrite memory_lookup_memory_set_neq by congruence; reflexivity).

      (** * facts about t_id *)
      remember (memory_next_key init_m) as t_id eqn:T_ID.
      assert (T_next_M : t_id ≡ memory_next_key m).
      {
        subst.
        rewrite memory_next_key_override.
        reflexivity.
        apply mem_block_exists_exists_equiv.
        eexists.
        eq_to_equiv.
        eassumption.
      }
      assert (TX_neq : t_id <> x_id)
        by (apply memory_lookup_not_next_equiv in XID_M; congruence).
      assert (TY_neq : t_id <> y_id)
        by (eq_to_equiv; apply memory_lookup_not_next_equiv in YID_M; congruence).
      rename XY into T; assert (XY_neq : x_id <> y_id) by congruence; clear T.

      (** * lookups in [loopN_tm] *)
      apply DSHAlloc_inv with (t_id:=t_id) in LoopN_M; [| subst; reflexivity].
      destruct LoopN_M as [loopN_tm [LoopN_TM LoopN_M]].
      assert (X_LoopNTM : lookup_Pexp σ loopN_tm x_p = inr x_m).
      {
        rewrite <-X_LoopNM.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X_ID.
        cbn.
        rewrite LoopN_M.
        rewrite memory_lookup_memory_remove_neq by congruence.
        reflexivity.
      }
      assert (Y_LoopNTM : lookup_Pexp σ loopN_tm y_p = inr y_loopNm).
      {
        rewrite <-Y_LoopNM.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite Y_ID.
        cbn.
        rewrite LoopN_M.
        rewrite memory_lookup_memory_remove_neq by congruence.
        reflexivity.
      }
      assert (T : exists t_loopNtm, memory_lookup loopN_tm t_id = Some t_loopNtm);
        [| destruct T as [t_loopNtm T_LoopNTM]].
      {
        clear - P LoopN_TM.
        assert (mem_stable'
                  (DSHLoop n (DSHSeq rr
                     (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) 
                        (PVar 1) (incrPVar 0 (incrPVar 0 y_p)) df)))).
        {
          apply DSHLoop_mem_stable.
          apply DSHSeq_mem_stable.
          eapply DSH_pure_mem_stable; eassumption.
          eapply DSH_pure_mem_stable; eapply MemMap2_DSH_pure.
        }
        apply H in LoopN_TM; clear H.
        specialize (LoopN_TM t_id).
        repeat rewrite memory_is_set_is_Some in LoopN_TM.
        rewrite memory_lookup_memory_set_eq in LoopN_TM by reflexivity.
        assert (T : is_Some (Some mem_empty)) by reflexivity;
          apply LoopN_TM in T; clear LoopN_TM.
        apply is_Some_def in T.
        destruct T.
        exists x.
        rewrite H; reflexivity.
      }
      assert (M_sub_LoopNTM : memory_subset_except y_id m loopN_tm).
      {
        clear - M_LoopNM_E M_LoopNM_K YID_M LoopN_M TY_neq T_next_M.
        intros k v V.
        destruct (Nat.eq_dec k y_id).
        -
          subst.
          specialize (M_LoopNM_K y_id).
          repeat rewrite memory_is_set_is_Some in M_LoopNM_K.
          assert (is_Some (memory_lookup m y_id))
            by (apply is_Some_equiv_def; eexists; eassumption).
          apply M_LoopNM_K in H.
          eapply is_Some_equiv_def in H; destruct H.
          exists x.
          intuition.
          rewrite <-H.
          rewrite LoopN_M.
          rewrite memory_lookup_memory_remove_neq by congruence.
          reflexivity.
        -
          exists v.
          intuition.
          rewrite <-V.
          rewrite M_LoopNM_E by congruence.
          rewrite LoopN_M.
          rewrite memory_lookup_memory_remove_neq; [reflexivity |].
          clear - T_next_M V.
          apply memory_lookup_not_next_equiv in V.
          congruence.
      }
      (** * specialize FC *)
      specialize (FC loopN_tm t_id (mkFinNat nSn) y_id t_loopNtm).
      full_autospecialize FC; try congruence; try assumption.
      cbn in FC.
      inversion_clear FC as [T]; rename T into FC.
      specialize (FC x_m t_loopNtm).
      full_autospecialize FC.
      {
        repeat rewrite lookup_Pexp_incrPVar.
        unfold lookup_Pexp, memory_lookup_err, trywith.
        rewrite X_ID.
        simpl.
        rewrite memory_lookup_memory_set_neq by congruence.
        unfold lookup_Pexp, memory_lookup_err in X_LoopNTM.
        rewrite X_ID in X_LoopNTM.
        cbn in X_LoopNTM.
        break_match; inversion X_LoopNTM.
        rewrite H1; reflexivity.
      }
      {
        cbn.
        unfold memory_lookup_err.
        rewrite memory_lookup_memory_set_eq by congruence.
        reflexivity.
      }
      rewrite memory_set_same in FC by assumption.


      
      inversion FC as [M D | msg M D | opf_n_m rr_m R OPF_M RR_M]; clear FC.
      *
        (* rr[n] runs out of fuel *)
        exfalso; symmetry in D; contradict D; clear.
        apply is_Some_ne_None.
        apply evalDSHOperator_estimateFuel.
      *
        (* last family member fails in both MSH and DSH *)
        rewrite Alloc_Loop_error2.
        cbn.
        repeat break_match; constructor.
        reflexivity.
        rewrite <-T_ID.
        apply LoopN_TM.
        cbn.
        rewrite evalDSHOperator_estimateFuel_ge
          by (pose proof estimateFuel_positive rr; cbn; nia).
        rewrite <-T_ID.
        rewrite <-D.
        reflexivity.
      *
        (* last family member succeeds in both MSH and DSH *)
        symmetry in OPF_M, RR_M.

        assert (X_RRM : lookup_Pexp σ rr_m x_p = inr x_m).
        {
          clear - P RR_M X_LoopNTM X_ID TX_neq.
          eq_to_equiv_hyp.
          eapply mem_write_safe in RR_M; [| cbn; reflexivity].
          unfold lookup_Pexp, memory_lookup_err in *.
          rewrite X_ID in *.
          cbn in *.
          rewrite RR_M in X_LoopNTM by congruence.
          assumption.
        }
        assert (Y_RRM : lookup_Pexp σ rr_m y_p = inr y_loopNm).
        {
          clear - P RR_M Y_LoopNTM Y_ID TY_neq.
          eq_to_equiv_hyp.
          eapply mem_write_safe in RR_M; [| cbn; reflexivity].
          unfold lookup_Pexp, memory_lookup_err in *.
          rewrite Y_ID in *.
          cbn in *.
          rewrite RR_M in Y_LoopNTM by congruence.
          assumption.
        }
        assert (T : exists t_rrm, memory_lookup rr_m t_id = Some t_rrm);
          [| destruct T as [t_rrm T_RRM]].
        {
          apply is_Some_equiv_def.
          apply memory_is_set_is_Some.
          eq_to_equiv.
          apply mem_stable with (k:=t_id) in RR_M.
          apply RR_M.
          apply memory_is_set_is_Some.
          apply is_Some_equiv_def.
          eexists; eassumption.
        }

        assert (opf_mm_fill : forall k, k < o -> mem_in k opf_mm).
        {
          intros.
          replace (IReduction_mem dot init (get_family_mem_op opf) x_m)
            with (mem_op (MSHIReduction init dot opf) x_m)
            in OPF_MM
            by reflexivity.
          unshelve eapply out_mem_fill_pattern with (j:=k) in OPF_MM; try eassumption.
          subst opf.
          unfold shrink_m_op_family.
          apply IReduction_MFacts.
          intros.
          apply FMF.
          intros.
          apply FD.
          apply OPF_MM.
          cbn.
          apply m_family_out_set_implies_members.
          subst opf.
          unfold shrink_m_op_family.
          eexists.
          eexists.
          eapply FD.
          constructor.

          Unshelve.
          exact O. (* TODO: this is rather strange - just returning a random nat *)
          omega.
        }

        assert (opf_n_m_fill : forall k, k < o -> mem_in k opf_n_m).
        {
          intros.
          eapply out_mem_fill_pattern; try eassumption.
          apply FD.
          constructor.
          Unshelve.
          assumption.
        }

        assert (y_loopNm_fill : forall k, k < o -> mem_in k y_loopNm).
        {
          clear Y_RRM Y_LoopNM.
          generalize dependent y_loopNm.
          eapply DSHLoop_invariant' with (m:=memory_set init_m t_id mem_empty)
                                        (rm:=loopN_tm).
          4: eassumption.
          -
            intros m1 m2 ME.
            split; intros.
            all: specialize (H y_loopNm).
            1: autospecialize H; [rewrite ME; assumption |].
            2: autospecialize H; [rewrite <-ME; assumption |].
            all: apply H; assumption.
          -
            intros.
            rename m into mb, m' into ma, y_loopNm into b.
            cbn in H.
            repeat break_match; try some_none; try (some_inv; inl_inr).
            rewrite evalDSHOperator_estimateFuel_ge in H by (cbn; nia).
            eapply MemMap2_result_fill in H.
            eapply H.
            repeat rewrite lookup_Pexp_incrPVar.
            assumption.
            assumption.
          -
            intros.
            unfold lookup_Pexp, memory_lookup_err in Y_LoopNTM.
            rewrite Y_ID in Y_LoopNTM.
            simpl bind in Y_LoopNTM.
            subst init_m.
            rewrite memory_lookup_memory_set_neq in Y_LoopNTM by congruence.
            rewrite memory_lookup_memory_set_eq in Y_LoopNTM by congruence.
            cbn in Y_LoopNTM.
            inl_inr_inv.
            rewrite <-Y_LoopNTM.
            subst y_initm.
            apply mem_in_mem_lookup.
            unfold mem_lookup, mem_union.
            rewrite NP.F.map2_1bis by reflexivity.
            rewrite mem_const_block_find by assumption.
            reflexivity.
        }

        assert (t_rrm_fill : forall k, k < o -> mem_in k t_rrm).
        {
          intros.
          cbn in R.
          unfold memory_lookup_err in R.
          rewrite T_RRM in R.
          cbn in R.
          inversion R.
          subst x.
          specialize (H1 k).
          specialize (opf_n_m_fill k H).
          apply mem_in_mem_lookup in opf_n_m_fill.
          apply is_Some_equiv_def in opf_n_m_fill.
          destruct opf_n_m_fill.
          rewrite H0 in H1.
          inversion H1; try some_none.
          apply mem_in_mem_lookup.
          apply is_Some_equiv_def.
          eexists; eassumption.
        }

        assert (
            evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                            (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
                                        (incrPVar 0 (incrPVar 0 y_p)) df)
                            rr_m
                            (estimateFuel ((DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p))
                                                       (PVar 1)
                                                       (incrPVar 0 (incrPVar 0 y_p))
                                                       df))) =
            Some (inr
                    (memory_set rr_m y_id (mem_union
                                          (mem_merge_with_def dot init
                                                              (mem_firstn o y_loopNm)
                                                              (mem_firstn o t_rrm))
                                          y_loopNm)))).
        {
          apply MemMap2_merge_with_def_firstn.
          -
            assumption.
          -
            repeat rewrite lookup_Pexp_incrPVar.
            assumption.
          -
            cbn.
            unfold memory_lookup_err.
            rewrite T_RRM.
            reflexivity.
          -
            repeat rewrite evalPexp_incrPVar.
            rewrite Y_ID; reflexivity.
          -
            cbn in Y_RRM.
            rewrite Y_ID in Y_RRM.
            memory_lookup_err_to_option.
            assumption.
          -
            assumption.
          -
            assumption.
          -
            eapply DC.
            reflexivity.
            unfold memory_subset_except.
            intros.
            destruct (Nat.eq_dec k y_id).
            +
              subst k.
              exists y_loopNm.
              split; [| congruence].
              apply Option_equiv_eq in RR_M.
              apply mem_write_safe with (y_i:=t_id) in RR_M; [| reflexivity].
              rewrite <-RR_M by congruence.
              unfold lookup_Pexp in Y_LoopNTM.
              rewrite Y_ID in Y_LoopNTM.
              cbn in Y_LoopNTM.
              memory_lookup_err_to_option.
              assumption.
            +
              destruct (Nat.eq_dec k t_id).
              *
                subst k.
                rewrite T_next_M in H.
                apply memory_lookup_not_next_equiv in H.
                congruence.
              *
                apply Option_equiv_eq in RR_M.
                apply mem_write_safe with (y_i:=t_id) in RR_M; [| reflexivity].
                specialize (M_sub_LoopNTM k v H).
                destruct M_sub_LoopNTM as [v' G].
                exists v'.
                rewrite <-RR_M by congruence.
                apply G.
        }

        (** * DSH step *)
        erewrite Alloc_Loop_step; try (eq_to_equiv; eauto; fail).
        2: {
          intros.
          cbn.
          replace (Init.Nat.max (estimateFuel rr) 1)
            with (estimateFuel rr)
            by (pose proof estimateFuel_positive rr; lia).
          rewrite RR_M.
          rewrite evalDSHOperator_estimateFuel_ge
            by (pose proof estimateFuel_positive rr; cbn; lia).
          eapply H.
        }

        (** * simplify MSH part *)
        replace (mem_op (MSHIReduction init dot opf) x_m)
          with (Some opf_mm)
          by (rewrite <-OPF_MM; reflexivity).
        remember (λ (md : mem_block) (m' : memory),
                  err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
                        (lookup_Pexp σ m' y_p))
          as Rel.
        cbn.
        constructor.

        (** * coerse MSH and DSH steps to common form *)
        subst Rel.
        assert (T : lookup_Pexp σ
                  (memory_remove
                     (memory_set rr_m y_id
                        (mem_union
                           (mem_merge_with_def dot init
                                               (mem_firstn o y_loopNm)
                                               (mem_firstn o t_rrm))
                           y_loopNm))
                     t_id)
                  y_p = inr (mem_union (mem_merge_with_def dot init
                                                           (mem_firstn o y_loopNm)
                                                           (mem_firstn o t_rrm))
                                       y_loopNm)).
        {
          unfold lookup_Pexp, memory_lookup_err.
          rewrite Y_ID.
          simpl.
          rewrite memory_lookup_memory_remove_neq by congruence.
          rewrite memory_lookup_memory_set_eq by reflexivity.
          reflexivity.
        }

        rewrite T; clear T.
        constructor.
        intros k.
        destruct (le_lt_dec o k).
        --
          (* k is OOB *)
          constructor 1.
          ++
            apply mem_not_in_mem_lookup.
            rewrite <-mem_merge_with_def_as_Union.
            intros C; destruct C as [C | C]; contradict C.
            **
              move OPF_MM after l.
              replace (IReduction_mem dot init (get_family_mem_op opf) x_m)
                with (mem_op (MSHIReduction init dot opf) x_m)
                in OPF_MM
                by reflexivity.
              unshelve eapply out_mem_oob with (j:=k) in OPF_MM; try eassumption.
              subst opf.
              unfold shrink_m_op_family.
              apply IReduction_MFacts.
              intros.
              apply FMF.
              intros.
              apply FD.
            **
              eapply out_mem_oob; eassumption.
          ++
            assert (T : mem_lookup k (mem_union
                                        (mem_merge_with_def dot init
                                                            (mem_firstn o y_loopNm)
                                                            (mem_firstn o t_rrm))
                                        y_loopNm) = mem_lookup k y_loopNm).
            {
              unfold mem_lookup, mem_union.
              rewrite NP.F.map2_1bis by reflexivity.
              break_match; try reflexivity.
              enough (is_None (Some c)) by some_none.
              rewrite <-Heqo0; clear Heqo0 c.
              apply mem_not_in_mem_lookup.
              rewrite <-mem_merge_with_def_as_Union.
              intros C; destruct C as [C | C].
              all: contradict C.
              all: apply mem_not_in_mem_lookup.
              all: rewrite mem_firstn_lookup_oob; [reflexivity | assumption].
            }
            rewrite T.
            eapply MemMap2_rest_preserved with (k:=k) in H.
            2: repeat rewrite lookup_Pexp_incrPVar; eassumption.
            2: {
              repeat rewrite lookup_Pexp_incrPVar.
              unfold lookup_Pexp, memory_lookup_err.
              rewrite Y_ID.
              simpl bind.
              rewrite memory_lookup_memory_set_eq by reflexivity.
              cbn.
              reflexivity.
            }
            2: assumption.
            rewrite <-H.
            rewrite T.
            clear H T.


            clear Y_LoopNM y_loopNm_fill Y_RRM.
            generalize dependent y_loopNm.
            eapply DSHLoop_invariant with (m:=memory_set init_m t_id mem_empty)
                                          (rm:=loopN_tm).
            4: eassumption.
            **
              intros m1 m2 ME.
              split; intros.
              all: specialize (H y_loopNm).
              1: autospecialize H; [rewrite ME; assumption |].
              2: autospecialize H; [rewrite <-ME; assumption |].
              all: apply H; assumption.
            **
              intros.
              cbn in H0.
              repeat break_match;
                try some_none; repeat some_inv;
                try inl_inr; repeat inl_inr_inv.
              subst s.
              rewrite evalDSHOperator_estimateFuel_ge in H0
                by (pose proof estimateFuel_positive rr; cbn; lia).


              pose proof H0 as T.
              cbn in T.
              repeat break_match; try some_none; repeat some_inv; try inl_inr.
              memory_lookup_err_to_option.
              repeat rewrite evalPexp_incrPVar in Heqs.
              rewrite Y_ID in Heqs; inl_inr_inv; subst m2.
              clear Heqs1 Heqs2 Heqs3 T m4 m5.
              
              eapply MemMap2_rest_preserved in H0.
              4: eassumption.
              3: repeat rewrite lookup_Pexp_incrPVar; eassumption.
              2: {
                repeat rewrite lookup_Pexp_incrPVar.
                unfold lookup_Pexp, memory_lookup_err.
                rewrite Y_ID.
                cbn.
                rewrite Heqs0.
                cbn.
                reflexivity.
              }
              rewrite H0.
              apply H.

              unfold lookup_Pexp, memory_lookup_err.
              rewrite Y_ID.
              cbn.

              apply Option_equiv_eq in Heqo0.
              eapply mem_write_safe with (y_i:=t_id) in Heqo0; [| reflexivity].
              rewrite Heqo0 by congruence.
              rewrite Heqs0.
              reflexivity.
            **
              intros.
              unfold lookup_Pexp, memory_lookup_err in Y_LoopNTM.
              rewrite Y_ID in Y_LoopNTM.
              simpl bind in Y_LoopNTM.
              subst init_m.
              rewrite memory_lookup_memory_set_neq in Y_LoopNTM by congruence.
              rewrite memory_lookup_memory_set_eq in Y_LoopNTM by congruence.
              cbn in Y_LoopNTM.
              inl_inr_inv.
              rewrite <-Y_LoopNTM.
              subst y_initm.
              unfold mem_lookup, mem_union.
              rewrite NP.F.map2_1bis by reflexivity.
              rewrite mem_const_block_find_oob by assumption.
              reflexivity.
        --
          (* k is within bounds *)
          constructor 2.
          ++
            apply mem_in_mem_lookup.
            rewrite <-mem_merge_with_def_as_Union.
            right.
            eapply out_mem_fill_pattern; try eassumption.
            apply FD.
            constructor.
            Unshelve.
            assumption.
          ++
            assert (T : mem_lookup k (mem_union
                                        (mem_merge_with_def dot init
                                                            (mem_firstn o y_loopNm)
                                                            (mem_firstn o t_rrm))
                                        y_loopNm) =
                        mem_lookup k (mem_merge_with_def dot init
                                                         (mem_firstn o y_loopNm)
                                                         (mem_firstn o t_rrm)));
              [| rewrite T; clear T].
            {
              unfold mem_lookup, mem_union.
              rewrite NP.F.map2_1bis by reflexivity.
              break_match; try reflexivity.
              enough (is_Some (@None CarrierA)) by some_none.
              rewrite <-Heqo0; clear Heqo0.
              apply mem_in_mem_lookup.
              rewrite <-mem_merge_with_def_as_Union.
              left.
              apply mem_in_mem_lookup.
              rewrite mem_firstn_lookup by assumption.
              apply mem_in_mem_lookup.
              apply y_loopNm_fill.
              assumption.
            }
            
            rewrite Y_LoopNM in OPF_LoopN.
            inversion OPF_LoopN; subst x.
            
            assert (T : lookup_Pexp (DSHnatVal n :: DSHPtrVal t_id o :: σ) rr_m (PVar 1)
                        = inr t_rrm)
              by (cbn; unfold memory_lookup_err; rewrite T_RRM; reflexivity).
            rewrite T in R; clear T.
            inversion R; subst.
            f_equiv.
            f_equiv.
            assumption.
            **
              intros j.
              specialize (H1 j).
              destruct (le_lt_dec o j).
              ---
                rewrite mem_firstn_lookup_oob by assumption.
                apply Option_equiv_eq.
                symmetry.
                apply NP.F.not_find_in_iff.

                move OPF_MM after l0.
                replace (IReduction_mem dot init
                                        (get_family_mem_op (shrink_m_op_family S_opf)) x_m)
                  with (mem_op (MSHIReduction init dot (shrink_m_op_family S_opf)) x_m)
                  in OPF_MM
                  by reflexivity.
                eapply out_mem_oob with (j0:=j) in OPF_MM.
                assumption.
                assumption.
                Unshelve.
                eapply IReduction_MFacts.
                intros.
                unfold shrink_m_op_family.
                apply FMF.
                intros.
                apply FD.
              ---
                rewrite mem_firstn_lookup by assumption.
                inversion H1.
                {
                  exfalso.
                  apply mem_not_in_mem_lookup in H0.
                  contradict H0.
                  replace (IReduction_mem dot init
                                          (get_family_mem_op (shrink_m_op_family S_opf)) x_m)
                    with (mem_op (MSHIReduction init dot (shrink_m_op_family S_opf)) x_m)
                    in OPF_MM
                    by reflexivity.
                  eapply out_mem_fill_pattern with (j0:=j) in OPF_MM.
                  apply OPF_MM.
                  cbn.
                  left.
                  unfold shrink_m_op_family.
                  cbn.
                  eapply FD.
                  constructor.
                }
                assumption.
                Unshelve.
                eapply IReduction_MFacts.
                intros.
                unfold shrink_m_op_family.
                apply FMF.
                intros.
                apply FD.
                assumption.
            **
              intros j.
              specialize (H2 j).
              destruct (le_lt_dec o j).
              ---
                rewrite mem_firstn_lookup_oob by assumption.
                apply Option_equiv_eq.
                symmetry.
                apply NP.F.not_find_in_iff.

                eapply out_mem_oob in OPF_M.
                eassumption.
                assumption.
              ---
                rewrite mem_firstn_lookup by assumption.
                inversion H2.
                {
                  exfalso.
                  exfalso.
                  apply mem_not_in_mem_lookup in H0.
                  contradict H0.
                  unshelve eapply out_mem_fill_pattern with (j0:=j) in OPF_M.
                  assumption.
                  apply OPF_M.
                  apply FD.
                  constructor.
                }
                assumption.
Qed.
