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
(* problem: these depend on MemSetoid.v, which depends on Memory.v *)
Section memory_aux.

  (* Two memory locations equivalent on all addresses except one *)
  Definition memory_equiv_except (m m': memory) (e:mem_block_id)
    := forall k, k ≢ e -> memory_lookup m k = memory_lookup m' k.
  
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
      (x_p y_p: PExpr)
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
      `{DSH_pure dop x_p y_p}
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
        apply eq_inr_is_OK in Heqe. rename Heqe into H1.
        apply eq_inr_is_OK in Heqe0. rename Heqe0 into H2.
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
        apply eq_inr_is_OK in Heqe. rename Heqe into H1.
        apply eq_inr_is_OK in Heqe0. rename Heqe0 into H2.
        clear Heqe1 c c0.
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
        rewrite Heqe0, H.
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

        clear - Heqe1 H.
        rewrite Heqe1, H.
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

        rewrite Heqe1, H.
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
        apply err_equiv_eq in Heqe.
        contradict Heqe.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe0.
        clear - Heqe0; rename Heqe0 into H.
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
        apply err_equiv_eq in Heqe.
        contradict Heqe.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe0.
        clear - Heqe0; rename Heqe0 into H.
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
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe2.
        clear - Heqe2; rename Heqe2 into H,
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
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe2.
        clear - Heqe2; rename Heqe2 into H,
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
        apply err_equiv_eq in Heqe.
        contradict Heqe.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe0.
        clear - Heqe0; rename Heqe0 into H.
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
        apply err_equiv_eq in Heqe.
        contradict Heqe.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe0.
        clear - Heqe0; rename Heqe0 into H.
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
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe2.
        clear - Heqe2; rename Heqe2 into H,
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
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe2.
        clear - Heqe2; rename Heqe2 into H,
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
      unfold mem_lookup_err, trywith in Heqe.
      break_match; try inversion Heqe; try some_none.
    -
      err_eq_to_equiv_hyp.
      contradict Heqe0.
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
      unfold mem_lookup_err, trywith in Heqe.
      break_match; try inversion Heqe; try some_none.
    -
      assert (T : n < S n) by omega.
      specialize (H n T).
      destruct H as [a [b [L1 [L2 S]]]].
      unfold mem_lookup_err, trywith in Heqe0.
      break_match; try inversion Heqe0; try some_none.
    -
      err_eq_to_equiv_hyp.
      contradict Heqe1.
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
        unfold mem_lookup_err in Heqe, Heqe0.
        try rewrite Heqo in Heqe; try rewrite Heqo in Heqe0.
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
        all: unfold mem_lookup_err in Heqe, Heqe0.
        all: try rewrite Heqo in Heqe; try rewrite Heqo in Heqe0.
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
    DSH_pure (DSHAssign (x_p, x_n) (y_p, y_n)) x_p y_p.
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
      apply memory_lookup_err_inr_is_Some in Heqe2.
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
       (BP : DSH_pure (DSHAssign (x_p, NConst 0) (y_p, y_n)) x_p y_p)
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
      unfold mem_lookup_err, trywith in Heqe2.
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
    unfold mem_lookup_err, trywith in Heqe2.
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
       (BP : DSH_pure (DSHAssign (x_p, x_n) (y_p, NConst 0)) x_p y_p)
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
    unfold mem_lookup_err, trywith in Heqe2.
    break_match; try inl_inr.
    rewrite <-Heqo1, <-Heqo2.
    unfold mem_lookup.
    rewrite X.
    inversion MX.
    apply H1.
  -
    unfold mem_lookup_err, trywith in Heqe2.
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
      unfold mem_lookup_err, trywith in Heqe2.
      break_match; try inl_inr.
      inversion Heqe2; subst.
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
    DSH_pure (DSHIMap nn x_p y_p a) x_p y_p.
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
      apply memory_lookup_err_inr_is_Some in Heqe2.
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
       (P : DSH_pure (DSHIMap n x_p y_p df) x_p y_p)
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
      clear - MX Heqe1.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MX in Heqe1.
      some_none.
    +
      clear - MB Heqe2.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MB in Heqe2.
      some_none.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqe1, <-Heqe2 in *.
      clear Heqe1 Heqe2 m2 m3.

      rename Heqe3 into E.

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
      rewrite <-Heqe1, <-Heqe2 in *.
      clear Heqe1 Heqe2 m2 m3.

      rename Heqe3 into ME.
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
    rewrite <-Heqe1, <-Heqe2 in *.
    clear Heqe1 Heqe2 m2 m3.

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
      contradict Heqe3.
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
    DSH_pure (DSHBinOp o x_p y_p a) x_p y_p.
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
      apply memory_lookup_err_inr_is_Some in Heqe2.
      assumption.
  -
    intros σ m m' fuel E y_i P.
    destruct fuel; cbn in E; [some_none |].

    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    err_eq_to_equiv_hyp.
    rewrite P in Heqe0, Heqe2, E.
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
       (BP: DSH_pure (DSHBinOp o x_p y_p df) x_p y_p)
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
      clear - MX Heqe1.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MX in Heqe1.
      some_none.
    +
      clear - MB Heqe2.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MB in Heqe2.
      some_none.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqe1, <-Heqe2 in *.
      clear Heqe1 Heqe2 m2 m3.

      rename Heqe3 into E.

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
      rewrite <-Heqe1, <-Heqe2 in *.
      clear Heqe1 Heqe2 m2 m3.

      rename Heqe3 into ME.
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
    rewrite <-Heqe1, <-Heqe2 in *.
    clear Heqe1 Heqe2 m2 m3.

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
      contradict Heqe3.
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
    DSH_pure (DSHPower n (x_p, x_n) (y_p, y_n) a initial) x_p y_p.
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
      apply memory_lookup_err_inr_is_Some in Heqe2.
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
    all: try rewrite X in Heqe.
    all: try rewrite Y in Heqe0.
    all: try rewrite Heqe in *.
    all: try rewrite Heqe0 in *.
    all: try inl_inr; repeat inl_inr_inv.
    all: rewrite Heqe2 in *.
    all: rewrite Heqe3 in *.

    (* AExp evaluation (evalBinCType *)
    all: rewrite M, Σ, F in Heqe1.
    all: rewrite Heqe1 in Heqe4.
    all: try inl_inr; repeat inl_inr_inv.

    eapply IHn.
    rewrite Y, Heqe4.
    reflexivity.
Qed.

Ltac mem_lookup_err_to_option :=
  repeat
    match goal with
    | [ H: memory_lookup_err _ _ _ ≡ inr _ |- _] =>
      apply memory_lookup_err_inr_is_Some in H
    | [ H: memory_lookup_err _ _ _ = inr _ |- _] =>
      apply memory_lookup_err_inr_Some in H
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
       (PD : DSH_pure (DSHPower nx (x_p, NConst 0) (y_p, NConst 0) a init) x_p y_p)
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
      rename m0 into pm, Heqe into PM,
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
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqe1.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqe2.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        unfold memory_lookup_err, trywith in *.
        rewrite X_M' in Heqe1.
        rewrite Y_M' in Heqe2.
        repeat inl_inr_inv.
        subst.
        cbn in Heqe4.
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
      rewrite N in DOP.
      repeat break_match_hyp; try inl_inr;
        repeat inl_inr_inv; repeat some_inv; try some_none; subst.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqe1.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        repeat err_eq_to_equiv_hyp.
        apply memory_lookup_err_inl_None in Heqe2.
        repeat eq_to_equiv_hyp.
        some_none.
      *
        unfold memory_lookup_err, trywith in *.
        rewrite X_M' in Heqe1.
        rewrite Y_M' in Heqe2.
        repeat inl_inr_inv.
        subst.

        rename Heqe3 into EV.
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
            unfold mem_lookup_err,trywith in Heqe.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            unfold mem_lookup_err,trywith in Heqe0.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            destruct FA.
            specialize (bin_equiv0 c0 c).
            rewrite Heqe1 in bin_equiv0.
            inl_inr.
        --
          revert IHn EV.
          generalize (S n) as z.
          intros z IHn EV.
          cbn in EV.
          repeat break_match_hyp; try inl_inr;
            repeat inl_inr_inv; repeat some_inv; try some_none; subst.
          ++
            unfold mem_lookup_err,trywith in Heqe.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            unfold mem_lookup_err,trywith in Heqe0.
            break_match_hyp; try inl_inr.
            some_none.
          ++
            destruct FA.
            specialize (bin_equiv0 c0 c).
            rewrite Heqe1 in bin_equiv0.
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
    cbn in DOP; some_inv; rename H0 into DOP.
    rewrite N in DOP.
    repeat break_match; try inl_inr.

    destruct n;[cbn in MOP;some_none|].
    cbn in MOP.
    unfold mem_op_of_hop in MOP.
    repeat break_match_hyp; try inl_inr;
      repeat inl_inr_inv; repeat some_inv; try some_none; subst.

    rename Heqe3 into EV.

    unfold memory_lookup_err, trywith in *.
    rewrite X_M' in Heqe1.
    rewrite Y_M' in Heqe2.
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
      unfold mem_lookup_err,trywith in Heqe.
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
       {x_p y_p : PExpr}
       (P : DSH_pure dop (incrPVar 0 x_p) (incrPVar 0 y_p))

  :
    DSH_pure (DSHLoop n dop) x_p y_p.
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
  all: rewrite Heqe in *.
  all: try inl_inr; inl_inr_inv.
  all: rewrite Heqe0 in *.
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
       {DP : DSH_pure dop (incrPVar 0 x_p) (incrPVar 0 y_p)}
       {LP : DSH_pure (DSHLoop n dop) x_p y_p}
       (FC : forall t m, @MSH_DSH_compat _ _ (opf t) dop
                                  ((DSHnatVal (proj1_sig t)) :: σ)
                                  m (incrPVar 0 x_p) (incrPVar 0 y_p) DP)
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
    rewrite Y_M.
    constructor 1.
    reflexivity.
    reflexivity.
  -
    intros.
    simpl evalDSHOperator.
    repeat break_match; subst.
    +
      (* evalDSHOperator errors *)
      pose (opf' := shrink_m_op_family opf).
      assert (T1 : DSH_pure (DSHLoop n dop) x_p y_p) by (apply Loop_DSH_pure; assumption).
      assert (T2: (∀ (t : FinNat n) (m : memory),
                      MSH_DSH_compat (opf' t) dop (DSHnatVal (` t) :: σ) m 
                                     (incrPVar 0 x_p) (incrPVar 0 y_p))).
      {
        clear - FC.
        subst opf'.
        intros.
        unfold shrink_m_op_family.
        specialize (FC (mkFinNat (le_S (proj2_sig t))) m).
        enough (T : (` (mkFinNat (le_S (proj2_sig t)))) ≡ (` t))
          by (rewrite T in FC; assumption).
        cbv.
        repeat break_match; congruence.
      }
      specialize (IHn opf' T1 T2 m X_M Y_M); clear T1 T2.
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
      assert (T1 : DSH_pure (DSHLoop n dop) x_p y_p) by (apply Loop_DSH_pure; assumption).
      assert (T2: (∀ (t : FinNat n) (m : memory),
                      MSH_DSH_compat (opf' t) dop (DSHnatVal (` t) :: σ) m 
                                     (incrPVar 0 x_p) (incrPVar 0 y_p))).
      {
        clear - FC.
        subst opf'.
        intros.
        unfold shrink_m_op_family.
        specialize (FC (mkFinNat (le_S (proj2_sig t))) m).
        enough (T : (` (mkFinNat (le_S (proj2_sig t)))) ≡ (` t))
          by (rewrite T in FC; assumption).
        cbv.
        repeat break_match; congruence.
      }
      specialize (IHn opf' T1 T2 m X_M Y_M); clear T1 T2.
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

      specialize (FC (mkFinNat (Nat.lt_succ_diag_r n)) loop_m).
      cbn in FC.
      inversion_clear FC as [F].

      assert (T1 : lookup_Pexp (DSHnatVal n :: σ) loop_m (incrPVar 0 x_p) = inr x_m).
      {
        rewrite lookup_Pexp_incrPVar.
        clear - Heqo0 DP Y_M X_M XY.
        pose proof @Loop_DSH_pure n dop x_p y_p DP.
        inversion_clear H as [T C]; clear T.
        eq_to_equiv_hyp.
        specialize (C σ m loop_m (estimateFuel (DSHLoop n dop)) Heqo0).
        unfold lookup_Pexp in Y_M.
        cbn in Y_M; break_match; try inl_inr.
        assert (T : inr m0 = inr m0) by reflexivity.
        specialize (C m0 T); clear T.
        unfold memory_equiv_except in *.
        clear - X_M C XY.
        unfold lookup_Pexp, memory_lookup_err in *; cbn in *.
        destruct (evalPexp σ x_p); try inl_inr.
        assert (m1 ≢ m0)
          by (intros T; contradict XY; f_equal; assumption).
        specialize (C m1 H).
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


(** * MSHIReduction *)

(* TODO: move *)
Lemma memory_set_overwrite (m : memory) (k : mem_block_id) (mb mb' : mem_block) :
  memory_set (memory_set m k mb) k mb' = memory_set m k mb'.
Proof.
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

Lemma memory_remove_memory_set (m : memory) (k : mem_block_id) (mb : mem_block) :
  memory_remove (memory_set m k mb) k = memory_remove m k.
Proof.
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

Global Instance Seq_DSH_pure
       {dop1 dop2 : DSHOperator}
       {x_p y_p : PExpr}
       (P1: DSH_pure dop1 x_p y_p)
       (P2: DSH_pure dop2 x_p y_p)
  :
    DSH_pure (DSHSeq dop1 dop2) x_p y_p.
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

    inversion P1; clear P1 mem_write_safe0;
      rename mem_stable0 into P1.
    apply P1 with (k:=k) in M1; clear P1.
    inversion P2; clear P2 mem_write_safe0;
      rename mem_stable0 into P2.
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

    inversion P1; clear P1 mem_stable0;
      rename mem_write_safe0 into P1.
    eapply P1 with (y_i := y_i) in M1; [| assumption].
    inversion P2; clear P2 mem_stable0;
      rename mem_write_safe0 into P2.
    eapply P2 with (y_i := y_i) in M2; [| assumption].
    clear - M1 M2.
    eapply memory_equiv_except_trans; eassumption.
Qed.

Global Instance MemMap2_DSH_pure
       {x_p x0_p x1_p y_p : PExpr}
       {n : nat}
       {a : AExpr}
  :
    DSH_pure (DSHMemMap2 n x0_p x1_p y_p a) x_p y_p.
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
       {x_p y_p : PExpr}
       (P : DSH_pure dop x_p (incrPVar 0 y_p))
  :
  DSH_pure (DSHAlloc size dop) x_p y_p.
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
       {x_p y_p : PExpr}
       {init : CarrierA}
  :
    DSH_pure (DSHMemInit size y_p init) x_p y_p.
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

Global Instance IReduction_DSH_pure
       {no nn : nat}
       {x_p y_p y_p'': PExpr}
       {init : CarrierA}
       {rr : DSHOperator}
       {df : AExpr}
       (Y: y_p'' ≡ incrPVar 0 (incrPVar 0 y_p))
       (P: DSH_pure rr
                    (incrPVar 0 (incrPVar 0 x_p)) y_p'')
  :
    DSH_pure (DSHAlloc no
                       (DSHSeq
                          (DSHMemInit no (PVar 0) init)
                          (DSHLoop nn
                                   (DSHSeq
                                      rr
                                      (DSHMemMap2 no (PVar 1)
                                                  y_p''
                                                  y_p''
                                                  df)))))
             x_p y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    destruct fuel; [inversion Heqo |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    destruct fuel; [inversion Heqo |].
    induction nn.
    +
      cbn in *.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      admit.
    +
      admit.
  -
    admit.
Admitted.

Global Instance IReduction_MSH_DSH_compat
       {i o n: nat}
       {init : CarrierA}
       {dot: CarrierA -> CarrierA -> CarrierA}
       {pdot: Proper ((=) ==> (=) ==> (=)) dot}
       {op_family: @MSHOperatorFamily i o n}
       {df : AExpr}
       {x_p y_p y_p'': PExpr}
       {Y : y_p'' ≡ incrPVar 0 (incrPVar 0 y_p)}
       {rr : DSHOperator}
       {σ : evalContext}
       {m : memory}
       {DP}
       (P: DSH_pure rr (incrPVar 0 (incrPVar 0 x_p)) y_p'')
       (FC : forall tmpk t,
           tmpk ≡ memory_next_key m ->
           @MSH_DSH_compat _ _ (op_family t) rr
                           (DSHnatVal (proj1_sig t) :: DSHPtrVal tmpk o :: σ)
                           (memory_set m tmpk (mem_empty))
                           (incrPVar 0 (incrPVar 0 x_p)) y_p'' P)
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i o n initial dot pdot op_family)
      (DSHAlloc o
                (DSHSeq
                   (DSHMemInit o (PVar 0) init)
                   (DSHLoop n
                            (DSHSeq
                               rr
                               (DSHMemMap2 o (PVar 1)
                                           y_p''
                                           y_p''
                                           df)))))
      σ m x_p y_p DP.
Admitted.


(** * MSHCompose *)
Global Instance Compose_DSH_pure
         {n: nat}
         {x_p y_p: PExpr}
         {dop1 dop2: DSHOperator}
         (P2: DSH_pure dop2 (incrPVar 0 x_p) (PVar 0))
         (P1: DSH_pure dop1 (PVar 0) (incrPVar 0 y_p))
  : DSH_pure (DSHAlloc n (DSHSeq dop2 dop1)) x_p y_p.
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
    rename Heqo into D1, Heqe0 into D2.
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
         (P: DSH_pure (DSHAlloc o2 (DSHSeq dop2 dop1)) x_p y_p)
         (P2: DSH_pure dop2 (incrPVar 0 x_p) (PVar 0))
         (P1: DSH_pure dop1 (PVar 0) (incrPVar 0 y_p))
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
      rewrite Heqe3.
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
      rewrite Heqe3.
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
      rewrite Heqe2.

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
      rewrite Heqe3.
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
      rewrite Heqe2.

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
      rewrite Heqe2.
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
      rewrite Heqe2.
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
      rewrite Heqe1.

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
      rewrite Heqe0.
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
        rewrite Heqe3.
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
      rewrite Heqe2.

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
        rewrite Heqe3.
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
         (P: DSH_pure (DSHSeq dop1 dop2) x_p y_p)
         (D : herr_f nat nat (compose2 not equiv) (evalPexp σ x_p) (evalPexp σ y_p))
         (P1: DSH_pure dop1 x_p y_p)
         (P2: DSH_pure dop2 x_p y_p)
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
