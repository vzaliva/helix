Require Import Coq.Arith.Arith.
Require Import Omega.
Require Import Psatz.
Require Import CoLoR.Util.Nat.NatUtil.

Require Import Helix.HCOL.CarrierType.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

(* When proving concrete functions we need to use some implementation defs from this packages *)
Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.FinNat.

Require Import MathClasses.misc.util.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

Require Import Helix.Util.OptionSetoid.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.Tactics.HelixTactics.

Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

(* Shows relations of cells before ([b]) and after ([a]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [d] *)
Inductive MemOpDelta (b a d: option CarrierA) : Prop :=
| MemPreserved: is_None d -> b = a -> MemOpDelta b a d (* preserving memory state *)
| MemExpected: is_Some d -> a = d -> MemOpDelta b a d (* expected results *).

(* Shows relations of memory blocks before ([mb]) and after ([ma]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [md] *)
Definition SHCOL_DSHCOL_mem_block_equiv (mb ma md: mem_block) : Prop :=
  forall i,
    MemOpDelta
      (mem_lookup i mb)
      (mem_lookup i ma)
      (mem_lookup i md).

Require Import CoLoR.Util.Relation.RelUtil.

(*
TODO: move
*)
Section opt_p.

  Variables (A : Type) (P : A -> Prop).

  (* lifting Predicate to option. None is not allowed *)
  Inductive opt_p : (option A) -> Prop :=
  | opt_p_intro : forall x, P x -> opt_p (Some x).

  (* lifting Predicate to option. None is allowed *)
  Inductive opt_p_n : (option A) -> Prop :=
  | opt_p_None_intro: opt_p_n None
  | opt_p_Some_intro : forall x, P x -> opt_p_n (Some x).

End opt_p.
Arguments opt_p {A} P.
Arguments opt_p_n {A} P.

(* Extension to [option _] of a heterogenous relation on [A] [B]
TODO: move
*)
Section hopt.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Reflexive on [None]. *)
  Inductive hopt_r : (option A) -> (option B) -> Prop :=
  | hopt_r_None : hopt_r None None
  | hopt_r_Some : forall a b, R a b -> hopt_r (Some a) (Some b).

  (** Non-Reflexive on [None]. *)
  Inductive hopt : (option A) -> (option B) -> Prop :=
  | hopt_Some : forall a b, R a b -> hopt (Some a) (Some b).

  (** implication-like. *)
  Inductive hopt_i : (option A) -> (option B) -> Prop :=
  | hopt_i_None_None : hopt_i None None
  | hopt_i_None_Some : forall a, hopt_i None (Some a)
  | hopt_i_Some : forall a b, R a b -> hopt_i (Some a) (Some b).

End hopt.
Arguments hopt {A B} R.
Arguments hopt_r {A B} R.
Arguments hopt_i {A B} R.

Definition lookup_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  a <- evalPexp σ p ;;
      memory_lookup m a.

Definition valid_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  opt_p (fun k => mem_block_exists k m) (evalPexp σ p).

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
      subst.
      constructor.
      rewrite <- Em.
      apply H1.
    +
      inversion H.
  -
    unfold valid_Pexp in *.
    destruct (evalPexp s1 p1).
    +
      inversion H.
      subst.
      constructor.
      rewrite Em.
      apply H1.
    +
      inversion H.
Qed.

(*
   - [evalPexp σ p] must not to fail
   - [memory_lookup] must succeed
*)
Definition blocks_equiv_at_Pexp (σ0 σ1:evalContext) (p:PExpr): rel (memory)
  := fun m0 m1 =>
       opt (fun a b => (opt equiv (memory_lookup m0 a) (memory_lookup m1 b)))
             (evalPexp σ0 p) (evalPexp σ1 p).

(* This relations represents consistent memory/envirnment combinations. That means all pointer variables should resolve to existing memory blocks *)
Inductive EnvMemoryConsistent: evalContext -> memory -> Prop :=
| EmptyEnvConsistent: forall m, EnvMemoryConsistent [] m
| DSHPtrValConsistent: forall σ m a,
    mem_block_exists a m ->
    EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHPtrVal a :: σ) m
(* the remaining case does not depend on memory and just recurse over environment *)
| DSHnatValConsistent : forall σ m n, EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHnatVal n :: σ) m
| DSHCarrierAValConsistent: forall σ m a, EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHCarrierAVal a :: σ) m
| DSHMemValConsistent: forall σ b m, EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHMemVal b :: σ) m.


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
        evalDSHOperator σ d m fuel = Some m' ->
        forall k, mem_block_exists k m <-> mem_block_exists k m';

      (* depends only [x_p], which must be valid in [σ], in all
         consistent memory configurations *)
      mem_read_safe: forall σ0 σ1 m0 m1 fuel,
          (*
            EnvMemoryConsistent σ0 m0 ->
            EnvMemoryConsistent σ1 m1 ->
           *)
            valid_Pexp σ0 m0 y_p ->
            valid_Pexp σ1 m1 y_p ->
        blocks_equiv_at_Pexp σ0 σ1 x_p m0 m1 ->
        opt_r
          (blocks_equiv_at_Pexp σ0 σ1 y_p)
          (evalDSHOperator σ0 d m0 fuel)
          (evalDSHOperator σ1 d m1 fuel);

      (* modifies only [y_p], which must be valid in [σ] *)
      mem_write_safe: forall σ m m' fuel,
          evalDSHOperator σ d m fuel = Some m' ->
          (forall y_i , evalPexp σ y_p = Some y_i ->
                   memory_remove m y_i = memory_remove m' y_i)
    }.


(* Given MSHCOL and DSHCOL operators are quivalent, if wrt [x_i] and
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
          (lookup_Pexp σ m x_p ≡ Some mx) (* input exists *) ->
          (lookup_Pexp σ m y_p ≡ Some mb) (* output before *) ->

          (hopt_r (fun md (* memory diff *) m' (* memory state after execution *) =>
                     opt_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md
                           ) (lookup_Pexp σ m' y_p)
                  ) (mem_op mop mx) (evalDSHOperator σ dop m (estimateFuel dop)));
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

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive MExpr_typecheck: MExpr -> evalContext -> Prop :=
| MVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHMemBlock -> MExpr_typecheck (MVar n) σ
| MConst_tc (σ: evalContext) {a}: MExpr_typecheck (MConst a) σ.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive PExpr_typecheck: PExpr -> evalContext -> Prop :=
| PVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHPtr -> PExpr_typecheck (PVar n) σ
| PConst_tc (σ: evalContext) {a}: PExpr_typecheck (PConst a) σ.

(* Check if [AExpr] is properly typed in given evaluation context *)
Inductive AExpr_typecheck: AExpr -> evalContext -> Prop
  :=
  | AVar_tc (σ: evalContext) (n:var_id):
      context_pos_typecheck σ n DSHCarrierA ->  AExpr_typecheck (AVar n) σ
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

Class MSH_DSH_BinCarrierA_compat
      {o: nat}
      (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
      (σ: evalContext)
      (df : DSHIBinCarrierA)
  :=
    {
      ibin_typechecks:
        forall n a b,
          AExpr_typecheck df (DSHCarrierAVal b :: DSHCarrierAVal a :: DSHnatVal n :: σ);

      ibin_equiv:
        forall nc a b, evalIBinCarrierA σ df (proj1_sig nc) a b = Some (f nc a b)
    }.

Instance Abs_MSH_DSH_BinCarrierA_compat
  :
    forall σ,
    MSH_DSH_BinCarrierA_compat
      (λ i (a b : CarrierA),
       IgnoreIndex abs i
                   (HCOL.Fin1SwapIndex2 (n:=2)
                                        jf
                                        (IgnoreIndex2 sub) i a b))
      σ
      (AAbs (AMinus (AVar 1) (AVar 0))).
Proof.
  split.
  -
    intros n a b.
    repeat constructor.
  -
    intros nc a b.
    unfold evalIBinCarrierA.
    f_equiv.
Qed.

Lemma evalDSHBinOp_mem_lookup_mx
      {n off: nat}
      {df : DSHIBinCarrierA}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (E: evalDSHBinOp n off df σ mx mb ≡ Some ma)
      (k: nat)
      (kc:k<n):
  is_Some (mem_lookup k mx) /\ is_Some (mem_lookup (k+off) mx).
Proof.
  apply eq_Some_is_Some in E.
  revert mb E k kc.
  induction n; intros.
  -
    inversion kc.
  -
    destruct (Nat.eq_dec k n).
    +
      subst.
      simpl in *.
      repeat break_match_hyp; try some_none.
      split;constructor.
    +
      simpl in *.
      repeat break_match_hyp; try some_none.
      apply eq_Some_is_Some in Heqo. rename Heqo into H1.
      apply eq_Some_is_Some in Heqo0. rename Heqo0 into H2.
      clear Heqo1 c c0.
      apply IHn with (mb:=mem_add n c1 mb); clear IHn.
      *
        apply E.
      *
        lia.
Qed.

(* TODO: Move to Memory.v *)
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

Fact evalDSHBinOp_preservation
     {n off k: nat}
     {kc: k>=n}
     {df : DSHIBinCarrierA}
     {σ : evalContext}
     {mx ma mb : mem_block}
     {c : CarrierA}:
  evalDSHBinOp n off df σ mx (mem_add k c mb) = Some ma
  → mem_lookup k ma = Some c.
Proof.
  revert mb k kc.
  induction n; intros mb k kc E.
  -
    simpl in *.
    some_inv.
    unfold mem_lookup, mem_add in *.
    rewrite <- E.
    apply Option_equiv_eq.
    apply NP.F.add_eq_o.
    reflexivity.
  -
    simpl in E.
    repeat break_match_hyp; try some_none.
    apply IHn with (mb:=mem_add n c2 mb).
    lia.
    rewrite mem_add_comm by auto.
    apply E.
Qed.

Lemma evalDSHBinOp_nth
      {n off: nat}
      {df : DSHIBinCarrierA}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (k: nat)
      (kc: k<n)
      {a b : CarrierA}:
  (mem_lookup k mx ≡ Some a) ->
  (mem_lookup (k + off) mx ≡ Some b) ->
  (evalDSHBinOp n off df σ mx mb ≡ Some ma) ->
  (mem_lookup k ma = evalIBinCarrierA σ df k a b).
Proof.
  intros A B E.
  revert mb a b A B E.
  induction n; intros.
  -
    inversion kc.
  -
    simpl in *.
    repeat break_match_hyp; try some_none.
    destruct (Nat.eq_dec k n).
    +
      clear IHn.
      subst k.
      rewrite Heqo in A. clear Heqo.
      rewrite Heqo0 in B. clear Heqo0.
      repeat some_inv.
      subst_max.
      rewrite Heqo1. clear Heqo1.
      clear - E.
      apply Option_equiv_eq in E.
      unshelve eapply (evalDSHBinOp_preservation E).
      lia.
    +
      apply IHn with (mb:=mem_add n c1 mb); auto.
      lia.
Qed.

Lemma evalDSHBinOp_oob_preservation
      {n off: nat}
      {df : DSHIBinCarrierA}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (ME: evalDSHBinOp n off df σ mx mb ≡ Some ma):
  ∀ (k : NM.key) (kc:k>=n), mem_lookup k mb = mem_lookup k ma.
Proof.
  intros k kc.
  revert mb ME.
  induction n; intros.
  -
    inversion kc; simpl in ME; some_inv; reflexivity.
  -
    simpl in *.
    repeat break_match_hyp; try some_none.
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

Lemma evalDSHBinOp_is_Some
      (off n: nat)
      (df : DSHIBinCarrierA) (σ : evalContext)
      (mx mb : mem_block)
      (DX: ∀ k (kc: k < (n + off)%nat), is_Some (mem_lookup k mx))
      (FV: ∀ k (kc: k < n) (a b : CarrierA), is_Some (evalIBinCarrierA σ df k a b))
  :
    is_Some (evalDSHBinOp n off df σ mx mb).
Proof.
  revert mb.
  induction n.
  -
    constructor.
  -
    intros mb.
    simpl.
    repeat break_match; simpl in *.
    +
      apply IHn.
      intros k kc.
      apply DX.
      lia.
      intros k kc a b.
      apply FV.
      lia.
    +
      contradict Heqo1.
      apply is_Some_ne_None.
      apply FV.
      lia.
    +
      contradict Heqo0.
      apply is_Some_ne_None.
      apply DX.
      lia.
    +
      contradict Heqo.
      apply is_Some_ne_None.
      apply DX.
      lia.
Qed.

Lemma evalDSHBinOp_is_None
      (off n: nat)
      (nz: n≢0)
      (df : DSHIBinCarrierA) (σ : evalContext)
      (mx mb : mem_block)
      (DX: exists k (kc:k<n),
          is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx))
  :
    is_None (evalDSHBinOp n off df σ mx mb).
Proof.
  revert mb DX.
  induction n; intros mb DX.
  -
    crush.
  -
    destruct DX as [k [kc DX]].
    destruct (Nat.eq_dec k n).
    +
      clear IHn.
      subst k.
      simpl.
      repeat break_match; try constructor.
      crush.
    +
      simpl.
      repeat break_match; try constructor.
      apply IHn.
      lia.
      exists k.
      assert(k < n) as kc1 by lia.
      exists kc1.
      apply DX.
Qed.

Global Instance BinOp_DSH_pure:
  DSH_pure (DSHBinOp o x_i y_i df) x_i y_i.
Proof.
  split.
Admitted.

Global Instance BinOp_MSH_DSH_compat
       {o: nat}
       (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
       `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
       (x_p y_p : PExpr)
       (df : DSHIBinCarrierA)
       (σ: evalContext)
       (m: memory)
       `{MSH_DSH_BinCarrierA_compat _ f σ df}
  :
    MSH_DSH_compat (MSHBinOp f) (DSHBinOp o x_p y_p df) σ m x_p y_p.
Proof.
  split.
  intros mx mb MX MB.
  simpl.
  destruct (mem_op_of_hop (HCOL.HBinOp f) mx) as [md|] eqn:MD.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match; subst; try some_none.
    +
      constructor.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      constructor.
      repeat some_inv.
      subst m3 m2.
      rename Heqo4 into ME.
      intros k.

      unfold mem_op_of_hop in MD.
      break_match_hyp; try some_none.
      inversion_clear MD. clear md.
      rename t into vx.

      unfold avector_to_mem_block.

      avector_to_mem_block_to_spec md HD OD.
      destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
      *
        (* k<o, which is normal *)
        clear OD.
        simpl in *.
        rewrite HD with (ip:=kc).
        clear HD md.
        apply MemExpected.
        --
          unfold is_Some.
          tauto.
        --
          inversion_clear H as [_ FV].

          assert (k < o + o)%nat as kc1 by omega.
          assert (k + o < o + o)%nat as kc2 by omega.
          rewrite HBinOp_nth with (jc1:=kc1) (jc2:=kc2).

          pose proof (evalDSHBinOp_mem_lookup_mx ME k kc) as [A B].

          apply is_Some_def in A. destruct A as [a A].
          apply is_Some_def in B. destruct B as [b B].

          rewrite (evalDSHBinOp_nth k kc A B ME).
          specialize FV with (nc:=mkFinNat kc) (a:=a) (b:=b).
          simpl in FV.
          rewrite FV.

          pose proof (mem_block_to_avector_nth Heqo4 (kc:=kc1)) as MVA.
          pose proof (mem_block_to_avector_nth Heqo4 (kc:=kc2)) as MVB.

          repeat f_equiv.
          apply Some_inj_equiv ; rewrite <- A; apply Option_equiv_eq; apply MVA.
          apply Some_inj_equiv; rewrite <- B; apply Option_equiv_eq; apply MVB.
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
          apply (evalDSHBinOp_oob_preservation ME),kc.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)
      exfalso.
      repeat some_inv.
      subst m3. subst m2.
      rename Heqo4 into E.

      apply eq_Some_is_Some in MD.
      pose proof (mem_op_of_hop_x_density MD) as DX.
      clear MD pF.

      inversion_clear H as [_ FV].

      contradict E.
      apply is_Some_ne_None.
      eapply evalDSHBinOp_is_Some; eauto.
      intros k kc a b.
      specialize (FV (FinNat.mkFinNat kc) a b).
      apply equiv_Some_is_Some in FV.
      apply FV.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match; try some_none.
    +
      apply Some_ne_None in Heqo2.
      contradict Heqo2.
      repeat some_inv. subst m3 m2.
      unfold mem_op_of_hop in MD.
      break_match_hyp; try some_none.
      clear MD.
      rename Heqo2 into MX.
      unfold mem_block_to_avector in MX.
      apply vsequence_Vbuild_eq_None in MX.
      apply is_None_def.
      destruct o.
      *
        destruct MX as [k [kc MX]].
        inversion kc.
      *
        contradict Heqo4.
        apply None_ne_Some.
        apply is_None_def.


        apply evalDSHBinOp_is_None.
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
    +
      constructor.
Qed.

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
      (NY0: evalPexp σ0 y_p ≢ Some t0_i)
      (NY1: evalPexp σ1 y_p ≢ Some t1_i):
  blocks_equiv_at_Pexp σ0 σ1 y_p m0'' m1''
  → blocks_equiv_at_Pexp σ0 σ1 y_p (memory_remove m0'' t0_i) (memory_remove m1'' t1_i).
Proof.
  intros EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 y_p), (evalPexp σ1 y_p).
  -
    constructor.
    inversion_clear EE.
    rewrite Some_neq in NY0.
    rewrite Some_neq in NY1.
    unfold memory_lookup, memory_remove in *.
    rewrite 2!NP.F.remove_neq_o; auto.
  -
    inversion EE.
  -
    inversion EE.
  -
    inversion EE.
Qed.

(* TODO: maybe not needed *)
Definition decrPVar (p: PExpr) (NP: p ≢ PVar 0): PExpr :=
  match p with
  | PVar (S v) => PVar v
  | _ => p
  end.

(* TODO: maybe not needed *)
Lemma blocks_equiv_at_Pexp_decrPVar
      (p : PExpr)
      (σ0 σ1: evalContext)
      (m0 m1 : memory)
      (t0 t1: mem_block_id)
      (NP: p ≢ PVar 0)
  :
    blocks_equiv_at_Pexp (DSHPtrVal t0 :: σ0) (DSHPtrVal t1 :: σ1) p m0 m1 <->
    blocks_equiv_at_Pexp σ0 σ1 (decrPVar p NP) m0 m1.
Proof.
  split; intros H.
  -
    unfold blocks_equiv_at_Pexp in *.
    inversion H; clear H.
    symmetry in H0, H1.
    destruct p.
    +
      simpl in H0; repeat break_match_hyp; try some_none.
      simpl in H1; repeat break_match_hyp; try some_none.
      some_inv; subst a0.
      some_inv; subst a.
      clear d0 Heqd1 d Heqd0.
      rename Heqo into H0, Heqo0 into H1.
      destruct v.
      *
        congruence.
      *
        simpl in H0, H1.
        simpl.
        rewrite H0, H1.
        constructor.
        apply H2.
    +
      simpl in H0, H1.
      repeat some_inv.
      subst_max.
      constructor.
      apply H2.
  -
    unfold blocks_equiv_at_Pexp in *.
    inversion H; clear H.
    symmetry in H0, H1.
    destruct p.
    +
      simpl in H0; repeat break_match_hyp; try some_none.
      *
        congruence.
      *
        simpl in H0; repeat break_match_hyp; try some_none.
        simpl in H1; repeat break_match_hyp; try some_none.
        subst v.
        repeat some_inv.
        subst_max.
        simpl.
        rewrite Heqo, Heqo0.
        constructor.
        apply H2.
    +
      simpl in H0, H1.
      repeat some_inv.
      subst_max.
      constructor.
      apply H2.
Qed.

Lemma blocks_equiv_at_Pexp_add_mem
      (p : PExpr)
      (σ0 σ1 : evalContext)
      (m0 m1 : memory)
      (t0 t1 : mem_block_id)
      (foo0 foo1: mem_block)
  :
    evalPexp σ0 p ≢ Some t0 ->
    evalPexp σ1 p ≢ Some t1 ->
    blocks_equiv_at_Pexp σ0 σ1 p m0 m1 ->
    blocks_equiv_at_Pexp σ0 σ1 p
                         (memory_set m0 t0 foo0)
                         (memory_set m1 t1 foo1).
Proof.
  intros E0 E1 EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 p), (evalPexp σ1 p).
  -
    constructor.
    inversion_clear EE.
    inversion H. clear H.
    symmetry in H0, H1.
    rewrite Some_neq in E0.
    rewrite Some_neq in E1.
    unfold memory_lookup, memory_set in *.
    rewrite 2!NP.F.add_neq_o; auto.
    rewrite H0, H1.
    constructor.
    apply H2.
  -
    inversion EE.
  -
    inversion EE.
  -
    inversion EE.
Qed.

Instance Compose_DSH_pure
         {n: nat}
         {x_p y_p: PExpr}
         {dop1 dop2: DSHOperator}
         (NXP: x_p ≢ PVar 0)
         (NYP: y_p ≢ PVar 0)
         `{P2: DSH_pure dop2 (incrPVar 0 x_p) (PVar 0)}
         `{P1: DSH_pure dop1 (PVar 0) (incrPVar 0 y_p)}
  : DSH_pure (DSHAlloc n (DSHSeq dop2 dop1)) x_p y_p.
Proof.
  split.
  - (* mem_stable *)
    intros σ m m' fuel H k.
    destruct P1 as [MS1 _ _].
    destruct P2 as [MS2 _ _].
    destruct fuel; simpl in *; try some_none.
    break_match_hyp; try some_none.
    destruct fuel; simpl in *; try some_none.
    break_match_hyp; try some_none.
    rename Heqo into D1, Heqo0 into D2.
    some_inv. rewrite <- H. clear m' H.
    remember (memory_new m) as k'.

    destruct(Nat.eq_dec k k') as [E|NE].
    +
      subst k'.
      rewrite <- E in D1.
      rewrite <- E in D2.
      apply Option_equiv_eq in D1.
      apply Option_equiv_eq in D2.
      rewrite <- E.
      apply MS2 with (k:=k) in D2.
      apply MS1 with (k:=k) in D1.
      clear MS1 MS2.
      split; intros H.
      *
        contradict H.
        subst k.
        apply mem_block_exists_memory_new.
      *
        contradict H.
        subst k.
        apply mem_block_exists_memory_remove.
    +
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
    intros σ0 σ1 m0 m1 fuel (* C0 C1 *) VY0 VY1 E.
    destruct fuel; try constructor.
    simpl.
    repeat break_match; try some_none; try constructor.
    +
      rename m into m0''',  m2 into m1'''.

      inversion VY0 as [y0_i M0Y E0Y]; symmetry in E0Y; clear VY0.
      inversion VY1 as [y1_i M1Y E1Y]; symmetry in E1Y; clear VY1.

      remember (memory_new m0) as t0_i.
      remember (memory_new m1) as t1_i.
      remember (DSHPtrVal t0_i) as t0_v.
      remember (DSHPtrVal t1_i) as t1_v.

      remember (memory_set m0 t0_i mem_empty) as m0'.
      remember (memory_set m1 t1_i mem_empty) as m1'.

      remember (t0_v :: σ0) as σ0'.
      remember (t1_v :: σ1) as σ1'.

      destruct fuel;  simpl in *; try  some_none.
      break_match_hyp; try some_none.
      break_match_hyp; try some_none.

      rename Heqo1 into E12, Heqo0 into E11.
      rename Heqo2 into E02, Heqo into E01.
      rename m2 into m0''.
      rename m into m1''.

      destruct P1, P2.

      assert(evalPexp σ0 y_p ≢ Some t0_i) as NYT0.
      {
        rewrite E0Y.
        apply Some_neq.
        admit.
        (* follows from:
        t0_i ≡ memory_new m0
        mem_block_exists y0_i m0
         *)
      }

      assert(evalPexp σ1 y_p ≢ Some t1_i) as NYT1.
      {
        admit.
      }

      apply blocks_equiv_at_Pexp_remove; auto.

      cut (opt_r (blocks_equiv_at_Pexp σ0' σ1' (incrPVar 0 y_p)) (Some m0''') (Some m1''')).
      intros H; inversion H.

      apply blocks_equiv_at_Pexp_incrVar with (foo0:=DSHPtrVal t0_i) (foo1:=DSHPtrVal t1_i); auto.
      replace (DSHPtrVal t0_i :: σ0) with σ0' by crush.
      replace (DSHPtrVal t1_i :: σ1) with σ1' by crush.
      apply H2.

      specialize (mem_read_safe0 σ0' σ1' m0'' m1'' fuel).
      rewrite E01 in mem_read_safe0.
      rewrite E11 in mem_read_safe0.
      apply mem_read_safe0; clear mem_read_safe0.
      admit.
      admit.

      cut (opt_r (blocks_equiv_at_Pexp σ0' σ1' (PVar 0)) (Some m0'') (Some m1'')).
      intros H;  inversion H.
      apply H2.
      specialize (mem_read_safe1 σ0' σ1' m0' m1' fuel).
      rewrite E02 in mem_read_safe1.
      rewrite E12 in mem_read_safe1.
      apply mem_read_safe1; clear mem_read_safe1.
      admit.
      admit.

      subst σ0' σ1' t0_v t1_v.
      apply blocks_equiv_at_Pexp_incrVar; auto.
      subst m0' m1'.

      assert(evalPexp σ0 x_p ≢ Some t0_i) as NXT0.
      {
      (* follows from:
         t0_i ≡ memory_new m0
         blocks_equiv_at_Pexp σ0 σ1 x_p m0 m1
       *)
        admit.
      }

      assert(evalPexp σ1 x_p ≢ Some t1_i) as NXT1.
      {
        admit.
      }
      apply blocks_equiv_at_Pexp_add_mem; auto.
    +
      exfalso.
    +
      exfalso.

Admitted.

Instance Compose_MSH_DSH_compat
         {i1 o2 o3: nat}
         {mop1: @MSHOperator o2 o3}
         {mop2: @MSHOperator i1 o2}
         (* {compat: Included _ (in_index_set fm op1) (out_index_set fm op2)} *)
         {σ: evalContext}
         {m: memory}
         {dop1 dop2: DSHOperator}
         {t_i x_i y_i: mem_block_id}
         `{P2: DSH_pure dop2 x_i t_i}
         `{P1: DSH_pure dop1 t_i y_i}
         (tcx: t_i ≢ x_i)
         (tcy: t_i ≢ y_i)
         (tct: ¬ mem_block_exists t_i m) (* [t_i] must not be allocated yet *)
         `{P: DSH_pure (DSHAlloc o2 t_i (DSHSeq dop2 dop1)) x_i y_i}
  :
    MSH_DSH_compat mop2 dop2 σ (memory_alloc_empty m t_i) x_i t_i ->

    (forall m', evalDSHOperator σ dop2 (memory_alloc_empty m t_i) (estimateFuel dop2) ≡ Some m' ->
           MSH_DSH_compat mop1 dop1 σ m' t_i y_i) ->

    MSH_DSH_compat
      (MSHCompose mop1 mop2)
      (DSHAlloc o2 t_i (DSHSeq dop2 dop1))
      σ m x_i y_i.
Proof.
  intros E2 E1.
  unshelve eapply DSHAlloc_MSH_DSH_compat; auto.
  apply P.
  split.
  intros mx my MX MY.

  simpl.
  unfold MSHCompose, option_compose; simpl.

  assert(exists mt, memory_lookup (memory_alloc_empty m t_i) t_i ≡ Some mt) as MT.
  {
    exists (mem_empty).
    apply NP.F.add_eq_o.
    reflexivity.
  }
  destruct MT as [mt MT].
  destruct E2 as [E2].
  specialize (E2 mx mt MX MT).

  destruct (evalDSHOperator σ dop2 (memory_alloc_empty m t_i)) as [m'|] eqn:EV2.
  -
    specialize (E1 m').
    destruct E1 as [E1].
    reflexivity.

    assert(MT': memory_lookup m' t_i ≡ Some mt). admit.
    assert(MY': memory_lookup m' y_i ≡ Some my). admit.
    specialize (E1 mt my MT' MY').
  -
    (* [dop2] failed *)
    clear E1.
    inversion_clear E2.

    (* Stopped here 2019-08-80 *)

  destruct (mem_op mop2 mx) as [mt'|], (mem_op mop1 mt) as [my'|].

  repeat break_match; inversion E1; inversion E2; clear E1 E2; try rename H3 into D2;
    try rename H0 into D1;
    (repeat match goal with
         | [H: opt_p _ _ |- _ ] => inversion_clear H
         end);
    symmetry_option_hyp; subst.
  -
    rewrite enough_fuel in D1 by lia.
    some_none.
  -
    rewrite enough_fuel in D1 by lia.
    rewrite enough_fuel by lia.
    assert(m1 ≡ a).
    {
      apply Some_inj_eq.
      rewrite <- D1.
      rewrite <- H.
      reflexivity.
    }
    subst.
    clear H.
    rewrite H2.
    admit.
  -
    admit.
  -
    admit.

  inversion E2.
  -


//


  destruct E1 as [E1].
  specialize (E1 mt my).


Admitted.

  (*
  (* High-level equivalence *)
  Instance dynwin_SHCOL_DSHCOL
           (a: vector CarrierA 3):
    @SHCOL_DSHCOL_equiv _ _ _ _ (dynwin_SHCOL1 a) _
                        (DynWinSigmaHCOL1_Mem a)
                        dynwin_DSHCOL1
                        [DSHvecVal a]
                        (* assuming reification uses [x_i=0] and [y_i=1] *)
                        (NM.add 1 mem_empty
                                (NM.add 0 mem_empty (NM.empty mem_block)))
                        0 1.
  Proof.
    unfold dynwin_DSHCOL1, dynwin_SHCOL1.
    unfold DynWinSigmaHCOL1_Mem, DynWinSigmaHCOL1_Facts.

    (* Normalize by unfolding [@zero] instances: *)
    unfold zero in *.
    (* Normalize dimensionality in DHSCOL. Due to refication,
       for example [o2:=1+1] in SHCOL is replaced with [2] in DHSCOL: *)
    (* simpl in *. *)


    Typeclasses eauto := 1.
    unfold In.
    eapply SHCompose_SHCOL_DSHCOL.
    eapply SafeCast_SHCOL_DSHCOL.


    match goal with
    | [|-  SHCOL_DSHCOL_equiv
            (facts:=?facts)
            (SHCompose ?fm ?op1 ?op2 (o2:=?o2))
            (DSHSeq (DSHAlloc ?o2 ?t_i) (DSHSeq ?d1 ?d2))
            ?σ ?m ?x_i ?y_i] =>
      unshelve eapply (SHCompose_SHCOL_DSHCOL 0 1
                                     (fm:=fm)
                                     (op1:=op1)
                                     (op2:=op2)
                                     (m:=m)
                                     (d1:=d1)
                                     (d2:=d2)
                                     (t_i:=t_i)
                                     (σ:=σ)
                                     (facts:=facts)

             )

    end.


    apply SafeCast_SHCOL_DSHCOL.
  Qed.



     "@SHCOL_DSHCOL_equiv (1 + (2 + 2)) 1 0 Monoid_RthetaFlags
    (?op1 ⊚ ?op2) ?facts
    (@SHCompose_Mem Monoid_RthetaFlags 0 (1 + (2 + 2)) ?o2 1
       ?op1 ?op2 ?compat ?facts1 ?Meq1 ?facts2 ?Meq2 ?facts)
    (DSHAlloc ?o2 ?t_i; ?d1; ?d2) [@DSHvecVal 3 a] ?m 0 1" with

    eapply (SHCompose_SHCOL_DSHCOL 0 1
                                   (i1:=1 + (2 + 2))
                                   (o3:=1)
                                   (svalue:=zero)
                                   (fm:=Monoid_RthetaFlags)
                                   (σ:=[DSHvecVal a])
           ).
    apply SafeCast_SHCOL_DSHCOL.
  Qed.

   *)

(* Heterogenous relation of semantic equivalence of structurally correct SHCOL and DSHCOL operators *)

(*
Open Scope list_scope.
Definition SHCOL_DSHCOL_equiv {i o:nat} {svalue:CarrierA} {fm}
           (σ: evalContext)
           (s: @SHOperator fm i o svalue)
           `{facts: !SHOperator_Facts fm s}
           `{SHM: !SHOperator_Mem  s}
           (d: DSHOperator) (x_i y_i: nat): Prop
  := forall (Γ: evalContext) (x:svector fm i),

    let Γ := σ ++ in

    (List.nth_error Γ' x_i = Some (svector_to_mem_block x)) ->
    match evalDSHOperator Γ' d (estimateFuel d), mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end.


    let xm := svector_to_mem_block x in (* input as mem_block *)
    let ym := mem_empty in (* placeholder for output *)
    let x_i := List.length (σ ++ Γ) in
    let y_i := x_i + 1 in
    let Γ := σ ++ Γ ++ [DSHmemVal xm ; DSHmemVal ym]  in (* add them to context *)
    let fuel := estimateFuel d in
    match evalDSHOperator Γ d fuel, mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end
    | None, None  => True
    | _, _ => False
    end.
*)

(*
Theorem SHCompose_DSHCompose
        {i1 o2 o3} {svalue} {fm}
        (σ: evalContext)
        (f: @SHOperator fm o2 o3 svalue)
        (g: @SHOperator fm i1 o2 svalue)
        (df: DSHOperator o2 o3)
        (dg: DSHOperator i1 o2)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    SHCOL_DSHCOL_equiv σ
                       (SHCompose fm f g)
                       (DSHCompose df dg).
Proof.
  intros Ef Eg.
  intros Γ x.
  simpl.
  break_match.
  -
    unfold compose.
    specialize (Eg Γ x).
    specialize (Ef Γ (op fm g x)).
    rewrite Ef.
    apply evalDSHOperator_arg_proper.
    apply Some_inj_equiv.
    rewrite <- Heqo.
    apply Eg.
  -
    specialize (Eg Γ x).
    rewrite Heqo in Eg.
    some_none.
Qed.

Theorem SHCOL_DSHCOL_equiv_SafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaSafeFlags i o svalue)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.SafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rvector2rsvector _ x)).
  rewrite densify_rvector2rsvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHCOL_DSHCOL_equiv_UnSafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaFlags i o svalue)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.UnSafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rsvector2rvector _ x)).
  rewrite densify_rsvector2rvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHBinOp_DSHBinOp
        {o: nat}
        {svalue: CarrierA}
        {fm}
        (σ: evalContext)
        (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (df: DSHIBinCarrierA)
  :
    (forall (Γ: evalContext) j a b, Some (f j a b) = evalIBinCarrierA
                                                       (σ ++ Γ)
                                                       df (proj1_sig j) a b) ->
    @SHCOL_DSHCOL_equiv (o+o) o svalue fm σ
                        (@SHBinOp fm svalue o f pF)
                        (DSHBinOp df).
Proof.
  intros H.
  intros Γ x.
  simpl.
  unfold evalDSHBinOp.
  unfold SHBinOp'.
  break_let.
  rename t into x0, t0 into x1.

  unfold densify.
  rewrite Vmap_Vbuild.

  break_let.
  unfold vector2pair in *.

  apply Vbreak_arg_app in Heqp.
  subst x.
  rewrite Vmap_app in Heqp0.
  apply Vbreak_arg_app in Heqp0.
  apply Vapp_eq in Heqp0.
  destruct Heqp0 as [H0 H1].
  subst t. subst t0.
  setoid_rewrite Vnth_map.

  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  rewrite Vmap_Vbuild with (fm:=Some).

  vec_index_equiv j jc.
  rewrite 2!Vbuild_nth.
  rewrite evalWriter_Rtheta_liftM2.
  symmetry.
  specialize (H Γ (mkFinNat jc)).
  rewrite H.
  reflexivity.
Qed.

Theorem HTSUMUnion_DSHHTSUMUnion
        {i o: nat}
        {svalue: CarrierA}
        {fm}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (ddot: DSHBinCarrierA)
        (σ: evalContext)
        (f g: @SHOperator fm i o svalue)
        (df dg: DSHOperator i o)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    (forall (Γ:evalContext) a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@HTSUMUnion fm i o svalue dot dot_mor scompat f g)
                       (DSHHTSUMUnion ddot df dg).
Proof.
  intros Ef Eg Edot.
  intros Γ x.
  specialize (Ef Γ).
  specialize (Eg Γ).
  specialize (Edot Γ).
  simpl.
  repeat break_match.
  -
    rewrite Vmap2_as_Vbuild.
    symmetry.
    apply vsequence_Vbuild_equiv_Some.
    unfold HTSUMUnion', Vec2Union.
    unfold densify.
    rewrite Vmap_map.
    rewrite Vmap2_as_Vbuild.
    rewrite Vmap_Vbuild.
    unfold Union.

    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    rewrite evalWriter_Rtheta_liftM2.
    symmetry.

    specialize (Ef x). specialize (Eg x).
    rewrite Heqo0 in Ef; clear Heqo0; some_inv.
    rewrite Heqo1 in Eg; clear Heqo1; some_inv.
    rewrite Edot; clear Edot.
    apply evalBinCarrierA_proper; try reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Ef.
    rewrite <- Ef.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Eg.
    rewrite <- Eg.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.
  -
    specialize (Eg x).
    rewrite Heqo1 in Eg.
    some_none.
  -
    specialize (Ef x).
    rewrite Heqo0 in Ef.
    some_none.
Qed.

Theorem eUnion_DSHeUnion
        {fm}
        (σ: evalContext)
        {o b:nat}
        (bc: b < o)
        (svalue: CarrierA)
        (db: NExpr)
  :
    (forall Γ, Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ (svalue:=svalue)
                       (eUnion fm bc)
                       (DSHeUnion db svalue).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
  break_match; some_inv; repeat nat_equiv_to_eq; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.

    apply castWriter_equiv.
    unfold eUnion'.
    repeat rewrite Vbuild_nth.
    break_if.
    +
      subst.
      rewrite Vhead_Vmap.
      apply castWriter_mkValue_evalWriter.
    +
      apply castWriter_mkStruct.
  -
    destruct n0; auto.
Qed.

 *)

               (*
Definition SHOperatorFamily_DSHCOL_equiv
           {i o n:nat}
           {svalue: CarrierA}
           {fm}
           (Γ: evalContext)
           (op_family: @SHOperatorFamily fm i o n svalue)
           {op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc))}
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
           (d: DSHOperator) : Prop :=
  forall (j:nat) (jc:j<n), SHCOL_DSHCOL_equiv (DSHnatVal j :: Γ)
                                       (op_family (mkFinNat jc))
                                       d.
                *)

(*
Section Expr_NVar_subst_S.

  Local Ltac twoarg := simpl;
                       repeat break_match; auto; try some_none;
                       f_equiv;
                       repeat some_inv;
                       crush.

  Fact NExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : NExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalNexp Γs exp =
    evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      break_if.
      +
        (* accessing variable at pos *)
        subst n.
        simpl.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity; try some_none.
        *
          some_inv.
          inversion H0. inversion H1. subst.
          f_equiv.
          repeat nat_equiv_to_eq; subst.
          apply peano_naturals.S_nat_plus_1.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

  Fact VExpr_NVar_subst_S
       {d: nat}
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : VExpr d)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalVexp Γs exp =
    evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n0 pos).
      +
        (* accessing variable at pos *)
        subst n0.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H0.
        * inversion H0.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n0 n1).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        repeat break_match; try reflexivity.
        subst.
        symmetry.
        compute.
        f_equiv.
        apply H3.
    -
      reflexivity.
  Qed.

  Fact AExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : AExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalAexp Γs exp =
    evalAexp Γ (AExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n pos).
      +
        (* accessing variable at pos *)
        subst n.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0. subst. inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    -
      rename n0 into ne.
      simpl.
      assert(V:evalVexp Γs v = evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) v)) by (apply VExpr_NVar_subst_S with (j0:=j); auto).
      unfold listsDiffByOneElement, isNth in *.
      assert (C: evalNexp Γs ne = evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) ne)) by (apply NExpr_NVar_subst_S with (j:=j); auto).
      twoarg.
      repeat nat_equiv_to_eq.
      subst.
      replace l0 with l by apply proof_irrelevance; clear l0.
      apply Vnth_proper, V.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

End Expr_NVar_subst_S.

Fact evalDiamond_NVar_subst_S:
  ∀ (i o n : nat) (dot : DSHBinCarrierA) (initial : CarrierA)
    (dop_family : DSHOperator i o) (y : vector CarrierA i)
    (j : nat), (∀ (y0 : vector CarrierA i) (pos : nat) (Γ Γs : evalContext),
                   listsDiffByOneElement Γ Γs pos
                   → isNth Γ pos (DSHnatVal j)
                   → isNth Γs pos (DSHnatVal (S j))
                   → evalDSHOperator Γs dop_family y0 =
                     evalDSHOperator Γ
                                     (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1))
                                                            dop_family) y0)
               → ∀ (pos : nat) (Γ Γs : evalContext), listsDiffByOneElement Γ Γs pos
                                                     → isNth Γ pos (DSHnatVal j)
                                                     → isNth Γs pos (DSHnatVal (S j))
                                                     →
                                                     evalDiamond
                                                       (evalBinCarrierA Γs dot)
                                                       initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γs)
                                                             dop_family y)) =
                                                     evalDiamond
                                                       (evalBinCarrierA Γ
                                                                        (AExpr_natvar_subst
                                                                           (pos + 2)
                                                                           (NPlus
                                                                              (if
                                                                                  PeanoNat.Nat.eq_dec pos pos
                                                                                then NVar (pos + 2)
                                                                                else NVar pos)
                                                                              (NConst 1)) dot)) initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γ)
                                                             (DSHOperator_NVar_subt
                                                                (S pos)
                                                                (NPlus
                                                                   (if
                                                                       PeanoNat.Nat.eq_dec pos pos
                                                                     then NVar (S pos)
                                                                     else NVar pos)
                                                                   (NConst 1)) dop_family) y)).
Proof.
  intros i o n dot initial dop_family y j IHdop_family pos Γ Γs L L0 L1.


  dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

  replace (pos+2)%nat with (S (S pos)).
  2:{
    rewrite <- 2!plus_n_Sm.
    rewrite PeanoNat.Nat.add_0_r.
    reflexivity.
  }

  assert(D: evalBinCarrierA Γs dot =
            evalBinCarrierA Γ
                            (AExpr_natvar_subst (S (S pos))
                                                (NPlus (NVar (S (S pos)))
                                                       (NConst 1)) dot)).
  {
    unfold evalBinCarrierA.
    intros a a' Ea b b' Eb.
    apply AExpr_NVar_subst_S with (j:=j).
    apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
    apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
    apply L.
    -- apply L0.
    -- apply L1.
  }

  induction n.
  + reflexivity.
  +
    unfold evalDiamond in *.
    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.
    apply optDot_proper.
    *
      apply D.
    *
      eapply Vfold_left_rev_proper.
      --
        apply optDot_proper.
        unfold evalBinCarrierA.
        intros a a' Ea b b' Eb.

        apply AExpr_NVar_subst_S with (j:=j).
        ++
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
          apply L.
        ++ apply L0.
        ++ apply L1.
      --
        reflexivity.
      --
        vec_index_equiv j jc.
        rewrite 2!Vbuild_nth.
        apply IHdop_family.
        apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
        apply L.
        apply L0.
        apply L1.
    *
      apply IHdop_family.
      apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
      apply L.
      apply L0.
      apply L1.
Qed.

Fact DSHOperator_NVar_subst_S
     {i o : nat}
     (Γ Γs : evalContext)
     (dop_family : DSHOperator i o)
     (pos:nat)
     (y : vector CarrierA i)
     (j : nat):
  listsDiffByOneElement Γ Γs pos ->
  isNth Γ pos (DSHnatVal j) ->
  isNth Γs pos (DSHnatVal (S j)) ->
  evalDSHOperator Γs dop_family y =
  evalDSHOperator Γ
                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family) y.
Proof.
  revert Γ Γs.
  revert pos.
  induction dop_family; intros pos Γ Γs L L0 L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    reflexivity.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    replace l0 with l by apply proof_irrelevance.
    reflexivity.
  -
    simpl.
    unfold evalDSHPointwise, evalIUnCarrierA.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros t tc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    unfold evalDSHBinOp, evalIBinCarrierA.
    break_let.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros m mc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+3)%nat with (S (S (S pos))).
    2:{
      rewrite <- 3!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos n j) as Hn.
    specialize (Hn L L0 L1).

    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      destruct a ; destruct b
    end; try some_none; try reflexivity.


    some_inv.
    nat_equiv_to_eq.
    subst n0.
    generalize (Vhead y); intros y'; clear y; rename y' into y.

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b)
    end.
    {
      induction n1.
      * reflexivity.
      *
        rewrite 2!evalDSHInductor_Sn.
        Opaque evalDSHInductor. simpl.
        repeat break_match; try reflexivity.
        unfold evalBinCarrierA.
        apply AExpr_NVar_subst_S with (j:=j).
        Transparent evalDSHInductor.
        --
          some_inv.
          apply listsDiffByOneElement_Sn; try reflexivity.
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply IHn1).
          apply L.
        -- apply L0.
        -- apply L1.
        -- some_none.
        -- some_none.
    }

    repeat break_match; try some_none; try reflexivity.
    f_equiv.
    f_equiv.
    some_inv.
    apply C.
  -
    simpl.
    apply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    eapply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b) by (apply IHdop_family2; auto)
    end.
    repeat break_match; try reflexivity; try some_none.
    some_inv.
    rewrite <- C.
    eapply IHdop_family1; auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C0: a = b) by (apply IHdop_family1; auto)
    end.

    assert(C1: evalDSHOperator Γs dop_family2 y = evalDSHOperator Γ
                                                                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family2) y) by (apply IHdop_family2; auto).

    repeat break_match; try reflexivity; try some_none; try contradiction.
    repeat some_inv.
    rewrite C0, C1.
    apply vsequence_option_proper.
    rewrite 2!Vmap2_as_Vbuild.
    apply Vbuild_proper.
    intros m mc.
    unfold evalBinCarrierA.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    --
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    -- apply L0.
    -- apply L1.
Qed.

Theorem IReduction_DSHIReduction
        {i o n: nat}
        {svalue: CarrierA}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n svalue)
        (ddot: DSHBinCarrierA)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    (forall Γ a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@IReduction svalue i o n dot pdot scompat op_family)
                       (@DSHIReduction i o n ddot svalue dop_family).
Proof.
  intros Hdot Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaSafeFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn pdot Hdot ddot x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaSafeFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaSafeFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaSafeFlags)) x))
      with
        (Some
           (densify Monoid_RthetaSafeFlags
                    (op Monoid_RthetaSafeFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    setoid_rewrite <- Hdot.
    clear ddot Hdot Γ σ.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply pdot.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

Theorem SHPointwise_DSHPointwise
        {fm}
        {svalue: CarrierA}
        {n: nat}
        (f: FinNat n -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (df: DSHIUnCarrierA)
        (σ: evalContext)
  :
    (forall Γ j a, Some (f j a) = evalIUnCarrierA (σ++Γ) df (proj1_sig j) a) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHPointwise fm svalue  n f pF)
                       (DSHPointwise df).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  unfold evalDSHPointwise.
  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  unfold densify.
  rewrite Vmap_map.
  simpl.
  unfold SHPointwise'.
  rewrite Vmap_Vbuild.
  apply Vbuild_proper.
  intros j jc.
  rewrite Vnth_map.
  rewrite evalWriter_Rtheta_liftM.
  specialize (H (mkFinNat jc)).
  rewrite <- H.
  reflexivity.
Qed.

Lemma evalDSHInductor_not_None
      (n : nat)
      (initial : CarrierA)
      (df : DSHBinCarrierA)
      (σ Γ : evalContext)
      (Edot: forall a b : CarrierA, is_Some (evalBinCarrierA (σ ++ Γ) df a b)) :
  forall x : CarrierA, is_Some (evalDSHInductor (σ ++ Γ) n df initial x).
Proof.
  intros x.
  induction n.
  -
    crush.
  -
    simpl.
    break_match; crush.
Qed.

Theorem SHInductor_DSHInductor
        {fm}
        {svalue: CarrierA}
        (n:nat)
        (f: CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (initial: CarrierA)
        (dn:NExpr)
        (df: DSHBinCarrierA)
        (σ: evalContext)
  :
    (forall Γ, Some n = evalNexp (σ++Γ) dn) ->
    (forall  Γ a b, Some (f a b) = evalBinCarrierA (σ++Γ) df a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHInductor fm svalue n f pF initial)
                       (DSHInductor dn df initial).
Proof.
  intros E Edot.
  intros Γ x.
  specialize (E Γ).
  specialize (Edot Γ).
  simpl evalDSHOperator.
  break_match; try some_none.
  apply Some_inj_equiv in E.
  unfold equiv, peano_naturals.nat_equiv in E.
  subst n0.

  simpl op.
  unfold SHInductor', Lst, Vconst, densify.
  rewrite Vmap_cons.
  rewrite evalWriter_Rtheta_liftM.
  simpl.
  dep_destruct x.
  simpl.
  clear x0 x.
  generalize (WriterMonadNoT.evalWriter h). intros x. clear h.

  break_match.
  -
    f_equiv.
    apply Vcons_proper; try reflexivity.
    clear dn Heqo.
    dependent induction n.
    +
      crush.
    +
      simpl.
      specialize (IHn f pF initial df σ Γ Edot).
      simpl in Heqo0.
      break_match.
      *
        rewrite IHn with (x:=x) (c:=c0).
        specialize (Edot c0 x).
        rewrite Heqo0 in Edot.
        some_inv; auto.
        auto.
      *
        some_none.
  -
    contradict Heqo0.
    apply is_Some_ne_None.
    apply evalDSHInductor_not_None.
    intros a b.
    specialize (Edot a b).
    symmetry in Edot.
    apply equiv_Some_is_Some in Edot.
    apply Edot.
Qed.

Theorem eT_DSHeT
        {fm}
        {svalue: CarrierA}
        {i b:nat}
        (bc: b < i)
        (db: NExpr)
        (σ: evalContext)
  :
    (forall (Γ:evalContext), Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ
                       (@eT fm svalue i b bc)
                       (@DSHeT i (db:NExpr)).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
  break_match; some_inv; unfold equiv, peano_naturals.nat_equiv in H; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.
    dep_destruct jc;try inversion x0.
    rewrite Vnth_cons.
    break_match. inversion l0.
    apply castWriter_equiv.
    simpl.
    rewrite Vnth_map.
    replace l with bc by apply proof_irrelevance.
    apply castWriter_mkValue_evalWriter.
  -
    destruct n0; auto.
Qed.

Theorem ISumUnion_DSHISumUnion
        {i o n: nat}
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n zero)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@ISumUnion i o n op_family)
                       (@DSHIUnion i o n (APlus (AVar 1) (AVar 0)) 0 dop_family).
Proof.
  (* significant code duplication with `IReduction_DSHIReduction` *)
  intros Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaFlags)) x))
      with
        (Some
           (densify Monoid_RthetaFlags
                    (op Monoid_RthetaFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    assert(Hdot: forall Γ a b, Some (CarrierAplus a b) = evalBinCarrierA (σ++Γ) (APlus (AVar 1) (AVar 0))  a b) by reflexivity.

    setoid_rewrite <- Hdot.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply CarrierAPlus_proper.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

(* Attemts to solve evaluation lemmas on DSHCOL Aexpr *)
Ltac solve_evalAexp :=
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ H: FinNat _ |- _ ] => destruct H
         | [ |- evalAexp _ _ = Some _] =>
           unfold Fin1SwapIndex, const, mult_by_nth; simpl;
           try (repeat break_match; try some_none; try congruence)
         | [H: Some ?A ≡ Some ?b |- _ ] => inversion H; clear H
         | [H: Some ?A = Some ?b |- _ ] => apply Some_inj_equiv in H
         | [ |- ?a _ = ?a _ ] => f_equiv
         | [ |- Vnth ?a _ ≡ Vnth ?a _] => try apply Vnth_eq
         | [ |- _ ] => auto
         end.

(* Solves obligations generated by `reifySHCOL` *)
Ltac solve_reifySHCOL_obligations E :=
  intros ;
  unfold E ;
  match goal with
  | [ |- SHCOL_DSHCOL_equiv _ _ ?d] => unfold d
  end ;
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ |- SHCOL_DSHCOL_equiv _ (SHCompose _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_SafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (UnSafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_UnSafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (SHBinOp _ _) (DSHBinOp _) ] => apply SHBinOp_DSHBinOp
         | [ |- SHCOL_DSHCOL_equiv _ (HTSUMUnion _ _ _ _) (DSHHTSUMUnion _ _ _) ] => apply HTSUMUnion_DSHHTSUMUnion
         | [ |- SHCOL_DSHCOL_equiv _ (eUnion _ _) (DSHeUnion _ _)] => apply eUnion_DSHeUnion
         | [  |- SHCOL_DSHCOL_equiv _ (IReduction _ _) (DSHIReduction _ _ _ _)] => apply IReduction_DSHIReduction
         | [ |- SHOperatorFamily_DSHCOL_equiv _ _ _ ] => unfold SHOperatorFamily_DSHCOL_equiv
         | [ |- SHCOL_DSHCOL_equiv _ (SHFamilyOperatorCompose _ _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SHPointwise _ _) (DSHPointwise _) ] =>  apply SHPointwise_DSHPointwise
         | [ |- SHCOL_DSHCOL_equiv _ (SHInductor _ _ _ _) (DSHInductor _ _ _)] => apply SHInductor_DSHInductor
         | [ |- SHCOL_DSHCOL_equiv _ (eT _ _) (DSHeT _)] => apply eT_DSHeT
         | [ |- SHCOL_DSHCOL_equiv _(ISumUnion _) (DSHIUnion _ _ _ _) ] => apply ISumUnion_DSHISumUnion
         | [ |- Some _ = evalIUnCarrierA _ _ _ _ ] => unfold evalIUnCarrierA; symmetry; solve_evalAexp
         | [ |- _ ] => try reflexivity
         end.
*)
