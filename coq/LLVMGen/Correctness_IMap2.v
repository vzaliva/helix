Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.
Require Import Helix.LLVMGen.Correctness_While.

From Vellvm Require Import Utils.Commutation.

Require Import Paco.paco.

Import ProofMode.

Set Implicit Arguments.
Set Strict Implicit.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Import Memory.NM.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Section DSHIMap_is_tfor.

  (* Iterative body of [IMap] *)
  Definition DSHIMap_tfor_body
             (σ : evalContext)
             (f : AExpr)
             (offset : nat)
             (init acc : mem_block) :=
    v <-
       lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" offset init);;
    vn <- lift_Serr (MInt64asNT.from_nat offset);;
    v'<- denoteIUnCType σ f vn v;;
    ret (mem_add offset v' acc).

  (* [tfor] formulation of [DSHIMap]. *)
  Definition DSHIMap_tfor
             (σ : evalContext)
             (n : nat)
             (f : AExpr)
             (x y : mem_block):
    itree Event mem_block :=
    (* IMap has "reverse indexing" on its body *)
    tfor (fun i acc => DSHIMap_tfor_body σ f (n - 1 - i) x acc) 0 n y.

  (* [denoteDSHIMap] is equivalent to [tfor] with "reverse indexing" on an
     [IMap] body. *)
  Lemma denoteDSHIMap_as_tfor:
    forall (σ : evalContext) n f x y,
      denoteDSHIMap n f σ x y ≈ DSHIMap_tfor σ n f x y.
  Proof.
    intros.
    unfold DSHIMap_tfor. revert y.
    induction n.
    - cbn. intros.
      setoid_rewrite tfor_0.
      reflexivity.
    - intros.
      rewrite tfor_unroll; [| lia].
      assert (S n - 1 - 0 ≡ n) by lia. rewrite H. cbn.
      repeat setoid_rewrite bind_bind.
      cbn.
      eapply eutt_clo_bind; [reflexivity|].
      intros u1 u2 H'.
      eapply eutt_clo_bind; [reflexivity|].
      intros u0 u3 H''. subst.
      eapply eutt_clo_bind; [reflexivity|].
      intros; subst. rewrite bind_ret_l.
      rewrite IHn.

      setoid_rewrite tfor_ss_dep. 3 : lia.
      reflexivity. intros.
      cbn. assert (n - 0 - S i ≡ n - 1 - i) by lia. rewrite H0. reflexivity.
  Qed.

  Definition mem_block_Equiv_up_to (n : nat) (m m' : mem_block) :=
    forall k, k < n -> find k m = find k m'.

  (* < Desired Lemma > *)
  (* Lemma mem_block_equiv_is_order_independent : *)
  (*   forall n mem init_vec, *)
  (*       eutt (equiv_mem_block /2\ eq_mem) *)
  (*       interp_helix (tfor body_up   0 n) (m, init_vec) *)
  (*       interp_helix (tfor body_down 0 n) (m, init_vec) *)
  (*       equiv_mem_block_frag i n *)
  (*       equiv_mem_block <-> equiv_mem_block_frag 0 n. *)

  (* TODO *)

  (* < Generalized Lemma >
        Equivalent to Desired lemma when i = 0
   *)
  (* TODO *)

  (*
        forall i, 0 <= i < n,
        eutt (equiv_mem_block ** eq_mem)
        interp_helix (vec <- (tfor body_up i n) init ;;
                          (tfor body_down (n-i) n) vec)
                    (vec <- tfor body_down i n) init ;;
                          (tfor body_up  (n-i) n)
   *)
  (*
        (* Inductive hypothesis with one step "bubbled up" *)
        equiv_mem_block_frag i n 
          ((vec0 <- (tfor body_up (S i) j) init ;;
            (veci <- (body_up i) vec0 ;;
          (vecn <- (tfor body_up j n) veci;;
          (tfor body_down (n-i) n) vecn)
          ((vec0 <- (tfor body_up (S i) n) init ;;
          (veci <- (body_up i) vec0 ;;
          (tfor body_down (n-i) n) vecn)
  *)


  (* Wishful? *)
  Lemma tfor_IMap_rev_fixed :
    forall {E} (σ : evalContext) (n : nat) (f : AExpr) (x y : mem_block) mem,
    exists vec,
      eutt (E:=E) (fun x y =>
              match x, y with
              | None, None => True
              | Some (mH, mem_bl), Some (mH', mem_bl') =>
                  mH ≡ mH' /\
                  mem_block_Equiv_up_to n mem_bl mem_bl'
              | _, _ => False
              end)
    (interp_helix (tfor (fun i acc => DSHIMap_tfor_body σ f (n - i) x acc) 0 n y) mem)
    (Ret vec)
      (* /\ (forall k, k < n -> exists v, find k vec = Some v). *).
  Admitted.

  (* Lemma mem_block_Equiv_up_to_eq : *)
  (* ... *)
  (*   mem_block_Equiv m m' ~ mem_block_Equiv_up_to n m m' *)


  (* TODO: 1. Prove this
           2. Generalize (t : nat -> itree void1 nat)
           3. 
   *)
  Lemma pure_swap :
    forall (t t' : unit -> itree void1 unit),
      x <- t () ;; t' x ≈ x <- t' () ;; t x.
  Admitted.

(* TODO : F : nat -> binary64 Formal I, 0 <=I <k, mem1[i] = f i /\ mem2[n-i-1] = f (n-i-1) *)
  (* The "IMap" operator is compiled "backwards", resulting in a need to
     equate reversed and unreversed denotation with the mem_blocks equiv
     relation. *)
  (* needs to be stated after interpretation *)
  (* TODO: interp (bind (trigger read1) (fun x => bind (trigger read2) (fun y => k x y) \approx interp (bind (trigger read 2) (fun y => bind (trigger read1) (fun x => k x y))  *)
  Lemma tfor_IMap_rev :
    forall {E} (σ : evalContext) (n : nat) (f : AExpr) (x y : mem_block) mem,
    no_failure (E:=E)
      (interp_helix (tfor (fun i acc => DSHIMap_tfor_body σ f (n - i) x acc) 0 n y) mem) ->
    no_failure (E:=E)
      (interp_helix (tfor (fun i acc => DSHIMap_tfor_body σ f i x acc) 0 n y) mem) ->
    eutt (E:=E) (fun x y =>
            match x, y with
            | None, None => True
            | Some (mH, mem_bl), Some (mH', mem_bl') =>
                mH ≡ mH' /\
                equiv mem_bl mem_bl'
            | _, _ => False
            end)
  (interp_helix (tfor (fun i acc => DSHIMap_tfor_body σ f (n - i) x acc) 0 n y) mem)
  (interp_helix (tfor (fun i acc => DSHIMap_tfor_body σ f i x acc) 0 n y) mem).
Proof.

  intros.
  (* eapply eqit_trans. *)
  (*   revert σ f x y. *)
  (*   induction n. *)
  (*   - intros. setoid_rewrite tfor_0. apply eutt_Ret. *)
  (*     apply mem_block_Equiv_Reflexive. *)
  (*   - intros. *)
  (*     rewrite tfor_unroll. *)
  (*     rewrite tfor_unroll. unfold equiv, mem_block_Equiv. *)
  Admitted.

  (* What kind of post conditions can we write? *)
  Lemma IMap_body_post:
    forall σ f n x y,
    exists X, DSHIMap_tfor_body σ f n x y ⤳ X.
  Proof.
    intros. cbn.
    evar (post : Memory.NM.t binary64 -> Prop).
    exists post.
    rewrite has_post_post_strong. unfold has_post_strong.
    Unshelve.
    2 : refine (fun m => find n m = find n m).
    Admitted.

  Lemma distinct_bind_swap :
    forall E n1 n2 t1 t1' t2 t2',
      eutt (E := E) (fun m m' => find n1 m = find n1 m') t1 t1' ->
      eutt (E := E) (fun m m' => find n2 m = find n2 m') t2 t2' ->
      n1 ≢ n2 ->
      eutt (E := E) (@equiv mem_block _) (t1 ;; t2) (t2' ;; t1').
  Admitted.

  Lemma has_post_distinct :
    forall E n (t t': itree E mem_block),
      t' ⤳ (fun m => exists k, find n m = Some k) ->
      (* has only modified a range that is not n1 *)
      t ⤳ (fun m => find n m = None) ->
      eutt (E := E) (@equiv mem_block _) (t ;; t') (t' ;; t).
  Admitted.

  Notation mem := mem_block.

  Definition predicate := mem -> Prop.

  Definition mem_disjoint (m1 m2 : mem) :=
      let kx := mem_keys_set m1 in
      let ky := mem_keys_set m2 in
      is_disjoint kx ky.

  Definition star (p1 p2 : predicate) : predicate :=
    (fun m => exists m1 m2, m = mem_union m1 m2 /\
                    p1 m1 /\ p2 m2 /\
                    mem_disjoint m1 m2).

  Notation "m1 ⊍ m2" := (mem_union m1 m2).
  Notation "m1 ⟂ m2" := (mem_disjoint m1 m2) (at level 40).


End DSHIMap_is_tfor.
