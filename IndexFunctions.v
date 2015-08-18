(* Coq defintions for Sigma-HCOL operator language *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

(*  CoLoR *)
Require Import CoLoR.Util.List.ListUtil.

Global Open Scope nat_scope.

(* Vector index mapping functon which maps between two sets of natrual
     numers. *)
Definition index_map_spec (domain range: nat) :=
  forall n : nat, n < domain -> {v : nat | v < range}.

(* Returns upper domain bound for given `index_map_spec` *)
Definition index_map_dom {d r:nat} (s: index_map_spec d r) := d.

(* Returns upper rang bound for given `index_map_spec` *)
Definition index_map_range {d r:nat} (s: index_map_spec d r) := r.

Global Instance index_map_equiv {domain range:nat}:
  Equiv (index_map_spec domain range)
  :=
    fun f g => forall (x:nat) (xd: x<domain), f x xd = g x xd.

Fixpoint natrange_list (n:nat) : list nat :=
  match n with
  | 0 => nil
  | S p => cons p (natrange_list p)
  end.

Lemma le_pred_l {n m} (H: S n <= m): n <= m.
Proof.
  auto with arith.
Defined.

Section Permutations.
  Fixpoint natrange_f_spec
           (n:nat)
           {i o: nat}
           (nd: n<=i)
           (f_spec: index_map_spec i o)
  : list nat
    :=
      match n return n <= i -> list nat with
      | 0 => fun _ => nil
      | S n' => fun nd => cons n' (natrange_f_spec n' (le_pred_l nd) f_spec)
      end nd.
  
  Program Definition index_map_is_permutation
          {n: nat}
          (f_spec: index_map_spec n n)
    :=
      Permutation
        (natrange_list n)
        (@natrange_f_spec n n n _ f_spec).
End Permutations.

Section Jections.

  Definition index_map_injective
             {n: nat}
             (f_spec: index_map_spec n n)
    :=
      forall (x:nat) (xc: x<n) (y:nat) (yc: y<n), 
        f_spec x xc ≡ f_spec y yc → x ≡ y.

  Definition index_map_surjective
             {n: nat}
             (f_spec: index_map_spec n n)
    :=
      forall (y:nat) (yc: y<n), exists (x:nat) (xc: x<n), proj1_sig (f_spec x xc) ≡ y.

  Definition index_map_bijective
            {n: nat}
            (f_spec: index_map_spec n n)
    :=
      (index_map_injective f_spec) /\ (index_map_surjective f_spec).

End Jections.

(* permutation is bijective function of a set into itself *)
Lemma permutation_is_bijection
      {n: nat}
      (f_spec: index_map_spec n n):
  index_map_bijective f_spec <-> index_map_is_permutation f_spec.
Proof.
  split.
  unfold index_map_bijective, index_map_is_permutation.
  intros.
  destruct H as [IH SH].
  generalize (index_map_is_permutation_obligation_1 n f_spec) as nn; intros.

  induction n.
  + auto.
  + simpl.
    constructor.
Admitted.
  
Section Primitive_Functions.
  
  Program Definition identity_index_map
          (dr: nat):
    index_map_spec dr dr
    :=
      fun i _ => i.
  
  Program Definition constant_index_map
          {range: nat}
          (j: nat)
          {jdep: j<range}:
    index_map_spec 1%nat range
    :=
      fun _ _ => j.
  
  Program Definition add_index_map
          {domain range: nat}
          (k: nat)
          {kdep: k+domain <= range}:
    index_map_spec domain range
    :=
      fun i i_dim => i+k.
  Next Obligation.
    lia.
  Defined.

End Primitive_Functions.

Section Function_Operators.
  
  Definition index_map_compose
             {i o t: nat}
             (g: index_map_spec t o)
             (f: index_map_spec i t) :
    index_map_spec i o
    := fun x xdom_bound =>
         (* manual uncurry *)
         let (fv, fv_dom_bound) := f x xdom_bound in
         g fv fv_dom_bound.

  Program Definition index_map_tensor_product
          {m n M N: nat}
          {nz: 0 ≢ n}
          (f: index_map_spec m M)
          (g: index_map_spec n N):
    index_map_spec (m*n) (M*N)
    := fun i _ =>
         let pn := pred n in
         let ab := divmod i pn 0 pn in
         N * (f (fst ab) _) + (g (pn - (snd ab)) _).
  Next Obligation.
    destruct n.
    congruence. clear nz.
    simpl.
    generalize (divmod_spec i n 0 n). 
    destruct divmod as (q,u).
    simpl.
    nia.
  Defined.
  Next Obligation.
    destruct n.
    congruence. clear nz.
    lia.
  Defined.
  Next Obligation.
    generalize (f (fst (divmod i (pred n) 0 (pred n)))
                  (index_map_tensor_product_obligation_1 m n M N nz f g i H)) as fg.
    generalize (g (pred n - snd (divmod i (pred n) 0 (pred n)))
                  (index_map_tensor_product_obligation_2 m n M N nz f g i H)) as gg.
    intros.
    destruct gg as [gv ga].
    destruct fg as [fv fa].
    simpl.
    nia.
  Defined.

End Function_Operators.

Notation "g ∘ f" := (index_map_compose g f) : index_f_scope.
Notation "x ⊗ y" := (index_map_tensor_product x y) (at level 90) : index_f_scope.

Lemma index_function_proj1_bound
      {domain range: nat}
      (f_spec: index_map_spec domain range):
  forall n (nd: n<domain), proj1_sig (f_spec n nd) < range.
Proof.
  auto.
Qed.

Section Function_Rules.

  Local Open Scope index_f_scope.

  Lemma index_map_rule_39
        {rf0 rf1 dg0 dg1 rg0 rg1:nat}
        {g0: index_map_spec dg0 rg0}
        {g1: index_map_spec dg1 rg1}
        {f0: index_map_spec rg0 rf0}
        {f1: index_map_spec rg1 rf1}
        {ndg1: 0 ≢ dg1}
        {nrg1: 0 ≢ rg1}
        {ls:  (dg0 * dg1) ≡ (rf0 * rf1)}
        {nf1cg1: 0 ≢ index_map_dom (f1 ∘ g1)}
    :
      (index_map_tensor_product f0 f1 (nz:=nrg1))
        ∘ (index_map_tensor_product g0 g1 (nz:=ndg1))
      =
      index_map_tensor_product
        (f0 ∘ g0)
        (f1 ∘ g1)
        (nz := nf1cg1).
  Proof.
    unfold equiv, index_map_equiv.
    intros.
    unfold index_map_compose.
    unfold index_map_tensor_product.
    

  Qed.

  Local Close Scope index_f_scope.
        
End Function_Rules.
  

