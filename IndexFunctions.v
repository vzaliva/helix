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

Require Import Spiral.

Global Open Scope nat_scope.

Record index_map (domain range : nat)
  :=
    IndexMap { index_f : nat -> nat; index_f_spec : forall x, x<domain -> (index_f x) < range }.

Notation "⟦ f ⟧" := (@index_f _ _ f).
Notation "« f »" := (@index_f_spec _ _ f).

(* Returns upper domain bound for given `index_map_spec` *)
Definition index_map_dom {d r:nat} (s: index_map d r) := d.

(* Returns upper rang bound for given `index_map_spec` *)
Definition index_map_range {d r:nat} (s: index_map d r) := r.

Global Instance index_map_equiv {domain range:nat}:
  Equiv (index_map domain range)
  :=
    fun f g => forall (x:nat) (xd: x<domain), ⟦ f ⟧ x = ⟦ g ⟧ x.


Section Inversions.
  Definition partial_function_spec domain range f' :=
    forall x, x<range -> forall z, (((f' x) ≡ Some z) -> z < domain).
  
  Definition inverse_map_spec (i o: nat) :=
    { f': nat -> option nat | partial_function_spec i o f'}.
  
  Program Definition build_inverse_map_spec
          {i o: nat}
          (f: index_map i o): inverse_map_spec i o
    := fun y =>
         List.fold_right
           (fun x' p => if eq_nat_dec y ( ⟦ f ⟧ x') then Some x' else p)
           None
           (rev_natrange_list i).
  Next Obligation.
    destruct f.  simpl.
    unfold partial_function_spec.
    intros.
    induction i.
    crush.
    simpl in H0.
    destruct (eq_nat_dec x (index_f0 i)); crush.
  Defined.
End Inversions.
  

Section Permutations.
  Fixpoint natrange_f_spec
           (n:nat)
           {i o: nat}
           (nd: n<=i)
           (f_spec: index_map i o)
  : list nat
    :=
      match n return n <= i -> list nat with
      | 0 => fun _ => List.nil
      | S n' => fun nd => List.cons n' (natrange_f_spec n' (le_pred_l nd) f_spec)
      end nd.
  
  Program Definition index_map_is_permutation
          {n: nat}
          (f: index_map n n)
    :=
      let l:=(rev_natrange_list n) in
      Permutation l (List.map ⟦ f ⟧ l).
End Permutations.

Section Jections.

  Definition index_map_injective
             {n: nat}
             (f: index_map n n)
    := 
      forall (x:nat) (xc: x<n) (y:nat) (yc: y<n), 
         ⟦ f ⟧ x ≡ ⟦ f ⟧ y → x ≡ y.

  Definition index_map_surjective
             {n: nat}
             (f: index_map n n)
    :=
      forall (y:nat) (yc: y<n), exists (x:nat) (xc: x<n), ⟦ f ⟧ x ≡ y.

  Definition index_map_bijective
            {n: nat}
            (f: index_map n n)
    :=
      (index_map_injective f) /\ (index_map_surjective f).

End Jections.

(* permutation is bijective function of a set into itself *)
(*
Lemma permutation_is_bijection
      {n: nat}
      (f: index_map n n):
  index_map_bijective  f <-> index_map_is_permutation f.
Proof.
  destruct f as [f f_spec]. 
  split.
  +unfold index_map_bijective, index_map_injective, index_map_surjective, index_map_is_permutation.
   simpl.
   intros.   
   destruct H as [IH SH].

   apply NoDup_Permutation.
   {
     induction n.
     constructor 1.
     simpl.
     constructor 2.
     unfold List.In.
     admit.
     apply IHn; admit.
   }
   admit.
   admit.
  +
    admit.
Qed.
 *)

Section Primitive_Functions.
  
  Program Definition identity_index_map
          (dr: nat) {dp: dr>0}:
    index_map dr dr
    := IndexMap dr dr (id) _.
  
  Program Definition constant_index_map
          {range: nat}
          (j: nat)
          {jdep: j<range}:
    index_map 1 range
    := IndexMap 1 range (fun _ => j) _.
  
  Program Definition add_index_map
          {domain range: nat}
          (k: nat)
          {kdep: k+domain <= range}:
    index_map domain range
    := IndexMap domain range (fun i => i+k) _.
  Next Obligation.
    lia.
  Defined.

  Program Definition h_index_map
          {domain range: nat}
          (b s: nat)
          {range_bound: (b+(pred domain)*s) < range}
          {sc: s>0} (* required constraint, according by Franz *)
    : index_map domain range
    :=
      IndexMap domain range (fun i => b + i*s) _.
  Next Obligation.
    nia.
  Defined.

End Primitive_Functions.

Section Function_Operators.
  
  Definition index_map_compose
             {i o t: nat}
             (g: index_map t o)
             (f: index_map i t) :
    index_map i o.
  Proof.
      refine (IndexMap i o (⟦g⟧ ∘ ⟦f⟧) _).
      intros.
      destruct f, g.
      simpl.
      unfold compose.
      auto.
  Defined.
      
  Definition tensor_product
             (n N: nat)
             {nz: 0 ≢ n}
             (f: nat -> nat)
             (g: nat -> nat)
             (i: nat): nat
    :=  N * (f (i / n)) + (g (i mod n)).

  Program Definition index_map_tensor_product
          {m n M N: nat}
          {nz: 0 ≢ n}
          (f: index_map m M)
          (g: index_map n N):
    index_map (m*n) (M*N)
    := IndexMap (m*n) (M*N)  (tensor_product n N ⟦f⟧ ⟦g⟧ (nz:=nz))  _.
  Next Obligation.
    destruct f,g.
    unfold tensor_product, div, modulo.
    assert ((fst (divmod x (pred n) 0 (pred n))) < m).
    {
      destruct n.
      congruence. clear nz.
      simpl.
      generalize (divmod_spec x n 0 n). 
      destruct divmod as (q,u).
      simpl.
      nia.
    }
    assert (index_f0 (fst (divmod x (pred n) 0 (pred n))) < M) by auto.
    
    assert ((pred n - snd (divmod x (pred n) 0 (pred n))) < n).
    {
      destruct n.
      congruence. clear nz.
      simpl.
      generalize (divmod_spec x n 0 n). 
      destruct divmod as (q,u).
      simpl.
      nia.
    }
    assert (index_f1 (pred n - snd (divmod x (pred n) 0 (pred n))) < N) by auto.
    simpl.
    replace (match n with
                | 0 => n
                | S y' => fst (divmod x y' 0 y')
                end) with (fst (divmod x (pred n) 0 (pred n))).
    replace (match n with
            | 0 => n
            | S y' => y' - snd (divmod x y' 0 y') end) with
    ((pred n) - snd (divmod x (pred n) 0 (pred n))).
    nia.
    break_match; auto.
    break_match; auto.
    congruence.
  Defined.

End Function_Operators.

Notation "g ∘ f" := (index_map_compose g f) : index_f_scope.
Notation "x ⊗ y" := (index_map_tensor_product x y) (at level 90) : index_f_scope.

Section Function_Rules.

  Local Open Scope index_f_scope.

  Lemma index_map_rule_39
        {rf0 rf1 dg0 dg1 rg0 rg1:nat}
        {g0: index_map dg0 rg0}
        {g1: index_map dg1 rg1}
        {f0: index_map rg0 rf0}
        {f1: index_map rg1 rf1}
        {ndg1: 0 ≢ dg1}
        {nrg1: 0 ≢ rg1}
        {ls:  (dg0 * dg1) ≡ (rf0 * rf1)}
    :
      (index_map_tensor_product f0 f1 (nz:=nrg1))
        ∘ (index_map_tensor_product g0 g1 (nz:=ndg1))
      =
      index_map_tensor_product
        (f0 ∘ g0)
        (f1 ∘ g1)
        (nz := ndg1).
  Proof.
    destruct f0 as [f0 f0_spec].
    destruct f1 as [f1 f1_spec].
    destruct g0 as [g0 g0_spec].
    destruct g1 as [g1 g1_spec].

    unfold equiv, index_map_equiv.
    intros. simpl.
    unfold compose, tensor_product.

    assert (X: (rg1 * g0 (x / dg1) + g1 (x mod dg1)) / rg1 ≡ g0 (x / dg1)).
    {
      rewrite plus_comm, mult_comm, Nat.div_add by auto.
      + assert(x mod dg1 < dg1). {
          apply modulo_smaller_than_devisor. assumption.
        }
        assert (g1 (x mod dg1) < rg1). {
          apply g1_spec. assumption.
        }
        assert (X0: g1 (x mod dg1) / rg1 ≡ 0). {
          apply Nat.div_small.  assumption.
        }
        rewrite X0.
        auto.
    }
    rewrite_clear X.
    
    assert (X: (rg1 * g0 (x / dg1) + g1 (x mod dg1)) mod rg1 ≡  g1 (x mod dg1)).
    {
      rewrite plus_comm, mult_comm.
      rewrite Nat.mod_add by auto.
      rewrite Nat.mod_small.
      reflexivity.
      assert (x mod dg1 < dg1).  {
        apply modulo_smaller_than_devisor.
        assumption.
      }
      auto.
    }
    rewrite_clear X.
    reflexivity.
  Qed.

  Lemma index_map_rule_40:
    forall n (np: n>0)
      {range_bound_h_0: 0 + pred n * 1 < n}
      {c1_gt_0: 1>0}
    ,
      @identity_index_map n np = @h_index_map n n 0 1
                                              range_bound_h_0 c1_gt_0.
  Proof.
    intros.
    unfold identity_index_map, h_index_map, equiv, index_map_equiv, id.
    intros. simpl.
    symmetry. apply mult_1_r.
  Qed.

  Local Close Scope index_f_scope.
        
End Function_Rules.
  

