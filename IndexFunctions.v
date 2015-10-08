(* Coq defintions for Sigma-HCOL operator language *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

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


(* Index maps (total functions) *)

Record index_map (domain range : nat)
  :=
    IndexMap { index_f : nat -> nat; index_f_spec : forall x, x<domain -> (index_f x) < range }.

Notation "⟦ f ⟧" := (@index_f _ _ f).
Notation "« f »" := (@index_f_spec _ _ f).

(* Returns upper domain bound for given `index_map` *)
Definition index_map_dom {d r:nat} (s: index_map d r) := d.

(* Returns upper rang bound for given `index_map` *)
Definition index_map_range {d r:nat} (s: index_map d r) := r.

Global Instance index_map_equiv {domain range:nat}:
  Equiv (index_map domain range)
  :=
    fun f g => forall (x:nat) (xd: x<domain), ⟦ f ⟧ x = ⟦ g ⟧ x.

(* Index maps (partial functions) *)

Record partial_index_map (domain range : nat)
  :=
    PartialIndexMap { partial_index_f : nat -> option nat; partial_index_f_spec :  forall x, x<domain -> forall z, (((partial_index_f x) ≡ Some z) -> z < range)}.

(* Returns upper domain bound for given `partial_index_map` *)
Definition patial_index_map_dom {d r:nat} (s: partial_index_map d r) := d.

(* Returns upper rang bound for given `patial_index_map` *)
Definition partial_index_map_range {d r:nat} (s: partial_index_map d r) := r.

Global Instance partial_index_map_equiv {domain range:nat}:
  Equiv (partial_index_map domain range)
  :=
    fun fp gp =>
      let f := partial_index_f _ _ fp in
      let g := partial_index_f _ _ gp in
      forall (x:nat) (xd: x<domain), f x = g x.

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
             {d r: nat}
             (f: index_map d r)
    := 
      forall (x y:nat) (xc: x<d) (yc: y<d),
         ⟦ f ⟧ x ≡ ⟦ f ⟧ y → x ≡ y.

  Definition index_map_surjective
             {d r: nat}
             (f: index_map d r)
    :=
      forall (y:nat) (yc: y<r), exists (x:nat) (xc: x<d), ⟦ f ⟧ x ≡ y.

  Definition index_map_bijective
            {n: nat}
            (f: index_map n n)
    :=
      (index_map_injective f) /\ (index_map_surjective f).

  (* "A partial function is said to be injective or surjective when
  the total function given by the restriction of the partial function
  to its domain of definition is." *)

  Definition partial_index_map_injective
             {d r: nat}
             (fp: partial_index_map d r)
    := 
      let f := partial_index_f _ _ fp in
      forall (x y:nat) (xc: x<d) (yc: y<d) v, 
        (f x ≡ Some v /\ f y ≡ Some v) → x ≡ y.

  Definition partial_index_map_surjective
             {d r: nat}
             (fp: partial_index_map d r)
    :=
      let f := partial_index_f _ _ fp in
      forall (y:nat) (yc: y<r), exists (x:nat) (xc: x<d),  f x ≡ Some y.
  
  Definition partial_index_map_bijective
             {n: nat}
             (f: partial_index_map n n)
    :=
      (partial_index_map_injective f) /\ (partial_index_map_surjective f).
  
End Jections.

Section Inversions.

  Fact h'_dom (domain x z : nat) (f: nat->nat):
    List.fold_right
      (λ (x' : nat) (p : option nat),
       if eq_nat_dec x (f x') then Some x' else p) None
      (rev_natrange_list domain) ≡ Some z → z < domain.
  Proof.
    intros H.
    induction domain.
    simpl in *.  congruence.
    simpl in H.
    destruct (eq_nat_dec x (f domain)).
    inversion H.
    lia.
    crush.
  Qed.

  (* Theoretically, we can only build inverse of injective functions. However this
definition does not enforce this requirement, and the function produced might not be
   true inverse in mathematical sense. To make sure it is, checl (index_map_injective f) *)
  Program Definition build_inverse_index_map
          {i o: nat}
          (f: index_map i o)
    : partial_index_map o i
    := PartialIndexMap o i (fun y =>
                              List.fold_right
                                (fun x' p => if eq_nat_dec y ( ⟦ f ⟧ x') then Some x' else p)
                                None
                                (rev_natrange_list i)) _.
  Next Obligation.
    
    destruct f.  simpl in *.
    apply h'_dom with (x:=x) (f:=index_f0).
    assumption.
  Defined.


  Lemma build_inverse_index_map_is_left_inverse
             {i o: nat}
             (f: index_map i o)
             (f_inj: index_map_injective f):
    let fp := build_inverse_index_map f in
    let f' := partial_index_f _ _ fp in
    forall x y (xc:x<i), ⟦ f ⟧ x ≡ y -> f' y ≡ Some x.
  Proof.
    intros fp f' x y xc A.
    destruct f.
    unfold index_map_injective in f_inj.
    unfold build_inverse_index_map in fp.
    simpl in *.
    unfold f'.
    subst y.
    clear fp f'.
    
    induction i.
    - nat_lt_0_contradiction.
    - simpl.
      destruct (eq_nat_dec (index_f0 x) (index_f0 i)) as [E|N].
      apply f_inj in E; auto.
      apply IHi; auto.
      destruct (eq_nat_dec x i).
      + congruence.
      + lia.
  Qed.
  
End Inversions.
  

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
          {snz: s ≢ 0} (* required constraint, according by Franz *)
    : index_map domain range
    :=
      IndexMap domain range (fun i => b + i*s) _.
  Next Obligation.
    nia.
  Defined.

  Lemma h_index_map_is_injective
        {domain range: nat}
        (b s: nat)
        {range_bound: (b+(pred domain)*s) < range}
        {snz: s ≢ 0}:
    index_map_injective  (@h_index_map domain range b s range_bound snz).
  Proof.
    unfold index_map_injective.
    intros x y xc yc H.
    simpl in H.
    nia.
  Qed.

  Fact h'_returns_from_h_domain (r x:nat) (f: nat->nat) l:
    List.fold_right
      (λ (x' : nat) (p : option nat),
       if eq_nat_dec x (f x') then Some x' else p) None
      l ≡ Some r -> f r ≡ x.
  Proof.
    intros.
    induction l.
    + simpl in H. congruence.
    + simpl in H.
      destruct (eq_nat_dec x (f a)).
    - inversion H as [R]; rewrite <- R; symmetry; assumption.
    - apply IHl; assumption.
  Qed.
  
  Lemma h_index_map'_is_injective
        {domain range: nat}
        (b s: nat)
        {range_bound: (b+(pred domain)*s) < range}
        {snz: s ≢ 0}:
    partial_index_map_injective
      (build_inverse_index_map 
         (@h_index_map domain range b s range_bound snz)
      ).
  Proof.
    unfold partial_index_map_injective.
    intros x y xc yc v H.
    destruct H as [H1 E].
    rewrite <- H1 in E. 
    remember (build_inverse_index_map (h_index_map b s)) as hp'.
    unfold build_inverse_index_map in Heqhp'.
    destruct hp' as [h' h'_spec].
    simpl in E, H1.
    inversion Heqhp' as [H]. clear Heqhp'.
    remember (rev_natrange_list domain) as l.

    subst_max.
    dependent induction domain.
    + crush.
    + simpl in E.
      destruct 
        (eq_nat_dec y (b + domain * s)) as [yT | yF],
                                           (eq_nat_dec x (b + domain * s)) as [xT | xF].

    - subst x y; reflexivity.
    - symmetry in E.
      apply h'_returns_from_h_domain in E.
      congruence.
    - apply h'_returns_from_h_domain in E.
      congruence.
    - apply IHdomain with (range:=range) (b:=b) (s:=s) (v:=v); try assumption.
      nia.
      intros; apply h'_dom with (x:=x0) (f:=fun x' => b+x'*s); assumption.
      {
        simpl in H1.
        destruct (eq_nat_dec x (b + domain * s)).
        congruence.
        apply H1.
      }
  Qed.
  
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
      {c1_ne_0: 1≢0}
    ,
      @identity_index_map n np = @h_index_map n n 0 1
                                              range_bound_h_0 c1_ne_0.
  Proof.
    intros.
    unfold identity_index_map, h_index_map, equiv, index_map_equiv, id.
    intros. simpl.
    symmetry. apply mult_1_r.
  Qed.

  Local Close Scope index_f_scope.
        
End Function_Rules.
  

