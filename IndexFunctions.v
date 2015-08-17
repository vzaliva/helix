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

Require Export ListUtil.

Global Open Scope nat_scope.

(* Vector index mapping functon which maps between two sets of natrual
     numers. *)
Definition index_map_spec (domain range: nat) :=
  forall n : nat, n < domain -> {v : nat | v < range}.

(* Returns upper domain bound for given `index_map_spec` *)
Definition index_map_dom {d r:nat} (s: index_map_spec d r) := d.

(* Returns upper rang bound for given `index_map_spec` *)
Definition index_map_range {d r:nat} (s: index_map_spec d r) := r.

Fixpoint natrange_list (n:nat) : list nat :=
  match n with
  | 0 => nil
  | S p => cons p (natrange_list p)
  end.

Lemma natrange_to_cons (n:nat):
  natrange_list (S n) ≡ cons n (natrange_list n).
Proof.
  auto.
Qed.

Lemma natrage_le (n:nat):
  forall x, In x (natrange_list n) -> x<n.
Proof.
  intros.
  induction n.
  simpl in H. contradiction.

  rewrite natrange_to_cons in H.
  rewrite In_cons in H.
  destruct H; crush.
Qed.


Lemma lt_pred_l {n m} (H: S n < m): n < m.
Proof.
  auto with arith.
Defined.

Fixpoint natrange_f_spec
         (n:nat)
         {i o: nat}
         (nd: n<i)
         (f_spec: index_map_spec i o)
  : list nat
  :=
    match n return list nat with
    | 0 => nil
    | S n' => cons n' (natrange_f_spec n' (lt_pred_l nd) f_spec)
    end.

Program Definition index_map_f_is_permutation
           {n: nat}
           (f_spec: index_map_spec n n) :=
  let i := natrange_list n in
  let o := map (fun z => proj1_sig (f_spec (natrage_le n z))) i in
  Permutation i o.

Lemma xxx:
  (f1: index_func)
    (f2: index_func)
    index_map_f_is_permutation f1 ->
  index_map_f_is_permutation f2 ->
  index_map_f_is_permutation (tens f1 f2)

Lemma l1: index_map_f_is_permutation (f_id).
Proof.
  ...
  Qed.

index_map_f_is_permutation (f_id) -> .....

Section Primitive_Functions.
  
  Program Definition identity_index_map
          {domain range: nat}
          {drdep: domain ≡ range}:
    index_map_spec domain range
    :=
      fun i i_dim => i.
  
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

