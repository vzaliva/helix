(* Coq defintions for Sigma-HCOL operator language *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

Global Open Scope nat_scope.

(* Vector index mapping functon which maps between two sets of natrual
     numers. Mapping is partial and it returns None if there is no correspondance
     between a number in source set and target set. *)
Definition index_map_spec (domain range: nat) :=
  forall n : nat, n < domain -> {v : option nat | forall n' : nat, v ≡ Some n' -> n' < range}.

(* Returns upper domain bound for given `index_map_spec` *)
Definition index_map_dom {d r:nat} (s: index_map_spec d r) := d.

(* Returns upper rang bound for given `index_map_spec` *)
Definition index_map_range {d r:nat} (s: index_map_spec d r) := r.

Section TotalIndexMap.

  (* Vector index mapping functon which maps between two sets of natrual
     numers. *)
  Definition total_index_map_spec (domain range: nat) :=
    forall n : nat, n < domain -> {v : nat | v < range}.
  
  (* Returns upper domain bound for given `total_index_map_spec` *)
  Definition total_index_map_dom {d r:nat} (s: total_index_map_spec d r) := d.
  
  (* Returns upper rang bound for given `total_index_map_spec` *)
  Definition total_index_map_range {d r:nat} (s: total_index_map_spec d r) := r.

  Section Primitive_Functions.
    
    Program Definition identity_index_map
            {domain range: nat}
            {drdep: domain ≡ range}:
      total_index_map_spec domain range
      :=
        fun i i_dim => i.
    
    Program Definition constant_index_map
            {range: nat}
            (j: nat)
            {jdep: j<range}:
      total_index_map_spec 1%nat range
      :=
        fun _ _ => j.
    
    Program Definition add_index_map
            {domain range: nat}
            (k: nat)
            {kdep: k+domain <= range}:
      total_index_map_spec domain range
      :=
        fun i i_dim => i+k.
    Next Obligation.
      lia.
    Defined.

  End Primitive_Functions.

  Section Function_Operators.
    
    Definition total_index_map_compose
               {i o t: nat}
               (g: total_index_map_spec t o)
               (f: total_index_map_spec i t) :
      total_index_map_spec i o
      := fun x xdom_bound =>
           (* manual uncurry *)
           let (fv, fv_dom_bound) := f x xdom_bound in
           g fv fv_dom_bound.

    Program Definition total_index_map_tensor_product
               {m n M N: nat}
               {nz: 0 ≢ n}
               (f: total_index_map_spec m M)
               (g: total_index_map_spec n N):
      total_index_map_spec (m*n) (M*N)
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
                    (total_index_map_tensor_product_obligation_1 m n M N nz f g i H)) as fg.
      generalize (g (pred n - snd (divmod i (pred n) 0 (pred n)))
                    (total_index_map_tensor_product_obligation_2 m n M N nz f g i H)) as gg.
      intros.
      destruct gg as [gv ga].
      destruct fg as [fv fa].
      simpl.
      nia.
    Defined.
    
  End Function_Operators.
  
  
End TotalIndexMap.
