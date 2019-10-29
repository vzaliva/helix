(* Sparse-vector-based implementations of SHCOL operators *)

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.HCOL.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import Helix.Tactics.HelixTactics.
Require Import Psatz.
Require Import Omega.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.theory.setoids.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Import Monoid.

Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

(* Returns an element of the vector 'x' which is result of mapping of
given natrual number by index mapping function `f`. *)
Definition VnthIndexMapped
           {i o:nat}
           {A: Type}
           (x: vector A i)
           (f: index_map o i)
           (n:nat) (np: n<o)
  : A
  := Vnth x (« f » n np).

Set Implicit Arguments.

Section FlagsMonoidGenericOperators.

  Variable fm:Monoid RthetaFlags.

  Definition liftM_HOperator_impl
             {i o}
             (op: avector i -> avector o)
    : svector fm i -> svector fm o :=
    sparsify fm ∘ op ∘ densify fm.

  Global Instance liftM_HOperator_impl_proper
         {i o}
         (op: avector i -> avector o)
         `{HOP: HOperator i o op}
    :
      Proper ((=) ==> (=)) (liftM_HOperator_impl op).
  Proof.
    intros x y H.
    unfold liftM_HOperator_impl.
    unfold compose.
    f_equiv.
    rewrite H.
    reflexivity.
  Qed.


    Definition Pick_impl
               {o b:nat}
               (bc: b < o)
               (z: CarrierA)
               (x: svector fm 1):
      svector fm o
      := Vbuild (fun j jc =>
                   match Nat.eq_dec j b with
                   | in_left => Vhead x
                   | right fc => mkStruct z
                   end).

    Global Instance Pick_impl_arg_proper
           {o b: nat}
           (bc: b < o)
           (z: CarrierA):
      Proper ((=) ==> (=)) (Pick_impl bc z).
    Proof.
      intros x x' Ex.
      unfold Pick_impl.
      vec_index_equiv j jp.
      rewrite 2!Vbuild_nth.
      break_if.
      rewrite Ex.
      reflexivity.
      reflexivity.
    Qed.

    Definition Embed_impl
               {i b:nat}
               (bc: b < i)
               (v: svector fm i)
      := [Vnth v bc].

    Global Instance Embed_impl_proper
           {i b:nat}
           (bc: b < i):
      Proper ((=) ==> (=)) (Embed_impl bc).
    Proof.
      intros x y E.
      unfold Embed_impl.
      apply Vcons_single_elim.
      apply Vnth_equiv; auto.
    Qed.

    Definition Gather_impl
               {i o: nat}
               (f: index_map o i)
               (x: svector fm i):
      svector fm o
      := Vbuild (VnthIndexMapped x f).

    Global Instance Gather_impl_proper
           {i o: nat}:
      Proper ((=) ==> (=) ==> (=)) (@Gather_impl i o).
    Proof.
      intros f g Efg x y Exy.
      unfold Gather_impl, VnthIndexMapped.
      vec_index_equiv j jp.
      rewrite 2!Vbuild_nth.
      apply Vnth_equiv.
      apply Efg, jp.
      apply Exy.
    Qed.

    Definition Scatter_impl
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (idv: CarrierA)
               (x: svector fm i) : svector fm o
      :=
        let f' := build_inverse_index_map f in
        Vbuild (fun n np =>
                  match decide (in_range f n) with
                  | left r => Vnth x (inverse_index_f_spec f f' n r)
                  | right _ => mkStruct idv
                  end).

    Global Instance Scatter_impl_proper
           {i o: nat}
           (f: index_map i o)
           {f_inj: index_map_injective f}:
      Proper ((=) ==> (=) ==> (=)) (@Scatter_impl i o f f_inj).
    Proof.
      intros z0 z1 Ez x y Exy.
      unfold Scatter_impl.
      vec_index_equiv j jp.
      simpl.
      rewrite 2!Vbuild_nth.
      break_match.
      - apply Vnth_arg_equiv, Exy.
      - rewrite Ez.
        reflexivity.
    Qed.


    (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
    Definition SHPointwise_impl
               {n: nat}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               (x: svector fm n): svector fm n
      := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

    Global Instance SHPointwise_impl_proper {n: nat}:
      Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=)) (@SHPointwise_impl n).
    Proof.
      intros f f' Ef x y Exy.
      unfold SHPointwise_impl.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM.
      f_equiv.
      apply Ef.
      f_equiv.
      apply evalWriter_proper.
      apply Vnth_arg_equiv.
      apply Exy.
    Qed.

    Definition SHBinOp_impl
               {o: nat}
               (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
               (v:svector fm (o+o)): svector fm o
      :=  match (vector2pair o v) with
          | (a,b) => Vbuild (fun i (ip:i<o) => liftM2 (f (mkFinNat ip)) (Vnth a ip) (Vnth b ip))
          end.

    Global Instance SHBinOp_impl_proper {o:nat}:
      Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=)) (@SHBinOp_impl o).
    Proof.
      intros f f' Ef x y E.
      unfold SHBinOp_impl.

      vec_index_equiv j jc.
      unfold vector2pair.

      repeat break_let.
      rename Heqp into H0, Heqp0 into H1.

      replace t with (fst (Vbreak x)) by (rewrite H0 ; reflexivity).
      replace t0 with (snd (Vbreak x)) by (rewrite H0 ; reflexivity).
      replace t1 with (fst (Vbreak y)) by (rewrite H1 ; reflexivity).
      replace t2 with (snd (Vbreak y)) by (rewrite H1 ; reflexivity).
      clear H0 H1.

      rewrite 2!Vbuild_nth.

      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM2.

      f_equiv.
      apply Ef.
      reflexivity.
      - apply evalWriter_proper.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
      - apply evalWriter_proper.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
    Qed.

    Definition SHInductor_impl
               (n:nat)
               (f: CarrierA -> CarrierA -> CarrierA)
               (initial: CarrierA)
               (x: svector fm 1): svector fm 1
      := Lst ((liftM (HCOLImpl.Inductor n f initial)) (Vhead x)).

    Global Instance SHInductor_impl_proper {n:nat}:
      Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@SHInductor_impl n).
    Proof.
      intros f f' Ef.
      intros ini ini' Eini.
      intros x y E.
      unfold SHInductor_impl.
      apply Vcons_proper. 2:{ reflexivity. }
      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM.
      apply HCOLImpl.Inductor_proper; auto.
      f_equiv.
      rewrite E;reflexivity.
    Qed.

    (** Apply family of functions to same vector and return matrix of results *)
    Definition Apply_Family'
               {i o n}
               (op_family_f: forall k, (k<n) -> svector fm i -> svector fm o)
               (v: svector fm i) :
      vector (svector fm o) n :=
      Vbuild
        (λ (j:nat) (jc:j<n),  (op_family_f j jc) v).


    Global Instance Apply_Family'_arg_proper
           {i o n}
           (op_family_f: forall k, (k<n) -> svector fm i -> svector fm o)
           (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
      :
        Proper ((=) ==> (=)) (@Apply_Family' i o n op_family_f).
    Proof.
      intros x y E.
      unfold Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      apply op_family_f_proper, E.
    Qed.


  (** Matrix-union. This is a common implementations for IUnion and IReduction *)
  Definition Diamond
             {i o n}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
             (v:svector fm i): svector fm o
    :=
      MUnion fm dot initial (Apply_Family' op_family_f v).


  Global Instance Diamond_proper
         {i o n}
    : Proper (
          (=) ==> (=) ==>
              (@forall_relation nat
                                (fun k : nat =>  forall _ : k<n, (svector fm i -> svector fm o))
                                (fun k : nat =>  @pointwise_relation (k < n)
                                                                (svector fm i -> svector fm o) (=)))
              ==> (=) ==> (=)) (@Diamond i o n).
  Proof.
    intros d d' Ed ini ini' Ei f f' Ef v v' Ev.
    unfold Diamond.
    apply MUnion_proper; auto.

    unfold Apply_Family'.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    unfold forall_relation, pointwise_relation in Ef.
    apply Ef, Ev.
  Qed.

  (* One might think we do not need this in presence of Diamond_proper. However even this partially applied morphism could be easily proven from Diamond_proper sometimes helps class resolutuion which does not always find Diamond_proper *)
  Global Instance Diamond_arg_proper
         {i o n}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
         (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
    : Proper ((=) ==> (=)) (Diamond dot initial op_family_f).
  Proof.
    apply Diamond_proper.
    - apply pdot.
    - reflexivity.
    - unfold forall_relation, pointwise_relation.
      apply op_family_f_proper.
  Qed.

End FlagsMonoidGenericOperators.
