Require Coq.Program.Basics.
Require Coq.Program.Equality.
Require Omega.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Vectors.Vector.
Require CoLoR.Util.Vector.VecUtil.
Require Coq.Logic.Eqdep.
Require Coq.Lists.List.
Require Coq.Logic.JMeq.
Require Coq.Arith.Lt.
Require Coq.Arith.Peano_dec.
Require MathClasses.interfaces.canonical_names.
Require Coq.Arith.Arith.
Require Coq.Arith.Minus.
Require Coq.Arith.EqNat.
Require Coq.Program.Program.
Require Coq.Classes.Morphisms.
Require Coq.Strings.String.
Require Coq.Logic.Decidable.
Require Coq.micromega.Psatz.
Require MathClasses.interfaces.abstract_algebra.
Require MathClasses.interfaces.orders.
Require MathClasses.orders.minmax.
Require MathClasses.orders.orders.
Require MathClasses.orders.rings.
Require MathClasses.theory.abs.
Require MathClasses.theory.setoids.
Require CoLoR.Util.Nat.NatUtil.
Require Coq.micromega.Lia.
Require CoLoR.Util.List.ListUtil.
Require MathClasses.theory.rings.
Require MathClasses.theory.naturals.
Require Coq.Bool.Bool.
Require Coq.setoid_ring.Ring.
Require ExtLib.Core.Type.
Require ExtLib.Structures.Monads.
Require ExtLib.Structures.MonadLaws.
Require ExtLib.Data.Monads.WriterMonad.
Require ExtLib.Data.Monads.IdentityMonad.
Require ExtLib.Structures.Monoid.
Require ExtLib.Data.PPair.
Require Coq.Classes.RelationClasses.
Require Coq.Relations.Relations.
Require Coq.Arith.Plus.
Require MathClasses.implementations.peano_naturals.
Require Coq.Sorting.Permutation.
Require Coq.Init.Specif.
Require Coq.Sets.Ensembles.
Require Coq.Bool.BoolEq.
Require MathClasses.orders.semirings.
Require ExtLib.Structures.Monad.
Require Coq.Arith.Compare_dec.
Require Coq.Setoids.Setoid.
Require Coq.Logic.ProofIrrelevance.
Require Coq.Logic.Eqdep_dec.

Module Spiral_DOT_Spiral.
  Module Spiral.
    Module Spiral.

      Global Generalizable All Variables.
      Import Coq.Arith.Arith.
      Import Coq.Arith.Minus.
      Import Coq.Arith.EqNat.
      Import Coq.Arith.Lt.
      Import Coq.Program.Program.
      Import Coq.Classes.Morphisms.
      Import Coq.Strings.String.
      Import Coq.Logic.Decidable.
      Import Coq.micromega.Psatz.
      Import Omega.
      Import Coq.Logic.FunctionalExtensionality.
      Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
      Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
      Import MathClasses.theory.abs.
      Import MathClasses.theory.setoids.
      Import CoLoR.Util.Nat.NatUtil.


      Global Instance max_proper A `{Le A, TotalOrder A, !Setoid A} `{!∀ x y: A, Decision (x ≤ y)}:
        Proper ((=) ==> (=) ==> (=)) max.
      Admitted.

      Global Instance negate_proper A `{Ar: Ring A} `{!Setoid A}:
        Setoid_Morphism (negate).
      Admitted.


      Global Instance abs_Setoid_Morphism A
             `{Ar: Ring A}
             `{Asetoid: !Setoid A}
             `{Ato: !@TotalOrder A Ae Ale}
             `{Aabs: !@Abs A Ae Ale Azero Anegate}
        : Setoid_Morphism abs | 0.
      Admitted.

      Global Instance abs_idempotent
             `{Ae: Equiv A}
             `{Az: Zero A} `{A1: One A}
             `{Aplus: Plus A} `{Amult: Mult A}
             `{Aneg: Negate A}
             `{Ale: Le A}
             `{Ato: !@TotalOrder A Ae Ale}
             `{Aabs: !@Abs A Ae Ale Az Aneg}
             `{Ar: !Ring A}
             `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
        :UnaryIdempotent abs.
      Admitted.

      Local Open Scope nat_scope.

      Lemma S_j_lt_n {n j:nat}:
        S j ≡ n -> j < n.
      Admitted.

      Lemma Decidable_decision
            (P:Prop):
        Decision P -> decidable P.
      Admitted.

      Global Instance Sig_Equiv {A:Type} {Ae : Equiv A} {P:A->Prop}:
        Equiv (@sig A P) := fun a b => (proj1_sig a) = (proj1_sig b).

      Instance proj1_Proper {A:Type} {Ae : Equiv A} {P:A->Prop}:
        Proper ((=)==>(=)) (@proj1_sig A P).
      Admitted.


    End Spiral.
  End Spiral.
End Spiral_DOT_Spiral.

Module Spiral_DOT_VecUtil.
  Module Spiral.
    Module VecUtil.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Coq.Program.Basics.
      Import Coq.Program.Equality. (* for dependent induction *)
      Import Omega.
      Import Coq.Logic.FunctionalExtensionality.
      Export Coq.Vectors.Vector.
      Export CoLoR.Util.Vector.VecUtil.
      Import VectorNotations.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Coq.micromega.Lia.

      Local Open Scope program_scope. (* for \circ notation *)
      Open Scope vector_scope.

      (* Re-define :: List notation for vectors. Probably not such a good idea *)
      Notation "h :: t" := (cons h t) (at level 60, right associativity)
                           : vector_scope.


      (* Split vector into a pair: first  'p' elements and the rest. *)
      Definition vector2pair {A:Type} (p:nat) {t:nat} (v:vector A (p+t)) : (vector A p)*(vector A t) :=
        @Vbreak A p t v.


      Section VFold.
        Definition Vfold_right_aux {A B:Type} {n} (f:A->B->B) (initial:B) (v: vector A n): B := @Vfold_right A B f n v initial.
      End VFold.

      Section VectorPairs.

        Definition Ptail {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): (vector A n)*(vector B n)
          := match ab with
             | (va,vb) => ((Vtail va), (Vtail vb))
             end.

      End VectorPairs.

      Section VMap2_Indexed.

        Definition Vmap2Indexed {A B C : Type} {n}
                   (f: nat->A->B->C) (a: vector A n) (b: vector B n)
          := Vbuild (fun i ip => f i (Vnth a ip) (Vnth b ip)).

      End VMap2_Indexed.


      Definition Lst {B:Type} (x:B) := [x].




      (* --- Some tactics --- *)


    End VecUtil.

  End Spiral.

End Spiral_DOT_VecUtil.

Module Spiral_DOT_VecSetoid.
  Module Spiral.
    Module VecSetoid.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Coq.Arith.Arith.
      Import Coq.Program.Basics. (* for \circ notation *)
      Export Coq.Vectors.Vector.
      Import Omega.

      (* CoRN MathClasses *)
      Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
      Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
      Import MathClasses.theory.rings MathClasses.theory.abs.
      Import MathClasses.theory.naturals.


      (* CoLoR *)
      Export CoLoR.Util.Vector.VecUtil.
      Import VectorNotations.


      (* Various definitions related to vector equality and setoid rewriting *)

      Section VectorSetoid.

        Global Instance vec_Equiv `{Equiv A} {n}: Equiv (vector A n)
          := Vforall2 (n:=n) equiv.

        Global Instance vec_Equivalence `{Ae: Equiv A} {n:nat}
               `{!Equivalence (@equiv A _)}
          : Equivalence (@vec_Equiv A Ae n).
        Admitted.

        Global Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
        Admitted.

      End VectorSetoid.


      Section Vconst.
        Context
          `{eqA: Equiv A}.

        Definition Vconst_reord {n} (x:A): vector A n :=
          Vconst x n.


        Global Instance Vconst_reord_proper {n}:
          Proper ((=)==>(=)) (@Vconst_reord n).
        Admitted.

      End Vconst.



      (* TODO: check if needed for Coq-8.6 *)
      Section Vfold_left.
        Context
          `{eqA: Equiv A}
          `{eqB: Equiv B}.

        Definition Vfold_left_reord {A B:Type} {n} (f:A->B->A) (initial:A) (v: vector B n): A := @Vfold_left A B f n initial v.


        Global Instance Vfold_left_reord_proper n :
          Proper (((=) ==> (=) ==> (=)) ==> ((=) ==> (=) ==> (=)))
                 (@Vfold_left_reord A B n).
        Admitted.

      End Vfold_left.

      (* TODO: check if needed for Coq-8.6 *)
      Section Vfold_left_rev.
        Context
          `{eqA: Equiv A}
          `{eqB: Equiv B}.

        Definition Vfold_left_rev_reord {A B:Type} {n} (f:A->B->A) (initial:A) (v: vector B n): A := @Vfold_left_rev A B f n initial v.


        Global Instance Vfold_left_rev_reord_proper n :
          Proper (((=) ==> (=) ==> (=)) ==> ((=) ==> (=) ==> (=)))
                 (@Vfold_left_rev_reord A B n).
        Admitted.

      End Vfold_left_rev.

      (* TODO: check if needed for Coq-8.6 *)
      Section Vfold_right.
        Context
          `{eqA: Equiv A}
          `{eqB: Equiv B}.

        Definition Vfold_right_reord {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B): B := @Vfold_right A B f n v initial.


        Global Instance Vfold_right_reord_proper n :
          Proper (((=) ==> (=) ==> (=)) ==> ((=) ==> (=) ==> (=)))
                 (@Vfold_right_reord A B n).
        Admitted.

        Global Instance Vfold_right_aux_proper n :
          Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
                 (@Vfold_right_aux A B n).
        Admitted.

      End Vfold_right.

      (* TODO: check if needed for Coq-8.6 *)
      Section VCons.

        Definition Vcons_reord {A} {n} (t: vector A n) (h:A): vector A (S n) := Vcons h t.


        Global Instance Vcons_reord_proper `{Equiv A} n:
          Proper ((=) ==> (=) ==> (=))
                 (@Vcons_reord A n).
        Admitted.

      End VCons.

      Global Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
        Proper ((=) ==>  (=) ==> (=)) (@Vapp A n1 n2).
      Admitted.

      Global Instance Vhead_proper `{Equiv A} n:
        Proper ((=) ==> (=)) (@Vhead A n).
      Admitted.

      Global Instance Vtail_proper `{Equiv A} n:
        Proper ((=) ==> (=)) (@Vtail A n).
      Admitted.

      Global Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
        Proper ((=) ==> (=)) (@Ptail A B n).
      Admitted.

      (* TODO: Check if it is still needed in Coq-8.6 *)
      Section VMap_reord.

        Definition Vmap_reord (A B: Type) (n:nat) (f:A->B) (x: vector A n): vector B n := Vmap f x.

        Global Instance Vmap_reord_proper n (M N:Type) `{Ne:!Equiv N, Me:!Equiv M}:
          Proper (((=) ==> (=)) ==> (=) ==> (=))
                 (@Vmap_reord M N n).
        Admitted.


        Global Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
               `{fP: !Proper (Me ==> Ne) f} (n:nat):
          Proper ((@vec_Equiv M _ n) ==> (@vec_Equiv N _ n)) (@Vmap M N f n).
        Admitted.

      End VMap_reord.


      Global Instance VBreak_proper (A:Type) `{Setoid A} (n1 n2:nat) `{Plus nat}:
        Proper ((=) ==> (=)) (@Vbreak A n1 n2).
      Admitted.

      Global Instance Vmap2Indexed_proper
             `{Setoid A, Setoid B, Setoid C} {n:nat}
        :
          Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
                 (@Vmap2Indexed A B C n).
      Admitted.

      Global Instance indexed_vector_equiv `{Equiv A} {n}:
        Equiv (∀ i : nat, i < n → vector A n)
        :=  @forall_relation nat
                             (fun i : nat =>  forall _ : i<n, vector A n)
                             (fun i : nat =>  @pointwise_relation (i < n)
                                                             (vector A n) (=)).

      (* @jwiegley version *)
      Global Instance Vbuild_proper {n : nat} {A:Type} `{Equiv A}:
        Proper ((forall_relation
                   (fun i => pointwise_relation (i < n)%nat equiv)) ==> equiv)
               (@Vbuild A n).
      Admitted.

      (* --- Tactics --- *)


    End VecSetoid.

  End Spiral.

End Spiral_DOT_VecSetoid.

Module Spiral_DOT_CarrierType.
  Module Spiral.
    Module CarrierType.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.

      Import CoLoR.Util.Vector.VecUtil.
      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.theory.rings.
      Import MathClasses.interfaces.orders.

      Parameter CarrierA: Type.
      Parameter CarrierAe: Equiv CarrierA.
      Parameter CarrierAsetoid: @Setoid CarrierA CarrierAe.
      Parameter CarrierAz: Zero CarrierA.
      Parameter CarrierA1: One CarrierA.
      Parameter CarrierAplus: Plus CarrierA.
      Parameter CarrierAmult: Mult CarrierA.
      Parameter CarrierAneg: Negate CarrierA.
      Parameter CarrierAle: Le CarrierA.
      Parameter CarrierAlt: Lt CarrierA.
      Parameter CarrierAto: @TotalOrder CarrierA CarrierAe CarrierAle.
      Parameter CarrierAabs: @Abs CarrierA CarrierAe CarrierAle CarrierAz CarrierAneg.
      Parameter CarrierAr: Ring CarrierA.
      Parameter CarrierAltdec: ∀ x y: CarrierA, Decision (x < y).
      Parameter CarrierAledec: ∀ x y: CarrierA, Decision (x ≤ y).
      Parameter CarrierAequivdec: ∀ x y: CarrierA, Decision (x = y).
      Parameter CarrierASSO: @StrictSetoidOrder CarrierA CarrierAe CarrierAlt.
      Parameter CarrierASRO: @SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle.

      Add Ring RingA: (stdlib_ring_theory CarrierA).

      Global Instance CarrierAPlus_proper:
        Proper ((=) ==> (=) ==> (=)) (plus).
      Admitted.

      Global Instance CommutativeMonoid_plus_zero:
        @MathClasses.interfaces.abstract_algebra.CommutativeMonoid CarrierA _ plus zero.
      Admitted.

      Notation avector n := (vector CarrierA n) (only parsing).

    End CarrierType.

  End Spiral.

End Spiral_DOT_CarrierType.

Module Spiral_DOT_WriterMonadNoT.
  Module Spiral.
    Module WriterMonadNoT.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Coq.Program.Basics. (* for (∘) *)
      Import ExtLib.Data.Monads.IdentityMonad.
      Import ExtLib.Data.Monads.WriterMonad.
      Import ExtLib.Structures.Monoid.
      Import ExtLib.Data.PPair.

      Set Implicit Arguments.
      Set Universe Polymorphism.

      Section MapWriterT.
        Variable A B: Type.
        Variable W W': Type.
        Variable Monoid_W : Monoid W.
        Variable Monoid_W' : Monoid W'.
        Variable m n : Type -> Type.

        Open Scope program_scope.

        (** Map both the return value and output of a computation using the given function.
        [[ 'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m) ]]
         *)
        Definition mapWriterT (f: (m (pprod A W)%type) -> (n (pprod B W')%type)):
          (writerT Monoid_W m A) -> writerT Monoid_W' n B
          :=
            mkWriterT Monoid_W' ∘ f ∘ runWriterT.

      End MapWriterT.


      Section CastWriterT.
        Variable A: Type.
        Variable W : Type.
        Variable Monoid_W Monoid_W': Monoid W.
        Variable m : Type -> Type.

        Open Scope program_scope.

        (* Special case of mapWriterT where mapping functoin is identity *)
        Definition castWriterT:
          writerT Monoid_W m A -> writerT Monoid_W' m A
          := mkWriterT Monoid_W' ∘ runWriterT.

      End CastWriterT.


      (** Simple wrapper around ExtLib's WriterMonadT trasformed pairing it with Identity monad to simulate classic Writer Monad *)
      Section WriterMonad.

        Variable W: Type.
        Variable A: Type.
        Variable Monoid_W : Monoid W.

        Open Scope program_scope.

        Definition writer := writerT Monoid_W ident.
        Definition runWriter := unIdent ∘ (@runWriterT W Monoid_W ident A).
        Definition execWriter:= psnd ∘ runWriter.
        Definition evalWriter:= pfst ∘ runWriter.

      End WriterMonad.

      Section CastWriter.
        Variable A: Type.
        Variable W : Type.
        Variable Monoid_W Monoid_W': Monoid W.

        Open Scope program_scope.

        (* Special case of mapWriter where mapping functoin is identity *)
        Definition castWriter: writer Monoid_W A -> writer Monoid_W' A
          := castWriterT Monoid_W' (m:=ident).

      End CastWriter.

    End WriterMonadNoT.

  End Spiral.

End Spiral_DOT_WriterMonadNoT.

Module Spiral_DOT_Rtheta.
  Module Spiral.
    Module Rtheta.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Export Spiral_DOT_CarrierType.Spiral.CarrierType.
      Import Coq.Bool.Bool.
      Import Coq.setoid_ring.Ring.
      Import ExtLib.Core.Type.
      Import ExtLib.Structures.Monads.
      Import ExtLib.Structures.MonadLaws.
      Import ExtLib.Data.Monads.WriterMonad.
      Import ExtLib.Data.Monads.IdentityMonad.
      Import ExtLib.Structures.Monoid.
      Import Spiral_DOT_WriterMonadNoT.Spiral.WriterMonadNoT.
      Import ExtLib.Data.PPair.

      (* CoRN MathClasses *)
      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.theory.rings.


      Import MonadNotation.
      Import Monoid.
      Local Open Scope monad_scope.


      Record RthetaFlags : Type :=
        mkRthetaFlags
          {
            is_struct: bool ;
            is_collision: bool
          }.

      (* Propositional predicates *)
      Definition IsCollision (x:RthetaFlags) := Is_true (is_collision x).
      Definition IsVal (x:RthetaFlags) := not (Is_true (is_struct x)).

      Global Instance RthetaFlags_equiv:
        Equiv RthetaFlags :=
        fun a b =>
          is_collision a ≡ is_collision b /\
          is_struct a ≡ is_struct b.

      Global Instance RthetaFlags_Reflexive_equiv: Reflexive RthetaFlags_equiv.
      Admitted.

      Global Instance RthetaFlags_Symmetric_equiv: Symmetric RthetaFlags_equiv.
      Admitted.

      Global Instance RthetaFlags_Transitive_equiv: Transitive RthetaFlags_equiv.
      Admitted.

      Global Instance RthetaFlags_Equivalence_equiv: Equivalence RthetaFlags_equiv.
      Admitted.

      Global Instance RthetaFlags_Setoid: @Setoid RthetaFlags RthetaFlags_equiv.
      Admitted.

      (* mzero *)
      Definition RthetaFlagsZero := mkRthetaFlags true false.

      Global Instance RthetaFlags_type:
        type RthetaFlags := type_libniz RthetaFlags.

      Section CollisionTrackingRthetaFlags.
        (* mappend which tracks collisions *)
        Definition RthetaFlagsAppend (a b: RthetaFlags) : RthetaFlags :=
          mkRthetaFlags
            (is_struct a && is_struct b)
            (is_collision a || (is_collision b ||
                               (negb (is_struct a || is_struct b)))).

        Definition Monoid_RthetaFlags : Monoid RthetaFlags := Build_Monoid RthetaFlagsAppend RthetaFlagsZero.


        (* Monoid is just a record and equivalence is established pointwise on fields *)
        Global Instance Monoid_equiv `{Equiv f}:
          Equiv (Monoid f) :=
          fun a b =>
            (monoid_plus a = monoid_plus b) /\
            (monoid_unit a = monoid_unit b).




        Global Instance MonoidLaws_RthetaFlags:
          MonoidLaws Monoid_RthetaFlags.
        Admitted.
      End CollisionTrackingRthetaFlags.

      Section SafeRthetaFlags.

        (* mappend which does not track collisions *)
        Definition RthetaFlagsSafeAppend (a b: RthetaFlags) : RthetaFlags :=
          mkRthetaFlags
            (andb (is_struct a) (is_struct b))
            (orb (is_collision a) (is_collision b)).

        Definition Monoid_RthetaSafeFlags : Monoid RthetaFlags := ExtLib.Structures.Monoid.Build_Monoid RthetaFlagsSafeAppend RthetaFlagsZero.




        Global Instance MonoidLaws_SafeRthetaFlags:
          MonoidLaws Monoid_RthetaSafeFlags.
        Admitted.

      End SafeRthetaFlags.

      Section RMonad.
        Variable fm:Monoid RthetaFlags.
        (* Monad_RthetaFlags is just a Writer Monad for RthetaFlags *)
        Definition Monad_RthetaFlags := writer fm.

        (* Generic Rtheta type is parametrized by Monoid, which defines how structural flags are handled. *)
        Definition Rtheta' := Monad_RthetaFlags CarrierA.
      End RMonad.

      Definition Rtheta := Rtheta' Monoid_RthetaFlags.
      Definition RStheta := Rtheta' Monoid_RthetaSafeFlags.

      (* Monad morhisms *)

      Definition Rtheta2RStheta: Rtheta -> RStheta := castWriter Monoid_RthetaSafeFlags.

      Definition RStheta2Rtheta: RStheta -> Rtheta := castWriter Monoid_RthetaFlags.

      (* Some convenience constructros *)

      Section Rtheta'Utils.
        Context {fm:Monoid RthetaFlags}.

        Definition mkStruct (val: CarrierA) : Rtheta' fm
          := ret val.

        Definition mkValue (val: CarrierA) : Rtheta' fm :=
          tell (mkRthetaFlags false false) ;; ret val.

        Definition Is_Val: (Rtheta' fm) -> Prop :=
          IsVal ∘ (@execWriter RthetaFlags CarrierA fm).

        Definition Is_Collision (x:Rtheta' fm) :=
          (IsCollision ∘ (@execWriter RthetaFlags CarrierA fm)) x.

        Definition liftRthetaP (P: CarrierA -> Prop): (Rtheta' fm) -> Prop :=
          fun x => P (evalWriter x).

        Definition Is_NonNegative (x:Rtheta' fm) : Prop := liftRthetaP (le 0) x.

        Definition Is_ValX (z:CarrierA)
          := fun (x:Rtheta' fm) => (WriterMonadNoT.evalWriter x) = z.



        Global Instance Rtheta'_equiv: Equiv (Rtheta' fm) :=
          fun am bm => (evalWriter am) = (evalWriter bm).

        Global Instance evalWriter_proper:
          Proper ((=) ==> (=)) (@evalWriter RthetaFlags CarrierA fm).
        Admitted.

        Global Instance liftRthetaP_proper
               (P: CarrierA -> Prop)
               (P_mor: Proper ((=) ==> iff) P)
          :
            Proper ((=) ==> iff) (@liftRthetaP P).
        Admitted.

        Global Instance Is_ValX_proper:
          Proper ((=) ==> (=) ==> (iff)) (Is_ValX).
        Admitted.

        Global Instance Rtheta_Reflexive_equiv:
          @Reflexive (Rtheta' fm) Rtheta'_equiv.
        Admitted.

        Global Instance Rtheta_Symmetric_equiv:
          @Symmetric (Rtheta' fm) Rtheta'_equiv.
        Admitted.

        Global Instance Rtheta_Transitive_equiv:
          @Transitive (Rtheta' fm) Rtheta'_equiv.
        Admitted.

        Global Instance Rtheta_Equivalence_equiv:
          @Equivalence (Rtheta' fm) Rtheta'_equiv.
        Admitted.

        Global Instance Rtheta_Setoid:
          @Setoid (Rtheta' fm) Rtheta'_equiv.
        Admitted.

      End Rtheta'Utils.

      (* For some reason class resolver could not figure this out on it's own *)
      Global Instance Rtheta_equiv: Equiv (Rtheta) := Rtheta'_equiv.
      Global Instance RStheta_equiv: Equiv (RStheta) := Rtheta'_equiv.

      Global Instance Rtheta2RStheta_proper
        : Proper ((=) ==> (=)) (Rtheta2RStheta).
      Admitted.

      Global Instance RStheta2Rtheta_proper
        : Proper ((=) ==> (=)) (RStheta2Rtheta).
      Admitted.

      Section Decidablitiy.
        Global Instance IsVal_dec (x: RthetaFlags) : Decision (IsVal x).
        Admitted.

        Global Instance Is_Val_dec
               {fm:Monoid RthetaFlags}
               (x: Rtheta' fm):
          Decision (Is_Val x).
        Admitted.

      End Decidablitiy.

      Section Zero_Utils.


        Global Instance mkValue_proper
               {fm:Monoid RthetaFlags}
        :
          Proper((=) ==> (=)) (@mkValue fm).
        Admitted.

        Global Instance mkStruct_proper
               {fm:Monoid RthetaFlags}
          :
            Proper((=) ==> (=)) (@mkStruct fm).
        Admitted.

        Definition Is_ValZero {fm:Monoid RthetaFlags}
          := @Is_ValX fm 0.

        Global Instance Is_ValZero_dec {fm:Monoid RthetaFlags} (x:Rtheta' fm):
          Decision (Is_ValZero x).
        Admitted.

        Global Instance Is_ValZero_proper
               {fm:Monoid RthetaFlags}
          :
            Proper ((=) ==> (iff)) (@Is_ValZero fm).
        Admitted.

      End Zero_Utils.


    End Rtheta.

  End Spiral.

End Spiral_DOT_Rtheta.

Module Spiral_DOT_SVector.
  Module Spiral.
    Module SVector.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.Rtheta.
      Import Coq.Bool.Bool.
      Import Coq.Arith.Arith.
      Import Coq.Logic.FunctionalExtensionality.
      Import MathClasses.interfaces.canonical_names.
      Import MathClasses.interfaces.abstract_algebra.

      Import VectorNotations.
      Import ExtLib.Structures.Monads.
      Import Spiral_DOT_WriterMonadNoT.Spiral.WriterMonadNoT.

      Import Monoid.

      Open Scope vector_scope.
      Open Scope nat_scope.

      (* Vector using Rtheta (exlusive) *)
      Notation rvector n := (vector Rtheta n) (only parsing).
      (* Vector using RStheta (safe) *)
      Notation rsvector n := (vector RStheta n) (only parsing).

      Definition rvector2rsvector := Vmap Rtheta2RStheta.
      Definition rsvector2rvector := Vmap RStheta2Rtheta.

      Section SvectorBasics.
        Variable fm:Monoid RthetaFlags.

        (* "sparse" vector for CarrierA type elements could be simulated using Rtheta *)
        Definition svector n := (vector (Rtheta' fm) n).

        (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
        Definition sparsify {n} (v:avector n): svector n :=
          Vmap mkValue v.

        Global Instance sparsify_proper {n:nat}:
          Proper ((=) ==> (=)) (@sparsify n).
        Admitted.

        (* Project out carrier type values from vector of Rheta values *)
        Definition densify {n} (v:svector n): avector n :=
          Vmap (A:=(Rtheta' fm)) (@evalWriter _ _ _) v.

        Global Instance densify_proper {n:nat}:
          Proper ((=) ==> (=)) (@densify n).
        Admitted.

      End SvectorBasics.

      Section Union.

        Variable fm:Monoid RthetaFlags.

        Definition Union (dot : CarrierA -> CarrierA -> CarrierA)
          : Rtheta' fm -> Rtheta' fm -> Rtheta' fm := liftM2 dot.



        Global Instance Union_proper:
          Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) Union.
        Admitted.

        (** Pointwise union of two vectors *)
        Definition Vec2Union
                   {n}
                   (dot:CarrierA->CarrierA->CarrierA)
                   (a b: svector fm n): svector fm n
          := Vmap2 (Union dot) a b.

        Global Instance Vec2Union_proper {n}
          :
            Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (Vec2Union (n:=n)).
        Admitted.

        Definition MUnion'
                   {o n}
                   (dot:CarrierA->CarrierA->CarrierA)
                   (initial:CarrierA)
                   (v: vector (svector fm o) n): svector fm o
          :=  Vfold_left_rev (Vec2Union dot) (Vconst (mkStruct initial) o) v.

        Global Instance MUnion'_proper {o n}
          : Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@MUnion' o n).
        Admitted.
      End Union.

      Section ExclusiveUnion.

      End ExclusiveUnion.


      Section NonExclusiveUnion.

      End NonExclusiveUnion.


      Close Scope vector_scope.
      Close Scope nat_scope.


    End SVector.

  End Spiral.

End Spiral_DOT_SVector.

Module Spiral_DOT_HCOLImpl.
  Module Spiral.
    Module HCOLImpl.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.CarrierType.
      Import Coq.Arith.Arith.
      Import Coq.Program.Program. (* compose *)
      Import Coq.Classes.Morphisms.
      Import Coq.Classes.RelationClasses.
      Import Coq.Relations.Relations.
      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.
      Import MathClasses.theory.rings.


      Import VectorNotations.

      Open Scope vector_scope.
      Open Scope nat_scope.

      Section HCOL_implementations.

        (* --- Type casts --- *)

        (* Promote scalar to unit vector *)
        Definition Vectorize (x:CarrierA): (avector 1) := [x].

        (* Convert single element vector to scalar *)
        Definition Scalarize (x: avector 1) : CarrierA := Vhead x.

        (* --- Scalar Product --- *)

        Definition ScalarProd
                   {n} (ab: (avector n)*(avector n)) : CarrierA :=
          match ab with
          | (a, b) => Vfold_right plus (Vmap2 mult a b) zero
          end.

        (* Poor man's minus *)
        Definition sub := plus∘negate.

        Global Instance CarrierA_sub_proper:
          Proper ((=) ==> (=) ==> (=)) (sub).
        Admitted.

        Definition VMinus
                   {n} (ab: (avector n)*(avector n)) : avector n :=
          match ab with
          | (a,b) => Vmap2 ((+)∘(-)) a b
          end.

        Fixpoint MonomialEnumerator
                 (n:nat) (x:CarrierA) {struct n} : avector (S n) :=
          match n with
          | O => [one]
          | S p => Vcons one (Vmap (mult x) (MonomialEnumerator p x))
          end.

        Fixpoint EvalPolynomial {n}
                 (a: avector n) (x:CarrierA) : CarrierA  :=
          match a with
            nil => zero
          | a0 :: a' => plus a0 (mult x (EvalPolynomial a' x))
          end.

        Definition BinOp {n}
                   (f: nat -> CarrierA -> CarrierA -> CarrierA)
                   (ab: (avector n)*(avector n))
          : avector n :=
          match ab with
          | (a,b) =>  Vmap2Indexed f a b
          end.

        Fixpoint Induction (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
                 (initial: CarrierA) (v: CarrierA) {struct n} : avector n
          :=
            match n with
            | O => []
            | S p => Vcons initial (Vmap (fun x => f x v) (Induction p f initial v))
            end.

        Definition Reduction {n:nat}
                   (f: CarrierA -> CarrierA -> CarrierA)
                   (id:CarrierA) (a: avector n) : CarrierA
          :=
            Vfold_right f a id.

        Definition Scale
                   {n} (sv:(CarrierA)*(avector n)) : avector n :=
          match sv with
          | (s,v) => Vmap (mult s) v
          end.

      End HCOL_implementations.
      Section HCOL_implementation_proper.

        Global Instance Scale_proper
               `{!Proper ((=) ==> (=) ==> (=)) mult} (n:nat)
        :
          Proper ((=) ==> (=)) (Scale (n:=n)).
        Admitted.

        Global Instance ScalarProd_proper (n:nat):
          Proper ((=) ==> (=))
                 (ScalarProd (n:=n)).
        Admitted.

        Global Instance BinOp_proper {n:nat}:
          Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=)) (BinOp (n:=n)).
        Admitted.

        Global Instance Reduction_proper {n:nat}:
          Proper (((=) ==> (=) ==>  (=)) ==> (=) ==> (=) ==> (=)) (Reduction (n:=n)).
        Admitted.

        Global Instance EvalPolynomial_proper (n:nat):
          Proper ((=) ==> (=) ==> (=))  (EvalPolynomial (n:=n)).
        Admitted.

        Global Instance MonomialEnumerator_proper (n:nat):
          Proper ((=) ==> (=))  (MonomialEnumerator n).
        Admitted.

        Global Instance Induction_proper {n:nat}:
          Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@Induction n).
        Admitted.

        Global Instance VMinus_proper (n:nat):
          Proper ((=) ==> (=))
                 (@VMinus n).
        Admitted.

      End HCOL_implementation_proper.

      Close Scope nat_scope.
      Close Scope vector_scope.
    End HCOLImpl.
  End Spiral.
End Spiral_DOT_HCOLImpl.

Module Spiral_DOT_HCOL.
  Module Spiral.
    Module HCOL.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.CarrierType.
      Import Spiral_DOT_HCOLImpl.Spiral.HCOLImpl.
      Import Coq.Arith.Arith.
      Import Coq.Arith.Plus.
      Import Coq.Program.Program.
      Import Coq.Classes.Morphisms.
      Import Coq.Logic.FunctionalExtensionality.

      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.
      Import MathClasses.implementations.peano_naturals.
      Import MathClasses.theory.setoids.


      Import VectorNotations.
      Open Scope vector_scope.

      Section HCOL_Language.

        Class HOperator {i o:nat} (op: avector i -> avector o) :=
          HOperator_setoidmor :> Setoid_Morphism op.


        Definition HPrepend {i n} (a:avector n)
          : avector i -> avector (n+i)
          := Vapp a.

        Definition HReduction {i}
                   (f: CarrierA -> CarrierA -> CarrierA)
                   `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                   (idv: CarrierA)
          : avector i -> avector 1
          := Vectorize ∘ (Reduction f idv).

        Definition HVMinus {o}
          : avector (o+o) -> avector o
          := VMinus  ∘ (vector2pair o).

        Definition HBinOp {o}
                   (f: nat -> CarrierA -> CarrierA -> CarrierA)
                   `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
          : avector (o+o) -> avector o
          :=  BinOp f ∘ (vector2pair o).

        Definition HEvalPolynomial {n} (a: avector n): avector 1 -> avector 1
          := Lst ∘ EvalPolynomial a ∘ Scalarize.

        Definition HMonomialEnumerator n
          : avector 1 -> avector (S n)
          := MonomialEnumerator n ∘ Scalarize.

        Definition HScalarProd {h}
          : avector (h+h) -> avector 1
          := Lst ∘ ScalarProd ∘ (vector2pair h).

        Definition HInduction (n:nat)
                   (f: CarrierA -> CarrierA -> CarrierA)
                   `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                   (initial: CarrierA)
          : avector 1 -> avector n
          := Induction n f initial ∘ Scalarize.

        Definition HPointwise
                   {n: nat}
                   (f: { i | i<n} -> CarrierA -> CarrierA)
                   `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                   (x: avector n)
          := Vbuild (fun j jd => f (j ↾ jd) (Vnth x jd)).

        Section HCOL_operators.

          Global Instance HPointwise_HOperator
                 {n: nat}
                 (f: { i | i<n} -> CarrierA -> CarrierA)
                 `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
            HOperator (@HPointwise n f pF).
          Admitted.

          Global Instance HScalarProd_HOperator {n}:
            HOperator (@HScalarProd n).
          Admitted.

          Global Instance HBinOp_HOperator {o}
                 (f: nat -> CarrierA -> CarrierA -> CarrierA)
                 `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
            HOperator (@HBinOp o f pF).
          Admitted.

          Global Instance HReduction_HOperator {i}
                 (f: CarrierA -> CarrierA -> CarrierA)
                 `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                 (idv: CarrierA):
            HOperator (@HReduction i f pF idv).
          Admitted.

          Global Instance HEvalPolynomial_HOperator {n} (a: avector n):
            HOperator (@HEvalPolynomial n a).
          Admitted.

          Global Instance HPrepend_HOperator {i n} (a:avector n):
            HOperator (@HPrepend i n a).
          Admitted.

          Global Instance HMonomialEnumerator_HOperator n:
            HOperator (@HMonomialEnumerator n).
          Admitted.

          Global Instance HInduction_HOperator {n:nat}
                 (f: CarrierA -> CarrierA -> CarrierA)
                 `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                 (initial: CarrierA):
            HOperator (HInduction n f initial).
          Admitted.

          Global Instance HVMinus_HOperator h:
            HOperator (@HVMinus h).
          Admitted.

        End HCOL_operators.
      End HCOL_Language.

      Section IgnoreIndex_wrapper.

        Definition SwapIndex2 {A} (i:nat) (f:nat->A->A->A) := const (B:=nat) (f i).

        Global Instance SwapIndex2_specialized_proper `{Setoid A} (i:nat) (f:nat->A->A->A)
               `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
          :
            Proper ((=) ==> (=) ==> (=) ==> (=)) (@SwapIndex2 A i f).
        Admitted.

        Definition IgnoreIndex2 {A} (f:A->A->A) := const (B:=nat) f.


        Global Instance IgnoreIndex2_proper `{Equiv A}:
          (Proper (((=) ==> (=)) ==> (=) ==> (=) ==> (=) ==> (=)) (@IgnoreIndex2 A)).
        Admitted.

        Definition IgnoreIndex {A:Type} {n:nat} (f:A->A) := const (B:=@sig nat (fun i : nat => @lt nat peano_naturals.nat_lt i n)) f.

        Global Instance IgnoredIndex_proper {n:nat} `{Equiv A}:
          (Proper
             (((=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@IgnoreIndex A n)).
        Admitted.

      End IgnoreIndex_wrapper.
    End HCOL.
  End Spiral.
End Spiral_DOT_HCOL.

Module Spiral_DOT_THCOLImpl.
  Module Spiral.
    Module THCOLImpl.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_CarrierType.Spiral.CarrierType.
      Import Coq.Arith.Arith.
      Import Coq.Program.Program.
      Import Coq.Classes.Morphisms.
      Import Coq.Classes.RelationClasses.
      Import Coq.Relations.Relations.
      Import Coq.Logic.FunctionalExtensionality.


      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.


      Import VectorNotations.
      Open Scope vector_scope.

      Section THCOL_implementations.

        (* Apply 2 functions to the same input returning tuple of results *)
        Definition Stack {D R F: Type} (fg:(D->R)*(D->F)) (x:D) : (R*F) :=
          match fg with
          | (f,g) => pair (f x) (g x)
          end.

        (* Apply 2 functions to 2 inputs returning tuple of results *)
        Definition Cross {D R E F: Type} (fg:(D->R)*(E->F)) (x:D*E) : (R*F) :=
          match fg with
          | (f,g) => match x with
                    | (x0,x1) => pair (f x0) (g x1)
                    end
          end.

        Definition Zless (a b: CarrierA): CarrierA
          := if CarrierAltdec a b then one else zero.

        Global Instance Zless_proper:
          Proper ((=) ==> (=) ==> (=)) (Zless).
        Admitted.

        (* --- Pointwise Comparison --- *)

        (* Zero/One version *)
        Definition ZVLess {n}
                   (ab: (avector n)*(avector n)) : avector n :=
          match ab with
          | (a,b) => Vmap2 (Zless) a b
          end.

        Global Instance ZVLess_proper {n:nat}:
          Proper ((=) ==> (=))  (@ZVLess n).
        Admitted.

      End THCOL_implementations.


      Section THCOL_implementation_proper.

        Global Instance Cross_arg_proper
               `{Equiv D,Equiv R,Equiv E,Equiv F}
               `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
               `{pG: !Proper ((=) ==> (=)) (g: E -> F)}:
          Proper ((=) ==> (=))  (Cross (f,g)).
        Admitted.

        Global Instance Stack_arg_proper
               `{Equiv D,Equiv R,Equiv F}
               `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
               `{pG: !Proper ((=) ==> (=)) (g: D -> F)}:
          Proper ((=) ==> (=))  (Stack (f,g)).
        Admitted.

      End THCOL_implementation_proper.



    End THCOLImpl.

  End Spiral.

End Spiral_DOT_THCOLImpl.

Module Spiral_DOT_THCOL.
  Module Spiral.
    Module THCOL.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.CarrierType.
      Import Spiral_DOT_THCOLImpl.Spiral.THCOLImpl.
      Import Spiral_DOT_HCOL.Spiral.HCOL.
      Import Coq.Arith.Arith.
      Import Coq.Program.Program.
      Import Coq.Classes.Morphisms.
      Import Coq.Classes.RelationClasses.
      Import Coq.Relations.Relations.
      Import Coq.Logic.FunctionalExtensionality.


      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.


      Import VectorNotations.
      Open Scope vector_scope.

      (* Templete HCOL operator which uses two HOperators to build a new HOperator *)
      Class THOperator2 {i1 o1 i2 o2 ix ox} (top: (avector i1 -> avector o1) -> (avector i2 -> avector o2) -> avector ix -> avector ox) :=
        THOperator2_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

      (* Curried Templete HCOL operator with arity 2 is HOperators *)
      Global Instance THOperator_HOperator
             `{O1: @HOperator i1 o1 op1}
             `{O2: @HOperator i2 o2 op2}
             `{T: @THOperator2 i1 o1 i2 o2 ix ox to}:
        HOperator (to op1 op2).
      Admitted.

      Global Instance compose_THOperator2 {o2 o3 i1 o2:nat}:
        @THOperator2 o2 o3 i1 o2 i1 o3 (compose).
      Admitted.


      Global Instance compose_HOperator
             {i1 o2 o3}
             `{hop1: HOperator o2 o3 op1}
             `{hop2: HOperator i1 o2 op2}
        :
          HOperator (op1 ∘ op2).
      Admitted.

    End THCOL.

  End Spiral.

End Spiral_DOT_THCOL.

Module Spiral_DOT_FinNatSet.
  Module Spiral.
    Module FinNatSet.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Export Coq.Init.Specif.
      Export Coq.Sets.Ensembles.
      Import Coq.Logic.Decidable.

      Notation FinNat n := {x:nat | (x<n)}.
      Notation FinNatSet n := (Ensemble (FinNat n)).

      Definition mkFinNat {n} {j:nat} (jc:j<n) : FinNat n := @exist _ (gt n) j jc.

    End FinNatSet.

  End Spiral.

End Spiral_DOT_FinNatSet.

Module Spiral_DOT_IndexFunctions.
  Module Spiral.
    Module IndexFunctions.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_FinNatSet.
      Import Spiral_DOT_FinNatSet.Spiral.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.

      (* Coq defintions for Sigma-HCOL operator language *)
      Import Coq.Arith.Arith.
      Import Coq.Strings.String.
      Import Coq.Arith.Peano_dec.
      Import Coq.Sorting.Permutation.
      Import Coq.Lists.List.
      Import Coq.Logic.FunctionalExtensionality.
      Import Coq.Arith.PeanoNat.Nat.
      Import Coq.micromega.Psatz.
      Import Omega.
      Import MathClasses.interfaces.canonical_names.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.
      Import MathClasses.implementations.peano_naturals.
      Import MathClasses.orders.orders.
      Import MathClasses.interfaces.abstract_algebra.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.


      (* Setoid equality for option types *)
      Section OptionSetoid.
        Global Instance option_Equiv `{Equiv A}: Equiv (option A) :=
          fun a b =>
            match a with
            | None => is_None b
            | Some x => (match b with
                        | None => False
                        | Some y => equiv x y
                        end)
            end.

        Global Instance option_Setoid `{Setoid A}: Setoid (@option A).
        Admitted.
      End OptionSetoid.

      Global Open Scope nat_scope.

      (* Index maps (total functions) *)

      Record index_map (domain range : nat) :=
        IndexMap
          {
            index_f : nat -> nat;
            index_f_spec : forall x, x<domain -> (index_f x) < range;
          }.

      Notation "⟦ f ⟧" := (@index_f _ _ f).
      Notation "« f »" := (@index_f_spec _ _ f).

      Global Instance index_map_equiv {domain range:nat}:
        Equiv (index_map domain range)
        :=
          fun f g => forall (x:nat) (xd: x<domain), ⟦ f ⟧ x = ⟦ g ⟧ x.

      (* Restriction on domain *)
      Definition shrink_index_map_domain {d r:nat} (f: index_map (S d) r)
        : index_map d r.
      Proof.
        destruct f.
        assert (new_spec : ∀ x : nat, x < d → index_f0 x < r) by auto.
        exact (IndexMap d r index_f0 new_spec).
      Defined.

      Section InRange.

        Fixpoint in_range  {d r:nat} (f: index_map d r)
                 (i:nat)
        : Prop :=
          match d return (index_map d r) -> Prop with
          | O => fun _ => False
          | S d' => fun f' =>
                     match Nat.eq_dec (⟦f⟧ d') i with
                     | left x => True
                     | right x => in_range (shrink_index_map_domain f') i
                     end
          end f.

        Global Instance in_range_dec {d r:nat} (f: index_map d r) (i:nat) : Decision (in_range f i).
        Admitted.

      End InRange.

      Section Jections.


        Definition index_map_injective
                   {d r: nat}
                   (f: index_map d r)
          :=
            forall (x y:nat) (xc: x<d) (yc: y<d),
              ⟦ f ⟧ x ≡ ⟦ f ⟧ y → x ≡ y.

      End Jections.

      Section Inversions.
        Record inverse_index_map {d r: nat} (f: index_map d r)
          :=
            InverseIndexMap {
                inverse_index_f : nat -> nat;
                inverse_index_f_spec: forall x, in_range f x -> ((inverse_index_f x) < d)
              }.

        Fixpoint gen_inverse_index_f {d r: nat} (f: index_map d r)
                 (i: nat): nat :=
          let dummy := O in
          match d return (index_map d r) -> nat with
          | O => fun _ => dummy
          | S d' => fun f' =>
                     match Nat.eq_dec (⟦f⟧ d') i with
                     | left x => d'
                     | right x => gen_inverse_index_f (shrink_index_map_domain f') i
                     end
          end f.

        Lemma gen_inverse_index_f_spec {d r: nat} (f: index_map d r):
          forall (i: nat), in_range f i -> (gen_inverse_index_f f i) < d.
        Admitted.

        Definition build_inverse_index_map
                   {d r: nat}
                   (f: index_map d r)
          : inverse_index_map f
          := let f' := gen_inverse_index_f f in
             @InverseIndexMap d r f f' (gen_inverse_index_f_spec f).


      End Inversions.


      Record index_map_family (d r n : nat) :=
        IndexMapFamily { family_f : forall k, k<n -> index_map d r }.

      Notation "⦃ f ⦄" := (@family_f _ _ _ f).


      Section IndexFamilies.

        Definition index_map_family_injective
                   {n d r: nat}
                   (f: index_map_family d r n)
          :=
            forall (i j: nat) (ic: i<n) (jc: j<n) (x y:nat) (xc: x<d) (yc: y<d),
              ⟦ ⦃f⦄ i ic ⟧ x ≡ ⟦ ⦃f⦄ j jc ⟧ y → (x ≡ y) /\ (i ≡ j).

        Lemma index_map_family_member_injective
              {d r n: nat}
              {f: index_map_family d r n}:
          index_map_family_injective f -> forall j (jc:j<n), index_map_injective (⦃f⦄ j jc).
        Admitted.

      End IndexFamilies.


      Section Primitive_Functions.

        Program Definition h_index_map
                {domain range: nat}
                (b s: nat)
                {range_bound: forall x, x<domain -> (b+x*s) < range}
        : index_map domain range
          :=
            IndexMap domain range (fun i => b + i*s) _.

        Lemma h_index_map_is_injective
              {domain range: nat}
              (b s: nat)
              {range_bound: forall x, x<domain -> (b+x*s) < range}
              {snzord0: s ≢ 0 \/ domain < 2} (* without this it is not injective! *)
          :
            index_map_injective  (@h_index_map domain range b s range_bound).
        Admitted.

      End Primitive_Functions.

      Section IndexMapSets.

        Definition index_map_range_set
                   {d r: nat}
                   (f: index_map d r): FinNatSet r :=
          fun x => in_range f (proj1_sig x).

      End IndexMapSets.


    End IndexFunctions.

  End Spiral.

End Spiral_DOT_IndexFunctions.

Module Spiral_DOT_SigmaHCOL.
  Module Spiral.
    Module SigmaHCOL.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_FinNatSet.
      Import Spiral_DOT_IndexFunctions.
      Import Spiral_DOT_IndexFunctions.Spiral.
      Import Spiral_DOT_FinNatSet.Spiral.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.Rtheta.
      Import Spiral_DOT_SVector.Spiral.SVector.
      Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
      Import Spiral_DOT_HCOL.Spiral.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
      Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.
      Import Spiral_DOT_WriterMonadNoT.Spiral.WriterMonadNoT.
      Import Coq.Logic.FunctionalExtensionality.
      Import Coq.Arith.Arith.
      Import Coq.Bool.Bool.
      Import Coq.Bool.BoolEq.
      Import Coq.Strings.String.
      Import Coq.Arith.Peano_dec.
      Import Coq.Logic.Decidable.
      Import Coq.micromega.Psatz.
      Import Omega.


      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.
      Import MathClasses.theory.rings.
      Import MathClasses.implementations.peano_naturals.
      Import MathClasses.orders.orders.
      Import MathClasses.orders.semirings.
      Import MathClasses.theory.setoids.

      (* Ext Lib *)
      Import ExtLib.Structures.Monad.
      Import ExtLib.Structures.Monoid.

      Import Monoid.

      (*  CoLoR *)

      Import VectorNotations.
      Open Scope vector_scope.

      Global Open Scope nat_scope.

      (* Returns an element of the vector 'x' which is result of mapping of
given natrual number by index mapping function f_spec. *)
      Definition VnthIndexMapped
                 {i o:nat}
                 {A: Type}
                 (x: vector A i)
                 (f: index_map o i)
                 (n:nat) (np: n<o)
        : A
        := Vnth x (« f » n np).


      Section SigmaHCOL_Operators.

        Section FlagsMonoidGenericOperators.

          Variable fm:Monoid RthetaFlags.

          Record SHOperator
                 {i o: nat}
            : Type
            := mkSHOperator {
                   op: svector fm i -> svector fm o ;
                   op_proper: Proper ((=) ==> (=)) op;
                   in_index_set: FinNatSet i ;
                   out_index_set: FinNatSet o;
                 }.


          (* Two vectors (=) at indices at given set *)
          Definition vec_equiv_at_set
                     {n:nat}
                     (x y: svector fm n)
                     (s: FinNatSet n)
            :=
              (forall j (jc:j<n),
                  s(mkFinNat jc) -> Vnth x jc = Vnth y jc).





          (* Equivalence of two SHOperators is defined via functional extensionality *)
          Global Instance SHOperator_equiv
                 {i o: nat}:
            Equiv (@SHOperator i o) :=
            fun a b => op a = op b.

          Definition op_Vforall_P
                     {i o: nat}
                     (P: Rtheta' fm -> Prop)
                     (f: @SHOperator i o)
            :=
              forall x, Vforall P ((op f) x).

          Record SHOperatorFamily
                 {i o n: nat}
            : Type
            := mkSHOperatorFamily {
                   family_member: (forall j (jc:j<n), @SHOperator i o)
                 }.

          (* Accessors, mapping SHOperator family to family of underlying "raw" functions *)
          Definition get_family_op
                     {i o n}
                     (op_family: @SHOperatorFamily i o n):
            forall j (jc:j<n), svector fm i -> svector fm o
            := fun j (jc:j<n) => op (family_member op_family j jc).

          Definition get_family_proper
                     {i o n}
                     (op_family: @SHOperatorFamily i o n):
            forall j (jc:j<n), Proper ((=) ==> (=)) (get_family_op op_family j jc)
            := fun j (jc:j<n) => op_proper (family_member op_family j jc).

          Definition shrink_op_family
                     {i o n}
                     (op_family: @SHOperatorFamily i o (S n)): @SHOperatorFamily i o n :=
            match op_family with
            | mkSHOperatorFamily _ _ _ m =>
              mkSHOperatorFamily i o n
                                 (fun (j:nat) (jc:j<n) => m j (@le_S (S j) n jc))
            end.

          Fixpoint family_in_index_set
                   {i o n}
                   (op_family: @SHOperatorFamily i o n): FinNatSet i
            :=
              match n as y return (y ≡ n -> @SHOperatorFamily i o y -> FinNatSet i) with
              | O => fun _ _ => (Empty_set _)
              | S j => fun E f => Union _
                                    (in_index_set (family_member op_family j (S_j_lt_n E)))
                                    (family_in_index_set (shrink_op_family f))
              end (eq_refl n) op_family.

          Fixpoint family_out_index_set
                   {i o n}
                   (op_family: @SHOperatorFamily i o n): FinNatSet o
            :=
              match n as y return (y ≡ n -> @SHOperatorFamily i o y -> FinNatSet o) with
              | O => fun _ _ => (Empty_set _)
              | S j => fun E f => Union _
                                    (out_index_set (family_member op_family j (S_j_lt_n E)))
                                    (family_out_index_set (shrink_op_family f))
              end (eq_refl n) op_family.






          Global Instance SHOperator_equiv_Reflexive
                 {i o: nat}:
            Reflexive (@SHOperator_equiv i o).
          Admitted.

          Global Instance SHOperator_equiv_Symmetric
                 {i o: nat}:
            Symmetric (@SHOperator_equiv i o).
          Admitted.

          Global Instance SHOperator_equiv_Transitive
                 {i o: nat}:
            Transitive (@SHOperator_equiv i o).
          Admitted.

          Global Instance SHOperator_equiv_Equivalence
                 {i o: nat}:
            Equivalence (@SHOperator_equiv i o).
          Admitted.

          Global Instance SHOperatorFamily_equiv
                 {i o n: nat}:
            Equiv (@SHOperatorFamily i o n) :=
            fun a b => forall j (jc:j<n), family_member a j jc = family_member b j jc.

          Global Instance SHOperatorFamily_equiv_Reflexive
                 {i o n: nat}:
            Reflexive (@SHOperatorFamily_equiv i o n).
          Admitted.

          Global Instance SHOperatorFamily_equiv_Symmetric
                 {i o n: nat}:
            Symmetric (@SHOperatorFamily_equiv i o n).
          Admitted.

          Global Instance SHOperatorFamily_equiv_Transitive
                 {i o n: nat}:
            Transitive (@SHOperatorFamily_equiv i o n).
          Admitted.

          Global Instance SHOperatorFamily_equiv_Equivalence
                 {i o n: nat}:
            Equivalence (@SHOperatorFamily_equiv i o n).
          Admitted.


          Global Instance SHOperator_op_proper {i o} :
            Proper ((=) ==> (=) ==> (=)) (@op i o).
          Admitted.

          Global Instance get_family_op_proper {i o n} :
            Proper ((=) ==>
                        (forall_relation (λ j : nat, pointwise_relation (j < n) (=))))
                   (@get_family_op i o n).
          Admitted.

          Global Instance SHOperator_op_arg_proper {i o} (a:@SHOperator i o):
            Proper ((=) ==> (=)) (op a).
          Admitted.

          Global Instance mkSHOperatorFamily_proper
                 {i o n: nat}:
            Proper (forall_relation (λ i : nat, pointwise_relation (i < n) equiv) ==> equiv)
                   (mkSHOperatorFamily i o n).
          Admitted.

          Global Instance op_Vforall_P_arg_proper
                 {i o: nat}
                 (P: Rtheta' fm -> Prop)
                 (P_mor: Proper ((=) ==> iff) P):
            Proper ((=) ==> iff) (@op_Vforall_P i o P).
          Admitted.

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
          Admitted.

          Definition liftM_HOperator
                     {i o}
                     (op: avector i -> avector o)
                     `{HOP: HOperator i o op}
            := mkSHOperator i o (liftM_HOperator_impl op) (@liftM_HOperator_impl_proper i o op HOP)
                            (Full_set _) (Full_set _).

          (** Apply family of functions to same fector and return matrix of results *)
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
          Admitted.

          (** Apply family of SHOperator's to same fector and return matrix of results *)
          Definition Apply_Family
                     {i o n}
                     (op_family: @SHOperatorFamily i o n)
            :=
              Apply_Family' (get_family_op op_family).

          Global Instance Apply_Family_proper
                 {i o n}:
            Proper ((=) ==> (=) ==> (=)) (@Apply_Family i o n).
          Admitted.

          (* Do we need this in presence of Apply_Family_proper ? *)
          Global Instance Apply_Family_arg_proper
                 {i o n}
                 (op_family: @SHOperatorFamily i o n):
            Proper ((=) ==> (=)) (@Apply_Family i o n op_family).
          Admitted.

          Definition Gather_impl
                     {i o: nat}
                     (f: index_map o i)
                     (x: svector fm i):
            svector fm o
            := Vbuild (VnthIndexMapped x f).

          Global Instance Gather_impl_proper
                 {i o: nat}
                 (f: index_map o i):
            Proper ((=) ==> (=)) (Gather_impl f).
          Admitted.

          Definition Gather
                     {i o: nat}
                     (f: index_map o i)
            := mkSHOperator i o (Gather_impl f) _
                            (index_map_range_set f) (* Read pattern is governed by index function *)
                            (Full_set _) (* Gater always writes everywhere *).

          Definition GathH
                     {i o}
                     (base stride: nat)
                     {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
            :=
              Gather (h_index_map base stride
                                  (range_bound:=domain_bound) (* since we swap domain and range, domain bound becomes range boud *)
                     ).

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
            Proper ((=) ==> (=) ==> (=)) (Scatter_impl f (f_inj:=f_inj)).
          Admitted.

          Definition Scatter
                     {i o: nat}
                     (f: index_map i o)
                     {f_inj: index_map_injective f}
                     (idv: CarrierA)
            := mkSHOperator i o (Scatter_impl f (f_inj:=f_inj) idv) _
                            (Full_set _) (* Scatter always reads evertying *)
                            (index_map_range_set f) (* Write pattern is governed by index function *).

          Definition ScatH
                     {i o}
                     (base stride: nat)
                     {range_bound: ∀ x : nat, x < i → base + x * stride < o}
                     {snzord0: stride ≢ 0 \/ i < 2}
            :=
              Scatter (h_index_map base stride (range_bound:=range_bound))
                      (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)).

          Definition SHCompose
                     {i1 o2 o3}
                     (op1: @SHOperator o2 o3)
                     (op2: @SHOperator i1 o2)
            : @SHOperator i1 o3 := mkSHOperator i1 o3 (compose (op op1) (op op2)) _
                                                (in_index_set op2)
                                                (out_index_set op1).

          Local Notation "g ⊚ f" := (@SHCompose _ _ _ g f) (at level 40, left associativity) : type_scope.


          Global Instance SHCompose_proper
                 {i1 o2 o3}
            :
              Proper ((=) ==> (=) ==> (=)) (@SHCompose i1 o2 o3).
          Admitted.


          Definition SHFamilyFamilyCompose
                     {i1 o2 o3 n}
                     (f: @SHOperatorFamily o2 o3 n)
                     (g: @SHOperatorFamily i1 o2 n)
            : @SHOperatorFamily i1 o3 n
            :=
              mkSHOperatorFamily _ _ _
                                 (fun (j : nat) (jc : j < n) =>
                                    family_member f j jc  ⊚ family_member g j jc).

          Global Instance SHFamilyFamilyCompose_proper
                 {i1 o2 o3 n: nat}
            :
              Proper ((=) ==> (=) ==> (=)) (@SHFamilyFamilyCompose i1 o2 o3 n).
          Admitted.

          (* Family/operator composition *)
          Definition  SHOperatorFamilyCompose
                      {i1 o2 o3 n}
                      (f: @SHOperator o2 o3)
                      (g: @SHOperatorFamily i1 o2 n)
            : @SHOperatorFamily i1 o3 n
            :=
              mkSHOperatorFamily _ _ _
                                 (fun (j : nat) (jc : j < n) =>
                                    f  ⊚ family_member g j jc).

          Global Instance SHOperatorFamilyCompose_proper
                 {i1 o2 o3 n: nat}
            :
              Proper ((=) ==> (=) ==> (=)) (@SHOperatorFamilyCompose i1 o2 o3 n).
          Admitted.

          Definition  SHFamilyOperatorCompose
                      {i1 o2 o3 n}
                      (f: @SHOperatorFamily o2 o3 n)
                      (g: @SHOperator i1 o2)
            : @SHOperatorFamily i1 o3 n
            :=
              mkSHOperatorFamily _ _ _
                                 (fun (j : nat) (jc : j < n) =>
                                    family_member f j jc  ⊚ g).

          Global Instance SHFamilyOperatorCompose_proper
                 {i1 o2 o3 n: nat}
            :
              Proper ((=) ==> (=) ==> (=)) (@SHFamilyOperatorCompose i1 o2 o3 n).
          Admitted.


          (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
          Definition SHPointwise'
                     {n: nat}
                     (f: { i | i<n} -> CarrierA -> CarrierA)
                     `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                     (x: svector fm n): svector fm n
            := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

          Global Instance SHPointwise'_proper
                 {n: nat}
                 (f: { i | i<n} -> CarrierA -> CarrierA)
                 `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
            Proper ((=) ==> (=)) (SHPointwise' f).
          Admitted.

          Definition SHPointwise
                     {n: nat}
                     (f: { i | i<n} -> CarrierA -> CarrierA)
                     `{pF: !Proper ((=) ==> (=) ==> (=)) f}
            := mkSHOperator n n (SHPointwise' f) _ (Full_set _) (Full_set _).

          Definition SHBinOp'
                     {o}
                     (f: nat -> CarrierA -> CarrierA -> CarrierA)
                     `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
                     (v:svector fm (o+o)): svector fm o
            :=  match (vector2pair o v) with
                | (a,b) => Vbuild (fun i ip => liftM2 (f i) (Vnth a ip) (Vnth b ip))
                end.

          Global Instance SHBinOp'_proper
                 {o}
                 (f: nat -> CarrierA -> CarrierA -> CarrierA)
                 `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
            Proper ((=) ==> (=)) (SHBinOp' (o:=o) f).
          Admitted.

        End FlagsMonoidGenericOperators.

        Definition SHBinOp
                   {o}
                   (f: nat -> CarrierA -> CarrierA -> CarrierA)
                   `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
          := mkSHOperator Monoid_RthetaSafeFlags
                          (o+o) o (SHBinOp' Monoid_RthetaSafeFlags f) _ (Full_set _) (Full_set _).

        (** Matrix-union. This is a common implementations for IUnion and IReduction *)
        Definition Diamond'
                   {i o n}
                   {fm}
                   (dot: CarrierA -> CarrierA -> CarrierA)
                   (initial: CarrierA)
                   (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
                   (v:svector fm i): svector fm o
          :=
            MUnion' fm dot initial (@Apply_Family' fm i o n op_family_f v).


        Global Instance Diamond'_proper
               {i o n} {fm}
          : Proper (
                (=) ==> (=) ==>
                    (@forall_relation nat
                                      (fun k : nat =>  forall _ : k<n, (svector fm i -> svector fm o))
                                      (fun k : nat =>  @pointwise_relation (k < n)
                                                                      (svector fm i -> svector fm o) (=)))
                    ==> (=) ==> (=)) (@Diamond' i o n fm).
        Admitted.

        (* One might think we do not need this in presence of Diamond'_proper. However even this partially applied morphism could be easily proven from Diamond'_proper sometimes helps class resolutuion which does not always find Diamond'_proper *)
        Global Instance Diamond'_arg_proper
               {i o n}
               {fm}
               (dot: CarrierA -> CarrierA -> CarrierA)
               `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
               (initial: CarrierA)
               (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
               (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
          : Proper ((=) ==> (=)) (Diamond' dot initial op_family_f).
        Admitted.

        Definition IUnion
                   {i o n}
                   (* Functional parameters *)
                   (dot: CarrierA -> CarrierA -> CarrierA)
                   `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
                   (initial: CarrierA)
                   (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
          : @SHOperator Monoid_RthetaFlags i o
          :=
            mkSHOperator Monoid_RthetaFlags i o
                         (Diamond' dot initial (get_family_op Monoid_RthetaFlags op_family))
                         _
                         (family_in_index_set _ op_family)
                         (family_out_index_set _ op_family)
        . (* requires get_family_op_proper OR SHOperator_op_arg_proper *)

        Definition IReduction
                   {i o n}
                   (dot: CarrierA -> CarrierA -> CarrierA)
                   `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
                   (initial: CarrierA)
                   (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
          : @SHOperator Monoid_RthetaSafeFlags i o:=
          mkSHOperator Monoid_RthetaSafeFlags i o
                       (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family))
                       _
                       (family_in_index_set _ op_family)
                       (family_out_index_set _ op_family) (* All scatters must be the same but we do not enforce it here. However if they are the same, the union will equal to any of them, so it is legit to use union here *)
        .

        Global Instance IReduction_proper
               {i o n: nat}
               (dot: CarrierA -> CarrierA -> CarrierA)
               `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
          :
            Proper ((=) ==> (=) ==> (=)) (@IReduction i o n dot pdot).
        Admitted.


      End SigmaHCOL_Operators.

      Section OperatorProperies.

        Variable fm:Monoid RthetaFlags.
        Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

        Local Notation "g ⊚ f" := (@SHCompose _ _ _ _ g f) (at level 40, left associativity) : type_scope.
      End OperatorProperies.








    End SigmaHCOL.

  End Spiral.

End Spiral_DOT_SigmaHCOL.

Module Spiral_DOT_TSigmaHCOL.
  Module Spiral.
    Module TSigmaHCOL.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_FinNatSet.
      Import Spiral_DOT_IndexFunctions.
      Import Spiral_DOT_SigmaHCOL.
      Import Spiral_DOT_SigmaHCOL.Spiral.
      Import Spiral_DOT_IndexFunctions.Spiral.
      Import Spiral_DOT_FinNatSet.Spiral.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.Rtheta.
      Import Spiral_DOT_SVector.Spiral.SVector.
      Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
      Import Spiral_DOT_SigmaHCOL.Spiral.SigmaHCOL. (* Presently for SHOperator only. Consider moving it elsewhere *)
      Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.
      Import Coq.Arith.Arith.
      Import Coq.Program.Program.
      Import Coq.Classes.Morphisms.
      Import Coq.Classes.RelationClasses.
      Import Coq.Relations.Relations.
      Import Coq.Logic.FunctionalExtensionality.

      Import MathClasses.interfaces.abstract_algebra.
      Import MathClasses.orders.minmax MathClasses.interfaces.orders.
      Import MathClasses.theory.rings.
      Import MathClasses.theory.setoids.


      Import ExtLib.Structures.Monoid.
      Import Monoid.

      Section RthetaSafetyCast.

        Definition SafeCast'
                   {o i}
                   (f: rsvector i -> rsvector o):
          rvector i -> rvector o
          := (rsvector2rvector o) ∘ f ∘ (rvector2rsvector i).

        Global Instance SafeCast'_proper (i o : nat):
          Proper (equiv ==> equiv ==> equiv) (@SafeCast' i o).
        Admitted.

        Definition SafeCast {i o}
                   (f: @SHOperator Monoid_RthetaSafeFlags i o)
          : @SHOperator Monoid_RthetaFlags i o.
        Proof.
          refine (mkSHOperator Monoid_RthetaFlags i o
                               (SafeCast' (op Monoid_RthetaSafeFlags f))
                               _  _ _).
          -
            apply f.
          -
            apply f.
        Defined.

        Global Instance SafeCast_proper (i o:nat):
          Proper (equiv ==> equiv) (@SafeCast i o).
        Admitted.

        Definition SafeFamilyCast {i o n}
                   (f: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
          : @SHOperatorFamily Monoid_RthetaFlags i o n
          :=
            mkSHOperatorFamily _ _ _ _
                               (fun (j : nat) (jc : j < n) =>
                                  SafeCast (family_member Monoid_RthetaSafeFlags f j jc)).

        Global Instance SafeFamilyCast_proper (i o n:nat):
          Proper (equiv ==> equiv) (@SafeFamilyCast i o n).
        Admitted.

        Definition UnSafeCast'
                   {o i}
                   (f: rvector i -> rvector o):
          rsvector i -> rsvector o
          := (rvector2rsvector o) ∘ f ∘ (rsvector2rvector i).


        Global Instance UnSafeCast'_proper (i o : nat):
          Proper (equiv ==> equiv ==> equiv) (@UnSafeCast' i o).
        Admitted.

        Definition UnSafeCast {i o}
                   (f: @SHOperator Monoid_RthetaFlags i o)
          : @SHOperator Monoid_RthetaSafeFlags i o.
        Proof.
          refine (mkSHOperator Monoid_RthetaSafeFlags i o
                               (UnSafeCast' (op Monoid_RthetaFlags f))
                               _  _ _).
          -
            apply f.
          -
            apply f.
        Defined.

        Global Instance UnSafeCast_proper (i o:nat):
          Proper (equiv ==> equiv) (@UnSafeCast i o).
        Admitted.


        Definition UnSafeFamilyCast {i o n}
                   (f: @SHOperatorFamily Monoid_RthetaFlags i o n)
          : @SHOperatorFamily Monoid_RthetaSafeFlags i o n
          :=
            mkSHOperatorFamily _ _ _ _
                               (fun (j : nat) (jc : j < n) =>
                                  UnSafeCast (family_member Monoid_RthetaFlags f j jc)).


        Global Instance UnSafeFamilyCast_proper (i o n:nat):
          Proper (equiv ==> equiv) (@UnSafeFamilyCast i o n).
        Admitted.

      End RthetaSafetyCast.


      (* For now we are not define special type for TSigmahcolOperators, like we did for SHOperator. Currently we have only 2 of these: SHCompose and HTSumunion. We will generalize in future, if needed *)
      Section TSigmaHCOLOperators.

        Variable fm:Monoid RthetaFlags.

        (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.
         *)
        Definition HTSUMUnion' {i o}
                   (dot: CarrierA -> CarrierA -> CarrierA)
                   (op1: svector fm i -> svector fm o)
                   (op2: svector fm i -> svector fm o):
          svector fm i -> svector fm o
          := fun x => Vec2Union fm dot (op1 x) (op2 x).


        (* TODO: make dot part of morphism *)
        Global Instance HTSUMUnion'_proper {i o}
               (dot: CarrierA -> CarrierA -> CarrierA)
               `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
          : Proper ((=) ==> (=) ==> (=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot).
        Admitted.

        Global Instance HTSUMUnion'_arg_proper {i o}
               (op1: svector fm i -> svector fm o)
               `{op1_proper: !Proper ((=) ==> (=)) op1}
               (op2: svector fm i -> svector fm o)
               `{op2_proper: !Proper ((=) ==> (=)) op2}
               (dot: CarrierA -> CarrierA -> CarrierA)
               `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
          : Proper ((=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot op1 op2).
        Admitted.

        Definition HTSUMUnion {i o}
                   (dot: CarrierA -> CarrierA -> CarrierA)
                   `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
                   (op1 op2: @SHOperator fm i o)
          : @SHOperator fm i o
          :=
            mkSHOperator fm i o (HTSUMUnion' dot (op fm op1) (op fm op2))
                         (@HTSUMUnion'_arg_proper i o
                                                  (op fm op1) (op_proper fm op1)
                                                  (op fm op2) (op_proper fm op2)
                                                  dot dot_mor)
                         (Ensembles.Union _ (in_index_set _ op1) (in_index_set _ op2))
                         (Ensembles.Union _ (out_index_set _ op1) (out_index_set _ op2)).

        Global Instance HTSUMUnion_proper
               {i o}
               (dot: CarrierA -> CarrierA -> CarrierA)
               `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
          : Proper ((=) ==> (=) ==> (=))
                   (@HTSUMUnion i o dot dot_mor).
        Admitted.

      End TSigmaHCOLOperators.

    End TSigmaHCOL.

  End Spiral.

End Spiral_DOT_TSigmaHCOL.


Module Spiral_DOT_MonoidalRestriction.
  Module Spiral.
    Module MonoidalRestriction.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_FinNatSet.
      Import Spiral_DOT_IndexFunctions.
      Import Spiral_DOT_SigmaHCOL.
      Import Spiral_DOT_TSigmaHCOL.
      Import Spiral_DOT_TSigmaHCOL.Spiral.
      Import Spiral_DOT_SigmaHCOL.Spiral.
      Import Spiral_DOT_IndexFunctions.Spiral.
      Import Spiral_DOT_FinNatSet.Spiral.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import MathClasses.interfaces.abstract_algebra.


      Section MonoidalRestriction.
        Context A {Ae : Equiv A}.

        (* Predicate on type [A] *)
        Class SgPred A := sg_P: A → Prop.

        (* Restriction of monoid operator and unit values *)
        Class MonRestriction {Aop : SgOp A} {Aunit : MonUnit A} {Apred: SgPred A}: Prop :=
          { rmonoid_unit_P: sg_P mon_unit
            ; rmonoid_plus_closed: forall a b, sg_P a -> sg_P b -> sg_P (a & b)
          }.

        Class RMonoid {Aop : SgOp A} {Aunit : MonUnit A} {Apred: SgPred A} :=
          {  sg_setoid :> Setoid A
             ; mon_restriction :> MonRestriction
             ; rsg_op_proper :> Proper ((=) ==> (=) ==> (=)) (&)

             ; rmonoid_ass: forall x y z,
                 sg_P x -> sg_P y -> sg_P z -> x & (y & z) = (x & y) & z
             ; rmonoid_left_id : forall y, sg_P y -> mon_unit & y = y
             ; rmonoid_right_id : forall x, sg_P x -> x & mon_unit = x
          }.

        Class CommutativeRMonoid {Aop Aunit Ares} : Prop :=
          {
            comrmonoid_rmon :> @RMonoid Aop Aunit Ares
            ; rcommutativity: forall x y, sg_P x -> sg_P y -> x & y = y & x
          }.

      End MonoidalRestriction.

      Arguments rsg_op_proper {A Ae Aop Aunit Apred RMonoid}.


    End MonoidalRestriction.

  End Spiral.

End Spiral_DOT_MonoidalRestriction.


Module Spiral_DOT_SigmaHCOLRewriting.
  Module Spiral.
    Module SigmaHCOLRewriting.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_FinNatSet.
      Import Spiral_DOT_IndexFunctions.
      Import Spiral_DOT_SigmaHCOL.
      Import Spiral_DOT_TSigmaHCOL.
      Import Spiral_DOT_MonoidalRestriction.
      Import Spiral_DOT_MonoidalRestriction.Spiral.
      Import Spiral_DOT_TSigmaHCOL.Spiral.
      Import Spiral_DOT_SigmaHCOL.Spiral.
      Import Spiral_DOT_IndexFunctions.Spiral.
      Import Spiral_DOT_FinNatSet.Spiral.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.

      Global Generalizable All Variables.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.Rtheta.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_SVector.Spiral.SVector.
      Import Spiral_DOT_HCOL.Spiral.HCOL.
      Import Spiral_DOT_THCOL.Spiral.THCOL.
      Import Spiral_DOT_SigmaHCOL.Spiral.SigmaHCOL.
      Import Spiral_DOT_TSigmaHCOL.Spiral.TSigmaHCOL.
      Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
      Import Spiral_DOT_MonoidalRestriction.Spiral.MonoidalRestriction.
      Import Coq.Arith.Arith.
      Import Coq.Arith.Compare_dec.
      Import Coq.Arith.Peano_dec.
      Import Coq.Logic.Eqdep_dec.
      Import Coq.Logic.ProofIrrelevance.
      Import Coq.Program.Program.
      Import Coq.Logic.FunctionalExtensionality.
      Import Coq.micromega.Psatz.
      Import Omega.

      (* CoRN Math-classes *)
      Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
      Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
      Import MathClasses.theory.rings MathClasses.theory.abs.
      Import MathClasses.theory.setoids.

      Import ExtLib.Structures.Monoid.
      Import Monoid.

      Import VectorNotations.

      Local Open Scope vector_scope.
      Local Open Scope nat_scope.

      Section SigmaHCOLHelperLemmas.

        Variable fm:Monoid RthetaFlags.
        Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

        Fact ScatH_stride1_constr:
        forall {a b:nat}, 1 ≢ 0 ∨ a < b.
        Admitted.

        Fact h_bound_first_half (o1 o2:nat):
          ∀ x : nat, x < o1 → 0 + x * 1 < o1 + o2.
        Admitted.

        Fact h_bound_second_half (o1 o2:nat):
          ∀ x : nat, x < o2 → o1 + x * 1 < o1 + o2.
        Admitted.

        Fact ScatH_1_to_n_range_bound base o stride:
          base < o ->
          ∀ x : nat, x < 1 → base + x * stride < o.
        Admitted.

        Fact GathH_jn_domain_bound i n:
          i < n ->
          ∀ x : nat, x < 2 → i + x * n < (n+n).
        Admitted.

      End SigmaHCOLHelperLemmas.



      Section SigmaHCOLExpansionRules.
        Section Value_Correctness.

          Lemma h_j_1_family_injective {n}:
            index_map_family_injective
              (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound _ _ j n 1 jc)))).
          Admitted.

        End Value_Correctness.


      End SigmaHCOLExpansionRules.

      Section SigmaHCOLRewritingRules.
        Section Value_Correctness.

          Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.


          Section VecMap2CommutativeRMonoid.

            Variable n:nat.
            Variable A: Type.
            Variable Ae: Equiv A.
            Variable As: @Setoid A Ae.
            Variable z: MonUnit A.
            Variable f: SgOp A.
            Variable P: SgPred A.

            Global Instance VecMonRestrictionMap2
                   {f_mon: @MonRestriction A f z P}:
              @MonRestriction
                (vector A n)
                (Vmap2 f (n:=n))
                (Vconst z n)
                (Vforall P (n:=n)).
            Admitted.

            Global Instance VecRMonoidMap2
                   {f_mon: @RMonoid A Ae f z P}
              :
                @RMonoid
                  (vector A n)
                  (=)
                  (Vmap2 f (n:=n))
                  (Vconst z n)
                  (Vforall P (n:=n)).
            Admitted.

            Global Instance VecCommutativeRMonoidMap2
                   {f_mon: @CommutativeRMonoid A Ae f z P}
              :
                @CommutativeRMonoid
                  (vector A n)
                  (=)
                  (Vmap2 f (n:=n))
                  (Vconst z n)
                  (Vforall P (n:=n)).
            Admitted.

          End VecMap2CommutativeRMonoid.


          Global Instance max_Assoc:
            @Associative CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec).
          Admitted.

          Global Instance max_Comm:
            @Commutative CarrierA CarrierAe CarrierA (@max CarrierA CarrierAle CarrierAledec).
          Admitted.

          Section NN.
            (* Non-negative CarrierA subtype *)

            Global Instance NN:
              SgPred CarrierA := CarrierAle CarrierAz.

            Global Instance RMonoid_max_NN:
              @RMonoid CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
            Admitted.

            Global Instance CommutativeRMonoid_max_NN:
              @CommutativeRMonoid CarrierA CarrierAe (@minmax.max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
            Admitted.

          End NN.

          Lemma rewrite_Reduction_ScatHUnion_max_zero
                (n m: nat)
                (fm: Monoid.Monoid RthetaFlags)
                (F: @SHOperator fm m 1)
                (f: index_map 1 (S n))
                (f_inj: index_map_injective f)
                (FP: op_Vforall_P fm Is_NonNegative F)

            :
              SHCompose fm
                        (SHCompose fm
                                   (liftM_HOperator fm (HReduction minmax.max zero))
                                   (Scatter fm f zero (f_inj:=f_inj)))
                        F
              =
              F.
          Admitted.

          Lemma rewrite_Reduction_ScatHUnion_max_zero'
                (n m: nat)
                (fm: Monoid.Monoid RthetaFlags)
                (F: @SHOperator fm m 1)
                (f: index_map 1 (S n))
                (f_inj: index_map_injective f)
                (* FP: op_Vforall_P fm Is_NonNegative F *)

            :
              SHCompose fm
                        (SHCompose fm
                                   (liftM_HOperator fm (HReduction minmax.max zero))
                                   (Scatter fm f zero (f_inj:=f_inj)))
                        F
              =
              F.
          Admitted.



        End Value_Correctness.

      End SigmaHCOLRewritingRules.


    End SigmaHCOLRewriting.
  End Spiral.
End Spiral_DOT_SigmaHCOLRewriting.

Module Spiral_DOT_DynWin.
  Module Spiral.
    Module DynWin.
      Import Spiral_DOT_Spiral.
      Import Spiral_DOT_VecUtil.
      Import Spiral_DOT_VecSetoid.
      Import Spiral_DOT_CarrierType.
      Import Spiral_DOT_WriterMonadNoT.
      Import Spiral_DOT_Rtheta.
      Import Spiral_DOT_SVector.
      Import Spiral_DOT_HCOLImpl.
      Import Spiral_DOT_HCOL.
      Import Spiral_DOT_THCOLImpl.
      Import Spiral_DOT_THCOL.
      Import Spiral_DOT_FinNatSet.
      Import Spiral_DOT_IndexFunctions.
      Import Spiral_DOT_SigmaHCOL.
      Import Spiral_DOT_TSigmaHCOL.
      Import Spiral_DOT_MonoidalRestriction.
      Import Spiral_DOT_SigmaHCOLRewriting.
      Import Spiral_DOT_SigmaHCOLRewriting.Spiral.
      Import Spiral_DOT_MonoidalRestriction.Spiral.
      Import Spiral_DOT_TSigmaHCOL.Spiral.
      Import Spiral_DOT_SigmaHCOL.Spiral.
      Import Spiral_DOT_IndexFunctions.Spiral.
      Import Spiral_DOT_FinNatSet.Spiral.
      Import Spiral_DOT_THCOL.Spiral.
      Import Spiral_DOT_THCOLImpl.Spiral.
      Import Spiral_DOT_HCOL.Spiral.
      Import Spiral_DOT_HCOLImpl.Spiral.
      Import Spiral_DOT_SVector.Spiral.
      Import Spiral_DOT_Rtheta.Spiral.
      Import Spiral_DOT_WriterMonadNoT.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.
      Import Spiral_DOT_VecSetoid.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.
      Import Spiral_DOT_Spiral.Spiral.
      Import Spiral_DOT_VecUtil.Spiral.VecUtil.
      Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
      Import Spiral_DOT_SVector.Spiral.SVector.
      Import Spiral_DOT_Spiral.Spiral.Spiral.
      Import Spiral_DOT_CarrierType.Spiral.CarrierType.
      Import Spiral_DOT_HCOL.Spiral.HCOL.
      Import Spiral_DOT_HCOLImpl.Spiral.HCOLImpl.
      Import Spiral_DOT_THCOL.Spiral.THCOL.
      Import Spiral_DOT_THCOLImpl.Spiral.THCOLImpl.
      Import Spiral_DOT_Rtheta.Spiral.Rtheta.
      Import Spiral_DOT_SigmaHCOL.Spiral.SigmaHCOL.
      Import Spiral_DOT_TSigmaHCOL.Spiral.TSigmaHCOL.
      Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
      Import Coq.Arith.Arith.
      Import Coq.Arith.Compare_dec.
      Import Coq.Arith.Peano_dec.
      Import Spiral_DOT_SigmaHCOLRewriting.Spiral.SigmaHCOLRewriting.
      Import MathClasses.interfaces.canonical_names.


      Section SigmaHCOL_rewriting.

        Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.


        Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.


        Parameter dynwin_SHCOL1: (avector 3) -> @SHOperator Monoid_RthetaFlags (1+(2+2)) 1.

        Goal forall a : vector CarrierA (S (S (S O))),
            @equiv (@SHOperator Monoid_RthetaFlags (S (S (S (S (S O))))) (S O))
                   (@SHOperator_equiv Monoid_RthetaFlags (S (S (S (S (S O))))) (S O))
                   (@SHCompose Monoid_RthetaFlags (S (S (S (S (S O))))) (S (S O))
                               (S O)
                               (@SafeCast (S (S O)) (S O)
                                          (@SHBinOp (S O) (@IgnoreIndex2 CarrierA Zless)
                                                    (@Reflexive_partial_app_morphism
                                                       (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                       (forall (_ : nat) (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                       (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                                    (@equiv CarrierA CarrierAe)
                                                                    (@equiv (forall _ : CarrierA, CarrierA)
                                                                            (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                                                       (@respectful nat (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                                    (@equiv nat peano_naturals.nat_equiv)
                                                                    (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                                                 (@equiv CarrierA CarrierAe)
                                                                                 (@respectful CarrierA CarrierA (@equiv CarrierA CarrierAe)
                                                                                              (@equiv CarrierA CarrierAe)))) (@IgnoreIndex2 CarrierA)
                                                       (@IgnoreIndex2_proper CarrierA CarrierAe) Zless
                                                       (@proper_proper_proxy (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                                             Zless
                                                                             (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                                                          (@equiv CarrierA CarrierAe)
                                                                                          (@equiv (forall _ : CarrierA, CarrierA)
                                                                                                  (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                                                                             Zless_proper))))
                               (@HTSUMUnion Monoid_RthetaFlags (S (S (S (S (S O)))))
                                            (S (S O)) (@plus CarrierA CarrierAplus) CarrierAPlus_proper
                                            (@SHCompose Monoid_RthetaFlags (S (S (S (S (S O)))))
                                                        (S O) (S (S O))
                                                        (@SHCompose Monoid_RthetaFlags (S O) (S (S (S O)))
                                                                    (S (S O))
                                                                    (@SHCompose Monoid_RthetaFlags (S (S (S O)))
                                                                                (S (S (S (S (S (S O)))))) (S (S O))
                                                                                (@SHCompose Monoid_RthetaFlags (S (S (S (S (S (S O))))))
                                                                                            (S (S (S O))) (S (S O))
                                                                                            (@SHCompose Monoid_RthetaFlags (S (S (S O)))
                                                                                                        (S O) (S (S O))
                                                                                                        (@ScatH Monoid_RthetaFlags (S O) (S (S O)) O
                                                                                                                (S O)
                                                                                                                (h_bound_first_half Monoid_RthetaSafeFlags
                                                                                                                                    MonoidLaws_SafeRthetaFlags (S O)
                                                                                                                                    (S O))
                                                                                                                (@ScatH_stride1_constr Monoid_RthetaSafeFlags
                                                                                                                                       MonoidLaws_SafeRthetaFlags (S O)
                                                                                                                                       (S (S O))) (@zero CarrierA CarrierAz))
                                                                                                        (@liftM_HOperator Monoid_RthetaFlags
                                                                                                                          (S (S (S O))) (S O)
                                                                                                                          (@HReduction (S (S (S O))) (@plus CarrierA CarrierAplus)
                                                                                                                                       CarrierAPlus_proper (@zero CarrierA CarrierAz))
                                                                                                                          (@HReduction_HOperator (S (S (S O)))
                                                                                                                                                 (@plus CarrierA CarrierAplus) CarrierAPlus_proper
                                                                                                                                                 (@zero CarrierA CarrierAz))))
                                                                                            (@SafeCast (S (S (S (S (S (S O)))))) (S (S (S O)))
                                                                                                       (@SHBinOp (S (S (S O)))
                                                                                                                 (@IgnoreIndex2 CarrierA (@mult CarrierA CarrierAmult))
                                                                                                                 (@Reflexive_partial_app_morphism
                                                                                                                    (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                                                                                    (forall (_ : nat) (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                                                                                    (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                                                                                                 (@equiv CarrierA CarrierAe)
                                                                                                                                 (@equiv (forall _ : CarrierA, CarrierA)
                                                                                                                                         (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                                                                                                                    (@respectful nat
                                                                                                                                 (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                                                                                                 (@equiv nat peano_naturals.nat_equiv)
                                                                                                                                 (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                                                                                                              (@equiv CarrierA CarrierAe)
                                                                                                                                              (@respectful CarrierA CarrierA
                                                                                                                                                           (@equiv CarrierA CarrierAe)
                                                                                                                                                           (@equiv CarrierA CarrierAe))))
                                                                                                                    (@IgnoreIndex2 CarrierA)
                                                                                                                    (@IgnoreIndex2_proper CarrierA CarrierAe)
                                                                                                                    (@mult CarrierA CarrierAmult)
                                                                                                                    (@proper_proper_proxy
                                                                                                                       (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                                                                                                       (@mult CarrierA CarrierAmult)
                                                                                                                       (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                                                                                                    (@equiv CarrierA CarrierAe)
                                                                                                                                    (@equiv (forall _ : CarrierA, CarrierA)
                                                                                                                                            (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                                                                                                                       (@abstract_algebra.sg_op_proper CarrierA CarrierAe
                                                                                                                                                       CarrierAmult
                                                                                                                                                       (@abstract_algebra.monoid_semigroup CarrierA
                                                                                                                                                                                           CarrierAe CarrierAmult
                                                                                                                                                                                           (@one_is_mon_unit CarrierA CarrierA1)
                                                                                                                                                                                           (@abstract_algebra.commonoid_mon CarrierA
                                                                                                                                                                                                                            CarrierAe CarrierAmult
                                                                                                                                                                                                                            (@one_is_mon_unit CarrierA CarrierA1)
                                                                                                                                                                                                                            (@abstract_algebra.semimult_monoid CarrierA
                                                                                                                                                                                                                                                               CarrierAe CarrierAplus CarrierAmult
                                                                                                                                                                                                                                                               CarrierAz CarrierA1
                                                                                                                                                                                                                                                               (@rings.Ring_Semi CarrierA CarrierAe
                                                                                                                                                                                                                                                                                 CarrierAplus CarrierAmult CarrierAz
                                                                                                                                                                                                                                                                                 CarrierA1 CarrierAneg CarrierAr))))))))))
                                                                                (@liftM_HOperator Monoid_RthetaFlags (S (S (S O)))
                                                                                                  (S (S (S (S (S (S O)))))) (@HPrepend (S (S (S O))) (S (S (S O))) a)
                                                                                                  (@HPrepend_HOperator (S (S (S O))) (S (S (S O))) a)))
                                                                    (@liftM_HOperator Monoid_RthetaFlags (S O) (S (S (S O)))
                                                                                      (@HInduction (S (S (S O))) (@mult CarrierA CarrierAmult)
                                                                                                   (@abstract_algebra.sg_op_proper CarrierA CarrierAe CarrierAmult
                                                                                                                                   (@abstract_algebra.monoid_semigroup CarrierA CarrierAe
                                                                                                                                                                       CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                                                                                                                                                                       (@abstract_algebra.commonoid_mon CarrierA CarrierAe
                                                                                                                                                                                                        CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                                                                                                                                                                                                        (@abstract_algebra.semimult_monoid CarrierA CarrierAe
                                                                                                                                                                                                                                           CarrierAplus CarrierAmult CarrierAz CarrierA1
                                                                                                                                                                                                                                           (@rings.Ring_Semi CarrierA CarrierAe CarrierAplus
                                                                                                                                                                                                                                                             CarrierAmult CarrierAz CarrierA1 CarrierAneg
                                                                                                                                                                                                                                                             CarrierAr))))) (@one CarrierA CarrierA1))
                                                                                      (@HInduction_HOperator (S (S (S O))) (@mult CarrierA CarrierAmult)
                                                                                                             (@abstract_algebra.sg_op_proper CarrierA CarrierAe CarrierAmult
                                                                                                                                             (@abstract_algebra.monoid_semigroup CarrierA CarrierAe
                                                                                                                                                                                 CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                                                                                                                                                                                 (@abstract_algebra.commonoid_mon CarrierA CarrierAe
                                                                                                                                                                                                                  CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                                                                                                                                                                                                                  (@abstract_algebra.semimult_monoid CarrierA CarrierAe
                                                                                                                                                                                                                                                     CarrierAplus CarrierAmult CarrierAz CarrierA1
                                                                                                                                                                                                                                                     (@rings.Ring_Semi CarrierA CarrierAe CarrierAplus
                                                                                                                                                                                                                                                                       CarrierAmult CarrierAz CarrierA1 CarrierAneg
                                                                                                                                                                                                                                                                       CarrierAr))))) (@one CarrierA CarrierA1))))
                                                        (@GathH Monoid_RthetaFlags (S (S (S (S (S O)))))
                                                                (S O) O (S O)
                                                                (h_bound_first_half Monoid_RthetaSafeFlags MonoidLaws_SafeRthetaFlags
                                                                                    (S O) (S (S (S (S O)))))))
                                            (@SHCompose Monoid_RthetaFlags (S (S (S (S (S O)))))
                                                        (S O) (S (S O))
                                                        (@ScatH Monoid_RthetaFlags (S O) (S (S O)) (S O)
                                                                (S O)
                                                                (h_bound_second_half Monoid_RthetaSafeFlags MonoidLaws_SafeRthetaFlags
                                                                                     (S O) (S O))
                                                                (@ScatH_stride1_constr Monoid_RthetaSafeFlags MonoidLaws_SafeRthetaFlags
                                                                                       (S O) (S (S O))) (@zero CarrierA CarrierAz))
                                                        (@SafeCast (S (S (S (S (S O))))) (S O)
                                                                   (@IReduction (S (S (S (S (S O))))) (S O) (S (S O))
                                                                                (@minmax.max CarrierA CarrierAle CarrierAledec)
                                                                                (@abstract_algebra.sg_op_proper CarrierA CarrierAe
                                                                                                                (fun x y : CarrierA =>
                                                                                                                   @snd CarrierA CarrierA
                                                                                                                        (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                                                                                                                (@abstract_algebra.comsg_setoid CarrierA CarrierAe
                                                                                                                                                (fun x y : CarrierA =>
                                                                                                                                                   @snd CarrierA CarrierA
                                                                                                                                                        (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                                                                                                                                                (@abstract_algebra.semilattice_sg CarrierA CarrierAe
                                                                                                                                                                                  (fun x y : CarrierA =>
                                                                                                                                                                                     @snd CarrierA CarrierA
                                                                                                                                                                                          (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                                                                                                                                                                                  (@abstract_algebra.join_semilattice CarrierA CarrierAe
                                                                                                                                                                                                                      (fun x y : CarrierA =>
                                                                                                                                                                                                                         @snd CarrierA CarrierA
                                                                                                                                                                                                                              (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                                                                                                                                                                                                                      (@abstract_algebra.lattice_join CarrierA CarrierAe
                                                                                                                                                                                                                                                      (fun x y : CarrierA =>
                                                                                                                                                                                                                                                         @snd CarrierA CarrierA
                                                                                                                                                                                                                                                              (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                                                                                                                                                                                                                                                      (@minmax.min CarrierA CarrierAle CarrierAledec)
                                                                                                                                                                                                                                                      (@abstract_algebra.distr_lattice_lattice CarrierA
                                                                                                                                                                                                                                                                                               CarrierAe
                                                                                                                                                                                                                                                                                               (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                  @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                       (@minmax.sort CarrierA CarrierAle CarrierAledec x
                                                                                                                                                                                                                                                                                                                     y))
                                                                                                                                                                                                                                                                                               (@minmax.min CarrierA CarrierAle CarrierAledec)
                                                                                                                                                                                                                                                                                               (@minmax.DistributiveLattice_instance_0 CarrierA
                                                                                                                                                                                                                                                                                                                                       CarrierAe CarrierAle CarrierAto CarrierAledec)))))))
                                                                                (@zero CarrierA CarrierAz)
                                                                                (@SHFamilyOperatorCompose Monoid_RthetaSafeFlags
                                                                                                          (S (S (S (S (S O))))) (S (S (S (S O))))
                                                                                                          (S O) (S (S O))
                                                                                                          (mkSHOperatorFamily Monoid_RthetaSafeFlags
                                                                                                                              (S (S (S (S O)))) (S O) (S (S O))
                                                                                                                              (fun (j : nat) (jc : @lt nat Peano.lt j (S (S O))) =>
                                                                                                                                 @UnSafeCast (S (S (S (S O)))) (S O)
                                                                                                                                             (@SHCompose Monoid_RthetaFlags (S (S (S (S O))))
                                                                                                                                                         (S O) (S O)
                                                                                                                                                         (@SHCompose Monoid_RthetaFlags
                                                                                                                                                                     (S O) (S (S O)) (S O)
                                                                                                                                                                     (@liftM_HOperator Monoid_RthetaFlags
                                                                                                                                                                                       (S (S O)) (S O)
                                                                                                                                                                                       (@HReduction (S (S O))
                                                                                                                                                                                                    (@minmax.max CarrierA CarrierAle CarrierAledec)
                                                                                                                                                                                                    (@abstract_algebra.sg_op_proper CarrierA
                                                                                                                                                                                                                                    CarrierAe
                                                                                                                                                                                                                                    (fun x y : CarrierA =>
                                                                                                                                                                                                                                       @snd CarrierA CarrierA
                                                                                                                                                                                                                                            (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                          CarrierAledec x y))
                                                                                                                                                                                                                                    (@abstract_algebra.comsg_setoid CarrierA
                                                                                                                                                                                                                                                                    CarrierAe
                                                                                                                                                                                                                                                                    (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                       @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                            (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                                          CarrierAledec x y))
                                                                                                                                                                                                                                                                    (@abstract_algebra.semilattice_sg CarrierA
                                                                                                                                                                                                                                                                                                      CarrierAe
                                                                                                                                                                                                                                                                                                      (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                         @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                              (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                                            CarrierAledec x y))
                                                                                                                                                                                                                                                                                                      (@abstract_algebra.join_semilattice
                                                                                                                                                                                                                                                                                                         CarrierA CarrierAe
                                                                                                                                                                                                                                                                                                         (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                            @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                 (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                                               CarrierAledec x y))
                                                                                                                                                                                                                                                                                                         (@abstract_algebra.lattice_join
                                                                                                                                                                                                                                                                                                            CarrierA CarrierAe
                                                                                                                                                                                                                                                                                                            (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                               @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                    (@minmax.sort CarrierA
                                                                                                                                                                                                                                                                                                                                  CarrierAle CarrierAledec x y))
                                                                                                                                                                                                                                                                                                            (@minmax.min CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                                         CarrierAledec)
                                                                                                                                                                                                                                                                                                            (@abstract_algebra.distr_lattice_lattice
                                                                                                                                                                                                                                                                                                               CarrierA CarrierAe
                                                                                                                                                                                                                                                                                                               (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                                  @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                       (@minmax.sort CarrierA
                                                                                                                                                                                                                                                                                                                                     CarrierAle CarrierAledec x y))
                                                                                                                                                                                                                                                                                                               (@minmax.min CarrierA
                                                                                                                                                                                                                                                                                                                            CarrierAle CarrierAledec)
                                                                                                                                                                                                                                                                                                               (@minmax.DistributiveLattice_instance_0
                                                                                                                                                                                                                                                                                                                  CarrierA CarrierAe CarrierAle
                                                                                                                                                                                                                                                                                                                  CarrierAto CarrierAledec)))))))
                                                                                                                                                                                                    (@zero CarrierA CarrierAz))
                                                                                                                                                                                       (@HReduction_HOperator (S (S O))
                                                                                                                                                                                                              (@minmax.max CarrierA CarrierAle CarrierAledec)
                                                                                                                                                                                                              (@abstract_algebra.sg_op_proper CarrierA
                                                                                                                                                                                                                                              CarrierAe
                                                                                                                                                                                                                                              (fun x y : CarrierA =>
                                                                                                                                                                                                                                                 @snd CarrierA CarrierA
                                                                                                                                                                                                                                                      (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                    CarrierAledec x y))
                                                                                                                                                                                                                                              (@abstract_algebra.comsg_setoid CarrierA
                                                                                                                                                                                                                                                                              CarrierAe
                                                                                                                                                                                                                                                                              (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                 @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                      (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                    CarrierAledec x y))
                                                                                                                                                                                                                                                                              (@abstract_algebra.semilattice_sg CarrierA
                                                                                                                                                                                                                                                                                                                CarrierAe
                                                                                                                                                                                                                                                                                                                (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                                   @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                        (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                                                      CarrierAledec x y))
                                                                                                                                                                                                                                                                                                                (@abstract_algebra.join_semilattice
                                                                                                                                                                                                                                                                                                                   CarrierA CarrierAe
                                                                                                                                                                                                                                                                                                                   (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                                      @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                           (@minmax.sort CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                                                         CarrierAledec x y))
                                                                                                                                                                                                                                                                                                                   (@abstract_algebra.lattice_join
                                                                                                                                                                                                                                                                                                                      CarrierA CarrierAe
                                                                                                                                                                                                                                                                                                                      (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                                         @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                              (@minmax.sort CarrierA
                                                                                                                                                                                                                                                                                                                                            CarrierAle CarrierAledec x y))
                                                                                                                                                                                                                                                                                                                      (@minmax.min CarrierA CarrierAle
                                                                                                                                                                                                                                                                                                                                   CarrierAledec)
                                                                                                                                                                                                                                                                                                                      (@abstract_algebra.distr_lattice_lattice
                                                                                                                                                                                                                                                                                                                         CarrierA CarrierAe
                                                                                                                                                                                                                                                                                                                         (fun x y : CarrierA =>
                                                                                                                                                                                                                                                                                                                            @snd CarrierA CarrierA
                                                                                                                                                                                                                                                                                                                                 (@minmax.sort CarrierA
                                                                                                                                                                                                                                                                                                                                               CarrierAle CarrierAledec x y))
                                                                                                                                                                                                                                                                                                                         (@minmax.min CarrierA
                                                                                                                                                                                                                                                                                                                                      CarrierAle CarrierAledec)
                                                                                                                                                                                                                                                                                                                         (@minmax.DistributiveLattice_instance_0
                                                                                                                                                                                                                                                                                                                            CarrierA CarrierAe CarrierAle
                                                                                                                                                                                                                                                                                                                            CarrierAto CarrierAledec)))))))
                                                                                                                                                                                                              (@zero CarrierA CarrierAz)))
                                                                                                                                                                     (@Scatter Monoid_RthetaFlags
                                                                                                                                                                               (S O) (S (S O))
                                                                                                                                                                               (@h_index_map (S O) (S (S O)) j
                                                                                                                                                                                             (S O)
                                                                                                                                                                                             (ScatH_1_to_n_range_bound Monoid_RthetaSafeFlags
                                                                                                                                                                                                                       MonoidLaws_SafeRthetaFlags j
                                                                                                                                                                                                                       (S (S O)) (S O) jc))
                                                                                                                                                                               (@index_map_family_member_injective
                                                                                                                                                                                  (S O) (S (S O)) (S (S O))
                                                                                                                                                                                  (IndexMapFamily (S O)
                                                                                                                                                                                                  (S (S O)) (S (S O))
                                                                                                                                                                                                  (fun (j0 : nat) (jc0 : Peano.lt j0 (S (S O)))
                                                                                                                                                                                                   =>
                                                                                                                                                                                                     @h_index_map (S O)
                                                                                                                                                                                                                  (S (S O)) j0 (S O)
                                                                                                                                                                                                                  (ScatH_1_to_n_range_bound
                                                                                                                                                                                                                     Monoid_RthetaSafeFlags
                                                                                                                                                                                                                     MonoidLaws_SafeRthetaFlags j0
                                                                                                                                                                                                                     (S (S O)) (S O) jc0)))
                                                                                                                                                                                  (@h_j_1_family_injective (S (S O))) j jc)
                                                                                                                                                                               (@zero CarrierA CarrierAz)))
                                                                                                                                                         (@SHCompose Monoid_RthetaFlags
                                                                                                                                                                     (S (S (S (S O)))) (S (S O))
                                                                                                                                                                     (S O)
                                                                                                                                                                     (@SHCompose Monoid_RthetaFlags
                                                                                                                                                                                 (S (S O)) (S O) (S O)
                                                                                                                                                                                 (@SHPointwise Monoid_RthetaFlags
                                                                                                                                                                                               (S O)
                                                                                                                                                                                               (@IgnoreIndex CarrierA
                                                                                                                                                                                                             (S O)
                                                                                                                                                                                                             (@abs CarrierA CarrierAe CarrierAle CarrierAz
                                                                                                                                                                                                                   CarrierAneg CarrierAabs))
                                                                                                                                                                                               (@Reflexive_partial_app_morphism
                                                                                                                                                                                                  (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                  (forall
                                                                                                                                                                                                      (_ : @sig nat
                                                                                                                                                                                                                (fun i : nat => Peano.lt i (S O)))
                                                                                                                                                                                                      (_ : CarrierA), CarrierA)
                                                                                                                                                                                                  (@respectful CarrierA CarrierA
                                                                                                                                                                                                               (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                               (@equiv CarrierA CarrierAe))
                                                                                                                                                                                                  (@respectful
                                                                                                                                                                                                     (@sig nat (fun i : nat => Peano.lt i (S O)))
                                                                                                                                                                                                     (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                     (@equiv
                                                                                                                                                                                                        (@sig nat
                                                                                                                                                                                                              (fun i : nat => Peano.lt i (S O)))
                                                                                                                                                                                                        (@Sig_Equiv nat peano_naturals.nat_equiv
                                                                                                                                                                                                                    (fun i : nat => Peano.lt i (S O))))
                                                                                                                                                                                                     (@respectful CarrierA CarrierA
                                                                                                                                                                                                                  (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                                  (@equiv CarrierA CarrierAe)))
                                                                                                                                                                                                  (@IgnoreIndex CarrierA (S O))
                                                                                                                                                                                                  (@IgnoredIndex_proper (S O) CarrierA CarrierAe)
                                                                                                                                                                                                  (@abs CarrierA CarrierAe CarrierAle CarrierAz
                                                                                                                                                                                                        CarrierAneg CarrierAabs)
                                                                                                                                                                                                  (@proper_proper_proxy
                                                                                                                                                                                                     (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                     (@abs CarrierA CarrierAe CarrierAle
                                                                                                                                                                                                           CarrierAz CarrierAneg CarrierAabs)
                                                                                                                                                                                                     (@respectful CarrierA CarrierA
                                                                                                                                                                                                                  (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                                  (@equiv CarrierA CarrierAe))
                                                                                                                                                                                                     (@abstract_algebra.sm_proper CarrierA
                                                                                                                                                                                                                                  CarrierA CarrierAe CarrierAe
                                                                                                                                                                                                                                  (@abs CarrierA CarrierAe CarrierAle
                                                                                                                                                                                                                                        CarrierAz CarrierAneg CarrierAabs)
                                                                                                                                                                                                                                  (@abs_Setoid_Morphism CarrierA CarrierAe
                                                                                                                                                                                                                                                        CarrierAplus CarrierAmult CarrierAz
                                                                                                                                                                                                                                                        CarrierA1 CarrierAneg CarrierAr
                                                                                                                                                                                                                                                        CarrierAsetoid CarrierAle CarrierAto
                                                                                                                                                                                                                                                        CarrierAabs)))))
                                                                                                                                                                                 (@SafeCast (S (S O)) (S O)
                                                                                                                                                                                            (@SHBinOp (S O)
                                                                                                                                                                                                      (@SwapIndex2 CarrierA j
                                                                                                                                                                                                                   (@IgnoreIndex2 CarrierA sub))
                                                                                                                                                                                                      (@SwapIndex2_specialized_proper CarrierA
                                                                                                                                                                                                                                      CarrierAe CarrierAsetoid j
                                                                                                                                                                                                                                      (@IgnoreIndex2 CarrierA sub)
                                                                                                                                                                                                                                      (@Reflexive_partial_app_morphism
                                                                                                                                                                                                                                         (forall (_ : CarrierA) (_ : CarrierA),
                                                                                                                                                                                                                                             CarrierA)
                                                                                                                                                                                                                                         (forall (_ : nat)
                                                                                                                                                                                                                                            (_ : CarrierA)
                                                                                                                                                                                                                                            (_ : CarrierA), CarrierA)
                                                                                                                                                                                                                                         (@respectful CarrierA
                                                                                                                                                                                                                                                      (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                                                                      (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                                                                      (@equiv
                                                                                                                                                                                                                                                         (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                                                                         (@ext_equiv CarrierA CarrierAe
                                                                                                                                                                                                                                                                     CarrierA CarrierAe)))
                                                                                                                                                                                                                                         (@respectful nat
                                                                                                                                                                                                                                                      (forall (_ : CarrierA) (_ : CarrierA),
                                                                                                                                                                                                                                                          CarrierA)
                                                                                                                                                                                                                                                      (@equiv nat peano_naturals.nat_equiv)
                                                                                                                                                                                                                                                      (@respectful CarrierA
                                                                                                                                                                                                                                                                   (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                                                                                   (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                                                                                   (@respectful CarrierA CarrierA
                                                                                                                                                                                                                                                                                (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                                                                                                (@equiv CarrierA CarrierAe))))
                                                                                                                                                                                                                                         (@IgnoreIndex2 CarrierA)
                                                                                                                                                                                                                                         (@IgnoreIndex2_proper CarrierA CarrierAe)
                                                                                                                                                                                                                                         sub
                                                                                                                                                                                                                                         (@proper_proper_proxy
                                                                                                                                                                                                                                            (forall (_ : CarrierA) (_ : CarrierA),
                                                                                                                                                                                                                                                CarrierA) sub
                                                                                                                                                                                                                                            (@respectful CarrierA
                                                                                                                                                                                                                                                         (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                                                                         (@equiv CarrierA CarrierAe)
                                                                                                                                                                                                                                                         (@equiv
                                                                                                                                                                                                                                                            (forall _ : CarrierA, CarrierA)
                                                                                                                                                                                                                                                            (@ext_equiv CarrierA CarrierAe
                                                                                                                                                                                                                                                                        CarrierA CarrierAe)))
                                                                                                                                                                                                                                            CarrierA_sub_proper))))))
                                                                                                                                                                     (@Gather Monoid_RthetaFlags
                                                                                                                                                                              (S (S (S (S O)))) (S (S O))
                                                                                                                                                                              (@h_index_map (S (S O))
                                                                                                                                                                                            (S (S (S (S O)))) j (S (S O))
                                                                                                                                                                                            (GathH_jn_domain_bound Monoid_RthetaSafeFlags
                                                                                                                                                                                                                   MonoidLaws_SafeRthetaFlags j
                                                                                                                                                                                                                   (S (S O)) jc)))))))
                                                                                                          (@GathH Monoid_RthetaSafeFlags (S (S (S (S (S O)))))
                                                                                                                  (S (S (S (S O)))) (S O) (S O)
                                                                                                                  (h_bound_second_half Monoid_RthetaSafeFlags
                                                                                                                                       MonoidLaws_SafeRthetaFlags (S O)
                                                                                                                                       (S (S (S (S O)))))))))))) (dynwin_SHCOL1 a).
        Proof.


          (* --- BEGIN: problem --- *)

          intros a.
          Opaque SHCompose.

          (* The following fails with:

             Error:
             Ltac call to "setoid_rewrite (orient) (glob_constr_with_bindings)" failed.
             Tactic failure: setoid rewrite failed: Nothing to rewrite.

          setoid_rewrite rewrite_Reduction_ScatHUnion_max_zero.
           *)

           (* However this versoin of the same lemma without one of the premises
works: *)
          setoid_rewrite rewrite_Reduction_ScatHUnion_max_zero'.


        (* Workaround to apply original lemma

          match goal with
          | [ |- context G [ mkSHOperatorFamily _ _ _ _ ?f ]] =>
            match f with
            | (fun j jc => UnSafeCast (?torewrite ⊚ ?rest )) =>
              setoid_replace
                (mkSHOperatorFamily _ _ _ _ f) with
                  (mkSHOperatorFamily _ _ _ _
                                      (fun (j:nat) (jc:j<2) => UnSafeCast rest))
            end
          end.
          all:revgoals.
          f_equiv.
          intros j jc.
          f_equiv.

          apply rewrite_Reduction_ScatHUnion_max_zero.

           *)


        Admitted.

      End SigmaHCOL_rewriting.
    End DynWin.
  End Spiral.
End Spiral_DOT_DynWin.
