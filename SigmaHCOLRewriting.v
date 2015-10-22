
Require Import Spiral.
Require Import SVector.
Require Import AExp.
Require Import HCOL.
Require Import SigmaHCOL.
Import SigmaHCOL_Operators.
Require Import HCOLSyntax.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program. 

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Section SigmaHCOLRewriting.
  Context

    `{Ae: Equiv A}
    `{Az: Zero A} `{A1: One A}
    `{Aplus: Plus A} `{Amult: Mult A} 
    `{Aneg: Negate A}
    `{Ale: Le A}
    `{Alt: Lt A}
    `{Ato: !@TotalOrder A Ae Ale}
    `{Aabs: !@Abs A Ae Ale Az Aneg}
    `{Asetoid: !@Setoid A Ae}
    `{Aledec: !∀ x y: A, Decision (x ≤ y)}
    `{Aeqdec: !∀ x y, Decision (x = y)}
    `{Altdec: !∀ x y: A, Decision (x < y)}
    `{Ar: !Ring A}
    `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
    `{ASSO: !@StrictSetoidOrder A Ae Alt}
  .

  Add Ring RingA: (stdlib_ring_theory A).
  
  Open Scope vector_scope.
  Global Open Scope nat_scope.

  Lemma Vfold_OptionUnion_empty:
    ∀ (m : nat) (h : option A) (x : vector (option A) m),
      Vforall is_None x → Vfold_left OptionUnion h x ≡ h.
  Proof.
    intros m h x E.
    induction x.
    auto.
    simpl.
    simpl in E. destruct E as [Eh Ex].
    rewrite IHx; try assumption.
    dep_destruct h0; none_some_elim.
    destruct h; auto.
  Qed.
  
  
  (* Unary union of vector where all except exactly one element are "structural zero", and one is unknown, is the value of this element  *)
  Lemma Lemma3 m j (x:svector A (S m)) (jc:j<(S m)):
      (forall i (ic:i<(S m)) (inej: i ≢ j), is_None (Vnth x ic)) -> (VecOptUnion x ≡ Vnth x jc).
  Proof.
    intros SZ.

    induction m.
    - dep_destruct x.
      dep_destruct x0.
      destruct j; crush.
      (* got IHm *)

    - dep_destruct x.
      destruct (eq_nat_dec j 0).
      +
        rewrite Vnth_cons_head; try assumption.
        unfold VecOptUnion.
        simpl.
        
        assert(Vforall is_None x0).
        {
          apply Vforall_nth_intro.
          intros.
          assert(ipp:S i < S (S m)) by lia.
          replace (Vnth x0 ip) with (Vnth (Vcons h x0) ipp) by apply Vnth_Sn.
          apply SZ; lia.
        }

        apply Vfold_OptionUnion_empty; assumption.
      +
  Qed.
  
  Section SigmaHCOLRewriting.
    