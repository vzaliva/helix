Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Definition evalContext:Type := list DSHVar.

Definition evalVexp (st:evalContext) {n} (exp:VExpr n): option (avector n) :=
  match exp in (VExpr n0) return (option (vector CarrierA n0)) with
  | @VVar n0 i =>
    match nth_error st i with
    | Some (@DSHvecVar n2 v) =>
      match eq_nat_dec n2 n0 as s0 return (_ ≡ s0 -> option (vector CarrierA n0))
      with
      | left E => fun _ => eq_rect n2 (fun n3 => option (vector CarrierA n3)) (Some v) n0 E
      | right _ => fun _ => None
      end eq_refl
    | _ => None
    end
  | @VConst _ t => Some t
  end.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Fixpoint evalNexp (st:evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => v <- (nth_error st i) ;;
               (match v with
                | DSHnatVar x => Some x
                | _ => None
                end)
  | NConst c => Some c
  | NDiv a b => liftM2 Nat.div (evalNexp st a) (evalNexp st b)
  | NMod a b => liftM2 Nat.modulo (evalNexp st a) (evalNexp st b)
  | NPlus a b => liftM2 Nat.add (evalNexp st a) (evalNexp st b)
  | NMinus a b => liftM2 Nat.sub (evalNexp st a) (evalNexp st b)
  | NMult a b => liftM2 Nat.mul (evalNexp st a) (evalNexp st b)
  | NMin a b => liftM2 Nat.min (evalNexp st a) (evalNexp st b)
  | NMax a b => liftM2 Nat.max (evalNexp st a) (evalNexp st b)
  end.

Fixpoint evalAexp (st:evalContext) (e:AExpr): option CarrierA :=
  match e with
  | AVar i => v <- (nth_error st i) ;;
               (match v with
                | DSHCarrierAVar x => Some x
                | _ => None
                end)
  | AConst x => Some x
  | AAbs x =>  liftM abs (evalAexp st x)
  | APlus a b => liftM2 plus (evalAexp st a) (evalAexp st b)
  | AMult a b => liftM2 mult (evalAexp st a) (evalAexp st b)
  | AMin a b => liftM2 min (evalAexp st a) (evalAexp st b)
  | AMax a b => liftM2 max (evalAexp st a) (evalAexp st b)
  | AMinus a b =>
    a' <- (evalAexp st a) ;;
       b' <- (evalAexp st b) ;;
       ret (sub a' b')
  | @ANth n v i =>
    v' <- (evalVexp st v) ;;
       i' <- (evalNexp st i) ;;
       match Compare_dec.lt_dec i' n with
       | left ic => Some (Vnth v' ic)
       | in_right => None
       end
  | AZless a b => liftM2 Zless (evalAexp st a) (evalAexp st b)
  end.

Require Import Coq.Arith.Compare_dec.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.Rtheta.

Definition unLiftM_HOperator'
           {fm}
           {i o}
           (op: svector fm i -> svector fm o)
  : avector i -> avector o :=
  densify fm ∘ op ∘ sparsify fm.

Global Instance unLiftM_HOperator'_proper
       {fm} {i o} :
  Proper (
      ((=) ==> (=)) ==>  (=) ==> (=)) (@unLiftM_HOperator' fm i o).
Proof.
  intros f g Efg x y E.
  unfold unLiftM_HOperator', compose.
  f_equiv.
  apply Efg.
  f_equiv.
  apply E.
Qed.

Definition evalIUnCarrierA (Γ: evalContext) (f: DSHIUnCarrierA)
           (i:nat) (a:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVar a :: DSHnatVar i :: Γ) f.

Definition evalIBinCarrierA (Γ: evalContext) (f: DSHIBinCarrierA)
           (i:nat) (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVar b :: DSHCarrierAVar a :: DSHnatVar i :: Γ) f.

Definition evalBinCarrierA (Γ: evalContext) (f: DSHBinCarrierA)
           (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVar b :: DSHCarrierAVar a :: Γ) f.

Definition evalDSHPointwise (Γ: evalContext) {i: nat} (f: DSHIUnCarrierA) (x:avector i): option (avector i) :=
  vsequence (Vbuild (fun j jd => evalIUnCarrierA Γ f j (Vnth x jd))).

Definition evalDSHBinOp (Γ: evalContext) {o:nat} (f: DSHIBinCarrierA) (x:avector (o+o)) : option (avector o) :=
  let (a,b) := vector2pair o x in
  vsequence (Vbuild (fun i (ip:i<o) =>
                       evalIBinCarrierA Γ f i (Vnth a ip) (Vnth b ip))).

Definition evalDSHInductor (Γ: evalContext) (n:nat) (f: DSHBinCarrierA) (initial: CarrierA) (v:CarrierA): option CarrierA :=
  nat_rect _
           (Some initial)
           (fun _ (x:option CarrierA) => x' <- x ;; evalBinCarrierA Γ f x' v)
           n.

Fixpoint evalDSHOperator {i o} (Γ: evalContext) (op: DSHOperator i o) (x:avector i) {struct op}: option (avector o) :=
  match op with
  | @DSHeUnion o be z =>
    fun x => b <- evalNexp Γ be ;;
            match lt_dec b o as l return (_ ≡ l → option (vector CarrierA o))
            with
            | left bc => fun _ => ret (unLiftM_HOperator' (eUnion' Monoid_RthetaFlags bc z) x)
            | right _ => fun _ => None
            end eq_refl
  | @DSHeT i be =>
    fun x => b <- evalNexp Γ be ;;
            match lt_dec b i as l return (_ ≡ l → option (vector CarrierA 1))
            with
            | left bc => fun _ => ret (unLiftM_HOperator' (eT' Monoid_RthetaFlags bc) x)
            | right _ => fun _ => None
            end eq_refl
  | @DSHPointwise i f => fun x => evalDSHPointwise Γ f x
  | @DSHBinOp o f => fun x => evalDSHBinOp Γ f x
  | @DSHInductor ne f initial => fun x =>
                                  n <- evalNexp Γ ne ;;
                                    r <- evalDSHInductor Γ n f initial (Vhead x) ;;
                                    ret (Lst r)
  | @DSHIUnion i o n dot initial body =>
    fun (x:avector i) =>
      nat_rect _
               (Some (Vconst initial o))
               (fun j (t:option (avector o)) =>
                  t' <- t ;;
                     v' <- evalDSHOperator (DSHnatVar j :: Γ) body x ;;
                     vsequence (Vmap2 (evalBinCarrierA Γ dot) v' t'))
               n
  | @DSHISumUnion i o n body =>
    fun (x:avector i) =>
      let dot := APlus (AVar 1) (AVar 0) in
      let initial := zero in
      nat_rect _
               (Some (Vconst initial o))
               (fun j (t:option (avector o)) =>
                  t' <- t ;;
                     v' <- evalDSHOperator (DSHnatVar j :: Γ) body x ;;
                     vsequence (Vmap2 (evalBinCarrierA Γ dot) v' t'))
               n
  | @DSHIReduction i o n dot initial body =>
    (* Actually same as IUnion *)
    fun (x:avector i) =>
      nat_rect _
               (Some (Vconst initial o))
               (fun j (t:option (avector o)) =>
                  t' <- t ;;
                     v' <- evalDSHOperator (DSHnatVar j :: Γ) body x ;;
                     vsequence (Vmap2 (evalBinCarrierA Γ dot) v' t'))
               n
  | @DSHCompose i1 o2 o3 f g =>
    fun v => evalDSHOperator Γ g v >>= evalDSHOperator Γ f
  | @DSHHTSUMUnion i o dot f g =>
    fun v =>
      a <- evalDSHOperator Γ f v ;;
        b <- evalDSHOperator Γ g v ;;
        vsequence (Vmap2 (evalBinCarrierA Γ dot) a b)
  end x.


Local Ltac proper_eval2 IHe1 IHe2 :=
  simpl;
  repeat break_match;subst; try reflexivity; try some_none_contradiction;
  f_equiv;
  rewrite <- Some_inj_equiv in IHe1;
  rewrite <- Some_inj_equiv in IHe2;
  rewrite IHe1, IHe2;
  reflexivity.

Global Instance evalNexp_proper:
  Proper ((=) ==> (=) ==> (=)) evalNexp.
Proof.
  intros c1 c2 Ec e1 e2 Ee.
  induction Ee; simpl.
  -
    unfold equiv, peano_naturals.nat_equiv in H.
    subst n2. rename n1 into n.
    assert(E: nth_error c1 n = nth_error c2 n).
    {
      apply nth_error_proper.
      apply Ec.
      reflexivity.
    }
    repeat break_match; subst; try reflexivity; try some_none_contradiction; try (rewrite <- Some_inj_equiv in E; inversion E).
    subst.
    rewrite H1.
    reflexivity.
  -
    rewrite H.
    reflexivity.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
Qed.

Global Instance evalVexp_proper:
  Proper ((=) ==> (forall_relation (fun n => (=) ==> (=)))) (evalVexp).
Proof.
  intros c1 c2 Ec n e1 e2 Ee.
  induction Ee; simpl.
  -
    unfold equiv, peano_naturals.nat_equiv in H.
    subst n1. rename n0 into v.

    assert(E: nth_error c1 v = nth_error c2 v).
    {
      apply nth_error_proper.
      apply Ec.
      reflexivity.
    }
    repeat break_match; subst; try reflexivity; try some_none_contradiction; try (rewrite <- Some_inj_equiv in E; inversion E); inv_exitstT; subst; try congruence.
    simpl.
    f_equiv.
    auto.
  -
    rewrite H.
    auto.
Qed.

Global Instance evalAexp_proper:
  Proper ((=) ==> (=) ==> (=)) evalAexp.
Proof.
  intros c1 c2 Ec e1 e2 Ee.
  induction Ee; simpl.
  - unfold equiv, peano_naturals.nat_equiv in H.
    subst n1. rename n0 into n.
    assert(E: nth_error c1 n = nth_error c2 n).
    {
      apply nth_error_proper.
      apply Ec.
      reflexivity.
    }
    repeat break_match; subst; try reflexivity; try some_none_contradiction; try (rewrite <- Some_inj_equiv in E; inversion E).
    subst.
    rewrite H1.
    reflexivity.
  - f_equiv. apply H.
  - assert(C1:  evalVexp c1 v1 = evalVexp c2 v2)
      by (apply evalVexp_proper; auto).
    assert(C2:  evalNexp c1 n1 = evalNexp c2 n2)
      by (apply evalNexp_proper; auto).
    repeat break_match; subst ; try reflexivity; subst;
      try inversion C1; try inversion C2;
        apply Some_inj_equiv in C1;
        apply Some_inj_equiv in C2; try congruence.
    unfold peano_naturals.nat_equiv in *.
    subst.
    f_equiv.
    apply Vnth_equiv; auto.
  - repeat break_match;subst; try reflexivity; try some_none_contradiction.
    f_equiv.
    rewrite <- Some_inj_equiv in IHEe.
    rewrite IHEe.
    reflexivity.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
Qed.

Lemma evalBinCarrierA_proper:
  Proper ((=) ==> (=) ==> (=)) evalBinCarrierA.
Proof.
  intros c1 c2 Ec e1 e2 Ee.
  unfold evalBinCarrierA.
  intros a a' Ea b b' Eb.
  apply evalAexp_proper.
  -
    unfold equiv, List_equiv.
    apply List.Forall2_cons; constructor; auto.
    constructor; auto.
  -
    auto.
Qed.

Lemma evalDSHOperator_DSHIUnion_Sn
      {i o: nat}
      (n:nat) (dot: DSHBinCarrierA) (initial: CarrierA)
      (op: DSHOperator i o)
      (x: avector i)
      {Γ: evalContext}
  :
    evalDSHOperator Γ (@DSHIUnion i o (S n) dot initial op) x =
    (t <- evalDSHOperator Γ (@DSHIUnion i o n dot initial op) x ;;
       v <- evalDSHOperator (DSHnatVar n :: Γ) op x ;;
       vsequence (Vmap2 (evalBinCarrierA Γ dot) v t)).
Proof.
  reflexivity.
Qed.

Lemma evalDSHOperator_DSHIReduction_Sn
      {i o: nat}
      (n:nat) (dot: DSHBinCarrierA) (initial: CarrierA)
      (op: DSHOperator i o)
      (x: avector i)
      {Γ: evalContext}
  :
    evalDSHOperator Γ (@DSHIReduction i o (S n) dot initial op) x =
    (t <- evalDSHOperator Γ (@DSHIReduction i o n dot initial op) x ;;
       v <- evalDSHOperator (DSHnatVar n :: Γ) op x ;;
       vsequence (Vmap2 (evalBinCarrierA Γ dot) v t)).
Proof.
  reflexivity.
Qed.

Lemma evalDSHOperator_DSHISumunion_Sn
      {i o: nat}
      (n:nat)
      (op: DSHOperator i o)
      (x: avector i)
      {Γ: evalContext}
  :
    evalDSHOperator Γ (@DSHISumUnion i o (S n) op) x =
    (t <- evalDSHOperator Γ (@DSHISumUnion i o n op) x ;;
       v <- evalDSHOperator (DSHnatVar n :: Γ) op x ;;
       vsequence (Vmap2 (evalBinCarrierA Γ (APlus (AVar 1) (AVar 0))) v t)).
Proof.
  reflexivity.
Qed.

Lemma evalDSHOperator_DSHISumUnion_DSHIUnion
      {i o n: nat}
      {body: DSHOperator i o}
      {Γ: evalContext}:
  evalDSHOperator Γ (@DSHISumUnion i o n body) ≡
                  evalDSHOperator Γ (@DSHIUnion i o n (APlus (AVar 1) (AVar 0)) zero body).
Proof.
  reflexivity.
Qed.

Lemma evalDSHOperator_DSHISumUnion_DSHIReduction
      {i o n: nat}
      {dot}
      {initial}
      {body: DSHOperator i o}
      {Γ: evalContext}:
  evalDSHOperator Γ (@DSHIUnion i o n dot initial body) ≡
                  evalDSHOperator Γ (@DSHIReduction i o n dot initial body).
Proof.
  reflexivity.
Qed.

Global Instance evalDSHOperator_arg_proper
       {i o} (Γ: evalContext) (op: DSHOperator i o):
  Proper ((=) ==> (=)) (@evalDSHOperator i o Γ op).
Proof.
  intros x y E.
  revert Γ.
  induction op; intros Γ.
  -
    simpl.
    repeat break_match; auto.
    f_equiv.
    rewrite E.
    reflexivity.
  -
    simpl.
    repeat break_match; auto.
    f_equiv.
    rewrite E.
    reflexivity.
  -
    simpl.
    unfold evalDSHPointwise.
    apply vsequence_option_proper.
    f_equiv.
    intros j jc.
    unfold evalIUnCarrierA.
    apply evalAexp_proper.
    *
      unfold equiv, List_equiv.
      apply List.Forall2_cons.
      --
        unfold equiv, DSHVar_Equiv.
        simpl.
        constructor.
        apply Vnth_arg_equiv.
        apply E.
      --
        reflexivity.
    *
      reflexivity.
  -
    simpl.
    unfold evalDSHBinOp.
    rewrite Vbreak_eq_app with (v:=x).
    rewrite Vbreak_eq_app with (v:=y).
    break_let.
    break_let.
    apply vsequence_option_proper.
    f_equiv.
    intros j jc.

    unfold evalIBinCarrierA.
    apply evalAexp_proper; try reflexivity.

    unfold vector2pair in *.
    rewrite Vbreak_app in Heqp0.
    rewrite Vbreak_app in Heqp.
    inversion Heqp0.
    inversion Heqp.

    apply List.Forall2_cons.
    +
      apply DSHCarrierAVar_equiv.
      apply Vnth_proper.
      rewrite E.
      reflexivity.
    +
      apply List.Forall2_cons.
      apply DSHCarrierAVar_equiv.
      apply Vnth_proper.
      rewrite E.
      reflexivity.
      reflexivity.
  -
    simpl.
    break_match; try reflexivity.
    dep_destruct x.
    dep_destruct y.
    simpl.
    inversion E.
    clear E x y x0 x1 H0.
    rename h into x.
    rename h0 into y.
    assert(C: evalDSHInductor Γ n0 f initial x = evalDSHInductor Γ n0 f initial y).
    {
      clear Heqo.
      induction n0.
      -
        reflexivity.
      -
        simpl.
        repeat break_match.
        unfold evalBinCarrierA.
        apply evalAexp_proper.
        apply List.Forall2_cons.
        apply DSHCarrierAVar_equiv.
        apply H.
        apply List.Forall2_cons.
        apply DSHCarrierAVar_equiv.
        apply Some_inj_equiv, IHn0.
        reflexivity.
        reflexivity.
        some_none_contradiction.
        some_none_contradiction.
        reflexivity.
    }
    break_match; inversion C.
    +
      f_equiv.
      rewrite H2.
      reflexivity.
    +
      reflexivity.
  -
    induction n.
    +
      reflexivity.
    +
      rewrite 2!evalDSHOperator_DSHIUnion_Sn.
      Opaque evalDSHOperator. simpl. Transparent evalDSHOperator.
      specialize (IHop x y E (DSHnatVar n :: Γ) ).
      repeat break_match ; subst; try reflexivity; try inversion IHn; try inversion IHop.
      apply vsequence_option_proper.
      eapply Vmap2_proper.
      apply evalBinCarrierA_proper; reflexivity.
      apply Some_inj_equiv, IHop.
      apply Some_inj_equiv, IHn.
  -
    rewrite evalDSHOperator_DSHISumUnion_DSHIUnion.
    (* Same proof as for IUnion (above) *)
    induction n.
    +
      reflexivity.
    +
      rewrite 2!evalDSHOperator_DSHIUnion_Sn.
      Opaque evalDSHOperator. simpl. Transparent evalDSHOperator.
      specialize (IHop x y E (DSHnatVar n :: Γ) ).
      repeat break_match ; subst; try reflexivity; try inversion IHn; try inversion IHop.
      apply vsequence_option_proper.
      eapply Vmap2_proper.
      apply evalBinCarrierA_proper; reflexivity.
      apply Some_inj_equiv, IHop.
      apply Some_inj_equiv, IHn.
  -
    rewrite <- evalDSHOperator_DSHISumUnion_DSHIReduction.
    (* Same proof as for IUnion (above) *)
    induction n.
    +
      reflexivity.
    +
      rewrite 2!evalDSHOperator_DSHIUnion_Sn.
      Opaque evalDSHOperator. simpl. Transparent evalDSHOperator.
      specialize (IHop x y E (DSHnatVar n :: Γ) ).
      repeat break_match ; subst; try reflexivity; try inversion IHn; try inversion IHop.
      apply vsequence_option_proper.
      eapply Vmap2_proper.
      apply evalBinCarrierA_proper; reflexivity.
      apply Some_inj_equiv, IHop.
      apply Some_inj_equiv, IHn.
  -
    simpl.
    specialize (IHop2 x y E Γ).
    repeat break_match; try reflexivity; try inversion IHop2.
    apply IHop1, H1.
  -
    simpl.
    specialize (IHop1 x y E Γ).
    specialize (IHop2 x y E Γ).
    repeat break_match; try reflexivity; try inversion IHop2; try inversion IHop1.
    subst.
    apply vsequence_option_proper.
    eapply Vmap2_proper.
    apply evalBinCarrierA_proper; reflexivity.
    apply H4.
    apply H1.
Qed.
