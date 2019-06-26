Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
(* Require Import Helix.SigmaHCOL.SigmaHCOLImpl. *)
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.


Definition evalContext:Type := list DSHVal.
Definition context_index := nat.

Definition context_lookup
           (c: evalContext)
           (n: context_index)
           : option DSHVal
  := nth_error c n.

Definition context_replace
           (c: evalContext)
           (n: context_index)
           (v: DSHVal)
  : evalContext
  :=
    ListUtil.replace_at c n v.

Definition context_lookup_mem
           (c: evalContext)
           (n: context_index)
           : option mem_block
  := match (nth_error c n) with
     | Some (DSHmemVal m) => ret m
     | _ => None
     end.



(* Evaluation of expressions does not allow for side-effects *)
Definition evalVexp (st:evalContext) {n} (exp:VExpr n): option (avector n) :=
  match exp in (VExpr n0) return (option (vector CarrierA n0)) with
  | @VVar n0 i =>
    match nth_error st i with
    | Some (@DSHvecVal n2 v) =>
      match eq_nat_dec n2 n0 as s0 return (_ ≡ s0 -> option (vector CarrierA n0))
      with
      | left E => fun _ => eq_rect n2 (fun n3 => option (vector CarrierA n3)) (Some v) n0 E
      | right _ => fun _ => None
      end eq_refl
    | _ => None
    end
  | @VConst _ t => Some t
  end.

(* Evaluation of expressions does not allow for side-effects *)
Fixpoint evalNexp (st:evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => v <- (nth_error st i) ;;
               (match v with
                | DSHnatVal x => Some x
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

(* Evaluation of expressions does not allow for side-effects *)
Fixpoint evalAexp (st:evalContext) (e:AExpr): option CarrierA :=
  match e with
  | AVar i => v <- (nth_error st i) ;;
                (match v with
                 | DSHCarrierAVal x => Some x
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

(*
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
 *)

(* Evaluation of functions does not allow for side-effects *)
Definition evalIUnCarrierA (Γ: evalContext) (f: DSHIUnCarrierA)
           (i:nat) (a:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal a :: DSHnatVal i :: Γ) f.

(* Evaluation of functions does not allow for side-effects *)
Definition evalIBinCarrierA (Γ: evalContext) (f: DSHIBinCarrierA)
           (i:nat) (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal b :: DSHCarrierAVal a :: DSHnatVal i :: Γ) f.

(* Evaluation of functions does not allow for side-effects *)
Definition evalBinCarrierA (Γ: evalContext) (f: DSHBinCarrierA)
           (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal b :: DSHCarrierAVal a :: Γ) f.

Fixpoint evalDSHMap
         (i: nat)
         (f: DSHIUnCarrierA)
         (Γ: evalContext)
         (x y: mem_block) : option (mem_block)
  :=
    v <- mem_lookup i x ;;
      let v' := evalIUnCarrierA Γ f i v in
      let y' := mem_add i v y in
      match i with
      | O => ret y'
      | S i' => evalDSHMap i' f Γ x y'
      end.

(*
Definition evalDSHPointwise (Γ: evalContext) {i: nat} (f: DSHIUnCarrierA) (x:avector i): option (avector i) :=
  vsequence (Vbuild (fun j jd => evalIUnCarrierA Γ f j (Vnth x jd))).

Definition evalDSHBinOp (Γ: evalContext) {o:nat} (f: DSHIBinCarrierA) (x:avector (o+o)) : option (avector o) :=
  let (a,b) := vector2pair o x in
  vsequence (Vbuild (fun i (ip:i<o) =>
                       evalIBinCarrierA Γ f i (Vnth a ip) (Vnth b ip))).

Fixpoint evalDSHInductor (Γ: evalContext) (n:nat) (f: DSHBinCarrierA) (initial: CarrierA) (v:CarrierA): option CarrierA :=
  match n with
  | O => Some initial
  | S p => t <- evalDSHInductor Γ p f initial v ;;
            evalBinCarrierA Γ f t v
  end.

Lemma evalDSHInductor_Sn
      (Γ: evalContext)
      (n:nat)
      (f: DSHBinCarrierA)
      (initial: CarrierA)
      (v:CarrierA):
  evalDSHInductor Γ (S n) f initial v =
  (
    t <- evalDSHInductor Γ n f initial v ;;
      evalBinCarrierA Γ f t v
  ).
Proof.
  reflexivity.
Qed.

Definition optDot
           {n}
           (dot: CarrierA -> CarrierA -> option CarrierA)
           (a b: option (avector n)): option (avector n)
  :=
    a' <- a ;;
       b' <- b ;;
       vsequence (Vmap2 dot a' b').

Global Instance optDot_arg_proper
       {n:nat}
       {f: CarrierA → CarrierA → option CarrierA}
       `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}:
  Proper (equiv ==> equiv ==> equiv) (optDot (n:=n) f).
Proof.
  intros x x' Ex y y' Ey.
  unfold optDot.
  simpl.
  repeat break_match; try reflexivity; try some_none.
  apply vsequence_option_proper.
  repeat some_inv.
  f_equiv; auto.
Qed.

Global Instance optDot_proper
       {n:nat}:
  Proper (((=) ==> (=) ==> (=)) ==> equiv ==> equiv ==> equiv) (optDot (n:=n)).
Proof.
  intros f f' Ef x x' Ex y y' Ey.
  unfold optDot.
  simpl.
  repeat break_match; try reflexivity; try some_none.
  apply vsequence_option_proper.
  repeat some_inv.
  rewrite 2!Vmap2_as_Vbuild.
  apply Vbuild_proper.
  intros j jc.
  f_equiv.
  -
    apply Ef.
  -
    apply Vnth_arg_equiv; auto.
  -
    apply Vnth_arg_equiv; auto.
Qed.

Definition evalDiamond
           {n o: nat}
           (dot: CarrierA → CarrierA → option CarrierA)
           (initial: CarrierA)
           (m: vector (option (avector o)) n)
  : option (avector o)
  := Vfold_left_rev (optDot dot) (Some (Vconst initial o)) m.
 *)

Fixpoint evalDSHOperator
         (Γ: evalContext)
         (op: DSHOperator)
         (x_i y_i: context_index) {struct op}: option (evalContext)
  :=
    x <- context_lookup_mem Γ x_i ;;
      y <- context_lookup_mem Γ y_i ;;
      (match op with
      | DSHAssign src_e dst_e =>
        (src <- evalNexp Γ src_e ;;
             dst <- evalNexp Γ dst_e ;;
             v <- mem_lookup src x ;;
             let y' := mem_add dst v y in
             ret (context_replace Γ y_i (DSHmemVal y'))
        )
      | @DSHMap i f =>
        y' <- evalDSHMap i f Γ x y ;;
           ret (context_replace Γ y_i (DSHmemVal y'))
      | @DSHMap2 o f => None
      | DSHPower n f initial => None
      | DSHLoop n dot initial => None
      | @DSHFold o n dot initial => None
      | DSHSeq f g => None
      | @DSHSum o dot f g => None
      end).

(*
  match op with
  | @DSHeUnion o be z =>
    fun x => b <- evalNexp Γ be ;;
            match lt_dec b o as l return (_ ≡ l → option (vector CarrierA o))
            with
            | left bc => fun _ => ret (unLiftM_HOperator' (eUnion' (fm:=Monoid_RthetaFlags) bc z) x)
            | right _ => fun _ => None
            end eq_refl
  | @DSHeT i be =>
    fun x => b <- evalNexp Γ be ;;
            match lt_dec b i as l return (_ ≡ l → option (vector CarrierA 1))
            with
            | left bc => fun _ => ret (unLiftM_HOperator' (eT' (fm:=Monoid_RthetaFlags) bc) x)
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
      evalDiamond (evalBinCarrierA Γ dot) initial
                  (Vbuild (λ (j:nat) (jc:j<n), evalDSHOperator (DSHnatVal j :: Γ) body x))
  | @DSHIReduction i o n dot initial body =>
    (* Actually same as IUnion *)
    fun (x:avector i) =>
      evalDiamond (evalBinCarrierA Γ dot) initial
                  (Vbuild (λ (j:nat) (jc:j<n), evalDSHOperator (DSHnatVal j :: Γ) body x))
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
  repeat break_match;subst; try reflexivity; try some_none;
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
    repeat break_match; subst; try reflexivity; try some_none; try (rewrite <- Some_inj_equiv in E; inversion E).
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
    repeat break_match; subst; try reflexivity; try some_none; try (rewrite <- Some_inj_equiv in E; inversion E); inv_exitstT; subst; try congruence.
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
    repeat break_match; subst; try reflexivity; try some_none; try (rewrite <- Some_inj_equiv in E; inversion E).
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
  - repeat break_match;subst; try reflexivity; try some_none.
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

Global Instance evalBinCarrierA_proper:
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

Lemma evalDSHOperator_DSHIUnion_DSHIReduction
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
      apply DSHCarrierAVal_equiv.
      apply Vnth_proper.
      rewrite E.
      reflexivity.
    +
      apply List.Forall2_cons.
      apply DSHCarrierAVal_equiv.
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
        apply DSHCarrierAVal_equiv.
        apply H.
        apply List.Forall2_cons.
        apply DSHCarrierAVal_equiv.
        apply Some_inj_equiv, IHn0.
        reflexivity.
        reflexivity.
        some_none.
        some_none.
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
    + reflexivity.
    + simpl.
      unfold evalDiamond.
      eapply Vfold_left_rev_arg_proper; try typeclasses eauto.
      apply Vbuild_proper.
      intros j jc.
      apply IHop.
      apply E.
  -
    rewrite <- evalDSHOperator_DSHIUnion_DSHIReduction.
    (* Same proof as for IUnion (above) *)
    induction n.
    + reflexivity.
    + simpl.
      unfold evalDiamond.
      eapply Vfold_left_rev_arg_proper.
      * typeclasses eauto.
      * apply optDot_arg_proper.
      * apply Vbuild_proper.
        intros j jc.
        apply IHop.
        apply E.
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

Fixpoint NExpr_var_subst
         (name: nat)
         (value: NExpr)
         (nexp: NExpr): NExpr :=
  match nexp with
  | NVar v =>
    if eq_nat_dec v name
    then value
    else nexp
  | NConst _ => nexp
  | NDiv   a b => NDiv   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMod   a b => NMod   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NPlus  a b => NPlus  (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMinus a b => NMinus (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMult  a b => NMult  (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMin   a b => NMin   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMax   a b => NMax   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  end.

(* No natvars used in vector expressions *)
Definition VExpr_natvar_subst
         {n:nat}
         (name: nat)
         (value: NExpr)
         (vexp: VExpr n): VExpr n := vexp.

Fixpoint AExpr_natvar_subst
         (name: nat)
         (value: NExpr)
         (aexp: AExpr): AExpr :=
  match aexp with
  | AVar _ => aexp
  | AConst _ => aexp
  | ANth n ve ne => ANth n (VExpr_natvar_subst name value ve) (NExpr_var_subst name value ne)
  | AAbs x => AAbs (AExpr_natvar_subst name value x)
  | APlus  a b => APlus (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMinus a b => AMinus (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMult  a b => AMult (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMin   a b => AMin (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMax   a b => AMax (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AZless a b => AZless (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  end.

Fixpoint DSHOperator_NVar_subt
         {i o: nat}
         (name: nat)
         (value: NExpr)
         (exp: DSHOperator i o): DSHOperator i o :=
  match exp with
  | @DSHeUnion o be z => @DSHeUnion o (NExpr_var_subst name value be) z
  | @DSHeT i be => @DSHeT i (NExpr_var_subst name value be)
  | @DSHPointwise i f => @DSHPointwise i (AExpr_natvar_subst (name+2)
                                                            (NExpr_var_subst
                                                               name
                                                               (NVar (name+2))
                                                               value)
                                                            f)
  | @DSHBinOp o f => @DSHBinOp o (AExpr_natvar_subst (name+3)
                                                    (NExpr_var_subst
                                                       name
                                                       (NVar (name+3))
                                                       value)
                                                    f)
  | @DSHInductor ne f initial => @DSHInductor (NExpr_var_subst name value ne)
                                             (AExpr_natvar_subst (name+2)
                                                    (NExpr_var_subst
                                                       name
                                                       (NVar (name+2))
                                                       value)
                                                    f)
                                             initial
  | @DSHIUnion i o n dot initial body =>
    @DSHIUnion i o n
               (AExpr_natvar_subst (name+2)
                                   (NExpr_var_subst
                                      name
                                      (NVar (name+2))
                                      value)
                                   dot)
               initial (DSHOperator_NVar_subt (S name)
                                              (NExpr_var_subst
                                                 name
                                                 (NVar (S name))
                                                 value)
                                              body)
  | @DSHIReduction i o n dot initial body =>
    @DSHIReduction i o n (AExpr_natvar_subst (name+2)
                                       (NExpr_var_subst
                                          name
                                          (NVar (name+2))
                                          value)
                                       dot)
                   initial (DSHOperator_NVar_subt (S name)
                                                  (NExpr_var_subst
                                                     name
                                                     (NVar (S name))
                                                     value)
                                                  body)
  | @DSHCompose i1 o2 o3 f g =>
    @DSHCompose i1 o2 o3
                (DSHOperator_NVar_subt name value f)
                (DSHOperator_NVar_subt name value g)
  | @DSHHTSUMUnion i o dot f g =>
    @DSHHTSUMUnion i o (AExpr_natvar_subst (name+2)
                                           (NExpr_var_subst
                                              name
                                              (NVar (name+2))
                                              value)
                                           dot)
                   (DSHOperator_NVar_subt name value f)
                   (DSHOperator_NVar_subt name value g)
  end.
*)
