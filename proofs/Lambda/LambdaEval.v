Require Import Helix.Lambda.LambdaDef.

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Lists.ListSet.

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.Misc.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

(* Variable bindings *)
Record LState :=
  mkLState {
      getN: varname nat -> option nat;
      getA: varname CarrierA -> option CarrierA;
      getV {n:nat}: varname (avector n) -> option (avector n)
    }.

Global Instance LState_Equiv: Equiv (LState)
  := fun x y =>
       (getN x = getN y) /\
       (getA x = getA y) /\
       (forall n, @getV x n = @getV y n).

Global Instance getN_proper:
  Proper ((=) ==> (=) ==> (=)) getN.
Proof.
  intros s s' Es v v' Ev.
  inversion Es.
  inversion_clear Ev.
  auto.
Qed.

Global Instance getA_proper:
  Proper ((=) ==> (=) ==> (=)) getA.
Proof.
  intros s s' Es v v' Ev.
  inversion Es as [A [B C]].
  auto.
Qed.

Global Instance getV_proper:
  Proper ((=) ==> forall_relation (λ n : nat, (=) ==> (=))) getV.
Proof.
  intros s s' Es n v v' Ev.
  inversion Es as [A [B C]].
  inversion_clear Ev.
  specialize (C n).
  auto.
Qed.

Definition empty_LState: LState :=
  mkLState
    (Basics.const None)
    (Basics.const None)
    (fun n _ => None).

(* State update for `nat` *)
Definition putN (x:varname nat) (n:nat) (st:LState) : LState :=
  {|
    getN x' := if eq_varname_dec x x' then Some n else getN st x' ;
    getA := getA st ;
    getV := @getV st
  |}.

(* State update for `CarrierA` *)
Definition putA (x:varname CarrierA) (n:CarrierA) (st:LState): LState :=
  {|
    getN := getN st ;
    getA x' := if eq_varname_dec x x' then Some n else getA st x' ;
    getV := @getV st
  |}.

Global Instance putN_proper:
  Proper ((=) ==> (=) ==> (=) ==> (=)) putN.
Proof.
  intros x x' Ex n n' En s s' Es.
  unfold putN, equiv, LState_Equiv; simpl.
  repeat split.
  -
    intros y y' Ey.
    repeat break_if; subst.
    +
      some_apply.
    +
      unfold equiv, LState_Equiv in Es.
      destruct Es as [A [B C]].
      destruct Heqd, Heqd0.
      congruence.
    +
      unfold equiv, LState_Equiv in Es.
      destruct Es as [A [B C]].
      destruct Heqd, Heqd0.
      congruence.
    +
      f_equiv; auto.
  -
    f_equiv; auto.
  -
    intros n0.
    apply getV_proper; auto.
Qed.

Global Instance putA_proper:
  Proper ((=) ==> (=) ==> (=) ==> (=)) putA.
Proof.
  simpl_relation.
  repeat split.
  -
    apply getN_proper, H1.
  -
    unfold equiv, ext_equiv, respectful.
    intros.
    rewrite H, H2.
    break_if.
    + some_apply.
    + apply getA_proper; auto.
  -
    intros n.
    apply getV_proper, H1.
Qed.

(* State update for `avector n` *)
Definition putV {n:nat} (x:varname (avector n)) (v: avector n) (st:LState) : LState :=
  {|
    getN := getN st;
    getA := getA st;
    getV := fun (n' : nat) (x' : varname (vector CarrierA n')) =>
              match eq_nat_dec n n' with
              | left E =>
                let x'' := (match E in  _ ≡ p return varname (vector CarrierA p) with | eq_refl => x end) in
                if eq_varname_dec x' x'' then
                  Some (match E in  _ ≡ p return avector p with | eq_refl => v end)
                else
                  @getV st n' x'
              | in_right => @getV st n' x'
              end
  |}.

Definition evalVexp (st:LState) {n} (e:VExpr n): option (avector n) :=
  match e with
  | VVar v => getV st v
  | VConst x => Some x
  end.

Fixpoint evalNexp (st:LState) (e:NExpr): option nat :=
  match e with
  | NVar v => getN st v
  | NConst c => Some c
  | NDiv a b => liftM2 Nat.div (evalNexp st a) (evalNexp st b)
  | NMod a b => liftM2 Nat.modulo (evalNexp st a) (evalNexp st b)
  | NPlus a b => liftM2 plus (evalNexp st a) (evalNexp st b)
  | NMinus a b => liftM2 minus (evalNexp st a) (evalNexp st b)
  | NMult a b => liftM2 mult (evalNexp st a) (evalNexp st b)
  | NMin a b => liftM2 min (evalNexp st a) (evalNexp st b)
  | NMax a b => liftM2 max (evalNexp st a) (evalNexp st b)
  end.

Fixpoint evalAexp (st:LState) (e:AExpr): option CarrierA :=
  match e with
  | AVar v => getA st v
  | AConst x => Some x
  | AAbs x =>  liftM abs (evalAexp st x)
  | APlus a b => liftM2 plus (evalAexp st a) (evalAexp st b)
  | AMult a b => liftM2 mult (evalAexp st a) (evalAexp st b)
  | AMin a b => liftM2 min (evalAexp st a) (evalAexp st b)
  | AMax a b => liftM2 max (evalAexp st a) (evalAexp st b)
  | AMinus a b =>
    a' <- (evalAexp st a) ;;
       b' <- (evalAexp st b) ;;
       ret (plus a' (negate b'))
  | @ANth n v i =>
    v' <- (evalVexp st v) ;;
       i' <- (evalNexp st i) ;;
       match Compare_dec.lt_dec i' n with
       | left ic => Some (Vnth v' ic)
       | in_right => None
       end
  | AZless a b => liftM2 Zless (evalAexp st a) (evalAexp st b)
  end.

Global Instance LState_equivalence : Equivalence LState_Equiv.
Proof.
  split.
  -
    intros x.
    induction x.
    repeat split; simpl;reflexivity.
  -
    intros x y [E1 [E2 E3]].
    destruct x,y;
      repeat split; simpl in *.
    + auto.
    +
      symmetry.
      auto.
    +
      intros n.
      specialize (E3 n).
      auto.
  -
    intros x y z [Exy1 [Exy2 Exy3]] [Eyz1 [Eyz2 Eyz3]].
    destruct x,y,z;
      repeat split; simpl in *.
    +
      auto.
    +
      auto.
    +
      intros n.
      specialize (Exy3 n).
      specialize (Eyz3 n).
      auto.
Qed.

Global Instance evalVexpr_proper:
  Proper ((=) ==> forall_relation (λ n, (=) ==> (=))) evalVexp.
Proof.
  intros s s' Es n a a' Ea.
  induction a, a'; try inversion Ea; crush.
Qed.

Global Instance evalNexpr_proper:
  Proper ((=) ==> (=) ==> (=)) evalNexp.
Proof.
  intros s s' Es e e' Ee.
  unfold equiv, NExpr_Equiv in Ee.
  rewrite <- Ee. clear Ee e'.

  induction e; simpl; try reflexivity;
    repeat break_match; try some_none_contradiction; try reflexivity; f_equiv;
      repeat some_inv; try rewrite IHe1; try rewrite IHe2; auto.
Qed.

Global Instance evalAexpr_proper:
  Proper ((=) ==> (=) ==> (=)) evalAexp.
Proof.
  intros s s' Es a a' Ea.
  induction Ea; simpl.
  -
    rewrite Es,H; reflexivity.
  -
    f_equiv; auto.
  -
    assert (EF: evalNexp s i = evalNexp s' i')
      by (apply evalNexpr_proper; auto).
    assert (EV: evalVexp s v = evalVexp s' v')
      by (apply evalVexpr_proper; auto).
    repeat break_match; try reflexivity; try inversion EF; try inversion EV; try congruence.
    f_equiv.
    apply VecSetoid.Vnth_equiv; auto.
  -
    repeat break_match; subst; try inversion IHEa; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa.
    rewrite IHEa.
    reflexivity.
  -
    repeat break_match; subst; try inversion IHEa1;try inversion IHEa2; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa1.
    apply Some_inj_equiv in IHEa2.
    rewrite IHEa1, IHEa2.
    reflexivity.
  -
    repeat break_match; subst; try inversion IHEa1;try inversion IHEa2; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa1.
    apply Some_inj_equiv in IHEa2.
    rewrite IHEa1, IHEa2.
    reflexivity.
  -
    repeat break_match; subst; try inversion IHEa1;try inversion IHEa2; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa1.
    apply Some_inj_equiv in IHEa2.
    rewrite IHEa1, IHEa2.
    reflexivity.
  -
    repeat break_match; subst; try inversion IHEa1;try inversion IHEa2; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa1.
    apply Some_inj_equiv in IHEa2.
    rewrite IHEa1, IHEa2.
    reflexivity.
  -
    repeat break_match; subst; try inversion IHEa1;try inversion IHEa2; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa1.
    apply Some_inj_equiv in IHEa2.
    rewrite IHEa1, IHEa2.
    reflexivity.
  -
    repeat break_match; subst; try inversion IHEa1;try inversion IHEa2; try reflexivity.
    f_equiv.
    apply Some_inj_equiv in IHEa1.
    apply Some_inj_equiv in IHEa2.
    rewrite IHEa1, IHEa2.
    reflexivity.
Qed.

Section Wrappers.

  Inductive UnNat: Type :=
  | mkUnNat: varname nat → NExpr → UnNat.

  Inductive UnCarrierA : Type :=
  | mkUnCarrierA: varname CarrierA -> AExpr -> UnCarrierA.

  Inductive IUnCarrierA: nat -> Type :=
  | mkIUnCarrierA {n}: varname nat → varname CarrierA -> AExpr → IUnCarrierA n.

  Inductive BinCarrierA : Type :=
  | mkBinCarrierA: forall va vb : varname CarrierA, va ≠ vb -> AExpr -> BinCarrierA.

  Inductive IBinCarrierA: nat -> Type :=
  | mkIBinCarrierA {n}: varname nat ->
                        forall va vb : varname CarrierA, va ≠ vb → AExpr → IBinCarrierA n.

  Inductive IBinCarrierA_α_equiv: forall n, IBinCarrierA n -> IBinCarrierA n -> Prop :=
  | mkIBinCarrierA_α_equiv
      {n: nat}
      {vi vi': varname nat}
      {va va' vb vb': varname CarrierA}
      {vab: va ≠ vb} {va'b': va' ≠ vb'}
      {vba': vb ≠ va'} {vab': va ≠ vb'}
      {body body': AExpr}
    :
      let abound: varset CarrierA := set_add eq_varname_dec va' (set_add eq_varname_dec vb'
                                                                         (empty_set (varname CarrierA)))  in
      let nbound: varset nat := set_add eq_varname_dec vi'  (empty_set (varname nat)) in
      body = AExpr_avar_subst abound va' va (AExpr_avar_subst abound vb' vb (AExpr_natvar_subst nbound vi' vi body')) ->
      IBinCarrierA_α_equiv n (mkIBinCarrierA vi va vb vab body) (mkIBinCarrierA vi' va' vb' va'b' body').

  Definition evalUnNat (st:LState) (f:UnNat) :=
    match f with
    | mkUnNat v nexp => fun x => evalNexp (putN v x st) nexp
    end.

  Definition evalUnCarrierA (st:LState) (f: UnCarrierA) :=
    match f with
    | mkUnCarrierA va aexp => fun x => evalAexp (putA va x st) aexp
    end.

  Definition evalIUnCarrierA {n:nat} (st:LState) (f:IUnCarrierA n) :=
    match f with
    | mkIUnCarrierA vi va aexp => fun (i:FinNat n) a =>
                                   evalAexp (putN vi (proj1_sig i) (putA va a st)) aexp
    end.

  Global Instance IUnCarrierA_Equiv {n: nat}: Equiv (@IUnCarrierA n)
    := fun a b => forall st, evalIUnCarrierA st a = evalIUnCarrierA st b.

  Global Instance evalIUnCarrierA_proper {n:nat}:
    Proper ( (=) ==> (=) ==> (=)) (@evalIUnCarrierA n).
  Proof.
    intros s s' Es a a' Ea.
    unfold equiv, IUnCarrierA_Equiv in Ea.
    rewrite Ea. clear a Ea.
    unfold evalIUnCarrierA.
    repeat break_match.
    intros i i' Ei.
    intros b b' Eb.
    repeat f_equiv; auto.
  Qed.

  Global Instance evalIUnCarrierA_arg_proper {n:nat} (st:LState) (f:IUnCarrierA n):
    Proper ((=) ==> (=)) (@evalIUnCarrierA n st f).
  Proof.
    intros i i' Ei.
    unfold evalIUnCarrierA.
    repeat break_match.
    intros b b' Eb.
    repeat f_equiv; auto.
  Qed.

  Global Instance IUnCarrierA_Equivalence {n}: Equivalence (@IUnCarrierA_Equiv n).
  Proof.
    split.
    -
      intros f s x x' E.
      rewrite_clear E. clear x.
      intros a a' Ea.
      rewrite_clear Ea.
      auto.
    -
      intros f f' Ef st.
      unfold IUnCarrierA_Equiv in *.
      symmetry.
      apply Ef.
    -
      intros x y z Exy Eyz.
      unfold IUnCarrierA_Equiv in *.
      intros st.
      rewrite Exy, Eyz; clear Exy Eyz x y.
      intros a a' Ea.
      rewrite_clear Ea. clear a.

      unfold evalIUnCarrierA.
      repeat break_match.
      intros b b' Eb.
      repeat f_equiv; auto.
  Qed.

  Definition evalBinCarrierA (st:LState) (f: BinCarrierA) :=
    match f with
    | mkBinCarrierA va vb H aexp => fun a b => evalAexp (putA vb b (putA va a st )) aexp
    end.

  Definition evalIBinCarrierA {n} (st:LState) (f: IBinCarrierA n) :=
    match f with
    | mkIBinCarrierA vi va vb H aexp => fun (i:FinNat n) a b
                                       => evalAexp (putN vi (proj1_sig i) (putA vb b (putA va a st ))) aexp
    end.

  Global Instance BinCarrierA_Equiv: Equiv BinCarrierA
    := fun a b => forall st, evalBinCarrierA st a = evalBinCarrierA st b.

  Global Instance evalBinCarrierA_proper:
    Proper ( (=) ==> (=) ==> (=)) evalBinCarrierA.
  Proof.
    intros s s' Es x y Exy.
    unfold equiv, BinCarrierA_Equiv in Exy.
    rewrite Exy; clear x Exy.
    unfold evalBinCarrierA.
    repeat break_match.
    rename a into e.
    intros a a' Ea.
    intros b b' Eb.
    repeat f_equiv; auto.
  Qed.

  Global Instance evalBinCarrierA_arg_proper (st:LState) (f:BinCarrierA):
    Proper ( (=) ==> (=)) (@evalBinCarrierA st f).
  Proof.
    intros a a' Ea b b' Eb.
    unfold evalBinCarrierA.
    repeat break_match.
    rename a into e.
    repeat f_equiv; auto.
  Qed.

  Global Instance BinCarrierA_Equivalence: Equivalence BinCarrierA_Equiv.
  Proof.
    split.
    -
      intros f s x x' E.
      rewrite_clear E. clear x.
      intros a a' Ea.
      rewrite_clear Ea.
      unfold evalBinCarrierA.
      repeat break_match.
      repeat f_equiv; auto.
    -
      intros f f' Ef st.
      unfold BinCarrierA_Equiv in *.
      symmetry.
      apply Ef.
    -
      intros x y z Exy Eyz.
      unfold BinCarrierA_Equiv in *.
      intros st.
      rewrite Exy, Eyz; clear Exy Eyz x y.
      intros a a' Ea.
      rewrite_clear Ea. clear a.

      unfold evalBinCarrierA.
      repeat break_match.
      rename a into e, a' into i'.
      intros b b' Eb.
      repeat f_equiv; auto.
  Qed.

  Global Instance IBinCarrierA_Equiv {n: nat}: Equiv (@IBinCarrierA n)
    := fun a b => forall st, evalIBinCarrierA st a = evalIBinCarrierA st b.

  Global Instance evalIBinCarrierA_proper {n:nat}:
    Proper ( (=) ==> (=) ==> (=)) (@evalIBinCarrierA n).
  Proof.
    intros s s' Es x y Exy.
    unfold equiv, IBinCarrierA_Equiv in Exy.
    rewrite Exy; clear x Exy.
    unfold evalIBinCarrierA.
    repeat break_match.
    rename a into e.
    intros i i' Ei.
    intros a a' Ea.
    intros b b' Eb.
    repeat f_equiv; auto.
  Qed.

  Global Instance evalIBinCarrierA_arg_proper {n:nat} (st:LState) (f:IBinCarrierA n):
    Proper ((=) ==> (=)) (@evalIBinCarrierA n st f).
  Proof.
    intros i i' Ei.
    unfold evalIBinCarrierA.
    repeat break_match.
    rename a into e.
    intros b b' Eb a a' Ea.
    repeat f_equiv; auto.
  Qed.

  Global Instance IBinCarrierA_Equivalence {n}: Equivalence (@IBinCarrierA_Equiv n).
  Proof.
    split.
    -
      intros f s x x' E.
      rewrite_clear E. clear x.
      intros a a' Ea.
      rewrite_clear Ea.
      unfold evalIBinCarrierA.
      repeat break_match.
      intros b b' Eb.
      repeat f_equiv; auto.

    -
      intros f f' Ef st.
      unfold IBinCarrierA_Equiv in *.
      symmetry.
      apply Ef.
    -
      intros x y z Exy Eyz.
      unfold IBinCarrierA_Equiv in *.
      intros st.
      rewrite Exy, Eyz; clear Exy Eyz x y.
      intros a a' Ea.
      rewrite_clear Ea. clear a.

      unfold evalIBinCarrierA.
      repeat break_match.
      rename a into e, a' into i'.
      intros a a' Ea b b' Eb.
      repeat f_equiv; auto.
  Qed.

  Global Instance UnNat_Equiv: Equiv (UnNat)
    := fun a b => forall st, evalUnNat st a = evalUnNat st b.

  Global Instance evalUnNat_proper:
    Proper ((=) ==> (=) ==> (=)) (evalUnNat).
  Proof.
    intros s s' Es f f' Ef.
    unfold equiv, UnNat_Equiv in Ef.
    unfold evalUnNat in *.
    repeat break_match.
    subst.
    equiv_extensionality j j' Ej.
    rewrite <- Es; clear s' Es.
    apply Ef, Ej.
  Qed.

  Global Instance UnNat_Equivalence: Equivalence (UnNat_Equiv).
  Proof.
    split.
    -
      intros f s x x' E.
      rewrite E.
      reflexivity.
    -
      intros f f' Ef st.
      unfold UnNat_Equiv in *.
      symmetry.
      apply Ef.
    -
      intros x y z Exy Eyz.
      unfold UnNat_Equiv in *.
      intros st.
      rewrite Exy, Eyz.
      reflexivity.
  Qed.

  Definition CastIBinCarrierA {m n:nat} (mn: m<=n)
             (f:IBinCarrierA n):  IBinCarrierA m :=
    match f  with
    | @mkIBinCarrierA _ vi va vb vab a =>  @mkIBinCarrierA m vi va vb vab a
    end.

End Wrappers.

Section Alpha_Equivalence.

  Inductive UnNat_α_equiv: UnNat -> UnNat -> Prop :=
  | mkUnNat_α_equiv (k k': varname nat) (nexp nexp': NExpr):
      (* Q: do we need bounding sets here at all? *)
      let nbound: varset nat := set_add eq_varname_dec k  (empty_set (varname nat)) in
      let nbound': varset nat := set_add eq_varname_dec k'  (empty_set (varname nat)) in
      let w := max (free_natvar nexp) (free_natvar nexp') in
      NExpr_natvar_subst nbound k w nexp = NExpr_natvar_subst nbound' k' w nexp' ->
      UnNat_α_equiv (mkUnNat k nexp) (mkUnNat k' nexp').

  Inductive IUnCarrierA_α_equiv: forall n, IUnCarrierA n -> IUnCarrierA n -> Prop :=
  | mkIUnCarrierA_α_equiv
      {n: nat}
      (vi vi': varname nat)
      (va va': varname CarrierA)
      (aexp aexp': AExpr) :
      let abound: varset CarrierA := set_add eq_varname_dec va'  (empty_set (varname CarrierA)) in
      let nbound: varset nat := set_add eq_varname_dec vi'  (empty_set (varname nat)) in
      aexp = AExpr_avar_subst abound va' va (AExpr_natvar_subst nbound vi' vi aexp') ->
      IUnCarrierA_α_equiv n (mkIUnCarrierA vi va aexp) (mkIUnCarrierA vi' va' aexp').

  Inductive BinCarrierA_α_equiv: BinCarrierA -> BinCarrierA -> Prop :=
  | mkBinCarrierA_α_equiv
      {va va' vb vb': varname CarrierA}
      {vab: va ≠ vb} {va'b': va' ≠ vb'}
      {vba': vb ≠ va'} {vab': va ≠ vb'}
      {aexp aexp': AExpr}
    :
      let abound: varset CarrierA := set_add eq_varname_dec va' (set_add eq_varname_dec vb'
                                                                         (empty_set (varname CarrierA)))  in
      aexp = AExpr_avar_subst abound va' va (AExpr_avar_subst abound vb' vb aexp') ->
      BinCarrierA_α_equiv (mkBinCarrierA va vb vab aexp) (mkBinCarrierA va' vb' va'b' aexp').

  Definition BinCarrierA_natvar_subst
             (nbound: varset nat)
             (k k': varname nat)
             (dot: BinCarrierA): BinCarrierA :=
    match dot with
    | mkBinCarrierA va vb vd aexp =>
      let nbound: varset nat := set_add eq_varname_dec k'  nbound in
      mkBinCarrierA va vb vd (AExpr_natvar_subst nbound k k' aexp)
    end.

  Definition IBinCarrierA_natvar_subst
             {n: nat}
             (nbound: varset nat)
             (k k': varname nat)
             (dot: IBinCarrierA n): IBinCarrierA n :=
    match dot in IBinCarrierA n' return (n≡n') -> IBinCarrierA n with
    | @mkIBinCarrierA n vi va vb vab aexp =>
      fun _ =>
        let nbound' := set_add eq_varname_dec vi nbound in
        @mkIBinCarrierA _ vi va vb vab (AExpr_natvar_subst nbound' k k' aexp)
    end (eq_refl).

  Definition IUnCarrierA_natvar_subst
             {n:nat}
             (nbound: varset nat)
             (k k': varname nat)
             (dot:  IUnCarrierA n): IUnCarrierA n :=
    match dot in IUnCarrierA n' return (n≡n') -> IUnCarrierA n with
    | @mkIUnCarrierA n vi va aexp =>
      fun _ =>
        let nbound' := set_add eq_varname_dec vi nbound in
        @mkIUnCarrierA _ vi va (AExpr_natvar_subst nbound' k k' aexp)
    end (eq_refl).

  (* UnCarrierA does not use natvars. *)
  Definition UnCarrierA_natvar_subst
             (nbound: varset nat)
             (k k': varname nat):
    UnCarrierA -> UnCarrierA := id.

  Definition UnNat_natvar_subst
             (nbound: varset nat)
             (k k': varname nat)
             (dot:  UnNat): UnNat :=
    match dot with
    | mkUnNat vi nexp =>
      let nbound' := set_add eq_varname_dec vi nbound in
      mkUnNat vi (NExpr_natvar_subst nbound' k k' nexp)
    end.

End Alpha_Equivalence.
