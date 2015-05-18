(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import HCOL.

Require Import ArithRing.

Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import Coq.Lists.List.

Global Instance opt_equiv `{Equiv A}: Equiv (option A) :=
  fun a b =>
    match a with
    | None => is_None b
    | Some x => (match b with
                 | None => False
                 | Some y => equiv x y
                 end)
    end.

Global Instance opt_vec_equiv `{Equiv A} {n}: Equiv (vector (option A) n) := Vforall2 (n:=n) opt_equiv.

Fixpoint catSomes {A} {n} (v:vector (option A) n): list A :=
  match v with
  | Vnil => @List.nil A
  | Vcons None _ vs  => catSomes vs
  | Vcons (Some x) _ vs => List.cons x (catSomes vs)
  end.

Module SigmaHCOLOperators.

  (* zero - based, (stride-1) parameter *)
  Program Fixpoint GathH_0 {A} {t:nat} (n s:nat) : vector A ((n*(S s)+t)) -> vector A n :=
    let stride := S s in (
      match n return vector A ((n*stride)+t) -> vector A n with
        | O => fun _ => Vnil
        | S p => fun a => Vcons (Vhead a) (GathH_0 p s (t0:=t) (drop_plus stride a))
      end).
  Next Obligation.
    lia.
  Defined.

  Program Definition GathH {A: Type} (n base stride: nat) {s t} {snz: stride≡S s} (v: vector A (base+n*stride+t)) : vector A n :=
    GathH_0 n s (t0:=t) (drop_plus base v).
  Next Obligation.
    lia.
  Defined.

  Section Coq84Workaround.
    
    (* 
This section is workaround for Coq 8.4 bug in Program construct. under Coq 8.5 
the following definition suffice:

Program Fixpoint ScatHUnion_0 {A} {n:nat} (pad:nat): t A n -> t (option A) ((S pad)*n) :=
  match n return (t A n) -> (t (option A) ((S pad)*n)) with
  | 0 => fun _ => @nil (option A)
  | S p => fun a => cons _ (Some (hd a)) _ (append (const None pad) (ScatHUnion_0 pad (tl a)))
  end.
Next Obligation.
  ring.
Defined.
     *)
    
    Open Scope nat_scope.
    
    Fixpoint ScatHUnion_0 (A:Type) (n:nat) (pad:nat) {struct n}:
      vector A n -> vector (option A) ((S pad)*n).
        refine(
            match n as m return m=n -> _ with
            | O =>  fun _ _ => (fun _ => _) Vnil
            | S p => fun H1 a =>
                       let aa := (fun _ => _) a in
                       let hh := Some (Vhead aa) in
                       let tt := ScatHUnion_0 A p pad (Vtail aa) in
                       let ttt := Vector.append (Vector.const None pad) tt in
                       (fun _ => _) (Vcons hh ttt)
            end
              (eq_refl _)
          );
      try match goal with
          | [ H: ?vector ?t1 ?n1 |- ?vector ?t2 ?n2] => replace n2 with n1 by lia
          end;
      eauto.        
    Defined.
    
    Close Scope nat_scope.
  End Coq84Workaround.
  
  Definition ScatHUnion {A} {n:nat} (base:nat) (pad:nat) (v:vector A n): vector (option A) (base+((S pad)*n)) :=
    Vector.append (Vconst None base) (ScatHUnion_0 A n pad v).
  
End SigmaHCOLOperators.

Import SigmaHCOLOperators.
Require Import HCOLSyntax.

(*
Lemma test `{Equiv A}: @ScatHUnion_0 nat 0 0 Vnil = Vnil.
Proof.
Qed.
 *)

(*
Motivating example:

BinOp(2, Lambda([ r4, r5 ], sub(r4, r5)))

-->

ISumUnion(i3, 2,
  ScatHUnion(2, 1, i3, 1) o
  BinOp(1, Lambda([ r4, r5 ], sub(r4, r5))) o
  GathH(4, 2, i3, 2)
)

*)  


Section OHOperator_language.
  (* ---  An extension of HOperator to deal with missing values. Instead of vector of type 'A' they operate on vectors of 'option A'  --- *)
  
  Inductive OHOperator : nat -> bool -> nat -> bool -> Type :=
  | OHScatHUnion {i} (base pad:nat): OHOperator i false (base+((S pad)*i)) true
  | OHGathH (n base stride: nat) {s t} {snz: stride≡S s}: OHOperator (base+n*stride+t) false n false
  | OHHOperator {i o} (op: HOperator i o): OHOperator i false o false (* cast classic HOperator to  OHOperator *)
  | OHCompose i ifl {t} {tfl} o ofl: OHOperator t tfl o ofl -> OHOperator i ifl t tfl -> OHOperator i ifl o ofl
  | OHOptCast {i}: OHOperator i false i true (* Cast any vector to vector of options *)
  .

End OHOperator_language.  
(*
| SHISumUnion {i o: nat} (r:nat) : OHOperator i false o true -> OHOperator i false o false (* this does not reflect variable substitutuin rules *)
| SHISumUnionG {i o: nat} (r:nat)
               (ogen: forall n:nat, (n < r) -> (OHOperator i false o true))
  : OHOperator i false o false (* operator generator *)
*)

Section SOHOperator_language.
  (* Sigma-HCOL language, introducing even higher level concepts like variables *)
  
  Require Import Coq.Strings.String.
  
  Inductive varname : Type :=
    Var : string → varname.
  
  Global Instance varname_equiv `{Equiv string}: Equiv (varname) :=
    fun a b => match a with
               | Var a => match b with
                          | Var b => equiv a b
                          end
               end.
  
  Inductive aexp : Type :=
  | ANum : nat → aexp
  | AName : varname → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp.
  
  Inductive SHAOperator: aexp -> bool -> aexp -> bool -> Type :=
  | SHAScatHUnion {i o:aexp} (base pad:aexp): SHAOperator i false o true
  | SHAGathH (i n base stride: aexp): SHAOperator i false n false
  (* TODO: all HCOL operators but with aexpes instead of nums *)
  | SHACompose i ifl {t} {tfl} o ofl: SHAOperator t tfl o ofl -> SHAOperator i ifl t tfl -> SHAOperator i ifl o ofl
  | SHAOptCast {i}: SHAOperator i false i true
  | SHAISumUnion {i o: aexp} (v:varname) (r:aexp) : SHAOperator i false o true -> SHAOperator i false o false
  .
  
  Global Instance aexp_equiv `{Equiv nat} `{Equiv varname}: Equiv (aexp).
  Admitted.
  
  End SOHOperator_language.
  
  
  
