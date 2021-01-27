(*
MiniCandid: A formalization of the core ideas of Candid
*)

Require Import FunInd.

Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Operators_Properties.

Require Import Coq.Logic.Decidable.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* Loads the idiosyncratic CaseNames extension *)
Require Import candid.NamedCases.
Set Printing Goal Names. (* Coqide doesn’t use it yet, will be in 8.13 *)

(* Types are coinductive (we do not want to model the graph structure explicilty) *)
CoInductive T :=
  | NatT: T
  | IntT: T
  | NullT : T
  | OptT : T -> T
  | FuncT : T -> T -> T
  | VoidT : T
  | ReservedT : T
  .

(* Some unspecified value representation for references *)
Axiom RefV : Type.

Inductive V :=
  | NatV : nat -> V
  | IntV : Z -> V
  | NullV : V
  | SomeV : V -> V
  | FuncV : RefV -> V
  | ReservedV : V
  .

(* This is a stand in for `null <: t` in places where <: is not allowed yet. *)
Definition is_opt_like_type (t : T) : bool :=
  match t with
  | NullT => true
  | OptT _ => true
  | ReservedT => true
  | _ => false
  end.


Definition is_not_opt_like_value (v : V) : Prop :=
match v with
| NullV => False
| SomeV _ => False
| ReservedV => False
| _ => True
end.

(* The boring, non-subtyping typing relation. *)
Inductive HasType : V -> T -> Prop :=
  | NatHT:
    case natHT,
    forall n, NatV n :: NatT
  | IntHT:
    case intHT,
    forall n, IntV n :: IntT
  | NullHT:
    case nullHT,
    NullV :: NullT
  | NullOptHT:
    case nullOptHT,
    forall t, NullV :: OptT t
  | OptHT:
    case optHT,
    forall v t, v :: t -> SomeV v :: OptT t
  | FuncHT:
    case funcHT,
    forall rv t1 t2, FuncV rv :: FuncT t1 t2
  | ReservedHT:
    case reservedHT,
    ReservedV :: ReservedT
where "v :: t" := (HasType v t).


Reserved Infix "<:" (at level 80, no associativity).
CoInductive Subtype : T -> T -> Prop :=
  | ReflST :
    case reflST,
    forall t, t <: t
  | NatIntST :
    case natIntST,
    NatT <: IntT
  | OptST :
    case optST,
    forall t1 t2,
    t1 <: OptT t2
  | FuncST :
    case funcST,
    forall ta1 ta2 tr1 tr2,
    ta2 <: ta1 ->
    tr1 <: tr2 ->
    FuncT ta1 tr1 <: FuncT ta2 tr2
  | VoidST :
    case voidST,
    forall t, VoidT <: t
  | ReservedST :
    case reservedST,
    forall t, t <: ReservedT
where "t1 <: t2" := (Subtype t1 t2).


Theorem subtyping_refl: reflexive _ Subtype.
Proof. intros x. apply ReflST; constructor. Qed.


Theorem subtyping_trans: transitive _ Subtype.
Proof.
  cofix Hyp.
  intros t1 t2 t3 H1 H2.
  inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
    name_cases;
    try (constructor; firstorder).
Qed.

(*
Subtyping is undecidable, at least the way we model it in Coq.
So let’s pretend it is.
*)
Axiom subtyping_decidable:
  forall t1 t2, {t1 <: t2} + { ~(t1 <: t2) }.
Infix "<:?" := subtyping_decidable (at level 80, no associativity).


Lemma subtype_dec_true:
  forall T t1 t2 (x y : T), t1 <: t2 -> (if t1 <:? t2 then x else y) = x.
Proof. intros. destruct (t1 <:? t2); intuition. Qed.

Lemma subtype_dec_false:
  forall T t1 t2 (x y : T), ~ (t1 <: t2) -> (if t1 <:? t2 then x else y) = y.
Proof. intros. destruct (t1 <:? t2); intuition. Qed.

Lemma subtype_dec_refl:
  forall T t (x y : T), (if t <:? t then x else y) = x.
Proof. intros. apply subtype_dec_true. named_constructor. Qed. 

(*
The spec defines the coercion function as indexed by the subtyping relation.
But that relation is coinductive, so Coq will not allow that.
We thus define the function by recursion on the value.

We use NullV on the RHS of invalid cases.
*)

Function coerce (t1 : T) (t2 : T) (v1 : V) : V :=
  match v1, t1, t2 with
  | NatV n, NatT, NatT => NatV n
  | IntV n, IntT, IntT => IntV n
  | NatV n, NatT, IntT => IntV (Z.of_nat n)
  | FuncV r, FuncT ta1 tr1, FuncT ta2 tr2 => FuncV r

  | SomeV v, OptT t1, OptT t2 =>
    if t1 <:? t2
    then SomeV (coerce t1 t2 v)
    else NullV
  
  (* This is the rule we would like to have, but 
     in order to please the termination checker,
     we have to duplicate all non-opt rules in their opt variant
  | v, t1, OptT t2 =>
    if not (is_opt_like_type t) && t <: t2
    then SomeV (coerce v t1 t2)
  *)
  | NatV n, NatT, OptT NatT => SomeV (NatV n)
  | IntV n, IntT, OptT IntT => SomeV (IntV n)
  | NatV n, NatT, OptT IntT => SomeV (IntV (Z.of_nat n))
  | FuncV r, FuncT ta1 tr1, OptT (FuncT ta2 tr2) =>
    if ta2 <:? ta1
    then if tr1 <:? tr2 then  SomeV (FuncV r) else NullV else NullV

  | v, t, ReservedT => ReservedV

  (* Failure is NullV. This also subsumes “valid” rules for NullV *)
  | _, _, _ => NullV
  end.


(* Let’s try to create a suitable induction principle for this function *)
Lemma coerce_nice_ind:
  forall (P : T -> T -> V -> V -> Prop),
  (case natC, forall n, P NatT NatT (NatV n) (NatV n)) ->
  (case intC, forall n, P IntT IntT (IntV n) (IntV n)) ->
  (case natIntC, forall n, P NatT IntT (NatV n) (IntV (Z.of_nat n))) ->
  (case nullC, P NullT NullT NullV NullV) ->
  (case nullOptC, forall t, P NullT (OptT t) NullV NullV) ->
  (case optNullC, forall t1 t2, P (OptT t1) (OptT t2) NullV NullV) ->
  (case optSomeC, forall t1 t2 v1 v2,
    t1 <: t2 ->
    P t1 t2 v1 v2 ->
    P (OptT t1) (OptT t2) (SomeV v1) (SomeV v2)) ->
  (case opportunisticOptC, forall t1 t2 v1,
    ~ (t1 <: t2) ->
    P (OptT t1) (OptT t2) (SomeV v1) NullV) ->
  (case reservedOptC,
    forall t, P ReservedT (OptT t) ReservedV NullV) ->
  (case constituentOptC,
    forall t1 t2 v1 v2,
    is_opt_like_type t1 = false ->
    is_opt_like_type t2 = false ->
    t1 <: t2 ->
    P t1 t2 v1 v2 ->
    P t1 (OptT t2) v1 (SomeV v2)) ->
  (case opportunisticConstituentOptC,
    forall t1 t2 v1,
    is_opt_like_type t1 = false ->
    is_opt_like_type t2 = true \/ ~ (t1 <: t2) ->
    P t1 (OptT t2) v1 NullV) ->
  (case funcC, forall ta1 tr1 ta2 tr2 v,
    ta2 <: ta1 ->
    tr1 <: tr2 ->
    P (FuncT ta1 tr1) (FuncT ta2 tr2) (FuncV v) (FuncV v)) ->
  (case reservedC, forall t v, v :: t -> P t ReservedT v ReservedV) ->
  (forall t1 t2 v1, t1 <: t2 -> v1 :: t1 -> P t1 t2 v1 (coerce t1 t2 v1)).
Proof.
  intros P.
  intros NatC IntC NatIntC NullC NullOptC OptNullC OptSomeC OpportunisticOptC ReservedOptC ConstituentOptC OpportunisticConstituentOptC FuncC ReservedC.
  intros t1 t2 v1 HST HHT.
  revert t2 HST.
  induction HHT; name_cases.
  [natHT]: {
    intros. 
    inversion HST; subst; clear HST; name_cases.
    [reflST]: { apply NatC; clear_names. }
    [natIntST]: { apply NatIntC; clear_names. }
    [optST]: {
      destruct (is_opt_like_type t0) eqn:His_opt_like.
      * destruct t0; inversion His_opt_like; simpl; clear His_opt_like;
        apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
      * destruct (subtyping_decidable NatT t0).
        + destruct t0; inversion s; subst; clear s; inversion His_opt_like; clear His_opt_like.
          - apply ConstituentOptC; clear_names; simpl; intuition; named_constructor.
          - apply ConstituentOptC; clear_names; simpl; intuition; named_constructor.
        + destruct t0; inversion His_opt_like; clear His_opt_like.
          - contradict n0. named_constructor.
          - contradict n0. named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
    }
    [reservedST]: { apply ReservedC; clear_names. named_constructor. }
  }
  [intHT]: {
    intros. 
    inversion HST; subst; clear HST; name_cases.
    [reflST]: { apply IntC; clear_names. }
    [optST]: {
      destruct (is_opt_like_type t0) eqn:His_opt_like.
      * destruct t0; inversion His_opt_like; simpl; clear His_opt_like;
        apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
      * destruct (subtyping_decidable IntT t0).
        + destruct t0; inversion s; subst; clear s; inversion His_opt_like; clear His_opt_like.
          - apply ConstituentOptC; clear_names; simpl; intuition; named_constructor.
        + destruct t0; inversion His_opt_like; clear His_opt_like.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
          - contradict n0. named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
    }
    [reservedST]: { apply ReservedC; clear_names. named_constructor. }
  }
  [funcHT]: {
    intros. 
    inversion HST; subst; clear HST; name_cases.
    [reflST]: { apply FuncC; clear_names; apply ReflST; clear_names. }
    [optST]: {
      destruct (is_opt_like_type t4) eqn:His_opt_like.
      * destruct t4; inversion His_opt_like; simpl; clear His_opt_like;
        apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
      * destruct (subtyping_decidable (FuncT t1 t2) t4).
        + destruct t4; inversion s; subst; clear s; inversion His_opt_like; clear His_opt_like.
          - simpl. repeat rewrite subtype_dec_refl.
            apply ConstituentOptC; clear_names; simpl; try (intuition;fail).
            ** apply ReflST; clear_names; apply ReflST; clear_names.
            ** apply FuncC; clear_names; apply ReflST; clear_names.
          - simpl. repeat rewrite subtype_dec_true by assumption.
            apply ConstituentOptC; clear_names; simpl; try (intuition;fail).
            named_constructor; assumption.
        + destruct t4; inversion His_opt_like; clear His_opt_like.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
          - simpl.
            destruct (t4_1 <:? t1).
            ** destruct (t2 <:? t4_2).
               ++ contradict n. named_constructor; assumption.
               ++ apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
            ** apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
    }
    [funcST]: { apply FuncC; clear_names; assumption. }
    [reservedST]: { apply ReservedC; clear_names. named_constructor. }
  }
  [nullHT]: {
    intros.
    inversion HST; subst; clear HST; name_cases.
    [reflST]: { apply NullC; clear_names. }
    [optST]: { apply NullOptC; clear_names. }
    [reservedST]: { apply ReservedC; clear_names. named_constructor. }
  }
  [nullOptHT]: {
    intros.
    inversion HST; subst; clear HST; name_cases.
    [reflST]: { apply OptNullC; clear_names. }
    [optST]: { apply OptNullC; clear_names. }
    [reservedST]: { apply ReservedC; clear_names. named_constructor. }
  }
  [optHT]: {
    intros.
    inversion HST; subst; clear HST; name_cases.
    [reflST]: {
      simpl.
      destruct (t <:? t) as [HST | HNoST].
      * apply OptSomeC; clear_names; intuition.
      * contradict HNoST. apply ReflST; clear_names.
    }
    [optST]: {
      simpl. 
      destruct (t <:? t0) as [HST | HNoST].
      * apply OptSomeC; clear_names; intuition.
      * apply OpportunisticOptC; clear_names; intuition.
    }
    [reservedST]: { apply ReservedC; clear_names. named_constructor; assumption. }
  }
  [reservedHT]: { 
    intros.
    inversion HST; subst; clear HST; name_cases.
    [reflST]: { apply ReservedC; clear_names. named_constructor. }
    [optST]: { apply ReservedOptC; clear_names. }
    [reservedST]: { apply ReservedC; clear_names.  named_constructor. }
  }
Qed.

Lemma coerce_roundtrip:
  forall t1 v1,
  v1 :: t1 ->
  coerce t1 t1 v1 = v1.
Proof.
  enough (forall t1 t2 v1,
    t1 <: t2 -> v1 :: t1 -> t2 = t1 ->
    coerce t1 t2 v1 = v1)
    by (intros; apply H; intuition; try apply ReflST; clear_names).
  apply (coerce_nice_ind (fun t1 t2 v1 v2 => t2 = t1 -> v2 = v1));
    intros; name_cases; subst; simpl in *; try solve [congruence].
  [optSomeC]: {apply f_equal. apply H0. congruence. }
  [opportunisticOptC]: {
    inversion H0; subst; clear H0. contradiction H; apply ReflST; clear_names.
  }
  * (* why is this not named? *)
    inversion H; subst; clear H. reflexivity.
Qed.

Lemma coerce_well_defined:
  forall t1 t2 v1,
  t1 <: t2 -> v1 :: t1 ->
  coerce t1 t2 v1 :: t2.
Proof.
  apply coerce_nice_ind with (P := fun t1 t2 v1 v2 => v2 :: t2); intros; name_cases;
     named_constructor; assumption.
Qed.


Lemma is_not_opt_like_type_contravariant:
  forall t1 t2,
  is_opt_like_type t1 = false -> t2 <: t1 -> is_opt_like_type t2 = false.
Proof. intros. destruct t1, t2; easy. Qed.
