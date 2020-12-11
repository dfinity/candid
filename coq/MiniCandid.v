(*
MiniCandid: A formalization of the core ideas of Candid
*)

Require Import FunInd.

Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Operators_Properties.

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
  | VoidT : T
  | ReservedT : T
  .

Inductive V :=
  | NatV : nat -> V
  | IntV : Z -> V
  | NullV : V
  | SomeV : V -> V
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
  | ReservedHT:
    case reservedHT,
    ReservedV :: ReservedT
where "v :: t" := (HasType v t).


Module NoOpportunisticDecoding.

(*
This is the variant without `t <: opt t'`, but with `t <: opt t`.
Here things are simple and inductive.
*)

Reserved Infix "<:" (at level 80, no associativity).
CoInductive Subtype : T -> T -> Prop :=
  | ReflST :
    case reflSL,
    forall t, t <: t
  | NatIntST :
    case natIntSL,
    NatT <: IntT
  | NullOptST :
    case nullOptST,
    forall t, NullT <: OptT t
  | OptST :
    case optST,
    forall t1 t2,
    (* This additional restriction added to fix https://github.com/dfinity/candid/issues/146 *)
    (is_opt_like_type t1 = is_opt_like_type t2) -> 
    t1 <: t2 ->
    OptT t1 <: OptT t2
  | ConstituentOptST :
    case constituentOptST,
    forall t1 t2,
    is_opt_like_type t2 = false ->
    t1 <: t2 -> t1 <: OptT t2
  | VoidST :
    case voidST,
    forall t, VoidT <: t
  | ReservedST :
    case reservedST,
    forall t, t <: ReservedT
where "t1 <: t2" := (Subtype t1 t2).


Reserved Notation "v1 ~> v2 :: t" (at level 80, v2 at level 50, no associativity).
Inductive Coerces : V -> V -> T -> Prop :=
  | NatC: 
    case natC,
    forall n, NatV n ~> NatV n :: NatT
  | IntC:
    case intC,
    forall n, IntV n ~> IntV n :: IntT
  | NatIntC:
    case natIntC,
    forall n i, i = Z.of_nat n -> (NatV n ~> IntV i :: IntT)
  | NullC:
    case nullC,
    NullV ~> NullV :: NullT
  | NullOptC:
    case nullOptC,
    forall t, NullV ~> NullV :: OptT t
  | SomeOptC:
    case someOptC,
    forall v1 v2 t,
    v1 ~> v2 :: t ->
    SomeV v1 ~> SomeV v2 :: OptT t
  | ConstituentOptC:
    case constituentC,
    forall v1 v2 t,
    is_not_opt_like_value v1 ->
    v1 ~> v2 :: t ->
    v1 ~> SomeV v2 :: OptT t
  | ReservedC:
    case reservedC,
    forall v1,
    v1 ~> ReservedV :: ReservedT
where "v1 ~> v2 :: t" := (Coerces v1 v2 t).

Lemma is_opt_like_type_correct:
  forall t,
  is_opt_like_type t = true <-> NullT <: t.
Proof.
  intros. destruct t; simpl; intuition.
  all: try inversion H.
  all: try named_constructor.
Qed.

Theorem coercion_correctness:
  forall v1 v2 t, v1 ~> v2 :: t -> v2 :: t.
Proof.
  intros. induction H; constructor; assumption.
Qed.

Theorem coercion_roundtrip:
  forall v t, v :: t -> v ~> v :: t.
Proof.
  intros. induction H; constructor; intuition.
Qed.

Theorem coercion_uniqueness:
  forall v v1 v2 t, v ~> v1 :: t -> v ~> v2 :: t -> v1 = v2.
Proof.
  intros.
  revert v2 H0.
  induction H; intros v2' Hother;
    try (inversion Hother; subst; clear Hother; try congruence; firstorder congruence).
Qed.

Theorem soundness_of_subtyping:
  forall t1 t2,
  t1 <: t2 ->
  forall v1, v1 :: t1 -> exists v2, v1 ~> v2 :: t2.
Proof.
  intros t1 t2 Hsub v HvT. revert t2 Hsub.
  induction HvT; intros t1 Hsub; inversion Hsub; subst; clear Hsub;
    name_cases;
    try (eexists;constructor; try constructor; fail).
  [natHT_constituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
    - eexists. named_constructor; [constructor|named_constructor].
    - eexists. named_constructor; [constructor|named_constructor;reflexivity].
  }
  [intHT_constituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
    econstructor. named_econstructor; [constructor|named_constructor].
  }
  [optHT_reflSL]: {
    specialize (IHHvT t (ReflST _ _)).
    destruct IHHvT as [v2 Hv2].
    eexists. named_econstructor; try eassumption.
  }
  [optHT_optST]: {
    specialize (IHHvT _ H1).
    destruct IHHvT as [v2 Hv2].
    eexists; named_econstructor; eassumption.
  }
  [optHT_constituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
  }
  [reservedHT_constituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
  }
Qed.

Theorem subtyping_refl: reflexive _ Subtype.
Proof. intros x. apply ReflST; constructor. Qed.

Lemma is_not_opt_like_type_contravariant:
  forall t1 t2,
     is_opt_like_type t1 = false -> t2 <: t1 -> is_opt_like_type t2 = false.
Proof. intros. destruct t1, t2; easy. Qed.

Theorem subtyping_trans: transitive _ Subtype.
Proof.
  cofix Hyp.
  intros t1 t2 t3 H1 H2.
  inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
    name_cases;
    try (constructor; easy).
  [natIntSL_constituentOptST]: {
    named_constructor.
    - assumption.
    - eapply Hyp; [named_econstructor | assumption].
  }
  [optST_optST0]: {
    named_constructor.
    - congruence.
    - eapply Hyp; eassumption.
  }
  [optST_constituentOptST]: {
    inversion H3; subst; clear H3; simpl in H1; congruence.
  }
  [constituentOptST_optST]: {
    named_constructor.
    - congruence.
    - firstorder.
  }
  [constituentOptST_constituentOptST0]: {
    inversion H3; subst; clear H3; try easy.
  }
  [reservedST_constituentOptST]: {
    inversion H0; subst; clear H0; inversion H.
  }
Qed.

End NoOpportunisticDecoding.

Module OpportunisticDecoding.
(*
This is the variant with the opportunistic `t <: opt t'` rule.
*)

Reserved Infix "<:" (at level 80, no associativity).
CoInductive Subtype : T -> T -> Prop :=
  | ReflST :
    case reflSL,
    forall t, t <: t
  | NatIntST :
    case natIntSL,
    NatT <: IntT
  | OptST :
    case optST,
    forall t1 t2,
    t1 <: OptT t2
  | VoidST :
    case voidST,
    forall t, VoidT <: t
  | ReservedST :
    case reservedST,
    forall t, t <: ReservedT
where "t1 <: t2" := (Subtype t1 t2).

(*
The coercion relation is not strictly positive, and thus can’t be an inductive
relations, so we have to implement it as a function that recurses on the value.

This is essentially coercion function, and we can separately try to prove that
it corresponds to the relation.
 *)

Definition recover x := match x with
  | None => Some NullV
  | Some x => Some (SomeV x)
 end.

Function coerce (v1 : V) (t : T) : option V :=
  match v1, t with
  | NatV n, NatT => Some (NatV n)
  | IntV n, IntT => Some (IntV n)
  | NatV n, IntT => Some (IntV (Z.of_nat n))
  | NullV, NullT => Some NullV
  | SomeV v, OptT t => recover (coerce v t)
  
  (* This is the rule we would like to have, but 
     in order to please the termination checker,
     we have to duplicate all non-opt rules in their opt variant
  | v, OptT t =>
    if is_opt_like_type t
    then None
    else option_map SomeV (coerce n v t)
  *)
  | NatV n, OptT NatT => recover (Some (NatV n))
  | IntV n, OptT IntT => recover (Some (IntV n))
  | NatV n, OptT IntT => recover (Some (IntV (Z.of_nat n)))
  (* OptT never fails (this subsumes NullV and ReservedV) *)
  | v, OptT _ => Some NullV

  | v, ReservedT => Some ReservedV
  | v, t => None
  end.
  
Definition Coerces (v1 v2 : V) (t : T) : Prop := coerce v1 t = Some v2.
Notation "v1 ~> v2 :: t" := (Coerces v1 v2 t) (at level 80, v2 at level 50, no associativity).

Definition DoesNotCoerce (v1 : V) (t : T) : Prop := coerce v1 t = None.
Notation "v1 ~/> :: t" := (DoesNotCoerce v1 t) (at level 80, no associativity).

(*
Now we can prove that this indeed implements the inductive relation in the spec:
*)

Lemma NatC: forall n, NatV n ~> NatV n :: NatT.
Proof. intros. reflexivity. Qed.

Lemma IntC: forall n, IntV n ~> IntV n :: IntT.
Proof. intros. reflexivity. Qed.

Lemma NatIntC: forall n i, i = Z.of_nat n -> NatV n ~> IntV i :: IntT.
Proof. intros. subst. reflexivity. Qed.

Lemma NullC: NullV ~> NullV :: NullT.
Proof. intros. reflexivity. Qed.

Lemma NullOptC: forall t, NullV ~> NullV :: OptT t.
Proof. intros. reflexivity. Qed.

Lemma SomeOptC: forall v1 v2 t,
    v1 ~> v2 :: t ->
    SomeV v1 ~> SomeV v2 :: OptT t.
Proof. unfold Coerces. intros. simpl. rewrite H. reflexivity. Qed.

Lemma OpportunisticOptC:
    forall v1 t,
    v1 ~/> :: t ->
    SomeV v1 ~> NullV :: OptT t.
Proof.
  unfold Coerces; unfold DoesNotCoerce. simpl. intros.
  rewrite H; reflexivity.
Qed.

Lemma ReservedOptC:
  forall t, ReservedV ~> NullV :: OptT t.
Proof. intros. reflexivity. Qed.

Lemma ConstituentOptC:
    forall v1 v2 t,
    is_not_opt_like_value v1 ->
    is_opt_like_type t = false ->
    v1 ~> v2 :: t ->
    v1 ~> SomeV v2 :: OptT t.
Proof.
  unfold Coerces. simpl. intros.
  destruct v1, t; simpl in *; try contradiction; try congruence.
Qed.

Lemma OpportunisticConstituentOptC:
    forall v1 t,
    is_not_opt_like_value v1 ->
    is_opt_like_type t = false ->
    v1 ~/> :: t ->
    v1 ~> NullV :: OptT t.
Proof.
  unfold Coerces; unfold DoesNotCoerce. simpl. intros.
  destruct v1, t; simpl in *; try contradiction; try congruence.
Qed.

Lemma ReservedC: forall v, v ~> ReservedV :: ReservedT.
Proof. unfold Coerces. intros. destruct v; reflexivity. Qed.

(*
Now the induction theorem. As always, ugly and bit.
Note that negative assumptions don’t give you a P predicate.
*)

Lemma Coerces_ind:
  forall P,
  (case natC, forall n, P (NatV n) (NatV n) NatT) ->
  (case intC, forall n, P (IntV n) (IntV n) IntT) ->
  (case natIntC, forall n, P (NatV n) (IntV (Z.of_nat n)) IntT) ->
  (case nullC, P NullV NullV NullT) ->
  (case nullOptC, forall t, P NullV  NullV (OptT t)) ->
  (case someOptC, forall v1 v2 t,
    v1 ~> v2 :: t -> P v1 v2 t -> P (SomeV v1) (SomeV v2) (OptT t)) ->
  (case opportunisticOptC,
      forall v1 t, v1 ~/> :: t -> P (SomeV v1) NullV (OptT t)) ->
  (case reservedOptC,
    forall t, P ReservedV NullV (OptT t)) ->
  (case constituentOptC,
    forall v1 v2 t,
    is_not_opt_like_value v1 ->
    is_opt_like_type t = false ->
    v1 ~> v2 :: t ->
    P v1 v2 t -> 
    P v1 (SomeV v2) (OptT t)) ->
  (case opportunisticConstituentOptC,
    forall v1 t,
    is_not_opt_like_value v1 ->
    is_opt_like_type t = true \/ v1 ~/> :: t ->
    P v1 NullV (OptT t)) ->
  (case reservedC, forall v, P v ReservedV ReservedT) ->
  (forall v1 v2 t, v1 ~> v2 :: t -> P v1 v2 t).
Proof.
  unfold Coerces. unfold DoesNotCoerce.
  intros P NatC IntC NatIntC NullC NullOptC SomeOptC OpportunisticOptC ReservedOptC ConstituentOptC OpportunisticConstituentOptC ReservedC v1.
  induction v1; intros v2 t Hcoerces; destruct t.
  all: try (inversion Hcoerces; subst; clear Hcoerces; intuition; fail). 
  all: simpl in Hcoerces.
  * destruct t;
    inversion Hcoerces; subst; clear Hcoerces.
    + apply ConstituentOptC; clear_names; simpl; intuition.
    + apply ConstituentOptC; clear_names; simpl; intuition.
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition.
  * destruct t;
    inversion Hcoerces; subst; clear Hcoerces.
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition. 
    + apply ConstituentOptC; clear_names; simpl; intuition.
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition. 
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition. 
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition. 
    + apply OpportunisticConstituentOptC; clear_names; simpl; intuition. 
  * destruct (coerce v1 t) eqn:Heq; simpl in Hcoerces;
    inversion Hcoerces; subst; clear Hcoerces.
    + apply SomeOptC; clear_names; intuition.
    + apply OpportunisticOptC; clear_names; easy.
Qed.

Lemma is_opt_like_type_correct:
  forall t,
  is_opt_like_type t = true <-> NullT <: t.
Proof.
  intros. destruct t; simpl; intuition.
  all: try inversion H.
  all: try named_constructor.
Qed.

Theorem coercion_correctness:
  forall v1 v2 t, v1 ~> v2 :: t -> v2 :: t.
Proof.
  intros.
  revert v2 t H.
  induction v1;
  intros v2 t Hcoerce;
    unfold Coerces in Hcoerce;
    functional inversion Hcoerce; simpl in *; subst; clear Hcoerce;
    try (named_constructor; named_constructor; fail).
  * destruct (coerce v1 t1) eqn:Heq; simpl in *; inversion H0; subst; clear H0.
    - specialize (IHv1 _ _ Heq).
      named_constructor; assumption. 
    - named_constructor.
Qed.

Theorem coercion_roundtrip:
  forall v t, v :: t -> v ~> v :: t.
Proof.
  intros.
  induction H; try reflexivity.
  * unfold Coerces in *. simpl. rewrite IHHasType. reflexivity.
Qed.

Theorem coercion_uniqueness:
  forall v v1 v2 t, v ~> v1 :: t -> v ~> v2 :: t -> v1 = v2.
Proof.
  intro v.
  induction v; intros v1 v2 t Heq1 Heq;
    unfold Coerces in *;
    congruence.
Qed.

Theorem soundness_of_subtyping:
  forall t1 t2,
  t1 <: t2 ->
  forall v1, v1 :: t1 -> exists v2, v1 ~> v2 :: t2.
Proof.
  intros t1 t2 Hsub v HvT. revert t2 Hsub.
  induction HvT; intros t1 Hsub; inversion Hsub; subst; clear Hsub;
    name_cases;
    try (eexists;reflexivity).
  Show Existentials.
  [natHT_optST]: {
    destruct t2; eexists; reflexivity.
  }
  [intHT_optST]: {
    destruct t2; eexists; reflexivity.
  }
  [optHT_reflSL]: {
    specialize (IHHvT t (ReflST _ _)).
    destruct IHHvT as [v2 Hv2].
    eexists. unfold Coerces in *. simpl. rewrite Hv2. reflexivity.
  }
  [optHT_optST]: {
    unfold Coerces. simpl.
    destruct (coerce v t2) eqn:Heq; eexists; reflexivity.
  }
Qed.

Theorem subtyping_refl: reflexive _ Subtype.
Proof. intros x. apply ReflST; constructor. Qed.

Lemma is_not_opt_like_type_contravariant:
  forall t1 t2,
  is_opt_like_type t1 = false -> t2 <: t1 -> is_opt_like_type t2 = false.
Proof. intros. destruct t1, t2; easy. Qed.

Theorem subtyping_trans: transitive _ Subtype.
Proof.
  cofix Hyp.
  intros t1 t2 t3 H1 H2.
  inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
    name_cases;
    try (constructor; easy).
Qed.

End OpportunisticDecoding.