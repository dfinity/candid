(*
MiniCandid: A formalization of the core ideas of Candid
*)

Require Import Coq.ZArith.BinInt.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Operators_Properties.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Require Import candid.NamedCases.

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

Definition is_not_opt_like_type (t : T) : Prop :=
  match t with
  | NullT => False
  | OptT _ => False
  | ReservedT => False
  | _ => True
  end.

Reserved Infix "<:" (at level 80, no associativity).
CoInductive Subtype : T -> T -> Prop :=
  | ReflST :
    forall Case_ReflSL : CaseName,
    forall t, t <: t
  | NatIntST :
    forall Case_NatIntSL : CaseName,
    NatT <: IntT
  | NullOptST :
    forall Case_NullOptST : CaseName,
    forall t, NullT <: OptT t
  | OptST :
    forall Case_OptST : CaseName,
    forall t1 t2,
    (* This additional restriction added to fix https://github.com/dfinity/candid/issues/146 *)
    (is_not_opt_like_type t1 <-> is_not_opt_like_type t2) -> 
    t1 <: t2 ->
    OptT t1 <: OptT t2
  | ConstituentOptST :
    forall Case_ConstituentOptST : CaseName,
    forall t1 t2,
    is_not_opt_like_type t2 ->
    t1 <: t2 -> t1 <: OptT t2
  | VoidST :
    forall Case_VoidST : CaseName,
    forall t, VoidT <: t
  | ReservedST :
    forall Case_ReservedST : CaseName,
    forall t, t <: ReservedT
where "t1 <: t2" := (Subtype t1 t2).

Inductive HasType : V -> T -> Prop :=
  | NatHT:
    forall Case_NatHT : CaseName,
    forall n, NatV n :: NatT
  | IntHT:
    forall Case_IntHT : CaseName,
    forall n, IntV n :: IntT
  | NullHT:
    forall Case_NullHT : CaseName,
    NullV :: NullT
  | NullOptHT:
    forall Case_NullOptHT : CaseName,
    forall t, NullV :: OptT t
  | OptHT:
    forall Case_OptHT : CaseName,
    forall v t, v :: t -> SomeV v :: OptT t
  | ReservedHT:
    forall Case_ReservedHT : CaseName,
    ReservedV :: ReservedT
where "v :: t" := (HasType v t).

Definition is_not_opt_like_value (v : V) : Prop :=
  match v with
  | NullV => False
  | SomeV _ => False
  | ReservedV => False
  | _ => True
  end.


Reserved Notation "v1 ~> v2 :: t" (at level 80, v2 at level 50, no associativity).
Inductive Coerces : V -> V -> T -> Prop :=
  | NatC: 
    forall Case_NatC : CaseName,
    forall n, (NatV n ~> NatV n :: NatT)
  | IntC:
    forall Case_IntC : CaseName,
    forall n, (IntV n ~> IntV n :: IntT)
  | NatIntC:
    forall Case_NatIntC : CaseName,
    forall n i, i = Z.of_nat n -> (NatV n ~> IntV i :: IntT)
  | NullC:
    forall Case_NullC : CaseName,
    NullV ~> NullV :: NullT
  | NullOptC:
    forall Case_NullOptC : CaseName,
    forall t, NullV ~> NullV :: OptT t
  | SomeOptC:
    forall Case_SomeOptC : CaseName,
    forall v1 v2 t, v1 ~> v2 :: t -> SomeV v1 ~> SomeV v2 :: OptT t
  | ConstituentOptC:
    forall Case_ConstituentC : CaseName,
    forall v1 v2 t,
    is_not_opt_like_value v1 ->
    v1 ~> v2 :: t ->
    v1 ~> SomeV v2 :: OptT t
  | ReservedC:
    forall Case_ReservedC : CaseName,
    forall v1,
    v1 ~> ReservedV :: ReservedT
where "v1 ~> v2 :: t" := (Coerces v1 v2 t).

(* The is_not_opt_like_type definition is only introduced because
   Coq (and not only coq) does not like hyptheses like ~(null <: t)
*)
Lemma is_not_opt_like_type_correct:
  forall t,
  is_not_opt_like_type t <-> ~ (NullT <: t).
Proof.
  intros. destruct t; simpl; intuition.
  all: try inversion H0; (apply H; named_constructor).
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
  [Case_NatHT_Case_ConstituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
    - eexists. named_constructor; [constructor|named_constructor].
    - eexists. named_constructor; [constructor|named_constructor;reflexivity].
  }
  [Case_IntHT_Case_ConstituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
    econstructor. named_econstructor; [constructor|named_constructor].
  }
  [Case_OptHT_Case_ReflSL]: {
    specialize (IHHvT t (ReflST _ _)).
    destruct IHHvT as [v2 Hv2].
    eexists. named_econstructor; try eassumption.
  }
  [Case_OptHT_Case_OptST]: {
    specialize (IHHvT _ H1).
    destruct IHHvT as [v2 Hv2].
    eexists; named_econstructor; eassumption.
  }
  [Case_OptHT_Case_ConstituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
  }
  [Case_ReservedHT_Case_ConstituentOptST]: {
    inversion H0; subst; clear H0; simpl in H; inversion H.
  }
Qed.

Theorem subtyping_refl: reflexive _ Subtype.
Proof. intros x. apply ReflST; constructor. Qed.

Lemma is_not_opt_like_type_contravariant:
  forall t1 t2,
     is_not_opt_like_type t1 -> t2 <: t1 -> is_not_opt_like_type t2.
Proof. intros. destruct t1, t2; easy. Qed.

Theorem subtyping_trans: transitive _ Subtype.
Proof.
  cofix Hyp.
  intros t1 t2 t3 H1 H2.
  inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
    name_cases;
    try (constructor; easy).
  [Case_NatIntSL_Case_ConstituentOptST]: {
    named_constructor.
    - assumption.
    - eapply Hyp; [named_econstructor | assumption].
  }
  [Case_OptST_Case_OptST0]: {
    named_constructor.
    - intuition.
    - eapply Hyp; eassumption.
  }
  [Case_OptST_Case_ConstituentOptST]: {
    inversion H3; subst; clear H3; simpl in H0; contradiction.
  }
  [Case_ConstituentOptST_Case_OptST]: {
    named_constructor.
    - intuition.
    - firstorder.
  }
  [Case_ConstituentOptST_Case_ConstituentOptST0]: {
    inversion H3; subst; clear H3; try easy.
  }
  [Case_ReservedST_Case_ConstituentOptST]: {
    inversion H0; subst; clear H0; inversion H.
  }
Qed.