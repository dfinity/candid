(*
MiniCandid: A formalization of the core ideas of Candid
*)

Require Import Coq.ZArith.BinInt.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Operators_Properties.

Set Bullet Behavior "Strict Subproofs".


(* Types are coinductive (we do not want to model the graph structure explicilty) *)
CoInductive T :=
  | NatT: T
  | IntT: T
  | NullT : T
  | OptT : T -> T.

Inductive V :=
  | NatV : nat -> V
  | IntV : Z -> V
  | NullV : V
  | SomeV : V -> V.


Definition is_not_opt_like_type (t : T) : Prop :=
  match t with
  | NullT => False
  | OptT _ => False
  | _ => True
  end.

Reserved Infix "<:" (at level 80, no associativity).
CoInductive Subtype : T -> T -> Prop :=
  | ReflST : forall t, t <: t
  | NatIntST : NatT <: IntT
  | NullOptST : forall t, NullT <: OptT t
  | OptST :
    forall t1 t2,
    (* This additional restriction added to fix https://github.com/dfinity/candid/issues/146 *)
    (is_not_opt_like_type t1 <-> is_not_opt_like_type t2) -> 
    t1 <: t2 ->
    OptT t1 <: OptT t2
  | ConstituentOptST :
    forall t1 t2,
    is_not_opt_like_type t2 ->
    t1 <: t2 -> t1 <: OptT t2
where "t1 <: t2" := (Subtype t1 t2).


Inductive HasType : V -> T -> Prop :=
  | NatHT: forall n, NatV n :: NatT
  | IntHT: forall n, IntV n :: IntT
  | NullHT: NullV :: NullT
  | NullOptHT: forall t, NullV :: OptT t
  | OptHT: forall v t, v :: t -> SomeV v :: OptT t
where "v :: t" := (HasType v t).

Definition is_not_opt_like_value (v : V) : Prop :=
  match v with
  | NullV => False
  | SomeV _ => False
  | _ => True
  end.


Reserved Notation "v1 ~> v2 :: t" (at level 80, v2 at level 50, no associativity).
Inductive Coerces : V -> V -> T -> Prop :=
  | NatC: forall n, (NatV n ~> NatV n :: NatT)
  | IntC: forall n, (IntV n ~> IntV n :: IntT)
  | NatIntC: forall n i, i = Z.of_nat n -> (NatV n ~> IntV i :: IntT)
  | NullC: NullV ~> NullV :: NullT
  | NullOptC: forall t, NullV ~> NullV :: OptT t
  | SomeOptC: forall v1 v2 t, v1 ~> v2 :: t -> SomeV v1 ~> SomeV v2 :: OptT t
  | ConstituentOptC: forall v1 v2 t,
    is_not_opt_like_value v1 ->
    v1 ~> v2 :: t ->
    v1 ~> SomeV v2 :: OptT t
where "v1 ~> v2 :: t" := (Coerces v1 v2 t).

(* The is_not_opt_like_type definition is only introduced because
   Coq (and not only coq) does not like hyptheses like ~(null <: t)
*)
Lemma is_not_opt_like_type_correct:
  forall t,
  is_not_opt_like_type t <-> ~ (NullT <: t).
Proof.
  intros. destruct t; simpl; intuition.
  * inversion H0.
  * inversion H0.
  * apply H. constructor.
  * apply H. constructor.
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
    try (eexists;constructor; fail).
  * eexists. constructor. reflexivity. 
  * inversion H0; subst; clear H0; simpl in H; inversion H.
    - eexists. constructor; try constructor.
    - eexists. constructor; try constructor; reflexivity.
  * inversion H0; subst; clear H0; simpl in H; inversion H.
    econstructor. econstructor. constructor. constructor.
  * specialize (IHHvT t (ReflST _)).
    destruct IHHvT as [v2 Hv2].
    eexists; econstructor; try eassumption.
  * specialize (IHHvT _ H1).
    destruct IHHvT as [v2 Hv2].
    eexists; econstructor; eassumption.
  * inversion H0; subst; clear H0; simpl in H; inversion H.
Qed.

Theorem subtyping_refl: reflexive _ Subtype.
Proof. intros x. apply ReflST. Qed.

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
    try (constructor; easy).
  * constructor. assumption.
    eapply Hyp; [econstructor|assumption].
  * constructor.
    - intuition.
    - eapply Hyp; eassumption.
  * inversion H3; subst; clear H3; simpl in H0; contradiction.
  * constructor.
    - intuition.
    - firstorder.
  * inversion H3; subst; clear H3; try easy.
Qed.