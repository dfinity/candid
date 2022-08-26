(**
MiniCandid: A formalization of the core ideas of Candid
*)

Require Import FunInd.

Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Operators_Properties.

Require Import Coq.Logic.Decidable.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

(* Loads the idiosyncratic CaseNames extension *)
Require Import candid.NamedCases.
Set Printing Goal Names. (* Coqide doesn’t use it yet, will be in 8.13 *)

(**
* Types

We begin by defining the Candid types (or at least some of them).

Candid types are inherently coinductive (e.g. <<type T = opt T>>), so we describe
them as a coinductive relation. This way we don’t have to model an explicit graph
structure in Coq.
*)
CoInductive T :=
  | NatT: T
  | IntT: T
  | NullT : T
  | OptT : T -> T
  | FuncT : T -> T -> T
  | VoidT : T
  | ReservedT : T
  .

(**
* Values

Values are inductive.

Function reference values are modeled as an abstract type.
*)
Axiom Ref : Type.

Inductive V :=
  | NatV : nat -> V
  | IntV : Z -> V
  | NullV : V
  | SomeV : V -> V
  | FuncV : Ref -> V
  | ReservedV : V
  .
(**

* Typing and subtyping

The following is a stand in for `null <: t` in places where <: is not allowed yet.
*)
Definition is_opt_like_type (t : T) : bool :=
  match t with
  | NullT => true
  | OptT _ => true
  | ReservedT => true
  | _ => false
  end.


(** The boring, non-subtyping typing relation.

This is parametrized by a typing relation for references.
*)
Reserved Notation "G '|-' v ':::' T" (at level 80).

Inductive HasType (G : Ref -> T -> T -> Prop) : V -> T -> Prop :=
  | NatHT:
    case natHT,
    forall n,
    G |- NatV n ::: NatT
  | IntHT:
    case intHT,
    forall n,
    G |- IntV n ::: IntT
  | NullHT:
    case nullHT,
    G |- NullV ::: NullT
  | NullOptHT:
    case nullOptHT,
    forall t,
    G |- NullV ::: OptT t
  | OptHT:
    case optHT,
    forall v t, G |- v ::: t ->
    G |- SomeV v ::: OptT t
  | FuncHT:
    case funcHT,
    forall r t1 t2, G r t1 t2 ->
    G |- FuncV r ::: FuncT t1 t2
  | ReservedHT:
    case reservedHT,
    G |- ReservedV ::: ReservedT
where "G |- v ::: t" := (HasType G v t).

(** The subtyping relation *)
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

(**
Subtyping is reflexive and transitive.

Note that these are coinductive proofs! (And yet so neat)
**)

Theorem subtyping_refl: reflexive _ Subtype.
Proof. intros x. apply ReflST; constructor. Qed.


Theorem subtyping_trans: transitive _ Subtype.
Proof.
  cofix Hyp.
  intros t1 t2 t3 H1 H2.
  inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
  constructor; firstorder.
Qed.

(**
Subtyping is undecidable, at least the way we model it in Coq.
But for the decoding function we have to pretend it is decidable.
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

(**

* Coercion function

The spec defines the coercion function as indexed by the subtyping relation.
But that relation is coinductive, so Coq will not allow that.
We thus define the function by recursion on the value.

*)

Function coerce (t1 : T) (t2 : T) (v1 : V) : option V :=
  match v1, t1, t2 with
  | NatV n, NatT, NatT => Some (NatV n)
  | IntV n, IntT, IntT => Some (IntV n)
  | NatV n, NatT, IntT => Some (IntV (Z.of_nat n))
  | FuncV r, FuncT ta1 tr1, FuncT ta2 tr2 =>
    if FuncT ta1 tr1 <:? (FuncT ta2 tr2)
    then Some (FuncV r)
    else None

  | NullV, NullT, NullT => Some NullV

  | NullV, NullT, OptT t2 => Some NullV
  | NullV, OptT t1, OptT t2 => Some NullV
  | SomeV v, OptT t1, OptT t2 =>
    match coerce t1 t2 v with
    | None => Some NullV
    | Some t => Some (SomeV t)
    end

  (* We’d prefer the equation from [coerce_constituent_eq] below,
     but that looks like it recurses on t2, and that’s coinductive,
     but that will not satisfy the termination checker,
     so we have to repeat all the above rules for OptT again.
  *)
  | NatV n, NatT, OptT NatT => Some (SomeV (NatV n))
  | IntV n, IntT, OptT IntT => Some (SomeV (IntV n))
  | NatV n, NatT, OptT IntT => Some (SomeV (IntV (Z.of_nat n)))
  | FuncV r, FuncT ta1 tr1, OptT (FuncT ta2 tr2) =>
    if FuncT ta1 tr1 <:? (FuncT ta2 tr2)
    then Some (SomeV (FuncV r))
    else Some NullV

  (* The final catch-all for OptT *)
  | _, _, OptT t => Some NullV


  | v, t, ReservedT => Some ReservedV

  | _, _, _ => None
  end.

(* We can prove the desired equation at least as an equality *)
Lemma coerce_constituent_eq:
  forall G v t1 t2,
  G |- v ::: t1 ->
  is_opt_like_type t1 = false ->
  is_opt_like_type t2 = false ->
  coerce t1 (OptT t2) v =
    match coerce t1 t2 v with
    | None => Some NullV
    | Some t => Some (SomeV t)
    end.
Proof.
  intros G v t1 t2 HHT His_opt_like_t1 His_opt_like_t2.
  inversion HHT; subst; clear HHT; inversion His_opt_like_t1; clear His_opt_like_t1; name_cases.
  [natHT]: {
    destruct t2; subst; inversion His_opt_like_t2; clear His_opt_like_t2; simpl; try reflexivity.
  }
  [intHT]: {
    destruct t2; subst; inversion His_opt_like_t2; clear His_opt_like_t2; simpl; try reflexivity.
  }
  [funcHT]: {
    destruct t2; subst; inversion His_opt_like_t2; clear His_opt_like_t2; simpl; try reflexivity.
    destruct (FuncT t0 t3 <:? FuncT t2_1 t2_2); try reflexivity.
  }
Qed.

Lemma coerce_reservedT:
  forall v t1, coerce t1 ReservedT v = Some ReservedV.
Proof.
  intros v1 t1.
  destruct v1, t1; reflexivity.
Qed.

(** TODO: What to make of this now


(**
This beast of a lemma defines and proves a nice induction principle for [coerce],
*)
Lemma coerce_nice_ind:
  forall (P : T -> T -> V -> V -> Prop),
  (case natC, forall n, P NatT NatT (NatV n) (NatV n)) ->
  (case intC, forall n, P IntT IntT (IntV n) (IntV n)) ->
  (case natIntC, forall n, P NatT IntT (NatV n) (IntV (Z.of_nat n))) ->
  (case nullC, P NullT NullT NullV NullV) ->
  (case nullOptC, forall t, P NullT (OptT t) NullV NullV) ->
  (case optNullC, forall t1 t2, P (OptT t1) (OptT t2) NullV NullV) ->
  (case optSomeC, forall t1 t2 v1 v2,
    v1 :: t1 ->
    P t1 t2 v1 v2 ->
    P (OptT t1) (OptT t2) (SomeV v1) (SomeV v2)) ->
  (case opportunisticOptC, forall t1 t2 v1,
    coerce t1 t2 v = None ->
    v1 :: t1 ->
    P (OptT t1) (OptT t2) (SomeV v1) NullV) ->
  (case reservedOptC,
    forall t, P ReservedT (OptT t) ReservedV NullV) ->
  (case constituentOptC,
    forall t1 t2 v1 v2,
    is_opt_like_type t1 = false ->
    is_opt_like_type t2 = false ->
    v1 :: t1 ->
    P t1 t2 v1 v2 ->
    P t1 (OptT t2) v1 (SomeV v2)) ->
  (case opportunisticConstituentOptC,
    forall t1 t2 v1,
    v1 :: t1 ->
    is_opt_like_type t1 = false ->
    is_opt_like_type t2 = true \/ coerce t1 t2 v1 = None ->
    P t1 (OptT t2) v1 NullV) ->
  (case funcC, forall ta1 tr1 ta2 tr2 v,
    ta2 <: ta1 ->
    tr1 <: tr2 ->
    P (FuncT ta1 tr1) (FuncT ta2 tr2) (FuncV v) (FuncV v)) ->
  (case reservedC, forall t v, v :: t -> P t ReservedT v ReservedV) ->
  (forall t1 t2 v1,
   v1 :: t1 -> P t1 t2 v1 (coerce t1 t2 v1)).
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
      (* oddly,
        rewrite coerce_constituent_eq by (try named_constructor; reflexivity).
        does not seem to lead to a simpler proof here.
      *)
      destruct (is_opt_like_type t0) eqn:His_opt_like.
      * destruct t0; inversion His_opt_like; simpl; clear His_opt_like;
        apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
      * destruct (subtyping_decidable NatT t0).
        + destruct t0; inversion s; subst; clear s; inversion His_opt_like; clear His_opt_like.
          - apply ConstituentOptC; clear_names; simpl; intuition; named_constructor.
          - apply ConstituentOptC; clear_names; simpl; intuition; named_constructor.
        + destruct t0; inversion His_opt_like; clear His_opt_like.
          - contradict n0. named_constructor.
          - contradict n0. named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
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
        apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
      * destruct (subtyping_decidable IntT t0).
        + destruct t0; inversion s; subst; clear s; inversion His_opt_like; clear His_opt_like.
          - apply ConstituentOptC; clear_names; simpl; intuition; named_constructor.
        + destruct t0; inversion His_opt_like; clear His_opt_like.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
          - contradict n0. named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
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
        apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
      * destruct (subtyping_decidable (FuncT t1 t2) t4).
        + destruct t4; inversion s; subst; clear s; inversion His_opt_like; clear His_opt_like.
          - simpl. repeat rewrite subtype_dec_refl.
            apply ConstituentOptC; clear_names; simpl; try (intuition;fail).
            ** apply ReflST; clear_names; apply ReflST; clear_names.
            ** named_constructor.
            ** apply FuncC; clear_names; apply ReflST; clear_names.
          - simpl. repeat rewrite subtype_dec_true by assumption.
            apply ConstituentOptC; clear_names; simpl; try (intuition;fail).
            ** named_constructor; assumption.
            ** named_constructor.
        + destruct t4; inversion His_opt_like; clear His_opt_like.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
          - simpl.
            destruct (t4_1 <:? t1).
            ** destruct (t2 <:? t4_2).
               ++ contradict n. named_constructor; assumption.
               ++ apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
            ** apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
          - apply OpportunisticConstituentOptC; clear_names; simpl; intuition named_constructor.
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
**)


(**
* Properties of coercion

Round-tripping
*)
Lemma coerce_roundtrip:
  forall G t1 v1,
  G |- v1 ::: t1 ->
  coerce t1 t1 v1 = Some v1.
Proof.
(** 
  enough (forall t1 t2 v1,
    t1 <: t2 -> v1 :: t1 -> t2 = t1 ->
    coerce t1 t2 v1 = v1)
    by (intros; apply H; intuition; try apply ReflST; clear_names).
  apply (coerce_nice_ind (fun t1 t2 v1 v2 => t2 = t1 -> v2 = v1));
    intros; name_cases; try solve [subst; simpl in *; congruence].
  [optSomeC]: {apply f_equal. apply H1. congruence. }
  [opportunisticOptC]: {
    inversion H1; subst; clear H1. contradiction H; apply ReflST; clear_names.
  }
  [reservedC]: {  inversion H; subst; clear H; congruence. }
*)
  intros G t1 v1 HHT.
  induction HHT; name_cases. all: simpl; try rewrite subtype_dec_refl; try reflexivity.
  * rewrite IHHHT; reflexivity.
Qed.

(**
Coercion does not fail on subtypes and well-typed values
*)

Lemma coerce_well_defined:
  forall G t1 t2 v1,
  t1 <: t2 -> G |- v1 ::: t1 ->
  coerce t1 t2 v1 <> None.
Proof.
  intros G t1 t2 v1 HST HHT.
  revert t2 HST.
  induction HHT; name_cases; intros t3 HST; inversion HST.
  all: try (simpl; congruence).
  all: try (destruct t2; simpl; congruence).
  * simpl. rewrite (coerce_roundtrip G _ _ HHT). congruence.
  * simpl; destruct (coerce t t2 v) eqn:H2; try congruence.
  * simpl; rewrite subtype_dec_refl; congruence.
  * simpl. destruct t4;simpl; try congruence.
    destruct (_ <:? _); congruence.
  * simpl. destruct (_ <:? _); congruence.
Qed.


Definition Ok_ref_env (G : Ref -> T -> T -> Prop) :=
  forall r ta1 tr1 ta2 tr2,
  G r ta1 tr1 -> ta2 <: ta1 -> tr1 <: tr2 -> G r ta2 tr2.

(**
Coercion returns well-typed values
*)

Lemma coerce_well_typed:
  forall G, Ok_ref_env G ->
  forall t1 t2 v1 v2, G |- v1 ::: t1 ->
  coerce t1 t2 v1 = Some v2 ->
  G |- v2 ::: t2.
Proof.
  intros G HG t1 t2 v1 v2 HHT Heq.
  revert t2 v2 Heq.
  induction HHT; name_cases; intros t3 v3 Heq.
  all: simpl in Heq; destruct t3; try congruence.
  all: inversion Heq; clear Heq; try named_constructor.
  + destruct t3; try congruence;
    inversion H0; try named_constructor; try named_constructor.
  + destruct t3; try congruence;
    inversion H0; try named_constructor; try named_constructor.
  + destruct (coerce t t3 v) eqn:Heq.
    - specialize (IHHHT _ _ Heq).
      inversion H0; clear H0.
      named_constructor; assumption.
    - inversion H0; clear H0; named_constructor.
  + destruct t3; try congruence.
    all: inversion H1; clear H1; try named_constructor; try named_constructor.
    - destruct (FuncT t1 t2 <:? FuncT t3_1 t3_2) eqn:Hst.
      * inversion H2; clear H2.
        named_constructor.
        named_constructor.
        (* This doesn’t quite work: Looks like :: needs to take <: into account in
        the FuncT case *)
        (* apply FuncHT. *)
        inversion s; subst; clear s Hst.
        ++ apply H.
        ++ apply (HG _ _ _ _ _ H H4 H6).
      * inversion H2; clear H2.
        subst.
        named_constructor.
  + destruct (FuncT t1 t2 <:? FuncT t3_1 t3_2) eqn:Hst; try congruence.
    inversion H1; subst; clear H1.
    named_constructor.
    inversion s; subst; clear s Hst.
    ++ apply H.
    ++ apply (HG _ _ _ _ _ H H3 H5).
Qed.


(**
* IDL Soundess 

To work towards IDL soundness, we need a predicate for “Value v contains
a function reference at function type t.”. Moreover, this contains
relation should indicate the position in the value in a way that
the positions match up even after coercions.

So we start by giving names to positions
(This needs to be extended once we have sequences and records)
*)
Inductive Path :=
  | Here : Path
  | The : Path -> Path
  .

(**
And a function that finds the value at a given path.

It returns [None] if the path does not make sense for this value.
*)
Fixpoint val_idx (p : Path) (v : V) : option V :=
  match p with
  | Here => Some v
  | The p =>
    match v with
    | SomeV v => val_idx p v
    | _ => None
    end
  end.

(**
This is a lenient variant, which is total (returning [NullV]
when the path is invalid), which makes proofs simpler.

It also ignores extra [The] on the path; this way one can 
use this on the pre-coerced value, and get the right value,
even if the constituent-to-optional rule was used.
*)
Fixpoint val_idx' (p : Path) (v : V) : V :=
  match p with
  | Here => v
  | The p =>
    match v with
    | SomeV v => val_idx' p v
    | NullV => NullV
    | ReservedV => NullV
    | _ => val_idx' p v
    end
  end.

(**
The corresponding function for types, also lenient.
*)
Fixpoint typ_idx' (p : Path) (t : T) : T :=
  match p with
  | Here => t
  | The p =>
    match t with
    | OptT t => typ_idx' p t
    | NullT => VoidT
    | ReservedT => VoidT
    | _ => typ_idx' p t
    end
  end.

(**
Properties about [val_idx] and [typ_idx'], mostly for sanity-checking
*)
Lemma path_preserves_types:
  forall G v v' t p,
  G |- v ::: t ->
  val_idx p v = Some v' ->
  G |- v' ::: typ_idx' p t.
Proof.
  intros G v v' t p.
  revert v v' t.
  induction p.
  * intros v v' t HHT Hval_idx.
    inversion Hval_idx; subst; clear Hval_idx.
    assumption.
  * intros v v' t HHT Hval_idx.
    inversion Hval_idx; subst; clear Hval_idx.
    inversion HHT; subst; clear HHT; name_cases.
    all: firstorder congruence.
Qed.

Lemma val_idx_is_val_idx':
  forall G v v' t p,
  G |- v ::: t ->
  val_idx p v = Some v' ->
  val_idx' p v = v'.
Proof.
  intros G v v' t p.
  revert v v' t.
  induction p.
  * intros v v' t HHT Hval_idx.
    inversion Hval_idx; subst; clear Hval_idx.
    reflexivity.
  * intros v v' t HHT Hval_idx.
    inversion Hval_idx; subst; clear Hval_idx.
    inversion HHT; subst; clear HHT; name_cases.
    all: firstorder congruence.
Qed.

(**
The core lemma towards compositionality:

All values in a decoded value originate from a value in the original value,
and their types are related.

This may be proving a bit more than needed for compositionality, but it my be
handy for other things.
*)

(* TODO: Update to option-returning coerce
  (although we know it can't be Null due to coerce_well_defined) *)

Lemma no_new_values:
  forall G t1 t2 v1,
  t1 <: t2 ->
  G |- v1 ::: t1 ->
  forall p iv2,
  val_idx p (coerce t1 t2 v1) = Some iv2 ->
    (iv2 = NullV \/ typ_idx' p t1 <: typ_idx' p t2) /\
    G |- val_idx' p v1 ::: typ_idx' p t1 /\
    coerce (typ_idx' p t1) (typ_idx' p t2) (val_idx' p v1) = iv2.
Proof.
  apply (coerce_nice_ind (fun t1 t2 v1 v2 =>
    forall p iv2,
    forall (Hval_idx : val_idx p v2 = Some iv2),
      (iv2 = NullV \/ typ_idx' p t1 <: typ_idx' p t2) /\
      val_idx' p v1 :: typ_idx' p t1 /\
      coerce (typ_idx' p t1) (typ_idx' p t2) (val_idx' p v1) = iv2
  )); intros; name_cases.
  all:
    try solve [destruct p; inversion Hval_idx; subst; clear Hval_idx; intuition (named_constructor; assumption)].
  [optSomeC]: {
    destruct p; inversion Hval_idx; subst; clear Hval_idx.
    * specialize (H1 Here v2 eq_refl).
      simpl in *.
      decompose record H1; clear H1.
      repeat split.
      - right; named_constructor; assumption.
      - named_constructor; assumption.
      - simpl. rewrite subtype_dec_true by assumption. congruence.
    * specialize (H1 _ _ H3).
      intuition.
  }
  [opportunisticOptC]: {
    destruct p; inversion Hval_idx; subst; clear Hval_idx.
    simpl in *.
    repeat split.
    - left; reflexivity.
    - named_constructor. assumption.
    - simpl. rewrite subtype_dec_false by assumption. reflexivity.
  }
  [constituentOptC]: {
    destruct p; inversion Hval_idx; subst; clear Hval_idx.
    * specialize (H3 Here v2 eq_refl).
      simpl in *.
      decompose record H3; clear H3.
      repeat split.
      - right;  named_constructor.
      - assumption.
      - rewrite coerce_constituent_eq by assumption.
        rewrite H0.
        rewrite subtype_dec_true by assumption. congruence.
    * specialize (H3 _ _ H5).
      decompose record H3; clear H3.
      inversion H2; subst; clear H2; inversion H; subst; clear H; intuition.
  }
  [opportunisticConstituentOptC]: {
    destruct p; inversion Hval_idx; subst; clear Hval_idx.
    simpl in *.
    repeat split.
    - left; reflexivity.
    - assumption.
    - rewrite coerce_constituent_eq by assumption.
      destruct H1.
      * rewrite H1. destruct (t1 <:? t2); reflexivity.
      * rewrite subtype_dec_false by assumption. reflexivity.
  }
  [reservedC]: {
    destruct p; inversion Hval_idx; subst; clear Hval_idx.
    simpl in *.
    repeat split.
    - right; named_constructor; assumption.
    - assumption.
    - destruct t, v; simpl; try reflexivity.
  }
Qed.

(**
This is the instantiation of [passesThrough] from the IDL-Soundness theory.
*)
Definition passesThrough (s1 : T * T) (t1 : T) (s2 : T * T) (t2 : T) :=
  exists v1 p r,
  v1 :: t1 /\
  val_idx' p v1 = FuncV r /\
  typ_idx' p t1 = FuncT (fst s1) (snd s1) /\
  val_idx  p (coerce t1 t2 v1) = Some (FuncV r) /\
  typ_idx' p t2 = FuncT (fst s2) (snd s2).

(**
And indeed subtyping is compositional:
*)
Lemma compositional:
  forall t1 t2 s1 s2,
  t1 <: t2 -> passesThrough s1 t1 s2 t2 -> (snd s1 <: snd s2 /\ fst s2 <: fst s1).
Proof.
  intros.
  unfold passesThrough in *.
  destruct s1, s2.
  simpl in *.
  enough (FuncT t t0 <: FuncT t3 t4)
    by (inversion H1; subst; clear H1; split; try assumption; named_constructor).
  destruct H0 as [v1 [p [r Hpt]]].
  decompose record Hpt; clear Hpt.
  pose proof (no_new_values t1 t2 v1 H H0 p _ H3) as Hnnv.
  decompose record Hnnv; clear Hnnv.
  destruct H4; congruence.
Qed.

(**
Now we can instantiate the soundness theorem from IDLSoundness
*)

Require Import candid.IDLSoundness.

Theorem soundness:
  forall I,
  IDLSound T Subtype passesThrough
    (fun '(ta2, tr2) '(ta1,tr1)  => ta2 <: ta1 /\ tr1 <: tr2)
    (fun '(ta1,tr1) '(ta2, tr2) => ta2 <: ta1 /\ tr1 <: tr2)
    I.
Proof.
  intro.
  apply canonical_soundness.
  - apply subtyping_refl.
  - apply subtyping_trans.
  - unfold service_subtyping.
    intros.
    destruct s1 as [ta1 tr1].
    destruct s2 as [ta2 tr2].
    intuition.
  - intros.
    pose proof (compositional _ _ _ _ H H0).
    unfold service_subtyping.
    intros.
    destruct s1 as [ta1 tr1].
    destruct s2 as [ta2 tr2].
    intuition.
  - intros.
    destruct s1 as [ta1 tr1].
    destruct s2 as [ta2 tr2].
    unfold service_subtyping.
    intuition.
Qed.

(**
* Transitive coherence

Transitive coherence only holds up to a weaker relation:
*)

Reserved Infix "~~" (at level 80, no associativity).
CoInductive UpToNull : V -> V -> Prop :=
  (* This is the interesting rule: *)
  | NullSomeUT:
    forall v,
    NullV ~~ SomeV v
  | SomeNullUT:
    forall v,
    SomeV v ~~ NullV
    
  (* The rest just form the homomorphic closure *)
  | NatUT:
    forall n, NatV n ~~ NatV n
  | IntUT:
    forall n, IntV n ~~ IntV n
  | NullUT:
    NullV ~~ NullV
  | SomeUT:
    forall v1 v2,
    v1 ~~ v2 ->
    SomeV v1 ~~ SomeV v2
  | FuncUT:
    forall r, FuncV r ~~ FuncV r
  | ReservedUT:
    ReservedV ~~ ReservedV
where "v1 ~~ v2" := (UpToNull v1 v2).

Lemma UpToNull_refl:
  forall v, UpToNull v v.
Proof. intros. induction v; constructor; assumption. Qed.

(** A small tactic that I keep copying into each development *)
Ltac destruct_match :=
  match goal with
  | [ H :context[match ?a with _ => _ end] |- _] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq
  | [ |- context[match ?a with _ => _ end]] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq
  end.

Theorem transitive_coherence:
  forall ta tb tc v1,
  ta <: tb ->
  tb <: tc ->
  v1 :: ta ->
  coerce tb tc (coerce ta tb v1) ~~ coerce ta tc v1.
Proof.
  intros ta tb tc v1 HST1 HST2 HHT.
  revert tc HST2.
  revert ta tb v1 HST1 HHT.
  apply (coerce_nice_ind (fun ta tb v1 v2 =>
    forall tc : T,
     forall HST2 : tb <: tc,
      coerce tb tc v2 ~~ coerce ta tc v1
  )); intros; inversion HST2; subst; clear HST2.
  all: simpl.
  all: try rewrite coerce_constituent_eq by assumption.
  all: try rewrite coerce_reservedT.
  all: try rewrite subtype_dec_refl.
  all: try rewrite subtype_dec_true by assumption.
  all: try solve [
    repeat destruct_match;
    try apply UpToNull_refl;
    intuition constructor
    ].
  all: name_cases.
  [optSomeC_reflST]: { constructor. apply H1. named_constructor. }
  [optSomeC_optST]: {
    repeat destruct_match; try apply UpToNull_refl; try  apply NullSomeUT.
    - constructor. apply H1. assumption.
    - contradiction n. eapply subtyping_trans; eassumption.
  }
  [constituentOptC_reflST]: {
    rewrite H0.
    constructor. apply H3. named_constructor.
  }
  [constituentOptC_optST]: {
    repeat destruct_match; try apply UpToNull_refl; try  apply NullSomeUT.
    - constructor.
    - constructor. apply H3. assumption.
    - contradiction n. eapply subtyping_trans; eassumption.
  }
  [reservedC_optST]: {
    destruct t, v; simpl; repeat destruct_match; try apply UpToNull_refl; try  apply NullSomeUT.
  } 
Qed.
