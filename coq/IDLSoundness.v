(**

This theory formalizes
   https://github.com/dfinity/candid/blob/master/spec/IDL-Soundness.md

*)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Sets.Ensembles.
(* Odd that this is needed, see
https://www.reddit.com/r/Coq/comments/bmslyy/why_doesnt_ensemble_functions_in_coqs_standard/emzazzd
*)
Arguments In {U}.
Arguments Add {U}.
Arguments Empty_set {U}.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Operators_Properties.

Require Import candid.NamedCases.

Set Bullet Behavior "Strict Subproofs".

Section IDL.

  (**
  
  * The Abstract IDL theory
  
  An abstract theory of IDLs is parametrized as follows:
  *)
  
  (** The type of (argument or result types) *)
  Variable T : Set.

  (** A service type is a pair of types (argument and results) *)
  Definition S : Set := (T * T).
  Notation "t1 --> t2" := (t1, t2) (at level 80, no associativity).

  (** The theory has to define the following predicates *)
  Variable decodesAt : T -> T -> Prop.
  Notation "t1 <: t2" := (decodesAt t1 t2) (at level 70, no associativity).

  Variable passesThrough : S -> T -> S -> T -> Prop.
  Notation "s1 ∈ t1 <: s2 ∈ t2" := (passesThrough s1 t1 s2 t2)
    (t1 at level 50, s2 at level 50, at level 70, no associativity).

  Variable evolves : S -> S -> Prop.
  Notation "s1 ~> s2" := (evolves s1 s2) (at level 70, no associativity).

  Variable hostSubtypeOf : S -> S -> Prop.
  Notation "s1 <<: s2" := (hostSubtypeOf s1 s2) (at level 70, no associativity).

  (** This is generic in the set of service identifiers *)
  Variable I : Set.

  (** ** Judgements *)
  Inductive Assertion : Set :=
    | HasType : I -> S -> Assertion
    | HasRef : I -> I -> S -> Assertion.

  Definition State := Ensemble Assertion.

  Definition FreshIn (i : I) (st : State) : Prop :=
    (forall s, ~ In st (HasType i s)) /\
    (forall i' s, ~ In st (HasRef i i' s)) /\
    (forall i' s, ~ In st (HasRef i' i s)).

  Inductive CanSend : State -> I -> T -> T -> I -> Prop :=
    | CanCall:
      case canCall,
      forall st A B t1 t1' t2 t2',
      In st (HasRef A B (t1 --> t1')) ->
      In st (HasType B (t2 --> t2')) ->
      CanSend st A t1 t2 B
    | CanReply:
      case canReply,
      forall st A B t1 t1' t2 t2',
      In st (HasRef B A (t1 --> t1')) ->
      In st (HasType A (t2 --> t2')) ->
      CanSend st A t2' t1' B.

  Inductive step : State -> State -> Prop :=
    | NewService :
      case newService,
      forall (i : I) (s : S) st,
      FreshIn i st ->
      step st (Add st (HasType i s))
    | EvolveService :
      case evolveService,
      forall (i : I) (s1 s2 : S) st,
      ~ In st (HasType i s1) ->
      s1 ~> s2 ->
      step (Add st (HasType i s1)) (Add st (HasType i s2))
    | LearnService :
      case learnService,
      forall (i1 i2 : I) (s: S) st,
      In st (HasType i1 s) ->
      step st (Add st (HasRef i2 i1 s))
    | TransmitService :
      case transmitService,
      forall (A B C : I) (s1 s2 : S) (t1 t2 : T) st,
      In st (HasRef A C s1) ->
      CanSend st A t1 t2 B ->
      (s1 ∈ t1 <: s2 ∈ t2) ->
      step st (Add st (HasRef B C s2))
    | HostSubtyping :
      case hostSubtyping,
      forall (A B : I) (s1 s2 : S) st,
      s1 <<: s2 ->
      step (Add st (HasRef A B s1)) (Add st (HasRef A B s2))
    .

  Definition StateSound (st : State) : Prop :=
    forall A t1 t2 B, CanSend st A t1 t2 B ->  t1 <: t2.
    
  (** The final soundness proposition *)

  Definition IDLSound : Prop :=
    forall s, clos_refl_trans _ step Empty_set s -> StateSound s.

  (** * Canonical subtyping *)

  (**
  We continue with the soundness proof for canonical subtyping.

  We do so by just adding more hypotheses to this Section.
  *)

  Hypothesis decodesAt_refl: reflexive _ decodesAt.
  Hypothesis decodesAt_trans: transitive _ decodesAt.

  Definition service_subtyping (s1 s2 : S) : Prop :=
    let '(t1 --> t1') := s1 in
    let '(t2 --> t2') := s2 in
    t1' <: t2' /\ t2 <: t1.
  Notation "s1 <:: s2" := (service_subtyping s1 s2) (at level 70, no associativity).
  
  Hypothesis evolves_correctly:
   forall s1 s2, s1 ~> s2 -> s2 <:: s1.
  Hypothesis compositional:
    forall t1 t2 s1 s2,
    t1 <: t2 -> s1 ∈ t1 <: s2 ∈ t2 -> s1 <:: s2.
  Hypothesis host_subtyping_sound:
   forall s1 s2, s1 <<: s2 -> s1 <:: s2.

  (**
  Now the actual proofs. When I was writing these, my Coq has become
  pretty rusty, so these are rather manual proofs, with little
  automation. The style is heavily influenced by the explicit Isar-style
  proofs in Isabelle. But hey, it works, and may aid readiablity.
  *)

  Lemma service_subtype_refl: reflexive _ service_subtyping.
  Proof.
    intros [t1 t1'].
    split; apply decodesAt_refl.
  Qed.

  Lemma service_subtype_trans: transitive _ service_subtyping.
  Proof.
    intros [t1 t1'] [t2 t2'] [t3 t3'] H1 H2.
    destruct H1, H2.
    split; eapply decodesAt_trans; eassumption.
  Qed.


  Definition unique (st : State) :=
     forall A s1 s2,
     In st (HasType A s1) -> In st (HasType A s2) -> s1 = s2.

  Definition invariant (st : State) :=
     forall A B s1 s2,
     In st (HasType A s1) -> In st (HasRef B A s2) -> s1 <:: s2 .

  Lemma invariant_implies_StateSound:
    forall st, invariant st -> StateSound st.
  Proof.
    intros st Hinvariant.
    intros A t1 t2 B HCanSend.
    destruct HCanSend; name_cases.
    [canCall]: {
      pose proof (Hinvariant B A (t2 --> t2') (t1 --> t1') H0 H) as H1.
      apply H1.
    }
    [canReply]: {
      pose proof (Hinvariant A B (t2 --> t2') (t1 --> t1') H0 H) as H1.
      apply H1.
    }
  Qed.

  Lemma invariant_Add_HasType:
    forall st A s1,
    invariant st ->
    (forall B s2, In st (HasRef B A s2) -> s1 <:: s2) ->
    invariant (Add st (HasType A s1)).
  Proof.
     intros st A s1 Hinv HA.
     intros A' B s1' s2 HHasType HHasRef.
     inversion HHasType; clear HHasType; inversion HHasRef; clear HHasRef; subst.
     * eapply Hinv; eassumption.
     * inversion H1.
     * inversion H; subst; clear H.
       eapply HA; eassumption.
     * inversion H; subst; clear H.
       inversion H1; subst; clear H1.
  Qed.

  Lemma invariant_Add_HasRef:
    forall st A B s2,
    invariant st ->
    (forall s1, In st (HasType B s1) -> s1 <:: s2) ->
    invariant (Add st (HasRef A B s2)).
  Proof.
    intros st A B s2 Hinv HA.
    intros A' B' s1' s2' HHasRef HHasType.
    inversion HHasType; clear HHasType; inversion HHasRef; clear HHasRef; subst.
    * eapply Hinv; eassumption.
    * inversion H1.
    * inversion H; subst; clear H.
      eapply HA; eassumption.
    * inversion H; subst; clear H.
      inversion H1; subst; clear H1.
  Qed.

  Lemma invariant_Add_HasType_elim:
    forall st A s1,
    invariant (Add st (HasType A s1)) ->
    invariant st /\ (forall B s2, In st (HasRef B A s2) -> s1 <:: s2).
  Proof.
    intros st A s1 HInv.
    split.
    * intros A' B' s1' s2' HHasRef HHasType.
      eapply HInv.
      - apply Union_introl. eassumption.
      - apply Union_introl. eassumption.
    * intros B s2' HIn.
      eapply HInv.
      - apply Union_intror. constructor.
      - apply Union_introl. eassumption.
  Qed.

  Lemma invariant_Add_HasRef_elim:
    forall st A B s2,
    invariant (Add st (HasRef A B s2)) ->
    invariant st /\ (forall s1, In st (HasType B s1) -> s1 <:: s2).
  Proof.
    intros st A B s2 HInv.
    split.
    * intros A' B' s1' s2' HHasRef HHasType.
      eapply HInv.
      - apply Union_introl. eassumption.
      - apply Union_introl. eassumption.
    * intros s1' HIn.
      eapply HInv.
      - apply Union_introl. eassumption.
      - apply Union_intror. constructor.
  Qed.

  Lemma invariant_Change_HasType:
    forall st A s1 s2,
    invariant (Add st (HasType A s1)) ->
    (forall B s3, In st (HasRef B A s3) -> s1 <:: s3 -> s2 <:: s3) ->
    invariant (Add st (HasType A s2)).
  Proof.
    intros st A s1 s2 Hinv Himp.
    apply invariant_Add_HasType_elim in Hinv as [Hinv HA].
    apply invariant_Add_HasType.
    * apply Hinv.
    * intros B s3 HHasRef.
      eapply Himp.
      - apply HHasRef.
      - eapply HA. apply HHasRef.
  Qed.

  Lemma invariant_Change_HasRef:
    forall st A B s1 s2,
    invariant (Add st (HasRef A B s1)) ->
    (forall s3, In st (HasType B s3) -> s3 <:: s1 -> s3 <:: s2) ->
    invariant (Add st (HasRef A B s2)).
  Proof.
    intros st A B s1 s2 Hinv Himp.
    apply invariant_Add_HasRef_elim in Hinv as [Hinv HA].
    apply invariant_Add_HasRef.
    * apply Hinv.
    * intros s3 HHasType.
      apply Himp.
      - apply HHasType.
      - apply HA. apply HHasType.
  Qed.

  Lemma unique_Add_HasRef:
    forall st A B s,
    unique (Add st (HasRef A B s)) <-> unique st.
  Proof.
    intros st A B s.
    split; intro Huniq.
    * intros A' s1' s2' HType1 HType2.
      eapply Huniq.
      - apply Union_introl. eassumption.
      - apply Union_introl. eassumption.
    * intros A' s1' s2' HType1 HType2.
      inversion HType1; subst; clear HType1;
      inversion HType2; subst; clear HType2.
      - eapply Huniq; eassumption.
      - inversion H0; subst; clear H0.
      - inversion H; subst; clear H.
      - inversion H; subst; clear H.
  Qed.

  Lemma step_preserves_unique:
    forall st1 st2, step st1 st2 -> unique st1 -> unique st2.
  Proof.
    intros st1 st2 Hstep Huniq.
    induction Hstep; name_cases.
    [newService]: {
      intros A' s1' s2' HType1 HType2.
      inversion HType1; subst; clear HType1;
      inversion HType2; subst; clear HType2.
      - eapply Huniq; eassumption.
      - inversion H1; subst; clear H1.
        eapply H in H0. inversion H0.
      - inversion H0; subst; clear H0.
        eapply H in H1. inversion H1.
      - inversion H1; subst; clear H1;
        inversion H0; subst; clear H0.
        reflexivity.
    }
    [evolveService]: {
      intros A' s1' s2' HType1 HType2.
      inversion HType1; subst; clear HType1;
      inversion HType2; subst; clear HType2.
      - eapply Huniq.
        + apply Union_introl. eassumption.
        + apply Union_introl. eassumption.
      - inversion H2; subst; clear H2.
        replace s1' with s1 in *.
        + tauto.
        + eapply Huniq.
          ** apply Union_intror. constructor.
          ** apply Union_introl. assumption.
      - inversion H1; subst; clear H1.
        replace s2' with s1 in *.
        + tauto.
        + eapply Huniq.
          ** apply Union_intror. constructor.
          ** apply Union_introl. assumption.
      - inversion H1; subst; clear H1;
        inversion H2; subst; clear H0.
        reflexivity.
    }
    [learnService]: {
      rewrite unique_Add_HasRef in *.
      assumption.
    }
    [transmitService]: {
      rewrite unique_Add_HasRef in *.
      assumption.
    }
    [hostSubtyping]: {
      rewrite unique_Add_HasRef in *.
      assumption.
    }
  Qed.

  Lemma step_preserves_invariant:
    forall st1 st2, step st1 st2 -> unique st1 -> invariant st1 -> invariant st2.
  Proof.
    intros st1 st2 Hstep Huniq Hinv.
    induction Hstep; name_cases.
    [newService]: {
      apply invariant_Add_HasType.
      - apply Hinv.
      - intros  B s2 HB.
        eapply H in HB.
        inversion HB.
    }
    [evolveService]: {
      eapply invariant_Change_HasType.
      - apply Hinv.
      - intros B s3 HB Hsub.
        apply evolves_correctly in H0.
        eapply service_subtype_trans; eassumption.
    }
    [learnService]: {
      apply invariant_Add_HasRef.
      - apply Hinv.
      - intros s2 HHasType.
        (* Uniqueness of HasType, reflexivity *)
        replace s2 with s.
        + apply service_subtype_refl.
        + eapply Huniq; eassumption.
    }
    [transmitService]: {
      apply invariant_Add_HasRef.
      - apply Hinv.
      - intros s3 HC.
        assert (Hsub : s3 <:: s1) by apply (Hinv _ _ _ _ HC H).
        assert (HSound : StateSound st) by (apply invariant_implies_StateSound; assumption).
        assert (t1 <: t2) by (eapply HSound; apply H0).
        assert (s1 <:: s2) by (eapply compositional;  eassumption).
        eapply service_subtype_trans; eassumption.
    }
    [hostSubtyping]: {
      eapply invariant_Change_HasRef.
      - apply Hinv.
      - intros s3 HB Hsub.
        apply host_subtyping_sound in H.
        eapply service_subtype_trans; eassumption.
    }
  Qed.

  Lemma canonical_soundness: IDLSound.
  Proof.
    intros st Hclos.
    enough (unique st /\ invariant st) by (apply invariant_implies_StateSound; tauto).
    induction Hclos using clos_refl_trans_ind_left.
    - split.
      * intros A s1 s2 Hin1 Hin2. inversion Hin1.
      * intros A B s1 s2 Hin1 Hin2. inversion Hin1.
    - inversion IHHclos. split.
      * eapply step_preserves_unique; eassumption.
      * eapply step_preserves_invariant; eassumption.
  Qed.

End IDL.
