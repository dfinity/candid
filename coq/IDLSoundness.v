(* This tries to formalize 
   https://github.com/dfinity/candid/blob/master/spec/IDL-Soundness.md
 *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Odd that this is needed, see
   https://www.reddit.com/r/Coq/comments/bmslyy/why_doesnt_ensemble_functions_in_coqs_standard/emzazzd
*)
Require Import Coq.Sets.Ensembles.
Arguments In {U}.
Arguments Add {U}.
Arguments Empty_set {U}.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Set Bullet Behavior "Strict Subproofs".
 
Section IDL.

  (* An abstract theory of IDLs is parametrized as follows: *)
  
  (* Argument or result types *)
  Variable T : Set.
  
  (* A service type is a pair of types *)
  Definition S : Set := (T * T).
  Notation "t1 --> t2" := (t1, t2) (at level 80, no associativity).
  
  (* The prediates of the theory *)
  Variable decodesAt : T -> T -> Prop.
  Notation "t1 <: t2" := (decodesAt t1 t2) (at level 70, no associativity).
  
  Variable passesThrough : S -> T -> S -> T -> Prop.
  Notation "s1 ∈ t1 <: s2 ∈ t2" := (passesThrough s1 t1 s2 t2)
    (t1 at level 50, s2 at level 50, at level 70, no associativity).
  
  Variable evolves : S -> S -> Prop.
  Notation "s1 ~> s2" := (evolves s1 s2) (at level 70, no associativity).
  
  Variable hostSubtyping : S -> S -> Prop.
  Notation "s1 <<: s2" := (hostSubtyping s1 s2) (at level 70, no associativity).

  (* Service Identifiers *)
  Variable I : Set.

  (* Judgements *)  
  Inductive Assertion : Set :=
    | HasType : I -> S -> Assertion
    | HasRef : I -> I -> S -> Assertion.

  Definition State := Ensemble Assertion.
  
  Definition FreshIn (i : I) (st : State) : Prop :=
    (forall s, ~ In st (HasType i s)) /\
    (forall i' s, ~ In st (HasRef i i' s)) /\
    (forall i' s, ~ In st (HasRef i' i s)).
  
  Inductive CanSend : State -> I -> T -> T -> I -> Prop :=
    | CanCall: forall st A B t1 t1' t2 t2',
      In st (HasRef A B (t1 --> t1')) ->
      In st (HasType B (t2 --> t2')) ->
      CanSend st A t1 t2 B
    | CanReply: forall st A B t1 t1' t2 t2',
      In st (HasRef B A (t1 --> t1')) ->
      In st (HasType A (t2 --> t2')) ->
      CanSend st A t2' t1' B.
      
  Inductive step : State -> State -> Prop :=
    | NewService :
      forall (i : I) (s : S) st,
      FreshIn i st ->
      step st (Add st (HasType i s))
    | EvolveService :
      forall (i : I) (s1 s2 : S) st,
      ~ In st (HasType i s1) ->
      s1 ~> s2 ->
      step (Add st (HasType i s1)) (Add st (HasType i s2))
    | LearnService :
      forall (i1 i2 : I) (s: S) st,
      In st (HasType i1 s) ->
      step st (Add st (HasRef i2 i1 s))
    | TransmitService :
      forall (A B C : I) (s1 s2 : S) (t1 t2 : T) st,
      In st (HasRef A C s1) ->
      CanSend st A t1 t2 B ->
      (s1 ∈ t1 <: s2 ∈ t2) ->
      step st (Add st (HasRef B C s2))
    | HostSubtyping :
      forall (A B : I) (s1 s2 : S) st,
      s1 <<: s2 ->
      step (Add st (HasRef A B s1)) (Add st (HasRef A B s2))
    .

  Definition StateSound (st : State) : Prop :=
    forall A t1 t2 B, CanSend st A t1 t2 B ->  t1 <: t2.

  Definition IDLSound : Prop :=
    forall s, clos_refl_trans _ step Empty_set s -> StateSound s.
    
   (* Now we continue with the soundness proof for canonical subtyping.
      TODO: Modularize this development, instead of continuing in the same Section *)
     
    Hypothesis decodesAt_refl: reflexive _ decodesAt.
    Hypothesis decodesAt_trans: transitive _ decodesAt.

    Variable service_subtyping : S -> S -> Prop.
    Notation "s1 <:: s2" := (service_subtyping s1 s2) (at level 70, no associativity).
    Hypothesis service_subtype_sound:
     forall t1 t1' t2 t2',
       (t1 --> t1') <:: (t2 --> t2') ->
       t1' <: t2' /\ t2 <: t1.

    Hypothesis evolves_correctly:
     forall s1 s2, s2 <:: s1 -> s1 ~> s2.
    Hypothesis compositional:
      forall t1 t2 s1 s2,
      t1 <: t2 -> s1 ∈ t1 <: s2 ∈ t2 -> s1 <:: s2.
    Hypothesis host_subtyping_sound:
     forall s1 s2, s2 <<: s1 -> s1 <:: s2.
    
    Definition invariant (st : State) :=
       forall A B s1 s2,
       In st (HasType A s1) -> In st (HasRef B A s2) -> s1 <:: s2 .
    
    Lemma invariant_implies_StateSound:
      forall st, invariant st -> StateSound st.
    Proof.
      intros st Hinvariant.
      intros A t1 t2 B HCanSend.
      destruct HCanSend.
      * pose proof (Hinvariant B A (t2 --> t2') (t1 --> t1') H0 H) as H1.
        apply service_subtype_sound in H1.
        apply H1.
      * pose proof (Hinvariant A B (t2 --> t2') (t1 --> t1') H0 H) as H1.
        apply service_subtype_sound in H1.
        apply H1.
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

    Lemma invariant_is_invariant:
      forall st1 st2, step st1 st2 -> invariant st1 -> invariant st2.
    Proof.
      intros st1 st2 Hstep Hinv.
      induction Hstep.
      * (* NewService *)
        apply invariant_Add_HasType.
        - apply Hinv.
        - intros  B s2 HB.
          eapply H in HB.
          inversion HB.
      * (* EvolveService *) 
        admit.
      * (* LearnService *)
        apply invariant_Add_HasRef.
        - apply Hinv.
        - intros s2 HHasType.
          (* Uniqueness of HasType, reflexivity *)
          admit.
      * (* TransmitService *) 
        apply invariant_Add_HasRef.
        - apply Hinv.
        - intros s3 HC.
        admit.
      * (* HostSubtyping *)
        apply invariant_Add_HasRef.
        - admit.
        - intros s3 HB.
          admit.
    Admitted.


End IDL.