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

End IDL.