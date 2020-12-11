(*
A demo of the NamedCases machinery.

This builds on an example from
https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
and is also explained in
https://www.joachim-breitner.de/blog/777-Named_goals_in_Coq
*)

Require Import candid.NamedCases.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive reg_exp (T : Type) : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp T)
| Union (r1 r2 : reg_exp T)
| Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty:
    case empty,
    [] =~ EmptyStr
  | MChar:
    case char,
    forall x,
    [x] =~ (Char x)
  | MApp:
    case app,
    forall s1 re1 s2 re2
    (H1 : s1 =~ re1)
    (H2 : s2 =~ re2),
    (s1 ++ s2) =~ (App re1 re2)
  | MUnionL:
    case unionL,
    forall s1 re1 re2
    (H1 : s1 =~ re1),
    s1 =~ (Union re1 re2)
  | MUnionR:
    case unionR,
    forall re1 s2 re2
    (H2 : s2 =~ re2),
    s2 =~ (Union re1 re2)
  | MStar0:
    case star0,
    forall re,
    [] =~ (Star re)
  | MStarApp:
    case starApp,
    forall s1 s2 re
    (H1 : s1 =~ re)
    (H2 : s2 =~ (Star re)),
    (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Lemma star_app0: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
   generalize dependent s2.
  induction H1.
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre' as Heqre''. intros s H. apply H.
  - (* MStarApp *)
    injection Heqre' as Heqre''.
    intros s3 H1. rewrite <- app_assoc.
    apply MStarApp.
    + trivial.
    + apply H1_.
    + apply IHexp_match2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.

Lemma star_app2: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
   generalize dependent s2.
  induction H1; name_cases; try discriminate.
  [starApp]: {
    injection Heqre' as Heqre''.
    intros s3 H1. rewrite <- app_assoc.
    apply MStarApp; clear_names.
    + apply H1_.
    + apply IHexp_match2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
   }
  [star0]: {
    injection Heqre' as Heqre''. intros s H. apply H.
  }
Qed.

Inductive Palindrome {T} : list T -> Prop :=
| EmptyPalin:
  case emptyP,
  Palindrome []
| SingletonPalin:
  case singletonP,
  forall x,
  Palindrome [x]
| GrowPalin:
  case growP,
  forall l x,
  Palindrome l -> Palindrome ([x] ++ l ++ [x])
.

Lemma snoc_app_right:
  forall T (s : list T) re,
  s =~ Star re ->
  s = [] \/ (exists s1 s2, s = s1 ++ s2 /\ s1 =~ Star re /\ s2 =~ re).
Proof.
  intros T s re H.
  remember (Star re) as re'.
  rewrite Heqre'.
  revert re Heqre'.
  induction H;
    intros re' Heq;
    inversion Heq; subst; clear Heq;
    name_cases;
    try (left; reflexivity).
  [starApp]: {
    clear IHexp_match1.
    specialize (IHexp_match2 re' eq_refl).
    destruct IHexp_match2.
    - subst.
      right.
      exists []. eexists s1.
      repeat split; try assumption.
      rewrite app_nil_r. reflexivity.
    - right.
      inversion H1 as [s3 [s4 [He1 [Hre1 Hre2]]]]; subst; clear H1.
      exists (s1 ++ s3). exists s4.
      repeat split; try assumption.
      + rewrite app_assoc. reflexivity.
      + named_constructor; assumption.
   }
Qed.

Lemma app_char_char:
  forall T (x y : T) s,
  s =~ App (Char x) (Char y) -> s = [x;y].
Proof.
  intros.
  inversion H; subst; clear H.
  inversion H3; subst; clear H3;
  inversion H4; subst; clear H4;
  reflexivity.
Qed.

Lemma palindrome_star_of_two:
  forall T (s : list T) a b,
  Palindrome s -> s =~ Star (App (Char a) (Char b)) ->
  s = [] \/ a = b.
Proof.
  intros T s x y  HPalin HRe.
  inversion HPalin; inversion HRe; subst; clear HRe; name_cases;
    try intuition congruence.
  [singletonP_starApp]: {
    apply app_char_char in H2; subst.
    inversion H0.
  }
  [growP_starApp]: {
    right.
    apply app_char_char in H2; subst.
    eapply snoc_app_right in H4.
    inversion H4; subst; clear H4.
    * rewrite app_nil_r in H3. destruct l; inversion H3; subst; try reflexivity.
      symmetry in H4.
      apply app_eq_nil in H4.
      intuition congruence.
    * inversion H0 as [s3 [s4 [He1 [Hre1 Hre2]]]]; subst; clear H0.
      apply app_char_char in Hre2; subst.
      simpl in H3.
      inversion H3; subst; clear H3.
      apply (f_equal (@rev T)) in H2; simpl in *.
      repeat rewrite ! rev_app_distr in H2; simpl in *.
      congruence.
  }
Qed.