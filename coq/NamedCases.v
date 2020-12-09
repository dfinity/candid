(** Fun stuff trying to emulate Isar-style case names *)

Inductive CaseName := CaseNameI.

Existing Class CaseName.
Existing Instance CaseNameI.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Default Proof Mode "Classic".
Ltac name_cases := ltac2:(
  (* Horribly manual string manipulations. Does this mean I should
     go to the Ocaml level?
  *)
  let strcpy s1 s2 o :=
    let rec go := fun n =>
      match Int.lt n (String.length s2) with
      | true => String.set s1 (Int.add o n) (String.get s2 n); go (Int.add n 1)
      | false => ()
      end
    in go 0
  in
  let concat := fun s1 s2 => 
    let l := Int.add (Int.add (String.length s1) (String.length s2)) 1 in
    let s := String.make l (Char.of_int 95) in
    strcpy s s1 0;
    strcpy s s2 (Int.add (String.length s1) 1);
    s
  in
  Control.enter (let rec go () :=
    lazy_match! goal with
    | [ h1 : CaseName, h2 : CaseName |- _ ] =>
      (* Multiple case names? Combine them (and recurse) *)
      let h := concat (Ident.to_string h1) (Ident.to_string h2) in
      Std.clear [h1; h2];
      let h := Option.get (Ident.of_string h) in
      assert ($h := CaseNameI);
      go ()
    | [ _ : CaseName |- _ ] =>
      (* A single case name? Set current goal name accordigly. *)
      ltac1:(
        (* How to do this in ltac2? *)
        lazymatch goal with
        | [ H : CaseName |- _ ] => refine ?[H]; clear H
        end
      )
    | [ |- _ ] =>
      Control.backtrack_tactic_failure "Did not find any CaseName hypotheses"
    end
  in go)
).

(* To be used instead of constructor when the first assumption is 
   one of those CaseName assumptions *)
Ltac clear_names := try exact CaseNameI.
Ltac named_constructor  := constructor; [ exact CaseNameI | idtac .. ].
Ltac named_econstructor := econstructor; [ exact CaseNameI | idtac .. ].

Notation "'case' x , t" := (forall {x : CaseName}, t) (at level 200).

Section Example.

  Inductive Test :=
    | Foo: case foo, Test
    | Bar: case bar, Test.
  
  Goal Test -> Test.
    intros.
    destruct H; name_cases.
    [foo]: {
      named_constructor.
    }
    [bar]: {
      named_constructor.
    }
  Qed.
  
  Goal Test -> Test -> Test.
    intros.
    destruct H; destruct H0; name_cases.
    Show Existentials.
    [foo_foo0]: {
      named_constructor.
    }
    [foo_bar]: {
      named_constructor.
    }
    [bar_foo]: {
      named_constructor.
    }
    [bar_bar0]: {
      named_constructor.
    }
  Qed.


  Goal Test -> Test -> Test -> Test.
    intros.
    destruct H; destruct H0; destruct H1; name_cases.
    [foo_foo0_bar]: {
      named_constructor.
    }
    [foo_bar_foo0]: {
      named_constructor.
    }
    * named_constructor.
    * named_constructor.
    * named_constructor.
    * named_constructor.
    * named_constructor.
    * named_constructor.
  Qed.

  Goal True.
    (* The tactic fails if it does not find case names *)
    Fail name_cases.
  Abort.

End Example.

Require Import Coq.Lists.List.
Section Example2.
  (* From https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html *)

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
  
  Lemma palindrome_star_of_two:
    forall T (s : list T) a b,
    Palindrome s -> s =~ Star (App (Char a) (Char b)) ->
    s = [] \/ a = b.
  Proof.
    intros T s x y  HPalin HRe.
    induction HPalin; inversion HRe; name_cases.
    Show Existentials.
    [emptyP_star0]: {
      left. reflexivity.
    }
    [emptyP_starApp]: {
       left. reflexivity.
    }
    [singletonP_starApp]: {
      inversion HRe; clear HRe.
      inversion H5; clear H5.
      inversion H10; clear H10.
      inversion H11; clear H11.
      subst.
      inversion H3.
    }
    [growP_starApp]: {
      admit.
    }
  Admitted.
End Example2.   
