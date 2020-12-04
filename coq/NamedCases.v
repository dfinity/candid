(** Fun stuff trying to emulate Isar-style case names *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Default Proof Mode "Classic".

Inductive CaseName := CaseNameI.

Existing Class CaseName.
Existing Instance CaseNameI.

Require Import Coq.Strings.String.
Import StringSyntax.


(* Horribly manual string manipulations *)
Ltac2 strcpy := fun s1 s2 o =>
    let rec go := fun n =>
      match Int.lt n (String.length s2) with
      | true => String.set s1 (Int.add o n) (String.get s2 n); go (Int.add n 1)
      | false => ()
      end
    in go 0.
Ltac2 concat := fun s1 s2 => 
    let l := Int.add (Int.add (String.length s1) (String.length s2)) 1 in
    let s := String.make l (Char.of_int 95) in
    strcpy s s1 0;
    strcpy s s2 (Int.add (String.length s1) 1);
    s.

(* Combines the names of hyptheses of type CaseName *)
(* Writen in Ltac2 because I could not mangle identifier names in Ltac1 *)
Ltac2 rec combine_case_names () :=
  repeat (lazy_match! goal with
  | [ h1 : CaseName, h2 : CaseName |- _ ] =>
    let h := concat (Ident.to_string h1) (Ident.to_string h2) in
    (* Message.print (Message.of_string h); *)
    let h := Option.get (Ident.of_string h) in
    Std.clear [h1; h2];
    assert ($h : CaseName) by apply CaseNameI
  | [ |- _ ] => fail
  end).

(* Removes all CaseName hypotheses, and renames the goal based on their names *)
(* Writen in Ltac1 because I could not figure ou thow to use refine in Ltac2 *)
Ltac name_cases := 
  [> (
    ltac2:(combine_case_names ());
    lazymatch goal with
    | [ H : CaseName |- _ ] => refine ?[H]; clear H
    | _ => idtac "Could not find a CaseName assumption"; fail
    end
  )..].

(* To be used instead of constructor when the first assumption is 
   one of those CaseName assumptions *)
Ltac named_constructor :=
  constructor;[ apply CaseNameI | idtac .. ].
Ltac named_econstructor :=
  econstructor;[ apply CaseNameI | idtac .. ].

Notation "'case' x , t" := (forall x : CaseName, t)
  (at level 200).

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
    Show Existentials.
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

End Example.