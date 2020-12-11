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
