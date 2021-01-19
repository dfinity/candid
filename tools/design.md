# Candid DSL

## Motivation

Candid specifies the API of a canister. We want to provide a declarative DSL to specify how to interpret/generate data
for these APIs. Specifically, we want to automate the following processes:

* QuickTest. Generate test data based on the method signature or service class.
* Upgrade test. Test canister behaves correctly before and after an upgrade.
* E2E test. Writing assertion scripts about multiple canister interactions, like https://intuit.github.io/karate/
* Load/performance test.


logo.did
```
type Statements = opt record { Statement; Statements };
type Statement = variant {
  forward: int;
  home;
  left: int;
  right: int;
  repeat: record { nat; Statements };
};
type Object = variant {
  line: record { end: Coord; start: Coord };
};
type Coord = record { x: int; y: int };
service : {
  clear: () -> ();
  eval: (Statement) -> ();
  fakeEval: (Statement) -> (vec Object, int, int, int) query;
  output: () -> (vec Object, int, int, int) query;
}
```

```
import User "user.did";
forall(100) (age in nat(18,60), name in text("[a-z]{3,6} [a-z]{3,6}")) {
  User.add(record {age=age; name=name});
  assert(User.getAge(name) == opt age);
}
assert(User.count() == 100);
upgrade User;

```
* Import/export data. Transfer external data to the canister.
* Mock canister. Mock method response especially for external canisters.
* UI. Layout the canister API on the web, similar to SwiftUI and Flutter.

## Grammar

```
<exp> ::=
  <val>
  <exp_bin>
  <id> . <name>
  <exp> ( <exp>,* )
  let <id> = <exp> in <exp>
  assert <exp>
<imp> ::= import <id> <text>
<prog> ::=
  <imp>;* <exp>;*

```
