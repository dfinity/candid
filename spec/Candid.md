# Candid Specification

Version: 0.1.3

Date: February 3, 2021

## Motivation

To document, discover, and interact with _canisters_ (also known as _services_ or _actors_) on the Internet Computer, we need an interface description language (IDL) for specifying the signature of a canister.

#### Goals:

* Language-independent description of canister interfaces and the data they
exchange (names, parameter and result formats of service methods)
* Simple and canonical constructs (C-like; algebraically: sums, products, exponentials)
* Extensible, backwards-compatible
* Well-formedness is checkable and guaranteed by the platform
* Human-readable and machine-readable
* Declarative, usable as input to binding code generators

#### Non-Goals:

* Specification of semantic constraints beyond representation concerns
  (Rationale: (1) there is no natural boundary to what should be expressible, a scalable solution would quickly lead into the realm of program logics and/or dependent types; (2) cost and complexity for the platform, the hypervisor would have to check and guarantee these properties on every message send; (3) in general, interesting properties cannot be formulated or checked without contextual information such as a canister’s state.)
* Prescribing the wire format used internally by the network to transport data (though it will make sense to use an extension of the serialisation format decribed, which is fairly generic)

#### Inspiration:

* Protocol buffers
* Thrift
* Fuchsia IDL
* CORBA
* JSON, YAML
* ...
* Fisher, Mandelbaum, Walker: The next 700 data description languages

#### Why not Protocol Buffers or others?

Vanilla protocol buffers are not sufficient or well-suited for describing canisters on the Internet Computer:

* They are primarily a *data description language*, not an IDL. There is syntax for defining "services", but it assumes RPCs not messaging and requires developing a plugin (replacing the gRPC a.k.a. Stubby one) to provide semantics.

* They deserialise data into abstract protobuf objects, not actual language data structures. The "message" (a.k.a. objects/records/structs) format is designed to be represented as its own abstract in-memory type.

* They are an inherently first-order data format, i.e., cannot describe functions/callbacks or object/actor parameters with methods.

* They lack various data types that we want to be able to handle, such as proper arrays, big nums, variants, references.

* They provide no place to express other information we might need to incorporate into IDL descriptions, such as "read-onlyness" or access control specifications.

* They do not have a semantically sound and compositional foundation for defining safe upgradability (e.g., as a relation on interface types).

* They do have a number of features we do not need, or may want to define differently.

Given all of the above, I expect there would be fairly little we would be able to reuse from existing protobuf bindings. At the same time, there would be no easy way to incorporate various extensions we require.


## Type Structure

The purpose of an IDL is defining the signature, and thereby the *type* of an actor (service), that is, the set of messages and their parameter and result types. To that end, the grammar for Candid consists mostly of a type grammar.

#### Core Grammar

This is a summary of the grammar proposed:
```
<prog>  ::= <def>;* <actor>;?
<def>   ::= type <id> = <datatype> | import <text>
<actor> ::= service <id>? : (<tuptype> ->)? (<actortype> | <id>)

<actortype> ::= { <methtype>;* }
<methtype>  ::= <name> : (<functype> | <id>)
<functype>  ::= <tuptype> -> <tuptype> <funcann>*
<funcann>   ::= oneway | query
<tuptype>   ::= ( <argtype>,* )
<argtype>   ::= <datatype>
<fieldtype> ::= <nat> : <datatype>
<datatype>  ::= <id> | <primtype> | <comptype>
<comptype>  ::= <constype> | <reftype>

<primtype>  ::=
  | <numtype>
  | bool
  | text
  | null
  | reserved
  | empty
  | principal

<numtype>  ::=
  | nat | nat8 | nat16 | nat32 | nat64
  | int | int8 | int16 | int32 | int64
  | float32 | float64

<constype>  ::=
  | opt <datatype>
  | vec <datatype>
  | record { <fieldtype>;* }
  | variant { <fieldtype>;* }

<reftype>  ::=
  | func <functype>
  | service <actortype>

<name> ::= <id> | <text>
```
See [below](#values) for the definitions of `<id>`, `<nat>`, and `<text>`.


#### Syntactic Shorthands

In addition to this basic grammar, a few syntactic shorthands are supported that can be reduced to the basic forms:

```
<argtype>  ::= ...
  | <name> : <datatype>    := <datatype>

<constype> ::= ...
  | blob                   :=  vec nat8

<fieldtype> ::= ...
  | <name> : <datatype>    :=  <hash(name)> : <datatype>
  | <datatype>             :=  N : <datatype>  where N is either 0 or previous + 1  (only in records)
  | <nat>                  :=  <nat> : null   (only in variants)
  | <name>                 :=  <name> : null  (only in variants)
```

#### Comments

Comments can be given as either single-line or block form:
```
<comment> ::=
  | //<codepoint>*<nl>
  | /*(<codepoint>|<comment>)*/
```
Block comments nest properly (unlike in C).


### Services

A *service* is a standalone actor on the platform that can communicate with other services via sending and receiving *messages*. Messages are sent to a service by invoking one of its *methods*, i.e., functions that the service provides.

For the main service, there are two kinds of services: service constructor (or uninitialized service) and running service (or initialized service).
A service constructor takes *initialization parameters* for installing the service on the platform. Once it is initialized, the service becomes a running service. We can initialize a service constructor to multiple running services.

**Note:** Candid is in fact agnostic to the exact nature of services. In particular, it could be applied to a setting where services are synchronous (objects with RPCs) instead of asynchronous (actors with bidirectional message sends).


#### Structure

A service's signature is described by an *actor type*, which defines the list of *methods* that the service provides. Each method is described by its *name* and a *function type* describing its signature. The function type can also be given by referring to a type definition naming a function reference type.

```
<actortype> ::= { <methtype>;* }
<methtype>  ::= <name> : (<functype> | <id>)
```
We identify `<methtype>` lists in an actor type up to reordering.


#### Names

A name is given either in the syntax of a typical programming language identifier, or as an arbitrary string in quotes:
```
<name> ::= <id> | <text>
<id>   ::= (A..Z|a..z|_)(A..Z|a..z|_|0..9)*
<text> ::= "<char>*"
```
Identifiers cannot be keywords of the Candid grammar. In case a name is needed that coincides with a keyword, it has to be quoted as a text string.


#### Example
```
service : {
  addUser : (name : text, age : nat8) -> (id : nat64);
  userName : (id : nat64) -> (text) query;
  userAge : (id : nat64) -> (nat8) query;
  deleteUser : (id : nat64) -> () oneway;
}
```


### Functions

*Functions* are endpoints for communication.   A typical function invocation is a bidirectional communication, with *parameters* and *results*, a.k.a. request and response. A `oneway` function invocation is a uni-directional communication with zero or more parameters but no results, intended for fire-and-forget scenarios.

**Note:** Candid is in fact agnostic to the question of whether communication via functions is synchronous (like RPCs) or asynchronous (like messaging with callbacks as response continuations). However, it assumes that all invocations have the same semantics, i.e., there is no need to distinguish between both.

**Note:** In a synchronous interpretation of functions, invocation of a oneway function would return immediately, without waiting for completion of the service-side invocation of the function. In an asynchronous interpretation of functions, the invocation of a `oneway` function does not accept a callback (to invoke on completion).

#### Structure

A function type describes the list of parameters and results and their respective types. It can optionally be annotated to be *query*, which indicates that it does not modify any state and can potentially be executed more efficiently (e.g., on cached state). (Other annotations may be added in the future.)

```
<functype> ::= ( <argtype>,* ) -> ( <argtype>,* ) <funcann>*
<funcann>  ::= oneway | query
<argtype>  ::= <datatype>
```
We identify `<funcann>` lists in a function type up to reordering.

The list of parameters must be shorter than 2^32 values;
the same restriction apply to the result list.
The result list of a `oneway` function must be empty.


##### Shorthand: Named Parameters and Results

As a "shorthand", the types of parameters and results in a function type may be prefixed by a name:
```
<argtype> ::= <name> : <datatype>   := <datatype>
```
The chosen names only serve documentation purposes and have no semantic significance.
However, duplicate names are not allowed.


#### Example
```
(text, text, nat16) -> (text, nat64)
(name : text, address : text, nat16) -> (text, id : nat64)
(name : text, address : text, nr : nat16) -> (nick : text, id : nat64)
```
All three types are equivalent.


### Data

The content of message arguments and results is *data*. Three basic forms of *data types* can be distinguished: *primitive data*, which are basic values, and *constructed data*, which are compound forms of data types, and *references*, which point to a resource in the network.

```
<datatype>  ::= <primtype> | <constype> | <reftype>
```


### Primitive Data

*Primitive types* describe the possible forms of primitive data.

The primitive types that describe numbers are separated out in the grammar:
```
<primtype> ::= <numtype> | ...
```

#### Natural Numbers

The type `nat` describes a natural number (unsigned integer) of unlimited range. There are also variants limited to 8, 16, 32, or 64 bit value range with fixed-size representations.

```
<numtype> ::= nat | nat8 | nat16 | nat32 | nat64 | ...
```
**Note:** Values of type `nat` have variable length representations in the  binary serialisation format, and hence take up space proportional to (the logarithm of) their value. As long as typical values are small, they may hence be more space-efficient than the fixed size types.

#### Integer Numbers

The type `int` describes an integer number (signed) of unlimited range. There are also variants limited to 8, 16, 32, or 64 bit value range with fixed-size representations.

```
<numtype> ::= ... | int | int8 | int16 | int32 | int64 | ...
```
**Note:** Values of type `nat` have variable length representations in the binary serialisation format, and hence take up space proportional to (the logarithm of) their value. As long as typical values are small, they may hence be more space-efficient than the fixed size types.

#### Floating-Point Numbers

Floating-point values are represented in IEEE 754 binary format and are supported in single precision (32 bit) and double precision (64 bit).

```
<numtype> ::= ... | float32 | float64
```

#### Boolean

Boolean truth values are represented by the type `bool`.
```
<primtype> ::= ... | bool | ...
```

#### Text

Text strings are represented by the type `text` and consist of a sequence of Unicode scalar values.
```
<primtype> ::= ... | text | ...
```
**Note:** The `text` type is distinguished from `vec nat8` (a UTF-8 string) or `vec nat32` (a sequence of code points) in order to allow bindings to map it to a suitable string type, and enable the binary format to select an efficient internal representation independently.

#### Null

The type `null` has exactly one value (the *null* value) and therefore carries no information. It can e.g. be used as a placeholder for optional fields that ought to be added to a record in future upgrades, or for *variant cases* that do not need any value, see below.
```
<primtype> ::= ... | null | ...
```

#### Reserved

The type `reserved` is a type with unknown content that ought to be ignored. Its purpose is to occupy field ids in records in order to prevent backwards/forwards compatibility problems, see the description of record types below.
```
<primtype> ::= ... | reserved
```
**Note:** This type has a similar role as *reserved fields* in proto buffers.


#### Empty

The type `empty` is the type of values that are not present. Its purpose is to mark variants that are not actually there, or -- as argument types of function reference -- indicate that they will not be called.
```
<primtype> ::= ... | empty
```

### Constructed Data

*Constructed types* describe compound or aggregated forms of values.


#### Options

An *option* is a value of a specific data type that may be absent.
```
<constype>  ::= opt <datatype> | ...
```

#### Vectors

A *vector* is a *homogeneous* sequence of values of the same data type.
```
<constype>  ::= ... | vec <datatype> | ...
```

##### Shorthand: Blobs

A shorthand exists for the specific vector *blob*, which is an arbitrary sequence of bytes:
```
<constype> ::= ....
  | blob   := vec nat8
```

#### Records

A *record* is a *heterogeneous* sequence of values of different data types. Each value is tagged by a *field id* which is a numeric value that has to be unique within the record and carries a single value of specified data type. The order in which fields are specified is immaterial.

```
<constype>  ::= ... | record { <fieldtype>;* } | ...
<fieldtype> ::= <nat> : <datatype>
```
We identify `<fieldtype>` lists in a record type up to reordering.

The id is described as a simple unsigned integer that has to fit the 32 bit value range. It can be given in either decimal or hexadecimal notation:

```
<nat> ::= (0..9)(_? 0..9)* | 0x(0..9|a..f|A..F)(_? 0..9|a..f|A..F)*
```
An id value must be smaller than 2^32 and no id may occur twice in the same record type.


##### Shorthand: Symbolic Field Ids

An id can also be given as a *name*, which is a shorthand for a numeric id that is the hash of that name:
```
<fieldtype> ::= ...
  | <name> : <datatype>    :=  <hash(name)> : <datatype>
```

The purpose of identifying fields by unique (numeric or textual) ids is to support safe upgrading of the record type returned by a function: a new version of a function can safely *add* fields to an old record as long as their id has not been used before. See the discussion on upgrading below for more details.

The hash function is specified as
```
hash(id) = ( Sum_(i=0..k) utf8(id)[i] * 223^(k-i) ) mod 2^32 where k = |utf8(id)|-1
```

This expansion implies that a hash collision between field names within a single record is disallowed.

This hash function has the following useful properties:

 * Collisions are sufficiently rare. It has [no collisions for names up to length 4](https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf).

 * It is rather simple to implement, compared to, say, a cryptographic hash function (we do not need resistence against collision attacks).

The hash function does not have the property that every numeric value can be turned into a human-readable preimage. Host languages that cannot support numeric field names will have to come up with a suitable textual encoding of numeric field names, as well as of field names that are not valid in the host langauge.


##### Shorthand: Tuple Fields

Field ids can also be omitted entirely, which is just a shorthand for picking either 0 (for the first field) or N+1 when the previous field has id N.
```
<fieldtype> ::= ...
  | <datatype>    :=  N : <datatype>
```

##### Examples
```
record {
  name : text;
  street : text;
  num : nat;
  city : text;
  zip : nat;
}

record { nat; nat }
record { 0 : nat; 1 : nat }
```
The latter two records are equivalent.


#### Variants

A *variant* is a tagged union of different possible data types. The tag is given by a numeric id that uniquely determines the variant case. Each case is described as a field. The order in which fields are specified is immaterial.

```
<constype>  ::= ... | variant { <fieldtype>;* } | ...
```
We identify `<fieldtype>` lists in a variant type up to reordering.

A field id must be smaller than 2^32 and no id may occur twice in the same variant type.


##### Shorthand: Symbolic Tag Ids

Like for record fields, the id for a variant tag can also be given as a *name*, which is a shorthand for its hash.

##### Shorthand: Enumeration Types

The type of a variant field can be omitted, in which case it is `null`.
```
<fieldtype> ::= ...
  | <nat>    :=  <nat> : null
  | <name>   :=  <name> : null
```
This abbreviation only applies to variants. At the same time, variants do not allow the tuple field abbreviation for omitting the field id.

##### Example
```
type color = variant { red; green; blue };

type tree = variant {
  leaf : int;
  branch : record {left : tree; val : int; right : tree};
}
```


### References

A third form of value are *references*. They represent first-class handles to (possibly remote) *functions*, *services*, or *principals*.

#### Service References

A *service reference* points to a service and is described by an actor type. Through this, services can communicate connections to other services.

```
<reftype> ::= ... | service <actortype>
```

##### Example

```
type broker = service {
  findCounterService : (name : text) ->
    (service {up : () -> (); current : () -> nat});
}
```

#### Function References

A *function reference* is described by its function type. For example, they allow passing callbacks to other functions.

```
<reftype> ::= func <functype> | ...
```

##### Example

```
type engine = service {
  search : (query : text, callback : func (vec result) -> ());
}
```

#### Principal References

A *principal reference* points to an identity, such as a canister or a user. Through this, we can authenticate or authorize other services or users. Because the type constructor takes no arguments, it is classified as a _primitive_ type.

```
<primtype> ::= ... | principal | ...
```

### Type Definitions

Types can be named via *type definitions*.

```
<def>   ::= type <id> = <datatype>
```

Type definitions are mutually recursive, i.e., they can refer to themselves or each other. However, every type cycle must be productive, i.e., go through a type expression that is not just an identifier. A type definition that is *vacuous*, i.e., is only equal to itself, is not allowed.

##### Examples

```
type stream = opt record {head : nat; next : func () -> stream};
```
```
type node = record {head : nat; tail : list};
type list = opt node;
```
```
type A = B;
type B = A;  // error: cyclic type definition
```


### Imports

In order to allow splitting interface definitions up into multiple files or share common definitions between multiple interfaces, *import* declarations are provided.

```
<def>   ::= ... | import <text>
```

An import refers to another interface file by URL. The semantics is that of textual inclusion, except that definitions from the imported file must not refer to definitions from the importing file.

##### Example

File `A.did`:
```
type A = service { f : () -> () };
```
File `B.did`:
```
import "A.did"
service B : A ;
```

Open Question: Instead of a flat name space, should we require qualified names for imports?


### Interfaces

An *interface description* consists of a sequence of imports and type definitions, possibly followed by a service declaration. A service declaration names and specifies a service actor by specifying an actor type. The actor type may also be given by referring to the name of a type definition for an actor reference type.

```
<desc>  ::= <def>;* <service>;?
<service> ::= service <id>? : (<actortype> | <id>)
```

The optional name given to the service in an interface description is immaterial; it only serves as documentation.


## Values

To enable convenient debugging, the following grammar specifies a text format for values.
The types of these values are assumed to be known from context, so the syntax does not attempt to be self-describing.

```
<val> ::=
  | <primval> | <consval> | <refval>
  | ( <annval> )

<annval> ::=
  | <val>
  | <val> : <datatype>

<primval> ::=
  | <nat> | <int> | <float>
  | <text>
  | true | false
  | null

<consval> ::=
  | opt <val>
  | vec { <annval>;* }
  | record { <fieldval>;* }
  | variant { <fieldval> }

<fieldval> ::= <nat> = <annval>

<refval> ::=
  | service <text>             (canister URI)
  | func <text> . <name>       (canister URI and message name)
  | principal <text>           (principal URI)

<arg> ::= ( <annval>,* )

<letter> ::= A..Z | a..z
<digit>  ::= 0..9
<id>     ::= (<letter> | _)(<letter> | <digit> | _)*

<sign>   ::= + | -
<hex>    ::= <digit> | A..F | a..f
<num>    ::= <digit>(_? <digit>)*
<hexnum> ::= <hex>(_? <hex>)*
<nat>    ::= <num> | 0x<hexnum>
<int>    ::= <sign>? <num>
<float>  ::=
  | <sign>? <num> . <num>?
  | <sign>? <num> (. <frac>?)? (e | E) <sign>? <num>
  | <sign>? 0x<hexnum> . <hexnum>?
  | <sign>? 0x<hexnum> (. <hexnum>?)? (p | P) <sign>? <num>

<text>   ::= " <char>* "
<char>   ::=
  | <utf8>
  | \ <hex> <hex>
  | \ <escape>
  | \u{ <hexnum> }
<escape>  ::= n | r | t | \ | " | '
<utf8>    ::= <ascii> | <utf8enc>
<ascii>   ::= '\20'..'\7e' except " or \
<utf8enc> ::=
  | '\c2'..'\df' <utf8cont>
  | '\e0' '\a0'..'\bf' <utf8cont>
  | '\ed' '\80'..'\9f' <utf8cont>
  | '\e1'..'\ec' <utf8cont> <utf8cont>
  | '\ee'..'\xef' <utf8cont> <utf8cont>
  | '\f0' '\90'..'\bf' <utf8cont> <utf8cont>
  | '\f4' '\80'..'\8f' <utf8cont> <utf8cont>
  | '\f1'..'\f3' <utf8cont> <utf8cont> <utf8cont>
<utf8cont> ::= '\80'..'\bf'
```
A `<char>` is a *Unicode scalar value* (i.e., a codepoint that is not a surrogate part).


#### Syntactic Shorthands

Analoguous to types, a few syntactic shorthands are supported that can be reduced to the basic value forms:

```
<consval> ::= ...
  | blob <text>            := vec { N;* }  where N;* is the sequence of bytes in the string, interpreted [as in the WebAssembly textual format](https://webassembly.github.io/spec/core/text/values.html#strings)

<fieldval> ::= ...
  | <name> = <annval>      :=  <hash(name)> = <annval>
  | <annval>               :=  N = <annval>  where N is either 0 or previous + 1  (only in records)
  | <nat>                  :=  <nat> = null   (only in variants)
  | <name>                 :=  <name> = null  (only in variants)
```


## Upgrading and Subtyping

Interfaces are allowed to evolve over time in a manner that is *robust*, i.e., cannot break existing client code. To capture this notion precisely, a service of type `T` is *upgradable* to a version with another type `T'` if and only if `T'` is a *structural subtype* of `T`, written `T' <: T`. This relation expresses that `T'` is more *specialised* than `T`. (Note: A more specialised type is less general, i.e., denotes a smaller set of possible values, thus the direction of the subtype ordering, even though a subtype record can have *more* fields.)

For upgrading data structures passed between service and client, it is important to distinguish the direction in which the data flows, as the upgrading requirements are opposite to each other:

* *Outbound* data returned from service to client as message results is *provided* by the service; an upgrade may provide *more* or more refined data without breaking clients. For example, an outbound record may provide additional fields after an upgrade.

* *Inbound* data passed from client to service as message parameters is *required* by the service; an upgrade may only require *less* or less specific data without breaking clients. For example, an inbound record may require fewer fields after an upgrade.

That is, outbound message results can only be replaced with a subtype (more fields) in an upgrade, while inbound message parameters can only be replaced with a supertype (fewer fields). This corresponds to the notions of co-variance and contra-variance in type systems.

Subtyping applies recursively to the types of the fields themselves. Moreover, the orientation of subtyping is *inverted* for inbound function and service references, in compliance with standard rules.

In addition to the usual subtyping rules, the subtyping relation has some more unusual rules.
In particular, it also allows fields to be *added* to inbound values (and conversely, removed from outbound ones), as long as they are optional.
Similarly, it allows *removing* cases from inbound values (and conversely, adding them to outbound ones), as long as the variant itself is optional.
In all these cases, a receiver who cannot handle the tag or field will simply see `null`.
This allows for maximal flexibility when evolving an interface over time, while still remaining sound.


### Examples

For example, a representative case is an interface of the following form:
```
// Version 1
type t = {x : nat};
service : {
  produce : () -> t;
  consume : t -> ();
}
```
The subtyping rules allow extending type `t` with additional fields later, as long as they are given optional type:
```
// Version 2
type t = {x : nat; y : opt nat};
service : {
  produce : () -> t;
  consume : t -> ();
}
```
Under normal subtyping rules, this wouldn't be allowed, because such record extension isn't usually compatible (sound) when `t` occurs in inbound position, such as with the `consume` function.
There might be existing clients that are not aware of the new fields, and would fail to provide them.
However, by restricting such fields to option types, and interpreting them as `null` when missing, such a mismatch is bridged.

Such extensibility also extends to *higher-order* examples, where functions themselves become parameters:
```
type t = {x : nat};
service : {
  h1 : (f1 : () -> t) -> ();      // might call f1() and expects a t
  h2 : (f2 : t -> ()) -> ();      // might call f2({x = 5})
}
```
If type `t` is later extended with a new optional field, then an existing client passing some function for `f1` or `f2` that is not yet aware of this change will still work correctly.
This applies at any order, for example, `t` can safely be extended with a new optional field in the following scenario:
```
type t = {x : nat};
type f = t -> ();
type g = () -> t;
service : {
  h : (f, g) -> ();    // might compose f(g())
}
```

### Design Goals

To summarize, the subtyping relation for validating upgrades is designed with the following design goals in mind:

* Soundness: Subtyping implies that deserialisation at a supertype cannot fail.

* Completeness: Subtyping covers all cases of successful deserialisation.

* Transitivity: Subtyping implies that deserialisation cannot fail even across multiple upgrades.

* Record Extensibility: Records are upgradable by adding new (optional) fields, even when they appear in both outbound and inbound positions, such that round-trips always remain possible.

* Higher-order Extensibility: Subtyping extends to higher-order cases, where functions become parameters, so that there is no unique owner for their input/output contract.

* Language Injectivity: Subtyping does not depend on version or role annotations in interfaces that have no counterpart in source languages, i.e., an interface description can be generated from source-level types without special features or cross-version knowledge.

* Simple Deserialisation: Deserialisation does not require (sub)type checks other than the type-directed traversal of the value blob.

* Type Erasure: Deserialised values do not require carrying dynamic type information on the language side. In particular, service and function references can be represented without type information.

* No covert channels: Serialisation never includes any fields in the value that the sender is not aware of. Specifically, when passing on a value to a third party that the sender previously received itself, then that will only contain fields that the sender intends to send out per its type.

However, something has to give, so one seemingly desirable property that is not maintained is *transitive coherence*, i.e., given a value serialized at some type, deserialized and serialized at a supertype, and then again deserialized at a supertype of the supertype may yield a diferent result than deserialised directly at the later supertype.
However, the only possible difference can be one of getting `null` instead of an optional value, or vica versa.


### Rules

#### Primitive Types

Most primitive types cannot be changed in an upgrade.
```

------------------------
<primtype> <: <primtype>
```

An exception are integers, which can be specialised to natural numbers:

```

-----------
nat <: int
```

Additional rules apply to `empty` and `reserved`, which makes these a bottom resp. top type:
```

-------------------------
<datatype> <: reserved


--------------------
empty <: <datatype>
```

#### Vectors

A vector type can be specialised via its constituent type.
```
<datatype> <: <datatype'>
---------------------------------
vec <datatype> <: vec <datatype'>
```

#### Options

An option type can be specialised via its constituent type.
```
<datatype> <: <datatype'>
---------------------------------
opt <datatype> <: opt <datatype'>
```

Furthermore, an option type can be specialised to `null`:
```
------------------------
null <: opt <datatype>
```

It can also be specialised to its constituent type, unless that type is itself optional:

```
not (null <: <datatype'>)
<datatype> <: <datatype'>
-----------------------------
<datatype> <: opt <datatype'>
```
The premise means that the rule does not apply when the constituent type is itself `null`, an option or `reserved`. That restriction is necessary so that there is no ambiguity. For example, otherwise there would be two ways to interpret `null` when going from `opt nat` to `opt opt nat`, either as `null` or as `?null`.

Finally, in order to maintain *transitivity* of subtyping, two unusual rules allow, in fact, *any* type to be regarded as a subtype of an option.
```
not (<datatype> <: opt <datatype'>)
---------------------------------
opt <datatype> <: opt <datatype'>

not (null <: <datatype'>)
not (<datatype> <: <datatype'>)
---------------------------------
opt <datatype> <: opt <datatype'>
```
*Note:* These rules are necessary in the presence of the unusual record and variant rules shown below. Without them, certain upgrades may generally be valid one step at a time, but not taken together, which could cause problems for clients catching up with multiple upgrades.
For example, given a record type `record {666 : opt nat}` it is valid to remove the field `666` by the rule below and evolve the type to `record { 666 : nat }` and then to `record {}`.
A later step might legally re-add a field of the same name but with a different type, producing, e.g.,`record {666 : opt text}`.
A client having missed some of the  intermediate steps will have to upgrade directly to the newest version of the type.
If the type cannot be decoded, its value will be treated as `null`.

In practice, users are strongly discouraged to ever remove a record field or a variant tag and later re-add it with a different meaning. Instead of removing an optional record field, it should be replaced with `opt empty`, to prevent re-use of that field.
However, there is no general way for the type system to prevent this, since it cannot know the history of a type definition.
Consequently, the rule above is needed for technical more than for practical reasons.
Implementations of static upgrade checking are encouraged to warn if this rule is used.


#### Records

In a specialised record type, the type of a record field can be specialised, or a field can be added.
```

---------------------------------------
record { <fieldtype'>;* } <: record { }

<datatype> <: <datatype'>
record { <fieldtype>;* } <: record { <fieldtype'>;* }
----------------------------------------------------------------------------------------------
record { <nat> : <datatype>; <fieldtype>;* } <: record { <nat> : <datatype'>; <fieldtype'>;* }
```

In order to be able to evolve and extend record types that also occur in inbound position (i.e., are used both as function results and function parameters), the subtype relation also supports *removing* fields from records, provided they are optional (or `reserved`).
```
<nat> not in <fieldtype>;*
record { <fieldtype>;* } <: record { <fieldtype'>;* }
opt empty <: <datatype'>
------------------------------------------------------------------------------
record { <fieldtype>;* } <: record { <nat> : <datatype'>; <fieldtype'>;* }
```
*Note:* This rule is unusual from a regular subtyping perspective, but necessary in practice.
Together with the previous rule, it allows extending any record with optional fields in an upgrade, regardless of how it is used.
Any party not aware of the extension will treat the field as `null`.


#### Variants

For a specialised variant, the type of a tag can be specialised, or a tag can be removed.
```

-----------------------------------------
variant { } <: variant { <fieldtype'>;* }

<datatype> <: <datatype'>
variant { <fieldtype>;* } <: variant { <fieldtype'>;* }
------------------------------------------------------------------------------------------------
variant { <nat> : <datatype>; <fieldtype>;* } <: variant { <nat> : <datatype'>; <fieldtype'>;* }
```

*Note:* By virtue of the rules around `opt` above, it is possible to evolve and extend variant types that also occur in outbound position (i.e., are used both as function results and function parameters) by *adding* tags to variants, provided the variant itself is optional (e.g.  `opt variant { 0 : nat; 1 : bool } <: opt variant { 1 : bool }`). Any party not aware of the extension will treat the new case as `null`.


#### Functions

For a specialised function, any parameter type can be generalised and any result type specialised. Moreover, arguments can be dropped while results can be added. That is, the rules mirror those of tuple-like records, i.e., they are ordered and can only be extended at the end.
```
record { (N1' : <datatype1'>);* } <: record { (N1 : <datatype1>);* }
record { (N2 : <datatype2>);* } <: record { N2' : <datatype2'>);* }
-------------------------------------------------------------------------------------------------------------------
func ( <datatype1>,* ) -> ( <datatype2>,* ) <funcann>* <: func ( <datatype1'>,* ) -> ( <datatype2'>,* ) <funcann>*
```
where `NI*` is the `<nat>` sequence `1`..`|<datatypeNI>*|`, respectively.

Viewed as sets, the annotations on the functions must be equal.


#### Services

For a service, a method can be specialised (by specialising its function type), or a method added. Essentially, they are treated like records of functions.
```

----------------------------------------
service { <methtype'>;* } <: service { }

<functype> <: <functype'>
service { <methtype>;* } <: service { <methtype'>;* }
------------------------------------------------------------------------------------------------
service { <name> : <functype>; <methtype>;* } <: service { <name> : <functype'>; <methtype'>;* }
```

### Coercion

This subtyping is implemented during the deserialisation of Candid at an expected type. As described in [Section Deserialisation](#deserialisation), the binary value is conceptually first _decoded_ into the actual type and a value of that type, and then that value is _coerced_ into the expected type.

To model this, we define, for every `t1, t2` with `t1 <: t2`, a function `C[t1<:t2] : t1 -> t2`. This function maps values of type `t1` to values of type `t2`, and is indeed total.

to describe these values, we re-use the syntax of the textual representation, and use the the `<annval>` syntax (i.e. `(v : t)`) if necessary to resolve overloading.

#### Primitive Types

On primitve types, coercion is the identity:
```
C[<t> <: <t>](x) = x    for every <t> ∈ <numtype>, bool, text, null
```

Values of type `nat` coerce at type `int`:
```
C[nat <: int](<nat>) = <nat>
```

Coercion into `reserved` is the constant map (this is arbitrarily using `null` as “the” value of `reserved`):
```
C[<t> <: reserved](_) = null
```
NB: No rule is needed for type `empty`, because there are no values of that type. By construction, `C[empty <: <t>]` is the unique function on the empty domain.

#### Vectors

Vectors coerce pointwise:
```
C[vec <t> <: vec <t'>]( vec { <v>;* } ) = vec { C[<t> <: <t'>](<v>);* }
```

#### Options

The null type and the reserved type coerce into any option type:
```
C[null <: opt <t>](null) = null
```

An optional value coerces at an option type, if the constituent value has a suitable type, and else goes to `null`:
```
C[opt <t> <: opt <t'>](null) = null
C[opt <t> <: opt <t'>](opt <v>) = opt C[<t> <: <t'>](v)  if <t> <: <t'>
C[opt <t> <: opt <t'>](opt <v>) = null                   if not(<t> <: <t'>)
```

Coercing a non-null, non-optional and non-reserved type at an option type treats it as an optional value, if it has a suitable type:
```
C[<t> <: opt <t'>](<v>) = opt C[<t> <: <t'>](v)  if not (null <: <t'>) and <t> <: <t'>
```

Any other type goes to `null`:
```
C[reserved <: opt <t>](_) = null
C[<t> <: opt <t'>](_) = null  if not (null <: <t'>) and not (<t> <: <t'>)
C[<t> <: opt <t'>](_) = null  if null <: <t'> and not (null <: <t>)
```

NOTE: These rules above imply that a Candid decoder has to be able to decide the subtyping relation at runtime.

#### Records

In the following rule:

 * The `<nat1>*` field names are those present in both the actual and expected type. The values are coerced.
 * the `<nat2>*` field names those only in the actual type. The values are ignored.
 * the `<nat3>*` field names are those only in the expected type, which therefore must be of optional or reserved type. The `null` value is used for these.

```
C[record { <nat1> = <t1>;* <nat2> = <t2>;* } <: record { <nat1> = <t1'>;* <nat3> = <t3>;* }](record { <nat1> = <v1>;* <nat2> = <v2>;* })
    = record { <nat1> = C[<t1> <: <t1'>](<v1>);* <nat3> = null;* }
```

#### Variants

Only a variant value with an expected tag coerces at variant type.

```
C[variant { <nat> = <t>; _;* } <: variant { <nat> = <t'>; _;* }](variant { <nat> = <v> })
    = variant { <nat> = C[<t> <: <t'>](<v>) }
```


#### References

Function and services reference values are untyped, so the coercion function is the identity here:

```
C[func <functype> <: func <functype'>](func <text>.<id>) = func <text>.<id>
C[service <actortype> <: service <actortype'>](service <text>) = service <text>
C[principal <: principal](principal <text>) = principal <text>
```

#### Tuple types

Whole argument and result sequences are coerced with the same rules as tuple-like records. In particular, extra arguments are ignored, and optional parameters read as as `null` if the argument is missing or fails to coerce:

```
C[(<t>,*) <: (<t'>,*)]((<v>,*)) = (<v'>,*)
    if C[record {<t>;*} <: record {<t'>,*}](record {<v>;*}) = record {<v'>;*}
```


## Properties

The relations above have certain properties. As in the previous section, `<v> : <t>` means that <v> has inherently type `<t>`.

* Reflexivity of subtyping:
  ```
  <t> <: <t>
  ```

* Transitivity of subtyping:
  ```
  <t> <: <t'>, <t'> <: <t''> ⇒ <t> <: <t'>
  ```

* Roundtripping:
  ```
  (<v> : <t>) ⟺ C[<t> <: <t>](<v>) = <v>
  ```

* Soundness of subtyping (or, alternatively, well-definedness of coercion)
  ```
  <t> <: <t'> ⇒ ∀ <v> : <t>. v[<t> <: <t'>](<v>) : <t'>
  ```

* Higher-order soundness of subtyping
  See <./IDL-Soundness.md>, with the following instantiations:
  ```
  s1 ~> s2 ≔ s2 <: s1
  t1 <: t2 ≔ t1 <: t2
  s1 in t1 <: s2 in t2 ≔ (to be done)
  s1 <:h s2 ≔ (host-language dependent)
  ```

* NB: Transitive coherence does not hold:
  ```
  <t1> <: <t2>, <t2> <: <t3>
  ```
  does not imply
  ```
  C[<t1> <: <t3>] = C[<t2> <: <t3>] ⚬ C[<t1> <: <t2>]
  ```

  However, it implies
  ```
  C[<t1> <: <t3>] ~ (C[<t2> <: <t3>] ⚬ C[<t1> <: <t2>])
  ```
  where ~ is the smallest homomorphic, reflexive, symmetric relation that satisfies `∀ v. opt v ~ null`.

The goal of “subtyping completeness” has not been cast into a formal formulation yet.

## Binary Format

At runtime, every Candid value is serialised into a triple (T, M, R), where T ("type") and M ("memory") are sequences of bytes and R ("references") is a sequence of references. If R is empty, it can be omitted.

By making the type of the data explicit, (1) the serialised data becomes self-describing, which is useful for tooling, (2) error discovery and error handling is improved, (3) the binary format is decoupled from versioning concerns, so that the latter can be designed more flexible.

By using references, (1) the wire representation of reference values (which may be complex and involve system meta data such as types) need not be exposed to client code, and (2) the system knows where the references are in the serialised data, such that it can rewrite/map/filter/adjust them as it sees fit.

Accordingly, serialisation is defined by three mapping functions, `T`, `M` and `R`, producing the respective components.

Note:

* While not required, a serialiser can minimise the size of the serialised type by first computing a value's *principal* type with respect to the subtyping relation. In particular, a variant type need not include more fields than necessary. For example, if `E = variant { A, B, C }` and the value to serialise is `A` of type `E`, then it can be serialised with type `variant { A }`. Similarly, if the value is the vector `[C, A, C]`, then the principal type `vec (variant { A, C })` suffices.


### Serialisation

This section describes how abstract *Candid values* of the types described by Candid are serialised into a binary representation for transfer between services.

Serialisation is defined by three functions `T`, `M`, and `R` given below.

Most Candid values are self-explanatory, except for references. There are two forms of Candid values for service references and principal references:

* `ref(r)` indicates an opaque reference, understood only by the underlying system.
* `id(b)`, indicates a transparent reference to a service addressed by the blob `b`.

Likewise, there are two forms of Candid values for function references:

* `ref(r)` indicates an opaque reference, understood only by the underlying system.
* `pub(s,n)`, indicates the public method name `n` of the service referenced by `s`.

#### Notation

`T` and `M` create a byte sequence described below in terms of natural storage types (`i<N>` for `N = 8, 16, 32, 64`, `f<N>` for `N = 32, 64`). The bytes are sequenced according to increasing significance (least significant byte first, a.k.a. little-endian).

The following notation is used:

* `.` is the empty byte sequence
* `x1 x2` is concatenation
* `t^N`, `t+`, `t*`, `t?` are sequences of `N`, `N>0`, `N>=0`, or `N<=1` repetitions, respectively
* `leb128` and `sleb128` are the unsigned and signed [LEB128](https://en.wikipedia.org/wiki/LEB128) encodings of a number, respectively
* `utf8` is the UTF-8 encoding of a text string (not 0-terminated)


#### Types

`T` maps an Candid type to a byte sequence representing that type.
Each type constructor is encoded as a negative opcode.
We assume that the fields in a record or variant type are sorted by increasing id and the methods in a service are sorted by name.

```
T : <primtype> -> i8*
T(null)      = sleb128(-1)  = 0x7f
T(bool)      = sleb128(-2)  = 0x7e
T(nat)       = sleb128(-3)  = 0x7d
T(int)       = sleb128(-4)  = 0x7c
T(nat8)      = sleb128(-5)  = 0x7b
T(nat16)     = sleb128(-6)  = 0x7a
T(nat32)     = sleb128(-7)  = 0x79
T(nat64)     = sleb128(-8)  = 0x78
T(int8)      = sleb128(-9)  = 0x77
T(int16)     = sleb128(-10) = 0x76
T(int32)     = sleb128(-11) = 0x75
T(int64)     = sleb128(-12) = 0x74
T(float32)   = sleb128(-13) = 0x73
T(float64)   = sleb128(-14) = 0x72
T(text)      = sleb128(-15) = 0x71
T(reserved)  = sleb128(-16) = 0x70
T(empty)     = sleb128(-17) = 0x6f
T(principal) = sleb128(-24) = 0x68

T : <constype> -> i8*
T(opt <datatype>) = sleb128(-18) I(<datatype>)              // 0x6e
T(vec <datatype>) = sleb128(-19) I(<datatype>)              // 0x6d
T(record {<fieldtype>^N}) = sleb128(-20) T*(<fieldtype>^N)  // 0x6c
T(variant {<fieldtype>^N}) = sleb128(-21) T*(<fieldtype>^N) // 0x6b

T : <fieldtype> -> i8*
T(<nat>:<datatype>) = leb128(<nat>) I(<datatype>)

T : <reftype> -> i8*
T(func (<datatype1>*) -> (<datatype2>*) <funcann>*) =
  sleb128(-22) T*(<datatype1>*) T*(<datatype2>*) T*(<funcann>*) // 0x6a
T(service {<methtype>*}) =
  sleb128(-23) T*(<methtype>*)                                    // 0x69

T : <methtype> -> i8*
T(<name>:<datatype>) = leb128(|utf8(<name>)|) i8*(utf8(<name>)) I(<datatype>)

T : <funcann> -> i8*
T(query)  = i8(1)
T(oneway) = i8(2)

T* : <X>* -> i8*
T*(<X>^N) = leb128(N) T(<X>)^N
```

Every nested type is encoded as either a primitive type, via the negative op-code, or an index into a list of *type definitions*, via a positive number. This allows for recursive types and sharing of types occuring multiple times:

```
I : <datatype> -> i8*
I(<primtype>) = T(<primtype>)
I(<comptype>) = sleb128(i)  where type definition i defines T(<datatype>)
```

Type definitions themselves are represented as a list of serialised data types:
```
T*(<comptype>*)
```
The data types in this list can themselves refer to each other (or themselves) via `I`.

Note:

* Due to the type definition prefix, there are always multiple possible ways to represent any given serialised type. Type serialisation hence is not technically a function but a relation.

* The serialised data type representing a method type must denote a function type.

* Because recursion goes through `T`, this format by construction rules out non-well-founded definitions like `type t = t`.

* The type table may only contain composite types (no `<primtype>`).

#### Memory

`M` maps an Candid value to a byte sequence representing that value. The definition is indexed by type.
We assume that the fields in a record value are sorted by increasing id.

```
M : <val> -> <primtype> -> i8*
M(n : nat)      = leb128(n)
M(i : int)      = sleb128(i)
M(n : nat<N>)   = i<N>(n)
M(i : int<N>)   = i<N>(signed_N^-1(i))
M(z : float<N>) = f<N>(z)
M(b : bool)     = i8(if b then 1 else 0)
M(t : text)     = leb128(|utf8(t)|) i8*(utf8(t))
M(_ : null)     = .
M(_ : reserved) = .
// NB: M(_ : empty) will never be called

M : <val> -> <constype> -> i8*
M(null : opt <datatype>) = i8(0)
M(?v   : opt <datatype>) = i8(1) M(v : <datatype>)
M(v^N  : vec <datatype>) = leb128(N) M(v : <datatype>)^N
M(kv*  : record {<fieldtype>*}) = M(kv : <fieldtype>)*
M(kv   : variant {<fieldtype>*}) = leb128(i) M(kv : <fieldtype>*[i])

M : (<nat>, <val>) -> <fieldtype> -> i8*
M((k,v) : k:<datatype>) = M(v : <datatype>)

M : <val> -> <reftype> -> i8*
M(ref(r) : service <actortype>) = i8(0)
M(id(v*) : service <actortype>) = i8(1) M(v* : vec nat8)

M(ref(r)   : func <functype>) = i8(0)
M(pub(s,n) : func <functype>) = i8(1) M(s : service {}) M(n : text)

M(ref(r) : principal) = i8(0)
M(id(v*) : principal) = i8(1) M(v* : vec nat8)
```


#### References

`R` maps an Candid value to the sequence of references contained in that value. The definition is indexed by type.
We assume that the fields in a record value are sorted by increasing id.

```
R : <val> -> <primtype> -> <ref>*
R(_ : <primtype>) = .

R : <val> -> <constype> -> <ref>*
R(null : opt <datatype>) = .
R(?v   : opt <datatype>) = R(v : <datatype>)
R(v*   : vec <datatype>) = R(v : <datatype>)*
R(kv*  : record {<fieldtype>*}) = R(kv : <fieldtype>)*
R(kv   : variant {<fieldtype>*}) = R(kv : <fieldtype>*[i])

R : (<nat>, <val>) -> <fieldtype> -> <ref>*
R((k,v) : k:<datatype>) = R(v : <datatype>)

R : <val> -> <reftype> -> <ref>*
R(ref(r) : service <actortype>) = r
R(id(b*) : service <actortype>) = .
R(ref(r)   : func <functype>) = r
R(pub(s,n) : func <functype>) = .
R(ref(r) : principal) = r
R(id(b*) : principal) = .
```

Note:

* It is unspecified how references *r* are represented, neither internally nor externally. When binding to Wasm, their internal representation is expected to be based on Wasm reference types, i.e., `anyref` or subtypes thereof. It is up to the system how to represent or translate the reference table on the wire.


### Parameters and Results

`A` defines the argument mapping. Essentially, an argument list is serialised into the triple (T,M,R) as if it was a single closed record. T and M are combined into a single byte stream B, where they are preceded by the string "DIDL" as a magic number and a possible list of type definitions.
We assume that the argument values are sorted by increasing id.

```
A(kv* : <datatype>*) = ( B(kv* : <datatype>*), R(kv* : <datatype>*) )

B(kv* : <datatype>*) =
  i8('D') i8('I') i8('D') i8('L')      magic number
  T*(<comptype>*)                      type definition table
  I*(<datatype>*)                      types of the argument list
  M(kv* : <datatype>*)                 values of argument list
```
The vector `T*(<comptype>*)` contains an arbitrary sequence of type definitions (see above), to be referenced in the serialisation of the other `<datatype>` vector.

The same representation is used for function results.

Note:

* It is unspecified how the pair (B,R) representing a serialised value is bundled together in an external environment.

### Deserialisation

Deserialisation at an expected type sequence `(<t'>,*)` proceeds by

 * checking for the magic number `DIDL`
 * using the inverse of the `T` function to decode the type definitions `(<t>,*)`
 * check that `(<t>,*) <: (<t'>,*)`, else fail
 * using the inverse of the `M` function, indexed by `(<t>,*)`, to decode the values `(<v>,*)`
 * use the coercion function `C[(<t>,*) <: (<t'>,*)]((<v>,*))` to understand the decoded values at the expected type.

### Deserialisation of future types

Deserialisation uses the following mechanism for robustness towards future extensions:

* A serialised type may be headed by an opcode other than the ones defined above (i.e., less than -24). Any such opcode is followed by an LEB128-encoded count, and then a number of bytes corresponding to this count. A type represented that way is called a *future type*.

* A value corresponding to a future type is called a *future value*. It is represented by two LEB128-encoded counts, *m* and *n*, followed by a *m* bytes in the memory representation M and accompanied by *n* corresponding references in R.

These measures allow the serialisation format to be extended with new types in the future, as long as their representation and the representation of the corresponding values include a length prefix matching the above scheme, and thereby allowing an older deserialiser not understanding them to skip over them. The subtyping rules ensure that upgradability is maintained in this situation, i.e., an old deserialiser has no need to understand the encoded data.


## Open Questions

* Support default field values?
* Support generic type definitions?
* Namespaces for imports?
