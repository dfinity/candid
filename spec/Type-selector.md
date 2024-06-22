# Candid Type Selector specification

Date: Jun 10, 2024

## Motivation

We need a way to customize how we interpret Candid data for various use cases, for example,

* Candid binding generation. One Candid type can map to several types in a host language, such as Rust and TypeScript. We may also want to adjust the type name and field name in the generated code to fit in the host language’s naming convention.
* Pretty printer and Candid UI. One Candid type can have different meanings in different canisters. For example, a `blob` type can represent an image, an account id, a Wasm binary, etc. We want to customize the format when showing the data in the terminal or in the browser.
* Data validation in deserialization. For canisters taking variable-length arguments, e.g., `blob`, `vec` and recursive types, we may want to limit the size of the input data to prevent spending too many cycles in deserializing invalid data.
* Random value generator. We want to customize how we generate random Candid values for fuzz testing. For example, we may want to restrict the range of a `nat` type, or limit the maximal depth of a recursive type.

We can of course implement all these customizations in each application, but it is beneficial if we can identify a common syntax to express the type level customization and apply the same syntax to all applications to enforce a consistent user experience and reduce the learning curve.

## Design

Motivated by Cascading Style Sheets ([CSS](https://en.wikipedia.org/wiki/CSS)), we define a configuration language to specify the customization of a Candid interface. The configuration file enables the separation of the Candid interface and its configuration, including layout, binding, validation, etc.

There are two parts in the config language: 1) A way to quickly select particular type nodes in Candid types; 2) Attach semantic meaning to the selected type nodes.

### Type selector

For the first part, we define a type selector `<selector>` similar to a CSS selector.

```
<selector> := <scopes> (. <path>)? | <path>
<path> := <name> (. <name>)*
<scopes> := <scope> (. <scope>)*
<scope> := func:<name> | func:init | arg:<num> | ret:<num>
```

`<path>` is a sequence of names separated by "`.`". It is a pattern used to select the Candid type node you want to customize. For example, given the following Candid interface,

```
type tree = variant { leaf: int; branch: record { left: tree; right: tree } };
type pair = record { left: int; right: int };
service : {
  f : (pair, pair) -> (pair);
}
```

Paths `left.tree`, `branch.record.left` and `tree.variant.branch.record.left` all match the left branch of a tree. Path `left` will match the "left" field in both `tree` and `pair`. We greedily match the path with a shorter pattern. For example, if you have both path `left` and `left.tree`, we will always match `left`, and `left.tree` will never be matched (we will issue a warning, if a path is never matched). If you want to match `left.tree`, you can replace the `left` path with `pair.record.left`.

`<scopes>` is a special form of path, where each name has a prefix of `func:`, `arg:`, or `ret:`. It indicates that the path can only be matched when it’s inside a scope of a function or argument position. A scoped path match always takes precedence over a non-scoped path. For example, `func:f.left` matches the `left` field in `pair`, but not the `left` field in `tree`, and the global `left` path will not be matched when processing function `f`; `func:f.arg:1.left` matches the `left` field in the second input argument of `f`; `ret:0.left` matches the first return type of all functions.

Note that scoped path may not be available for some applications. For example, bindgen and deserialization don't support scoped path. In these applications, when a type variable is shared among multiple functions, scoped path can lead to duplication of type definitions, which makes the client code harder to maintain. You can still use non-scoped paths to match functions or arguments. We establish the following convention:

* `func:<name>` can be matched with `<name>`.
* `func:init`, the initialization arguments of the service constructor, can be matched with `init`.
* `arg:<num>` can be matched with `arg<num>`.
* `ret:<num>` can be matched with `ret<num>`.

Open question: The path doesn’t distinguish between label and type name. We cannot match just label `left`, but not type name `left`. We could add a prefix like `label:left`, but it means more things to type for the end user. We could work around this problem by providing a longer path if needed.

### Config properties

For the second part, we assign a set of key-value pairs (config) to the selected type nodes. It’s up to the implementer to interpret the meaning of these key-value pairs for different use cases. Concretely, each application defines its own config struct satisfying the following trait:

```rust
trait Config {
  fn merge_config(&mut self, config: &Self, ctx: &Context);
  fn unmatched_config() -> Self;
  fn update_state(&mut self, ctx: &Context);
  fn restore_state(&mut self, ctx: &Context);
}
```

As the application traverses through the Candid type AST, we check if there is any path match with the current type node. If there is a match, we load the associated config and merge it with the current config.

`merge_config` specifies the merging semantics of the key-value pairs. Specifically, whether these properties apply to the subtree rooted at the selected type node, or just the node itself. The merging semantics can depend on the `context`, which indicates the type of the current node (type or label), and whether the matched path is the first occurrence of the type path. Some properties, such as depth, can only apply to the first occurrence of the match. Otherwise, we get an infinite loop.

When there is a path match, the matched key-value pairs is provided to the `merge_config` function to merge the current config with the matched config. If there is no path match, `unmatched_config` is provided to the `merge_config` function, which usually is an empty config.

`update_state` and `restore_state` functions are used to update the config when traversing down/popping up the type AST.

### TOML config

Based on the above requirements, we choose TOML to specify our configurations for several reasons: 

1) The "." syntax to specify path is already part of the TOML syntax, and TOML allows to specify arbitrary key-value pairs as configurations; 
2) Both Rust and Motoko developers are already familiar with the TOML format (used in Cargo and mops).

A TOML config is always tied to a particular did file, similar to how CSS is tied to a particular HTML/JS file. Users can specify multiple config sections for different applications. A few known top level labels are `random`, `display`, `rust`, `motoko`, `typescript`. Developers are free to add new top-level labels. If the TOML file only contains config for one application, the top-level label can be omitted.

The following is an example TOML config file for the Candid interface we showed earlier. It contains the configs for two applications: `random` and `rust`. The random config specifies that when generating a tree, the left branch is at most of depth 1, and the right branch is at most depth 5. The numbers on the leaves of the left branch are in [-200, -100], and the numbers on the leaves of the right branch are in [100, 200]. When generating Rust bindings, all types have `pub(crate)` visibility. The top-level structs and enums have attribute `#[derive(CandidType, Deserialize, Clone, Debug)]`, and we use `i128` to represent the `int` type. The first argument name of function `f` is `input`.

```toml
[random]
left.tree = { depth = 1, range = [-200, -100] }
right.tree = { depth = 5, range = [100, 200] }

[rust]
visibility = "pub(crate)"
attributes = "#[derive(CandidType, Deserialize, Clone, Debug)]"
int.use_type = "i128"
f.arg0.name = "input"
```

Note that TOML is just one implemented way to specify configs for the end user. Any format that can be parsed into [candid_parser::configs::ConfigTree](https://docs.rs/candid_parser/0.2.0-beta.1/candid_parser/configs/struct.ConfigTree.html) is acceptable. Users can also add configs programmatically in Rust via [add_config](https://docs.rs/candid_parser/0.2.0-beta.1/candid_parser/configs/struct.ConfigTree.html#method.add_config). For deserialization validation, we also want to support specifying config via Rust attributes.

To facilitate tooling, we will add a new canister metadata `candid:config` to store the TOML config file if the canister author chooses to.

## Rust binding configuration

To generate Rust binding, we define the following config properties:

* `name`: Rename a type variable or label. It only applies to the current node.
* `use_type`: Map a Candid type to a known/user-defined Rust type. It applies to the current node, or the next type node when the current node is a label. This allows `label.use_type = "T"` to indicate that we want to map the type of label to T. Otherwise, we have to use `label.type.use_type = "T"`.
* `attributes`: Set the attributes for struct/enum or fields. It applies to the current node, or the next label when the current node is a type. This allows us to apply field attributes to all fields in a struct/enum with `record.attributes`.
* `visibility`: Set the visibility for a type variable or label. It applies to the subtree rooted at the current node. For example, `tree.visibility` applies to the type variable tree and its fields.

**Note**
+ Scoped path is not available in binding generation. You can use the non-scoped path, e.g., `init.arg0`, `f.ret0`, to match functions.
+ The bindgen generates a unit test for each instance of `use_type`. This is to ensure that the user provided type always conforms to Candid type.

## Random value generation

For random value generation, we define the following properties:

* `range`: Specifies the range for all integer types. If omitted or invalid, we use the full integer range for that type.
* `width`: Specifies the maximal length for `vec` and `text` value. If omitted, we estimate the length based on the size of the vector element.
* `text`: Specifies the kind of text we want to generate. If omitted, it generates a random utf8 text. The implemented kinds are "ascii", "emoji", as well as some words from the fake crate: "name", "name.cn", "company", "country", "path" and "bs".
* `value`: Specifies a list of Candid values to choose from. It will be type checked against the expected type.
* `depth`: Specifies the maximal depth of the Candid value. For recursive types, it only applies to the first occurrence of the type selector. The depth bound is a soft limit.
* `size`: Specifies the maximal size of the Candid value. For recursive types, it only applies to the first occurrence of the type selector. The size bound is a soft limit.

