# Configure language for Candid

## Motivation

We need a way to customize how we interpret Candid data for various use cases, for example,

* Random value generator. We want to restrict certain `nat` field in a record to be within a fixed range; 
  limit the maximal depth for a recursive data type. 
* Pretty printer. Rename record/variant label to be more human-readable; map the label id back to a text label; Reorder record fields; Change the identation of nested data.
* Candid UI. Upload a file for `blob` in a particular method; draw `vec Lines` on a canvas; adjust layout of canister methods.

We can of course implement all these in a host language, but there are some value to support these customizations in Candid
to benefit canisters written in different host languages. Without using dependent typing, we propose a light-weight config language to specify properties for type nodes.

## Why not use Candid as a configure language for Candid?

We can! The config lanauge is of the following Candid type `configs`:

```
type RandomConfig = record { 
  range: opt record { int; int }; 
  "text": opt text; 
  width: opt nat; 
  value: opt text;
  depth: opt nat;
  size: opt nat;
};
type node = record { 
  config: opt RandomConfig; 
  branch: configs 
};
type configs = vec record { text; node };
```

Given a `tree` type in Candid: `type tree = variant { leaf: int; branch: record { left: tree; right: tree } };`,
if we want to limit the depth of the left branch of a tree, we would write:

```
vec {
  record { 
    "left"; 
    record { 
      config = null; 
      branch = vec { record { "tree"; record { config = opt record { depth = opt 1 }; branch = vec {}} } }; 
    }
  };
}
```

As you can see, Candid's textual representation is not optimized for writing. What we really want to write is
simply `left.tree = { depth = Some 1 }` in Dhall.
