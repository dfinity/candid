# Configure language for Candid

## Motivation

We need a way to customize how we interpret Candid data for various use cases, for example,

* Random value generator. We want to restrict certain `nat` field in a record to be within a fixed range; 
  limit the maximal depth for a recursive data type. 
* Pretty printer. Rename record/variant label to be more human-readable; map the label id back to a text label; Reorder record fields; Change the identation of nested data.
* Candid UI. Upload a file for `blob` in a particular method; draw `vec Lines` on a canvas; adjust layout of canister methods.

We can of course implement all these in a host language, but there are some value to support these customizations in Candid
to benefit canisters written in different host languages. Without using dependent typing, we propose a light-weight config language to specify properties for type nodes.

## Design

There are two parts in the config language: 1) A way to quickly identify particular type nodes in Candid type; 2) Attach semantic meaning to the type nodes.

For the first problem, we use notations similar to CSS selector. For example, given the following Candid types,
```
type tree = variant { leaf: int; branch: record { left: tree; right: tree } };
type list = opt record { left: int; right: list };
type left = opt int;
```
If we want to find the left branch of a tree, we can write `left.tree`, `branch.record.left`
or `tree.variant.branch.record.left`.
If we write just `left`, it will match the `left` field in both `tree` and `list`, as well as the `left` type.

For the second problem, we assign a set of key-value pairs to the selected type nodes. It's up to the implementator to
interpret the meaning of these key-value pairs for different use cases. For example, if we want to generate a random tree
whose left branch is always 1, we can write `left.tree = { depth = Some 1 }`.


## Why not use Candid as a configure language for Candid?

We can! The config language is of the following Candid type `configs`:

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

if we want to limit the depth of the left branch of a tree, we would write:

```
vec {
  record { 
    "left"; 
    record { 
      config = null; 
      branch = vec { 
        record { 
          "tree"; 
          record { 
            config = opt record { depth = opt 1 }; 
            branch = vec {}
          }
        }
      };
    }
  };
}
```

As you can see, Candid's textual representation is not optimized for writing. What we really want to write is
simply `left.tree = { depth = Some 1 }` in Dhall.
