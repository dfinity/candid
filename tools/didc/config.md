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

For the first part, we use notations similar to CSS selector. For example, given the following Candid types,
```
type tree = variant { leaf: int; branch: record { left: tree; right: tree } };
type pair = record { left: int; right: nat };
type left = opt int;
```
If we want to find the left branch of a tree, we can write `left.tree`, `branch.record.left`
or `tree.variant.branch.record.left`.
If we write just `left`, it will match the `left` field in both `tree` and `pair`, as well as the `left` type.

For the second part, we assign a set of key-value pairs to the selected type nodes. It's up to the implementator to
interpret the meaning of these key-value pairs for different use cases. 
These properties apply to the sub-tree rooted at the selected type nodes, not just the node itself.
For example, if we want to generate a random tree whose left branch has depth 1 and leaf value between [20, 30], 
we can write `left.tree = { depth = Some 1, range = Some [20, 30] }`. 
Technically, `range` applies only to `left.tree.variant.leaf`, but since `leaf` is in the sub-tree of `left.tree`, 
we do not need to write a separate type selector.

Note that some properties, such as depth, only apply to the first occurance in the type path. 
Otherwise, we get an infinite recursion.

Based on the above requirements, we use Dhall as our config language.

## Random config

For random value generation, we define the following properties,

* `range = Some [lower, upper]`, specifies the range for all integer types. If omitted or invalid, we uses the full integer range.
* `width = Some 10`, specifies the maximal length for `vec` and `text`. If omitted, we estimate the length based on the size of the element.
* `text = Some "kind"`, specifies the kind of text we want to generate for `text`. If omitted, we take a random bytes and convert to utf-8 text. The implemented kind are "name", "name.cn", "company", "country", "path", "bs", which all come from the `fake` crate.
* `value = Some "CandidValue"`, specifies a fixed value in Candid textual form. It will be type checked against the expected type.
* `depth = Some 10`, specifies the maximal depth for the Candid value. For recursive types, it only applies to the first occurance of the type selector. The depth bound is a soft limit.
* `size = Some 10`, specifies the maximal size for the Candid value. For recursive types, it only applies to the first occurance of the type selector. The size bound is a soft limit.

## Why not use Candid as a configure language for Candid?

We can! The config language is of the following Candid type `configs`:

```
type RandomConfig = record { 
  range: opt record { int; int }; 
  depth: opt nat;
  ...
};
type node = record { 
  config: opt RandomConfig; 
  branch: configs 
};
type configs = vec record { text; node };
```

If we want to limit the depth of the left branch of a tree, we would write:

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
