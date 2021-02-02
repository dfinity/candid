# Configuration language for Candid

## Motivation

We need a way to customize how we interpret Candid data for various use cases, for example,

* Random value generator. We want to restrict certain `nat` field in a record to be within a fixed range; 
  limit the maximal depth for a recursive data type. 
* Pretty printer. Rename record/variant label to be more human-readable; map the label id back to a text label; Reorder record fields; Change the indentation and line width.
* Candid UI. Upload a file for `blob` in a particular method; draw `vec Lines` on a canvas; adjust layout of canister methods.

We can of course implement all these in a host language, but there are some value to support these customizations in Candid
to benefit canisters written in different host languages. Without using dependent typing, we propose a light-weight config language to specify properties for type nodes.

## Design

There are two parts in the config language: 1) A way to quickly select particular type nodes in Candid type; 2) Attach semantic meaning to the selected type nodes.

For the first part, we define a type selector `<selector>` similar to CSS selector. 

```
<selector> := <method> (. <path>)? | <path>
<method> := [ <name> ] | [ <nat> ] | [ <name> ] . [ <nat> ]
<path> := <name> (. <name>)*
```

For example, given the following Candid types,
```
type tree = variant { leaf: int; branch: record { left: tree; right: tree } };
type pair = record { left: int; right: nat };
type left = opt int;
service : {
  f : (record {a:int; b:int}, record {a:int; b:int}) -> ();
}
```
If we want to find the left branch of a tree, we can write `left.tree`, `branch.record.left`
or `tree.variant.branch.record.left`.
If we write just `left`, it will match the `left` field in both `tree` and `pair`, as well as the `left` type.

The type selector has an optional method prefix to specify the scope of the selector. For example, `[f].a` matches the `a` fields in method `f`; `[f].[0].a` matches the `a` field in the first argument of method `f`.

For the second part, we assign a set of key-value pairs to the selected type nodes. It's up to the implementer to
interpret the meaning of these key-value pairs for different use cases. 
These properties apply to the sub-tree rooted at the selected type nodes, not just the node itself.
For example, if we want to generate a random tree whose left branch has depth 1 and leaf value between [20, 30], 
we can write `left.tree = { depth = Some 1, range = Some [20, 30] }`. 
Technically, `range` applies only to `left.tree.variant.leaf`, but since `leaf` is in the sub-tree of `left.tree`, 
we do not need to write a separate type selector.

Note that some properties, such as depth, only apply to the first occurance in the type path. 
Otherwise, we get an infinite recursion.

Based on the above requirements, we use Dhall as our config language, which has similar type to Candid with more concise syntax.
This is a temporary choice. Eventually, we expect to expand the Candid syntax, see the last section for detail.

## Random config

For random value generation, we define the following properties,

* `range = Some [-300, 300]`, specifies the range for all integer types. If omitted or invalid, we use the full integer range.
* `width = Some 10`, specifies the maximal length for `vec` and `text`. If omitted, we estimate the length based on the size of the vector element.
* `text = Some "ascii"`, specifies the kind of text we want to generate for `text`. If omitted, it generates random utf8 text. The implemented kinds are "ascii", "emoji", as well as some words from the `fake` crate: "name", "name.cn", "company", "country", "path", and "bs".
* `value = Some ["null", "opt 42"]`, specifies a list of Candid values to choose from. It will be type checked against the expected type.
* `depth = Some 10`, specifies the maximal depth for the Candid value. For recursive types, it only applies to the first occurance of the type selector. The depth bound is a soft limit.
* `size = Some 10`, specifies the maximal size for the Candid value. For recursive types, it only applies to the first occurance of the type selector. The size bound is a soft limit.

### Example Dhall config

```dhall
let default =  {- This is the default config -}
      { range = None (List Natural)
      , text = Some "ascii"
      , width = Some 10
      , depth = Some 10
      , size = Some 100
      , value = None (List Text)
      }

in  default /\
    { {- Generate (record {a=42; b=1}, record {a=any int; b=1}) for method f  -}
      `[f]` =
      { `[0]`.a = { range = Some [ 42,42 ] }
      , b = { value = Some ["1"] }
      }
      
    {- Left tree is leaf only; Left tree has negative numbers and right tree has positive numbers -}
    , left.tree = { depth = Some 1, range = Some [ -200, -100 ] }
    , right.tree = { depth = Some 5, range = Some [ 100, 200 ] }
    
    {- Customize text fields in record type -}
    , profile.record =
      { name.text = Some "name"
      , age.range = Some [ 18, 65 ]
      , company.text = Some "company"
      , country.text = Some "country"
      , file.text = Some "path"
      , description.text = Some "bs"
      }
      
    {- Generate principal id -}
    , principal.value = Some ["principal \"aaaaa-aa\"", "principal \"2vxsx-fae\""]
    }
```

## Why not use Candid as a configuration language for Candid?

We can! The config is of the following Candid type `configs`:

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
simply `left.tree = { depth = Some 1 }` or `left.tree.depth = Some 1` in Dhall.
Note that this is not a fundamental obstacle, we can easily add shorthand for nested record 
and record merging semantics in Candid syntax.
