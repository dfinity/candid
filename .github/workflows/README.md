# Workflow naming

One rule: **the filename is the identity, and `name:` is its Title Case
rendering.** Either can be derived from the other.

```
<subject>[-<qualifier>].yml
```

Subject first, always — including for release and publish workflows. Product
identifiers keep their own spelling (`didc`, `candid_ui`).

| file | `name:` | |
|---|---|---|
| `candid-ui-release.yml` | Candid UI Release | |
| `coq.yml` | Coq | removed once `lean/` covers it |
| `crates-publish.yml` | Crates Publish | |
| `dependencies.yml` | Dependencies | licenses, bans and sources via cargo-deny |
| `didc-release.yml` | Release | generated — see below |
| `rust-bench.yml` | Rust Bench | |
| `rust.yml` | Rust | removed once `crates/` replaces it |
| `tools.yml` | Tools | |

Subject-first is what groups related workflows together (`rust.yml` /
`rust-bench.yml`, `crates.yml` / `crates-publish.yml`) and it is what
`didc-release.yml` forces, so there is one pattern rather than one pattern plus
an exception.

## Jobs

- Job ids are kebab-case.
- **Omit `name:`** unless it says something the id does not — GitHub falls back
  to the id, so a `name:` that repeats it is duplicated state.
- The check name is what appears in a list of a dozen-plus entries on a pull
  request, so it has to stand alone. `coq` works; `build` does not.
- **No `:required` suffix.** GitHub already labels required checks in the merge
  box. Encoding it in the name duplicates settings that live elsewhere, and it
  drifted the last time it was tried — the marker sat on `license-check`, which
  was not required, while `rust`, which is, never carried it.

## Required checks

`rust` is the only required status check. It is the reason `rust.yml` must not
use a workflow-level `paths:` filter — see the comment at the top of that file.

Workflows added for the rewrite (`crates`, `lean`, `conformance`) should **not**
be required. [REWRITE.md](../../REWRITE.md) depends on work in those directories
being allowed to be broken; making their checks gate merges would contradict it.
Promote them individually at v1.

Because the new checks are not gating, there is no need for an aggregate
`ci:required` job of the kind [dfinity/cdk-rs](https://github.com/dfinity/cdk-rs)
uses. That pattern exists to hold branch protection at a single context as checks
multiply; here the count of required contexts stays at one either way.

## `didc-release.yml` is generated

It is written by [dist](https://opensource.axo.dev/cargo-dist/) from
[`dist-workspace.toml`](../../dist-workspace.toml). Do not edit it; run
`dist generate` after changing that config.

Two things follow:

- The **filename** comes from `tag-namespace`, which is also the release tag
  prefix (`didc-vX.Y.Z`). `tag-namespace = "didc"` produces
  `didc-release.yml`. It cannot be set independently of the tag scheme.
- The **`name:` field** is not configurable at all; dist always emits
  `name: Release`. This is the one place the filename/`name:` mapping above does
  not hold.
