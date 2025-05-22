# Candid CLI

A multi-purpose tool for Candid.

```
caffeine-stub 0.1.0

USAGE:
    caffeine-stub <SUBCOMMAND>

SUBCOMMANDS:
    check    Type check Candid file
    bind     Generate binding for different languages
    hash     Compute the hash of a field name
    encode   Encode Candid value
    decode   Decode Candid binary data
    assist   Generate textual Candid values based on a terminal dialog
    random   Generate random Candid values
    subtype  Check for subtyping
```

## TOML config

`caffeine-stub bind -t rs` and `caffeine-stub random` can take a TOML file to configure how `caffeine-stub` generate Rust binding or random values.

Rust bindgen can take an external Handlebar template with the following TOML file,

```toml
[caffeine-stub.rust]
target = "custom"  # Other targets: canister_call, agent, stub
template = "template.hbs"  # required for custom target
# any tags mentioned from hbs
candid_crate = "candid"
service_name = "service"

[rust]
visibility = "pub(crate)"
attributes = "#[derive(CandidType, Deserialize, Debug)]"
GetBlocksResponse.attributes = "#[derive(CandidType, Deserialize, Debug, Clone, Serialize)]"
GetBlocksResponseArchivedBlocksItem.name = "ABetterName"
```

## Examples

```
$ caffeine-stub encode '(42, vec {1;2;-3})'
4449444c016d7c027c002a0301027d

$ caffeine-stub encode '(42, vec {1;2;-3})' -t '(nat, vec int32)' -f pretty
Length: 24 (0x18) bytes
0000:   44 49 44 4c  01 6d 75 02  7d 00 2a 03  01 00 00 00   DIDL.mu.}.*.....
0010:   02 00 00 00  fd ff ff ff                             ........

$ caffeine-stub encode '("text")' -d hello.did -m greet
4449444c0001710474657874

$ caffeine-stub encode '("text")' -d list.did -t '(list)'
Error: type mismatch: "text" can not be of type opt node

$ caffeine-stub decode '4449444c016d7c027c002a0301027d'
(42, vec { 1; 2; -3; })

$ caffeine-stub decode '4449444c016d7c027c002a0301027d' -t '(int)'
(42)

$ caffeine-stub bind hello.did -t js
export const idlFactory = ({ IDL }) => {
  return IDL.Service({ 'greet' : IDL.Func([IDL.Text], [IDL.Text], []) });
}

$ caffeine-stub random -t '(int, text)'
(-72_594_379_354_493_140_610_202_928_640_651_761_468, "_J`:t7^>")

$ caffeine-stub random -t '(int, text)' -c 'random = { range = [-10, +10], text = "name" }'
(-6, "Cindy Klocko")

$ caffeine-stub random -d service.did -m method -c random.toml -a '("seed argument")' -l js
[new BigNumber('-4'), 'Marcus Kris']
```
