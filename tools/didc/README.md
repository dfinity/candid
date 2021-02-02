# Candid CLI

A multi-purpose tool for Candid.

```
didc 0.1.0

USAGE:
    didc <SUBCOMMAND>

SUBCOMMANDS:
    check     Type check Candid file
    bind      Binding for different languages
    encode    Encode Candid value
    decode    Decode Candid binary data
    diff      Diff two Candid values
```

## Examples

```
$ didc encode '(42, vec {1;2;-3})'
4449444c016d7c027c002a0301027d

$ didc encode '(42, vec {1;2;-3})' -t '(nat, vec int32)' -f pretty
Length: 24 (0x18) bytes
0000:   44 49 44 4c  01 6d 75 02  7d 00 2a 03  01 00 00 00   DIDL.mu.}.*.....
0010:   02 00 00 00  fd ff ff ff                             ........

$ didc encode '("text")' -d hello.did -m greet
4449444c0001710474657874

$ didc encode '("text")' -d list.did -t '(list)'
Error: type mismatch: "text" can not be of type opt node

$ didc decode '4449444c016d7c027c002a0301027d'
(42, vec { 1; 2; -3; })

$ didc decode '4449444c016d7c027c002a0301027d' -t '(int)'
(42)

$ didc diff '(record{1;2;3}, 42)' '(record{1;5;9}, 42)'
record { edit { 1 put { 5 } }; edit { 2 put { 9 } }; }
skip

$ didc bind hello.did -t js
export default ({ IDL }) => {
  return IDL.Service({ 'greet' : IDL.Func([IDL.Text], [IDL.Text], []) });
};

$ didc random -t '(int, text)'
(-72_594_379_354_493_140_610_202_928_640_651_761_468, "_J`:t7^>")

$ didc random -t '(int, text)' -c '{ range = Some [-10, +10], text = "name" }'
(-6, "Cindy Klocko")

$ didc random -d service.did -m method -f random.dhall -a '("seed argument")' -l js
[new BigNumber('-4'), 'Marcus Kris']
```
