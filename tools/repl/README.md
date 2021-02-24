# Canister REPL

```
ic-repl --replica [local|ic|url]
```

## Commands

```
<command> := 
 | import <id> = <text>   (canister URI)
 | export <text>  (filename)
 | config <text>  (dhall config)
 | call <name> . <name> ( <val>,* )
 | let <id> = <val>
 | show <val>
 | assert <val> = <val>

<var> := <id> | _
<val> := <candid val> | <var> (. <id>)*
```
