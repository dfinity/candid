# Canister REPL

```
ic-repl --replica [local|ic|url]
```

## Commands

```
<command> := 
 | import <id> = <text>   (canister URI)
 | config <text>  (dhall config)
 | call <name> . <name> ( <val>,* )
 | let <id> = <val>
 | show <id>
 | assert <val> = <val>

<var> := <id> | $ <nat>
<val> := <candid val> | <var> (. <id>)*
```
