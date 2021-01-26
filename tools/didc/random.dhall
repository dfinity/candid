let default = { range = Some [300,400], text = Some "ascii", depth = Some 5, size = Some 100, value = None Text }
in {
 default,
 list = { depth = Some 20, size = Some 50, range = Some [42,43] },
 val.int = { range = Some [1,2] },
 left.tree = { range = Some [-200,-100] },
 right.tree = { range = Some [100,200] },

 vec.nat8 = { range = Some [21, 60] },
 vec = { size = Some 100 },
 tree.leaf = { value = Some "42" },
}

