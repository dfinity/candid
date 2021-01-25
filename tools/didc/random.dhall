let default = { range = Some [0,100], text = Some "ascii", depth = Some 5, size = Some 100, value = None Text }
in {
 default,
 list = { depth = Some 20, size = Some 50, range = Some [42,43] },
 tree = { range = Some [1,2] },
 vec.nat8 = { range = Some [21, 60] },
 vec = { size = Some 100 },
 tree.leaf = { value = Some "42" },
 tree.branch.right = { depth = Some 5, size = Some 100 },
}

