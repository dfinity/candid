let default = { range = [0,100], text = "ascii", depth = 5, size = 100, value = None Text }
in {
 default,
 list = { depth = 20, size = 50, range = [42,43] },
 vec.nat8 = { range = [21, 60] },
 vec = { size = Some 100 },
 tree.leaf = { value = "42" },
 tree.branch.right = { depth = 5, size = 100 },
}

