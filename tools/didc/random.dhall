let default =
      { range = None (List Natural)
      , text = Some "ascii"
      , depth = Some 5
      , size = Some 100
      , value = None Text
      }

in  { default
    , list = { depth = Some 20, size = Some 50, range = Some [ 42, 43 ] }
    , val.int.value = Some "42:int"
    , left.range = Some [ -200, -100 ]
    , right.tree.range = Some [ 100, 200 ]
    , vec.nat8.range = Some [ 65, 90 ]
    , vec.size = Some 100
    }
