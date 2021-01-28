let default =
      { range = None (List Natural)
      , text = Some "bs"
      , width = Some 10
      , depth = Some 5
      , size = Some 100
      , value = None Text
      }

in  { default
    , list = { depth = Some 20, size = Some 50 }
    , val.value = Some "42"
    , left = { depth = Some 1, range = Some [ -200, -100 ] }
    , right.tree = { depth = Some 5, range = Some [ 100, 200 ] }
    , vec.nat8.range = Some [ 65, 90 ]
    }
