let default =
      { range = None (List Natural)
      , text = Some "emoji"
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
    , Vec = { width = Some 2, size = Some 10 }
    , profile.record =
      { name.text = Some "name"
      , age.range = Some [ 18, 65 ]
      , company.text = Some "company"
      , country.text = Some "country"
      , file.text = Some "path"
      , description.text = Some "bs"
      }
    }
