type List = ?(Int, List);
public type _MAIN = (Int, List) -> {
  'get' : shared () -> async List;
  'set' : shared List -> async List;
}
