type s = actor { 'next' : shared () -> async s };
public type _MAIN = s -> s
