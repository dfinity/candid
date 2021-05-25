type t = { '\"'  : Nat; '\''  : Nat; '\"\''  : Nat; '\\\n\'\"'  : Nat };
public type _MAIN = { '\n\'\"\'\'\"\"\r\t' : shared t -> async () }
