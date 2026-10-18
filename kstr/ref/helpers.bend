def err(e: K.KStrError) -> String:
  match e:
    case K.KStrEmpty{}:
      "empty"
    case K.KStrBadChar{p}:
      "bad char " ++ Nat.show(p)
    case K.KStrRange{}:
      "range"
    case K.KStrBadFormat{p}:
      "bad format " ++ Nat.show(p)
    case K.KStrMissingArg{}:
      "missing arg"

def r32(r: Result<&2, &2, K.KStrError, U32>) -> String:
  match r:
    case Done{v}:
      U32.show(v)
    case Fail{e}:
      err(e)

def r64(r: Result<&2, &2, K.KStrError, W.W64>) -> String:
  match r:
    case Done{v}:
      W.W64.show(v)
    case Fail{e}:
      err(e)

def sres(r: Result<&2, &2, K.KStrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      err(e)

def q(o: B.Octets) -> String:
  "'" ++ B.Octets.to_string(o) ++ "'"
