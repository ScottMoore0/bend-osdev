def dv(r: D.KDiv64) -> String:
  match r:
    case D.KDiv64{q, r}:
      W.W64.show(q) ++ " " ++ U32.show(r)

def pr(p: W.W64 & W.W64) -> String:
  (q, r) = p
  W.W64.show(q) ++ " " ++ W.W64.show(r)

def rat(r: Q.KRational) -> String:
  match r:
    case Q.KRational{p, q}:
      U32.show(p) ++ "/" ++ U32.show(q)

# |a - b| <= 64, as signed 32-bit values
def near(+a: U32, +b: U32) -> Bool:
  U32.is_lt(U32.add(U32.sub(a, b), 64), 129)

def within(r: C.KCordic, +wc: U32, +ws: U32) -> Bool:
  match r:
    case C.KCordic{+c, +s}:
      Bool.and(near(c, wc), near(s, ws))

def cerr.show(ok: Bool, r: C.KCordic) -> String:
  match ok:
    case True{}:
      "ok"
    case False{}:
      match r:
        case C.KCordic{c, s}:
          U32.show(c) ++ " " ++ U32.show(s)

def cerr(+a: U32, +wc: U32, +ws: U32) -> String:
  cerr.show(within(C.KMath.cordic(a), wc, ws), C.KMath.cordic(a))

# every (angle, cos, sin) triple within the bound
def cordic_ok(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{a, Con{wc, Con{ws, rest}}}:
      Bool.and(within(C.KMath.cordic(a), wc, ws), cordic_ok(rest))
    case o:
      True{}
