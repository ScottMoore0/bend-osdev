import Base
import ../word64/word64.bend as W
import ./error.bend as E
import ./path.bend as P
import ./rights.bend as R
import ./net.bend as N
import ./scope.bend as S
import ./abi.bend as A
import ./ruleset.bend as RS
import ./domain.bend as D
import ./refer.bend as F
import ./landlock.bend as L
import ./LAWS.bend as Laws

# Contradictions

def b.bool_t(+x: Bool) -> Type:
  match x:
    case True{}:
      Unit
    case False{}:
      Empty

def b.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : b.bool_t(_)
  Unit{}

def b.tf(+e: {True{} == False{} : Bool}) -> Empty:
  %e : b.bool_t(_)
  Unit{}

def res.t(-X: Data, +r: Result<&2, &2, E.LandlockError, X>) -> Type:
  match r:
    case Fail{+e}:
      Unit
    case Done{+v}:
      Empty

def res.fd(-X: Data, -e: E.LandlockError, -v: X, +h: {Fail{e} == Done{v} : Result<&2, &2, E.LandlockError, X>}) -> Empty:
  %h : res.t(X, _)
  Unit{}

def res.get(-X: Data, +r: Result<&2, &2, E.LandlockError, X>, +dflt: X) -> X:
  match r:
    case Fail{+e}:
      dflt
    case Done{+v}:
      v

def res.inj(-X: Data, -x: X, -y: X, +h: {Done{x} == Done{y} : Result<&2, &2, E.LandlockError, X>}) -> {x == y : X}:
  Equal.cong(Result<&2, &2, E.LandlockError, X>, X, r => res.get(X, r, x), Done{x}, Done{y}, h)

def dec.t(+d: F.LandlockDecision) -> Type:
  match d:
    case F.LandlockAllowed{}:
      Empty
    case _:
      Unit

def dec.na_access(+e: {F.LandlockDeniedAccess{} == F.LandlockAllowed{} : F.LandlockDecision}) -> Empty:
  %e : dec.t(_)
  Unit{}

def dec.na_reparent(+e: {F.LandlockDeniedReparent{} == F.LandlockAllowed{} : F.LandlockDecision}) -> Empty:
  %e : dec.t(_)
  Unit{}

def dec.na_scope(+e: {F.LandlockDeniedScope{} == F.LandlockAllowed{} : F.LandlockDecision}) -> Empty:
  %e : dec.t(_)
  Unit{}

# Bool

def b.and_intro(+x: Bool, +y: Bool, +hx: {x == True{} : Bool}, +hy: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  match x:
    case True{}:
      hy
    case False{}:
      Empty.absurd({Bool.and(False{}, y) == True{} : Bool}, b.ft(hx))

def b.and_l(+x: Bool, +y: Bool, +h: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, b.ft(h))

def b.and_r(+x: Bool, +y: Bool, +h: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      Empty.absurd({y == True{} : Bool}, b.ft(h))

def b.and_false_l(+x: Bool, +y: Bool, +h: {x == False{} : Bool}) -> {Bool.and(x, y) == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.and(True{}, y) == False{} : Bool}, b.tf(h))

def b.and_false_r(+x: Bool, +y: Bool, +h: {y == False{} : Bool}) -> {Bool.and(x, y) == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      h

def b.and_false(+x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def b.or_false(+x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def b.or_true_l(+x: Bool, +y: Bool, +h: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, y) == True{} : Bool}, b.ft(h))

def b.or_true_r(+x: Bool, +y: Bool, +h: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

def b.or_ff(+x: Bool, +y: Bool, +hx: {x == False{} : Bool}, +hy: {y == False{} : Bool}) -> {Bool.or(x, y) == False{} : Bool}:
  match x:
    case False{}:
      hy
    case True{}:
      Empty.absurd({Bool.or(True{}, y) == False{} : Bool}, b.tf(hx))

def b.or_r_of(+x: Bool, +y: Bool, +hx: {x == False{} : Bool}, +h: {Bool.or(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case False{}:
      h
    case True{}:
      Empty.absurd({y == True{} : Bool}, b.tf(hx))

def b.or_mono(+x1: Bool, +y1: Bool, +x2: Bool, +y2: Bool, hx: {x1 == True{} : Bool} -> {x2 == True{} : Bool}, hy: {y1 == True{} : Bool} -> {y2 == True{} : Bool}, +h: {Bool.or(x1, y1) == True{} : Bool}) -> {Bool.or(x2, y2) == True{} : Bool}:
  match x1:
    case True{}:
      b.or_true_l(x2, y2, hx({==}))
    case False{}:
      b.or_true_r(x2, y2, hy(h))

def b.imp_r(+x: Bool, +y: Bool, +h: {y == True{} : Bool}) -> {R.LandlockBits.imp(x, y) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      h

def b.imp_false(+x: Bool, +y: Bool, +h: {x == False{} : Bool}) -> {R.LandlockBits.imp(x, y) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({R.LandlockBits.imp(True{}, y) == True{} : Bool}, b.tf(h))

def b.imp_mono(+x: Bool, +y: Bool, +z: Bool, hyz: {y == True{} : Bool} -> {z == True{} : Bool}, +h: {R.LandlockBits.imp(x, y) == True{} : Bool}) -> {R.LandlockBits.imp(x, z) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      hyz(h)

def b.not_false(+x: Bool, +h: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool}, b.tf(h))

def b.not_true(+x: Bool, f: {x == True{} : Bool} -> Empty) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, f({==}))
    case False{}:
      {==}

def b.imp_mp(+x: Bool, +y: Bool, +h1: {R.LandlockBits.imp(x, y) == True{} : Bool}, +h2: {x == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      h1
    case False{}:
      Empty.absurd({y == True{} : Bool}, b.ft(h2))

def b.notx(+x: Bool, +h: {x == True{} : Bool}) -> {Bool.not(x) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.not(False{}) == False{} : Bool}, b.ft(h))

def b.eq_ft(-x: Bool, +h1: {x == True{} : Bool}, +h2: {x == False{} : Bool}) -> Empty:
  b.ft(Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, h2), h1))

# Nat

def nat.le_zero(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      {==}

def nat.le_succ(+x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+(+xp) 0n:
      Empty.absurd({Nat.is_le(1n+xp, 1n) == True{} : Bool}, b.ft(h))
    case 1n+(+xp) 1n+(+yp):
      nat.le_succ(xp, yp, h)

def nat.lt_le(+x: Nat, +y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(1n+x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, b.ft(h))
    case 0n 1n+(+yp):
      nat.le_zero(yp)
    case 1n+(+xp) 0n:
      Empty.absurd({Nat.is_le(2n+xp, 0n) == True{} : Bool}, b.ft(h))
    case 1n+(+xp) 1n+(+yp):
      nat.lt_le(xp, yp, h)

# Lists of Bools

def bits.nth_nil(+i: Nat) -> {R.LandlockBits.nth(i, Nil{}) == False{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+(+p):
      {==}

def bits.nth_zand(+i: Nat, +xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {R.LandlockBits.nth(i, R.LandlockBits.zand(xs, ys)) == Bool.and(R.LandlockBits.nth(i, xs), R.LandlockBits.nth(i, ys)) : Bool}:
  match i:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          match ys:
            case Nil{}:
              Equal.sym(Bool, Bool.and(x, False{}), False{}, b.and_false(x))
            case Con{+y, +yt}:
              {==}
    case 1n+(+p):
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          match ys:
            case Nil{}:
              Equal.sym(Bool, Bool.and(R.LandlockBits.nth(p, xt), False{}), False{}, b.and_false(R.LandlockBits.nth(p, xt)))
            case Con{+y, +yt}:
              bits.nth_zand(p, xt, yt)

def bits.nth_zor(+i: Nat, +xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {R.LandlockBits.nth(i, R.LandlockBits.zor(xs, ys)) == Bool.or(R.LandlockBits.nth(i, xs), R.LandlockBits.nth(i, ys)) : Bool}:
  match i:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          match ys:
            case Nil{}:
              Equal.sym(Bool, Bool.or(x, False{}), x, b.or_false(x))
            case Con{+y, +yt}:
              {==}
    case 1n+(+p):
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xt}:
          match ys:
            case Nil{}:
              Equal.sym(Bool, Bool.or(R.LandlockBits.nth(p, xt), False{}), R.LandlockBits.nth(p, xt), b.or_false(R.LandlockBits.nth(p, xt)))
            case Con{+y, +yt}:
              bits.nth_zor(p, xt, yt)

def bits.sub_nth(+i: Nat, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +h1: {R.LandlockBits.sub(xs, ys) == True{} : Bool}, +h2: {R.LandlockBits.nth(i, xs) == True{} : Bool}) -> {R.LandlockBits.nth(i, ys) == True{} : Bool}:
  match i:
    case 0n:
      match xs:
        case Nil{}:
          Empty.absurd({R.LandlockBits.nth(0n, ys) == True{} : Bool}, b.ft(h2))
        case Con{+x, +xt}:
          match ys:
            case Nil{}:
              Empty.absurd({False{} == True{} : Bool}, b.ft(Equal.trans(Bool, False{}, Bool.not(x), True{}, Equal.sym(Bool, Bool.not(x), False{}, b.notx(x, h2)), b.and_l(Bool.not(x), R.LandlockBits.sub(xt, Nil{}), h1))))
            case Con{+y, +yt}:
              b.imp_mp(x, y, b.and_l(R.LandlockBits.imp(x, y), R.LandlockBits.sub(xt, yt), h1), h2)
    case 1n+(+p):
      match xs:
        case Nil{}:
          Empty.absurd({R.LandlockBits.nth(1n+p, ys) == True{} : Bool}, b.ft(h2))
        case Con{+x, +xt}:
          match ys:
            case Nil{}:
              Empty.absurd({False{} == True{} : Bool}, b.ft(Equal.trans(Bool, False{}, R.LandlockBits.nth(p, Nil{}), True{}, Equal.sym(Bool, R.LandlockBits.nth(p, Nil{}), False{}, bits.nth_nil(p)), bits.sub_nth(p, xt, Nil{}, b.and_r(Bool.not(x), R.LandlockBits.sub(xt, Nil{}), h1), h2))))
            case Con{+y, +yt}:
              bits.sub_nth(p, xt, yt, b.and_r(R.LandlockBits.imp(x, y), R.LandlockBits.sub(xt, yt), h1), h2)

def bits.sub_false(+i: Nat, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +h1: {R.LandlockBits.nth(i, xs) == True{} : Bool}, +h2: {R.LandlockBits.nth(i, ys) == False{} : Bool}) -> {R.LandlockBits.sub(xs, ys) == False{} : Bool}:
  b.not_true(R.LandlockBits.sub(xs, ys), e => b.eq_ft(R.LandlockBits.nth(i, ys), bits.sub_nth(i, xs, ys, e, h1), h2))

# BEGIN GENERATED by gen/sets.py: sets
# LandlockFs: what has answers on a set built from Bools, and on the set operations

def fs.has_of_bools(+xs: List<&2, Bool>, +r: R.LandlockFsRight) -> {R.LandlockFs.has(R.LandlockFs.of_bools(xs), r) == R.LandlockBits.nth(R.LandlockFsRight.index(r), xs) : Bool}:
  match r:
    case R.LandlockExecute{}:
      {==}
    case R.LandlockWriteFile{}:
      {==}
    case R.LandlockReadFile{}:
      {==}
    case R.LandlockReadDir{}:
      {==}
    case R.LandlockRemoveDir{}:
      {==}
    case R.LandlockRemoveFile{}:
      {==}
    case R.LandlockMakeChar{}:
      {==}
    case R.LandlockMakeDir{}:
      {==}
    case R.LandlockMakeReg{}:
      {==}
    case R.LandlockMakeSock{}:
      {==}
    case R.LandlockMakeFifo{}:
      {==}
    case R.LandlockMakeBlock{}:
      {==}
    case R.LandlockMakeSym{}:
      {==}
    case R.LandlockRefer{}:
      {==}
    case R.LandlockTruncate{}:
      {==}
    case R.LandlockIoctlDev{}:
      {==}

def fs.has_inter(+a: R.LandlockFs, +b: R.LandlockFs, +r: R.LandlockFsRight) -> {R.LandlockFs.has(R.LandlockFs.inter(a, b), r) == Bool.and(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r)) : Bool}:
  Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.inter(a, b), r), R.LandlockBits.nth(R.LandlockFsRight.index(r), R.LandlockBits.zand(R.LandlockFs.bools(a), R.LandlockFs.bools(b))), Bool.and(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r)), fs.has_of_bools(R.LandlockBits.zand(R.LandlockFs.bools(a), R.LandlockFs.bools(b)), r), bits.nth_zand(R.LandlockFsRight.index(r), R.LandlockFs.bools(a), R.LandlockFs.bools(b)))

def fs.has_union(+a: R.LandlockFs, +b: R.LandlockFs, +r: R.LandlockFsRight) -> {R.LandlockFs.has(R.LandlockFs.union(a, b), r) == Bool.or(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r)) : Bool}:
  Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.union(a, b), r), R.LandlockBits.nth(R.LandlockFsRight.index(r), R.LandlockBits.zor(R.LandlockFs.bools(a), R.LandlockFs.bools(b))), Bool.or(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r)), fs.has_of_bools(R.LandlockBits.zor(R.LandlockFs.bools(a), R.LandlockFs.bools(b)), r), bits.nth_zor(R.LandlockFsRight.index(r), R.LandlockFs.bools(a), R.LandlockFs.bools(b)))

def fs.has_none(+r: R.LandlockFsRight) -> {R.LandlockFs.has(R.LandlockFs.none(), r) == False{} : Bool}:
  Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.none(), r), R.LandlockBits.nth(R.LandlockFsRight.index(r), Nil{}), False{}, fs.has_of_bools(Nil{}, r), bits.nth_nil(R.LandlockFsRight.index(r)))

def fs.subset_has(+a: R.LandlockFs, +b: R.LandlockFs, +r: R.LandlockFsRight, +h1: {R.LandlockFs.subset(a, b) == True{} : Bool}, +h2: {R.LandlockFs.has(a, r) == True{} : Bool}) -> {R.LandlockFs.has(b, r) == True{} : Bool}:
  bits.sub_nth(R.LandlockFsRight.index(r), R.LandlockFs.bools(a), R.LandlockFs.bools(b), h1, h2)

def fs.subset_false(+a: R.LandlockFs, +b: R.LandlockFs, +r: R.LandlockFsRight, +h1: {R.LandlockFs.has(a, r) == True{} : Bool}, +h2: {R.LandlockFs.has(b, r) == False{} : Bool}) -> {R.LandlockFs.subset(a, b) == False{} : Bool}:
  bits.sub_false(R.LandlockFsRight.index(r), R.LandlockFs.bools(a), R.LandlockFs.bools(b), h1, h2)

def fs.has_inter_intro(+a: R.LandlockFs, +b: R.LandlockFs, +r: R.LandlockFsRight, +ha: {R.LandlockFs.has(a, r) == True{} : Bool}, +hb: {R.LandlockFs.has(b, r) == True{} : Bool}) -> {R.LandlockFs.has(R.LandlockFs.inter(a, b), r) == True{} : Bool}:
  Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.inter(a, b), r), Bool.and(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r)), True{}, fs.has_inter(a, b, r), b.and_intro(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r), ha, hb))

def fs.has_union_l(+a: R.LandlockFs, +b: R.LandlockFs, +r: R.LandlockFsRight, +h: {R.LandlockFs.has(a, r) == True{} : Bool}) -> {R.LandlockFs.has(R.LandlockFs.union(a, b), r) == True{} : Bool}:
  Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.union(a, b), r), Bool.or(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r)), True{}, fs.has_union(a, b, r), b.or_true_l(R.LandlockFs.has(a, r), R.LandlockFs.has(b, r), h))

# LandlockNet: what has answers on a set built from Bools, and on the set operations

def nt.has_of_bools(+xs: List<&2, Bool>, +r: N.LandlockNetRight) -> {N.LandlockNet.has(N.LandlockNet.of_bools(xs), r) == R.LandlockBits.nth(N.LandlockNetRight.index(r), xs) : Bool}:
  match r:
    case N.LandlockBindTcp{}:
      {==}
    case N.LandlockConnectTcp{}:
      {==}

def nt.has_inter(+a: N.LandlockNet, +b: N.LandlockNet, +r: N.LandlockNetRight) -> {N.LandlockNet.has(N.LandlockNet.inter(a, b), r) == Bool.and(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r)) : Bool}:
  Equal.trans(Bool, N.LandlockNet.has(N.LandlockNet.inter(a, b), r), R.LandlockBits.nth(N.LandlockNetRight.index(r), R.LandlockBits.zand(N.LandlockNet.bools(a), N.LandlockNet.bools(b))), Bool.and(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r)), nt.has_of_bools(R.LandlockBits.zand(N.LandlockNet.bools(a), N.LandlockNet.bools(b)), r), bits.nth_zand(N.LandlockNetRight.index(r), N.LandlockNet.bools(a), N.LandlockNet.bools(b)))

def nt.has_union(+a: N.LandlockNet, +b: N.LandlockNet, +r: N.LandlockNetRight) -> {N.LandlockNet.has(N.LandlockNet.union(a, b), r) == Bool.or(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r)) : Bool}:
  Equal.trans(Bool, N.LandlockNet.has(N.LandlockNet.union(a, b), r), R.LandlockBits.nth(N.LandlockNetRight.index(r), R.LandlockBits.zor(N.LandlockNet.bools(a), N.LandlockNet.bools(b))), Bool.or(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r)), nt.has_of_bools(R.LandlockBits.zor(N.LandlockNet.bools(a), N.LandlockNet.bools(b)), r), bits.nth_zor(N.LandlockNetRight.index(r), N.LandlockNet.bools(a), N.LandlockNet.bools(b)))

def nt.has_none(+r: N.LandlockNetRight) -> {N.LandlockNet.has(N.LandlockNet.none(), r) == False{} : Bool}:
  Equal.trans(Bool, N.LandlockNet.has(N.LandlockNet.none(), r), R.LandlockBits.nth(N.LandlockNetRight.index(r), Nil{}), False{}, nt.has_of_bools(Nil{}, r), bits.nth_nil(N.LandlockNetRight.index(r)))

def nt.subset_has(+a: N.LandlockNet, +b: N.LandlockNet, +r: N.LandlockNetRight, +h1: {N.LandlockNet.subset(a, b) == True{} : Bool}, +h2: {N.LandlockNet.has(a, r) == True{} : Bool}) -> {N.LandlockNet.has(b, r) == True{} : Bool}:
  bits.sub_nth(N.LandlockNetRight.index(r), N.LandlockNet.bools(a), N.LandlockNet.bools(b), h1, h2)

def nt.subset_false(+a: N.LandlockNet, +b: N.LandlockNet, +r: N.LandlockNetRight, +h1: {N.LandlockNet.has(a, r) == True{} : Bool}, +h2: {N.LandlockNet.has(b, r) == False{} : Bool}) -> {N.LandlockNet.subset(a, b) == False{} : Bool}:
  bits.sub_false(N.LandlockNetRight.index(r), N.LandlockNet.bools(a), N.LandlockNet.bools(b), h1, h2)

def nt.has_inter_intro(+a: N.LandlockNet, +b: N.LandlockNet, +r: N.LandlockNetRight, +ha: {N.LandlockNet.has(a, r) == True{} : Bool}, +hb: {N.LandlockNet.has(b, r) == True{} : Bool}) -> {N.LandlockNet.has(N.LandlockNet.inter(a, b), r) == True{} : Bool}:
  Equal.trans(Bool, N.LandlockNet.has(N.LandlockNet.inter(a, b), r), Bool.and(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r)), True{}, nt.has_inter(a, b, r), b.and_intro(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r), ha, hb))

def nt.has_union_l(+a: N.LandlockNet, +b: N.LandlockNet, +r: N.LandlockNetRight, +h: {N.LandlockNet.has(a, r) == True{} : Bool}) -> {N.LandlockNet.has(N.LandlockNet.union(a, b), r) == True{} : Bool}:
  Equal.trans(Bool, N.LandlockNet.has(N.LandlockNet.union(a, b), r), Bool.or(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r)), True{}, nt.has_union(a, b, r), b.or_true_l(N.LandlockNet.has(a, r), N.LandlockNet.has(b, r), h))

# LandlockScope: what has answers on a set built from Bools, and on the set operations

def sp.has_of_bools(+xs: List<&2, Bool>, +r: S.LandlockScopeRight) -> {S.LandlockScope.has(S.LandlockScope.of_bools(xs), r) == R.LandlockBits.nth(S.LandlockScopeRight.index(r), xs) : Bool}:
  match r:
    case S.LandlockScopeAbstractUnix{}:
      {==}
    case S.LandlockScopeSignal{}:
      {==}

def sp.has_inter(+a: S.LandlockScope, +b: S.LandlockScope, +r: S.LandlockScopeRight) -> {S.LandlockScope.has(S.LandlockScope.inter(a, b), r) == Bool.and(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r)) : Bool}:
  Equal.trans(Bool, S.LandlockScope.has(S.LandlockScope.inter(a, b), r), R.LandlockBits.nth(S.LandlockScopeRight.index(r), R.LandlockBits.zand(S.LandlockScope.bools(a), S.LandlockScope.bools(b))), Bool.and(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r)), sp.has_of_bools(R.LandlockBits.zand(S.LandlockScope.bools(a), S.LandlockScope.bools(b)), r), bits.nth_zand(S.LandlockScopeRight.index(r), S.LandlockScope.bools(a), S.LandlockScope.bools(b)))

def sp.has_union(+a: S.LandlockScope, +b: S.LandlockScope, +r: S.LandlockScopeRight) -> {S.LandlockScope.has(S.LandlockScope.union(a, b), r) == Bool.or(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r)) : Bool}:
  Equal.trans(Bool, S.LandlockScope.has(S.LandlockScope.union(a, b), r), R.LandlockBits.nth(S.LandlockScopeRight.index(r), R.LandlockBits.zor(S.LandlockScope.bools(a), S.LandlockScope.bools(b))), Bool.or(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r)), sp.has_of_bools(R.LandlockBits.zor(S.LandlockScope.bools(a), S.LandlockScope.bools(b)), r), bits.nth_zor(S.LandlockScopeRight.index(r), S.LandlockScope.bools(a), S.LandlockScope.bools(b)))

def sp.has_none(+r: S.LandlockScopeRight) -> {S.LandlockScope.has(S.LandlockScope.none(), r) == False{} : Bool}:
  Equal.trans(Bool, S.LandlockScope.has(S.LandlockScope.none(), r), R.LandlockBits.nth(S.LandlockScopeRight.index(r), Nil{}), False{}, sp.has_of_bools(Nil{}, r), bits.nth_nil(S.LandlockScopeRight.index(r)))

def sp.subset_has(+a: S.LandlockScope, +b: S.LandlockScope, +r: S.LandlockScopeRight, +h1: {S.LandlockScope.subset(a, b) == True{} : Bool}, +h2: {S.LandlockScope.has(a, r) == True{} : Bool}) -> {S.LandlockScope.has(b, r) == True{} : Bool}:
  bits.sub_nth(S.LandlockScopeRight.index(r), S.LandlockScope.bools(a), S.LandlockScope.bools(b), h1, h2)

def sp.subset_false(+a: S.LandlockScope, +b: S.LandlockScope, +r: S.LandlockScopeRight, +h1: {S.LandlockScope.has(a, r) == True{} : Bool}, +h2: {S.LandlockScope.has(b, r) == False{} : Bool}) -> {S.LandlockScope.subset(a, b) == False{} : Bool}:
  bits.sub_false(S.LandlockScopeRight.index(r), S.LandlockScope.bools(a), S.LandlockScope.bools(b), h1, h2)

def sp.has_inter_intro(+a: S.LandlockScope, +b: S.LandlockScope, +r: S.LandlockScopeRight, +ha: {S.LandlockScope.has(a, r) == True{} : Bool}, +hb: {S.LandlockScope.has(b, r) == True{} : Bool}) -> {S.LandlockScope.has(S.LandlockScope.inter(a, b), r) == True{} : Bool}:
  Equal.trans(Bool, S.LandlockScope.has(S.LandlockScope.inter(a, b), r), Bool.and(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r)), True{}, sp.has_inter(a, b, r), b.and_intro(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r), ha, hb))

def sp.has_union_l(+a: S.LandlockScope, +b: S.LandlockScope, +r: S.LandlockScopeRight, +h: {S.LandlockScope.has(a, r) == True{} : Bool}) -> {S.LandlockScope.has(S.LandlockScope.union(a, b), r) == True{} : Bool}:
  Equal.trans(Bool, S.LandlockScope.has(S.LandlockScope.union(a, b), r), Bool.or(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r)), True{}, sp.has_union(a, b, r), b.or_true_l(S.LandlockScope.has(a, r), S.LandlockScope.has(b, r), h))

# END GENERATED: sets

# Equality is reflexive: U32 (bit by bit), names and paths

def u.bool_cmp(+x: Bool) -> {Bool.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def u.word(+n: Nat, +w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match w:
        case WCon{+b0, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, u.word(p, t)) : {Word.cmp.fin(b0, b0, _) == EQ{} : Cmp}
          u.bool_cmp(b0)

def u.u32(+x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, u.word(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def u.char(+c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      u.u32(x)

def u.name(+s: String) -> {P.LandlockPath.name_eq(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      b.and_intro(Char.is_eq(h, h), P.LandlockPath.name_eq(t, t), u.char(h), u.name(t))

def u.names(+xs: List<&2, String>) -> {P.LandlockPath.names_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      b.and_intro(P.LandlockPath.name_eq(x, x), P.LandlockPath.names_eq(xt, xt), u.name(x), u.names(xt))

def u.path(+p: P.LandlockPath) -> {P.LandlockPath.is_eq(p, p) == True{} : Bool}:
  match p:
    case P.LandlockPath{+xs}:
      u.names(xs)

# Beneath: a path joined with anything is beneath it, and beneath stays true
# when the path is extended

def pth.prefix_append(+xs: List<&2, String>, +ys: List<&2, String>) -> {P.LandlockPath.prefix(xs, List.append(&2, String, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      b.and_intro(P.LandlockPath.name_eq(x, x), P.LandlockPath.prefix(xt, List.append(&2, String, xt, ys)), u.name(x), pth.prefix_append(xt, ys))

def pth.beneath_join(+q: P.LandlockPath, +s: P.LandlockPath) -> {P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), q) == True{} : Bool}:
  match q s:
    case P.LandlockPath{+xs} P.LandlockPath{+ys}:
      pth.prefix_append(xs, ys)

def pth.prefix_ext(+xs: List<&2, String>, +qs: List<&2, String>, +ss: List<&2, String>, +h: {P.LandlockPath.prefix(xs, qs) == True{} : Bool}) -> {P.LandlockPath.prefix(xs, List.append(&2, String, qs, ss)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      match qs:
        case Nil{}:
          Empty.absurd({P.LandlockPath.prefix(Con{x, xt}, List.append(&2, String, Nil{}, ss)) == True{} : Bool}, b.ft(h))
        case Con{+y, +yt}:
          b.and_intro(P.LandlockPath.name_eq(x, y), P.LandlockPath.prefix(xt, List.append(&2, String, yt, ss)), b.and_l(P.LandlockPath.name_eq(x, y), P.LandlockPath.prefix(xt, yt), h), pth.prefix_ext(xt, yt, ss, b.and_r(P.LandlockPath.name_eq(x, y), P.LandlockPath.prefix(xt, yt), h)))

def pth.beneath_ext(+p: P.LandlockPath, +x: P.LandlockPath, +s: P.LandlockPath, +h: {P.LandlockPath.is_beneath(p, x) == True{} : Bool}) -> {P.LandlockPath.is_beneath(P.LandlockPath.join(p, s), x) == True{} : Bool}:
  match p x s:
    case P.LandlockPath{+ps} P.LandlockPath{+xs} P.LandlockPath{+ss}:
      pth.prefix_ext(xs, ps, ss, h)

# What each ABI version knows, right by right

def abi.fs_has(+v: Nat, +r: R.LandlockFsRight) -> {R.LandlockFs.has(A.LandlockAbi.fs(v), r) == A.LandlockAbi.knows_fs(v, r) : Bool}:
  match r:
# BEGIN GENERATED by gen/sets.py: fs_cases
    case R.LandlockExecute{}:
      {==}
    case R.LandlockWriteFile{}:
      {==}
    case R.LandlockReadFile{}:
      {==}
    case R.LandlockReadDir{}:
      {==}
    case R.LandlockRemoveDir{}:
      {==}
    case R.LandlockRemoveFile{}:
      {==}
    case R.LandlockMakeChar{}:
      {==}
    case R.LandlockMakeDir{}:
      {==}
    case R.LandlockMakeReg{}:
      {==}
    case R.LandlockMakeSock{}:
      {==}
    case R.LandlockMakeFifo{}:
      {==}
    case R.LandlockMakeBlock{}:
      {==}
    case R.LandlockMakeSym{}:
      {==}
    case R.LandlockRefer{}:
      {==}
    case R.LandlockTruncate{}:
      {==}
    case R.LandlockIoctlDev{}:
      {==}
# END GENERATED: fs_cases

def abi.net_has(+v: Nat, +r: N.LandlockNetRight) -> {N.LandlockNet.has(A.LandlockAbi.net(v), r) == A.LandlockAbi.knows_net(v, r) : Bool}:
  match r:
# BEGIN GENERATED by gen/sets.py: net_cases
    case N.LandlockBindTcp{}:
      {==}
    case N.LandlockConnectTcp{}:
      {==}
# END GENERATED: net_cases

def abi.scope_has(+v: Nat, +r: S.LandlockScopeRight) -> {S.LandlockScope.has(A.LandlockAbi.scope(v), r) == A.LandlockAbi.knows_scope(v, r) : Bool}:
  match r:
# BEGIN GENERATED by gen/sets.py: scope_cases
    case S.LandlockScopeAbstractUnix{}:
      {==}
    case S.LandlockScopeSignal{}:
      {==}
# END GENERATED: scope_cases

# The ruleset that handles nothing allows everything

def rs.allows_none(+p: P.LandlockPath, +r: R.LandlockFsRight) -> {RS.LandlockRuleset.allows(RS.LandlockRuleset.none(), p, r) == True{} : Bool}:
  match r:
# BEGIN GENERATED by gen/sets.py: fs_cases2
    case R.LandlockExecute{}:
      {==}
    case R.LandlockWriteFile{}:
      {==}
    case R.LandlockReadFile{}:
      {==}
    case R.LandlockReadDir{}:
      {==}
    case R.LandlockRemoveDir{}:
      {==}
    case R.LandlockRemoveFile{}:
      {==}
    case R.LandlockMakeChar{}:
      {==}
    case R.LandlockMakeDir{}:
      {==}
    case R.LandlockMakeReg{}:
      {==}
    case R.LandlockMakeSock{}:
      {==}
    case R.LandlockMakeFifo{}:
      {==}
    case R.LandlockMakeBlock{}:
      {==}
    case R.LandlockMakeSym{}:
      {==}
    case R.LandlockRefer{}:
      {==}
    case R.LandlockTruncate{}:
      {==}
    case R.LandlockIoctlDev{}:
      {==}
# END GENERATED: fs_cases2

def rs.net_none(+port: U32, +r: N.LandlockNetRight) -> {RS.LandlockRuleset.allows_net(RS.LandlockRuleset.none(), port, r) == True{} : Bool}:
  match r:
# BEGIN GENERATED by gen/sets.py: net_cases2
    case N.LandlockBindTcp{}:
      {==}
    case N.LandlockConnectTcp{}:
      {==}
# END GENERATED: net_cases2

def rs.scope_none(+id: U32, +ts: List<&2, U32>, +r: S.LandlockScopeRight) -> {S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(RS.LandlockRuleset.none()), id, ts, r) == True{} : Bool}:
  match r:
# BEGIN GENERATED by gen/sets.py: scope_cases2
    case S.LandlockScopeAbstractUnix{}:
      {==}
    case S.LandlockScopeSignal{}:
      {==}
# END GENERATED: scope_cases2

def rs.all_none(+req: List<&2, R.LandlockFsRight>, +p: P.LandlockPath) -> {RS.LandlockRuleset.allows_all(req, RS.LandlockRuleset.none(), p) == True{} : Bool}:
  match req:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      b.and_intro(RS.LandlockRuleset.allows(RS.LandlockRuleset.none(), p, r), RS.LandlockRuleset.allows_all(t, RS.LandlockRuleset.none(), p), rs.allows_none(p, r), rs.all_none(t, p))

# Decisions

def mono.of_bool(+x: Bool, +y: Bool, +dd: F.LandlockDecision, +h: {F.LandlockDecision.is_allowed(F.LandlockDecision.of_bool(Bool.and(x, y), dd)) == True{} : Bool}) -> {F.LandlockDecision.is_allowed(F.LandlockDecision.of_bool(y, dd)) == True{} : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      match y:
        case True{}:
          {==}
        case False{}:
          h

def mono.worse(+x: F.LandlockDecision, +y: F.LandlockDecision, +h: {F.LandlockDecision.is_allowed(F.LandlockDecision.worse(x, y)) == True{} : Bool}) -> {F.LandlockDecision.is_allowed(y) == True{} : Bool}:
  match x:
    case F.LandlockAllowed{}:
      h
    case F.LandlockDeniedAccess{}:
      Empty.absurd({F.LandlockDecision.is_allowed(y) == True{} : Bool}, b.ft(h))
    case F.LandlockDeniedReparent{}:
      match y:
        case F.LandlockAllowed{}:
          {==}
        case F.LandlockDeniedAccess{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
        case F.LandlockDeniedReparent{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
        case F.LandlockDeniedScope{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
    case F.LandlockDeniedScope{}:
      Empty.absurd({F.LandlockDecision.is_allowed(y) == True{} : Bool}, b.ft(h))

def w.left(+x: F.LandlockDecision, +y: F.LandlockDecision, +h: {F.LandlockDecision.is_allowed(F.LandlockDecision.worse(x, y)) == True{} : Bool}) -> {F.LandlockDecision.is_allowed(x) == True{} : Bool}:
  match x:
    case F.LandlockAllowed{}:
      {==}
    case F.LandlockDeniedAccess{}:
      Empty.absurd({False{} == True{} : Bool}, b.ft(h))
    case F.LandlockDeniedReparent{}:
      match y:
        case F.LandlockAllowed{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
        case F.LandlockDeniedAccess{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
        case F.LandlockDeniedReparent{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
        case F.LandlockDeniedScope{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))
    case F.LandlockDeniedScope{}:
      Empty.absurd({False{} == True{} : Bool}, b.ft(h))

def w.na(+x: F.LandlockDecision, +y: F.LandlockDecision, +h: {F.LandlockDecision.is_allowed(x) == False{} : Bool}) -> {F.LandlockDecision.is_allowed(F.LandlockDecision.worse(x, y)) == False{} : Bool}:
  match x:
    case F.LandlockAllowed{}:
      Empty.absurd({F.LandlockDecision.is_allowed(y) == False{} : Bool}, b.tf(h))
    case F.LandlockDeniedAccess{}:
      {==}
    case F.LandlockDeniedReparent{}:
      match y:
        case F.LandlockAllowed{}:
          {==}
        case F.LandlockDeniedAccess{}:
          {==}
        case F.LandlockDeniedReparent{}:
          {==}
        case F.LandlockDeniedScope{}:
          {==}
    case F.LandlockDeniedScope{}:
      {==}

def dec.rep_false(+acc: Bool, +rep: Bool, +h: {rep == False{} : Bool}) -> {F.LandlockDecision.is_allowed(F.LandlockRefer.decide(acc, rep)) == False{} : Bool}:
  match acc:
    case False{}:
      {==}
    case True{}:
      match rep:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({F.LandlockDecision.is_allowed(F.LandlockRefer.decide(True{}, True{})) == False{} : Bool}, b.tf(h))

def dec.rep_true(+acc: Bool, +rep: Bool, +h: {F.LandlockDecision.is_allowed(F.LandlockRefer.decide(acc, rep)) == True{} : Bool}) -> {rep == True{} : Bool}:
  match acc:
    case False{}:
      Empty.absurd({rep == True{} : Bool}, b.ft(h))
    case True{}:
      match rep:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, b.ft(h))

# Restriction is monotone

def Laws.push_monotone(d, id, rs, op, h):
  match d:
    case D.LandlockDomain{+ls}:
      match op:
        case L.LandlockOpOpen{+p, +r, +w, +t}:
          mono.of_bool(RS.LandlockRuleset.allows_all(L.Landlock.open_rights(r, w, t), rs, p), D.LandlockDomain.allows.go(ls, p, L.Landlock.open_rights(r, w, t)), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpReadDir{+p}:
          mono.of_bool(RS.LandlockRuleset.allows_all([R.LandlockReadDir{}], rs, p), D.LandlockDomain.allows.go(ls, p, [R.LandlockReadDir{}]), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpExec{+p}:
          mono.of_bool(RS.LandlockRuleset.allows_all([R.LandlockExecute{}, R.LandlockReadFile{}], rs, p), D.LandlockDomain.allows.go(ls, p, [R.LandlockExecute{}, R.LandlockReadFile{}]), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpTruncate{+p}:
          mono.of_bool(RS.LandlockRuleset.allows_all([R.LandlockTruncate{}], rs, p), D.LandlockDomain.allows.go(ls, p, [R.LandlockTruncate{}]), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpIoctl{+p}:
          mono.of_bool(RS.LandlockRuleset.allows_all([R.LandlockIoctlDev{}], rs, p), D.LandlockDomain.allows.go(ls, p, [R.LandlockIoctlDev{}]), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpCreate{+p, +k}:
          mono.of_bool(RS.LandlockRuleset.allows_all([R.LandlockFileKind.make_right(k)], rs, p), D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpRemove{+p, +k}:
          mono.of_bool(RS.LandlockRuleset.allows_all([R.LandlockFileKind.remove_right(k)], rs, p), D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.remove_right(k)]), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpRename{+a, +c, +k}:
          mono.worse(F.LandlockRefer.layer(rs, a, c, k, P.LandlockPath.is_eq(a, c), True{}), F.LandlockRefer.go(ls, a, c, k, P.LandlockPath.is_eq(a, c), True{}), h)
        case L.LandlockOpLink{+a, +c, +k}:
          mono.worse(F.LandlockRefer.layer(rs, a, c, k, P.LandlockPath.is_eq(a, c), False{}), F.LandlockRefer.go(ls, a, c, k, P.LandlockPath.is_eq(a, c), False{}), h)
        case L.LandlockOpBind{+port}:
          mono.of_bool(RS.LandlockRuleset.allows_net(rs, port, N.LandlockBindTcp{}), D.LandlockDomain.allows_net.go(ls, port, N.LandlockBindTcp{}), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpConnect{+port}:
          mono.of_bool(RS.LandlockRuleset.allows_net(rs, port, N.LandlockConnectTcp{}), D.LandlockDomain.allows_net.go(ls, port, N.LandlockConnectTcp{}), F.LandlockDeniedAccess{}, h)
        case L.LandlockOpSignal{+t}:
          mono.of_bool(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(rs), id, D.LandlockDomain.ids(t), S.LandlockScopeSignal{}), D.LandlockDomain.allows_scope.go(ls, D.LandlockDomain.ids(t), S.LandlockScopeSignal{}), F.LandlockDeniedScope{}, h)
        case L.LandlockOpConnectAbstract{+t}:
          mono.of_bool(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(rs), id, D.LandlockDomain.ids(t), S.LandlockScopeAbstractUnix{}), D.LandlockDomain.allows_scope.go(ls, D.LandlockDomain.ids(t), S.LandlockScopeAbstractUnix{}), F.LandlockDeniedScope{}, h)

def Laws.witness_push_monotone():
  {==}

# restrict_self either refuses, leaves the domain as it is, or pushes the
# layer; each case reduces to push_monotone (or to nothing)

def rsm.tr(-t2: L.LandlockThread, -tx: L.LandlockThread, -op: L.LandlockOp, +e: {t2 == tx : L.LandlockThread}, +h: {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(t2), op)) == True{} : Bool}) -> {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(tx), op)) == True{} : Bool}:
  %e : {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(_), op)) == True{} : Bool}
  h

def rsm.dom(+nothing: Bool, +room: Bool, +d: D.LandlockDomain, +nnp: Bool, +cap: Bool, +id: U32, +rs: RS.LandlockRuleset, +t2: L.LandlockThread, +op: L.LandlockOp, +h1: {L.Landlock.restrict_self.wrap(D.LandlockDomain.restrict.go(nothing, room, d, id, rs), nnp, cap) == Done{t2} : Result<&2, &2, E.LandlockError, L.LandlockThread>}, +h2: {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(t2), op)) == True{} : Bool}) -> {F.LandlockDecision.is_allowed(L.Landlock.check(d, op)) == True{} : Bool}:
  match nothing:
    case True{}:
      rsm.tr(t2, L.LandlockThread{d, nnp, cap}, op, Equal.sym(L.LandlockThread, L.LandlockThread{d, nnp, cap}, t2, res.inj(L.LandlockThread, L.LandlockThread{d, nnp, cap}, t2, h1)), h2)
    case False{}:
      match room:
        case False{}:
          Empty.absurd({F.LandlockDecision.is_allowed(L.Landlock.check(d, op)) == True{} : Bool}, res.fd(L.LandlockThread, E.LandlockTooManyLayers{}, t2, h1))
        case True{}:
          Laws.push_monotone(d, id, rs, op, rsm.tr(t2, L.LandlockThread{D.LandlockDomain.push(d, id, rs), nnp, cap}, op, Equal.sym(L.LandlockThread, L.LandlockThread{D.LandlockDomain.push(d, id, rs), nnp, cap}, t2, res.inj(L.LandlockThread, L.LandlockThread{D.LandlockDomain.push(d, id, rs), nnp, cap}, t2, h1)), h2))

def rsm.go(+may: Bool, +max: Nat, +d: D.LandlockDomain, +nnp: Bool, +cap: Bool, +id: U32, +rs: RS.LandlockRuleset, +t2: L.LandlockThread, +op: L.LandlockOp, +h1: {L.Landlock.restrict_self.go(may, max, d, nnp, cap, id, rs) == Done{t2} : Result<&2, &2, E.LandlockError, L.LandlockThread>}, +h2: {F.LandlockDecision.is_allowed(L.Landlock.check(L.LandlockThread.domain(t2), op)) == True{} : Bool}) -> {F.LandlockDecision.is_allowed(L.Landlock.check(d, op)) == True{} : Bool}:
  match may:
    case False{}:
      Empty.absurd({F.LandlockDecision.is_allowed(L.Landlock.check(d, op)) == True{} : Bool}, res.fd(L.LandlockThread, E.LandlockNoNewPrivs{}, t2, h1))
    case True{}:
      rsm.dom(RS.LandlockRuleset.is_none(rs), Nat.is_lt(D.LandlockDomain.depth(d), max), d, nnp, cap, id, rs, t2, op, h1, h2)

def Laws.restrict_monotone(o, t, id, rs, t2, op, h1, h2):
  match t:
    case L.LandlockThread{+d, +nnp, +cap}:
      rsm.go(Bool.or(nnp, cap), L.LandlockOptions.max_layers(o), d, nnp, cap, id, rs, t2, op, h1, h2)

def Laws.witness_restrict_monotone():
  {==}

def Laws.witness_restrict_monotone_allowed():
  {==}

# A ruleset that handles nothing

def em.of_bool(+x: Bool, +y: Bool, +dd: F.LandlockDecision, +h: {x == True{} : Bool}) -> {F.LandlockDecision.of_bool(Bool.and(x, y), dd) == F.LandlockDecision.of_bool(y, dd) : F.LandlockDecision}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({F.LandlockDecision.of_bool(False{}, dd) == F.LandlockDecision.of_bool(y, dd) : F.LandlockDecision}, b.ft(h))

def em.worse(+x: F.LandlockDecision, +y: F.LandlockDecision, +h: {x == F.LandlockAllowed{} : F.LandlockDecision}) -> {F.LandlockDecision.worse(x, y) == y : F.LandlockDecision}:
  match x:
    case F.LandlockAllowed{}:
      {==}
    case F.LandlockDeniedAccess{}:
      Empty.absurd({F.LandlockDecision.worse(F.LandlockDeniedAccess{}, y) == y : F.LandlockDecision}, dec.na_access(h))
    case F.LandlockDeniedReparent{}:
      Empty.absurd({F.LandlockDecision.worse(F.LandlockDeniedReparent{}, y) == y : F.LandlockDecision}, dec.na_reparent(h))
    case F.LandlockDeniedScope{}:
      Empty.absurd({F.LandlockDecision.worse(F.LandlockDeniedScope{}, y) == y : F.LandlockDecision}, dec.na_scope(h))

def em.layer(+src: P.LandlockPath, +dst: P.LandlockPath, +k: R.LandlockFileKind, +same: Bool, +rm: Bool) -> {F.LandlockRefer.layer(RS.LandlockRuleset.none(), src, dst, k, same, rm) == F.LandlockAllowed{} : F.LandlockDecision}:
  match k same rm:
    case R.LandlockReg{} True{} True{}:
      {==}
    case R.LandlockReg{} True{} False{}:
      {==}
    case R.LandlockReg{} False{} True{}:
      {==}
    case R.LandlockReg{} False{} False{}:
      {==}
    case R.LandlockDir{} True{} True{}:
      {==}
    case R.LandlockDir{} True{} False{}:
      {==}
    case R.LandlockDir{} False{} True{}:
      {==}
    case R.LandlockDir{} False{} False{}:
      {==}
    case R.LandlockChr{} True{} True{}:
      {==}
    case R.LandlockChr{} True{} False{}:
      {==}
    case R.LandlockChr{} False{} True{}:
      {==}
    case R.LandlockChr{} False{} False{}:
      {==}
    case R.LandlockBlk{} True{} True{}:
      {==}
    case R.LandlockBlk{} True{} False{}:
      {==}
    case R.LandlockBlk{} False{} True{}:
      {==}
    case R.LandlockBlk{} False{} False{}:
      {==}
    case R.LandlockFifo{} True{} True{}:
      {==}
    case R.LandlockFifo{} True{} False{}:
      {==}
    case R.LandlockFifo{} False{} True{}:
      {==}
    case R.LandlockFifo{} False{} False{}:
      {==}
    case R.LandlockSock{} True{} True{}:
      {==}
    case R.LandlockSock{} True{} False{}:
      {==}
    case R.LandlockSock{} False{} True{}:
      {==}
    case R.LandlockSock{} False{} False{}:
      {==}
    case R.LandlockSym{} True{} True{}:
      {==}
    case R.LandlockSym{} True{} False{}:
      {==}
    case R.LandlockSym{} False{} True{}:
      {==}
    case R.LandlockSym{} False{} False{}:
      {==}

def Laws.empty_changes_nothing(d, id, op):
  match d:
    case D.LandlockDomain{+ls}:
      match op:
        case L.LandlockOpOpen{+p, +r, +w, +t}:
          em.of_bool(RS.LandlockRuleset.allows_all(L.Landlock.open_rights(r, w, t), RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, L.Landlock.open_rights(r, w, t)), F.LandlockDeniedAccess{}, rs.all_none(L.Landlock.open_rights(r, w, t), p))
        case L.LandlockOpReadDir{+p}:
          em.of_bool(RS.LandlockRuleset.allows_all([R.LandlockReadDir{}], RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, [R.LandlockReadDir{}]), F.LandlockDeniedAccess{}, rs.all_none([R.LandlockReadDir{}], p))
        case L.LandlockOpExec{+p}:
          em.of_bool(RS.LandlockRuleset.allows_all([R.LandlockExecute{}, R.LandlockReadFile{}], RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, [R.LandlockExecute{}, R.LandlockReadFile{}]), F.LandlockDeniedAccess{}, rs.all_none([R.LandlockExecute{}, R.LandlockReadFile{}], p))
        case L.LandlockOpTruncate{+p}:
          em.of_bool(RS.LandlockRuleset.allows_all([R.LandlockTruncate{}], RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, [R.LandlockTruncate{}]), F.LandlockDeniedAccess{}, rs.all_none([R.LandlockTruncate{}], p))
        case L.LandlockOpIoctl{+p}:
          em.of_bool(RS.LandlockRuleset.allows_all([R.LandlockIoctlDev{}], RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, [R.LandlockIoctlDev{}]), F.LandlockDeniedAccess{}, rs.all_none([R.LandlockIoctlDev{}], p))
        case L.LandlockOpCreate{+p, +k}:
          em.of_bool(RS.LandlockRuleset.allows_all([R.LandlockFileKind.make_right(k)], RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}, rs.all_none([R.LandlockFileKind.make_right(k)], p))
        case L.LandlockOpRemove{+p, +k}:
          em.of_bool(RS.LandlockRuleset.allows_all([R.LandlockFileKind.remove_right(k)], RS.LandlockRuleset.none(), p), D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.remove_right(k)]), F.LandlockDeniedAccess{}, rs.all_none([R.LandlockFileKind.remove_right(k)], p))
        case L.LandlockOpRename{+a, +c, +k}:
          em.worse(F.LandlockRefer.layer(RS.LandlockRuleset.none(), a, c, k, P.LandlockPath.is_eq(a, c), True{}), F.LandlockRefer.go(ls, a, c, k, P.LandlockPath.is_eq(a, c), True{}), em.layer(a, c, k, P.LandlockPath.is_eq(a, c), True{}))
        case L.LandlockOpLink{+a, +c, +k}:
          em.worse(F.LandlockRefer.layer(RS.LandlockRuleset.none(), a, c, k, P.LandlockPath.is_eq(a, c), False{}), F.LandlockRefer.go(ls, a, c, k, P.LandlockPath.is_eq(a, c), False{}), em.layer(a, c, k, P.LandlockPath.is_eq(a, c), False{}))
        case L.LandlockOpBind{+port}:
          em.of_bool(RS.LandlockRuleset.allows_net(RS.LandlockRuleset.none(), port, N.LandlockBindTcp{}), D.LandlockDomain.allows_net.go(ls, port, N.LandlockBindTcp{}), F.LandlockDeniedAccess{}, rs.net_none(port, N.LandlockBindTcp{}))
        case L.LandlockOpConnect{+port}:
          em.of_bool(RS.LandlockRuleset.allows_net(RS.LandlockRuleset.none(), port, N.LandlockConnectTcp{}), D.LandlockDomain.allows_net.go(ls, port, N.LandlockConnectTcp{}), F.LandlockDeniedAccess{}, rs.net_none(port, N.LandlockConnectTcp{}))
        case L.LandlockOpSignal{+t}:
          em.of_bool(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(RS.LandlockRuleset.none()), id, D.LandlockDomain.ids(t), S.LandlockScopeSignal{}), D.LandlockDomain.allows_scope.go(ls, D.LandlockDomain.ids(t), S.LandlockScopeSignal{}), F.LandlockDeniedScope{}, rs.scope_none(id, D.LandlockDomain.ids(t), S.LandlockScopeSignal{}))
        case L.LandlockOpConnectAbstract{+t}:
          em.of_bool(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(RS.LandlockRuleset.none()), id, D.LandlockDomain.ids(t), S.LandlockScopeAbstractUnix{}), D.LandlockDomain.allows_scope.go(ls, D.LandlockDomain.ids(t), S.LandlockScopeAbstractUnix{}), F.LandlockDeniedScope{}, rs.scope_none(id, D.LandlockDomain.ids(t), S.LandlockScopeAbstractUnix{}))

def Laws.empty_restrict_unchanged(max, d, id):
  {==}

# A right a layer does not handle

def un.and1(+x: Bool, +y: Bool, +h: {x == True{} : Bool}) -> {Bool.and(x, y) == y : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == y : Bool}, b.ft(h))

def un.and2(+x: Bool, +y: Bool, +h: {x == True{} : Bool}) -> {Bool.and(Bool.and(x, True{}), y) == y : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == y : Bool}, b.ft(h))

def Laws.unhandled_fs_not_refused(d, id, rs, p, r, h):
  match d:
    case D.LandlockDomain{+ls}:
      un.and2(RS.LandlockRuleset.allows(rs, p, r), D.LandlockDomain.allows.go(ls, p, [r]), b.imp_false(RS.LandlockRuleset.handles(rs, r), R.LandlockFs.has(RS.LandlockRuleset.granted(rs, p), r), h))

def Laws.witness_unhandled_fs():
  {==}

def Laws.unhandled_net_not_refused(d, id, rs, port, r, h):
  match d:
    case D.LandlockDomain{+ls}:
      un.and1(RS.LandlockRuleset.allows_net(rs, port, r), D.LandlockDomain.allows_net.go(ls, port, r), b.imp_false(RS.LandlockRuleset.handles_net(rs, r), N.LandlockNet.has(RS.LandlockRuleset.granted_net(rs, port), r), h))

def Laws.witness_unhandled_net():
  {==}

def Laws.unscoped_not_refused(d, id, rs, target, x, h):
  match d:
    case D.LandlockDomain{+ls}:
      un.and1(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(rs), id, D.LandlockDomain.ids(target), x), D.LandlockDomain.allows_scope.go(ls, D.LandlockDomain.ids(target), x), b.imp_false(S.LandlockScope.has(RS.LandlockRuleset.scoped(rs), x), S.LandlockScope.member(D.LandlockDomain.ids(target), id), h))

def Laws.witness_unscoped():
  {==}

# REFER

def Laws.refer_always_handled(rs, h):
  b.not_false(R.LandlockFs.is_empty(RS.LandlockRuleset.handled_fs(rs)), h)

def b.imp_tf(+x: Bool, +y: Bool, +hx: {x == True{} : Bool}, +hy: {y == False{} : Bool}) -> {R.LandlockBits.imp(x, y) == False{} : Bool}:
  match x:
    case True{}:
      hy
    case False{}:
      Empty.absurd({True{} == False{} : Bool}, b.ft(hx))

def Laws.refer_refused_unless_handled(rs, p, h1, h2):
  match rs:
    case RS.LandlockRuleset{+f, +n, +sc, +ps, +qs}:
      b.imp_tf(Bool.not(R.LandlockFs.is_empty(f)), R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, p)), R.LandlockRefer{}), b.not_false(R.LandlockFs.is_empty(f), h1), Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, p)), R.LandlockRefer{}), Bool.and(R.LandlockFs.has(f, R.LandlockRefer{}), R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, p), R.LandlockRefer{})), False{}, fs.has_inter(f, RS.LandlockRuleset.beneath(ps, p), R.LandlockRefer{}), b.and_false_l(R.LandlockFs.has(f, R.LandlockRefer{}), R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, p), R.LandlockRefer{}), h2)))

def Laws.witness_refer():
  {==}

# Path-beneath rules are inherited

def ap.pick(+hit: Bool, +a: R.LandlockFs, +r: R.LandlockFsRight, +hh: {hit == True{} : Bool}, +ha: {R.LandlockFs.has(a, r) == True{} : Bool}) -> {R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(hit, a), r) == True{} : Bool}:
  match hit:
    case True{}:
      ha
    case False{}:
      Empty.absurd({R.LandlockFs.has(R.LandlockFs.none(), r) == True{} : Bool}, b.ft(hh))

def ap.with(+rs: RS.LandlockRuleset, +q: P.LandlockPath, +a: R.LandlockFs, +s: P.LandlockPath, +r: R.LandlockFsRight, +hs: {R.LandlockFs.subset(a, RS.LandlockRuleset.handled_fs(rs)) == True{} : Bool}, +h2: {R.LandlockFs.has(a, r) == True{} : Bool}) -> {RS.LandlockRuleset.allows(RS.LandlockRuleset.with_path(rs, q, a), P.LandlockPath.join(q, s), r) == True{} : Bool}:
  match rs:
    case RS.LandlockRuleset{+f, +n, +sc, +ps, +qs}:
      b.imp_r(RS.LandlockRuleset.handles(RS.LandlockRuleset.with_path(RS.LandlockRuleset{f, n, sc, ps, qs}, q, a), r), R.LandlockFs.has(R.LandlockFs.inter(f, R.LandlockFs.union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), q), a), RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s)))), r), fs.has_inter_intro(f, R.LandlockFs.union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), q), a), RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s))), r, fs.subset_has(a, f, r, hs, h2), fs.has_union_l(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), q), a), RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s)), r, ap.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), q), a, r, pth.beneath_join(q, s), h2))))

def ap.go(+empty: Bool, +handled: Bool, +fits: Bool, +rs: RS.LandlockRuleset, +q: P.LandlockPath, +a: R.LandlockFs, +rs2: RS.LandlockRuleset, +s: P.LandlockPath, +r: R.LandlockFsRight, +eh: {handled == R.LandlockFs.subset(a, RS.LandlockRuleset.handled_fs(rs)) : Bool}, +h1: {RS.LandlockRuleset.add_path.go(empty, handled, fits, rs, q, a) == Done{rs2} : Result<&2, &2, E.LandlockError, RS.LandlockRuleset>}, +h2: {R.LandlockFs.has(a, r) == True{} : Bool}) -> {RS.LandlockRuleset.allows(rs2, P.LandlockPath.join(q, s), r) == True{} : Bool}:
  match empty:
    case True{}:
      Empty.absurd({RS.LandlockRuleset.allows(rs2, P.LandlockPath.join(q, s), r) == True{} : Bool}, res.fd(RS.LandlockRuleset, E.LandlockEmptyRule{}, rs2, h1))
    case False{}:
      match handled:
        case False{}:
          Empty.absurd({RS.LandlockRuleset.allows(rs2, P.LandlockPath.join(q, s), r) == True{} : Bool}, res.fd(RS.LandlockRuleset, E.LandlockRuleNotHandled{}, rs2, h1))
        case True{}:
          match fits:
            case False{}:
              Empty.absurd({RS.LandlockRuleset.allows(rs2, P.LandlockPath.join(q, s), r) == True{} : Bool}, res.fd(RS.LandlockRuleset, E.LandlockDirRightOnFile{}, rs2, h1))
            case True{}:
              %res.inj(RS.LandlockRuleset, RS.LandlockRuleset.with_path(rs, q, a), rs2, h1) : {RS.LandlockRuleset.allows(_, P.LandlockPath.join(q, s), r) == True{} : Bool}
              ap.with(rs, q, a, s, r, Equal.sym(Bool, True{}, R.LandlockFs.subset(a, RS.LandlockRuleset.handled_fs(rs)), eh), h2)

def Laws.rule_applies_beneath(rs, q, is_dir, a, rs2, s, r, h1, h2):
  ap.go(R.LandlockFs.is_empty(a), R.LandlockFs.subset(a, RS.LandlockRuleset.handled_fs(rs)), Bool.or(is_dir, R.LandlockFs.subset(a, R.LandlockFs.file_rights())), rs, q, a, rs2, s, r, {==}, h1, h2)

def Laws.witness_rule_applies_beneath():
  {==}

def Laws.witness_rule_applies_beneath_right():
  {==}

def inh.pick(+hit1: Bool, +hit2: Bool, +a: R.LandlockFs, +r: R.LandlockFsRight, hm: {hit1 == True{} : Bool} -> {hit2 == True{} : Bool}, +h: {R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(hit1, a), r) == True{} : Bool}) -> {R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(hit2, a), r) == True{} : Bool}:
  match hit1:
    case True{}:
      match hit2:
        case True{}:
          h
        case False{}:
          Empty.absurd({R.LandlockFs.has(R.LandlockFs.none(), r) == True{} : Bool}, b.ft(hm({==})))
    case False{}:
      Empty.absurd({R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(hit2, a), r) == True{} : Bool}, b.eq_ft(R.LandlockFs.has(R.LandlockFs.none(), r), h, fs.has_none(r)))

def inh.beneath(+ps: List<&2, RS.LandlockPathRule>, +q: P.LandlockPath, +s: P.LandlockPath, +r: R.LandlockFsRight, +h: {R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, q), r) == True{} : Bool}) -> {R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s)), r) == True{} : Bool}:
  match ps:
    case Nil{}:
      h
    case Con{RS.LandlockPathRule{+x, +a}, +t}:
      Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), x), a), RS.LandlockRuleset.beneath(t, P.LandlockPath.join(q, s))), r), Bool.or(R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), x), a), r), R.LandlockFs.has(RS.LandlockRuleset.beneath(t, P.LandlockPath.join(q, s)), r)), True{}, fs.has_union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), x), a), RS.LandlockRuleset.beneath(t, P.LandlockPath.join(q, s)), r), b.or_mono(R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(q, x), a), r), R.LandlockFs.has(RS.LandlockRuleset.beneath(t, q), r), R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), x), a), r), R.LandlockFs.has(RS.LandlockRuleset.beneath(t, P.LandlockPath.join(q, s)), r), e => inh.pick(P.LandlockPath.is_beneath(q, x), P.LandlockPath.is_beneath(P.LandlockPath.join(q, s), x), a, r, e2 => pth.beneath_ext(q, x, s, e2), e), e => inh.beneath(t, q, s, r, e), Equal.trans(Bool, Bool.or(R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(q, x), a), r), R.LandlockFs.has(RS.LandlockRuleset.beneath(t, q), r)), R.LandlockFs.has(R.LandlockFs.union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(q, x), a), RS.LandlockRuleset.beneath(t, q)), r), True{}, Equal.sym(Bool, R.LandlockFs.has(R.LandlockFs.union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(q, x), a), RS.LandlockRuleset.beneath(t, q)), r), Bool.or(R.LandlockFs.has(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(q, x), a), r), R.LandlockFs.has(RS.LandlockRuleset.beneath(t, q), r)), fs.has_union(RS.LandlockRuleset.beneath.pick(P.LandlockPath.is_beneath(q, x), a), RS.LandlockRuleset.beneath(t, q), r)), h)))

def inh.inter(+f: R.LandlockFs, +ps: List<&2, RS.LandlockPathRule>, +q: P.LandlockPath, +s: P.LandlockPath, +r: R.LandlockFsRight, +h: {R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, q)), r) == True{} : Bool}) -> {R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s))), r) == True{} : Bool}:
  +hi = Equal.trans(Bool, Bool.and(R.LandlockFs.has(f, r), R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, q), r)), R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, q)), r), True{}, Equal.sym(Bool, R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, q)), r), Bool.and(R.LandlockFs.has(f, r), R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, q), r)), fs.has_inter(f, RS.LandlockRuleset.beneath(ps, q), r)), h)
  fs.has_inter_intro(f, RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s)), r, b.and_l(R.LandlockFs.has(f, r), R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, q), r), hi), inh.beneath(ps, q, s, r, b.and_r(R.LandlockFs.has(f, r), R.LandlockFs.has(RS.LandlockRuleset.beneath(ps, q), r), hi)))

def inh.one(+rs: RS.LandlockRuleset, +q: P.LandlockPath, +s: P.LandlockPath, +r: R.LandlockFsRight, +h: {RS.LandlockRuleset.allows(rs, q, r) == True{} : Bool}) -> {RS.LandlockRuleset.allows(rs, P.LandlockPath.join(q, s), r) == True{} : Bool}:
  match rs:
    case RS.LandlockRuleset{+f, +n, +sc, +ps, +qs}:
      b.imp_mono(RS.LandlockRuleset.handles(RS.LandlockRuleset{f, n, sc, ps, qs}, r), R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, q)), r), R.LandlockFs.has(R.LandlockFs.inter(f, RS.LandlockRuleset.beneath(ps, P.LandlockPath.join(q, s))), r), e => inh.inter(f, ps, q, s, r, e), h)

def inh.all(+req: List<&2, R.LandlockFsRight>, +rs: RS.LandlockRuleset, +q: P.LandlockPath, +s: P.LandlockPath, +h: {RS.LandlockRuleset.allows_all(req, rs, q) == True{} : Bool}) -> {RS.LandlockRuleset.allows_all(req, rs, P.LandlockPath.join(q, s)) == True{} : Bool}:
  match req:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      b.and_intro(RS.LandlockRuleset.allows(rs, P.LandlockPath.join(q, s), r), RS.LandlockRuleset.allows_all(t, rs, P.LandlockPath.join(q, s)), inh.one(rs, q, s, r, b.and_l(RS.LandlockRuleset.allows(rs, q, r), RS.LandlockRuleset.allows_all(t, rs, q), h)), inh.all(t, rs, q, s, b.and_r(RS.LandlockRuleset.allows(rs, q, r), RS.LandlockRuleset.allows_all(t, rs, q), h)))

def inh.go(+ls: List<&2, D.LandlockLayer>, +q: P.LandlockPath, +s: P.LandlockPath, +req: List<&2, R.LandlockFsRight>, +h: {D.LandlockDomain.allows.go(ls, q, req) == True{} : Bool}) -> {D.LandlockDomain.allows.go(ls, P.LandlockPath.join(q, s), req) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{D.LandlockLayer{+id, +rs}, +t}:
      b.and_intro(RS.LandlockRuleset.allows_all(req, rs, P.LandlockPath.join(q, s)), D.LandlockDomain.allows.go(t, P.LandlockPath.join(q, s), req), inh.all(req, rs, q, s, b.and_l(RS.LandlockRuleset.allows_all(req, rs, q), D.LandlockDomain.allows.go(t, q, req), h)), inh.go(t, q, s, req, b.and_r(RS.LandlockRuleset.allows_all(req, rs, q), D.LandlockDomain.allows.go(t, q, req), h)))

def Laws.allowed_inherited(d, q, s, req, h):
  match d:
    case D.LandlockDomain{+ls}:
      inh.go(ls, q, s, req, h)

def Laws.witness_allowed_inherited():
  {==}

def ap2.pick(+hit: Bool, +a: N.LandlockNet, +r: N.LandlockNetRight, +hh: {hit == True{} : Bool}, +ha: {N.LandlockNet.has(a, r) == True{} : Bool}) -> {N.LandlockNet.has(N.LandlockNet.granted.pick(hit, a), r) == True{} : Bool}:
  match hit:
    case True{}:
      ha
    case False{}:
      Empty.absurd({N.LandlockNet.has(N.LandlockNet.none(), r) == True{} : Bool}, b.ft(hh))

def ap2.with(+rs: RS.LandlockRuleset, +port: U32, +a: N.LandlockNet, +r: N.LandlockNetRight, +hs: {N.LandlockNet.subset(a, RS.LandlockRuleset.handled_net(rs)) == True{} : Bool}, +h2: {N.LandlockNet.has(a, r) == True{} : Bool}) -> {RS.LandlockRuleset.allows_net(RS.LandlockRuleset.with_port(rs, port, a), port, r) == True{} : Bool}:
  match rs:
    case RS.LandlockRuleset{+f, +n, +sc, +ps, +qs}:
      b.imp_r(RS.LandlockRuleset.handles_net(RS.LandlockRuleset.with_port(RS.LandlockRuleset{f, n, sc, ps, qs}, port, a), r), N.LandlockNet.has(N.LandlockNet.inter(n, N.LandlockNet.union(N.LandlockNet.granted.pick(U32.is_eq(port, port), a), N.LandlockNet.granted(qs, port))), r), nt.has_inter_intro(n, N.LandlockNet.union(N.LandlockNet.granted.pick(U32.is_eq(port, port), a), N.LandlockNet.granted(qs, port)), r, nt.subset_has(a, n, r, hs, h2), nt.has_union_l(N.LandlockNet.granted.pick(U32.is_eq(port, port), a), N.LandlockNet.granted(qs, port), r, ap2.pick(U32.is_eq(port, port), a, r, u.u32(port), h2))))

def ap2.go(+empty: Bool, +handled: Bool, +fits: Bool, +rs: RS.LandlockRuleset, +port: U32, +a: N.LandlockNet, +rs2: RS.LandlockRuleset, +r: N.LandlockNetRight, +eh: {handled == N.LandlockNet.subset(a, RS.LandlockRuleset.handled_net(rs)) : Bool}, +h1: {RS.LandlockRuleset.add_port.go(empty, handled, fits, rs, port, a) == Done{rs2} : Result<&2, &2, E.LandlockError, RS.LandlockRuleset>}, +h2: {N.LandlockNet.has(a, r) == True{} : Bool}) -> {RS.LandlockRuleset.allows_net(rs2, port, r) == True{} : Bool}:
  match empty:
    case True{}:
      Empty.absurd({RS.LandlockRuleset.allows_net(rs2, port, r) == True{} : Bool}, res.fd(RS.LandlockRuleset, E.LandlockEmptyRule{}, rs2, h1))
    case False{}:
      match handled:
        case False{}:
          Empty.absurd({RS.LandlockRuleset.allows_net(rs2, port, r) == True{} : Bool}, res.fd(RS.LandlockRuleset, E.LandlockRuleNotHandled{}, rs2, h1))
        case True{}:
          match fits:
            case False{}:
              Empty.absurd({RS.LandlockRuleset.allows_net(rs2, port, r) == True{} : Bool}, res.fd(RS.LandlockRuleset, E.LandlockBadPort{}, rs2, h1))
            case True{}:
              %res.inj(RS.LandlockRuleset, RS.LandlockRuleset.with_port(rs, port, a), rs2, h1) : {RS.LandlockRuleset.allows_net(_, port, r) == True{} : Bool}
              ap2.with(rs, port, a, r, Equal.sym(Bool, True{}, N.LandlockNet.subset(a, RS.LandlockRuleset.handled_net(rs)), eh), h2)

def Laws.port_rule_applies(rs, port, a, rs2, r, h1, h2):
  ap2.go(N.LandlockNet.is_empty(a), N.LandlockNet.subset(a, RS.LandlockRuleset.handled_net(rs)), U32.is_le(port, N.LandlockNet.max_port()), rs, port, a, rs2, r, {==}, h1, h2)

def Laws.witness_port_rule():
  {==}

def Laws.witness_port_rule_right():
  {==}

# Rename and link within one directory

def sd.comb(+x: Bool, +y: Bool, +g: Bool) -> {F.LandlockDecision.worse(F.LandlockRefer.decide(Bool.and(x, y), True{}), F.LandlockDecision.of_bool(g, F.LandlockDeniedAccess{})) == F.LandlockDecision.of_bool(Bool.and(Bool.and(x, Bool.and(y, True{})), g), F.LandlockDeniedAccess{}) : F.LandlockDecision}:
  match x y g:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def sd.combl(+y: Bool, +g: Bool) -> {F.LandlockDecision.worse(F.LandlockRefer.decide(y, True{}), F.LandlockDecision.of_bool(g, F.LandlockDeniedAccess{})) == F.LandlockDecision.of_bool(Bool.and(Bool.and(y, True{}), g), F.LandlockDeniedAccess{}) : F.LandlockDecision}:
  match y g:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def sd.go1(+ls: List<&2, D.LandlockLayer>, +p: P.LandlockPath, +k: R.LandlockFileKind) -> {F.LandlockRefer.go(ls, p, p, k, True{}, True{}) == F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}:
  match ls:
    case Nil{}:
      {==}
    case Con{D.LandlockLayer{+id, +rs}, +t}:
      %Equal.sym(F.LandlockDecision, F.LandlockRefer.go(t, p, p, k, True{}, True{}), F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(t, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}), sd.go1(t, p, k)) : {F.LandlockDecision.worse(F.LandlockRefer.layer(rs, p, p, k, True{}, True{}), _) == F.LandlockDecision.of_bool(Bool.and(RS.LandlockRuleset.allows_all([R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)], rs, p), D.LandlockDomain.allows.go(t, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)])), F.LandlockDeniedAccess{}) : F.LandlockDecision}
      sd.comb(RS.LandlockRuleset.allows(rs, p, R.LandlockFileKind.remove_right(k)), RS.LandlockRuleset.allows(rs, p, R.LandlockFileKind.make_right(k)), D.LandlockDomain.allows.go(t, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)]))

def sd.go(+ls: List<&2, D.LandlockLayer>, +p: P.LandlockPath, +k: R.LandlockFileKind, +same: Bool, +hs: {same == True{} : Bool}) -> {F.LandlockRefer.go(ls, p, p, k, same, True{}) == F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}:
  match same:
    case True{}:
      sd.go1(ls, p, k)
    case False{}:
      Empty.absurd({F.LandlockRefer.go(ls, p, p, k, False{}, True{}) == F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.remove_right(k), R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}, b.ft(hs))

def Laws.rename_same_dir(d, p, k):
  match d:
    case D.LandlockDomain{+ls}:
      sd.go(ls, p, k, P.LandlockPath.is_eq(p, p), u.path(p))

def sd.lgo1(+ls: List<&2, D.LandlockLayer>, +p: P.LandlockPath, +k: R.LandlockFileKind) -> {F.LandlockRefer.go(ls, p, p, k, True{}, False{}) == F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}:
  match ls:
    case Nil{}:
      {==}
    case Con{D.LandlockLayer{+id, +rs}, +t}:
      %Equal.sym(F.LandlockDecision, F.LandlockRefer.go(t, p, p, k, True{}, False{}), F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(t, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}), sd.lgo1(t, p, k)) : {F.LandlockDecision.worse(F.LandlockRefer.layer(rs, p, p, k, True{}, False{}), _) == F.LandlockDecision.of_bool(Bool.and(RS.LandlockRuleset.allows_all([R.LandlockFileKind.make_right(k)], rs, p), D.LandlockDomain.allows.go(t, p, [R.LandlockFileKind.make_right(k)])), F.LandlockDeniedAccess{}) : F.LandlockDecision}
      sd.combl(RS.LandlockRuleset.allows(rs, p, R.LandlockFileKind.make_right(k)), D.LandlockDomain.allows.go(t, p, [R.LandlockFileKind.make_right(k)]))

def sd.lgo(+ls: List<&2, D.LandlockLayer>, +p: P.LandlockPath, +k: R.LandlockFileKind, +same: Bool, +hs: {same == True{} : Bool}) -> {F.LandlockRefer.go(ls, p, p, k, same, False{}) == F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}:
  match same:
    case True{}:
      sd.lgo1(ls, p, k)
    case False{}:
      Empty.absurd({F.LandlockRefer.go(ls, p, p, k, False{}, False{}) == F.LandlockDecision.of_bool(D.LandlockDomain.allows.go(ls, p, [R.LandlockFileKind.make_right(k)]), F.LandlockDeniedAccess{}) : F.LandlockDecision}, b.ft(hs))

def Laws.link_same_dir(d, p, k):
  match d:
    case D.LandlockDomain{+ls}:
      sd.lgo(ls, p, k, P.LandlockPath.is_eq(p, p), u.path(p))

# Reparenting under a layer that handles filesystem rights but not REFER

def rn.layer(+rs: RS.LandlockRuleset, +src: P.LandlockPath, +dst: P.LandlockPath, +k: R.LandlockFileKind, +same: Bool, +rm: Bool, +hs: {same == False{} : Bool}, +hr: {RS.LandlockRuleset.allows(rs, src, R.LandlockRefer{}) == False{} : Bool}) -> {F.LandlockDecision.is_allowed(F.LandlockRefer.layer(rs, src, dst, k, same, rm)) == False{} : Bool}:
  dec.rep_false(Bool.and(R.LandlockBits.imp(rm, RS.LandlockRuleset.allows(rs, src, R.LandlockFileKind.remove_right(k))), RS.LandlockRuleset.allows(rs, dst, R.LandlockFileKind.make_right(k))), Bool.or(same, F.LandlockRefer.reparent_ok(rs, src, dst, k)), b.or_ff(same, F.LandlockRefer.reparent_ok(rs, src, dst, k), hs, b.and_false_l(RS.LandlockRuleset.allows(rs, src, R.LandlockRefer{}), Bool.and(RS.LandlockRuleset.allows(rs, dst, R.LandlockRefer{}), F.LandlockRefer.no_gain(rs, src, dst, k)), hr)))

def Laws.reparent_needs_refer_rename(d, id, rs, src, dst, k, h1, h2, h3):
  match d:
    case D.LandlockDomain{+ls}:
      w.na(F.LandlockRefer.layer(rs, src, dst, k, P.LandlockPath.is_eq(src, dst), True{}), F.LandlockRefer.go(ls, src, dst, k, P.LandlockPath.is_eq(src, dst), True{}), rn.layer(rs, src, dst, k, P.LandlockPath.is_eq(src, dst), True{}, h3, Laws.refer_refused_unless_handled(rs, src, h1, h2)))

def Laws.reparent_needs_refer_link(d, id, rs, src, dst, k, h1, h2, h3):
  match d:
    case D.LandlockDomain{+ls}:
      w.na(F.LandlockRefer.layer(rs, src, dst, k, P.LandlockPath.is_eq(src, dst), False{}), F.LandlockRefer.go(ls, src, dst, k, P.LandlockPath.is_eq(src, dst), False{}), rn.layer(rs, src, dst, k, P.LandlockPath.is_eq(src, dst), False{}, h3, Laws.refer_refused_unless_handled(rs, src, h1, h2)))

def Laws.witness_reparent_needs_refer():
  {==}

# An allowed reparenting gains nothing

def ng.layer(+rs: RS.LandlockRuleset, +src: P.LandlockPath, +dst: P.LandlockPath, +k: R.LandlockFileKind, +r: R.LandlockFsRight, +same: Bool, +rm: Bool, +hs: {same == False{} : Bool}, +hl: {F.LandlockDecision.is_allowed(F.LandlockRefer.layer(rs, src, dst, k, same, rm)) == True{} : Bool}, +hc: {R.LandlockFs.has(R.LandlockFileKind.carried(k), r) == True{} : Bool}, +hd: {RS.LandlockRuleset.allows(rs, dst, r) == True{} : Bool}) -> {RS.LandlockRuleset.allows(rs, src, r) == True{} : Bool}:
  +hro = b.or_r_of(same, F.LandlockRefer.reparent_ok(rs, src, dst, k), hs, dec.rep_true(Bool.and(R.LandlockBits.imp(rm, RS.LandlockRuleset.allows(rs, src, R.LandlockFileKind.remove_right(k))), RS.LandlockRuleset.allows(rs, dst, R.LandlockFileKind.make_right(k))), Bool.or(same, F.LandlockRefer.reparent_ok(rs, src, dst, k)), hl))
  +hng = b.and_r(RS.LandlockRuleset.allows(rs, dst, R.LandlockRefer{}), F.LandlockRefer.no_gain(rs, src, dst, k), b.and_r(RS.LandlockRuleset.allows(rs, src, R.LandlockRefer{}), Bool.and(RS.LandlockRuleset.allows(rs, dst, R.LandlockRefer{}), F.LandlockRefer.no_gain(rs, src, dst, k)), hro))
  b.imp_mono(RS.LandlockRuleset.handles(rs, r), R.LandlockFs.has(RS.LandlockRuleset.granted(rs, dst), r), R.LandlockFs.has(RS.LandlockRuleset.granted(rs, src), r), e => fs.subset_has(R.LandlockFs.inter(RS.LandlockRuleset.granted(rs, dst), R.LandlockFileKind.carried(k)), RS.LandlockRuleset.granted(rs, src), r, hng, fs.has_inter_intro(RS.LandlockRuleset.granted(rs, dst), R.LandlockFileKind.carried(k), r, e, hc)), hd)

def ng.go(+ls: List<&2, D.LandlockLayer>, +src: P.LandlockPath, +dst: P.LandlockPath, +k: R.LandlockFileKind, +r: R.LandlockFsRight, +same: Bool, +rm: Bool, +hs: {same == False{} : Bool}, +ha: {F.LandlockDecision.is_allowed(F.LandlockRefer.go(ls, src, dst, k, same, rm)) == True{} : Bool}, +hc: {R.LandlockFs.has(R.LandlockFileKind.carried(k), r) == True{} : Bool}, +hd: {D.LandlockDomain.allows.go(ls, dst, [r]) == True{} : Bool}) -> {D.LandlockDomain.allows.go(ls, src, [r]) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{D.LandlockLayer{+id, +rs}, +t}:
      b.and_intro(Bool.and(RS.LandlockRuleset.allows(rs, src, r), True{}), D.LandlockDomain.allows.go(t, src, [r]), b.and_intro(RS.LandlockRuleset.allows(rs, src, r), True{}, ng.layer(rs, src, dst, k, r, same, rm, hs, w.left(F.LandlockRefer.layer(rs, src, dst, k, same, rm), F.LandlockRefer.go(t, src, dst, k, same, rm), ha), hc, b.and_l(RS.LandlockRuleset.allows(rs, dst, r), True{}, b.and_l(Bool.and(RS.LandlockRuleset.allows(rs, dst, r), True{}), D.LandlockDomain.allows.go(t, dst, [r]), hd))), {==}), ng.go(t, src, dst, k, r, same, rm, hs, mono.worse(F.LandlockRefer.layer(rs, src, dst, k, same, rm), F.LandlockRefer.go(t, src, dst, k, same, rm), ha), hc, b.and_r(Bool.and(RS.LandlockRuleset.allows(rs, dst, r), True{}), D.LandlockDomain.allows.go(t, dst, [r]), hd)))

def Laws.reparent_no_gain_rename(d, src, dst, k, r, h1, h2, h3, h4):
  match d:
    case D.LandlockDomain{+ls}:
      ng.go(ls, src, dst, k, r, P.LandlockPath.is_eq(src, dst), True{}, h1, h2, h3, h4)

def Laws.reparent_no_gain_link(d, src, dst, k, r, h1, h2, h3, h4):
  match d:
    case D.LandlockDomain{+ls}:
      ng.go(ls, src, dst, k, r, P.LandlockPath.is_eq(src, dst), False{}, h1, h2, h3, h4)

def Laws.witness_reparent_no_gain():
  {==}

# ABI versions

def Laws.abi_later_knows_fs(v, r, h):
  nat.le_succ(A.LandlockAbi.fs_since(r), v, h)

def Laws.abi_later_knows_net(v, r, h):
  nat.le_succ(A.LandlockAbi.net_since(r), v, h)

def Laws.abi_later_knows_scope(v, r, h):
  nat.le_succ(A.LandlockAbi.scope_since(r), v, h)

def Laws.witness_abi_knows():
  {==}

def cr.known_false(+known: Bool, +empty: Bool, +f: R.LandlockFs, +n: N.LandlockNet, +s: S.LandlockScope, +h: {known == False{} : Bool}) -> {L.Landlock.ok(RS.LandlockRuleset.create.go(known, empty, f, n, s)) == False{} : Bool}:
  match known:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({L.Landlock.ok(RS.LandlockRuleset.create.go(True{}, empty, f, n, s)) == False{} : Bool}, b.tf(h))

def Laws.strict_refuses_unknown_fs(v, m, f, n, s, r, h1, h2):
  match v:
    case 0n:
      {==}
    case 1n+(+p):
      cr.known_false(Bool.and(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p)))), Bool.and(R.LandlockFs.is_empty(f), Bool.and(N.LandlockNet.is_empty(n), S.LandlockScope.is_empty(s))), f, n, s, b.and_false_l(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p))), fs.subset_false(f, A.LandlockAbi.fs(1n+p), r, h1, Equal.trans(Bool, R.LandlockFs.has(A.LandlockAbi.fs(1n+p), r), A.LandlockAbi.knows_fs(1n+p, r), False{}, abi.fs_has(1n+p, r), h2))))

def Laws.strict_refuses_unknown_net(v, m, f, n, s, r, h1, h2):
  match v:
    case 0n:
      {==}
    case 1n+(+p):
      cr.known_false(Bool.and(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p)))), Bool.and(R.LandlockFs.is_empty(f), Bool.and(N.LandlockNet.is_empty(n), S.LandlockScope.is_empty(s))), f, n, s, b.and_false_r(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p))), b.and_false_l(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p)), nt.subset_false(n, A.LandlockAbi.net(1n+p), r, h1, Equal.trans(Bool, N.LandlockNet.has(A.LandlockAbi.net(1n+p), r), A.LandlockAbi.knows_net(1n+p, r), False{}, abi.net_has(1n+p, r), h2)))))

def Laws.strict_refuses_unknown_scope(v, m, f, n, s, r, h1, h2):
  match v:
    case 0n:
      {==}
    case 1n+(+p):
      cr.known_false(Bool.and(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p)))), Bool.and(R.LandlockFs.is_empty(f), Bool.and(N.LandlockNet.is_empty(n), S.LandlockScope.is_empty(s))), f, n, s, b.and_false_r(R.LandlockFs.subset(f, A.LandlockAbi.fs(1n+p)), Bool.and(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p))), b.and_false_r(N.LandlockNet.subset(n, A.LandlockAbi.net(1n+p)), S.LandlockScope.subset(s, A.LandlockAbi.scope(1n+p)), sp.subset_false(s, A.LandlockAbi.scope(1n+p), r, h1, Equal.trans(Bool, S.LandlockScope.has(A.LandlockAbi.scope(1n+p), r), A.LandlockAbi.knows_scope(1n+p, r), False{}, abi.scope_has(1n+p, r), h2)))))

def Laws.witness_strict_refuses():
  {==}

def Laws.best_effort_never_refuses(v, m, f, n, s):
  {==}

def Laws.best_effort_keeps_known_fs(v, f, n, s, r):
  Equal.trans(Bool, R.LandlockFs.has(R.LandlockFs.inter(f, A.LandlockAbi.fs(v)), r), Bool.and(R.LandlockFs.has(f, r), R.LandlockFs.has(A.LandlockAbi.fs(v), r)), Bool.and(R.LandlockFs.has(f, r), A.LandlockAbi.knows_fs(v, r)), fs.has_inter(f, A.LandlockAbi.fs(v), r), Equal.cong(Bool, Bool, x => Bool.and(R.LandlockFs.has(f, r), x), R.LandlockFs.has(A.LandlockAbi.fs(v), r), A.LandlockAbi.knows_fs(v, r), abi.fs_has(v, r)))

def Laws.best_effort_keeps_known_net(v, f, n, s, r):
  Equal.trans(Bool, N.LandlockNet.has(N.LandlockNet.inter(n, A.LandlockAbi.net(v)), r), Bool.and(N.LandlockNet.has(n, r), N.LandlockNet.has(A.LandlockAbi.net(v), r)), Bool.and(N.LandlockNet.has(n, r), A.LandlockAbi.knows_net(v, r)), nt.has_inter(n, A.LandlockAbi.net(v), r), Equal.cong(Bool, Bool, x => Bool.and(N.LandlockNet.has(n, r), x), N.LandlockNet.has(A.LandlockAbi.net(v), r), A.LandlockAbi.knows_net(v, r), abi.net_has(v, r)))

def Laws.best_effort_keeps_known_scope(v, f, n, s, r):
  Equal.trans(Bool, S.LandlockScope.has(S.LandlockScope.inter(s, A.LandlockAbi.scope(v)), r), Bool.and(S.LandlockScope.has(s, r), S.LandlockScope.has(A.LandlockAbi.scope(v), r)), Bool.and(S.LandlockScope.has(s, r), A.LandlockAbi.knows_scope(v, r)), sp.has_inter(s, A.LandlockAbi.scope(v), r), Equal.cong(Bool, Bool, x => Bool.and(S.LandlockScope.has(s, r), x), S.LandlockScope.has(A.LandlockAbi.scope(v), r), A.LandlockAbi.knows_scope(v, r), abi.scope_has(v, r)))

# The layer limit

def rb.go(+nothing: Bool, +room: Bool, +max: Nat, +ls: List<&2, D.LandlockLayer>, +id: U32, +rs: RS.LandlockRuleset, +d2: D.LandlockDomain, +er: {room == Nat.is_lt(List.length(&2, D.LandlockLayer, ls), max) : Bool}, +h1: {Nat.is_le(List.length(&2, D.LandlockLayer, ls), max) == True{} : Bool}, +h2: {D.LandlockDomain.restrict.go(nothing, room, D.LandlockDomain{ls}, id, rs) == Done{d2} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}) -> {Nat.is_le(D.LandlockDomain.depth(d2), max) == True{} : Bool}:
  match nothing:
    case True{}:
      %res.inj(D.LandlockDomain, D.LandlockDomain{ls}, d2, h2) : {Nat.is_le(D.LandlockDomain.depth(_), max) == True{} : Bool}
      h1
    case False{}:
      match room:
        case False{}:
          Empty.absurd({Nat.is_le(D.LandlockDomain.depth(d2), max) == True{} : Bool}, res.fd(D.LandlockDomain, E.LandlockTooManyLayers{}, d2, h2))
        case True{}:
          %res.inj(D.LandlockDomain, D.LandlockDomain.push(D.LandlockDomain{ls}, id, rs), d2, h2) : {Nat.is_le(D.LandlockDomain.depth(_), max) == True{} : Bool}
          nat.lt_le(List.length(&2, D.LandlockLayer, ls), max, Equal.sym(Bool, True{}, Nat.is_lt(List.length(&2, D.LandlockLayer, ls), max), er))

def Laws.restrict_bounded(max, d, id, rs, d2, h1, h2):
  match d:
    case D.LandlockDomain{+ls}:
      rb.go(RS.LandlockRuleset.is_none(rs), Nat.is_lt(List.length(&2, D.LandlockLayer, ls), max), max, ls, id, rs, d2, {==}, h1, h2)

def Laws.witness_restrict_bounded():
  {==}

def Laws.witness_restrict_bounded_depth():
  {==}

def rf.go(+nothing: Bool, +room: Bool, +d: D.LandlockDomain, +id: U32, +rs: RS.LandlockRuleset, +hn: {nothing == False{} : Bool}, +hr: {room == False{} : Bool}) -> {D.LandlockDomain.restrict.go(nothing, room, d, id, rs) == Fail{E.LandlockTooManyLayers{}} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}:
  match nothing:
    case True{}:
      Empty.absurd({Done{d} == Fail{E.LandlockTooManyLayers{}} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}, b.tf(hn))
    case False{}:
      match room:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({Done{D.LandlockDomain.push(d, id, rs)} == Fail{E.LandlockTooManyLayers{}} : Result<&2, &2, E.LandlockError, D.LandlockDomain>}, b.tf(hr))

def Laws.restrict_full_refused(max, d, id, rs, h1, h2):
  rf.go(RS.LandlockRuleset.is_none(rs), Nat.is_lt(D.LandlockDomain.depth(d), max), d, id, rs, h1, h2)

def Laws.witness_restrict_full():
  {==}

# Scoping

def sc.allm(+xs: List<&2, U32>, +ts: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +xt}:
      Bool.and(S.LandlockScope.member(ts, x), sc.allm(xt, ts))

def sc.all(+ls: List<&2, D.LandlockLayer>, +ts: List<&2, U32>, +x: S.LandlockScopeRight, +h: {sc.allm(D.LandlockDomain.ids.go(ls), ts) == True{} : Bool}) -> {D.LandlockDomain.allows_scope.go(ls, ts, x) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{D.LandlockLayer{+id, +rs}, +t}:
      b.and_intro(S.LandlockScope.layer_allows(RS.LandlockRuleset.scoped(rs), id, ts, x), D.LandlockDomain.allows_scope.go(t, ts, x), b.imp_r(S.LandlockScope.has(RS.LandlockRuleset.scoped(rs), x), S.LandlockScope.member(ts, id), b.and_l(S.LandlockScope.member(ts, id), sc.allm(D.LandlockDomain.ids.go(t), ts), h)), sc.all(t, ts, x, b.and_r(S.LandlockScope.member(ts, id), sc.allm(D.LandlockDomain.ids.go(t), ts), h)))

def sc.weaken(+ys: List<&2, U32>, +ts: List<&2, U32>, +z: U32, +h: {sc.allm(ys, ts) == True{} : Bool}) -> {sc.allm(ys, Con{z, ts}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +yt}:
      b.and_intro(S.LandlockScope.member(Con{z, ts}, y), sc.allm(yt, Con{z, ts}), b.or_true_r(U32.is_eq(z, y), S.LandlockScope.member(ts, y), b.and_l(S.LandlockScope.member(ts, y), sc.allm(yt, ts), h)), sc.weaken(yt, ts, z, b.and_r(S.LandlockScope.member(ts, y), sc.allm(yt, ts), h)))

def sc.self(+xs: List<&2, U32>) -> {sc.allm(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      b.and_intro(S.LandlockScope.member(Con{x, xt}, x), sc.allm(xt, Con{x, xt}), b.or_true_l(U32.is_eq(x, x), S.LandlockScope.member(xt, x), u.u32(x)), sc.weaken(xt, xt, x, sc.self(xt)))

def Laws.scope_same_domain(d, x):
  match d:
    case D.LandlockDomain{+ls}:
      sc.all(ls, D.LandlockDomain.ids.go(ls), x, sc.self(D.LandlockDomain.ids.go(ls)))

def Laws.scope_nested_allowed(d, id, rs, x):
  match d:
    case D.LandlockDomain{+ls}:
      sc.all(ls, Con{id, D.LandlockDomain.ids.go(ls)}, x, sc.weaken(D.LandlockDomain.ids.go(ls), D.LandlockDomain.ids.go(ls), id, sc.self(D.LandlockDomain.ids.go(ls))))

def so.go(+a: Bool, +rest: Bool, +h: {a == True{} : Bool}) -> {Bool.and(R.LandlockBits.imp(a, False{}), rest) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.and(True{}, rest) == False{} : Bool}, b.ft(h))

def Laws.scope_refuses_outside(d, id, rs, x, h):
  match d:
    case D.LandlockDomain{+ls}:
      so.go(S.LandlockScope.has(RS.LandlockRuleset.scoped(rs), x), D.LandlockDomain.allows_scope.go(ls, Nil{}, x), h)

def Laws.witness_scope_refuses():
  {==}

# Vectors

def Laws.mask_abi1():
  {==}

def Laws.mask_abi2():
  {==}

def Laws.mask_abi3():
  {==}

def Laws.mask_abi5():
  {==}

def Laws.mask_abi4_net():
  {==}

def Laws.mask_abi6_scope():
  {==}

def Laws.mask_abi0():
  {==}

def Laws.mask_round_trip():
  {==}

def Laws.mask_unknown_bit():
  {==}

def Laws.example_read_usr():
  {==}

def Laws.example_write_usr():
  {==}

def Laws.example_read_etc():
  {==}

def Laws.example_mkdir_usr():
  {==}

def Laws.example_v1_reparent():
  {==}

def Laws.example_v1_same_dir():
  {==}

def Laws.example_gain():
  {==}

def Laws.example_gain_dir():
  {==}

def Laws.example_lose():
  {==}

def Laws.example_link_gain():
  {==}
