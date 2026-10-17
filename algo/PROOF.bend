import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./algo.bend as A
import ./bitmap.bend as M
import ./bsearch.bend as S
import ./LAWS.bend as Laws

# Contradictions

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : absurd.bool(_)
  Unit{}

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

def absurd.nat(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def absurd.sz(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %e : absurd.nat(_)
  Unit{}

def absurd.maybe(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{k}:
      Unit

def absurd.sn(-k: Nat, e: {Some{k} == None{} : Maybe<&2, Nat>}) -> Empty:
  %e : absurd.maybe(_)
  Unit{}

def absurd.ns(-k: Nat, e: {None{} == Some{k} : Maybe<&2, Nat>}) -> Empty:
  %Equal.sym(Maybe<&2, Nat>, None{}, Some{k}, e) : absurd.maybe(_)
  Unit{}

def maybe.get(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{k}:
      k

def some_inj(-a: Nat, -b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => maybe.get(m), Some{a}, Some{b}, e)

# Nat

def nat.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.lt_irrefl(x: Nat) -> {Nat.is_lt(x, x) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nat.lt_irrefl(p)

def nat.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nat.le_refl(p)

def nat.le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, absurd.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

def nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nat.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def nat.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), nat.add_succ(p, b)) : {1n+_ == 2n+Nat.add(p, b) : Nat}
      {==}

# n - k + k = n, for k <= n
def nat.sub_add(n: Nat, k: Nat, e: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.add(Nat.sub(n, k), k) == n : Nat}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      Empty.absurd({Nat.add(0n, 1n+kp) == 0n : Nat}, absurd.ft(e))
    case 1n+np 0n:
      nat.add_zero(1n+np)
    case 1n+ +np 1n+ +kp:
      %Equal.sym(Nat, Nat.add(Nat.sub(np, kp), 1n+kp), 1n+Nat.add(Nat.sub(np, kp), kp), nat.add_succ(Nat.sub(np, kp), kp)) : {_ == 1n+np : Nat}
      %nat.sub_add(np, kp, e) : {1n+Nat.add(Nat.sub(np, kp), kp) == 1n+_ : Nat}
      {==}

def nat.sub_le(n: Nat, k: Nat) -> {Nat.is_le(Nat.sub(n, k), n) == True{} : Bool}:
  match n k:
    case 0n _:
      {==}
    case 1n+np 0n:
      nat.le_refl(np)
    case 1n+ +np 1n+ +kp:
      nat.le_succ(Nat.sub(np, kp), np, nat.sub_le(np, kp))

# k <= l <= n gives k + (n - l) <= n
def nat.add_sub_le(k: Nat, l: Nat, n: Nat, e: {Nat.is_le(k, l) == True{} : Bool}, f: {Nat.is_le(l, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, Nat.sub(n, l)), n) == True{} : Bool}:
  match k l n:
    case 0n _ _:
      nat.sub_le(n, l)
    case 1n+kp 0n _:
      Empty.absurd({Nat.is_le(Nat.add(1n+kp, Nat.sub(n, 0n)), n) == True{} : Bool}, absurd.ft(e))
    case 1n+kp 1n+lp 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+kp, 0n), 0n) == True{} : Bool}, absurd.ft(f))
    case 1n+kp 1n+lp 1n+np:
      nat.add_sub_le(kp, lp, np, e, f)

# Words: popcount

def bitw.popcount_le(n: Nat, w: Word(n)) -> {Nat.is_le(A.bitw.popcount(n, w), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{True{}, t}:
          bitw.popcount_le(p, t)
        case WCon{False{}, +t}:
          nat.le_succ(A.bitw.popcount(p, t), p, bitw.popcount_le(p, t))

def bitw.popcount_not(n: Nat, w: Word(n)) -> {Nat.add(A.bitw.popcount(n, w), A.bitw.popcount(n, Word.not(n, w))) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{True{}, +t}:
          %bitw.popcount_not(p, t) : {1n+Nat.add(A.bitw.popcount(p, t), A.bitw.popcount(p, Word.not(p, t))) == 1n+_ : Nat}
          {==}
        case WCon{False{}, +t}:
          %Equal.sym(Nat, Nat.add(A.bitw.popcount(p, t), 1n+A.bitw.popcount(p, Word.not(p, t))), 1n+Nat.add(A.bitw.popcount(p, t), A.bitw.popcount(p, Word.not(p, t))), nat.add_succ(A.bitw.popcount(p, t), A.bitw.popcount(p, Word.not(p, t)))) : {_ == 1n+p : Nat}
          %bitw.popcount_not(p, t) : {1n+Nat.add(A.bitw.popcount(p, t), A.bitw.popcount(p, Word.not(p, t))) == 1n+_ : Nat}
          {==}

# Words: the bit a 1-based position names, and the positions below and above

def bitw.at1(n: Nat, w: Word(n), m: Nat) -> Bool:
  match m:
    case 0n:
      False{}
    case 1n+k:
      A.bitw.test(n, w, k)

def nat.pos(m: Nat) -> Bool:
  match m:
    case 0n:
      False{}
    case 1n+k:
      True{}

# j lies below the lowest set bit (every j does when there is none)
def bitw.below(j: Nat, m: Nat) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+k:
      Nat.is_lt(j, k)

# j lies above the highest set bit (every j does when there is none)
def bitw.above(j: Nat, m: Nat) -> Bool:
  match m:
    case 0n:
      True{}
    case 1n+k:
      Nat.is_lt(k, j)

# Words: ffs

def bitw.ffs_set.h(p: Nat, -t: Word(p), m: Nat, ih: {bitw.at1(p, t, m) == nat.pos(m) : Bool}) -> {bitw.at1(1n+p, WCon{False{}, t}, A.bitw.ffs.step(False{}, m)) == nat.pos(A.bitw.ffs.step(False{}, m)) : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      ih

def bitw.ffs_set(n: Nat, w: Word(n)) -> {bitw.at1(n, w, A.bitw.ffs(n, w)) == nat.pos(A.bitw.ffs(n, w)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, +t}:
          bitw.ffs_set.h(p, t, A.bitw.ffs(p, t), bitw.ffs_set(p, t))

def bitw.ffs_low.z(m: Nat) -> {Bool.and(bitw.below(0n, A.bitw.ffs.step(False{}, m)), False{}) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def bitw.ffs_low.s(-p: Nat, -t: Word(p), m: Nat, -j: Nat, ih: {Bool.and(bitw.below(j, m), A.bitw.test(p, t, j)) == False{} : Bool}) -> {Bool.and(bitw.below(1n+j, A.bitw.ffs.step(False{}, m)), A.bitw.test(1n+p, WCon{False{}, t}, 1n+j)) == False{} : Bool}:
  match m:
    case 0n:
      ih
    case 1n+k:
      ih

def bitw.ffs_low(n: Nat, w: Word(n), j: Nat) -> {Bool.and(bitw.below(j, A.bitw.ffs(n, w)), A.bitw.test(n, w, j)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w j:
        case WCon{True{}, t} 0n:
          {==}
        case WCon{True{}, t} 1n+q:
          {==}
        case WCon{False{}, t} 0n:
          bitw.ffs_low.z(A.bitw.ffs(p, t))
        case WCon{False{}, +t} 1n+ +q:
          bitw.ffs_low.s(p, t, A.bitw.ffs(p, t), q, bitw.ffs_low(p, t, q))

def bitw.ffs_zero.h(m: Nat, e: {A.bitw.ffs.step(False{}, m) == 0n : Nat}) -> {m == 0n : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      Empty.absurd({1n+k == 0n : Nat}, absurd.sz(1n+k, e))

def bitw.ffs_zero(n: Nat, w: Word(n), e: {A.bitw.ffs(n, w) == 0n : Nat}) -> {w == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +p:
      match w:
        case WCon{True{}, t}:
          Empty.absurd({WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)}, absurd.sz(0n, e))
        case WCon{False{}, +t}:
          %bitw.ffs_zero(p, t, bitw.ffs_zero.h(A.bitw.ffs(p, t), e)) : {WCon{False{}, t} == WCon{False{}, _} : Word(1n+p)}
          {==}

# Words: fls

def bitw.fls_set.h(p: Nat, -t: Word(p), m: Nat, b: Bool, ih: {bitw.at1(p, t, m) == nat.pos(m) : Bool}) -> {bitw.at1(1n+p, WCon{b, t}, A.bitw.fls.step(m, b)) == nat.pos(A.bitw.fls.step(m, b)) : Bool}:
  match m:
    case 0n:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+k:
      ih

def bitw.fls_set(n: Nat, w: Word(n)) -> {bitw.at1(n, w, A.bitw.fls(n, w)) == nat.pos(A.bitw.fls(n, w)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{b, +t}:
          bitw.fls_set.h(p, t, A.bitw.fls(p, t), b, bitw.fls_set(p, t))

def bitw.fls_high.z(m: Nat, b: Bool) -> {Bool.and(bitw.above(0n, A.bitw.fls.step(m, b)), b) == False{} : Bool}:
  match m:
    case 0n:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+k:
      {==}

def bitw.fls_high.s(-p: Nat, -t: Word(p), m: Nat, b: Bool, -j: Nat, ih: {Bool.and(bitw.above(j, m), A.bitw.test(p, t, j)) == False{} : Bool}) -> {Bool.and(bitw.above(1n+j, A.bitw.fls.step(m, b)), A.bitw.test(1n+p, WCon{b, t}, 1n+j)) == False{} : Bool}:
  match m:
    case 0n:
      match b:
        case True{}:
          ih
        case False{}:
          ih
    case 1n+k:
      ih

def bitw.fls_high(n: Nat, w: Word(n), j: Nat) -> {Bool.and(bitw.above(j, A.bitw.fls(n, w)), A.bitw.test(n, w, j)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w j:
        case WCon{+b, t} 0n:
          bitw.fls_high.z(A.bitw.fls(p, t), b)
        case WCon{+b, +t} 1n+ +q:
          bitw.fls_high.s(p, t, A.bitw.fls(p, t), b, q, bitw.fls_high(p, t, q))

def bitw.fls_zero.m(m: Nat, b: Bool, e: {A.bitw.fls.step(m, b) == 0n : Nat}) -> {m == 0n : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      Empty.absurd({1n+k == 0n : Nat}, absurd.sz(1n+k, e))

def bitw.fls_zero.b(m: Nat, b: Bool, e: {A.bitw.fls.step(m, b) == 0n : Nat}) -> {b == False{} : Bool}:
  match m:
    case 0n:
      match b:
        case True{}:
          Empty.absurd({True{} == False{} : Bool}, absurd.sz(0n, e))
        case False{}:
          {==}
    case 1n+k:
      Empty.absurd({b == False{} : Bool}, absurd.sz(1n+k, e))

def bitw.fls_zero(n: Nat, w: Word(n), e: {A.bitw.fls(n, w) == 0n : Nat}) -> {w == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +p:
      match w:
        case WCon{+b, +t}:
          +e2 = e
          %bitw.fls_zero(p, t, bitw.fls_zero.m(A.bitw.fls(p, t), b, e2)) : {WCon{b, t} == WCon{False{}, _} : Word(1n+p)}
          %bitw.fls_zero.b(A.bitw.fls(p, t), b, e2) : {WCon{b, t} == WCon{_, t} : Word(1n+p)}
          {==}

def bitw.fls_le.h(m: Nat, b: Bool, +p: Nat, ih: {Nat.is_le(m, p) == True{} : Bool}) -> {Nat.is_le(A.bitw.fls.step(m, b), 1n+p) == True{} : Bool}:
  match m:
    case 0n:
      match b:
        case True{}:
          nat.le_zero(p)
        case False{}:
          {==}
    case 1n+k:
      ih

def bitw.fls_le(n: Nat, w: Word(n)) -> {Nat.is_le(A.bitw.fls(n, w), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{b, +t}:
          bitw.fls_le.h(A.bitw.fls(p, t), b, p, bitw.fls_le(p, t))

# ffs <= fls
def bitw.ffs_le_fls.f(a: Nat, m: Nat, ih: {Nat.is_le(a, m) == True{} : Bool}) -> {Nat.is_le(A.bitw.ffs.step(False{}, a), A.bitw.fls.step(m, False{})) == True{} : Bool}:
  match a m:
    case 0n _:
      nat.le_zero(A.bitw.fls.step(m, False{}))
    case 1n+i 0n:
      Empty.absurd({Nat.is_le(2n+i, 0n) == True{} : Bool}, absurd.ft(ih))
    case 1n+i 1n+k:
      ih

def bitw.ffs_le_fls.t(m: Nat) -> {Nat.is_le(1n, A.bitw.fls.step(m, True{})) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def bitw.ffs_le_fls(n: Nat, w: Word(n)) -> {Nat.is_le(A.bitw.ffs(n, w), A.bitw.fls(n, w)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{True{}, t}:
          bitw.ffs_le_fls.t(A.bitw.fls(p, t))
        case WCon{False{}, +t}:
          bitw.ffs_le_fls.f(A.bitw.ffs(p, t), A.bitw.fls(p, t), bitw.ffs_le_fls(p, t))

# Words: ctz

def bitw.ctz_spec(+n: Nat, m: Nat) -> Nat:
  match m:
    case 0n:
      n
    case 1n+k:
      k

def bitw.ctz_ffs.h(+p: Nat, c: Nat, m: Nat, ih: {c == bitw.ctz_spec(p, m) : Nat}) -> {1n+c == bitw.ctz_spec(1n+p, A.bitw.ffs.step(False{}, m)) : Nat}:
  match m:
    case 0n:
      %ih : {1n+c == 1n+_ : Nat}
      {==}
    case 1n+k:
      %ih : {1n+c == 1n+_ : Nat}
      {==}

def bitw.ctz_ffs(n: Nat, w: Word(n)) -> {A.bitw.ctz(n, w) == bitw.ctz_spec(n, A.bitw.ffs(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, +t}:
          bitw.ctz_ffs.h(p, A.bitw.ctz(p, t), A.bitw.ffs(p, t), bitw.ctz_ffs(p, t))

# Words: from a 0-based index back to the 1-based position

def bitw.index_some(m: Nat, -k: Nat, e: {A.bitw.index(m) == Some{k} : Maybe<&2, Nat>}) -> {m == 1n+k : Nat}:
  match m:
    case 0n:
      Empty.absurd({0n == 1n+k : Nat}, absurd.ns(k, e))
    case 1n+i:
      %some_inj(i, k, e) : {1n+i == 1n+_ : Nat}
      {==}

def bitw.index_none(m: Nat, e: {A.bitw.index(m) == None{} : Maybe<&2, Nat>}) -> {m == 0n : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+i:
      Empty.absurd({1n+i == 0n : Nat}, absurd.sn(i, e))

# Words: the laws, at any width

def bitw.first_set_is_set(+n: Nat, +w: Word(n), +k: Nat, e: {A.bitw.index(A.bitw.ffs(n, w)) == Some{k} : Maybe<&2, Nat>}) -> {A.bitw.test(n, w, k) == True{} : Bool}:
  %bitw.index_some(A.bitw.ffs(n, w), k, e) : {bitw.at1(n, w, _) == nat.pos(_) : Bool}
  bitw.ffs_set(n, w)

def bitw.first_set_lowest(+n: Nat, +w: Word(n), +k: Nat, +j: Nat, e: {A.bitw.index(A.bitw.ffs(n, w)) == Some{k} : Maybe<&2, Nat>}, l: {Nat.is_lt(j, k) == True{} : Bool}) -> {A.bitw.test(n, w, j) == False{} : Bool}:
  %l : {Bool.and(_, A.bitw.test(n, w, j)) == False{} : Bool}
  %bitw.index_some(A.bitw.ffs(n, w), k, e) : {Bool.and(bitw.below(j, _), A.bitw.test(n, w, j)) == False{} : Bool}
  bitw.ffs_low(n, w, j)

def bitw.first_set_none(+n: Nat, +w: Word(n), e: {A.bitw.index(A.bitw.ffs(n, w)) == None{} : Maybe<&2, Nat>}) -> {w == Word.zero(n) : Word(n)}:
  bitw.ffs_zero(n, w, bitw.index_none(A.bitw.ffs(n, w), e))

def bitw.last_set_is_set(+n: Nat, +w: Word(n), +k: Nat, e: {A.bitw.index(A.bitw.fls(n, w)) == Some{k} : Maybe<&2, Nat>}) -> {A.bitw.test(n, w, k) == True{} : Bool}:
  %bitw.index_some(A.bitw.fls(n, w), k, e) : {bitw.at1(n, w, _) == nat.pos(_) : Bool}
  bitw.fls_set(n, w)

def bitw.last_set_highest(+n: Nat, +w: Word(n), +k: Nat, +j: Nat, e: {A.bitw.index(A.bitw.fls(n, w)) == Some{k} : Maybe<&2, Nat>}, l: {Nat.is_lt(k, j) == True{} : Bool}) -> {A.bitw.test(n, w, j) == False{} : Bool}:
  %l : {Bool.and(_, A.bitw.test(n, w, j)) == False{} : Bool}
  %bitw.index_some(A.bitw.fls(n, w), k, e) : {Bool.and(bitw.above(j, _), A.bitw.test(n, w, j)) == False{} : Bool}
  bitw.fls_high(n, w, j)

def bitw.last_set_none(+n: Nat, +w: Word(n), e: {A.bitw.index(A.bitw.fls(n, w)) == None{} : Maybe<&2, Nat>}) -> {w == Word.zero(n) : Word(n)}:
  bitw.fls_zero(n, w, bitw.index_none(A.bitw.fls(n, w), e))

def bitw.ctz_first_set(+n: Nat, +w: Word(n), +k: Nat, e: {A.bitw.index(A.bitw.ffs(n, w)) == Some{k} : Maybe<&2, Nat>}) -> {A.bitw.ctz(n, w) == k : Nat}:
  %bitw.index_some(A.bitw.ffs(n, w), k, e) : {A.bitw.ctz(n, w) == bitw.ctz_spec(n, _) : Nat}
  bitw.ctz_ffs(n, w)

# with the highest set bit at k, k <= m in a word of width 1 + m
def bitw.last_le(+m: Nat, +w: Word(1n+m), +k: Nat, e: {A.bitw.index(A.bitw.fls(1n+m, w)) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_le(k, m) == True{} : Bool}:
  %bitw.index_some(A.bitw.fls(1n+m, w), k, e) : {Nat.is_le(_, 1n+m) == True{} : Bool}
  bitw.fls_le(1n+m, w)

def bitw.clz_last_set(+m: Nat, +w: Word(1n+m), +k: Nat, +e: {A.bitw.index(A.bitw.fls(1n+m, w)) == Some{k} : Maybe<&2, Nat>}) -> {Nat.add(A.bitw.clz(1n+m, w), k) == m : Nat}:
  %Equal.sym(Nat, A.bitw.fls(1n+m, w), 1n+k, bitw.index_some(A.bitw.fls(1n+m, w), k, e)) : {Nat.add(Nat.sub(1n+m, _), k) == m : Nat}
  nat.sub_add(m, k, bitw.last_le(m, w, k, e))

def bitw.first_le_last(+n: Nat, +w: Word(n), +i: Nat, +k: Nat, e: {A.bitw.index(A.bitw.ffs(n, w)) == Some{i} : Maybe<&2, Nat>}, f: {A.bitw.index(A.bitw.fls(n, w)) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_le(i, k) == True{} : Bool}:
  %bitw.index_some(A.bitw.ffs(n, w), i, e) : {Nat.is_le(_, 1n+k) == True{} : Bool}
  %bitw.index_some(A.bitw.fls(n, w), k, f) : {Nat.is_le(A.bitw.ffs(n, w), _) == True{} : Bool}
  bitw.ffs_le_fls(n, w)

def bitw.ctz_clz.h(+k: Nat, +m: Nat, l: Nat, e: {Nat.is_le(1n+k, l) == True{} : Bool}, f: {Nat.is_le(l, 1n+m) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, Nat.sub(1n+m, l)), m) == True{} : Bool}:
  match l:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(k, 1n+m), m) == True{} : Bool}, absurd.ft(e))
    case 1n+i:
      nat.add_sub_le(k, i, m, e, f)

def bitw.ffs_fls_k(+n: Nat, +w: Word(n), +k: Nat, e: {A.bitw.index(A.bitw.ffs(n, w)) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_le(1n+k, A.bitw.fls(n, w)) == True{} : Bool}:
  %bitw.index_some(A.bitw.ffs(n, w), k, e) : {Nat.is_le(_, A.bitw.fls(n, w)) == True{} : Bool}
  bitw.ffs_le_fls(n, w)

def bitw.ctz_clz(+m: Nat, +w: Word(1n+m), +k: Nat, +e: {A.bitw.index(A.bitw.ffs(1n+m, w)) == Some{k} : Maybe<&2, Nat>}) -> {Nat.is_le(Nat.add(A.bitw.ctz(1n+m, w), A.bitw.clz(1n+m, w)), m) == True{} : Bool}:
  %Equal.sym(Nat, A.bitw.ctz(1n+m, w), k, bitw.ctz_first_set(1n+m, w, k, e)) : {Nat.is_le(Nat.add(_, A.bitw.clz(1n+m, w)), m) == True{} : Bool}
  bitw.ctz_clz.h(k, m, A.bitw.fls(1n+m, w), bitw.ffs_fls_k(1n+m, w, k, e), bitw.fls_le(1n+m, w))

# U32: a word whose bits are all clear is 0

def u32.zero(+x: U32, e: {A.bits32.word(x) == Word.zero(32n) : Word(32n)}) -> {x == 0 : U32}:
  match x:
    case U32{w}:
      %e : {U32{w} == U32{_} : U32}
      {==}

# W64: the halves of a joined word (word64's bits.lo, bits.hi and bits.cat)

def w64.lo_cat(m: Nat, +n: Nat, l: Word(m), +h: Word(n)) -> {W.W64.bits.lo(m, n, W.W64.bits.cat(m, n, l, h)) == l : Word(m)}:
  match m:
    case 0n:
      match l:
        case WNil{}:
          {==}
    case 1n+ +p:
      match l:
        case WCon{+b, +t}:
          %w64.lo_cat(p, n, t, h) : {WCon{b, W.W64.bits.lo(p, n, W.W64.bits.cat(p, n, t, h))} == WCon{b, _} : Word(1n+p)}
          {==}

def w64.hi_cat(m: Nat, +n: Nat, l: Word(m), +h: Word(n)) -> {W.W64.bits.hi(m, n, W.W64.bits.cat(m, n, l, h)) == h : Word(n)}:
  match m:
    case 0n:
      match l:
        case WNil{}:
          {==}
    case 1n+ +p:
      match l:
        case WCon{b, +t}:
          w64.hi_cat(p, n, t, h)

def w64.zero(+a: W.W64, +e: {A.bits64.word(a) == Word.zero(64n) : Word(64n)}) -> {a == W.W64.zero() : W.W64}:
  +l = A.bits32.word(W.W64.lo(a))
  +h = A.bits32.word(W.W64.hi(a))
  +c = W.W64.bits.cat(32n, 32n, l, h)
  +el = Equal.trans(Word(32n), l, W.W64.bits.lo(32n, 32n, c), Word.zero(32n), Equal.sym(Word(32n), W.W64.bits.lo(32n, 32n, c), l, w64.lo_cat(32n, 32n, l, h)), Equal.cong(Word(64n), Word(32n), v => W.W64.bits.lo(32n, 32n, v), c, Word.zero(64n), e))
  +eh = Equal.trans(Word(32n), h, W.W64.bits.hi(32n, 32n, c), Word.zero(32n), Equal.sym(Word(32n), W.W64.bits.hi(32n, 32n, c), h, w64.hi_cat(32n, 32n, l, h)), Equal.cong(Word(64n), Word(32n), v => W.W64.bits.hi(32n, 32n, v), c, Word.zero(64n), e))
  %WL.parts_of(a) : {_ == W.W64.zero() : W.W64}
  %Equal.sym(U32, W.W64.hi(a), 0, u32.zero(W.W64.hi(a), eh)) : {W.W64.from_parts(_, W.W64.lo(a)) == W.W64.zero() : W.W64}
  %Equal.sym(U32, W.W64.lo(a), 0, u32.zero(W.W64.lo(a), el)) : {W.W64.from_parts(0, _) == W.W64.zero() : W.W64}
  {==}

# Bit sequences: next

def bitseq.next_le(size: Nat, start: Nat, want: Bool, bs: List<&2, Bool>) -> {Nat.is_le(M.bitseq.next(size, start, want, bs), size) == True{} : Bool}:
  match size:
    case 0n:
      {==}
    case 1n+ +s:
      match start want bs:
        case 1n+st w Nil{}:
          bitseq.next_le(s, st, w, Nil{})
        case 1n+st w Con{h, t}:
          bitseq.next_le(s, st, w, t)
        case 0n False{} Nil{}:
          {==}
        case 0n True{} Nil{}:
          nat.le_refl(s)
        case 0n True{} Con{True{}, t}:
          {==}
        case 0n False{} Con{False{}, t}:
          {==}
        case 0n True{} Con{False{}, t}:
          bitseq.next_le(s, 0n, True{}, t)
        case 0n False{} Con{True{}, t}:
          bitseq.next_le(s, 0n, False{}, t)

def bitseq.next_hit(size: Nat, start: Nat, want: Bool, bs: List<&2, Bool>, l: {Nat.is_lt(M.bitseq.next(size, start, want, bs), size) == True{} : Bool}) -> {M.bitseq.at(bs, M.bitseq.next(size, start, want, bs)) == want : Bool}:
  match size:
    case 0n:
      Empty.absurd({M.bitseq.at(bs, 0n) == want : Bool}, absurd.ft(l))
    case 1n+ +s:
      match start want bs:
        case 1n+st w Nil{}:
          bitseq.next_hit(s, st, w, Nil{}, l)
        case 1n+st w Con{h, t}:
          bitseq.next_hit(s, st, w, t, l)
        case 0n False{} Nil{}:
          {==}
        case 0n True{} Nil{}:
          Empty.absurd({False{} == True{} : Bool}, absurd.ft(Equal.trans(Bool, False{}, Nat.is_lt(s, s), True{}, Equal.sym(Bool, Nat.is_lt(s, s), False{}, nat.lt_irrefl(s)), l)))
        case 0n True{} Con{True{}, t}:
          {==}
        case 0n False{} Con{False{}, t}:
          {==}
        case 0n True{} Con{False{}, t}:
          bitseq.next_hit(s, 0n, True{}, t, l)
        case 0n False{} Con{True{}, t}:
          bitseq.next_hit(s, 0n, False{}, t, l)

def bitseq.next_ge(size: Nat, start: Nat, want: Bool, bs: List<&2, Bool>, l: {Nat.is_lt(M.bitseq.next(size, start, want, bs), size) == True{} : Bool}) -> {Nat.is_le(start, M.bitseq.next(size, start, want, bs)) == True{} : Bool}:
  match size:
    case 0n:
      Empty.absurd({Nat.is_le(start, 0n) == True{} : Bool}, absurd.ft(l))
    case 1n+ +s:
      match start want bs:
        case 1n+st w Nil{}:
          bitseq.next_ge(s, st, w, Nil{}, l)
        case 1n+st w Con{h, t}:
          bitseq.next_ge(s, st, w, t, l)
        case 0n False{} Nil{}:
          {==}
        case 0n True{} Nil{}:
          {==}
        case 0n True{} Con{True{}, t}:
          {==}
        case 0n False{} Con{False{}, t}:
          {==}
        case 0n True{} Con{False{}, t}:
          {==}
        case 0n False{} Con{True{}, t}:
          {==}

def bitseq.lt0(+j: Nat, -T: Type, l: {Nat.is_lt(j, 0n) == True{} : Bool}) -> T:
  Empty.absurd(T, absurd.ft(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, nat.lt_zero(j)), l)))

def bitseq.next_miss(size: Nat, start: Nat, want: Bool, bs: List<&2, Bool>, j: Nat, l: {Nat.is_le(start, j) == True{} : Bool}, m: {Nat.is_lt(j, M.bitseq.next(size, start, want, bs)) == True{} : Bool}) -> {M.bitseq.at(bs, j) == Bool.not(want) : Bool}:
  match size:
    case 0n:
      bitseq.lt0(j, {M.bitseq.at(bs, j) == Bool.not(want) : Bool}, m)
    case 1n+ +s:
      match start want bs j:
        case 1n+st w Nil{} 0n:
          Empty.absurd({False{} == Bool.not(w) : Bool}, absurd.ft(l))
        case 1n+st w Nil{} 1n+jp:
          bitseq.next_miss(s, st, w, Nil{}, jp, l, m)
        case 1n+st w Con{h, t} 0n:
          Empty.absurd({h == Bool.not(w) : Bool}, absurd.ft(l))
        case 1n+st w Con{h, t} 1n+jp:
          bitseq.next_miss(s, st, w, t, jp, l, m)
        case 0n False{} Nil{} +jj:
          bitseq.lt0(jj, {M.bitseq.at(Nil{}, jj) == True{} : Bool}, m)
        case 0n True{} Nil{} jj:
          {==}
        case 0n True{} Con{True{}, t} +jj:
          bitseq.lt0(jj, {M.bitseq.at(Con{True{}, t}, jj) == False{} : Bool}, m)
        case 0n False{} Con{False{}, t} +jj:
          bitseq.lt0(jj, {M.bitseq.at(Con{False{}, t}, jj) == True{} : Bool}, m)
        case 0n True{} Con{False{}, t} 0n:
          {==}
        case 0n True{} Con{False{}, t} 1n+ +jp:
          bitseq.next_miss(s, 0n, True{}, t, jp, nat.le_zero(jp), m)
        case 0n False{} Con{True{}, t} 0n:
          {==}
        case 0n False{} Con{True{}, t} 1n+ +jp:
          bitseq.next_miss(s, 0n, False{}, t, jp, nat.le_zero(jp), m)

# The laws: U32

def Laws.popcount_le(x):
  bitw.popcount_le(32n, A.bits32.word(x))

def Laws.popcount_not(x):
  match x:
    case U32{w}:
      bitw.popcount_not(32n, w)

def Laws.first_set_is_set(x, k, e):
  bitw.first_set_is_set(32n, A.bits32.word(x), k, e)

def Laws.first_set_lowest(x, k, j, e, l):
  bitw.first_set_lowest(32n, A.bits32.word(x), k, j, e, l)

def Laws.first_set_none(x, e):
  match x:
    case U32{+w}:
      %bitw.first_set_none(32n, w, e) : {U32{w} == U32{_} : U32}
      {==}

def Laws.last_set_is_set(x, k, e):
  bitw.last_set_is_set(32n, A.bits32.word(x), k, e)

def Laws.last_set_highest(x, k, j, e, l):
  bitw.last_set_highest(32n, A.bits32.word(x), k, j, e, l)

def Laws.last_set_none(x, e):
  match x:
    case U32{+w}:
      %bitw.last_set_none(32n, w, e) : {U32{w} == U32{_} : U32}
      {==}

def Laws.ctz_first_set(x, k, e):
  bitw.ctz_first_set(32n, A.bits32.word(x), k, e)

def Laws.clz_last_set(x, k, e):
  bitw.clz_last_set(31n, A.bits32.word(x), k, e)

def Laws.first_le_last(x, i, k, e, f):
  bitw.first_le_last(32n, A.bits32.word(x), i, k, e, f)

def Laws.ctz_clz(x, k, e):
  bitw.ctz_clz(31n, A.bits32.word(x), k, e)

# The laws: W64

def Laws.popcount64_le(a):
  bitw.popcount_le(64n, A.bits64.word(a))

def Laws.first_set64_is_set(a, k, e):
  bitw.first_set_is_set(64n, A.bits64.word(a), k, e)

def Laws.first_set64_lowest(a, k, j, e, l):
  bitw.first_set_lowest(64n, A.bits64.word(a), k, j, e, l)

def w64.first_set_none(+a: W.W64, e: {A.bits64.first_set(a) == None{} : Maybe<&2, Nat>}) -> {a == W.W64.zero() : W.W64}:
  w64.zero(a, bitw.first_set_none(64n, A.bits64.word(a), e))

def Laws.first_set64_none(a, e):
  w64.first_set_none(a, e)

def Laws.last_set64_is_set(a, k, e):
  bitw.last_set_is_set(64n, A.bits64.word(a), k, e)

def Laws.last_set64_highest(a, k, j, e, l):
  bitw.last_set_highest(64n, A.bits64.word(a), k, j, e, l)

def Laws.ctz64_first_set(a, k, e):
  bitw.ctz_first_set(64n, A.bits64.word(a), k, e)

def Laws.clz64_last_set(a, k, e):
  bitw.clz_last_set(63n, A.bits64.word(a), k, e)

def Laws.ctz_clz64(a, k, e):
  bitw.ctz_clz(63n, A.bits64.word(a), k, e)

# The laws: bitmaps

def Laws.next_set_le_size(words, size, start):
  bitseq.next_le(size, start, True{}, M.bitmap.bits(words))

def Laws.next_set_is_set(words, size, start, l):
  bitseq.next_hit(size, start, True{}, M.bitmap.bits(words), l)

def Laws.next_set_at_least(words, size, start, l):
  bitseq.next_ge(size, start, True{}, M.bitmap.bits(words), l)

def Laws.next_set_none_before(words, size, start, j, l, m):
  bitseq.next_miss(size, start, True{}, M.bitmap.bits(words), j, l, m)

def Laws.next_clear_le_size(words, size, start):
  bitseq.next_le(size, start, False{}, M.bitmap.bits(words))

def Laws.next_clear_is_clear(words, size, start, l):
  bitseq.next_hit(size, start, False{}, M.bitmap.bits(words), l)

def Laws.next_clear_at_least(words, size, start, l):
  bitseq.next_ge(size, start, False{}, M.bitmap.bits(words), l)

def Laws.next_clear_none_before(words, size, start, j, l, m):
  bitseq.next_miss(size, start, False{}, M.bitmap.bits(words), j, l, m)

# Vectors

def Laws.vec_popcount():
  {==}

def Laws.vec_zero():
  {==}

def Laws.vec_forty():
  {==}

def Laws.vec_top():
  {==}

def Laws.vec64_halves():
  {==}

def Laws.vec64_zero():
  {==}

def Laws.vec_next_set():
  {==}

def Laws.vec_next_set_none():
  {==}

def Laws.vec_next_clear():
  {==}

def Laws.vec_next_past_size():
  {==}

# Binary search: Maybe<&2, U32>

def absurd.maybe32(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{k}:
      Unit

def absurd.ns32(-k: U32, e: {None{} == Some{k} : Maybe<&2, U32>}) -> Empty:
  %Equal.sym(Maybe<&2, U32>, None{}, Some{k}, e) : absurd.maybe32(_)
  Unit{}

def maybe32.get(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{k}:
      k

def some_inj32(-a: U32, -b: U32, e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => maybe32.get(m), Some{a}, Some{b}, e)

def absurd.sn_nat(-k: Nat, e: {Some{k} == None{} : Maybe<&2, Nat>}) -> Empty:
  absurd.sn(k, e)

# Binary search: Bool

def bool.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))

def bool.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, absurd.ft(e))

# Binary search: the order of U32 is the order of its value as a Nat

def nat.dbit(b: Bool, a: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(a)
    case True{}:
      1n+Nat.double(a)

def word.cmp_nat.d(a: Nat, b: Nat, x: Bool, y: Bool) -> {Word.cmp.fin(x, y, Nat.cmp(a, b)) == Nat.cmp(nat.dbit(x, a), nat.dbit(y, b)) : Cmp}:
  match a b:
    case 0n 0n:
      match x y:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case 0n 1n+bp:
      match x y:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case 1n+ap 0n:
      match x y:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case 1n+ +ap 1n+ +bp:
      match x y:
        case True{} True{}:
          word.cmp_nat.d(ap, bp, True{}, True{})
        case True{} False{}:
          word.cmp_nat.d(ap, bp, True{}, False{})
        case False{} True{}:
          word.cmp_nat.d(ap, bp, False{}, True{})
        case False{} False{}:
          word.cmp_nat.d(ap, bp, False{}, False{})

def word.cmp_nat.h(+p: Nat, +x: Bool, +y: Bool, +at: Word(p), +bt: Word(p), ih: {Word.cmp(p, at, bt) == Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)) : Cmp}) -> {Word.cmp.fin(x, y, Word.cmp(p, at, bt)) == Nat.cmp(nat.dbit(x, Word.to_nat(p, at)), nat.dbit(y, Word.to_nat(p, bt))) : Cmp}:
  %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), ih) : {Word.cmp.fin(x, y, _) == Nat.cmp(nat.dbit(x, Word.to_nat(p, at)), nat.dbit(y, Word.to_nat(p, bt))) : Cmp}
  word.cmp_nat.d(Word.to_nat(p, at), Word.to_nat(p, bt), x, y)

def word.cmp_nat(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{True{}, +at} WCon{True{}, +bt}:
          word.cmp_nat.h(p, True{}, True{}, at, bt, word.cmp_nat(p, at, bt))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          word.cmp_nat.h(p, True{}, False{}, at, bt, word.cmp_nat(p, at, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          word.cmp_nat.h(p, False{}, True{}, at, bt, word.cmp_nat(p, at, bt))
        case WCon{False{}, +at} WCon{False{}, +bt}:
          word.cmp_nat.h(p, False{}, False{}, at, bt, word.cmp_nat(p, at, bt))

def u32.cmp_nat(a: U32, b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}:
  match a b:
    case U32{wa} U32{wb}:
      word.cmp_nat(32n, wa, wb)

# a hypothesis about U32's order, as one about Nat's
def u32.mv_le(+a: U32, +b: U32, -v: Bool, h: {U32.is_le(a, b) == v : Bool}) -> {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == v : Bool}:
  %u32.cmp_nat(a, b) : {Cmp.is_le(_) == v : Bool}
  h

def u32.mv_lt(+a: U32, +b: U32, -v: Bool, h: {U32.is_lt(a, b) == v : Bool}) -> {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == v : Bool}:
  %u32.cmp_nat(a, b) : {Cmp.is_lt(_) == v : Bool}
  h

def u32.mv_eq(+a: U32, +b: U32, -v: Bool, h: {U32.is_eq(a, b) == v : Bool}) -> {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == v : Bool}:
  %u32.cmp_nat(a, b) : {Cmp.is_eq(_) == v : Bool}
  h

# Nat order facts

def nat.le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      nat.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, absurd.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, absurd.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nat.le_trans(ap, bp, cp, e, f)

# not a < c, a <= b: not b < c
def nat.nlt_le(a: Nat, b: Nat, c: Nat, e: {Nat.is_lt(a, c) == False{} : Bool}, f: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, c) == False{} : Bool}:
  match a b c:
    case 0n _ 0n:
      nat.lt_zero(b)
    case 0n _ 1n+cp:
      Empty.absurd({Nat.is_lt(b, 1n+cp) == False{} : Bool}, absurd.tf(e))
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == False{} : Bool}, absurd.ft(f))
    case 1n+ap 1n+bp 0n:
      {==}
    case 1n+ap 1n+bp 1n+cp:
      nat.nlt_le(ap, bp, cp, e, f)

# k < a (not a < k, a != k), a <= b: b != k
def nat.gt_le_ne(a: Nat, b: Nat, k: Nat, e: {Nat.is_lt(a, k) == False{} : Bool}, f: {Nat.is_eq(a, k) == False{} : Bool}, g: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_eq(b, k) == False{} : Bool}:
  match a b k:
    case 0n _ 0n:
      Empty.absurd({Nat.is_eq(b, 0n) == False{} : Bool}, absurd.tf(f))
    case 0n _ 1n+kp:
      Empty.absurd({Nat.is_eq(b, 1n+kp) == False{} : Bool}, absurd.tf(e))
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_eq(0n, k) == False{} : Bool}, absurd.ft(g))
    case 1n+ap 1n+bp 0n:
      {==}
    case 1n+ap 1n+bp 1n+kp:
      nat.gt_le_ne(ap, bp, kp, e, f, g)

# U32 order facts

def u32.le_trans(+a: U32, +b: U32, +c: U32, e: {U32.is_le(a, b) == True{} : Bool}, f: {U32.is_le(b, c) == True{} : Bool}) -> {U32.is_le(a, c) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, c), Nat.cmp(U32.to_nat(a), U32.to_nat(c)), u32.cmp_nat(a, c)) : {Cmp.is_le(_) == True{} : Bool}
  nat.le_trans(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c), u32.mv_le(a, b, True{}, e), u32.mv_le(b, c, True{}, f))

def u32.nlt_le(+a: U32, +b: U32, +c: U32, e: {U32.is_lt(a, c) == False{} : Bool}, f: {U32.is_le(a, b) == True{} : Bool}) -> {U32.is_lt(b, c) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, c), Nat.cmp(U32.to_nat(b), U32.to_nat(c)), u32.cmp_nat(b, c)) : {Cmp.is_lt(_) == False{} : Bool}
  nat.nlt_le(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c), u32.mv_lt(a, c, False{}, e), u32.mv_le(a, b, True{}, f))

def u32.gt_le_ne(+a: U32, +b: U32, +k: U32, e: {U32.is_lt(a, k) == False{} : Bool}, f: {U32.is_eq(a, k) == False{} : Bool}, g: {U32.is_le(a, b) == True{} : Bool}) -> {U32.is_eq(b, k) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, k), Nat.cmp(U32.to_nat(b), U32.to_nat(k)), u32.cmp_nat(b, k)) : {Cmp.is_eq(_) == False{} : Bool}
  nat.gt_le_ne(U32.to_nat(a), U32.to_nat(b), U32.to_nat(k), u32.mv_lt(a, k, False{}, e), u32.mv_eq(a, k, False{}, f), u32.mv_le(a, b, True{}, g))

def cmp.lt_ne(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_eq(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.ft(e))
    case GT{}:
      Empty.absurd({False{} == False{} : Bool}, absurd.ft(e))

def u32.lt_ne(+a: U32, +b: U32, e: {U32.is_lt(a, b) == True{} : Bool}) -> {U32.is_eq(a, b) == False{} : Bool}:
  cmp.lt_ne(U32.cmp(a, b), e)

# is_eq gives equality

def word.eq_tail(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))

def word.eq_head(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {x == y : Bool}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Bool}, absurd.ft(e))
    case EQ{}:
      match x y:
        case True{} True{}:
          {==}
        case False{} False{}:
          {==}
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, absurd.ft(e))
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case GT{}:
      Empty.absurd({x == y : Bool}, absurd.ft(e))

def word.eq(n: Nat, a: Word(n), b: Word(n), e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +e2 = e
          %word.eq(p, at, bt, word.eq_tail(Word.cmp(p, at, bt), x, y, e2)) : {WCon{x, at} == WCon{y, _} : Word(1n+p)}
          %word.eq_head(Word.cmp(p, at, bt), x, y, e2) : {WCon{x, at} == WCon{_, at} : Word(1n+p)}
          {==}

def u32.eq(a: U32, b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+wa} U32{+wb}:
      %word.eq(32n, wa, wb, e) : {U32{wa} == U32{_} : U32}
      {==}

# Binary search: sorted lists

def bs.sorted_tail(t: List<&2, U32>, x0: U32, s: {S.bsearch.sorted.pair(t, x0) == True{} : Bool}) -> {S.bsearch.sorted(t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{y, tt}:
      bool.and_r(U32.is_le(x0, y), S.bsearch.sorted.pair(tt, y), s)

# the head of a sorted list is at most each of its elements
def bs.head_le(t: List<&2, U32>, +x0: U32, s: {S.bsearch.sorted.pair(t, x0) == True{} : Bool}, i: Nat, +x: U32, e: {List.get(&2, U32, t, i) == Some{x} : Maybe<&2, U32>}) -> {U32.is_le(x0, x) == True{} : Bool}:
  match t i:
    case Nil{} _:
      Empty.absurd({U32.is_le(x0, x) == True{} : Bool}, absurd.ns32(x, e))
    case Con{+y, tt} 0n:
      %some_inj32(y, x, e) : {U32.is_le(x0, _) == True{} : Bool}
      bool.and_l(U32.is_le(x0, y), S.bsearch.sorted.pair(tt, y), s)
    case Con{+y, +tt} 1n+ip:
      +s2 = s
      u32.le_trans(x0, y, x, bool.and_l(U32.is_le(x0, y), S.bsearch.sorted.pair(tt, y), s2), bs.head_le(tt, y, bool.and_r(U32.is_le(x0, y), S.bsearch.sorted.pair(tt, y), s2), ip, x, e))

# Binary search: lower_bound

def bs.le_len.h(c: Bool, r: Nat, +n: Nat, ih: {Nat.is_le(r, n) == True{} : Bool}) -> {Nat.is_le(S.bsearch.below.step(c, r), 1n+n) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      {==}

def bs.le_len(xs: List<&2, U32>, +key: U32) -> {Nat.is_le(S.bsearch.lower_bound(xs, key), List.length(&2, U32, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      bs.le_len.h(U32.is_lt(x, key), S.bsearch.lower_bound(t, key), List.length(&2, U32, t), bs.le_len(t, key))

def bs.step0(c: Bool, +r: Nat, l: {Nat.is_lt(0n, S.bsearch.below.step(c, r)) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(l))

def bs.step1(c: Bool, +r: Nat, +i: Nat, l: {Nat.is_lt(1n+i, S.bsearch.below.step(c, r)) == True{} : Bool}) -> {Nat.is_lt(i, r) == True{} : Bool}:
  match c:
    case True{}:
      l
    case False{}:
      Empty.absurd({Nat.is_lt(i, r) == True{} : Bool}, absurd.ft(l))

def bs.below(xs: List<&2, U32>, +key: U32, i: Nat, +x: U32, e: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}, l: {Nat.is_lt(i, S.bsearch.lower_bound(xs, key)) == True{} : Bool}) -> {U32.is_lt(x, key) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({U32.is_lt(x, key) == True{} : Bool}, absurd.ns32(x, e))
    case Con{+x0, t} 0n:
      %some_inj32(x0, x, e) : {U32.is_lt(_, key) == True{} : Bool}
      bs.step0(U32.is_lt(x0, key), S.bsearch.lower_bound(t, key), l)
    case Con{+x0, +t} 1n+ +ip:
      bs.below(t, key, ip, x, e, bs.step1(U32.is_lt(x0, key), S.bsearch.lower_bound(t, key), ip, l))

def bs.above0(c: Bool, +r: Nat, l: {Nat.is_le(S.bsearch.below.step(c, r), 0n) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.ft(l))
    case False{}:
      {==}

def bs.above1(c: Bool, +x0: U32, +x: U32, +key: U32, ec: {U32.is_lt(x0, key) == c : Bool}, +r: Nat, +i: Nat, l: {Nat.is_le(S.bsearch.below.step(c, r), 1n+i) == True{} : Bool}, ih: {Nat.is_le(r, i) == True{} : Bool} -> {U32.is_lt(x, key) == False{} : Bool}, h: {U32.is_le(x0, x) == True{} : Bool}) -> {U32.is_lt(x, key) == False{} : Bool}:
  match c:
    case True{}:
      ih(l)
    case False{}:
      u32.nlt_le(x0, x, key, ec, h)

def bs.above(xs: List<&2, U32>, +key: U32, i: Nat, +x: U32, s: {S.bsearch.sorted(xs) == True{} : Bool}, e: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}, l: {Nat.is_le(S.bsearch.lower_bound(xs, key), i) == True{} : Bool}) -> {U32.is_lt(x, key) == False{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({U32.is_lt(x, key) == False{} : Bool}, absurd.ns32(x, e))
    case Con{+x0, t} 0n:
      %some_inj32(x0, x, e) : {U32.is_lt(_, key) == False{} : Bool}
      bs.above0(U32.is_lt(x0, key), S.bsearch.lower_bound(t, key), l)
    case Con{+x0, +t} 1n+ +ip:
      +s2 = s
      +e2 = e
      bs.above1(U32.is_lt(x0, key), x0, x, key, {==}, S.bsearch.lower_bound(t, key), ip, l, h => bs.above(t, key, ip, x, bs.sorted_tail(t, x0, s2), e2, h), bs.head_le(t, x0, s2, ip, x, e2))

# Binary search: find

def bs.hit_none(c: Bool, +i: Nat, e: {S.bsearch.find.hit(c, i) == None{} : Maybe<&2, Nat>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.sn(i, e))
    case False{}:
      {==}

def bs.hit_shift(c: Bool, +i: Nat, e: {S.bsearch.find.hit(c, 1n+i) == None{} : Maybe<&2, Nat>}) -> {S.bsearch.find.hit(c, i) == None{} : Maybe<&2, Nat>}:
  match c:
    case True{}:
      Empty.absurd({Some{i} == None{} : Maybe<&2, Nat>}, absurd.sn(1n+i, e))
    case False{}:
      {==}

def bs.check_shift(m: Maybe<&2, U32>, +i: Nat, +key: U32, e: {S.bsearch.find.check(1n+i, m, key) == None{} : Maybe<&2, Nat>}) -> {S.bsearch.find.check(i, m, key) == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      bs.hit_shift(U32.is_eq(y, key), i, e)

def bs.some.h(c: Bool, x: U32, key: U32, ec: {U32.is_eq(x, key) == c : Bool}, +xs: List<&2, U32>, +lb: Nat, +i: Nat, e: {S.bsearch.find.hit(c, lb) == Some{i} : Maybe<&2, Nat>}, g: {List.get(&2, U32, xs, lb) == Some{x} : Maybe<&2, U32>}) -> {List.get(&2, U32, xs, i) == Some{key} : Maybe<&2, U32>}:
  match c:
    case True{}:
      %some_inj(lb, i, e) : {List.get(&2, U32, xs, _) == Some{key} : Maybe<&2, U32>}
      %u32.eq(x, key, ec) : {List.get(&2, U32, xs, lb) == Some{_} : Maybe<&2, U32>}
      g
    case False{}:
      Empty.absurd({List.get(&2, U32, xs, i) == Some{key} : Maybe<&2, U32>}, absurd.ns(i, e))

def bs.some(m: Maybe<&2, U32>, +key: U32, +xs: List<&2, U32>, +lb: Nat, +i: Nat, g: {List.get(&2, U32, xs, lb) == m : Maybe<&2, U32>}, e: {S.bsearch.find.check(lb, m, key) == Some{i} : Maybe<&2, Nat>}) -> {List.get(&2, U32, xs, i) == Some{key} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({List.get(&2, U32, xs, i) == Some{key} : Maybe<&2, U32>}, absurd.ns(i, e))
    case Some{+x}:
      bs.some.h(U32.is_eq(x, key), x, key, {==}, xs, lb, i, e, g)

def bs.none0(c: Bool, +x0: U32, +key: U32, ec: {U32.is_lt(x0, key) == c : Bool}, +t: List<&2, U32>, +r: Nat, e: {S.bsearch.find.check(S.bsearch.below.step(c, r), List.get(&2, U32, Con{x0, t}, S.bsearch.below.step(c, r)), key) == None{} : Maybe<&2, Nat>}) -> {U32.is_eq(x0, key) == False{} : Bool}:
  match c:
    case True{}:
      u32.lt_ne(x0, key, ec)
    case False{}:
      bs.hit_none(U32.is_eq(x0, key), 0n, e)

def bs.none1(c: Bool, +x0: U32, +x: U32, +key: U32, ec: {U32.is_lt(x0, key) == c : Bool}, +t: List<&2, U32>, +r: Nat, e: {S.bsearch.find.check(S.bsearch.below.step(c, r), List.get(&2, U32, Con{x0, t}, S.bsearch.below.step(c, r)), key) == None{} : Maybe<&2, Nat>}, ih: {S.bsearch.find.check(r, List.get(&2, U32, t, r), key) == None{} : Maybe<&2, Nat>} -> {U32.is_eq(x, key) == False{} : Bool}, h: {U32.is_le(x0, x) == True{} : Bool}) -> {U32.is_eq(x, key) == False{} : Bool}:
  match c:
    case True{}:
      ih(bs.check_shift(List.get(&2, U32, t, r), r, key, e))
    case False{}:
      u32.gt_le_ne(x0, x, key, ec, bs.hit_none(U32.is_eq(x0, key), 0n, e), h)

def bs.none(xs: List<&2, U32>, +key: U32, i: Nat, +x: U32, s: {S.bsearch.sorted(xs) == True{} : Bool}, e: {S.bsearch.find(xs, key) == None{} : Maybe<&2, Nat>}, g: {List.get(&2, U32, xs, i) == Some{x} : Maybe<&2, U32>}) -> {U32.is_eq(x, key) == False{} : Bool}:
  match xs i:
    case Nil{} _:
      Empty.absurd({U32.is_eq(x, key) == False{} : Bool}, absurd.ns32(x, g))
    case Con{+x0, +t} 0n:
      %some_inj32(x0, x, g) : {U32.is_eq(_, key) == False{} : Bool}
      bs.none0(U32.is_lt(x0, key), x0, key, {==}, t, S.bsearch.lower_bound(t, key), e)
    case Con{+x0, +t} 1n+ +ip:
      +s2 = s
      +g2 = g
      bs.none1(U32.is_lt(x0, key), x0, x, key, {==}, t, S.bsearch.lower_bound(t, key), e, h => bs.none(t, key, ip, x, bs.sorted_tail(t, x0, s2), h, g2), bs.head_le(t, x0, s2, ip, x, g2))

def bs.find_some(+xs: List<&2, U32>, +key: U32, +i: Nat, e: {S.bsearch.find(xs, key) == Some{i} : Maybe<&2, Nat>}) -> {List.get(&2, U32, xs, i) == Some{key} : Maybe<&2, U32>}:
  bs.some(List.get(&2, U32, xs, S.bsearch.lower_bound(xs, key)), key, xs, S.bsearch.lower_bound(xs, key), i, {==}, e)

# The laws: binary search

def Laws.lower_bound_le_length(xs, key):
  bs.le_len(xs, key)

def Laws.lower_bound_below(xs, key, i, x, e, l):
  bs.below(xs, key, i, x, e, l)

def Laws.lower_bound_above(xs, key, i, x, s, e, l):
  bs.above(xs, key, i, x, s, e, l)

def Laws.find_some(xs, key, i, e):
  bs.find_some(xs, key, i, e)

def Laws.find_none(xs, key, i, x, s, e, g):
  bs.none(xs, key, i, x, s, e, g)

def Laws.vec_lower_bound():
  {==}

def Laws.vec_array_lower_bound():
  {==}

def Laws.vec_array_lower_bound_end():
  {==}

def Laws.vec_array_find():
  {==}

def Laws.vec_array_find_none():
  {==}

def Laws.wit_first_last():
  {==}

def Laws.wit_first_last64():
  {==}

def Laws.wit_next():
  {==}

def Laws.wit_bsearch():
  {==}
