import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./algo.bend as A
import ./bitmap.bend as M
import ./bsearch.bend as S
import ../array/array.bend as AR
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ../u32/u32.bend as UN
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./proof_u32.bend as U
import ./proof_bsearch.bend as Q
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

# Binary search on an Array<U32>
# ===============================
#
# The array is reflected once into Arrays.of_list(d, l, 0) (array's
# `reflect`); proof_bsearch.bend shows that the search on it is Q.bq.run on
# Data and hands the array back (Q.bq.go). Below, Q.bq.run is followed on
# the values of lo and hi: lo <= lower_bound <= hi <= n throughout, and
# hi - lo < 2^f with f halvings left, so after the 33 halvings lo is the
# lower bound. LB below is Q.bq.lb(l, n, key), the lower bound of the
# searched prefix Q.bq.pre(l, n) of l.

# the element read at m is below the key exactly when m is below LB
def ba.kc(b: Bool, +l: List<&2, U32>, +key: U32, +n: U32, +hs: {S.bsearch.sorted(Q.bq.pre(l, n)) == True{} : Bool}, +m: Nat, +eg: {List.get(&2, U32, Q.bq.pre(l, n), m) == Some{AR.Arrays.nth(U32, l, m, 0)} : Maybe<&2, U32>}, +eb: {Nat.is_lt(m, Q.bq.lb(l, n, key)) == b : Bool}) -> {U32.is_lt(AR.Arrays.nth(U32, l, m, 0), key) == b : Bool}:
  match b:
    case True{}:
      bs.below(Q.bq.pre(l, n), key, m, AR.Arrays.nth(U32, l, m, 0), eg, eb)
    case False{}:
      bs.above(Q.bq.pre(l, n), key, m, AR.Arrays.nth(U32, l, m, 0), hs, eg, Q.bq.not_lt(m, Q.bq.lb(l, n, key), eb))

def ba.key_cmp(+d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, +key: U32, +n: U32, +hN: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +hs: {S.bsearch.sorted(Q.bq.pre(l, n)) == True{} : Bool}, +mid: U32, +m: Nat, +eM: {U32.to_nat(mid) == m : Nat}, +hmN: {Nat.is_lt(m, U32.to_nat(n)) == True{} : Bool}) -> {U32.is_lt(AR.Arrays.nth(U32, l, AR.Arrays.index(d, mid), 0), key) == Nat.is_lt(m, Q.bq.lb(l, n, key)) : Bool}:
  +hmS = Q.bq.lt_le_trans(m, U32.to_nat(n), AR.Arrays.slots(d), hmN, hN)
  +eI = Equal.trans(Nat, AR.Arrays.index(d, mid), U32.to_nat(mid), m, AL.index_of_u32(d, mid, Q.bq.lt_rw(m, AR.Arrays.slots(d), U32.to_nat(mid), AR.Arrays.slots(d), Equal.sym(Nat, U32.to_nat(mid), m, eM), {==}, hmS)), eM)
  +hml = Q.bq.lt_rw(m, AR.Arrays.slots(d), m, List.length(&2, U32, l), {==}, Equal.sym(Nat, List.length(&2, U32, l), AR.Arrays.slots(d), hl), hmS)
  +eg = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, Q.bq.pre(l, n), m), List.get(&2, U32, l, m), Some{AR.Arrays.nth(U32, l, m, 0)}, Q.bq.get_take(l, U32.to_nat(n), m, hmN), Q.bq.get_nth(l, m, hml))
  %Equal.sym(Nat, AR.Arrays.index(d, mid), m, eI) : {U32.is_lt(AR.Arrays.nth(U32, l, _, 0), key) == Nat.is_lt(m, Q.bq.lb(l, n, key)) : Bool}
  ba.kc(Nat.is_lt(m, Q.bq.lb(l, n, key)), l, key, n, hs, m, eg, {==})

# after a halving that keeps the upper half: hi - (mid + 1) is
# (hi - lo) - (1 + (hi - lo) / 2)
def ba.jz_eq(+lo: U32, +hi: U32, eI: {U32.to_nat(U32.inc(Q.bq.mid(lo, hi))) == 1n+Q.bq.m(lo, hi) : Nat}, ehs: {Nat.add(U32.to_nat(lo), Q.bq.s(lo, hi)) == U32.to_nat(hi) : Nat}) -> {Nat.sub(Q.bq.s(lo, hi), 1n+UN.U32Nat.half(Q.bq.s(lo, hi))) == Q.bq.s(U32.inc(Q.bq.mid(lo, hi)), hi) : Nat}:
  +l0 = U32.to_nat(lo)
  +s = Q.bq.s(lo, hi)
  +hs = UN.U32Nat.half(s)
  +m = Q.bq.m(lo, hi)
  %Equal.sym(Nat, U32.to_nat(U32.inc(Q.bq.mid(lo, hi))), 1n+m, eI) : {Nat.sub(s, 1n+hs) == Nat.sub(U32.to_nat(hi), _) : Nat}
  %ehs : {Nat.sub(s, 1n+hs) == Nat.sub(_, 1n+m) : Nat}
  %U.uq.add_succ(l0, hs) : {Nat.sub(s, 1n+hs) == Nat.sub(Nat.add(l0, s), _) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(l0, s), Nat.add(l0, 1n+hs)), Nat.sub(s, 1n+hs), Q.bq.sub_cancel(l0, s, 1n+hs))

# one halving, with the element at mid below the key (b) or not
def ba.adv2(b: Bool, +g: Nat, +d: Nat, +l: List<&2, U32>, +key: U32, +n: U32, +lo: U32, +hi: U32, +eb: {Nat.is_lt(Q.bq.m(lo, hi), Q.bq.lb(l, n, key)) == b : Bool}, +i1: {Nat.is_le(U32.to_nat(lo), Q.bq.lb(l, n, key)) == True{} : Bool}, +i2: {Nat.is_le(Q.bq.lb(l, n, key), U32.to_nat(hi)) == True{} : Bool}, +i3: {Nat.is_le(U32.to_nat(hi), U32.to_nat(n)) == True{} : Bool}, +hz: {Nat.is_lt(Q.bq.s(lo, hi), U.uq.pw(1n+g)) == True{} : Bool}, +eM: {U32.to_nat(Q.bq.mid(lo, hi)) == Q.bq.m(lo, hi) : Nat}, +ehs: {Nat.add(U32.to_nat(lo), Q.bq.s(lo, hi)) == U32.to_nat(hi) : Nat}, +hmh: {Nat.is_lt(Q.bq.m(lo, hi), U32.to_nat(hi)) == True{} : Bool}, ih: @lo2: U32 -> @hi2: U32 -> @j1: {Nat.is_le(U32.to_nat(lo2), Q.bq.lb(l, n, key)) == True{} : Bool} -> @j2: {Nat.is_le(Q.bq.lb(l, n, key), U32.to_nat(hi2)) == True{} : Bool} -> @j3: {Nat.is_le(U32.to_nat(hi2), U32.to_nat(n)) == True{} : Bool} -> @jz: {Nat.is_lt(Q.bq.s(lo2, hi2), U.uq.pw(g)) == True{} : Bool} -> {U32.to_nat(Q.bq.run(g, d, l, lo2, hi2, key)) == Q.bq.lb(l, n, key) : Nat}) -> {U32.to_nat(Q.bq.run(g, d, l, Q.bq.lo_b(b, lo, Q.bq.mid(lo, hi)), Q.bq.hi_b(b, hi, Q.bq.mid(lo, hi)), key)) == Q.bq.lb(l, n, key) : Nat}:
  match b:
    case True{}:
      +h0 = U32.to_nat(hi)
      +l0 = U32.to_nat(lo)
      +s = Q.bq.s(lo, hi)
      +m = Q.bq.m(lo, hi)
      +mid = Q.bq.mid(lo, hi)
      +lb = Q.bq.lb(l, n, key)
      +hinc = Q.bq.le_rw(1n+m, h0, 1n+U32.to_nat(mid), h0, U.uq.succ_cong(m, U32.to_nat(mid), Equal.sym(Nat, U32.to_nat(mid), m, eM)), {==}, Equal.trans(Bool, Nat.is_le(1n+m, h0), Nat.is_lt(m, h0), True{}, U.uq.le_succ(m, h0), hmh))
      +eI = Equal.trans(Nat, U32.to_nat(U32.inc(mid)), 1n+U32.to_nat(mid), 1n+m, UL.u32_inc_value(mid, hi, hinc), U.uq.succ_cong(U32.to_nat(mid), m, eM))
      +j1 = Q.bq.le_rw(1n+m, lb, U32.to_nat(U32.inc(mid)), lb, Equal.sym(Nat, U32.to_nat(U32.inc(mid)), 1n+m, eI), {==}, Equal.trans(Bool, Nat.is_le(1n+m, lb), Nat.is_lt(m, lb), True{}, U.uq.le_succ(m, lb), eb))
      +jz = Q.bq.lt_rw(Nat.sub(s, 1n+UN.U32Nat.half(s)), U.uq.pw(g), Q.bq.s(U32.inc(mid), hi), U.uq.pw(g), ba.jz_eq(lo, hi, eI, ehs), {==}, Q.bq.hr_lt_pw(s, U.uq.pw(g), hz))
      ih(U32.inc(mid), hi, j1, i2, i3, jz)
    case False{}:
      +h0 = U32.to_nat(hi)
      +l0 = U32.to_nat(lo)
      +s = Q.bq.s(lo, hi)
      +m = Q.bq.m(lo, hi)
      +mid = Q.bq.mid(lo, hi)
      +lb = Q.bq.lb(l, n, key)
      +j2 = Q.bq.le_rw(lb, m, lb, U32.to_nat(mid), {==}, Equal.sym(Nat, U32.to_nat(mid), m, eM), Q.bq.not_lt(m, lb, eb))
      +j3 = Q.bq.le_rw(m, U32.to_nat(n), U32.to_nat(mid), U32.to_nat(n), Equal.sym(Nat, U32.to_nat(mid), m, eM), {==}, Q.bq.le_trans(m, h0, U32.to_nat(n), Q.bq.lt_le(m, h0, hmh), i3))
      +e2 = Equal.trans(Nat, UN.U32Nat.half(s), Nat.sub(Nat.add(l0, UN.U32Nat.half(s)), l0), Nat.sub(U32.to_nat(mid), l0), Equal.sym(Nat, Nat.sub(Nat.add(l0, UN.U32Nat.half(s)), l0), UN.U32Nat.half(s), U.uq.sub_add_l(l0, UN.U32Nat.half(s))), Equal.cong(Nat, Nat, z => Nat.sub(z, l0), m, U32.to_nat(mid), Equal.sym(Nat, U32.to_nat(mid), m, eM)))
      +jz = Q.bq.lt_rw(UN.U32Nat.half(s), U.uq.pw(g), Q.bq.s(lo, mid), U.uq.pw(g), e2, {==}, Q.bq.half_lt_pw(s, U.uq.pw(g), hz))
      ih(lo, mid, i1, j2, j3, jz)

# one halving of [lo, hi): active when lo < hi (c)
def ba.adv(c: Bool, +g: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, +key: U32, +n: U32, +hN: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +hs: {S.bsearch.sorted(Q.bq.pre(l, n)) == True{} : Bool}, +lo: U32, +hi: U32, +ec: {U32.is_lt(lo, hi) == c : Bool}, +i1: {Nat.is_le(U32.to_nat(lo), Q.bq.lb(l, n, key)) == True{} : Bool}, +i2: {Nat.is_le(Q.bq.lb(l, n, key), U32.to_nat(hi)) == True{} : Bool}, +i3: {Nat.is_le(U32.to_nat(hi), U32.to_nat(n)) == True{} : Bool}, +hz: {Nat.is_lt(Q.bq.s(lo, hi), U.uq.pw(1n+g)) == True{} : Bool}, ih: @lo2: U32 -> @hi2: U32 -> @j1: {Nat.is_le(U32.to_nat(lo2), Q.bq.lb(l, n, key)) == True{} : Bool} -> @j2: {Nat.is_le(Q.bq.lb(l, n, key), U32.to_nat(hi2)) == True{} : Bool} -> @j3: {Nat.is_le(U32.to_nat(hi2), U32.to_nat(n)) == True{} : Bool} -> @jz: {Nat.is_lt(Q.bq.s(lo2, hi2), U.uq.pw(g)) == True{} : Bool} -> {U32.to_nat(Q.bq.run(g, d, l, lo2, hi2, key)) == Q.bq.lb(l, n, key) : Nat}) -> {U32.to_nat(Q.bq.run(g, d, l, Q.bq.nlo.a(c, U32.is_lt(Q.bq.x(d, l, lo, hi), key), lo, Q.bq.mid(lo, hi)), Q.bq.nhi.a(c, U32.is_lt(Q.bq.x(d, l, lo, hi), key), hi, Q.bq.mid(lo, hi)), key)) == Q.bq.lb(l, n, key) : Nat}:
  match c:
    case False{}:
      +h0 = U32.to_nat(hi)
      +l0 = U32.to_nat(lo)
      +e0 = Q.bq.sub_le0(h0, l0, Q.bq.not_lt(l0, h0, u32.mv_lt(lo, hi, False{}, ec)))
      ih(lo, hi, i1, i2, i3, Q.bq.lt_rw(0n, U.uq.pw(g), Q.bq.s(lo, hi), U.uq.pw(g), Equal.sym(Nat, Q.bq.s(lo, hi), 0n, e0), {==}, Q.bq.pw_pos(g)))
    case True{}:
      +h0 = U32.to_nat(hi)
      +l0 = U32.to_nat(lo)
      +s = Q.bq.s(lo, hi)
      +m = Q.bq.m(lo, hi)
      +mid = Q.bq.mid(lo, hi)
      +lb = Q.bq.lb(l, n, key)
      +sh = U32.to_nat(U32.shr(U32.sub(hi, lo)))
      +hlt = u32.mv_lt(lo, hi, True{}, ec)
      +hle = Q.bq.lt_le(l0, h0, hlt)
      +eD = UL.u32_sub_value(hi, lo, hle)
      +eE = Equal.trans(Nat, sh, UN.U32Nat.half(U32.to_nat(U32.sub(hi, lo))), UN.U32Nat.half(s), UL.u32_shr_value(U32.sub(hi, lo)), Equal.cong(Nat, Nat, z => UN.U32Nat.half(z), U32.to_nat(U32.sub(hi, lo)), s, eD))
      +ehs = Q.bq.add_sub(l0, h0, hle)
      +hmh = Q.bq.lt_rw(Nat.add(l0, UN.U32Nat.half(s)), Nat.add(l0, s), m, h0, {==}, ehs, Equal.trans(Bool, Nat.is_lt(Nat.add(l0, UN.U32Nat.half(s)), Nat.add(l0, s)), Nat.is_lt(UN.U32Nat.half(s), s), True{}, Q.bq.lt_cancel(l0, UN.U32Nat.half(s), s), Q.bq.half_lt(s, Q.bq.sub_pos(l0, h0, hlt))))
      +hadd = Q.bq.le_rw(m, h0, Nat.add(l0, sh), h0, Equal.cong(Nat, Nat, z => Nat.add(l0, z), UN.U32Nat.half(s), sh, Equal.sym(Nat, sh, UN.U32Nat.half(s), eE)), {==}, Q.bq.lt_le(m, h0, hmh))
      +eM = Equal.trans(Nat, U32.to_nat(mid), Nat.add(l0, sh), m, UL.u32_add_value(lo, U32.shr(U32.sub(hi, lo)), hi, hadd), Equal.cong(Nat, Nat, z => Nat.add(l0, z), sh, UN.U32Nat.half(s), eE))
      +hmN = Q.bq.lt_le_trans(m, h0, U32.to_nat(n), hmh, i3)
      %Equal.sym(Bool, U32.is_lt(Q.bq.x(d, l, lo, hi), key), Nat.is_lt(m, lb), ba.key_cmp(d, l, hl, key, n, hN, hs, mid, m, eM, hmN)) : {U32.to_nat(Q.bq.run(g, d, l, Q.bq.lo_b(_, lo, mid), Q.bq.hi_b(_, hi, mid), key)) == lb : Nat}
      ba.adv2(Nat.is_lt(m, lb), g, d, l, key, n, lo, hi, {==}, i1, i2, i3, hz, eM, ehs, hmh, ih)

# f halvings from lo <= LB <= hi <= n with hi - lo < 2^f end at LB
def ba.run(f: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, +key: U32, +n: U32, +hN: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +hs: {S.bsearch.sorted(Q.bq.pre(l, n)) == True{} : Bool}, +lo: U32, +hi: U32, +i1: {Nat.is_le(U32.to_nat(lo), Q.bq.lb(l, n, key)) == True{} : Bool}, +i2: {Nat.is_le(Q.bq.lb(l, n, key), U32.to_nat(hi)) == True{} : Bool}, +i3: {Nat.is_le(U32.to_nat(hi), U32.to_nat(n)) == True{} : Bool}, +hz: {Nat.is_lt(Q.bq.s(lo, hi), U.uq.pw(f)) == True{} : Bool}) -> {U32.to_nat(Q.bq.run(f, d, l, lo, hi, key)) == Q.bq.lb(l, n, key) : Nat}:
  match f:
    case 0n:
      +l0 = U32.to_nat(lo)
      +h0 = U32.to_nat(hi)
      +lb = Q.bq.lb(l, n, key)
      Q.bq.le_antisym(l0, lb, i1, Q.bq.le_trans(lb, h0, l0, i2, Q.bq.sub0_le(h0, l0, Q.bq.lt_one(Q.bq.s(lo, hi), hz))))
    case 1n+ +g:
      ba.adv(U32.is_lt(lo, hi), g, d, l, hl, key, n, hN, hs, lo, hi, {==}, i1, i2, i3, hz, lo2 => hi2 => j1 => j2 => j3 => jz => ba.run(g, d, l, hl, key, n, hN, hs, lo2, hi2, j1, j2, j3, jz))

# n < 2^32 < 2^33: the 33 halvings suffice (stated so that 2^33 is never
# expanded)
def ba.hz33(n: U32) -> {Nat.is_lt(Q.bq.s(0, n), U.uq.pw(33n)) == True{} : Bool}:
  match n:
    case U32{+w}:
      U.uq.lt_succ_pw(32n, 33n, {==}, Word.to_nat(32n, w), Q.bq.s(0, U32{w}), Equal.sym(Nat, Nat.sub(Word.to_nat(32n, w), 0n), Word.to_nat(32n, w), Q.bq.sub_zero(Word.to_nat(32n, w))), U.uq.val_lt(32n, w))

# the lower bound is at most n
def ba.lb_le(-d: Nat, +l: List<&2, U32>, +n: U32, +key: U32, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}) -> {Nat.is_le(Q.bq.lb(l, n, key), U32.to_nat(n)) == True{} : Bool}:
  Q.bq.le_rw(Q.bq.lb(l, n, key), List.length(&2, U32, Q.bq.pre(l, n)), Q.bq.lb(l, n, key), U32.to_nat(n), {==}, Q.bq.len_take(l, U32.to_nat(n), Q.bq.le_rw(U32.to_nat(n), AR.Arrays.slots(d), U32.to_nat(n), List.length(&2, U32, l), {==}, Equal.sym(Nat, List.length(&2, U32, l), AR.Arrays.slots(d), hl), hn)), Laws.lower_bound_le_length(Q.bq.pre(l, n), key))

# the search's answer is the lower bound
def ba.answer(+d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, +key: U32, +n: U32, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +hs: {S.bsearch.sorted(Q.bq.pre(l, n)) == True{} : Bool}) -> {U32.to_nat(Q.bq.run(33n, d, l, 0, n, key)) == Q.bq.lb(l, n, key) : Nat}:
  ba.run(33n, d, l, hl, key, n, hn, hs, 0, n, Q.bq.le_zero(Q.bq.lb(l, n, key)), ba.lb_le(d, l, n, key, hl, hn), Q.bq.le_refl(U32.to_nat(n)), ba.hz33(n))

# a sorted prefix of the reflected array is a sorted prefix of l
def ba.hs(+d: Nat, -a: Array<U32>, +l: List<&2, U32>, +n: U32, e1: {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}) -> {S.bsearch.sorted(Q.bq.pre(l, n)) == True{} : Bool}:
  %AL.of_list_leaves(U32, d, l, 0, hl) : {S.bsearch.sorted(List.take(&2, U32, _, U32.to_nat(n))) == True{} : Bool}
  %Equal.sym(Array<U32>, AR.Arrays.of_list(U32, d, l, 0), a, e1) : {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, _), U32.to_nat(n))) == True{} : Bool}
  hs

# The find: the element at the lower bound, if it is inside the first n

def ba.hit(b: Bool, +r: U32, +lb: Nat, +er: {U32.to_nat(r) == lb : Nat}) -> {Laws.algo_index_nat(Bool.pick(Maybe<&2, U32>, b, Some{r}, None{})) == S.bsearch.find.hit(b, lb) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, U32.to_nat(r), lb, er)
    case False{}:
      {==}

def ba.fd(c: Bool, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}, +key: U32, +n: U32, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +r: U32, +ec: {U32.is_lt(r, n) == c : Bool}, +er: {U32.to_nat(r) == Q.bq.lb(l, n, key) : Nat}) -> {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(c, (AR.Arrays.of_list(U32, d, l, 0), AR.Arrays.nth(U32, l, AR.Arrays.index(d, r), 0)), r, key))) == S.bsearch.find(Q.bq.pre(l, n), key) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      +lb = Q.bq.lb(l, n, key)
      +nn = U32.to_nat(n)
      +pre = Q.bq.pre(l, n)
      +hnl = Q.bq.le_rw(nn, AR.Arrays.slots(d), nn, List.length(&2, U32, l), {==}, Equal.sym(Nat, List.length(&2, U32, l), AR.Arrays.slots(d), hl), hn)
      +hc = Equal.trans(Bool, Nat.is_lt(lb, nn), Nat.is_lt(U32.to_nat(r), nn), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, nn), lb, U32.to_nat(r), Equal.sym(Nat, U32.to_nat(r), lb, er)), u32.mv_lt(r, n, True{}, ec))
      +hls = Q.bq.lt_le_trans(lb, nn, AR.Arrays.slots(d), hc, hn)
      +ei = Equal.trans(Nat, AR.Arrays.index(d, r), U32.to_nat(r), lb, AL.index_of_u32(d, r, Q.bq.lt_rw(lb, AR.Arrays.slots(d), U32.to_nat(r), AR.Arrays.slots(d), Equal.sym(Nat, U32.to_nat(r), lb, er), {==}, hls)), er)
      +hll = Q.bq.lt_rw(lb, AR.Arrays.slots(d), lb, List.length(&2, U32, l), {==}, Equal.sym(Nat, List.length(&2, U32, l), AR.Arrays.slots(d), hl), hls)
      +eg = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, pre, lb), List.get(&2, U32, l, lb), Some{AR.Arrays.nth(U32, l, lb, 0)}, Q.bq.get_take(l, nn, lb, hc), Q.bq.get_nth(l, lb, hll))
      %Equal.sym(Nat, AR.Arrays.index(d, r), lb, ei) : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(True{}, (AR.Arrays.of_list(U32, d, l, 0), AR.Arrays.nth(U32, l, _, 0)), r, key))) == S.bsearch.find(pre, key) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, pre, lb), Some{AR.Arrays.nth(U32, l, lb, 0)}, eg) : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(True{}, (AR.Arrays.of_list(U32, d, l, 0), AR.Arrays.nth(U32, l, lb, 0)), r, key))) == S.bsearch.find.check(lb, _, key) : Maybe<&2, Nat>}
      ba.hit(U32.is_eq(AR.Arrays.nth(U32, l, lb, 0), key), r, lb, er)
    case False{}:
      +lb = Q.bq.lb(l, n, key)
      +nn = U32.to_nat(n)
      +pre = Q.bq.pre(l, n)
      +hnl = Q.bq.le_rw(nn, AR.Arrays.slots(d), nn, List.length(&2, U32, l), {==}, Equal.sym(Nat, List.length(&2, U32, l), AR.Arrays.slots(d), hl), hn)
      +hc = Equal.trans(Bool, Nat.is_lt(lb, nn), Nat.is_lt(U32.to_nat(r), nn), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, nn), lb, U32.to_nat(r), Equal.sym(Nat, U32.to_nat(r), lb, er)), u32.mv_lt(r, n, False{}, ec))
      +eln = Q.bq.le_antisym(lb, nn, ba.lb_le(d, l, n, key, hl, hn), Q.bq.not_lt(lb, nn, hc))
      +eg = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, pre, lb), List.get(&2, U32, pre, List.length(&2, U32, pre)), None{}, Equal.cong(Nat, Maybe<&2, U32>, z => List.get(&2, U32, pre, z), lb, List.length(&2, U32, pre), Equal.trans(Nat, lb, nn, List.length(&2, U32, pre), eln, Equal.sym(Nat, List.length(&2, U32, pre), nn, Q.bq.len_take(l, nn, hnl)))), Q.bq.get_len(pre))
      %Equal.sym(Maybe<&2, U32>, List.get(&2, U32, pre, lb), None{}, eg) : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(False{}, (AR.Arrays.of_list(U32, d, l, 0), AR.Arrays.nth(U32, l, AR.Arrays.index(d, r), 0)), r, key))) == S.bsearch.find.check(lb, _, key) : Maybe<&2, Nat>}
      {==}

def ba.fs(c: Bool, -a0: Array<U32>, -x: U32, +r: U32, +key: U32) -> {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(c, (a0, x), r, key)) == a0 : Array<U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# The laws, each on its array reflected

def ba.lb.body(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +key: U32, hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}, +l: List<&2, U32>, +e1: {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {U32.to_nat(Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(a, n, key))) == S.bsearch.lower_bound(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n)), key) : Nat}:
  -ol = AR.Arrays.of_list(U32, d, l, 0)
  %e1 : {U32.to_nat(Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(_, n, key))) == S.bsearch.lower_bound(List.take(&2, U32, AR.Arrays.leaves(U32, _), U32.to_nat(n)), key) : Nat}
  %Equal.sym(List<&2, U32>, AR.Arrays.leaves(U32, ol), l, AL.of_list_leaves(U32, d, l, 0, hl)) : {U32.to_nat(Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(ol, n, key))) == S.bsearch.lower_bound(List.take(&2, U32, _, U32.to_nat(n)), key) : Nat}
  %Equal.sym(Array<U32> & U32, S.bsearch.array.go(33n, S.BsearchState{ol, 0, n}, key), (ol, Q.bq.run(33n, d, l, 0, n, key)), Q.bq.go(33n, d, l, hl, hd, 0, n, key)) : {U32.to_nat(Pair.snd(Array<U32>, U32, _)) == Q.bq.lb(l, n, key) : Nat}
  ba.answer(d, l, hl, key, n, hn, ba.hs(d, a, l, n, e1, hl, hs))

def ba.lb.ref(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +key: U32, hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}, r: &l: List<&2, U32> -> {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {U32.to_nat(Pair.snd(Array<U32>, U32, S.bsearch.array_lower_bound(a, n, key))) == S.bsearch.lower_bound(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n)), key) : Nat}:
  (l, e) = r
  (e1, hl) = e
  ba.lb.body(d, a, hd, n, hn, key, hs, l, e1, hl)

def ba.lbs.body(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +key: U32, +l: List<&2, U32>, +e1: {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {Pair.fst(Array<U32>, U32, S.bsearch.array_lower_bound(a, n, key)) == a : Array<U32>}:
  -ol = AR.Arrays.of_list(U32, d, l, 0)
  %e1 : {Pair.fst(Array<U32>, U32, S.bsearch.array_lower_bound(_, n, key)) == _ : Array<U32>}
  %Equal.sym(Array<U32> & U32, S.bsearch.array.go(33n, S.BsearchState{ol, 0, n}, key), (ol, Q.bq.run(33n, d, l, 0, n, key)), Q.bq.go(33n, d, l, hl, hd, 0, n, key)) : {Pair.fst(Array<U32>, U32, _) == ol : Array<U32>}
  {==}

def ba.lbs.ref(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +key: U32, r: &l: List<&2, U32> -> {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {Pair.fst(Array<U32>, U32, S.bsearch.array_lower_bound(a, n, key)) == a : Array<U32>}:
  (l, e) = r
  (e1, hl) = e
  ba.lbs.body(d, a, hd, n, key, l, e1, hl)

def ba.fl.body(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +key: U32, hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}, +l: List<&2, U32>, +e1: {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(a, n, key))) == S.bsearch.find(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n)), key) : Maybe<&2, Nat>}:
  -ol = AR.Arrays.of_list(U32, d, l, 0)
  +r = Q.bq.run(33n, d, l, 0, n, key)
  %e1 : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(_, n, key))) == S.bsearch.find(List.take(&2, U32, AR.Arrays.leaves(U32, _), U32.to_nat(n)), key) : Maybe<&2, Nat>}
  %Equal.sym(List<&2, U32>, AR.Arrays.leaves(U32, ol), l, AL.of_list_leaves(U32, d, l, 0, hl)) : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(ol, n, key))) == S.bsearch.find(List.take(&2, U32, _, U32.to_nat(n)), key) : Maybe<&2, Nat>}
  %Equal.sym(Array<U32> & U32, S.bsearch.array.go(33n, S.BsearchState{ol, 0, n}, key), (ol, r), Q.bq.go(33n, d, l, hl, hd, 0, n, key)) : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array.find(_, n, key))) == S.bsearch.find(Q.bq.pre(l, n), key) : Maybe<&2, Nat>}
  %Equal.sym(Array<U32> & U32, Array.get(U32, ol, r), (ol, AR.Arrays.nth(U32, l, AR.Arrays.index(d, r), 0)), AL.of_list_get(U32, d, l, 0, hl, hd, r)) : {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(U32.is_lt(r, n), _, r, key))) == S.bsearch.find(Q.bq.pre(l, n), key) : Maybe<&2, Nat>}
  ba.fd(U32.is_lt(r, n), d, l, hl, key, n, hn, r, {==}, ba.answer(d, l, hl, key, n, hn, ba.hs(d, a, l, n, e1, hl, hs)))

def ba.fl.ref(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +hn: {Nat.is_le(U32.to_nat(n), AR.Arrays.slots(d)) == True{} : Bool}, +key: U32, hs: {S.bsearch.sorted(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n))) == True{} : Bool}, r: &l: List<&2, U32> -> {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {Laws.algo_index_nat(Pair.snd(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(a, n, key))) == S.bsearch.find(List.take(&2, U32, AR.Arrays.leaves(U32, a), U32.to_nat(n)), key) : Maybe<&2, Nat>}:
  (l, e) = r
  (e1, hl) = e
  ba.fl.body(d, a, hd, n, hn, key, hs, l, e1, hl)

def ba.fls.body(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +key: U32, +l: List<&2, U32>, +e1: {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(a, n, key)) == a : Array<U32>}:
  -ol = AR.Arrays.of_list(U32, d, l, 0)
  +r = Q.bq.run(33n, d, l, 0, n, key)
  %e1 : {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(_, n, key)) == _ : Array<U32>}
  %Equal.sym(Array<U32> & U32, S.bsearch.array.go(33n, S.BsearchState{ol, 0, n}, key), (ol, r), Q.bq.go(33n, d, l, hl, hd, 0, n, key)) : {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array.find(_, n, key)) == ol : Array<U32>}
  %Equal.sym(Array<U32> & U32, Array.get(U32, ol, r), (ol, AR.Arrays.nth(U32, l, AR.Arrays.index(d, r), 0)), AL.of_list_get(U32, d, l, 0, hl, hd, r)) : {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array.found(U32.is_lt(r, n), _, r, key)) == ol : Array<U32>}
  ba.fs(U32.is_lt(r, n), ol, AR.Arrays.nth(U32, l, AR.Arrays.index(d, r), 0), r, key)

def ba.fls.ref(+d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +n: U32, +key: U32, r: &l: List<&2, U32> -> {AR.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == AR.Arrays.slots(d) : Nat}) -> {Pair.fst(Array<U32>, Maybe<&2, U32>, S.bsearch.array_find(a, n, key)) == a : Array<U32>}:
  (l, e) = r
  (e1, hl) = e
  ba.fls.body(d, a, hd, n, key, l, e1, hl)

def Laws.array_lower_bound_list(d, a, hp, hd, n, hn, key, hs):
  ba.lb.ref(d, a, hd, n, hn, key, hs, AL.reflect(U32, d, a, hp, 0))

def Laws.array_lower_bound_same(d, a, hp, hd, n, key):
  ba.lbs.ref(d, a, hd, n, key, AL.reflect(U32, d, a, hp, 0))

def Laws.array_find_list(d, a, hp, hd, n, hn, key, hs):
  ba.fl.ref(d, a, hd, n, hn, key, hs, AL.reflect(U32, d, a, hp, 0))

def Laws.array_find_same(d, a, hp, hd, n, key):
  ba.fls.ref(d, a, hd, n, key, AL.reflect(U32, d, a, hp, 0))

def Laws.wit_array_bsearch():
  {==}
