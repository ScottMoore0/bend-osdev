# Proof helpers for bend-osdev-word64: the shifts, as Nat facts, for words
# of two halves of any width n (W64 is n = 32).
#
# A shift left by k bits of a word of width n is ws.shl, k one-bit shifts
# (U32.shln is ws.shl at 32); a shift right is ws.shr. Their values: the
# shift left multiplies by 2^k, less the bits carried out (ws.shlk, with
# the carry ws.ov), and the shift right is the floor of a division by 2^k
# (ws.shr_le, ws.shr_lt). The bits carried out of a shift left by k are the
# shift right by n - k (ws.g1a, ws.g1b), since a value below 2^n has one
# quotient and remainder by 2^n (ws.uniq). An "or" of two words whose bits
# do not meet is their sum (ws.or_dis). The W64 shifts put these together
# across the halves (ws.gshl_lo, ws.gshl_hi, ws.gshr_lo_*, ws.gshr_hi_*).
#
# As in proof_value.bend, every lemma is for a width n that is a variable,
# so that no closed power of two is computed.
import Base
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ./proof_value.bend as P

# Nat

def ns.nd(x: Nat) -> Type:
  match x:
    case 0n:
      Empty
    case 1n+ +p:
      Unit

def ns.sz(-a: Nat, e: {1n+a == 0n : Nat}) -> Empty:
  %e : ns.nd(_)
  Unit{}

def ns.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : P.wn.bt(_)
  Unit{}

def ns.pred(x: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n+ +p:
      p

def ns.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, z => ns.pred(z), 1n+a, 1n+b, e)

def ns.double_add(x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      P.wn.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), P.wn.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), ns.double_add(p, y)))

def ns.add_cancel_l(k: Nat, +a: Nat, +b: Nat, e: {Nat.add(k, a) == Nat.add(k, b) : Nat}) -> {a == b : Nat}:
  match k:
    case 0n:
      e
    case 1n+ +p:
      ns.add_cancel_l(p, a, b, ns.succ_inj(Nat.add(p, a), Nat.add(p, b), e))

# b <= a: (a - b) + b = a
def ns.sub_add_le(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      Empty.absurd({Nat.add(0n, 1n+q) == 0n : Nat}, P.wn.ft(h))
    case 1n+ +p 0n:
      P.wn.add_zero(1n+p)
    case 1n+ +p 1n+ +q:
      Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p, P.wn.add_succ(Nat.sub(p, q), q), P.wn.succ_cong(Nat.add(Nat.sub(p, q), q), p, ns.sub_add_le(p, q, h)))

# k <= n: k + (n - k) = n
def ns.add_sub_le(+k: Nat, +n: Nat, h: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.add(k, Nat.sub(n, k)) == n : Nat}:
  Equal.trans(Nat, Nat.add(k, Nat.sub(n, k)), Nat.add(Nat.sub(n, k), k), n, P.wn.add_comm(k, Nat.sub(n, k)), ns.sub_add_le(n, k, h))

# k <= n: n - (n - k) = k
def ns.sub_sub(+k: Nat, +n: Nat, h: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.sub(n, Nat.sub(n, k)) == k : Nat}:
  %ns.add_sub_le(k, n, h) : {Nat.sub(_, Nat.sub(n, k)) == k : Nat}
  P.wn.sub_add(k, Nat.sub(n, k))

def ns.le_succ_self(x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      ns.le_succ_self(p)

# n - k <= n
def ns.sub_le(n: Nat, k: Nat) -> {Nat.is_le(Nat.sub(n, k), n) == True{} : Bool}:
  match n k:
    case 0n _:
      {==}
    case 1n+ +p 0n:
      P.wn.le_refl(1n+p)
    case 1n+ +p 1n+ +q:
      P.wn.le_trans(Nat.sub(p, q), p, 1n+p, ns.sub_le(p, q), ns.le_succ_self(p))

def ns.le_of_not_lt(k: Nat, n: Nat, e: {Nat.is_lt(k, n) == False{} : Bool}) -> {Nat.is_le(n, k) == True{} : Bool}:
  match k n:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, ns.tf(e))
    case 1n+ +p 0n:
      {==}
    case 1n+ +p 1n+ +q:
      ns.le_of_not_lt(p, q, e)

def ns.eq_zero(x: Nat, e: {Nat.is_eq(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, P.wn.ft(e))

def ns.lt_one(x: Nat, e: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, P.wn.ft(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, P.wn.not_lt_zero(p), e)))

def ns.lt_succ_self(x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      ns.lt_succ_self(p)

# 1 + 2a = 2b never holds; 2a = 2b gives a = b
def ns.odd_even(a: Nat, b: Nat, e: {1n+Nat.double(a) == Nat.double(b) : Nat}) -> Empty:
  match a b:
    case _ 0n:
      ns.sz(Nat.double(a), e)
    case 0n 1n+ +q:
      ns.sz(Nat.double(q), Equal.sym(Nat, 0n, 1n+Nat.double(q), ns.succ_inj(0n, 1n+Nat.double(q), e)))
    case 1n+ +p 1n+ +q:
      ns.odd_even(p, q, ns.succ_inj(1n+Nat.double(p), Nat.double(q), ns.succ_inj(2n+Nat.double(p), 1n+Nat.double(q), e)))

def ns.double_inj(a: Nat, b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      Empty.absurd({0n == 1n+q : Nat}, ns.sz(1n+Nat.double(q), Equal.sym(Nat, 0n, 2n+Nat.double(q), e)))
    case 1n+ +p 0n:
      Empty.absurd({1n+p == 0n : Nat}, ns.sz(1n+Nat.double(p), e))
    case 1n+ +p 1n+ +q:
      P.wn.succ_cong(p, q, ns.double_inj(p, q, ns.succ_inj(Nat.double(p), Nat.double(q), ns.succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))))

def ns.lt_dbl(x: Nat, y: Nat) -> {Nat.is_lt(Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      {==}
    case 1n+ +p 1n+ +q:
      ns.lt_dbl(p, q)

def ns.lt_dbl1(x: Nat, y: Nat) -> {Nat.is_lt(1n+Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      {==}
    case 1n+ +p 1n+ +q:
      ns.lt_dbl1(p, q)

def ns.le_double(x: Nat) -> {Nat.is_le(x, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      P.wn.le_trans(p, Nat.double(p), 1n+Nat.double(p), ns.le_double(p), ns.le_succ_self(Nat.double(p)))

# 2 * (x / 2) <= x < 2 + 2 * (x / 2)
def ns.half_le(x: Nat) -> {Nat.is_le(Nat.double(U.U32Nat.half(x)), x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          ns.half_le(q)

def ns.half_lt(x: Nat) -> {Nat.is_lt(x, 2n+Nat.double(U.U32Nat.half(x))) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          ns.half_lt(q)

def ns.le_add_mono_r(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %P.wn.add_comm(c, a) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %P.wn.add_comm(c, b) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), True{}, P.wn.le_add_l(c, a, b), h)

# z + 2^n * 0 = z
def ns.d0(+n: Nat, +z: Nat) -> {Nat.add(z, U.U32Nat.dbl(n, 0n)) == z : Nat}:
  Equal.trans(Nat, Nat.add(z, U.U32Nat.dbl(n, 0n)), Nat.add(z, 0n), z, Equal.cong(Nat, Nat, v => Nat.add(z, v), U.U32Nat.dbl(n, 0n), 0n, UL.dbl_zero(n)), P.wn.add_zero(z))

# x <= x * 2^j
def ns.dbl_ge(j: Nat, +x: Nat) -> {Nat.is_le(x, U.U32Nat.dbl(j, x)) == True{} : Bool}:
  match j:
    case 0n:
      P.wn.le_refl(x)
    case 1n+ +p:
      P.wn.le_trans(x, U.U32Nat.dbl(p, x), Nat.double(U.U32Nat.dbl(p, x)), ns.dbl_ge(p, x), ns.le_double(U.U32Nat.dbl(p, x)))

def ns.dbl_double(m: Nat, +x: Nat) -> {U.U32Nat.dbl(m, Nat.double(x)) == Nat.double(U.U32Nat.dbl(m, x)) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, v => Nat.double(v), U.U32Nat.dbl(p, Nat.double(x)), Nat.double(U.U32Nat.dbl(p, x)), ns.dbl_double(p, x))

def ns.dbl_comm(+m: Nat, +k: Nat, +x: Nat) -> {U.U32Nat.dbl(m, U.U32Nat.dbl(k, x)) == U.U32Nat.dbl(k, U.U32Nat.dbl(m, x)) : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(m, U.U32Nat.dbl(k, x)), U.U32Nat.dbl(Nat.add(m, k), x), U.U32Nat.dbl(k, U.U32Nat.dbl(m, x)), UL.dbl_dbl(m, k, x), Equal.trans(Nat, U.U32Nat.dbl(Nat.add(m, k), x), U.U32Nat.dbl(Nat.add(k, m), x), U.U32Nat.dbl(k, U.U32Nat.dbl(m, x)), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(v, x), Nat.add(m, k), Nat.add(k, m), P.wn.add_comm(m, k)), Equal.sym(Nat, U.U32Nat.dbl(k, U.U32Nat.dbl(m, x)), U.U32Nat.dbl(Nat.add(k, m), x), UL.dbl_dbl(k, m, x))))

# k <= n: 2^k * 2^(n - k) = 2^n, either way round
def ns.dkm(+n: Nat, +k: Nat, +x: Nat, h: {Nat.is_le(k, n) == True{} : Bool}) -> {U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), x)) == U.U32Nat.dbl(n, x) : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), x)), U.U32Nat.dbl(Nat.add(k, Nat.sub(n, k)), x), U.U32Nat.dbl(n, x), UL.dbl_dbl(k, Nat.sub(n, k), x), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(v, x), Nat.add(k, Nat.sub(n, k)), n, ns.add_sub_le(k, n, h)))

def ns.dmk(+n: Nat, +k: Nat, +x: Nat, h: {Nat.is_le(k, n) == True{} : Bool}) -> {U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, x)) == U.U32Nat.dbl(n, x) : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, x)), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), x)), U.U32Nat.dbl(n, x), ns.dbl_comm(Nat.sub(n, k), k, x), ns.dkm(n, k, x, h))

# n <= k: x * 2^k = (x * 2^(k - n)) * 2^n
def ns.dnj(+n: Nat, +k: Nat, +x: Nat, h: {Nat.is_le(n, k) == True{} : Bool}) -> {U.U32Nat.dbl(k, x) == U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), x)) : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(k, x), U.U32Nat.dbl(Nat.add(n, Nat.sub(k, n)), x), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), x)), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(v, x), k, Nat.add(n, Nat.sub(k, n)), Equal.sym(Nat, Nat.add(n, Nat.sub(k, n)), k, ns.add_sub_le(n, k, h))), Equal.sym(Nat, U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), x)), U.U32Nat.dbl(Nat.add(n, Nat.sub(k, n)), x), UL.dbl_dbl(n, Nat.sub(k, n), x)))

# Words: shifts by k bits

def ws.shl(+n: Nat, k: Nat, w: Word(n)) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+ +p:
      Word.shl(n, ws.shl(n, p, w))

def ws.shr(+n: Nat, k: Nat, w: Word(n)) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+ +p:
      Word.shr(n, ws.shr(n, p, w))

# the bit Word.shl.put(n, c, w) shifts out at the top, and Word.shl's
def ws.topc(n: Nat, c: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      c
    case 1n+ +p:
      match w:
        case WCon{b, t}:
          ws.topc(p, b, t)

def ws.top(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+ +p:
      match w:
        case WCon{b, t}:
          ws.topc(p, b, t)

# the bits ws.shl(n, k, w) carries out, as a number
def ws.ov(+n: Nat, k: Nat, +w: Word(n)) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+ +p:
      Nat.add(U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))), Nat.double(ws.ov(n, p, w)))

def ws.wcon_cong(-p: Nat, -s: Bool, -x: Word(p), -y: Word(p), e: {x == y : Word(p)}) -> {WCon{s, x} == WCon{s, y} : Word(1n+p)}:
  %e : {WCon{s, x} == WCon{s, _} : Word(1n+p)}
  {==}

def ws.wcon_eq(-p: Nat, -x: Bool, -y: Bool, -s: Word(p), -t: Word(p), e1: {x == y : Bool}, e2: {s == t : Word(p)}) -> {WCon{x, s} == WCon{y, t} : Word(1n+p)}:
  %e1 : {WCon{x, s} == WCon{_, t} : Word(1n+p)}
  %e2 : {WCon{x, s} == WCon{x, _} : Word(1n+p)}
  {==}

# a shift left by one bit, a bit c coming in: the doubled value plus c, less
# 2^n for the bit shifted out
def ws.putv(n: Nat, c: Bool, w: Word(n)) -> {Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), U.U32Nat.dbl(n, U.U32Nat.bit(ws.topc(n, c, w)))) == Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(n, w))) : Nat}:
  match n:
    case 0n:
      match c w:
        case False{} WNil{}:
          {==}
        case True{} WNil{}:
          {==}
    case 1n+ +p:
      match c w:
        case False{} WCon{False{}, +t}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), ns.double_add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t)))), Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t))), ws.putv(p, False{}, t)))
        case False{} WCon{True{}, +t}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), ns.double_add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t)))), Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t))), ws.putv(p, True{}, t)))
        case True{} WCon{False{}, +t}:
          P.wn.succ_cong(Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t)))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), ns.double_add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t)))), Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t))), ws.putv(p, False{}, t))))
        case True{} WCon{True{}, +t}:
          P.wn.succ_cong(Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t)))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), ns.double_add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t)))), Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t))), ws.putv(p, True{}, t))))

# Word.shl: the doubled value, less 2^n for the top bit
def ws.shlv(n: Nat, w: Word(n)) -> {Nat.add(Word.to_nat(n, Word.shl(n, w)), U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, w)))) == Nat.double(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), ns.double_add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t))))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(p, Word.shl.put(p, False{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, False{}, t)))), Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, t))), ws.putv(p, False{}, t)))
        case WCon{True{}, +t}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.double(Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), ns.double_add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t))))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(p, Word.shl.put(p, True{}, t)), U.U32Nat.dbl(p, U.U32Nat.bit(ws.topc(p, True{}, t)))), Nat.add(U.U32Nat.bit(True{}), Nat.double(Word.to_nat(p, t))), ws.putv(p, True{}, t)))

# k shifts left: the value times 2^k, less 2^n times the bits carried out
def ws.shlk(+n: Nat, k: Nat, +w: Word(n)) -> {Nat.add(Word.to_nat(n, ws.shl(n, k, w)), U.U32Nat.dbl(n, ws.ov(n, k, w))) == U.U32Nat.dbl(k, Word.to_nat(n, w)) : Nat}:
  match k:
    case 0n:
      ns.d0(n, Word.to_nat(n, w))
    case 1n+ +p:
      Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))), Nat.double(ws.ov(n, p, w))))), Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w)))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w))))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, w))), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), v), U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))), Nat.double(ws.ov(n, p, w)))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w)))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), UL.dbl_add(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))), Nat.double(ws.ov(n, p, w)))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w)))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w))))), Nat.add(Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, w))), Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w)))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w))))), P.wn.add_assoc(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w)))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w))))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), Nat.add(Nat.double(Word.to_nat(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, w))), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), Nat.add(Word.to_nat(n, Word.shl(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, U.U32Nat.bit(ws.top(n, ws.shl(n, p, w))))), Nat.double(Word.to_nat(n, ws.shl(n, p, w))), ws.shlv(n, ws.shl(n, p, w))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(n, ws.shl(n, p, w))), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w)))), Nat.add(Nat.double(Word.to_nat(n, ws.shl(n, p, w))), Nat.double(U.U32Nat.dbl(n, ws.ov(n, p, w)))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, w))), Equal.cong(Nat, Nat, v => Nat.add(Nat.double(Word.to_nat(n, ws.shl(n, p, w))), v), U.U32Nat.dbl(n, Nat.double(ws.ov(n, p, w))), Nat.double(U.U32Nat.dbl(n, ws.ov(n, p, w))), ns.dbl_double(n, ws.ov(n, p, w))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(n, ws.shl(n, p, w))), Nat.double(U.U32Nat.dbl(n, ws.ov(n, p, w)))), Nat.double(Nat.add(Word.to_nat(n, ws.shl(n, p, w)), U.U32Nat.dbl(n, ws.ov(n, p, w)))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, w))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(n, ws.shl(n, p, w)), U.U32Nat.dbl(n, ws.ov(n, p, w)))), Nat.add(Nat.double(Word.to_nat(n, ws.shl(n, p, w))), Nat.double(U.U32Nat.dbl(n, ws.ov(n, p, w)))), ns.double_add(Word.to_nat(n, ws.shl(n, p, w)), U.U32Nat.dbl(n, ws.ov(n, p, w)))), Equal.cong(Nat, Nat, v => Nat.double(v), Nat.add(Word.to_nat(n, ws.shl(n, p, w)), U.U32Nat.dbl(n, ws.ov(n, p, w))), U.U32Nat.dbl(p, Word.to_nat(n, w)), ws.shlk(n, p, w)))))))

# x, y < 2^n and x + 2^n p = y + 2^n q: x = y
def ws.uniq(+n: Nat, p: Nat, q: Nat, +x: Nat, +y: Nat, e: {Nat.add(x, U.U32Nat.dbl(n, p)) == Nat.add(y, U.U32Nat.dbl(n, q)) : Nat}, hx: {Nat.is_lt(x, U.U32Nat.dbl(n, 1n)) == True{} : Bool}, hy: {Nat.is_lt(y, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {x == y : Nat}:
  match p q:
    case 0n 0n:
      Equal.trans(Nat, x, Nat.add(x, U.U32Nat.dbl(n, 0n)), y, Equal.sym(Nat, Nat.add(x, U.U32Nat.dbl(n, 0n)), x, ns.d0(n, x)), Equal.trans(Nat, Nat.add(x, U.U32Nat.dbl(n, 0n)), Nat.add(y, U.U32Nat.dbl(n, 0n)), y, e, ns.d0(n, y)))
    case 0n 1n+ +q:
      Empty.absurd({x == y : Nat}, P.wn.lt_irrefl(x, P.wn.lt_rw2(x, Nat.add(y, U.U32Nat.dbl(n, 1n+q)), x, Equal.trans(Nat, Nat.add(y, U.U32Nat.dbl(n, 1n+q)), Nat.add(x, U.U32Nat.dbl(n, 0n)), x, Equal.sym(Nat, Nat.add(x, U.U32Nat.dbl(n, 0n)), Nat.add(y, U.U32Nat.dbl(n, 1n+q)), e), ns.d0(n, x)), P.wn.lt_le_trans(x, U.U32Nat.dbl(n, 1n+q), Nat.add(y, U.U32Nat.dbl(n, 1n+q)), P.wn.lt_le_trans(x, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, 1n+q), hx, Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, 1n+q)), Nat.is_le(1n, 1n+q), True{}, UL.dbl_le(n, 1n, 1n+q), P.wn.le_zero(q))), P.wn.le_add_self(U.U32Nat.dbl(n, 1n+q), y)))))
    case 1n+ +p 0n:
      Empty.absurd({x == y : Nat}, P.wn.lt_irrefl(y, P.wn.lt_rw2(y, Nat.add(x, U.U32Nat.dbl(n, 1n+p)), y, Equal.trans(Nat, Nat.add(x, U.U32Nat.dbl(n, 1n+p)), Nat.add(y, U.U32Nat.dbl(n, 0n)), y, e, ns.d0(n, y)), P.wn.lt_le_trans(y, U.U32Nat.dbl(n, 1n+p), Nat.add(x, U.U32Nat.dbl(n, 1n+p)), P.wn.lt_le_trans(y, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, 1n+p), hy, Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, 1n+p)), Nat.is_le(1n, 1n+p), True{}, UL.dbl_le(n, 1n, 1n+p), P.wn.le_zero(p))), P.wn.le_add_self(U.U32Nat.dbl(n, 1n+p), x)))))
    case 1n+ +p 1n+ +q:
      ws.uniq(n, p, q, x, y, ns.add_cancel_l(U.U32Nat.dbl(n, 1n), Nat.add(x, U.U32Nat.dbl(n, p)), Nat.add(y, U.U32Nat.dbl(n, q)), Equal.trans(Nat, Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(x, U.U32Nat.dbl(n, p))), Nat.add(x, Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p))), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(y, U.U32Nat.dbl(n, q))), P.wn.left_comm(U.U32Nat.dbl(n, 1n), x, U.U32Nat.dbl(n, p)), Equal.trans(Nat, Nat.add(x, Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p))), Nat.add(x, U.U32Nat.dbl(n, 1n+p)), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(y, U.U32Nat.dbl(n, q))), Equal.cong(Nat, Nat, v => Nat.add(x, v), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p)), U.U32Nat.dbl(n, 1n+p), Equal.sym(Nat, U.U32Nat.dbl(n, 1n+p), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p)), UL.dbl_add(n, 1n, p))), Equal.trans(Nat, Nat.add(x, U.U32Nat.dbl(n, 1n+p)), Nat.add(y, U.U32Nat.dbl(n, 1n+q)), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(y, U.U32Nat.dbl(n, q))), e, Equal.trans(Nat, Nat.add(y, U.U32Nat.dbl(n, 1n+q)), Nat.add(y, Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, q))), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(y, U.U32Nat.dbl(n, q))), Equal.cong(Nat, Nat, v => Nat.add(y, v), U.U32Nat.dbl(n, 1n+q), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, q)), UL.dbl_add(n, 1n, q)), P.wn.left_comm(y, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, q))))))), hx, hy)

# k shifts right: the floor of the value divided by 2^k
def ws.shr_le(+n: Nat, j: Nat, +w: Word(n)) -> {Nat.is_le(U.U32Nat.dbl(j, Word.to_nat(n, ws.shr(n, j, w))), Word.to_nat(n, w)) == True{} : Bool}:
  match j:
    case 0n:
      P.wn.le_refl(Word.to_nat(n, w))
    case 1n+ +p:
      +e1 = Equal.trans(Nat, Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), U.U32Nat.dbl(p, Nat.double(Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), U.U32Nat.dbl(p, Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Equal.sym(Nat, U.U32Nat.dbl(p, Nat.double(Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), ns.dbl_double(p, Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(p, Nat.double(v)), Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))), U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))), UL.word_shr_value(n, ws.shr(n, p, w))))
      +l1 = Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(p, Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), U.U32Nat.dbl(p, Word.to_nat(n, ws.shr(n, p, w)))), Nat.is_le(Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w)))), Word.to_nat(n, ws.shr(n, p, w))), True{}, UL.dbl_le(p, Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w)))), Word.to_nat(n, ws.shr(n, p, w))), ns.half_le(Word.to_nat(n, ws.shr(n, p, w))))
      P.wn.le_rw(U.U32Nat.dbl(p, Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), Word.to_nat(n, w), Equal.sym(Nat, Nat.double(U.U32Nat.dbl(p, Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), U.U32Nat.dbl(p, Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), e1), P.wn.le_trans(U.U32Nat.dbl(p, Nat.double(U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), U.U32Nat.dbl(p, Word.to_nat(n, ws.shr(n, p, w))), Word.to_nat(n, w), l1, ws.shr_le(n, p, w)))

def ws.shr_lt(+n: Nat, j: Nat, +w: Word(n)) -> {Nat.is_lt(Word.to_nat(n, w), U.U32Nat.dbl(j, 1n+Word.to_nat(n, ws.shr(n, j, w)))) == True{} : Bool}:
  match j:
    case 0n:
      ns.lt_succ_self(Word.to_nat(n, w))
    case 1n+ +p:
      +e2 = Equal.trans(Nat, U.U32Nat.dbl(p, Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Nat.double(U.U32Nat.dbl(p, 1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Nat.double(U.U32Nat.dbl(p, 1n+Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), ns.dbl_double(p, 1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w)))), Equal.cong(Nat, Nat, v => Nat.double(U.U32Nat.dbl(p, 1n+v)), U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))), Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))), Equal.sym(Nat, Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))), U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))), UL.word_shr_value(n, ws.shr(n, p, w)))))
      +l2 = Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(p, 1n+Word.to_nat(n, ws.shr(n, p, w))), U.U32Nat.dbl(p, Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w)))))), Nat.is_le(1n+Word.to_nat(n, ws.shr(n, p, w)), Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), True{}, UL.dbl_le(p, 1n+Word.to_nat(n, ws.shr(n, p, w)), Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Equal.trans(Bool, Nat.is_le(1n+Word.to_nat(n, ws.shr(n, p, w)), Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Nat.is_lt(Word.to_nat(n, ws.shr(n, p, w)), Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), True{}, P.wn.le_succ(Word.to_nat(n, ws.shr(n, p, w)), Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), ns.half_lt(Word.to_nat(n, ws.shr(n, p, w)))))
      P.wn.lt_le_trans(Word.to_nat(n, w), U.U32Nat.dbl(p, 1n+Word.to_nat(n, ws.shr(n, p, w))), Nat.double(U.U32Nat.dbl(p, 1n+Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), ws.shr_lt(n, p, w), P.wn.le_rw2(U.U32Nat.dbl(p, 1n+Word.to_nat(n, ws.shr(n, p, w))), U.U32Nat.dbl(p, Nat.double(1n+U.U32Nat.half(Word.to_nat(n, ws.shr(n, p, w))))), Nat.double(U.U32Nat.dbl(p, 1n+Word.to_nat(n, Word.shr(n, ws.shr(n, p, w))))), e2, l2))

# or: commutes, has 0 as unit, and adds two words whose bits do not meet

def ws.bor_comm(x: Bool, y: Bool) -> {Bool.or(x, y) == Bool.or(y, x) : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def ws.or_comm(n: Nat, a: Word(n), b: Word(n)) -> {Word.or(n, a, b) == Word.or(n, b, a) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          ws.wcon_eq(p, Bool.or(x, y), Bool.or(y, x), Word.or(p, at, bt), Word.or(p, bt, at), ws.bor_comm(x, y), ws.or_comm(p, at, bt))

def ws.or_zero(n: Nat, w: Word(n)) -> {Word.or(n, w, Word.zero(n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          ws.wcon_cong(p, False{}, Word.or(p, t, Word.zero(p)), t, ws.or_zero(p, t))
        case WCon{True{}, +t}:
          ws.wcon_cong(p, True{}, Word.or(p, t, Word.zero(p)), t, ws.or_zero(p, t))

# x's value a multiple of 2^k and y's below 2^k: or(x, y) is x + y
def ws.or_dis(n: Nat, k: Nat, +x: Word(n), +y: Word(n), +q: Nat, ex: {Word.to_nat(n, x) == U.U32Nat.dbl(k, q) : Nat}, hy: {Nat.is_lt(Word.to_nat(n, y), U.U32Nat.dbl(k, 1n)) == True{} : Bool}) -> {Word.to_nat(n, Word.or(n, x, y)) == Nat.add(Word.to_nat(n, x), Word.to_nat(n, y)) : Nat}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match k:
        case 0n:
          +y0 = ns.lt_one(Word.to_nat(1n+p, y), hy)
          +ey = UL.word_value_eq(1n+p, y, Word.zero(1n+p), Equal.trans(Nat, Word.to_nat(1n+p, y), 0n, Word.to_nat(1n+p, Word.zero(1n+p)), y0, Equal.sym(Nat, Word.to_nat(1n+p, Word.zero(1n+p)), 0n, UL.word_zero_value(1n+p))))
          Equal.trans(Nat, Word.to_nat(1n+p, Word.or(1n+p, x, y)), Word.to_nat(1n+p, Word.or(1n+p, x, Word.zero(1n+p))), Nat.add(Word.to_nat(1n+p, x), Word.to_nat(1n+p, y)), Equal.cong(Word(1n+p), Nat, v => Word.to_nat(1n+p, Word.or(1n+p, x, v)), y, Word.zero(1n+p), ey), Equal.trans(Nat, Word.to_nat(1n+p, Word.or(1n+p, x, Word.zero(1n+p))), Word.to_nat(1n+p, x), Nat.add(Word.to_nat(1n+p, x), Word.to_nat(1n+p, y)), Equal.cong(Word(1n+p), Nat, v => Word.to_nat(1n+p, v), Word.or(1n+p, x, Word.zero(1n+p)), x, ws.or_zero(1n+p, x)), Equal.trans(Nat, Word.to_nat(1n+p, x), Nat.add(Word.to_nat(1n+p, x), 0n), Nat.add(Word.to_nat(1n+p, x), Word.to_nat(1n+p, y)), Equal.sym(Nat, Nat.add(Word.to_nat(1n+p, x), 0n), Word.to_nat(1n+p, x), P.wn.add_zero(Word.to_nat(1n+p, x))), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(1n+p, x), v), 0n, Word.to_nat(1n+p, y), Equal.sym(Nat, Word.to_nat(1n+p, y), 0n, y0)))))
        case 1n+ +j:
          match x y:
            case WCon{False{}, +xt} WCon{False{}, +yt}:
              Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.or(p, xt, yt))), Nat.double(Nat.add(Word.to_nat(p, xt), Word.to_nat(p, yt))), Nat.add(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))), Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(p, Word.or(p, xt, yt)), Nat.add(Word.to_nat(p, xt), Word.to_nat(p, yt)), ws.or_dis(p, j, xt, yt, q, ns.double_inj(Word.to_nat(p, xt), U.U32Nat.dbl(j, q), ex), Equal.trans(Bool, Nat.is_lt(Word.to_nat(p, yt), U.U32Nat.dbl(j, 1n)), Nat.is_lt(Nat.double(Word.to_nat(p, yt)), Nat.double(U.U32Nat.dbl(j, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(Word.to_nat(p, yt)), Nat.double(U.U32Nat.dbl(j, 1n))), Nat.is_lt(Word.to_nat(p, yt), U.U32Nat.dbl(j, 1n)), ns.lt_dbl(Word.to_nat(p, yt), U.U32Nat.dbl(j, 1n))), hy))), ns.double_add(Word.to_nat(p, xt), Word.to_nat(p, yt)))
            case WCon{False{}, +xt} WCon{True{}, +yt}:
              Equal.trans(Nat, 1n+Nat.double(Word.to_nat(p, Word.or(p, xt, yt))), 1n+Nat.add(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))), Nat.add(Nat.double(Word.to_nat(p, xt)), 1n+Nat.double(Word.to_nat(p, yt))), P.wn.succ_cong(Nat.double(Word.to_nat(p, Word.or(p, xt, yt))), Nat.add(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))), Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.or(p, xt, yt))), Nat.double(Nat.add(Word.to_nat(p, xt), Word.to_nat(p, yt))), Nat.add(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))), Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(p, Word.or(p, xt, yt)), Nat.add(Word.to_nat(p, xt), Word.to_nat(p, yt)), ws.or_dis(p, j, xt, yt, q, ns.double_inj(Word.to_nat(p, xt), U.U32Nat.dbl(j, q), ex), Equal.trans(Bool, Nat.is_lt(Word.to_nat(p, yt), U.U32Nat.dbl(j, 1n)), Nat.is_lt(1n+Nat.double(Word.to_nat(p, yt)), Nat.double(U.U32Nat.dbl(j, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(1n+Nat.double(Word.to_nat(p, yt)), Nat.double(U.U32Nat.dbl(j, 1n))), Nat.is_lt(Word.to_nat(p, yt), U.U32Nat.dbl(j, 1n)), ns.lt_dbl1(Word.to_nat(p, yt), U.U32Nat.dbl(j, 1n))), hy))), ns.double_add(Word.to_nat(p, xt), Word.to_nat(p, yt)))), Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(p, xt)), 1n+Nat.double(Word.to_nat(p, yt))), 1n+Nat.add(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt))), P.wn.add_succ(Nat.double(Word.to_nat(p, xt)), Nat.double(Word.to_nat(p, yt)))))
            case WCon{True{}, +xt} WCon{False{}, +yt}:
              Empty.absurd({Word.to_nat(1n+p, Word.or(1n+p, WCon{True{}, xt}, WCon{False{}, yt})) == Nat.add(Word.to_nat(1n+p, WCon{True{}, xt}), Word.to_nat(1n+p, WCon{False{}, yt})) : Nat}, ns.odd_even(Word.to_nat(p, xt), U.U32Nat.dbl(j, q), ex))
            case WCon{True{}, +xt} WCon{True{}, +yt}:
              Empty.absurd({Word.to_nat(1n+p, Word.or(1n+p, WCon{True{}, xt}, WCon{True{}, yt})) == Nat.add(Word.to_nat(1n+p, WCon{True{}, xt}), Word.to_nat(1n+p, WCon{True{}, yt})) : Nat}, ns.odd_even(Word.to_nat(p, xt), U.U32Nat.dbl(j, q), ex))

# The bits a shift left by k carries out are the shift right by n - k:
# 2^k * w = shl(w, k) + 2^n * shr(w, n - k), and shl(w, k) is 2^k times
# the remainder of w by 2^(n - k)
def ws.g1w(+n: Nat, +k: Nat, +w: Word(n), hk: {Nat.is_le(k, n) == True{} : Bool}) -> {U.U32Nat.dbl(k, Word.to_nat(n, w)) == Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))) : Nat}:
  +er = ns.sub_add_le(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))), ws.shr_le(n, Nat.sub(n, k), w))
  Equal.trans(Nat, U.U32Nat.dbl(k, Word.to_nat(n, w)), U.U32Nat.dbl(k, Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, v), Word.to_nat(n, w), Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Equal.sym(Nat, Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Word.to_nat(n, w), er)), Equal.trans(Nat, U.U32Nat.dbl(k, Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), UL.dbl_add(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Equal.cong(Nat, Nat, v => Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), v), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))), ns.dkm(n, k, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)), hk))))

def ws.g1a(+n: Nat, +k: Nat, +w: Word(n), +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {Word.to_nat(n, ws.shl(n, k, w)) == U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))) : Nat}:
  +er = ns.sub_add_le(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))), ws.shr_le(n, Nat.sub(n, k), w))
  +h1 = P.wn.lt_rw(Word.to_nat(n, w), Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))), Equal.sym(Nat, Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Word.to_nat(n, w), er), ws.shr_lt(n, Nat.sub(n, k), w))
  +h2 = P.wn.lt_rw2(Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))), Nat.add(U.U32Nat.dbl(Nat.sub(n, k), 1n), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), UL.dbl_add(Nat.sub(n, k), 1n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))), h1)
  +hr = Equal.trans(Bool, Nat.is_lt(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n)), Nat.is_lt(Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Nat.add(U.U32Nat.dbl(Nat.sub(n, k), 1n), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Nat.add(U.U32Nat.dbl(Nat.sub(n, k), 1n), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), Nat.is_lt(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n)), P.wn.lt_add_r(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), h2)
  +hrk = P.wn.lt_rw2(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n)), U.U32Nat.dbl(n, 1n), ns.dkm(n, k, 1n, hk), Equal.trans(Bool, Nat.is_lt(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n))), Nat.is_lt(Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n)), True{}, UL.dbl_lt(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(Nat.sub(n, k), 1n)), hr))
  ws.uniq(n, ws.ov(n, k, w), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)), Word.to_nat(n, ws.shl(n, k, w)), U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, w)), U.U32Nat.dbl(n, ws.ov(n, k, w))), U.U32Nat.dbl(k, Word.to_nat(n, w)), Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), ws.shlk(n, k, w), ws.g1w(n, k, w, hk)), UL.word_value_lt(n, ws.shl(n, k, w)), hrk)

def ws.g1b(+n: Nat, +k: Nat, +w: Word(n), +hk: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.add(Word.to_nat(n, ws.shl(n, k, w)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))) == U.U32Nat.dbl(k, Word.to_nat(n, w)) : Nat}:
  Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, w)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), U.U32Nat.dbl(k, Word.to_nat(n, w)), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), Word.to_nat(n, ws.shl(n, k, w)), U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), ws.g1a(n, k, w, hk)), Equal.sym(Nat, U.U32Nat.dbl(k, Word.to_nat(n, w)), Nat.add(U.U32Nat.dbl(k, Nat.sub(Word.to_nat(n, w), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w))))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), w)))), ws.g1w(n, k, w, hk)))

# The shifts across the halves, at width n

# 2^k * (lo + 2^n hi) = 2^k lo + 2^n (2^k hi)
def ws.ea(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n)) -> {U.U32Nat.dbl(k, P.wv.V(n, hw, lw)) == Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)))) : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(k, Nat.add(Word.to_nat(n, lw), U.U32Nat.dbl(n, Word.to_nat(n, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(k, U.U32Nat.dbl(n, Word.to_nat(n, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)))), UL.dbl_add(k, Word.to_nat(n, lw), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Equal.cong(Nat, Nat, v => Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), v), U.U32Nat.dbl(k, U.U32Nat.dbl(n, Word.to_nat(n, hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), ns.dbl_comm(k, n, Word.to_nat(n, hw))))

def ws.hb(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +ch: Word(n), +cl: Word(n), h: {Nat.is_le(U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), P.wv.V(n, ch, cl)) == True{} : Bool}) -> {Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), P.wv.Q(n, 1n)) == True{} : Bool}:
  +hc = P.wv.val_lt2(n, Word.to_nat(n, cl), Word.to_nat(n, ch), UL.word_value_lt(n, cl), UL.word_value_lt(n, ch))
  +l1 = P.wn.le_rw2(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.sym(Nat, U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)))), ws.ea(n, k, hw, lw)), P.wn.le_add_self(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), U.U32Nat.dbl(k, Word.to_nat(n, lw))))
  P.wn.le_lt_trans(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), P.wv.Q(n, 1n), l1, P.wn.le_lt_trans(U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), P.wv.V(n, ch, cl), P.wv.Q(n, 1n), h, hc))

# a shift left by k < n: the high half takes the low half's top k bits
def ws.gshl_lo(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +ch: Word(n), +cl: Word(n), hk: {Nat.is_lt(k, n) == True{} : Bool}, h: {Nat.is_le(U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), P.wv.V(n, ch, cl)) == True{} : Bool}) -> {P.wv.V(n, Word.or(n, ws.shl(n, k, hw), ws.shr(n, Nat.sub(n, k), lw)), ws.shl(n, k, lw)) == U.U32Nat.dbl(k, P.wv.V(n, hw, lw)) : Nat}:
  +hkle = P.wn.lt_le(k, n, hk)
  +hb = Equal.trans(Bool, Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(n, 1n)), Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(n, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(n, 1n))), Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(n, 1n)), UL.dbl_lt(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(n, 1n))), ws.hb(n, k, hw, lw, ch, cl, h))
  +exh = ws.uniq(n, ws.ov(n, k, hw), 0n, Word.to_nat(n, ws.shl(n, k, hw)), U.U32Nat.dbl(k, Word.to_nat(n, hw)), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, hw)), U.U32Nat.dbl(n, ws.ov(n, k, hw))), U.U32Nat.dbl(k, Word.to_nat(n, hw)), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(n, 0n)), ws.shlk(n, k, hw), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(n, 0n)), U.U32Nat.dbl(k, Word.to_nat(n, hw)), ns.d0(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))))), UL.word_value_lt(n, ws.shl(n, k, hw)), hb)
  +l3 = P.wn.le_lt_trans(U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), Word.to_nat(n, lw), U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, 1n)), ws.shr_le(n, Nat.sub(n, k), lw), P.wn.lt_rw2(Word.to_nat(n, lw), U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, 1n)), Equal.sym(Nat, U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, 1n)), U.U32Nat.dbl(n, 1n), ns.dmk(n, k, 1n, hkle)), UL.word_value_lt(n, lw)))
  +hs = Equal.trans(Bool, Nat.is_lt(Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)), U.U32Nat.dbl(k, 1n)), Nat.is_lt(U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(Nat.sub(n, k), U.U32Nat.dbl(k, 1n))), Nat.is_lt(Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)), U.U32Nat.dbl(k, 1n)), UL.dbl_lt(Nat.sub(n, k), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)), U.U32Nat.dbl(k, 1n))), l3)
  +ehi = ws.or_dis(n, k, ws.shl(n, k, hw), ws.shr(n, Nat.sub(n, k), lw), Word.to_nat(n, hw), exh, hs)
  Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Word.to_nat(n, Word.or(n, ws.shl(n, k, hw), ws.shr(n, Nat.sub(n, k), lw))))), Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Nat.add(Word.to_nat(n, ws.shl(n, k, hw)), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, v)), Word.to_nat(n, Word.or(n, ws.shl(n, k, hw), ws.shr(n, Nat.sub(n, k), lw))), Nat.add(Word.to_nat(n, ws.shl(n, k, hw)), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), ehi), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Nat.add(Word.to_nat(n, ws.shl(n, k, hw)), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))))), Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), v), U.U32Nat.dbl(n, Nat.add(Word.to_nat(n, ws.shl(n, k, hw)), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), UL.dbl_add(n, Word.to_nat(n, ws.shl(n, k, hw)), Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))))), Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), v), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), P.wn.add_comm(U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))))), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))))), Nat.add(Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), Nat.add(U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))))), P.wn.add_assoc(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw))))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), Nat.add(Word.to_nat(n, ws.shl(n, k, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, k), lw)))), U.U32Nat.dbl(k, Word.to_nat(n, lw)), ws.g1b(n, k, lw, hkle)), Equal.trans(Nat, Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, k, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, v)), Word.to_nat(n, ws.shl(n, k, hw)), U.U32Nat.dbl(k, Word.to_nat(n, hw)), exh), Equal.sym(Nat, U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)))), ws.ea(n, k, hw, lw))))))))

# a shift left by n <= k: the high half is the low half shifted by k - n, the
# high half's bits all carried out (and 0, if nothing overflows)
def ws.gshl_hi(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +ch: Word(n), +cl: Word(n), +h1: {Nat.is_le(n, k) == True{} : Bool}, +h: {Nat.is_le(U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), P.wv.V(n, ch, cl)) == True{} : Bool}) -> {P.wv.V(n, ws.shl(n, Nat.sub(k, n), lw), Word.zero(n)) == U.U32Nat.dbl(k, P.wv.V(n, hw, lw)) : Nat}:
  +dk1 = Equal.sym(Nat, U.U32Nat.dbl(k, 1n), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n)), ns.dnj(n, k, 1n, h1))
  +l3a = P.wn.le_rw2(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n)), U.U32Nat.dbl(k, 1n), dk1, Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n))), Nat.is_le(1n, U.U32Nat.dbl(Nat.sub(k, n), 1n)), True{}, UL.dbl_le(n, 1n, U.U32Nat.dbl(Nat.sub(k, n), 1n)), ns.dbl_ge(Nat.sub(k, n), 1n)))
  +l3 = Equal.trans(Bool, Nat.is_le(P.wv.Q(n, 1n), U.U32Nat.dbl(n, U.U32Nat.dbl(k, 1n))), Nat.is_le(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(k, 1n)), True{}, UL.dbl_le(n, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(k, 1n)), l3a)
  +l4 = P.wn.lt_le_trans(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), P.wv.Q(n, 1n), U.U32Nat.dbl(n, U.U32Nat.dbl(k, 1n)), ws.hb(n, k, hw, lw, ch, cl, h), l3)
  +l5 = Equal.trans(Bool, Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(k, 1n)), Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(k, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(k, Word.to_nat(n, hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(k, 1n))), Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(k, 1n)), UL.dbl_lt(n, U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(k, 1n))), l4)
  +l6 = Equal.trans(Bool, Nat.is_lt(Word.to_nat(n, hw), 1n), Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(k, 1n)), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, hw)), U.U32Nat.dbl(k, 1n)), Nat.is_lt(Word.to_nat(n, hw), 1n), UL.dbl_lt(k, Word.to_nat(n, hw), 1n)), l5)
  +eh = ns.lt_one(Word.to_nat(n, hw), l6)
  +eal = Equal.trans(Nat, P.wv.V(n, hw, lw), Nat.add(Word.to_nat(n, lw), U.U32Nat.dbl(n, 0n)), Word.to_nat(n, lw), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, lw), U.U32Nat.dbl(n, v)), Word.to_nat(n, hw), 0n, eh), ns.d0(n, Word.to_nat(n, lw)))
  +hc = P.wv.val_lt2(n, Word.to_nat(n, cl), Word.to_nat(n, ch), UL.word_value_lt(n, cl), UL.word_value_lt(n, ch))
  +m1 = P.wn.lt_rw(U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), U.U32Nat.dbl(k, Word.to_nat(n, lw)), P.wv.Q(n, 1n), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, v), P.wv.V(n, hw, lw), Word.to_nat(n, lw), eal), P.wn.le_lt_trans(U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), P.wv.V(n, ch, cl), P.wv.Q(n, 1n), h, hc))
  +m2 = P.wn.lt_rw(U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))), P.wv.Q(n, 1n), ns.dnj(n, k, Word.to_nat(n, lw), h1), m1)
  +m3 = Equal.trans(Bool, Nat.is_lt(U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), U.U32Nat.dbl(n, 1n)), Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))), U.U32Nat.dbl(n, U.U32Nat.dbl(n, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))), U.U32Nat.dbl(n, U.U32Nat.dbl(n, 1n))), Nat.is_lt(U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), U.U32Nat.dbl(n, 1n)), UL.dbl_lt(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), U.U32Nat.dbl(n, 1n))), m2)
  +exj = ws.uniq(n, ws.ov(n, Nat.sub(k, n), lw), 0n, Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)), U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)), U.U32Nat.dbl(n, ws.ov(n, Nat.sub(k, n), lw))), U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), Nat.add(U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), U.U32Nat.dbl(n, 0n)), ws.shlk(n, Nat.sub(k, n), lw), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), U.U32Nat.dbl(n, 0n)), U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), ns.d0(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))))), UL.word_value_lt(n, ws.shl(n, Nat.sub(k, n), lw)), m3)
  Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.zero(n)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)))), Nat.add(0n, U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)))), Word.to_nat(n, Word.zero(n)), 0n, UL.word_zero_value(n)), Equal.trans(Nat, Nat.add(0n, U.U32Nat.dbl(n, Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)))), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(n, v), Word.to_nat(n, ws.shl(n, Nat.sub(k, n), lw)), U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw)), exj), Equal.trans(Nat, U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))), U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(k, P.wv.V(n, hw, lw)), Equal.sym(Nat, U.U32Nat.dbl(k, Word.to_nat(n, lw)), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, lw))), ns.dnj(n, k, Word.to_nat(n, lw), h1)), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, v), Word.to_nat(n, lw), P.wv.V(n, hw, lw), Equal.sym(Nat, P.wv.V(n, hw, lw), Word.to_nat(n, lw), eal)))))

# a shift right by k < n: the low half takes the high half's low k bits
def ws.gshr_v(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), hk: {Nat.is_lt(k, n) == True{} : Bool}) -> {P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))) == Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))) : Nat}:
  +hkle = P.wn.lt_le(k, n, hk)
  +hmle = ns.sub_le(n, k)
  +es = Equal.cong(Nat, Nat, v => Word.to_nat(n, ws.shr(n, v, hw)), Nat.sub(n, Nat.sub(n, k)), k, ns.sub_sub(k, n, hkle))
  +l3 = P.wn.le_lt_trans(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), Word.to_nat(n, lw), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n)), ws.shr_le(n, k, lw), P.wn.lt_rw2(Word.to_nat(n, lw), U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n)), Equal.sym(Nat, U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n)), U.U32Nat.dbl(n, 1n), ns.dkm(n, k, 1n, hkle)), UL.word_value_lt(n, lw)))
  +hy = Equal.trans(Bool, Nat.is_lt(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), 1n)), Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), 1n))), Nat.is_lt(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), 1n)), UL.dbl_lt(k, Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), 1n))), l3)
  +eor = Equal.trans(Nat, Word.to_nat(n, Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), Word.to_nat(n, Word.or(n, ws.shl(n, Nat.sub(n, k), hw), ws.shr(n, k, lw))), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), Word.to_nat(n, ws.shr(n, k, lw))), Equal.cong(Word(n), Nat, v => Word.to_nat(n, v), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)), Word.or(n, ws.shl(n, Nat.sub(n, k), hw), ws.shr(n, k, lw)), ws.or_comm(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), ws.or_dis(n, Nat.sub(n, k), ws.shl(n, Nat.sub(n, k), hw), ws.shr(n, k, lw), Nat.sub(Word.to_nat(n, hw), U.U32Nat.dbl(Nat.sub(n, Nat.sub(n, k)), Word.to_nat(n, ws.shr(n, Nat.sub(n, Nat.sub(n, k)), hw)))), ws.g1a(n, Nat.sub(n, k), hw, hmle), hy))
  Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Nat.add(Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Word.to_nat(n, Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), Word.to_nat(n, ws.shr(n, k, lw))), eor), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Nat.add(Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), Word.to_nat(n, ws.shr(n, k, lw))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw))), P.wn.add_comm(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), Word.to_nat(n, ws.shr(n, k, lw)))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw))), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw))))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), P.wn.add_assoc(Word.to_nat(n, ws.shr(n, k, lw)), Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw)))), Equal.trans(Nat, Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, k, hw))))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, Nat.sub(n, k)), hw))))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), U.U32Nat.dbl(n, v))), Word.to_nat(n, ws.shr(n, k, hw)), Word.to_nat(n, ws.shr(n, Nat.sub(n, Nat.sub(n, k)), hw)), Equal.sym(Nat, Word.to_nat(n, ws.shr(n, Nat.sub(n, Nat.sub(n, k)), hw)), Word.to_nat(n, ws.shr(n, k, hw)), es)), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), v), Nat.add(Word.to_nat(n, ws.shl(n, Nat.sub(n, k), hw)), U.U32Nat.dbl(n, Word.to_nat(n, ws.shr(n, Nat.sub(n, Nat.sub(n, k)), hw)))), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)), ws.g1b(n, Nat.sub(n, k), hw, hmle))))))

def ws.gshr_lo_le(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> {Nat.is_le(U.U32Nat.dbl(k, P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), P.wv.V(n, hw, lw)) == True{} : Bool}:
  +hkle = P.wn.lt_le(k, n, hk)
  +e = Equal.trans(Nat, U.U32Nat.dbl(k, P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), U.U32Nat.dbl(k, Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, v), P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), ws.gshr_v(n, k, hw, lw, hk)), Equal.trans(Nat, U.U32Nat.dbl(k, Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), UL.dbl_add(k, Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), Equal.cong(Nat, Nat, v => Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), v), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), U.U32Nat.dbl(n, Word.to_nat(n, hw)), ns.dkm(n, k, Word.to_nat(n, hw), hkle))))
  P.wn.le_rw(Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), U.U32Nat.dbl(k, P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), P.wv.V(n, hw, lw), Equal.sym(Nat, U.U32Nat.dbl(k, P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), Nat.add(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), e), ns.le_add_mono_r(U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, k, lw))), Word.to_nat(n, lw), U.U32Nat.dbl(n, Word.to_nat(n, hw)), ws.shr_le(n, k, lw)))

def ws.gshr_lo_lt(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +hk: {Nat.is_lt(k, n) == True{} : Bool}) -> {Nat.is_lt(P.wv.V(n, hw, lw), U.U32Nat.dbl(k, 1n+P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))))) == True{} : Bool}:
  +hkle = P.wn.lt_le(k, n, hk)
  +s1 = Equal.trans(Bool, Nat.is_lt(Nat.add(Word.to_nat(n, lw), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw)))), Nat.is_lt(Word.to_nat(n, lw), U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw)))), True{}, P.wn.lt_add_r(Word.to_nat(n, lw), U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), ws.shr_lt(n, k, lw))
  +e = Equal.trans(Nat, Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), U.U32Nat.dbl(k, 1n+P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), Equal.cong(Nat, Nat, v => Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), v), U.U32Nat.dbl(n, Word.to_nat(n, hw)), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), Equal.sym(Nat, U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), U.U32Nat.dbl(n, Word.to_nat(n, hw)), ns.dkm(n, k, Word.to_nat(n, hw), hkle))), Equal.trans(Nat, Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), U.U32Nat.dbl(k, Nat.add(1n+Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), U.U32Nat.dbl(k, 1n+P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), Equal.sym(Nat, U.U32Nat.dbl(k, Nat.add(1n+Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(k, U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), UL.dbl_add(k, 1n+Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw)))), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, 1n+v), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), Equal.sym(Nat, P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw))), Nat.add(Word.to_nat(n, ws.shr(n, k, lw)), U.U32Nat.dbl(Nat.sub(n, k), Word.to_nat(n, hw))), ws.gshr_v(n, k, hw, lw, hk)))))
  P.wn.lt_rw2(P.wv.V(n, hw, lw), Nat.add(U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, k, lw))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), U.U32Nat.dbl(k, 1n+P.wv.V(n, ws.shr(n, k, hw), Word.or(n, ws.shr(n, k, lw), ws.shl(n, Nat.sub(n, k), hw)))), e, s1)

# a shift right by n <= k: the low half is the high half shifted by k - n
def ws.gshr_hi_v(+n: Nat, +k: Nat, +hw: Word(n)) -> {P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw)) == Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)) : Nat}:
  Equal.trans(Nat, P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw)), Nat.add(Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), U.U32Nat.dbl(n, 0n)), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), Equal.cong(Nat, Nat, v => Nat.add(Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), U.U32Nat.dbl(n, v)), Word.to_nat(n, Word.zero(n)), 0n, UL.word_zero_value(n)), ns.d0(n, Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))))

def ws.gshr_hi_le(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +h1: {Nat.is_le(n, k) == True{} : Bool}) -> {Nat.is_le(U.U32Nat.dbl(k, P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), P.wv.V(n, hw, lw)) == True{} : Bool}:
  +e = Equal.trans(Nat, U.U32Nat.dbl(k, P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), U.U32Nat.dbl(k, Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, v), P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw)), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), ws.gshr_hi_v(n, k, hw)), ns.dnj(n, k, Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), h1))
  +l1 = Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Nat.is_le(U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))), Word.to_nat(n, hw)), True{}, UL.dbl_le(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))), Word.to_nat(n, hw)), ws.shr_le(n, Nat.sub(k, n), hw))
  P.wn.le_rw(U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), U.U32Nat.dbl(k, P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), P.wv.V(n, hw, lw), Equal.sym(Nat, U.U32Nat.dbl(k, P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), e), P.wn.le_trans(U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), U.U32Nat.dbl(n, Word.to_nat(n, hw)), P.wv.V(n, hw, lw), l1, P.wn.le_add_self(U.U32Nat.dbl(n, Word.to_nat(n, hw)), Word.to_nat(n, lw))))

def ws.gshr_hi_lt(+n: Nat, +k: Nat, +hw: Word(n), +lw: Word(n), +h1: {Nat.is_le(n, k) == True{} : Bool}) -> {Nat.is_lt(P.wv.V(n, hw, lw), U.U32Nat.dbl(k, 1n+P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw)))) == True{} : Bool}:
  +s1 = Equal.trans(Bool, Nat.is_lt(Nat.add(Word.to_nat(n, lw), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, Word.to_nat(n, hw)))), Nat.is_lt(Word.to_nat(n, lw), U.U32Nat.dbl(n, 1n)), True{}, P.wn.lt_add_r(Word.to_nat(n, lw), U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, Word.to_nat(n, hw))), UL.word_value_lt(n, lw))
  +s2 = P.wn.lt_rw2(Nat.add(Word.to_nat(n, lw), U.U32Nat.dbl(n, Word.to_nat(n, hw))), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, Word.to_nat(n, hw))), U.U32Nat.dbl(n, 1n+Word.to_nat(n, hw)), Equal.sym(Nat, U.U32Nat.dbl(n, 1n+Word.to_nat(n, hw)), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, Word.to_nat(n, hw))), UL.dbl_add(n, 1n, Word.to_nat(n, hw))), s1)
  +s3 = Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(n, 1n+Word.to_nat(n, hw)), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))))), Nat.is_le(1n+Word.to_nat(n, hw), U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), True{}, UL.dbl_le(n, 1n+Word.to_nat(n, hw), U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), Equal.trans(Bool, Nat.is_le(1n+Word.to_nat(n, hw), U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), Nat.is_lt(Word.to_nat(n, hw), U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), True{}, P.wn.le_succ(Word.to_nat(n, hw), U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), ws.shr_lt(n, Nat.sub(k, n), hw)))
  +e = Equal.trans(Nat, U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))), U.U32Nat.dbl(k, 1n+P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), Equal.sym(Nat, U.U32Nat.dbl(k, 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw))), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), ns.dnj(n, k, 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), h1)), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(k, 1n+v), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw)), Equal.sym(Nat, P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw)), Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)), ws.gshr_hi_v(n, k, hw))))
  P.wn.lt_le_trans(P.wv.V(n, hw, lw), U.U32Nat.dbl(n, 1n+Word.to_nat(n, hw)), U.U32Nat.dbl(k, 1n+P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), s2, P.wn.le_rw2(U.U32Nat.dbl(n, 1n+Word.to_nat(n, hw)), U.U32Nat.dbl(n, U.U32Nat.dbl(Nat.sub(k, n), 1n+Word.to_nat(n, ws.shr(n, Nat.sub(k, n), hw)))), U.U32Nat.dbl(k, 1n+P.wv.V(n, Word.zero(n), ws.shr(n, Nat.sub(k, n), hw))), e, s3))
