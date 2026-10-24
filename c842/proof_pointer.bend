# Proof helpers for bend-osdev-c842: the pointer rule (pointer.bend) as Nat
# arithmetic.
#
# c842.pointer.pos computes, for an output of n bytes, t8 = n with its low 3
# bits cleared, base = t8 with its low k bits cleared (H = 2^k, the
# history), and p0 = base + s * i. Its value: t8 is 8 times n's high 29
# bits; split at k, t8 is rr + H * B with rr < H, and base is H * B; and
# s * i is the index shifted, i * s, below H. The comparisons are then
# comparisons of those values (bend-osdev-u32's laws), and the three cases
# (p0 below t8; none; p0 - H) give the rule (cp.g_found, cp.g_some).
#
# The word lemmas are stated for widths k and m that are variables, and
# instantiated at the 32 bits of a U32 (3 + 29, 9 + 23, 11 + 21) where every
# term is symbolic. No closed power of two above 2^11 is named.
import Base
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./format.bend as F
import ./pointer.bend as P

# Logic

def cp.bt(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def cp.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : cp.bt(_)
  Unit{}

def cp.absurd(-T: Type, e: Empty) -> T:
  match e:

def cp.true_false(e: {True{} == False{} : Bool}) -> Empty:
  cp.ft(Equal.sym(Bool, True{}, False{}, e))

def cp.mb(m: Maybe<&2, U32>) -> Type:
  match m:
    case Some{x}:
      Unit
    case None{}:
      Empty

def cp.none_some(-p: U32, +e: {None{} == Some{p} : Maybe<&2, U32>}) -> Empty:
  %Equal.sym(Maybe<&2, U32>, None{}, Some{p}, e) : cp.mb(_)
  Unit{}

def cp.some_inj(-a: U32, -b: U32, +e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => Maybe.default(&2, U32, m, 0), Some{a}, Some{b}, e)

# Nat: sums

def cp.succ_cong(-a: Nat, -b: Nat, +e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def cp.add_zero(+x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.succ_cong(Nat.add(p, 0n), p, cp.add_zero(p))

def cp.add_succ(+x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), cp.add_succ(p, y))

def cp.add_comm(+x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, cp.add_zero(y))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), cp.add_succ(y, p)) : {1n+Nat.add(p, y) == _ : Nat}
      cp.succ_cong(Nat.add(p, y), Nat.add(y, p), cp.add_comm(p, y))

def cp.add_assoc(+x: Nat, -y: Nat, -z: Nat) -> {Nat.add(Nat.add(x, y), z) == Nat.add(x, Nat.add(y, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.succ_cong(Nat.add(Nat.add(p, y), z), Nat.add(p, Nat.add(y, z)), cp.add_assoc(p, y, z))

def cp.double_add(+x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), cp.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), cp.double_add(p, y)))

def cp.double_cong(-a: Nat, -b: Nat, +e: {a == b : Nat}) -> {Nat.double(a) == Nat.double(b) : Nat}:
  %e : {Nat.double(a) == Nat.double(_) : Nat}
  {==}

# (h + z) - h = z
def cp.sub_add_l(+h: Nat, +z: Nat) -> {Nat.sub(Nat.add(h, z), h) == z : Nat}:
  match h:
    case 0n:
      match z:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      cp.sub_add_l(p, z)

# Nat: products

# (a + b) c = a c + b c
def cp.mul_add_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), cp.mul_add_r(p, b, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), cp.add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

# (a b) c = a (b c)
def cp.mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %cp.mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      cp.mul_add_r(b, Nat.mul(p, b), c)

# x 2^k = x * (2^k)
def cp.dbl_mul(+k: Nat, +x: Nat) -> {U.U32Nat.dbl(k, x) == Nat.mul(x, U.U32Nat.dbl(k, 1n)) : Nat}:
  match x:
    case 0n:
      UL.dbl_zero(k)
    case 1n+p:
      %cp.dbl_mul(k, p) : {U.U32Nat.dbl(k, 1n+p) == Nat.add(U.U32Nat.dbl(k, 1n), _) : Nat}
      UL.dbl_add(k, 1n, p)

# Nat: order

def cp.lt_add_l(+a: Nat, -x: Nat, -y: Nat) -> {Nat.is_lt(Nat.add(a, x), Nat.add(a, y)) == Nat.is_lt(x, y) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      cp.lt_add_l(p, x, y)

def cp.le_add_l(+a: Nat, -x: Nat, -y: Nat) -> {Nat.is_le(Nat.add(a, x), Nat.add(a, y)) == Nat.is_le(x, y) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      cp.le_add_l(p, x, y)

def cp.not_lt_add(+a: Nat, +b: Nat) -> {Nat.is_lt(Nat.add(a, b), a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      cp.not_lt_add(p, b)

def cp.le_add(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      cp.le_add(p, b)

def cp.le_add_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %cp.add_comm(b, a) : {Nat.is_le(b, _) == True{} : Bool}
  cp.le_add(b, a)

def cp.le_refl(+x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.le_refl(p)

def cp.lt_le(+x: Nat, +y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match y:
        case 0n:
          cp.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, cp.ft(h))
        case 1n+q:
          cp.lt_le(p, q, h)

# x < 1 + y: x <= y
def cp.not_lt_one(+p: Nat, +h: {Nat.is_lt(1n+p, 1n) == True{} : Bool}) -> Empty:
  match p:
    case 0n:
      cp.ft(h)
    case 1n+r:
      cp.ft(h)

def cp.lt_succ_le(+x: Nat, +y: Nat, +h: {Nat.is_lt(x, 1n+y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match y:
        case 0n:
          cp.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, cp.not_lt_one(p, h))
        case 1n+q:
          cp.lt_succ_le(p, q, h)

# x < y: 1 + x <= y
def cp.lt_succ(+x: Nat, +y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(1n+x, y) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          cp.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, cp.ft(h))
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              {==}
    case 1n+p:
      match y:
        case 0n:
          cp.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, cp.ft(h))
        case 1n+q:
          cp.lt_succ(p, q, h)

def cp.le_trans(+x: Nat, +y: Nat, +z: Nat, +h1: {Nat.is_le(x, y) == True{} : Bool}, +h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  match x:
    case 0n:
      match z:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p:
      match y:
        case 0n:
          cp.absurd({Nat.is_le(1n+p, z) == True{} : Bool}, cp.ft(h1))
        case 1n+q:
          match z:
            case 0n:
              cp.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, cp.ft(h2))
            case 1n+r:
              cp.le_trans(p, q, r, h1, h2)

def cp.lt_le_trans(+x: Nat, +y: Nat, +z: Nat, +h1: {Nat.is_lt(x, y) == True{} : Bool}, +h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          cp.absurd({Nat.is_lt(0n, z) == True{} : Bool}, cp.ft(h1))
        case 1n+q:
          match z:
            case 0n:
              cp.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, cp.ft(h2))
            case 1n+r:
              {==}
    case 1n+p:
      match y:
        case 0n:
          cp.absurd({Nat.is_lt(1n+p, z) == True{} : Bool}, cp.ft(h1))
        case 1n+q:
          match z:
            case 0n:
              cp.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, cp.ft(h2))
            case 1n+r:
              cp.lt_le_trans(p, q, r, h1, h2)

# not x < y: y <= x
def cp.le_of_not_lt(+x: Nat, +y: Nat, +e: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          cp.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, cp.true_false(e))
    case 1n+p:
      match y:
        case 0n:
          {==}
        case 1n+q:
          cp.le_of_not_lt(p, q, e)

# x <= y: not y < x
def cp.not_lt_of_le(+x: Nat, +y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_lt(y, x) == False{} : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match y:
        case 0n:
          cp.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, cp.ft(h))
        case 1n+q:
          cp.not_lt_of_le(p, q, h)

# a + c <= b + c from a <= b, the sum on the left
def cp.le_add_mono(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), True{}, cp.le_add_l(c, a, b), h)

# multiples of s: a s < x s gives a s + s <= x s
def cp.step_s(+a: Nat, +x: Nat, +sp: Nat, +h: {Nat.is_lt(Nat.mul(a, 1n+sp), Nat.mul(x, 1n+sp)) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mul(a, 1n+sp), 1n+sp), Nat.mul(x, 1n+sp)) == True{} : Bool}:
  match a:
    case 0n:
      match x:
        case 0n:
          cp.absurd({Nat.is_le(Nat.add(0n, 1n+sp), 0n) == True{} : Bool}, cp.ft(h))
        case 1n+q:
          cp.le_add(1n+sp, Nat.mul(q, 1n+sp))
    case 1n+p:
      match x:
        case 0n:
          cp.absurd({Nat.is_le(Nat.add(Nat.mul(1n+p, 1n+sp), 1n+sp), 0n) == True{} : Bool}, cp.ft(h))
        case 1n+q:
          +mp = Nat.mul(p, 1n+sp)
          +mq = Nat.mul(q, 1n+sp)
          %Equal.sym(Nat, Nat.add(Nat.add(1n+sp, mp), 1n+sp), Nat.add(1n+sp, Nat.add(mp, 1n+sp)), cp.add_assoc(1n+sp, mp, 1n+sp)) : {Nat.is_le(_, Nat.add(1n+sp, mq)) == True{} : Bool}
          %Equal.sym(Bool, Nat.is_le(Nat.add(1n+sp, Nat.add(mp, 1n+sp)), Nat.add(1n+sp, mq)), Nat.is_le(Nat.add(mp, 1n+sp), mq), cp.le_add_l(1n+sp, Nat.add(mp, 1n+sp), mq)) : {_ == True{} : Bool}
          cp.step_s(p, q, sp, Equal.trans(Bool, Nat.is_lt(mp, mq), Nat.is_lt(Nat.add(1n+sp, mp), Nat.add(1n+sp, mq)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(1n+sp, mp), Nat.add(1n+sp, mq)), Nat.is_lt(mp, mq), cp.lt_add_l(1n+sp, mp, mq)), h))

# rewriting under an order

def cp.le_rw(-x: Nat, -x2: Nat, -y: Nat, -y2: Nat, +ex: {x == x2 : Nat}, +ey: {y == y2 : Nat}, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x2, y2) == True{} : Bool}:
  %ex : {Nat.is_le(_, y2) == True{} : Bool}
  %ey : {Nat.is_le(x, _) == True{} : Bool}
  h

def cp.lt_rw(-x: Nat, -x2: Nat, -y: Nat, -y2: Nat, +ex: {x == x2 : Nat}, +ey: {y == y2 : Nat}, +h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y2) == True{} : Bool}:
  %ex : {Nat.is_lt(_, y2) == True{} : Bool}
  %ey : {Nat.is_lt(x, _) == True{} : Bool}
  h

# Nat: division by 1 + bp (Base's Nat.divmod counts m down and r up, and d
# once per round)

def cp.dm_small(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +h: {Nat.is_lt(n, 1n+m) == True{} : Bool}) -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          cp.absurd({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : Nat & Nat}, cp.not_lt_one(np, h))
        case 1n+mp:
          %cp.add_succ(np, r) : {Nat.divmod.go(1n+np, 1n+mp, d, r) == (d, _) : Nat & Nat}
          cp.dm_small(np, mp, d, 1n+r, h)

def cp.dm_round(+m: Nat, +n: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(Nat.add(m, 1n+n), m, d, r) == Nat.divmod.go(n, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      %cp.add_succ(mp, r) : {Nat.divmod.go(Nat.add(1n+mp, 1n+n), 1n+mp, d, r) == Nat.divmod.go(n, _, 1n+d, 0n) : Nat & Nat}
      cp.dm_round(mp, n, d, 1n+r)

def cp.dm_rounds(+g: Nat, +i: Nat, +d: Nat, +bp: Nat, +h: {Nat.is_lt(i, 1n+bp) == True{} : Bool}) -> {Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, d, 0n) == (Nat.add(g, d), i) : Nat & Nat}:
  match g:
    case 0n:
      %cp.add_zero(i) : {Nat.divmod.go(i, bp, d, 0n) == (d, _) : Nat & Nat}
      cp.dm_small(i, bp, d, 0n, h)
    case 1n+gp:
      +gg = Nat.mul(gp, 1n+bp)
      +y = Nat.add(gg, i)
      %Equal.sym(Nat, Nat.add(Nat.add(bp, gg), i), Nat.add(bp, y), cp.add_assoc(bp, gg, i)) : {Nat.divmod.go(1n+_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
      %cp.add_succ(bp, y) : {Nat.divmod.go(_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
      %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(bp, 1n+y), bp, d, 0n), Nat.divmod.go(y, Nat.add(bp, 0n), 1n+d, 0n), cp.dm_round(bp, y, d, 0n)) : {_ == (1n+Nat.add(gp, d), i) : Nat & Nat}
      %Equal.sym(Nat, Nat.add(bp, 0n), bp, cp.add_zero(bp)) : {Nat.divmod.go(y, _, 1n+d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
      %cp.add_succ(gp, d) : {Nat.divmod.go(y, bp, 1n+d, 0n) == (_, i) : Nat & Nat}
      cp.dm_rounds(gp, i, 1n+d, bp, h)

# g (1 + bp) + i, i <= bp: quotient g, remainder i
def cp.div_of(+g: Nat, +i: Nat, +bp: Nat, +h: {Nat.is_lt(i, 1n+bp) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.mul(g, 1n+bp), i), 1n+bp) == g : Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, 0n, 0n), (Nat.add(g, 0n), i), cp.dm_rounds(g, i, 0n, bp, h)) : {Pair.fst(Nat, Nat, _) == g : Nat}
  cp.add_zero(g)

def cp.mod_of(+g: Nat, +i: Nat, +bp: Nat, +h: {Nat.is_lt(i, 1n+bp) == True{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(g, 1n+bp), i), 1n+bp) == i : Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, 0n, 0n), (Nat.add(g, 0n), i), cp.dm_rounds(g, i, 0n, bp, h)) : {Pair.snd(Nat, Nat, _) == i : Nat}
  {==}

# Words: a word of k + m bits as its low k bits and its high m bits

def cp.take(+k: Nat, +m: Nat, w: Word(Nat.add(k, m))) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, cp.take(p, m, t)}

def cp.drop(+k: Nat, +m: Nat, w: Word(Nat.add(k, m))) -> Word(m):
  match k:
    case 0n:
      w
    case 1n+p:
      match w:
        case WCon{b, t}:
          cp.drop(p, m, t)

def cp.ones(+n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, cp.ones(p)}

def cp.cat(+k: Nat, +m: Nat, a: Word(k), b: Word(m)) -> Word(Nat.add(k, m)):
  match k:
    case 0n:
      match a:
        case WNil{}:
          b
    case 1n+p:
      match a:
        case WCon{x, t}:
          WCon{x, cp.cat(p, m, t, b)}

def cp.wd(u: U32) -> Word(32n):
  match u:
    case U32{w}:
      w

def cp.wcon_cong(-p: Nat, -s: Bool, -x: Word(p), -y: Word(p), +e: {x == y : Word(p)}) -> {WCon{s, x} == WCon{s, y} : Word(1n+p)}:
  %e : {WCon{s, x} == WCon{s, _} : Word(1n+p)}
  {==}

def cp.u32_cong(-x: Word(32n), -y: Word(32n), +e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  %e : {U32{x} == U32{_} : U32}
  {==}

# 2 (t + d) = 2 t + 2 d, from x = t + d
def cp.dstep(-x: Nat, +t: Nat, +d: Nat, +e: {x == Nat.add(t, d) : Nat}) -> {Nat.double(x) == Nat.add(Nat.double(t), Nat.double(d)) : Nat}:
  Equal.trans(Nat, Nat.double(x), Nat.double(Nat.add(t, d)), Nat.add(Nat.double(t), Nat.double(d)), cp.double_cong(x, Nat.add(t, d), e), cp.double_add(t, d))

# a word's value: its low k bits, plus 2^k times its high m bits
def cp.split_val(+k: Nat, +m: Nat, +w: Word(Nat.add(k, m))) -> {Word.to_nat(Nat.add(k, m), w) == Nat.add(Word.to_nat(k, cp.take(k, m, w)), U.U32Nat.dbl(k, Word.to_nat(m, cp.drop(k, m, w)))) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case False{}:
              cp.dstep(Word.to_nat(Nat.add(p, m), t), Word.to_nat(p, cp.take(p, m, t)), U.U32Nat.dbl(p, Word.to_nat(m, cp.drop(p, m, t))), cp.split_val(p, m, t))
            case True{}:
              cp.succ_cong(Nat.double(Word.to_nat(Nat.add(p, m), t)), Nat.add(Nat.double(Word.to_nat(p, cp.take(p, m, t))), Nat.double(U.U32Nat.dbl(p, Word.to_nat(m, cp.drop(p, m, t))))), cp.dstep(Word.to_nat(Nat.add(p, m), t), Word.to_nat(p, cp.take(p, m, t)), U.U32Nat.dbl(p, Word.to_nat(m, cp.drop(p, m, t))), cp.split_val(p, m, t)))

# k low bits a, then m high bits b: a + 2^k b
def cp.cat_val(+k: Nat, +m: Nat, +a: Word(k), +b: Word(m)) -> {Word.to_nat(Nat.add(k, m), cp.cat(k, m, a, b)) == Nat.add(Word.to_nat(k, a), U.U32Nat.dbl(k, Word.to_nat(m, b))) : Nat}:
  match k:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{x, t}:
          match x:
            case False{}:
              cp.dstep(Word.to_nat(Nat.add(p, m), cp.cat(p, m, t, b)), Word.to_nat(p, t), U.U32Nat.dbl(p, Word.to_nat(m, b)), cp.cat_val(p, m, t, b))
            case True{}:
              cp.succ_cong(Nat.double(Word.to_nat(Nat.add(p, m), cp.cat(p, m, t, b))), Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(U.U32Nat.dbl(p, Word.to_nat(m, b)))), cp.dstep(Word.to_nat(Nat.add(p, m), cp.cat(p, m, t, b)), Word.to_nat(p, t), U.U32Nat.dbl(p, Word.to_nat(m, b)), cp.cat_val(p, m, t, b)))

def cp.and_ones(+n: Nat, +w: Word(n)) -> {Word.and(n, w, cp.ones(n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              cp.wcon_cong(p, True{}, Word.and(p, t, cp.ones(p)), t, cp.and_ones(p, t))
            case False{}:
              cp.wcon_cong(p, False{}, Word.and(p, t, cp.ones(p)), t, cp.and_ones(p, t))

# w with its low k bits cleared: 2^k times its high m bits
def cp.and_hi_val(+k: Nat, +m: Nat, +w: Word(Nat.add(k, m))) -> {Word.to_nat(Nat.add(k, m), Word.and(Nat.add(k, m), w, cp.cat(k, m, Word.zero(k), cp.ones(m)))) == U.U32Nat.dbl(k, Word.to_nat(m, cp.drop(k, m, w))) : Nat}:
  match k:
    case 0n:
      Equal.cong(Word(m), Nat, x => Word.to_nat(m, x), Word.and(m, w, cp.ones(m)), w, cp.and_ones(m, w))
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              cp.double_cong(Word.to_nat(Nat.add(p, m), Word.and(Nat.add(p, m), t, cp.cat(p, m, Word.zero(p), cp.ones(m)))), U.U32Nat.dbl(p, Word.to_nat(m, cp.drop(p, m, t))), cp.and_hi_val(p, m, t))
            case False{}:
              cp.double_cong(Word.to_nat(Nat.add(p, m), Word.and(Nat.add(p, m), t, cp.cat(p, m, Word.zero(p), cp.ones(m)))), U.U32Nat.dbl(p, Word.to_nat(m, cp.drop(p, m, t))), cp.and_hi_val(p, m, t))

# 0 + y = y
def cp.add_zero_l(+n: Nat, +y: Word(n)) -> {Word.add(n, Word.zero(n), y) == y : Word(n)}:
  match n:
    case 0n:
      match y:
        case WNil{}:
          {==}
    case 1n+p:
      match y:
        case WCon{b, t}:
          match b:
            case True{}:
              cp.wcon_cong(p, True{}, Word.add(p, Word.zero(p), t), t, cp.add_zero_l(p, t))
            case False{}:
              cp.wcon_cong(p, False{}, Word.add(p, Word.zero(p), t), t, cp.add_zero_l(p, t))

# a product by a power of two is a shift
def cp.mul8(+a: U32) -> {U32.mul(8, a) == U32.shln(a, 3n) : U32}:
  match a:
    case U32{x}:
      cp.u32_cong(Word.add(32n, Word.zero(32n), Word.shl(32n, Word.shl(32n, Word.shl(32n, x)))), Word.shl(32n, Word.shl(32n, Word.shl(32n, x))), cp.add_zero_l(32n, Word.shl(32n, Word.shl(32n, Word.shl(32n, x)))))

def cp.mul4(+a: U32) -> {U32.mul(4, a) == U32.shln(a, 2n) : U32}:
  match a:
    case U32{x}:
      cp.u32_cong(Word.add(32n, Word.zero(32n), Word.shl(32n, Word.shl(32n, x))), Word.shl(32n, Word.shl(32n, x)), cp.add_zero_l(32n, Word.shl(32n, Word.shl(32n, x))))

def cp.mul2(+a: U32) -> {U32.mul(2, a) == U32.shln(a, 1n) : U32}:
  match a:
    case U32{x}:
      cp.u32_cong(Word.add(32n, Word.zero(32n), Word.shl(32n, x)), Word.shl(32n, x), cp.add_zero_l(32n, Word.shl(32n, x)))

# The rule's three cases, as values. With H = 1 + hp: t8 = rr + B H and
# p0 = B H + R, with rr and R below H, and h = H. Then p0 < t8 exactly when
# R < rr; if not, p0 < h exactly when B = 0.

# U32.is_lt(a, b), the values of a and b being x and y
def cp.ult(+a: U32, +b: U32, -x: Nat, -y: Nat, +ex: {U32.to_nat(a) == x : Nat}, +ey: {U32.to_nat(b) == y : Nat}) -> {U32.is_lt(a, b) == Nat.is_lt(x, y) : Bool}:
  %ex : {U32.is_lt(a, b) == Nat.is_lt(_, y) : Bool}
  %ey : {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), _) : Bool}
  UL.u32_lt_value(a, b)

def cp.lt_cancel(+z: Nat, +r: Nat, +rr: Nat) -> {Nat.is_lt(Nat.add(z, r), Nat.add(rr, z)) == Nat.is_lt(r, rr) : Bool}:
  %cp.add_comm(z, rr) : {Nat.is_lt(Nat.add(z, r), _) == Nat.is_lt(r, rr) : Bool}
  cp.lt_add_l(z, r, rr)

def cp.lt_pt(+p0: U32, +t8: U32, +B: Nat, +rr: Nat, +R: Nat, +H: Nat, +ht: {U32.to_nat(t8) == Nat.add(rr, Nat.mul(B, H)) : Nat}, +hp: {U32.to_nat(p0) == Nat.add(Nat.mul(B, H), R) : Nat}) -> {U32.is_lt(p0, t8) == Nat.is_lt(R, rr) : Bool}:
  Equal.trans(Bool, U32.is_lt(p0, t8), Nat.is_lt(Nat.add(Nat.mul(B, H), R), Nat.add(rr, Nat.mul(B, H))), Nat.is_lt(R, rr), cp.ult(p0, t8, Nat.add(Nat.mul(B, H), R), Nat.add(rr, Nat.mul(B, H)), hp, ht), cp.lt_cancel(Nat.mul(B, H), R, rr))

# p0 = (H + Y) + R is not below h = H
def cp.ge_h(+p0: U32, +h: U32, +hp: Nat, +y: Nat, +r: Nat, +hp0: {U32.to_nat(p0) == Nat.add(Nat.add(1n+hp, y), r) : Nat}, +hh: {U32.to_nat(h) == 1n+hp : Nat}) -> {U32.is_lt(p0, h) == False{} : Bool}:
  Equal.trans(Bool, U32.is_lt(p0, h), Nat.is_lt(Nat.add(Nat.add(1n+hp, y), r), 1n+hp), False{}, cp.ult(p0, h, Nat.add(Nat.add(1n+hp, y), r), 1n+hp, hp0, hh), Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.add(1n+hp, y), r), 1n+hp), Nat.is_lt(Nat.add(1n+hp, Nat.add(y, r)), 1n+hp), False{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+hp), Nat.add(Nat.add(1n+hp, y), r), Nat.add(1n+hp, Nat.add(y, r)), cp.add_assoc(1n+hp, y, r)), cp.not_lt_add(1n+hp, Nat.add(y, r))))

# and p0 - h = Y + R
def cp.vsub(+p0: U32, +h: U32, +hp: Nat, +y: Nat, +r: Nat, +hp0: {U32.to_nat(p0) == Nat.add(Nat.add(1n+hp, y), r) : Nat}, +hh: {U32.to_nat(h) == 1n+hp : Nat}) -> {U32.to_nat(U32.sub(p0, h)) == Nat.add(y, r) : Nat}:
  +e3 = Equal.trans(Nat, Nat.add(1n+hp, Nat.add(y, r)), Nat.add(Nat.add(1n+hp, y), r), U32.to_nat(p0), Equal.sym(Nat, Nat.add(Nat.add(1n+hp, y), r), Nat.add(1n+hp, Nat.add(y, r)), cp.add_assoc(1n+hp, y, r)), Equal.sym(Nat, U32.to_nat(p0), Nat.add(Nat.add(1n+hp, y), r), hp0))
  +hle = cp.le_rw(1n+hp, U32.to_nat(h), Nat.add(1n+hp, Nat.add(y, r)), U32.to_nat(p0), Equal.sym(Nat, U32.to_nat(h), 1n+hp, hh), e3, cp.le_add(1n+hp, Nat.add(y, r)))
  %Equal.sym(Nat, U32.to_nat(U32.sub(p0, h)), Nat.sub(U32.to_nat(p0), U32.to_nat(h)), UL.u32_sub_value(p0, h, hle)) : {_ == Nat.add(y, r) : Nat}
  %e3 : {Nat.sub(_, U32.to_nat(h)) == Nat.add(y, r) : Nat}
  %Equal.sym(Nat, U32.to_nat(h), 1n+hp, hh) : {Nat.sub(Nat.add(1n+hp, Nat.add(y, r)), _) == Nat.add(y, r) : Nat}
  cp.sub_add_l(1n+hp, Nat.add(y, r))

# Whether there is a position: exactly when R < t8

def cp.g_found_c(+p0: U32, +h: U32, +rr: Nat, +R: Nat, +hp: Nat, +c: Bool, +B: Nat, +ec: {Nat.is_lt(R, rr) == c : Bool}, +hp0: {U32.to_nat(p0) == Nat.add(Nat.mul(B, 1n+hp), R) : Nat}, +hh: {U32.to_nat(h) == 1n+hp : Nat}, +hR: {Nat.is_lt(R, 1n+hp) == True{} : Bool}) -> {Maybe.is_some(&2, U32, P.c842.pointer.at(c, p0, h)) == Nat.is_lt(R, Nat.add(rr, Nat.mul(B, 1n+hp))) : Bool}:
  match c:
    case True{}:
      Equal.sym(Bool, Nat.is_lt(R, Nat.add(rr, Nat.mul(B, 1n+hp))), True{}, cp.lt_le_trans(R, rr, Nat.add(rr, Nat.mul(B, 1n+hp)), ec, cp.le_add(rr, Nat.mul(B, 1n+hp))))
    case False{}:
      match B:
        case 0n:
          %Equal.sym(Bool, U32.is_lt(p0, h), True{}, Equal.trans(Bool, U32.is_lt(p0, h), Nat.is_lt(R, 1n+hp), True{}, cp.ult(p0, h, R, 1n+hp, hp0, hh), hR)) : {Maybe.is_some(&2, U32, P.c842.pointer.wrap(_, p0, h)) == Nat.is_lt(R, Nat.add(rr, 0n)) : Bool}
          %Equal.sym(Nat, Nat.add(rr, 0n), rr, cp.add_zero(rr)) : {False{} == Nat.is_lt(R, _) : Bool}
          Equal.sym(Bool, Nat.is_lt(R, rr), False{}, ec)
        case 1n+bq:
          +y = Nat.mul(bq, 1n+hp)
          %Equal.sym(Bool, U32.is_lt(p0, h), False{}, cp.ge_h(p0, h, hp, y, R, hp0, hh)) : {Maybe.is_some(&2, U32, P.c842.pointer.wrap(_, p0, h)) == Nat.is_lt(R, Nat.add(rr, Nat.add(1n+hp, y))) : Bool}
          Equal.sym(Bool, Nat.is_lt(R, Nat.add(rr, Nat.add(1n+hp, y))), True{}, cp.lt_le_trans(R, 1n+hp, Nat.add(rr, Nat.add(1n+hp, y)), hR, cp.le_trans(1n+hp, Nat.add(1n+hp, y), Nat.add(rr, Nat.add(1n+hp, y)), cp.le_add(1n+hp, y), cp.le_add_r(rr, Nat.add(1n+hp, y)))))

def cp.g_found(+p0: U32, +t8: U32, +h: U32, +B: Nat, +rr: Nat, +R: Nat, +hp: Nat, +ht: {U32.to_nat(t8) == Nat.add(rr, Nat.mul(B, 1n+hp)) : Nat}, +hp0: {U32.to_nat(p0) == Nat.add(Nat.mul(B, 1n+hp), R) : Nat}, +hh: {U32.to_nat(h) == 1n+hp : Nat}, +hR: {Nat.is_lt(R, 1n+hp) == True{} : Bool}) -> {Maybe.is_some(&2, U32, P.c842.pointer.at(U32.is_lt(p0, t8), p0, h)) == Nat.is_lt(R, U32.to_nat(t8)) : Bool}:
  %Equal.sym(Bool, U32.is_lt(p0, t8), Nat.is_lt(R, rr), cp.lt_pt(p0, t8, B, rr, R, 1n+hp, ht, hp0)) : {Maybe.is_some(&2, U32, P.c842.pointer.at(_, p0, h)) == Nat.is_lt(R, U32.to_nat(t8)) : Bool}
  %Equal.sym(Nat, U32.to_nat(t8), Nat.add(rr, Nat.mul(B, 1n+hp)), ht) : {Maybe.is_some(&2, U32, P.c842.pointer.at(Nat.is_lt(R, rr), p0, h)) == Nat.is_lt(R, _) : Bool}
  cp.g_found_c(p0, h, rr, R, hp, Nat.is_lt(R, rr), B, {==}, hp0, hh, hR)

# The position: p mod H = R, p + s <= t8 <= p + H (s = 1 + sp, H = Q s,
# t8 = X s, R = I s)

def cp.tri(-a: Nat, -b: Bool, -c: Bool, -x: Nat, +ea: {a == x : Nat}, +eb: {b == True{} : Bool}, +ec: {c == True{} : Bool}) -> {(a, b, c) == (x, True{}, True{}) : Nat & Bool & Bool}:
  %Equal.sym(Nat, a, x, ea) : {(_, b, c) == (x, True{}, True{}) : Nat & Bool & Bool}
  %Equal.sym(Bool, b, True{}, eb) : {(x, _, c) == (x, True{}, True{}) : Nat & Bool & Bool}
  %Equal.sym(Bool, c, True{}, ec) : {(x, True{}, _) == (x, True{}, True{}) : Nat & Bool & Bool}
  {==}

# P = A s below T = X s: P + s <= T
def cp.below(-p: Nat, -t: Nat, +a: Nat, +x: Nat, +sp: Nat, +ep: {p == Nat.mul(a, 1n+sp) : Nat}, +et: {t == Nat.mul(x, 1n+sp) : Nat}, +h: {Nat.is_lt(p, t) == True{} : Bool}) -> {Nat.is_le(Nat.add(p, 1n+sp), t) == True{} : Bool}:
  cp.le_rw(Nat.add(Nat.mul(a, 1n+sp), 1n+sp), Nat.add(p, 1n+sp), Nat.mul(x, 1n+sp), t, Equal.cong(Nat, Nat, z => Nat.add(z, 1n+sp), Nat.mul(a, 1n+sp), p, Equal.sym(Nat, p, Nat.mul(a, 1n+sp), ep)), Equal.sym(Nat, t, Nat.mul(x, 1n+sp), et), cp.step_s(a, x, sp, cp.lt_rw(p, Nat.mul(a, 1n+sp), t, Nat.mul(x, 1n+sp), ep, et, h)))

# B H + R = (B Q + I) s
def cp.mult(+b: Nat, +q: Nat, +i: Nat, +hp: Nat, +sp: Nat, -r: Nat, +hs: {1n+hp == Nat.mul(q, 1n+sp) : Nat}, +hi: {r == Nat.mul(i, 1n+sp) : Nat}) -> {Nat.add(Nat.mul(b, 1n+hp), r) == Nat.mul(Nat.add(Nat.mul(b, q), i), 1n+sp) : Nat}:
  %Equal.sym(Nat, 1n+hp, Nat.mul(q, 1n+sp), hs) : {Nat.add(Nat.mul(b, _), r) == Nat.mul(Nat.add(Nat.mul(b, q), i), 1n+sp) : Nat}
  %Equal.sym(Nat, r, Nat.mul(i, 1n+sp), hi) : {Nat.add(Nat.mul(b, Nat.mul(q, 1n+sp)), _) == Nat.mul(Nat.add(Nat.mul(b, q), i), 1n+sp) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(b, q), i), 1n+sp), Nat.add(Nat.mul(Nat.mul(b, q), 1n+sp), Nat.mul(i, 1n+sp)), cp.mul_add_r(Nat.mul(b, q), i, 1n+sp)) : {Nat.add(Nat.mul(b, Nat.mul(q, 1n+sp)), Nat.mul(i, 1n+sp)) == _ : Nat}
  %cp.mul_assoc(b, q, 1n+sp) : {Nat.add(_, Nat.mul(i, 1n+sp)) == Nat.add(Nat.mul(Nat.mul(b, q), 1n+sp), Nat.mul(i, 1n+sp)) : Nat}
  {==}

# rr < H: rr + Z <= (Z + R) + H
def cp.latest1(+rr: Nat, +z: Nat, +r: Nat, +hp: Nat, +hrr: {Nat.is_lt(rr, 1n+hp) == True{} : Bool}) -> {Nat.is_le(Nat.add(rr, z), Nat.add(Nat.add(z, r), 1n+hp)) == True{} : Bool}:
  cp.le_rw(Nat.add(z, rr), Nat.add(rr, z), Nat.add(z, Nat.add(r, 1n+hp)), Nat.add(Nat.add(z, r), 1n+hp), cp.add_comm(z, rr), Equal.sym(Nat, Nat.add(Nat.add(z, r), 1n+hp), Nat.add(z, Nat.add(r, 1n+hp)), cp.add_assoc(z, r, 1n+hp)), cp.le_add_mono(z, rr, Nat.add(r, 1n+hp), cp.le_trans(rr, 1n+hp, Nat.add(r, 1n+hp), cp.lt_le(rr, 1n+hp, hrr), cp.le_add_r(r, 1n+hp))))

# rr <= R: rr + (H + Y) <= (Y + R) + H
def cp.latest2(+rr: Nat, +hp: Nat, +y: Nat, +r: Nat, +hle: {Nat.is_le(rr, r) == True{} : Bool}) -> {Nat.is_le(Nat.add(rr, Nat.add(1n+hp, y)), Nat.add(Nat.add(y, r), 1n+hp)) == True{} : Bool}:
  +w = Nat.add(1n+hp, y)
  cp.le_rw(Nat.add(w, rr), Nat.add(rr, w), Nat.add(w, r), Nat.add(Nat.add(y, r), 1n+hp), cp.add_comm(w, rr), Equal.trans(Nat, Nat.add(w, r), Nat.add(1n+hp, Nat.add(y, r)), Nat.add(Nat.add(y, r), 1n+hp), cp.add_assoc(1n+hp, y, r), cp.add_comm(1n+hp, Nat.add(y, r))), cp.le_add_mono(w, rr, r, hle))

# R < H: Y + R < rr + (H + Y)
def cp.hlt2(+y: Nat, +r: Nat, +rr: Nat, +hp: Nat, +hR: {Nat.is_lt(r, 1n+hp) == True{} : Bool}) -> {Nat.is_lt(Nat.add(y, r), Nat.add(rr, Nat.add(1n+hp, y))) == True{} : Bool}:
  cp.lt_le_trans(Nat.add(y, r), Nat.add(1n+hp, y), Nat.add(rr, Nat.add(1n+hp, y)), cp.lt_rw(Nat.add(y, r), Nat.add(y, r), Nat.add(y, 1n+hp), Nat.add(1n+hp, y), {==}, cp.add_comm(y, 1n+hp), Equal.trans(Bool, Nat.is_lt(Nat.add(y, r), Nat.add(y, 1n+hp)), Nat.is_lt(r, 1n+hp), True{}, cp.lt_add_l(y, r, 1n+hp), hR)), cp.le_add_r(rr, Nat.add(1n+hp, y)))

def cp.g_some_c(+p0: U32, +h: U32, +p: U32, +rr: Nat, +R: Nat, +hp: Nat, +sp: Nat, +q: Nat, +x: Nat, +i: Nat, +c: Bool, +B: Nat, +ec: {Nat.is_lt(R, rr) == c : Bool}, +hp0: {U32.to_nat(p0) == Nat.add(Nat.mul(B, 1n+hp), R) : Nat}, +hh: {U32.to_nat(h) == 1n+hp : Nat}, +hrr: {Nat.is_lt(rr, 1n+hp) == True{} : Bool}, +hR: {Nat.is_lt(R, 1n+hp) == True{} : Bool}, +hs: {1n+hp == Nat.mul(q, 1n+sp) : Nat}, +hx: {Nat.add(rr, Nat.mul(B, 1n+hp)) == Nat.mul(x, 1n+sp) : Nat}, +hi: {R == Nat.mul(i, 1n+sp) : Nat}, +e: {P.c842.pointer.at(c, p0, h) == Some{p} : Maybe<&2, U32>}) -> {(Nat.mod(U32.to_nat(p), 1n+hp), Nat.is_le(Nat.add(U32.to_nat(p), 1n+sp), Nat.add(rr, Nat.mul(B, 1n+hp))), Nat.is_le(Nat.add(rr, Nat.mul(B, 1n+hp)), Nat.add(U32.to_nat(p), 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}:
  match c:
    case True{}:
      +z = Nat.mul(B, 1n+hp)
      %cp.some_inj(p0, p, e) : {(Nat.mod(U32.to_nat(_), 1n+hp), Nat.is_le(Nat.add(U32.to_nat(_), 1n+sp), Nat.add(rr, z)), Nat.is_le(Nat.add(rr, z), Nat.add(U32.to_nat(_), 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}
      %Equal.sym(Nat, U32.to_nat(p0), Nat.add(z, R), hp0) : {(Nat.mod(_, 1n+hp), Nat.is_le(Nat.add(_, 1n+sp), Nat.add(rr, z)), Nat.is_le(Nat.add(rr, z), Nat.add(_, 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}
      cp.tri(Nat.mod(Nat.add(z, R), 1n+hp), Nat.is_le(Nat.add(Nat.add(z, R), 1n+sp), Nat.add(rr, z)), Nat.is_le(Nat.add(rr, z), Nat.add(Nat.add(z, R), 1n+hp)), R, cp.mod_of(B, R, hp, hR), cp.below(Nat.add(z, R), Nat.add(rr, z), Nat.add(Nat.mul(B, q), i), x, sp, cp.mult(B, q, i, hp, sp, R, hs, hi), hx, Equal.trans(Bool, Nat.is_lt(Nat.add(z, R), Nat.add(rr, z)), Nat.is_lt(R, rr), True{}, cp.lt_cancel(z, R, rr), ec)), cp.latest1(rr, z, R, hp, hrr))
    case False{}:
      match B:
        case 0n:
          +e1 = Equal.trans(Bool, U32.is_lt(p0, h), Nat.is_lt(R, 1n+hp), True{}, cp.ult(p0, h, R, 1n+hp, hp0, hh), hR)
          cp.absurd({(Nat.mod(U32.to_nat(p), 1n+hp), Nat.is_le(Nat.add(U32.to_nat(p), 1n+sp), Nat.add(rr, 0n)), Nat.is_le(Nat.add(rr, 0n), Nat.add(U32.to_nat(p), 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}, cp.none_some(p, Equal.trans(Maybe<&2, U32>, None{}, P.c842.pointer.wrap(U32.is_lt(p0, h), p0, h), Some{p}, Equal.cong(Bool, Maybe<&2, U32>, b => P.c842.pointer.wrap(b, p0, h), True{}, U32.is_lt(p0, h), Equal.sym(Bool, U32.is_lt(p0, h), True{}, e1)), e)))
        case 1n+bq:
          +y = Nat.mul(bq, 1n+hp)
          +t = Nat.add(rr, Nat.add(1n+hp, y))
          +e1 = cp.ge_h(p0, h, hp, y, R, hp0, hh)
          +pe = cp.some_inj(U32.sub(p0, h), p, Equal.trans(Maybe<&2, U32>, Some{U32.sub(p0, h)}, P.c842.pointer.wrap(U32.is_lt(p0, h), p0, h), Some{p}, Equal.cong(Bool, Maybe<&2, U32>, b => P.c842.pointer.wrap(b, p0, h), False{}, U32.is_lt(p0, h), Equal.sym(Bool, U32.is_lt(p0, h), False{}, e1)), e))
          %pe : {(Nat.mod(U32.to_nat(_), 1n+hp), Nat.is_le(Nat.add(U32.to_nat(_), 1n+sp), t), Nat.is_le(t, Nat.add(U32.to_nat(_), 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}
          %Equal.sym(Nat, U32.to_nat(U32.sub(p0, h)), Nat.add(y, R), cp.vsub(p0, h, hp, y, R, hp0, hh)) : {(Nat.mod(_, 1n+hp), Nat.is_le(Nat.add(_, 1n+sp), t), Nat.is_le(t, Nat.add(_, 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}
          cp.tri(Nat.mod(Nat.add(y, R), 1n+hp), Nat.is_le(Nat.add(Nat.add(y, R), 1n+sp), t), Nat.is_le(t, Nat.add(Nat.add(y, R), 1n+hp)), R, cp.mod_of(bq, R, hp, hR), cp.below(Nat.add(y, R), t, Nat.add(Nat.mul(bq, q), i), x, sp, cp.mult(bq, q, i, hp, sp, R, hs, hi), hx, cp.hlt2(y, R, rr, hp, hR)), cp.latest2(rr, hp, y, R, cp.le_of_not_lt(R, rr, ec)))

def cp.g_some(+p0: U32, +t8: U32, +h: U32, +p: U32, +B: Nat, +rr: Nat, +R: Nat, +hp: Nat, +sp: Nat, +q: Nat, +x: Nat, +i: Nat, +ht: {U32.to_nat(t8) == Nat.add(rr, Nat.mul(B, 1n+hp)) : Nat}, +hp0: {U32.to_nat(p0) == Nat.add(Nat.mul(B, 1n+hp), R) : Nat}, +hh: {U32.to_nat(h) == 1n+hp : Nat}, +hrr: {Nat.is_lt(rr, 1n+hp) == True{} : Bool}, +hR: {Nat.is_lt(R, 1n+hp) == True{} : Bool}, +hs: {1n+hp == Nat.mul(q, 1n+sp) : Nat}, +hx: {U32.to_nat(t8) == Nat.mul(x, 1n+sp) : Nat}, +hi: {R == Nat.mul(i, 1n+sp) : Nat}, +e: {P.c842.pointer.at(U32.is_lt(p0, t8), p0, h) == Some{p} : Maybe<&2, U32>}) -> {(Nat.mod(U32.to_nat(p), 1n+hp), Nat.is_le(Nat.add(U32.to_nat(p), 1n+sp), U32.to_nat(t8)), Nat.is_le(U32.to_nat(t8), Nat.add(U32.to_nat(p), 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}:
  +elt = cp.lt_pt(p0, t8, B, rr, R, 1n+hp, ht, hp0)
  %Equal.sym(Nat, U32.to_nat(t8), Nat.add(rr, Nat.mul(B, 1n+hp)), ht) : {(Nat.mod(U32.to_nat(p), 1n+hp), Nat.is_le(Nat.add(U32.to_nat(p), 1n+sp), _), Nat.is_le(_, Nat.add(U32.to_nat(p), 1n+hp))) == (R, True{}, True{}) : Nat & Bool & Bool}
  cp.g_some_c(p0, h, p, rr, R, hp, sp, q, x, i, Nat.is_lt(R, rr), B, {==}, hp0, hh, hrr, hR, hs, Equal.trans(Nat, Nat.add(rr, Nat.mul(B, 1n+hp)), U32.to_nat(t8), Nat.mul(x, 1n+sp), Equal.sym(Nat, U32.to_nat(t8), Nat.add(rr, Nat.mul(B, 1n+hp)), ht), hx), hi, Equal.trans(Maybe<&2, U32>, P.c842.pointer.at(Nat.is_lt(R, rr), p0, h), P.c842.pointer.at(U32.is_lt(p0, t8), p0, h), Some{p}, Equal.cong(Bool, Maybe<&2, U32>, b => P.c842.pointer.at(b, p0, h), Nat.is_lt(R, rr), U32.is_lt(p0, t8), Equal.sym(Bool, U32.is_lt(p0, t8), Nat.is_lt(R, rr), elt)), e))

# The U32 words of c842.pointer.pos, for an output of n = U32{w} bytes

def cp.add_cong(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, +ea: {a == a2 : Nat}, +eb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %ea : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %eb : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def cp.lt_zero(+x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# t8: n with its low 3 bits cleared
def cp.t8(w: Word(32n)) -> U32:
  U32.and(U32{w}, 4294967288)

# n's high 29 bits, and its low 3
def cp.dv(w: Word(32n)) -> Nat:
  Word.to_nat(29n, cp.drop(3n, 29n, w))

def cp.lv(w: Word(32n)) -> Nat:
  Word.to_nat(3n, cp.take(3n, 29n, w))

# t8 is 8 times n's high 29 bits
def cp.vt8(+w: Word(32n)) -> {U32.to_nat(cp.t8(w)) == Nat.mul(cp.dv(w), 8n) : Nat}:
  Equal.trans(Nat, U32.to_nat(cp.t8(w)), U.U32Nat.dbl(3n, cp.dv(w)), Nat.mul(cp.dv(w), 8n), cp.and_hi_val(3n, 29n, w), cp.dbl_mul(3n, cp.dv(w)))

# n = 8 D + l, l < 8
def cp.ln(+w: Word(32n)) -> {Nat.is_lt(cp.lv(w), 8n) == True{} : Bool}:
  UL.word_value_lt(3n, cp.take(3n, 29n, w))

def cp.en(+w: Word(32n)) -> {Word.to_nat(32n, w) == Nat.add(Nat.mul(cp.dv(w), 8n), cp.lv(w)) : Nat}:
  Equal.trans(Nat, Word.to_nat(32n, w), Nat.add(cp.lv(w), U.U32Nat.dbl(3n, cp.dv(w))), Nat.add(Nat.mul(cp.dv(w), 8n), cp.lv(w)), cp.split_val(3n, 29n, w), Equal.trans(Nat, Nat.add(cp.lv(w), U.U32Nat.dbl(3n, cp.dv(w))), Nat.add(U.U32Nat.dbl(3n, cp.dv(w)), cp.lv(w)), Nat.add(Nat.mul(cp.dv(w), 8n), cp.lv(w)), cp.add_comm(cp.lv(w), U.U32Nat.dbl(3n, cp.dv(w))), Equal.cong(Nat, Nat, z => Nat.add(z, cp.lv(w)), U.U32Nat.dbl(3n, cp.dv(w)), Nat.mul(cp.dv(w), 8n), cp.dbl_mul(3n, cp.dv(w)))))

# the law's t8 (n rounded down to 8, by Nat.div) is the word t8's value
def cp.et(+w: Word(32n)) -> {U32.to_nat(cp.t8(w)) == Nat.mul(Nat.div(Word.to_nat(32n, w), 8n), 8n) : Nat}:
  %Equal.sym(Nat, Word.to_nat(32n, w), Nat.add(Nat.mul(cp.dv(w), 8n), cp.lv(w)), cp.en(w)) : {U32.to_nat(cp.t8(w)) == Nat.mul(Nat.div(_, 8n), 8n) : Nat}
  %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(cp.dv(w), 8n), cp.lv(w)), 8n), cp.dv(w), cp.div_of(cp.dv(w), cp.lv(w), 7n, cp.ln(w))) : {U32.to_nat(cp.t8(w)) == Nat.mul(_, 8n) : Nat}
  cp.vt8(w)

# t8 split at the history's k bits: rr + 2^k B
def cp.b11(w: Word(32n)) -> Nat:
  Word.to_nat(21n, cp.drop(11n, 21n, cp.wd(cp.t8(w))))

def cp.r11(w: Word(32n)) -> Nat:
  Word.to_nat(11n, cp.take(11n, 21n, cp.wd(cp.t8(w))))

def cp.b9(w: Word(32n)) -> Nat:
  Word.to_nat(23n, cp.drop(9n, 23n, cp.wd(cp.t8(w))))

def cp.r9(w: Word(32n)) -> Nat:
  Word.to_nat(9n, cp.take(9n, 23n, cp.wd(cp.t8(w))))

def cp.ht11(+w: Word(32n)) -> {U32.to_nat(cp.t8(w)) == Nat.add(cp.r11(w), Nat.mul(cp.b11(w), 2048n)) : Nat}:
  Equal.trans(Nat, U32.to_nat(cp.t8(w)), Nat.add(cp.r11(w), U.U32Nat.dbl(11n, cp.b11(w))), Nat.add(cp.r11(w), Nat.mul(cp.b11(w), 2048n)), cp.split_val(11n, 21n, cp.wd(cp.t8(w))), Equal.cong(Nat, Nat, z => Nat.add(cp.r11(w), z), U.U32Nat.dbl(11n, cp.b11(w)), Nat.mul(cp.b11(w), 2048n), cp.dbl_mul(11n, cp.b11(w))))

def cp.ht9(+w: Word(32n)) -> {U32.to_nat(cp.t8(w)) == Nat.add(cp.r9(w), Nat.mul(cp.b9(w), 512n)) : Nat}:
  Equal.trans(Nat, U32.to_nat(cp.t8(w)), Nat.add(cp.r9(w), U.U32Nat.dbl(9n, cp.b9(w))), Nat.add(cp.r9(w), Nat.mul(cp.b9(w), 512n)), cp.split_val(9n, 23n, cp.wd(cp.t8(w))), Equal.cong(Nat, Nat, z => Nat.add(cp.r9(w), z), U.U32Nat.dbl(9n, cp.b9(w)), Nat.mul(cp.b9(w), 512n), cp.dbl_mul(9n, cp.b9(w))))

def cp.hrr11(+w: Word(32n)) -> {Nat.is_lt(cp.r11(w), 2048n) == True{} : Bool}:
  UL.word_value_lt(11n, cp.take(11n, 21n, cp.wd(cp.t8(w))))

def cp.hrr9(+w: Word(32n)) -> {Nat.is_lt(cp.r9(w), 512n) == True{} : Bool}:
  UL.word_value_lt(9n, cp.take(9n, 23n, cp.wd(cp.t8(w))))

# p0 = base + s i, its value 2^k B + i s (no wrap: below the word with t8's
# high bits and k ones)
def cp.p0(w: Word(32n), h: U32, s: U32, i: U32) -> U32:
  U32.add(U32.and(cp.t8(w), U32.sub(0, h)), U32.mul(s, i))

# the word with t8's high bits and k ones below them
def cp.c11(w: Word(32n)) -> U32:
  U32{cp.cat(11n, 21n, cp.ones(11n), cp.drop(11n, 21n, cp.wd(cp.t8(w))))}

def cp.c9(w: Word(32n)) -> U32:
  U32{cp.cat(9n, 23n, cp.ones(9n), cp.drop(9n, 23n, cp.wd(cp.t8(w))))}

# s i, for s = 2^sh: i s (i s below the bound h)
def cp.vr(+i: U32, +s: U32, +sh: Nat, +h: U32, +em: {U32.mul(s, i) == U32.shln(i, sh) : U32}, +hR: {Nat.is_lt(Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)), U32.to_nat(h)) == True{} : Bool}) -> {U32.to_nat(U32.mul(s, i)) == Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)) : Nat}:
  +hb = cp.le_rw(Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)), U.U32Nat.dbl(sh, U32.to_nat(i)), U32.to_nat(h), U32.to_nat(h), Equal.sym(Nat, U.U32Nat.dbl(sh, U32.to_nat(i)), Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)), cp.dbl_mul(sh, U32.to_nat(i))), {==}, cp.lt_le(Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)), U32.to_nat(h), hR))
  Equal.trans(Nat, U32.to_nat(U32.mul(s, i)), U32.to_nat(U32.shln(i, sh)), Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)), Equal.cong(U32, Nat, u => U32.to_nat(u), U32.mul(s, i), U32.shln(i, sh), em), Equal.trans(Nat, U32.to_nat(U32.shln(i, sh)), U.U32Nat.dbl(sh, U32.to_nat(i)), Nat.mul(U32.to_nat(i), U.U32Nat.dbl(sh, 1n)), UL.u32_shln_value(i, sh, h, hb), cp.dbl_mul(sh, U32.to_nat(i))))

def cp.hp11(+w: Word(32n), +s: U32, +i: U32, +r: Nat, +vr: {U32.to_nat(U32.mul(s, i)) == r : Nat}, +hR: {Nat.is_lt(r, 2048n) == True{} : Bool}) -> {U32.to_nat(cp.p0(w, 2048, s, i)) == Nat.add(Nat.mul(cp.b11(w), 2048n), r) : Nat}:
  +base = U32.and(cp.t8(w), U32.sub(0, 2048))
  +c = cp.c11(w)
  +vb = cp.and_hi_val(11n, 21n, cp.wd(cp.t8(w)))
  +vc = cp.cat_val(11n, 21n, cp.ones(11n), cp.drop(11n, 21n, cp.wd(cp.t8(w))))
  +d = U.U32Nat.dbl(11n, cp.b11(w))
  +hc = cp.le_rw(Nat.add(d, r), Nat.add(U32.to_nat(base), U32.to_nat(U32.mul(s, i))), Nat.add(d, 2047n), U32.to_nat(c), Equal.sym(Nat, Nat.add(U32.to_nat(base), U32.to_nat(U32.mul(s, i))), Nat.add(d, r), cp.add_cong(U32.to_nat(base), d, U32.to_nat(U32.mul(s, i)), r, vb, vr)), Equal.trans(Nat, Nat.add(d, 2047n), Nat.add(2047n, d), U32.to_nat(c), cp.add_comm(d, 2047n), Equal.sym(Nat, U32.to_nat(c), Nat.add(2047n, d), vc)), cp.le_add_mono(d, r, 2047n, cp.lt_succ_le(r, 2047n, hR)))
  Equal.trans(Nat, U32.to_nat(cp.p0(w, 2048, s, i)), Nat.add(U32.to_nat(base), U32.to_nat(U32.mul(s, i))), Nat.add(Nat.mul(cp.b11(w), 2048n), r), UL.u32_add_value(base, U32.mul(s, i), c, hc), cp.add_cong(U32.to_nat(base), Nat.mul(cp.b11(w), 2048n), U32.to_nat(U32.mul(s, i)), r, Equal.trans(Nat, U32.to_nat(base), d, Nat.mul(cp.b11(w), 2048n), vb, cp.dbl_mul(11n, cp.b11(w))), vr))

def cp.hp9(+w: Word(32n), +s: U32, +i: U32, +r: Nat, +vr: {U32.to_nat(U32.mul(s, i)) == r : Nat}, +hR: {Nat.is_lt(r, 512n) == True{} : Bool}) -> {U32.to_nat(cp.p0(w, 512, s, i)) == Nat.add(Nat.mul(cp.b9(w), 512n), r) : Nat}:
  +base = U32.and(cp.t8(w), U32.sub(0, 512))
  +c = cp.c9(w)
  +vb = cp.and_hi_val(9n, 23n, cp.wd(cp.t8(w)))
  +vc = cp.cat_val(9n, 23n, cp.ones(9n), cp.drop(9n, 23n, cp.wd(cp.t8(w))))
  +d = U.U32Nat.dbl(9n, cp.b9(w))
  +hc = cp.le_rw(Nat.add(d, r), Nat.add(U32.to_nat(base), U32.to_nat(U32.mul(s, i))), Nat.add(d, 511n), U32.to_nat(c), Equal.sym(Nat, Nat.add(U32.to_nat(base), U32.to_nat(U32.mul(s, i))), Nat.add(d, r), cp.add_cong(U32.to_nat(base), d, U32.to_nat(U32.mul(s, i)), r, vb, vr)), Equal.trans(Nat, Nat.add(d, 511n), Nat.add(511n, d), U32.to_nat(c), cp.add_comm(d, 511n), Equal.sym(Nat, U32.to_nat(c), Nat.add(511n, d), vc)), cp.le_add_mono(d, r, 511n, cp.lt_succ_le(r, 511n, hR)))
  Equal.trans(Nat, U32.to_nat(cp.p0(w, 512, s, i)), Nat.add(U32.to_nat(base), U32.to_nat(U32.mul(s, i))), Nat.add(Nat.mul(cp.b9(w), 512n), r), UL.u32_add_value(base, U32.mul(s, i), c, hc), cp.add_cong(U32.to_nat(base), Nat.mul(cp.b9(w), 512n), U32.to_nat(U32.mul(s, i)), r, Equal.trans(Nat, U32.to_nat(base), d, Nat.mul(cp.b9(w), 512n), vb, cp.dbl_mul(9n, cp.b9(w))), vr))

# The index the parser reads: a field of w bits has a value below 2^w (for
# w <= 9, the pointers' widths)

def cp.lt_dbl(+x: Nat, +y: Nat) -> {Nat.is_lt(Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match y:
        case 0n:
          {==}
        case 1n+q:
          cp.lt_dbl(p, q)

def cp.lt_dbl1(+x: Nat, +y: Nat) -> {Nat.is_lt(1n+Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match y:
        case 0n:
          {==}
        case 1n+q:
          cp.lt_dbl1(p, q)

def cp.le_dbl(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.double(x), Nat.double(y)) == Nat.is_le(x, y) : Bool}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match y:
        case 0n:
          {==}
        case 1n+q:
          cp.le_dbl(p, q)

def cp.le_succ_self(+x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.le_succ_self(p)

def cp.le_double(+x: Nat) -> {Nat.is_le(x, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cp.le_trans(p, Nat.double(p), 1n+Nat.double(p), cp.le_double(p), cp.le_succ_self(Nat.double(p)))

# 1 <= 2^k
def cp.one_le(+k: Nat) -> {Nat.is_le(1n, U.U32Nat.dbl(k, 1n)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      cp.le_trans(1n, U.U32Nat.dbl(j, 1n), Nat.double(U.U32Nat.dbl(j, 1n)), cp.one_le(j), cp.le_double(U.U32Nat.dbl(j, 1n)))

# 2^j <= 2^k for j <= k
def cp.d_le(+j: Nat, +k: Nat, +h: {Nat.is_le(j, k) == True{} : Bool}) -> {Nat.is_le(U.U32Nat.dbl(j, 1n), U.U32Nat.dbl(k, 1n)) == True{} : Bool}:
  match j:
    case 0n:
      cp.one_le(k)
    case 1n+i:
      match k:
        case 0n:
          cp.absurd({Nat.is_le(Nat.double(U.U32Nat.dbl(i, 1n)), 1n) == True{} : Bool}, cp.ft(h))
        case 1n+l:
          Equal.trans(Bool, Nat.is_le(Nat.double(U.U32Nat.dbl(i, 1n)), Nat.double(U.U32Nat.dbl(l, 1n))), Nat.is_le(U.U32Nat.dbl(i, 1n), U.U32Nat.dbl(l, 1n)), True{}, cp.le_dbl(U.U32Nat.dbl(i, 1n), U.U32Nat.dbl(l, 1n)), cp.d_le(i, l, h))

def cp.or_zero(+n: Nat, +w: Word(n)) -> {Word.or(n, w, Word.zero(n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              cp.wcon_cong(p, True{}, Word.or(p, t, Word.zero(p)), t, cp.or_zero(p, t))
            case False{}:
              cp.wcon_cong(p, False{}, Word.or(p, t, Word.zero(p)), t, cp.or_zero(p, t))

# shl(v) | b: the bit b below v doubled
def cp.orb(+v: U32, +b: Bool) -> {U32.to_nat(U32.or(U32.shl(v), F.c842.fmt.b01(b))) == Nat.add(U.U32Nat.bit(b), U32.to_nat(U32.shl(v))) : Nat}:
  match v:
    case U32{w}:
      match w:
        case WCon{w0, wt}:
          match b:
            case True{}:
              cp.succ_cong(Nat.double(Word.to_nat(31n, Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n)))), Nat.double(Word.to_nat(31n, Word.shl.put(31n, w0, wt))), cp.double_cong(Word.to_nat(31n, Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n))), Word.to_nat(31n, Word.shl.put(31n, w0, wt)), Equal.cong(Word(31n), Nat, x => Word.to_nat(31n, x), Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n)), Word.shl.put(31n, w0, wt), cp.or_zero(31n, Word.shl.put(31n, w0, wt)))))
            case False{}:
              cp.double_cong(Word.to_nat(31n, Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n))), Word.to_nat(31n, Word.shl.put(31n, w0, wt)), Equal.cong(Word(31n), Nat, x => Word.to_nat(31n, x), Word.or(31n, Word.shl.put(31n, w0, wt), Word.zero(31n)), Word.shl.put(31n, w0, wt), cp.or_zero(31n, Word.shl.put(31n, w0, wt))))

# b + 2 V < 2 D from V < D
def cp.bit_lt(+b: Bool, +v: Nat, +d: Nat, +h: {Nat.is_lt(v, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(U.U32Nat.bit(b), Nat.double(v)), Nat.double(d)) == True{} : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, Nat.is_lt(1n+Nat.double(v), Nat.double(d)), Nat.is_lt(v, d), True{}, cp.lt_dbl1(v, d), h)
    case False{}:
      Equal.trans(Bool, Nat.is_lt(Nat.double(v), Nat.double(d)), Nat.is_lt(v, d), True{}, cp.lt_dbl(v, d), h)

def cp.vb(+bs: List<&2, Bool>, +hl: {Nat.is_le(List.length(&2, Bool, bs), 9n) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(F.c842.fmt.value(bs)), U.U32Nat.dbl(List.length(&2, Bool, bs), 1n)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      +v = U32.to_nat(F.c842.fmt.value(t))
      +d = U.U32Nat.dbl(List.length(&2, Bool, t), 1n)
      +ih = cp.vb(t, cp.le_trans(List.length(&2, Bool, t), 8n, 9n, hl, {==}))
      +h255 = cp.lt_succ_le(v, 255n, cp.lt_le_trans(v, d, 256n, ih, cp.d_le(List.length(&2, Bool, t), 8n, hl)))
      +hb = cp.le_trans(Nat.double(v), 510n, 1023n, Equal.trans(Bool, Nat.is_le(Nat.double(v), Nat.double(255n)), Nat.is_le(v, 255n), True{}, cp.le_dbl(v, 255n), h255), {==})
      +ev = Equal.trans(Nat, U32.to_nat(F.c842.fmt.value(Con{b, t})), Nat.add(U.U32Nat.bit(b), U32.to_nat(U32.shl(F.c842.fmt.value(t)))), Nat.add(U.U32Nat.bit(b), Nat.double(v)), cp.orb(F.c842.fmt.value(t), b), Equal.cong(Nat, Nat, z => Nat.add(U.U32Nat.bit(b), z), U32.to_nat(U32.shl(F.c842.fmt.value(t))), Nat.double(v), UL.u32_shl_value(F.c842.fmt.value(t), 1023, hb)))
      cp.lt_rw(Nat.add(U.U32Nat.bit(b), Nat.double(v)), U32.to_nat(F.c842.fmt.value(Con{b, t})), Nat.double(d), U.U32Nat.dbl(List.length(&2, Bool, Con{b, t}), 1n), Equal.sym(Nat, U32.to_nat(F.c842.fmt.value(Con{b, t})), Nat.add(U.U32Nat.bit(b), Nat.double(v)), ev), {==}, cp.bit_lt(b, v, d, ih))

# an index below 2^wb, times s = 2^sh: below 2^sh 2^wb
def cp.mulb(+v: Nat, +sh: Nat, +wb: Nat, +hv: {Nat.is_lt(v, U.U32Nat.dbl(wb, 1n)) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(v, U.U32Nat.dbl(sh, 1n)), U.U32Nat.dbl(sh, U.U32Nat.dbl(wb, 1n))) == True{} : Bool}:
  cp.lt_rw(U.U32Nat.dbl(sh, v), Nat.mul(v, U.U32Nat.dbl(sh, 1n)), U.U32Nat.dbl(sh, U.U32Nat.dbl(wb, 1n)), U.U32Nat.dbl(sh, U.U32Nat.dbl(wb, 1n)), cp.dbl_mul(sh, v), {==}, Equal.trans(Bool, Nat.is_lt(U.U32Nat.dbl(sh, v), U.U32Nat.dbl(sh, U.U32Nat.dbl(wb, 1n))), Nat.is_lt(v, U.U32Nat.dbl(wb, 1n)), True{}, UL.dbl_lt(sh, v, U.U32Nat.dbl(wb, 1n)), hv))

def cp.none_of(+m: Maybe<&2, U32>, +e: {Maybe.is_some(&2, U32, m) == False{} : Bool}) -> {None{} == m : Maybe<&2, U32>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      cp.absurd({None{} == Some{x} : Maybe<&2, U32>}, cp.true_false(e))

# the window: p + s <= t8 <= n and n < t8 + 8 <= p + H + 8
def cp.le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  cp.le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d), cp.le_add_mono(a, c, d, h2), cp.le_rw(Nat.add(d, a), Nat.add(a, d), Nat.add(d, b), Nat.add(b, d), cp.add_comm(d, a), cp.add_comm(d, b), cp.le_add_mono(d, a, b, h1)))

def cp.window(+p: Nat, +s: Nat, +hh: Nat, +w: Word(32n), +b1: {Nat.is_le(Nat.add(p, s), Nat.mul(Nat.div(Word.to_nat(32n, w), 8n), 8n)) == True{} : Bool}, +b2: {Nat.is_le(Nat.mul(Nat.div(Word.to_nat(32n, w), 8n), 8n), Nat.add(p, hh)) == True{} : Bool}) -> {(Nat.is_le(Nat.add(p, s), Word.to_nat(32n, w)), Nat.is_le(Word.to_nat(32n, w), Nat.add(Nat.add(p, hh), 7n))) == (True{}, True{}) : Bool & Bool}:
  +t = Nat.mul(Nat.div(Word.to_nat(32n, w), 8n), 8n)
  +m8 = Nat.mul(cp.dv(w), 8n)
  +etm = Equal.trans(Nat, m8, U32.to_nat(cp.t8(w)), t, Equal.sym(Nat, U32.to_nat(cp.t8(w)), m8, cp.vt8(w)), cp.et(w))
  +en = Equal.sym(Nat, Word.to_nat(32n, w), Nat.add(m8, cp.lv(w)), cp.en(w))
  +c1 = cp.le_trans(Nat.add(p, s), t, Word.to_nat(32n, w), b1, cp.le_rw(m8, t, Nat.add(m8, cp.lv(w)), Word.to_nat(32n, w), etm, en, cp.le_add(m8, cp.lv(w))))
  +c2 = cp.le_rw(Nat.add(m8, cp.lv(w)), Word.to_nat(32n, w), Nat.add(Nat.add(p, hh), 7n), Nat.add(Nat.add(p, hh), 7n), en, {==}, cp.le_add2(m8, Nat.add(p, hh), cp.lv(w), 7n, cp.le_rw(t, m8, Nat.add(p, hh), Nat.add(p, hh), Equal.sym(Nat, m8, t, etm), {==}, b2), cp.lt_succ_le(cp.lv(w), 7n, cp.ln(w))))
  %Equal.sym(Bool, Nat.is_le(Nat.add(p, s), Word.to_nat(32n, w)), True{}, c1) : {(_, Nat.is_le(Word.to_nat(32n, w), Nat.add(Nat.add(p, hh), 7n))) == (True{}, True{}) : Bool & Bool}
  %Equal.sym(Bool, Nat.is_le(Word.to_nat(32n, w), Nat.add(Nat.add(p, hh), 7n)), True{}, c2) : {(True{}, _) == (True{}, True{}) : Bool & Bool}
  {==}
