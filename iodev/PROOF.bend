import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../blockdev/LAWS.bend as BDL
import ../blockdev/PROOF.bend as BDP
import ../xarray/xarray.bend as X
import ../xarray/LAWS.bend as XL
import ../xarray/PROOF.bend as XP
import ./span.bend as S
import ./iodev.bend as V
import ./mem.bend as M
import ./overlay.bend as O
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP
import ../u32/LAWS_div.bend as UD
import ../u32/PROOF_div.bend as UDP

# Natural numbers: the arithmetic the span laws need, from Base's
# definitions of Nat.add, Nat.sub and Nat.mul (the division laws are
# bend-osdev-u32's, LAWS_div.bend)

def IOP.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def IOP.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def IOP.succ_inj(+x: Nat, +y: Nat, e: {1n+x == 1n+y : Nat}) -> {x == y : Nat}:
  Equal.cong(Nat, Nat, IOP.pred, 1n+x, 1n+y, e)

# a + r == b + r gives a == b
def IOP.add_cancel(+r: Nat, +a: Nat, +b: Nat, e: {Nat.add(a, r) == Nat.add(b, r) : Nat}) -> {a == b : Nat}:
  match r:
    case 0n:
      Equal.trans(Nat, a, Nat.add(b, 0n), b, Equal.trans(Nat, a, Nat.add(a, 0n), Nat.add(b, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, UL.nat_add_zero(a)), e), UL.nat_add_zero(b))
    case 1n+q:
      IOP.add_cancel(q, a, b, IOP.succ_inj(Nat.add(a, q), Nat.add(b, q), Equal.trans(Nat, 1n+Nat.add(a, q), Nat.add(a, 1n+q), 1n+Nat.add(b, q), Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), UL.nat_add_succ(a, q)), Equal.trans(Nat, Nat.add(a, 1n+q), Nat.add(b, 1n+q), 1n+Nat.add(b, q), e, UL.nat_add_succ(b, q)))))

def IOP.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      IOP.lt_succ(p)

def IOP.bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def IOP.bool_clash(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : IOP.bool_disc(_)
  Unit{}

def IOP.ex_falso(-A: Type, e: Empty) -> A:
  match e:

def IOP.no_lt_one(+np: Nat) -> {Nat.is_lt(1n+np, 1n) == True{} : Bool} -> Empty:
  match np:
    case 0n:
      h => IOP.bool_clash(h)
    case 1n+q:
      h => IOP.bool_clash(h)

# x < y gives x < y + 1
def IOP.lt_up(+x: Nat, +y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      IOP.ex_falso({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, IOP.bool_clash(h))
    case 1n+xp 1n+yp:
      IOP.lt_up(xp, yp, h)

# bp - r < bp + 1
def IOP.sub_lt(+bp: Nat, +r: Nat) -> {Nat.is_lt(Nat.sub(bp, r), 1n+bp) == True{} : Bool}:
  match bp r:
    case 0n _:
      {==}
    case 1n+b 0n:
      IOP.lt_succ(b)
    case 1n+b 1n+q:
      IOP.lt_up(Nat.sub(b, q), 1n+b, IOP.sub_lt(b, q))

# r < bp + 1 gives (bp - r) + r == bp
def IOP.sub_add(+bp: Nat, +r: Nat, h: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.add(Nat.sub(bp, r), r) == bp : Nat}:
  match bp r:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      IOP.ex_falso({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, IOP.no_lt_one(q, h))
    case 1n+b 0n:
      UL.nat_add_zero(1n+b)
    case 1n+b 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(b, q), 1n+q), 1n+Nat.add(Nat.sub(b, q), q), 1n+b, UL.nat_add_succ(Nat.sub(b, q), q), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(b, q), q), b, IOP.sub_add(b, q, h)))

# Base's division: Nat.divmod(a, 1 + bp) runs go(a, bp, 0, 0), which counts
# m down and r up (m + r == bp throughout) and d once per full round.

# Spans. With a block of 1 + bp bytes, Nat.sub(1 + bp, 1) is Nat.sub(bp, 0),
# which is bp by IOP.sub_zero.

def IOP.slack_lt(+bp: Nat, +t: Nat) -> {Nat.is_lt(Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(t, 1n+bp)), 1n+bp) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, IOP.sub_zero(bp)) : {Nat.is_lt(Nat.sub(_, Nat.mod(t, 1n+bp)), 1n+bp) == True{} : Bool}
  IOP.sub_lt(bp, Nat.mod(t, 1n+bp))

def Laws.span_start(bp, off, len):
  UD.nat_div_mod(off, bp)

def Laws.span_skip(bp, off, len):
  UD.nat_mod_lt(off, bp)

def Laws.span_cover(bp, off, len):
  UD.nat_round_up(bp, Nat.add(Nat.mod(off, 1n+bp), len))

def Laws.span_slack(bp, off, len):
  IOP.slack_lt(bp, Nat.add(Nat.add(Nat.mod(off, 1n+bp), len), Nat.sub(1n+bp, 1n)))

def Laws.span_in_block(bp, n, i, len, h):
  %Equal.sym(Nat & Nat, Nat.divmod(Nat.add(Nat.mul(n, 1n+bp), i), 1n+bp), (n, i), UD.nat_divmod_exact(n, i, bp, h)) : {(Pair.fst(Nat, Nat, _), Pair.snd(Nat, Nat, _)) == (n, i) : Nat & Nat}
  {==}

def Laws.blocks_cover(bp, size):
  UD.nat_round_up(bp, size)

# A span inside (or past) n blocks: (first + count) * bs is off + len plus
# the slack, which is less than a block

def IOP.lt_zero(+x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def IOP.lt0(+p: Nat, h: {Nat.is_lt(p, 0n) == True{} : Bool}) -> Empty:
  IOP.bool_clash(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, IOP.lt_zero(p)), h))

def IOP.le_zero(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a < b is 1 + a <= b
def IOP.lt_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      IOP.ex_falso({Nat.is_le(1n+a, 0n) == True{} : Bool}, IOP.lt0(a, h))
    case 0n 1n+ +q:
      IOP.le_zero(q)
    case 1n+ +p 1n+ +q:
      IOP.lt_le(p, q, h)

def IOP.le_lt(+a: Nat, +b: Nat, +h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      IOP.ex_falso({Nat.is_lt(a, 0n) == True{} : Bool}, IOP.bool_clash(h))
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 1n+ +q:
      IOP.le_lt(p, q, h)

def IOP.lt_rw_l(-x: Nat, -y: Nat, -m: Nat, e: {x == y : Nat}, h: {Nat.is_lt(y, m) == True{} : Bool}) -> {Nat.is_lt(x, m) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(_, m) == True{} : Bool}
  h

def IOP.lt_rw_r(-k: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, h: {Nat.is_lt(k, y) == True{} : Bool}) -> {Nat.is_lt(k, x) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(k, _) == True{} : Bool}
  h

def IOP.le_rw_l(-x: Nat, -y: Nat, -m: Nat, e: {x == y : Nat}, h: {Nat.is_le(y, m) == True{} : Bool}) -> {Nat.is_le(x, m) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_le(_, m) == True{} : Bool}
  h

def IOP.le_rw_r(-k: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, h: {Nat.is_le(k, y) == True{} : Bool}) -> {Nat.is_le(k, x) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_le(k, _) == True{} : Bool}
  h

# c + a < c + b is a < b
def IOP.add_lt_l(+c: Nat, -a: Nat, -b: Nat) -> {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == Nat.is_lt(a, b) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+ +p:
      IOP.add_lt_l(p, a, b)

# x * (1 + bp) < y * (1 + bp) gives x < y
def IOP.mul_lt_cancel(+x: Nat, +y: Nat, +bp: Nat, +h: {Nat.is_lt(Nat.mul(x, 1n+bp), Nat.mul(y, 1n+bp)) == True{} : Bool}) -> {Nat.is_lt(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      IOP.ex_falso({Nat.is_lt(0n, 0n) == True{} : Bool}, IOP.bool_clash(h))
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      IOP.ex_falso({Nat.is_lt(1n+p, 0n) == True{} : Bool}, IOP.bool_clash(h))
    case 1n+ +p 1n+ +q:
      IOP.mul_lt_cancel(p, q, bp, Equal.trans(Bool, Nat.is_lt(Nat.mul(p, 1n+bp), Nat.mul(q, 1n+bp)), Nat.is_lt(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), Nat.add(1n+bp, Nat.mul(q, 1n+bp))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), Nat.add(1n+bp, Nat.mul(q, 1n+bp))), Nat.is_lt(Nat.mul(p, 1n+bp), Nat.mul(q, 1n+bp)), IOP.add_lt_l(1n+bp, Nat.mul(p, 1n+bp), Nat.mul(q, 1n+bp))), h))

# x < 1 + n gives x <= n
def IOP.lt_succ_le(+x: Nat, +n: Nat, +h: {Nat.is_lt(x, 1n+n) == True{} : Bool}) -> {Nat.is_le(x, n) == True{} : Bool}:
  match x n:
    case 0n _:
      IOP.le_zero(n)
    case 1n+ +p 0n:
      IOP.ex_falso({Nat.is_le(1n+p, 0n) == True{} : Bool}, IOP.lt0(p, h))
    case 1n+ +p 1n+ +q:
      IOP.lt_succ_le(p, q, h)

# a <= b gives a + (b - a) == b
def IOP.le_wit(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n _:
      IOP.sub_zero(b)
    case 1n+ +p 0n:
      IOP.ex_falso({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, IOP.bool_clash(h))
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, Nat.sub(q, p)), q, IOP.le_wit(p, q, h))

# P <= Q and L < bs give P + L < bs + Q
def IOP.lt_add_both(+a: Nat, +b: Nat, +l: Nat, +bs: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_lt(l, bs) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, l), Nat.add(bs, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      UO.nat_lt_le_trans(l, bs, Nat.add(bs, b), h2, UO.nat_le_add_r(bs, b))
    case 1n+ +p 0n:
      IOP.ex_falso({Nat.is_lt(Nat.add(1n+p, l), Nat.add(bs, 0n)) == True{} : Bool}, IOP.bool_clash(h1))
    case 1n+ +p 1n+ +q:
      %Equal.sym(Nat, Nat.add(bs, 1n+q), 1n+Nat.add(bs, q), UL.nat_add_succ(bs, q)) : {Nat.is_lt(1n+Nat.add(p, l), _) == True{} : Bool}
      IOP.lt_add_both(p, q, l, bs, h1, h2)

def IOP.span_eq(+bp: Nat, +off: Nat, +len: Nat) -> {Nat.mul(Nat.add(S.IOSpan.first(S.IOSpan.of(1n+bp, off, len)), S.IOSpan.count(S.IOSpan.of(1n+bp, off, len))), 1n+bp) == Nat.add(Nat.add(off, len), S.IOSpan.slack(S.IOSpan.of(1n+bp, off, len))) : Nat}:
  +bs : Nat = 1n+bp
  +s = Nat.mod(off, bs)
  +f = Nat.div(off, bs)
  +t = Nat.add(Nat.add(s, len), Nat.sub(bs, 1n))
  +c = Nat.div(t, bs)
  +l = Nat.sub(Nat.sub(bs, 1n), Nat.mod(t, bs))
  %Equal.sym(Nat, Nat.mul(Nat.add(f, c), bs), Nat.add(Nat.mul(f, bs), Nat.mul(c, bs)), UL.nat_add_mul(f, c, bs)) : {_ == Nat.add(Nat.add(off, len), l) : Nat}
  %Equal.sym(Nat, Nat.mul(c, bs), Nat.add(Nat.add(s, len), l), UD.nat_round_up(bp, Nat.add(s, len))) : {Nat.add(Nat.mul(f, bs), _) == Nat.add(Nat.add(off, len), l) : Nat}
  %UL.nat_add_assoc(Nat.mul(f, bs), Nat.add(s, len), l) : {_ == Nat.add(Nat.add(off, len), l) : Nat}
  %UL.nat_add_assoc(Nat.mul(f, bs), s, len) : {Nat.add(_, l) == Nat.add(Nat.add(off, len), l) : Nat}
  %UD.nat_div_mod(off, bp) : {Nat.add(Nat.add(Nat.add(Nat.mul(f, bs), s), len), l) == Nat.add(Nat.add(_, len), l) : Nat}
  {==}

def IOP.span_within(+bp: Nat, +off: Nat, +len: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(off, len), Nat.mul(n, 1n+bp)) == True{} : Bool}) -> {Nat.is_le(Nat.add(S.IOSpan.first(S.IOSpan.of(1n+bp, off, len)), S.IOSpan.count(S.IOSpan.of(1n+bp, off, len))), n) == True{} : Bool}:
  +sp = S.IOSpan.of(1n+bp, off, len)
  +fc = Nat.add(S.IOSpan.first(sp), S.IOSpan.count(sp))
  +l = S.IOSpan.slack(sp)
  IOP.lt_succ_le(fc, n, IOP.mul_lt_cancel(fc, 1n+n, bp, IOP.lt_rw_l(Nat.mul(fc, 1n+bp), Nat.add(Nat.add(off, len), l), Nat.add(1n+bp, Nat.mul(n, 1n+bp)), IOP.span_eq(bp, off, len), IOP.lt_add_both(Nat.add(off, len), Nat.mul(n, 1n+bp), l, 1n+bp, h, Laws.span_slack(bp, off, len)))))

def IOP.span_past(+bp: Nat, +off: Nat, +len: Nat, +n: Nat, +h: {Nat.is_lt(Nat.mul(n, 1n+bp), Nat.add(off, len)) == True{} : Bool}) -> {Nat.is_lt(n, Nat.add(S.IOSpan.first(S.IOSpan.of(1n+bp, off, len)), S.IOSpan.count(S.IOSpan.of(1n+bp, off, len)))) == True{} : Bool}:
  +sp = S.IOSpan.of(1n+bp, off, len)
  +fc = Nat.add(S.IOSpan.first(sp), S.IOSpan.count(sp))
  +l = S.IOSpan.slack(sp)
  IOP.mul_lt_cancel(n, fc, bp, IOP.lt_rw_r(Nat.mul(n, 1n+bp), Nat.mul(fc, 1n+bp), Nat.add(Nat.add(off, len), l), IOP.span_eq(bp, off, len), UO.nat_lt_le_trans(Nat.mul(n, 1n+bp), Nat.add(off, len), Nat.add(Nat.add(off, len), l), h, UO.nat_le_add_r(Nat.add(off, len), l))))

def Laws.span_within(bp, off, len, n, h):
  IOP.span_within(bp, off, len, n, h)

def Laws.span_past(bp, off, len, n, h):
  IOP.span_past(bp, off, len, n, h)

# The adapters. One step of IODev.read_blocks on a pure device, with the
# read's result generalised to res (IOP.tail is the step as read_blocks runs
# it; its continuation is written as read_blocks writes its own, so that
# the two elaborate alike)

def IOP.cons(~D: Data, -R: Type, -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D, +blk: B.Octets, r: Result<&2, &2, D.DevError, B.Octets>) -> {V.IODev.cons(~D, blk, (d, r))(R, k) == k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, r, rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest))))) : IO.OP<R>}:
  match r:
    case Done{rest}:
      {==}
    case Fail{e}:
      {==}

def IOP.tail(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, d: D, res: Result<&2, &2, D.DevError, B.Octets>, +p: Nat, +first: Nat) -> IO.OP<R>:
  V.IODev.then(~D, (d, res), d2 => R2 => k2 => V.IODev.read_blocks(~D, ~V.IODev.of_pure_read(~D, ~read_block), p, d2, Nat.add(first, 1n))(R2, x => k2(x)))(R, k)

def IOP.step(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D, res: Result<&2, &2, D.DevError, B.Octets>, +p: Nat, +first: Nat, ih: @-k2: ((D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>) -> {V.IODev.read_blocks(~D, ~V.IODev.of_pure_read(~D, ~read_block), p, d, Nat.add(first, 1n))(R, k2) == k2((d, D.Dev.read_blocks(~D, ~read_block, d, p, Nat.add(first, 1n)))) : IO.OP<R>}) -> {IOP.tail(~D, ~read_block, R, k, d, res, p, first) == k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, res, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D, ~read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))))) : IO.OP<R>}:
  match res:
    case Done{+blk}:
      +rest = D.Dev.read_blocks(~D, ~read_block, d, p, Nat.add(first, 1n))
      Equal.trans(IO.OP<R>, V.IODev.read_blocks(~D, ~V.IODev.of_pure_read(~D, ~read_block), p, d, Nat.add(first, 1n))(R, x => V.IODev.cons(~D, blk, x)(R, y => k(y))), V.IODev.cons(~D, blk, (d, rest))(R, y => k(y)), k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, rest, r => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, r))))), ih(x => V.IODev.cons(~D, blk, x)(R, y => k(y))), IOP.cons(~D, R, y => k(y), d, blk, rest))
    case Fail{e}:
      {==}

def IOP.read_blocks(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +count: Nat, +d: D, +first: Nat) -> {V.IODev.read_blocks(~D, ~V.IODev.of_pure_read(~D, ~read_block), count, d, first)(R, k) == k((d, D.Dev.read_blocks(~D, ~read_block, d, count, first))) : IO.OP<R>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      IOP.step(~D, ~read_block, R, x => k(x), d, read_block(d, first), p, first, k2 => IOP.read_blocks(~D, ~read_block, R, x => k2(x), p, d, Nat.add(first, 1n)))

def Laws.io_read_blocks(D, read_block, R, k, d, count, first):
  IOP.read_blocks(~D, ~read_block, R, k, count, d, first)

def IOP.slice(~D: Data, -R: Type, -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D, +skip: Nat, +len: Nat, r: Result<&2, &2, D.DevError, B.Octets>) -> {V.IODev.slice(~D, skip, len, (d, r))(R, k) == k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, r, blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(skip, len, blocks))))) : IO.OP<R>}:
  match r:
    case Done{b}:
      {==}
    case Fail{e}:
      {==}

def IOP.read_bytes(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, -k: (D & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D, +off: Nat, +len: Nat) -> {V.IODev.read_bytes(~D, ~V.IODev.of_pure_size(~D, ~block_size), ~V.IODev.of_pure_read(~D, ~read_block), d, off, len)(R, k) == k((d, D.Dev.read_bytes(~D, ~block_size, ~read_block, d, off, len))) : IO.OP<R>}:
  match len:
    case 0n:
      {==}
    case 1n+lp:
      +bs = block_size(d)
      +skip = Nat.mod(off, bs)
      +count = Nat.div(Nat.add(Nat.add(skip, 1n+lp), Nat.sub(bs, 1n)), bs)
      +first = Nat.div(off, bs)
      +blocks = D.Dev.read_blocks(~D, ~read_block, d, count, first)
      Equal.trans(IO.OP<R>, V.IODev.read_blocks(~D, ~V.IODev.of_pure_read(~D, ~read_block), count, d, first)(R, x => V.IODev.slice(~D, skip, 1n+lp, x)(R, y => k(y))), V.IODev.slice(~D, skip, 1n+lp, (d, blocks))(R, y => k(y)), k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, blocks, b => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(skip, 1n+lp, b))))), IOP.read_blocks(~D, ~read_block, R, x => V.IODev.slice(~D, skip, 1n+lp, x)(R, y => k(y)), count, d, first), IOP.slice(~D, R, y => k(y), d, skip, 1n+lp, blocks))

def Laws.io_read_bytes(D, block_size, read_block, R, k, d, off, len):
  IOP.read_bytes(~D, ~block_size, ~read_block, R, k, d, off, len)

def Laws.io_mem_write_ok(R, k, d, n, data, len_ok, in_range):
  Equal.cong(D.MemDev & Result<&2, &2, D.DevError, Unit>, IO.OP<R>, x => k(x), D.MemDev.own_write_block(d, n, data), (D.MemDev.update(d, n, data), Done{Unit{}}), BDL.own_write_ok(d, n, data, len_ok, in_range))

# The overlay. A write is put.check on the two tests (length, range); each
# lemma takes the tests' results as okl and okn.

def IOP.res_disc(r: Result<&2, &2, D.DevError, Unit>) -> Type:
  match r:
    case Done{u}:
      Unit
    case Fail{e}:
      Empty

def IOP.res_clash(+e: D.DevError, h: {Fail{e} == Done{Unit{}} : Result<&2, &2, D.DevError, Unit>}) -> Empty:
  %Equal.sym(Result<&2, &2, D.DevError, Unit>, Fail{e}, Done{Unit{}}, h) : IOP.res_disc(_)
  Unit{}

def IOP.put_none(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), -R: Type, -k: (O.IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, okl: Bool, okn: Bool, b: D, +bs: Nat, +c: Nat, +x: X.XArray<B.Octets>, +n: Nat, +data: B.Octets, e: Empty) -> {O.IOOverlay.read_block(~D, ~read_block, Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put.check(~D, okl, okn, b, bs, c, x, n, data)), n)(R, k) == k((Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put.check(~D, okl, okn, b, bs, c, x, n, data)), Done{data})) : IO.OP<R>}:
  match e:

def IOP.put_read(~D: Type, ~read_block: D -> Nat -> IO(D & Result<&2, &2, D.DevError, B.Octets>), -R: Type, -k: (O.IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, okl: Bool, okn: Bool, b: D, +bs: Nat, +c: Nat, +x: X.XArray<B.Octets>, +n: Nat, +data: B.Octets, ok: {Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put.check(~D, okl, okn, b, bs, c, x, n, data)) == Done{Unit{}} : Result<&2, &2, D.DevError, Unit>}) -> {O.IOOverlay.read_block(~D, ~read_block, Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put.check(~D, okl, okn, b, bs, c, x, n, data)), n)(R, k) == k((Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put.check(~D, okl, okn, b, bs, c, x, n, data)), Done{data})) : IO.OP<R>}:
  match okl okn:
    case True{} True{}:
      +st = X.XArray.store(B.Octets, x, U32.from_nat(n), data)
      %Equal.sym(Maybe<&2, B.Octets>, X.XArray.load(B.Octets, st, U32.from_nat(n)), Some{data}, XL.load_store(B.Octets, x, U32.from_nat(n), data)) : {O.IOOverlay.read.got(~D, ~read_block, _, b, bs, c, st, n)(R, k) == k((O.IOOverlay{b, bs, c, st}, Done{data})) : IO.OP<R>}
      {==}
    case False{} _:
      IOP.put_none(~D, ~read_block, R, k, False{}, okn, b, bs, c, x, n, data, IOP.res_clash(D.DevBadLength{bs, B.Octets.len(data)}, ok))
    case True{} False{}:
      IOP.put_none(~D, ~read_block, R, k, True{}, False{}, b, bs, c, x, n, data, IOP.res_clash(D.DevOutOfRange{n}, ok))

def Laws.ov_read_put(D, read_block, R, k, o, n, data, ok):
  match o:
    case O.IOOverlay{b, +bs, +c, +x}:
      IOP.put_read(~D, ~read_block, R, k, Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c), b, bs, c, x, n, data, ok)

# reads through a pure device below do not depend on the overlay's blocks
# when the block is looked up the same way
def IOP.got_same(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, m: Maybe<&2, B.Octets>, +b: D, +bs: Nat, +c: Nat, x1: X.XArray<B.Octets>, x2: X.XArray<B.Octets>, +n: Nat) -> {O.IOOverlay.read.got(~D, ~V.IODev.of_pure_read(~D, ~read_block), m, b, bs, c, x1, n)(R, p => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, p))) == O.IOOverlay.read.got(~D, ~V.IODev.of_pure_read(~D, ~read_block), m, b, bs, c, x2, n)(R, p => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, p))) : IO.OP<R>}:
  match m:
    case Some{blk}:
      {==}
    case None{}:
      {==}

def IOP.put_other(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, okl: Bool, okn: Bool, +b: D, +bs: Nat, +c: Nat, +x: X.XArray<B.Octets>, +n: Nat, +m: Nat, +data: B.Octets, diff: {U32.is_eq(U32.from_nat(n), U32.from_nat(m)) == False{} : Bool}) -> {O.IOOverlay.read_block(~D, ~V.IODev.of_pure_read(~D, ~read_block), Pair.fst(O.IOOverlay<D>, Result<&2, &2, D.DevError, Unit>, O.IOOverlay.put.check(~D, okl, okn, b, bs, c, x, n, data)), m)(R, p => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, p))) == O.IOOverlay.read_block(~D, ~V.IODev.of_pure_read(~D, ~read_block), O.IOOverlay{b, bs, c, x}, m)(R, p => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, p))) : IO.OP<R>}:
  match okl okn:
    case True{} True{}:
      +st = X.XArray.store(B.Octets, x, U32.from_nat(n), data)
      %Equal.sym(Maybe<&2, B.Octets>, X.XArray.load(B.Octets, st, U32.from_nat(m)), X.XArray.load(B.Octets, x, U32.from_nat(m)), XL.load_store_other(B.Octets, x, U32.from_nat(n), U32.from_nat(m), data, diff)) : {O.IOOverlay.read.got(~D, ~V.IODev.of_pure_read(~D, ~read_block), _, b, bs, c, st, m)(R, p => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, p))) == O.IOOverlay.read.got(~D, ~V.IODev.of_pure_read(~D, ~read_block), X.XArray.load(B.Octets, x, U32.from_nat(m)), b, bs, c, x, m)(R, p => k(Pair.snd(O.IOOverlay<D>, Result<&2, &2, D.DevError, B.Octets>, p))) : IO.OP<R>}
      IOP.got_same(~D, ~read_block, R, k, X.XArray.load(B.Octets, x, U32.from_nat(m)), b, bs, c, st, x, m)
    case False{} _:
      {==}
    case True{} False{}:
      {==}

def Laws.ov_put_other(D, read_block, R, k, o, n, m, data, diff):
  match o:
    case O.IOOverlay{+b, +bs, +c, +x}:
      IOP.put_other(~D, ~read_block, R, k, Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c), b, bs, c, x, n, m, data, diff)

def IOP.read_fresh(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -R: Type, -k: (O.IOOverlay<D> & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D, +bs: Nat, +count: Nat, +n: Nat) -> {O.IOOverlay.read_block(~D, ~V.IODev.of_pure_read(~D, ~read_block), O.IOOverlay.of(~D, d, bs, count), n)(R, k) == k((O.IOOverlay.of(~D, d, bs, count), read_block(d, n))) : IO.OP<R>}:
  %Equal.sym(Maybe<&2, B.Octets>, X.XArray.load(B.Octets, X.XArray.empty(B.Octets), U32.from_nat(n)), None{}, XL.load_empty(B.Octets, U32.from_nat(n))) : {O.IOOverlay.read.got(~D, ~V.IODev.of_pure_read(~D, ~read_block), _, d, bs, count, X.XArray.empty(B.Octets), n)(R, k) == k((O.IOOverlay.of(~D, d, bs, count), read_block(d, n))) : IO.OP<R>}
  {==}

def Laws.ov_read_fresh(D, read_block, R, k, d, bs, count, n):
  IOP.read_fresh(~D, ~read_block, R, k, d, bs, count, n)

# Vectors, by computation

def Laws.vector_span():
  {==}

def Laws.vector_blocks():
  {==}

def Laws.vector_io_bytes():
  {==}

def Laws.vector_io_past_end():
  {==}

def Laws.vector_io_img():
  {==}

def Laws.vector_write_bytes():
  {==}

def Laws.vector_overlay():
  {==}

def Laws.vector_overlay_base():
  {==}
