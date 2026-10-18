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

# Natural numbers: the arithmetic the span laws need, from Base's
# definitions of Nat.add, Nat.sub, Nat.mul and Nat.divmod (the division
# lemmas are ext2's, from its PROOF.bend)

def IOP.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %IOP.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def IOP.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %IOP.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def IOP.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %IOP.add_zero(b) : {_ == Nat.add(b, 0n) : Nat}
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), IOP.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %IOP.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def IOP.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %IOP.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

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
      Equal.trans(Nat, a, Nat.add(b, 0n), b, Equal.trans(Nat, a, Nat.add(a, 0n), Nat.add(b, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, IOP.add_zero(a)), e), IOP.add_zero(b))
    case 1n+q:
      IOP.add_cancel(q, a, b, IOP.succ_inj(Nat.add(a, q), Nat.add(b, q), Equal.trans(Nat, 1n+Nat.add(a, q), Nat.add(a, 1n+q), 1n+Nat.add(b, q), Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), IOP.add_succ(a, q)), Equal.trans(Nat, Nat.add(a, 1n+q), Nat.add(b, 1n+q), 1n+Nat.add(b, q), e, IOP.add_succ(b, q)))))

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
      IOP.add_zero(1n+b)
    case 1n+b 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(b, q), 1n+q), 1n+Nat.add(Nat.sub(b, q), q), 1n+b, IOP.add_succ(Nat.sub(b, q), q), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(b, q), q), b, IOP.sub_add(b, q, h)))

# Base's division: Nat.divmod(a, 1 + bp) runs go(a, bp, 0, 0), which counts
# m down and r up (m + r == bp throughout) and d once per full round.

def IOP.dm_lhs(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> Nat:
  Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)))

def IOP.dm_sum(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {IOP.dm_lhs(n, m, d, r, bp) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match n m:
    case 0n _:
      h => {==}
    case 1n+np 0n:
      +h =>
        +dd = Nat.mul(d, 1n+bp)
        +x = Nat.add(Nat.add(bp, dd), 0n)
        %Equal.sym(Nat, r, bp, h) : {IOP.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, Nat.add(dd, _)) : Nat}
        %IOP.add_comm(bp, dd) : {IOP.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, _) : Nat}
        %IOP.add_zero(Nat.add(bp, dd)) : {IOP.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, _) : Nat}
        %IOP.add_succ(np, x) : {IOP.dm_lhs(1n+np, 0n, d, r, bp) == _ : Nat}
        IOP.dm_sum(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, IOP.add_zero(r), h))
    case 1n+np 1n+mp:
      h =>
        +dd = Nat.mul(d, 1n+bp)
        %IOP.add_succ(np, Nat.add(dd, r)) : {IOP.dm_lhs(1n+np, 1n+mp, d, r, bp) == _ : Nat}
        %IOP.add_succ(dd, r) : {IOP.dm_lhs(1n+np, 1n+mp, d, r, bp) == Nat.add(np, _) : Nat}
        IOP.dm_sum(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, IOP.add_succ(mp, r), h))

def IOP.div_mod(+k: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(k, 1n+bp), 1n+bp), Nat.mod(k, 1n+bp)) == k : Nat}:
  Equal.trans(Nat, IOP.dm_lhs(k, bp, 0n, 0n, bp), Nat.add(k, 0n), k, IOP.dm_sum(k, bp, 0n, 0n, bp, IOP.add_zero(bp)), IOP.add_zero(k))

def IOP.lt_add(+m: Nat, +r: Nat) -> {Nat.is_lt(r, 1n+Nat.add(m, r)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(m, 1n+p), 1n+Nat.add(m, p), IOP.add_succ(m, p)) : {Nat.is_lt(1n+p, 1n+_) == True{} : Bool}
      IOP.lt_add(m, p)

def IOP.dm_lt(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp) == True{} : Bool}:
  match n m:
    case 0n _:
      h =>
        %h : {Nat.is_lt(r, 1n+_) == True{} : Bool}
        IOP.lt_add(m, r)
    case 1n+np 0n:
      h => IOP.dm_lt(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, IOP.add_zero(r), h))
    case 1n+np 1n+mp:
      h => IOP.dm_lt(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, IOP.add_succ(mp, r), h))

def IOP.mod_lt(+k: Nat, +bp: Nat) -> {Nat.is_lt(Nat.mod(k, 1n+bp), 1n+bp) == True{} : Bool}:
  IOP.dm_lt(k, bp, 0n, 0n, bp, IOP.add_zero(bp))

# fewer steps than m left in the round: the remainder grows by n
def IOP.dm_small(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_lt(n, 1n+m) == True{} : Bool} -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
  match n m:
    case 0n _:
      h => {==}
    case 1n+np 0n:
      h => IOP.ex_falso({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : Nat & Nat}, IOP.no_lt_one(np, h))
    case 1n+np 1n+mp:
      h =>
        %IOP.add_succ(np, r) : {Nat.divmod.go(1n+np, 1n+mp, d, r) == (d, _) : Nat & Nat}
        IOP.dm_small(np, mp, d, 1n+r, h)

# finishing a round: m steps, then one more starts the next
def IOP.dm_round(+m: Nat, +n: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(Nat.add(m, 1n+n), m, d, r) == Nat.divmod.go(n, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      %IOP.add_succ(mp, r) : {Nat.divmod.go(Nat.add(1n+mp, 1n+n), 1n+mp, d, r) == Nat.divmod.go(n, _, 1n+d, 0n) : Nat & Nat}
      IOP.dm_round(mp, n, d, 1n+r)

def IOP.dm_rounds(+g: Nat, +i: Nat, +d: Nat, +bp: Nat) -> {Nat.is_lt(i, 1n+bp) == True{} : Bool} -> {Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, d, 0n) == (Nat.add(g, d), i) : Nat & Nat}:
  match g:
    case 0n:
      h =>
        %IOP.add_zero(i) : {Nat.divmod.go(i, bp, d, 0n) == (d, _) : Nat & Nat}
        IOP.dm_small(i, bp, d, 0n, h)
    case 1n+gp:
      h =>
        +gg = Nat.mul(gp, 1n+bp)
        +y = Nat.add(gg, i)
        %Equal.sym(Nat, Nat.add(Nat.add(bp, gg), i), Nat.add(bp, y), IOP.add_assoc(bp, gg, i)) : {Nat.divmod.go(1n+_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %IOP.add_succ(bp, y) : {Nat.divmod.go(_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(bp, 1n+y), bp, d, 0n), Nat.divmod.go(y, Nat.add(bp, 0n), 1n+d, 0n), IOP.dm_round(bp, y, d, 0n)) : {_ == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Equal.sym(Nat, Nat.add(bp, 0n), bp, IOP.add_zero(bp)) : {Nat.divmod.go(y, _, 1n+d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %IOP.add_succ(gp, d) : {Nat.divmod.go(y, bp, 1n+d, 0n) == (_, i) : Nat & Nat}
        IOP.dm_rounds(gp, i, 1n+d, bp, h)

# Spans. With a block of 1 + bp bytes, Nat.sub(1 + bp, 1) is Nat.sub(bp, 0),
# which is bp by IOP.sub_zero.

def IOP.slack_lt(+bp: Nat, +t: Nat) -> {Nat.is_lt(Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(t, 1n+bp)), 1n+bp) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, IOP.sub_zero(bp)) : {Nat.is_lt(Nat.sub(_, Nat.mod(t, 1n+bp)), 1n+bp) == True{} : Bool}
  IOP.sub_lt(bp, Nat.mod(t, 1n+bp))

# a + bp == (a + (bp - r)) + r, for r < 1 + bp
def IOP.cover_sum(+bp: Nat, +a: Nat, +r: Nat, h: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.add(a, Nat.sub(bp, 0n)) == Nat.add(Nat.add(a, Nat.sub(bp, r)), r) : Nat}:
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, IOP.sub_zero(bp)) : {Nat.add(a, _) == Nat.add(Nat.add(a, Nat.sub(bp, r)), r) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, Nat.sub(bp, r)), r), Nat.add(a, Nat.add(Nat.sub(bp, r), r)), IOP.add_assoc(a, Nat.sub(bp, r), r)) : {Nat.add(a, bp) == _ : Nat}
  %IOP.sub_add(bp, r, h) : {Nat.add(a, _) == Nat.add(a, Nat.add(Nat.sub(bp, r), r)) : Nat}
  {==}

def IOP.cover(+bp: Nat, +a: Nat) -> {Nat.mul(Nat.div(Nat.add(a, Nat.sub(1n+bp, 1n)), 1n+bp), 1n+bp) == Nat.add(a, Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(Nat.add(a, Nat.sub(1n+bp, 1n)), 1n+bp))) : Nat}:
  +t = Nat.add(a, Nat.sub(bp, 0n))
  +q = Nat.div(t, 1n+bp)
  +r = Nat.mod(t, 1n+bp)
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, IOP.sub_zero(bp)) : {Nat.mul(q, 1n+bp) == Nat.add(a, Nat.sub(_, r)) : Nat}
  IOP.add_cancel(r, Nat.mul(q, 1n+bp), Nat.add(a, Nat.sub(bp, r)), Equal.trans(Nat, Nat.add(Nat.mul(q, 1n+bp), r), t, Nat.add(Nat.add(a, Nat.sub(bp, r)), r), IOP.div_mod(t, bp), IOP.cover_sum(bp, a, r, IOP.mod_lt(t, bp))))

def Laws.span_start(bp, off, len):
  IOP.div_mod(off, bp)

def Laws.span_skip(bp, off, len):
  IOP.mod_lt(off, bp)

def Laws.span_cover(bp, off, len):
  IOP.cover(bp, Nat.add(Nat.mod(off, 1n+bp), len))

def Laws.span_slack(bp, off, len):
  IOP.slack_lt(bp, Nat.add(Nat.add(Nat.mod(off, 1n+bp), len), Nat.sub(1n+bp, 1n)))

def Laws.span_in_block(bp, n, i, len, h):
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(n, 1n+bp), i), bp, 0n, 0n), (Nat.add(n, 0n), i), IOP.dm_rounds(n, i, 0n, bp, h)) : {(Pair.fst(Nat, Nat, _), Pair.snd(Nat, Nat, _)) == (n, i) : Nat & Nat}
  %Equal.sym(Nat, Nat.add(n, 0n), n, IOP.add_zero(n)) : {(_, i) == (n, i) : Nat & Nat}
  {==}

def Laws.blocks_cover(bp, size):
  IOP.cover(bp, size)

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
