# Proofs of LAWS_write.bend. Internal lemmas are prefixed IWP. (the Nat
# lemmas IOP. are in PROOF.bend); blockdev's laws say what MemDev's reads
# and writes do (LAWS.bend, LAWS_range.bend).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BPF
import ../blockdev/blockdev.bend as D
import ../blockdev/LAWS.bend as BDL
import ../blockdev/PROOF.bend as BDP
import ../blockdev/LAWS_range.bend as BRL
import ../blockdev/PROOF_range.bend as BRP
import ./span.bend as S
import ./iodev.bend as V
import ./mem.bend as M
import ./LAWS.bend as L
import ./PROOF.bend as P
import ./LAWS_write.bend as Laws

# Nat

def IWP.nat_t(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+ +p:
      Empty

def IWP.sz(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %Equal.sym(Nat, 1n+k, 0n, e) : IWP.nat_t(_)
  Unit{}

def IWP.eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      IWP.eq_refl(p)

def IWP.eq_of(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  IWP.eq_refl(a)

def IWP.eq_nat(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      P.IOP.ex_falso({0n == 1n+q : Nat}, P.IOP.bool_clash(h))
    case 1n+ +p 0n:
      P.IOP.ex_falso({1n+p == 0n : Nat}, P.IOP.bool_clash(h))
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, IWP.eq_nat(p, q, h))

def IWP.add_one(+j: Nat) -> {Nat.add(j, 1n) == 1n+j : Nat}:
  Equal.trans(Nat, Nat.add(j, 1n), 1n+Nat.add(j, 0n), 1n+j, P.IOP.add_succ(j, 0n), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(j, 0n), j, P.IOP.add_zero(j)))

# p + (j + 1) == 1 + (p + j)
def IWP.add_one_r(+p: Nat, +j: Nat) -> {Nat.add(p, Nat.add(j, 1n)) == 1n+Nat.add(p, j) : Nat}:
  %Equal.sym(Nat, Nat.add(j, 1n), 1n+j, IWP.add_one(j)) : {Nat.add(p, _) == 1n+Nat.add(p, j) : Nat}
  P.IOP.add_succ(p, j)

# s is inside a range that starts at s and has 1 + n more before m
def IWP.lt_of_range(+n: Nat, +s: Nat, +m: Nat, +h: {Nat.is_le(1n+Nat.add(n, s), m) == True{} : Bool}) -> {Nat.is_lt(s, m) == True{} : Bool}:
  P.IOP.le_lt(s, m, P.IOP.le_trans(1n+s, 1n+Nat.add(n, s), m, P.IOP.le_rw_r(s, Nat.add(n, s), Nat.add(s, n), P.IOP.add_comm(n, s), P.IOP.le_add_r(s, n)), h))

def IWP.lt_to_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  P.IOP.le_trans(a, 1n+a, b, P.IOP.le_rw_r(a, 1n+a, Nat.add(a, 1n), Equal.sym(Nat, Nat.add(a, 1n), 1n+a, IWP.add_one(a)), P.IOP.le_add_r(a, 1n)), P.IOP.lt_le(a, b, h))

# c <= x gives x < c false
def IWP.le_not_lt(+c: Nat, +x: Nat, +h: {Nat.is_le(c, x) == True{} : Bool}) -> {Nat.is_lt(x, c) == False{} : Bool}:
  match c x:
    case 0n _:
      P.IOP.lt_zero(x)
    case 1n+ +p 0n:
      P.IOP.ex_falso({Nat.is_lt(0n, 1n+p) == False{} : Bool}, P.IOP.bool_clash(h))
    case 1n+ +p 1n+ +q:
      IWP.le_not_lt(p, q, h)

def IWP.le_cancel(+w: Nat, -x: Nat, -y: Nat) -> {Nat.is_le(Nat.add(w, x), Nat.add(w, y)) == Nat.is_le(x, y) : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+ +p:
      IWP.le_cancel(p, x, y)

def IWP.mul_mono(+a: Nat, +b: Nat, +w: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, w), Nat.mul(b, w)) == True{} : Bool}:
  match a b:
    case 0n _:
      P.IOP.le_zero(Nat.mul(b, w))
    case 1n+ +p 0n:
      P.IOP.ex_falso({Nat.is_le(Nat.mul(1n+p, w), 0n) == True{} : Bool}, P.IOP.bool_clash(h))
    case 1n+ +p 1n+ +q:
      %Equal.sym(Bool, Nat.is_le(Nat.add(w, Nat.mul(p, w)), Nat.add(w, Nat.mul(q, w))), Nat.is_le(Nat.mul(p, w), Nat.mul(q, w)), IWP.le_cancel(w, Nat.mul(p, w), Nat.mul(q, w))) : {_ == True{} : Bool}
      IWP.mul_mono(p, q, w, h)

def IWP.min_l(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +p 0n:
      P.IOP.ex_falso({Nat.min(1n+p, 0n) == 1n+p : Nat}, P.IOP.bool_clash(h))
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), p, IWP.min_l(p, q, h))

def IWP.mul_zero(+a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ +p:
      IWP.mul_zero(p)

# (a + m) - m == a, and (a + b) - a == b
def IWP.add_sub_r(+a: Nat, +m: Nat) -> {Nat.sub(Nat.add(a, m), m) == a : Nat}:
  match m:
    case 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(a, 0n), 0n), Nat.add(a, 0n), a, P.IOP.sub_zero(Nat.add(a, 0n)), P.IOP.add_zero(a))
    case 1n+ +q:
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), P.IOP.add_succ(a, q)) : {Nat.sub(_, 1n+q) == a : Nat}
      IWP.add_sub_r(a, q)

def IWP.add_sub_l(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      P.IOP.sub_zero(b)
    case 1n+ +p:
      IWP.add_sub_l(p, b)

# a <= b gives b - (b - a) == a
def IWP.sub_sub(+b: Nat, +a: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(b, Nat.sub(b, a)) == a : Nat}:
  +m = Nat.sub(b, a)
  %P.IOP.le_wit(a, b, h) : {Nat.sub(_, m) == a : Nat}
  IWP.add_sub_r(a, m)

# n * bs == 1 + x gives n == 1 + pred(n)
def IWP.succ_of(+n: Nat, +x: Nat, +bs: Nat, +h: {Nat.mul(n, bs) == 1n+x : Nat}) -> {n == 1n+P.IOP.pred(n) : Nat}:
  match n:
    case 0n:
      P.IOP.ex_falso({0n == 1n+P.IOP.pred(0n) : Nat}, IWP.sz(x, Equal.sym(Nat, 0n, 1n+x, h)))
    case 1n+ +q:
      {==}

# Octets

def IWP.nil_of(+xs: List<&2, U32>, +h: {B.len(xs) == 0n : Nat}) -> {B.Octets.of_list(xs) == B.Octets.empty() : B.Octets}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Empty.absurd({B.Octets.of_list(Con{x, t}) == B.Octets.empty() : B.Octets}, IWP.sz(B.len(t), h))

def IWP.len0(+o: B.Octets, +h: {B.Octets.len(o) == 0n : Nat}) -> {o == B.Octets.empty() : B.Octets}:
  Equal.trans(B.Octets, o, B.Octets.of_list(B.Octets.to_list(o)), B.Octets.empty(), Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)), IWP.nil_of(B.Octets.to_list(o), Equal.trans(Nat, B.len(B.Octets.to_list(o)), B.Octets.len(o), 0n, Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)), h)))

def IWP.patch_nil(+x: Nat, +o: B.Octets) -> {D.Dev.patch(x, B.Octets.empty(), o) == o : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), B.Octets.drop(Nat.add(x, 0n), o)), B.Octets.drop(Nat.add(x, 0n), o), BL.octets_append_empty_l(B.Octets.drop(Nat.add(x, 0n), o))) : {B.Octets.append(B.Octets.take(x, o), _) == o : B.Octets}
  %Equal.sym(Nat, Nat.add(x, 0n), x, P.IOP.add_zero(x)) : {B.Octets.append(B.Octets.take(x, o), B.Octets.drop(_, o)) == o : B.Octets}
  BL.octets_take_drop(x, o)

# IOMem's reads are blockdev's (IOP.read_blocks and IOP.read_bytes, for
# IOMem's operations)

def IWP.tail(-R: Type, k: (D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, d: D.MemDev, res: Result<&2, &2, D.DevError, B.Octets>, +p: Nat, +first: Nat) -> IO.OP<R>:
  V.IODev.then(~D.MemDev, (d, res), d2 => R2 => k2 => V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, p, d2, Nat.add(first, 1n))(R2, x => k2(x)))(R, k)

def IWP.step(-R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D.MemDev, res: Result<&2, &2, D.DevError, B.Octets>, +p: Nat, +first: Nat, ih: @-k2: ((D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>) -> {V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, p, d, Nat.add(first, 1n))(R, k2) == k2((d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n)))) : IO.OP<R>}) -> {IWP.tail(R, k, d, res, p, first) == k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, res, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))))) : IO.OP<R>}:
  match res:
    case Done{+blk}:
      +rest = D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n))
      Equal.trans(IO.OP<R>, V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, p, d, Nat.add(first, 1n))(R, x => V.IODev.cons(~D.MemDev, blk, x)(R, y => k(y))), V.IODev.cons(~D.MemDev, blk, (d, rest))(R, y => k(y)), k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, rest, r => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, r))))), ih(x => V.IODev.cons(~D.MemDev, blk, x)(R, y => k(y))), P.IOP.cons(~D.MemDev, R, y => k(y), d, blk, rest))
    case Fail{e}:
      {==}

def IWP.read_blocks(-R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +count: Nat, +d: D.MemDev, +first: Nat) -> {V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, d, first)(R, k) == k((d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first))) : IO.OP<R>}:
  match count:
    case 0n:
      {==}
    case 1n+ +p:
      IWP.step(R, x => k(x), d, D.MemDev.read_block(d, first), p, first, k2 => IWP.read_blocks(R, x => k2(x), p, d, Nat.add(first, 1n)))

def Laws.io_mem_read_blocks(R, k, d, count, first):
  IWP.read_blocks(R, k, count, d, first)

def IWP.read_bytes(-R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> IO.OP<R>, +d: D.MemDev, +off: Nat, +len: Nat) -> {V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, off, len)(R, k) == k((d, D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, off, len))) : IO.OP<R>}:
  match len:
    case 0n:
      {==}
    case 1n+ +lp:
      +bs = D.MemDev.block_size(d)
      +skip = Nat.mod(off, bs)
      +count = Nat.div(Nat.add(Nat.add(skip, 1n+lp), Nat.sub(bs, 1n)), bs)
      +first = Nat.div(off, bs)
      +blocks = D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first)
      Equal.trans(IO.OP<R>, V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, d, first)(R, x => V.IODev.slice(~D.MemDev, skip, 1n+lp, x)(R, y => k(y))), V.IODev.slice(~D.MemDev, skip, 1n+lp, (d, blocks))(R, y => k(y)), k((d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, blocks, b => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(skip, 1n+lp, b))))), IWP.read_blocks(R, x => V.IODev.slice(~D.MemDev, skip, 1n+lp, x)(R, y => k(y)), count, d, first), P.IOP.slice(~D.MemDev, R, y => k(y), d, skip, 1n+lp, blocks))

def Laws.io_mem_read_bytes(R, k, d, off, len):
  IWP.read_bytes(R, k, d, off, len)

# fold_blocks on a pure device is the step folded over read_list's blocks

def IWP.fmap(~A: Data, ~step: A -> B.Octets -> A, +blk: B.Octets, +acc: A, q: Result<&2, &2, D.DevError, List<&2, B.Octets>>) -> {Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, step(acc, blk)), q) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, acc), Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, q, rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest}))) : Result<&2, &2, D.DevError, A>}:
  match q:
    case Done{xs}:
      {==}
    case Fail{e}:
      {==}

def IWP.fold_tail(~A: Data, ~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~step: A -> B.Octets -> A, -R: Type, k: (T & Result<&2, &2, D.DevError, A>) -> IO.OP<R>, d: T, res: Result<&2, &2, D.DevError, B.Octets>, acc: A, +p: Nat, +first: Nat) -> IO.OP<R>:
  V.IODev.fold.then(~A, ~T, (d, res), acc, d2 => a => blk => R2 => k2 => V.IODev.fold_blocks(~A, ~T, ~V.IODev.of_pure_read(~T, ~read_block), ~step, p, d2, Nat.add(first, 1n), step(a, blk))(R2, x => k2(x)))(R, k)

def IWP.fstep(~A: Data, ~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~step: A -> B.Octets -> A, -R: Type, -k: (T & Result<&2, &2, D.DevError, A>) -> IO.OP<R>, +d: T, res: Result<&2, &2, D.DevError, B.Octets>, +acc: A, +p: Nat, +first: Nat, ih: @acc2: A -> @-k2: ((T & Result<&2, &2, D.DevError, A>) -> IO.OP<R>) -> {V.IODev.fold_blocks(~A, ~T, ~V.IODev.of_pure_read(~T, ~read_block), ~step, p, d, Nat.add(first, 1n), acc2)(R, k2) == k2((d, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, acc2), D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n))))) : IO.OP<R>}) -> {IWP.fold_tail(~A, ~T, ~read_block, ~step, R, k, d, res, acc, p, first) == k((d, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, acc), Result.bind(&2, &2, D.DevError, B.Octets, List<&2, B.Octets>, res, blk => Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest})))))) : IO.OP<R>}:
  match res:
    case Done{+blk}:
      +rl = D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n))
      Equal.trans(IO.OP<R>, V.IODev.fold_blocks(~A, ~T, ~V.IODev.of_pure_read(~T, ~read_block), ~step, p, d, Nat.add(first, 1n), step(acc, blk))(R, x => k(x)), k((d, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, step(acc, blk)), rl))), k((d, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, acc), Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, rl, rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest}))))), ih(step(acc, blk), x => k(x)), Equal.cong(Result<&2, &2, D.DevError, A>, IO.OP<R>, z => k((d, z)), Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, step(acc, blk)), rl), Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, acc), Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, rl, rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest}))), IWP.fmap(~A, ~step, blk, acc, rl)))
    case Fail{e}:
      {==}

def IWP.fold(~A: Data, ~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~step: A -> B.Octets -> A, -R: Type, -k: (T & Result<&2, &2, D.DevError, A>) -> IO.OP<R>, count: Nat, +d: T, +first: Nat, +acc: A) -> {V.IODev.fold_blocks(~A, ~T, ~V.IODev.of_pure_read(~T, ~read_block), ~step, count, d, first, acc)(R, k) == k((d, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, A, xs => Laws.fold_list(~A, ~step, xs, acc), D.Dev.read_list(~T, ~read_block, d, count, first)))) : IO.OP<R>}:
  match count:
    case 0n:
      {==}
    case 1n+ +p:
      IWP.fstep(~A, ~T, ~read_block, ~step, R, x => k(x), d, read_block(d, first), acc, p, first, acc2 => k2 => IWP.fold(~A, ~T, ~read_block, ~step, R, x => k2(x), p, d, Nat.add(first, 1n), acc2))

def Laws.io_fold_blocks(A, D, read_block, step, R, k, d, count, first, acc):
  IWP.fold(~A, ~D, ~read_block, ~step, R, k, count, d, first, acc)

# write_blocks on IOMem: the device after count block writes

def IWP.wb(count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets) -> D.MemDev:
  match count:
    case 0n:
      d
    case 1n+p:
      IWP.wb(p, D.MemDev.update(d, j, B.Octets.take(bs, data)), bs, Nat.add(j, 1n), B.Octets.drop(bs, data))

def IWP.wtail(-R: Type, k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, r: D.MemDev & Result<&2, &2, D.DevError, Unit>, +p: Nat, +bs: Nat, +j: Nat, +rest: B.Octets) -> IO.OP<R>:
  V.IODev.unit_then(~D.MemDev, r, d2 => R2 => k2 => V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, p, d2, bs, Nat.add(j, 1n), rest)(R2, x => k2(x)))(R, k)

def IWP.take_len(+bs: Nat, +p: Nat, +data: B.Octets, +hl: {B.Octets.len(data) == Nat.mul(1n+p, bs) : Nat}) -> {B.Octets.len(B.Octets.take(bs, data)) == bs : Nat}:
  BL.octets_len_take_le(bs, data, P.IOP.le_rw_r(bs, B.Octets.len(data), Nat.add(bs, Nat.mul(p, bs)), hl, P.IOP.le_add_r(bs, Nat.mul(p, bs))))

def IWP.drop_len(+bs: Nat, +p: Nat, +data: B.Octets, +hl: {B.Octets.len(data) == Nat.mul(1n+p, bs) : Nat}) -> {B.Octets.len(B.Octets.drop(bs, data)) == Nat.mul(p, bs) : Nat}:
  Equal.trans(Nat, B.Octets.len(B.Octets.drop(bs, data)), Nat.sub(B.Octets.len(data), bs), Nat.mul(p, bs), BL.octets_len_drop(bs, data), Equal.trans(Nat, Nat.sub(B.Octets.len(data), bs), Nat.sub(Nat.add(bs, Nat.mul(p, bs)), bs), Nat.mul(p, bs), Equal.cong(Nat, Nat, x => Nat.sub(x, bs), B.Octets.len(data), Nat.add(bs, Nat.mul(p, bs)), hl), IWP.add_sub_l(bs, Nat.mul(p, bs))))

def IWP.wrun(-R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, +count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets, +c: Nat, +hbs: {D.MemDev.block_size(d) == bs : Nat}, +hc: {D.MemDev.block_count(d) == c : Nat}, +hr: {Nat.is_le(Nat.add(count, j), c) == True{} : Bool}, +hl: {B.Octets.len(data) == Nat.mul(count, bs) : Nat}) -> {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, bs, j, data)(R, k) == k((IWP.wb(count, d, bs, j, data), Done{Unit{}})) : IO.OP<R>}:
  match count:
    case 0n:
      {==}
    case 1n+ +p:
      +tk = B.Octets.take(bs, data)
      +dr = B.Octets.drop(bs, data)
      +u = D.MemDev.update(d, j, tk)
      +len_ok = IWP.eq_of(B.Octets.len(tk), D.MemDev.block_size(d), Equal.trans(Nat, B.Octets.len(tk), bs, D.MemDev.block_size(d), IWP.take_len(bs, p, data, hl), Equal.sym(Nat, D.MemDev.block_size(d), bs, hbs)))
      +in_range = P.IOP.lt_rw_r(j, D.MemDev.block_count(d), c, hc, IWP.lt_of_range(p, j, c, hr))
      %Equal.sym(D.MemDev & Result<&2, &2, D.DevError, Unit>, D.MemDev.own_write_block(d, j, tk), (u, Done{Unit{}}), BDL.own_write_ok(d, j, tk, len_ok, in_range)) : {IWP.wtail(R, k, _, p, bs, j, dr) == k((IWP.wb(1n+p, d, bs, j, data), Done{Unit{}})) : IO.OP<R>}
      IWP.wrun(R, x => k(x), p, u, bs, Nat.add(j, 1n), dr, c, Equal.trans(Nat, D.MemDev.block_size(u), D.MemDev.block_size(d), bs, BDL.update_keeps_size(d, j, tk), hbs), Equal.trans(Nat, D.MemDev.block_count(u), D.MemDev.block_count(d), c, BDL.update_keeps_count(d, j, tk), hc), P.IOP.le_rw_l(Nat.add(p, Nat.add(j, 1n)), 1n+Nat.add(p, j), c, IWP.add_one_r(p, j), hr), IWP.drop_len(bs, p, data, hl))

def IWP.wb_size(+count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets) -> {D.MemDev.block_size(IWP.wb(count, d, bs, j, data)) == D.MemDev.block_size(d) : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+ +p:
      +u = D.MemDev.update(d, j, B.Octets.take(bs, data))
      Equal.trans(Nat, D.MemDev.block_size(IWP.wb(p, u, bs, Nat.add(j, 1n), B.Octets.drop(bs, data))), D.MemDev.block_size(u), D.MemDev.block_size(d), IWP.wb_size(p, u, bs, Nat.add(j, 1n), B.Octets.drop(bs, data)), BDL.update_keeps_size(d, j, B.Octets.take(bs, data)))

def IWP.wb_count(+count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets) -> {D.MemDev.block_count(IWP.wb(count, d, bs, j, data)) == D.MemDev.block_count(d) : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+ +p:
      +u = D.MemDev.update(d, j, B.Octets.take(bs, data))
      Equal.trans(Nat, D.MemDev.block_count(IWP.wb(p, u, bs, Nat.add(j, 1n), B.Octets.drop(bs, data))), D.MemDev.block_count(u), D.MemDev.block_count(d), IWP.wb_count(p, u, bs, Nat.add(j, 1n), B.Octets.drop(bs, data)), BDL.update_keeps_count(d, j, B.Octets.take(bs, data)))

def IWP.wb_valid(+count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}) -> {D.MemDev.valid(IWP.wb(count, d, bs, j, data)) == True{} : Bool}:
  match count:
    case 0n:
      hv
    case 1n+ +p:
      IWP.wb_valid(p, D.MemDev.update(d, j, B.Octets.take(bs, data)), bs, Nat.add(j, 1n), B.Octets.drop(bs, data), BRL.valid_update(d, j, B.Octets.take(bs, data), hv))

def IWP.wb_shape(+count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}) -> {Laws.shape(IWP.wb(count, d, bs, j, data)) == Laws.shape(d) : Bool & (Nat & Nat)}:
  +w = IWP.wb(count, d, bs, j, data)
  %Equal.sym(Bool, D.MemDev.valid(w), True{}, IWP.wb_valid(count, d, bs, j, data, hv)) : {(_, (D.MemDev.block_size(w), D.MemDev.block_count(w))) == (D.MemDev.valid(d), (D.MemDev.block_size(d), D.MemDev.block_count(d))) : Bool & (Nat & Nat)}
  %Equal.sym(Bool, D.MemDev.valid(d), True{}, hv) : {(True{}, (D.MemDev.block_size(w), D.MemDev.block_count(w))) == (_, (D.MemDev.block_size(d), D.MemDev.block_count(d))) : Bool & (Nat & Nat)}
  %Equal.sym(Nat, D.MemDev.block_size(w), D.MemDev.block_size(d), IWP.wb_size(count, d, bs, j, data)) : {(True{}, (_, D.MemDev.block_count(w))) == (True{}, (D.MemDev.block_size(d), D.MemDev.block_count(d))) : Bool & (Nat & Nat)}
  %Equal.sym(Nat, D.MemDev.block_count(w), D.MemDev.block_count(d), IWP.wb_count(count, d, bs, j, data)) : {(True{}, (D.MemDev.block_size(d), _)) == (True{}, (D.MemDev.block_size(d), D.MemDev.block_count(d))) : Bool & (Nat & Nat)}
  {==}

# the image's length, with the block size and count named
def IWP.img_len(+d: D.MemDev, +bs: Nat, +c: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hbs: {D.MemDev.block_size(d) == bs : Nat}, +hc: {D.MemDev.block_count(d) == c : Nat}) -> {B.Octets.len(D.MemDev.to_octets(d)) == Nat.mul(c, bs) : Nat}:
  %hc : {B.Octets.len(D.MemDev.to_octets(d)) == Nat.mul(_, bs) : Nat}
  %hbs : {B.Octets.len(D.MemDev.to_octets(d)) == Nat.mul(D.MemDev.block_count(d), _) : Nat}
  BRL.to_octets_len(d, hv)

def IWP.wb_img(+count: Nat, +d: D.MemDev, +bs: Nat, +j: Nat, +data: B.Octets, +c: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hbs: {D.MemDev.block_size(d) == bs : Nat}, +hc: {D.MemDev.block_count(d) == c : Nat}, +hr: {Nat.is_le(Nat.add(count, j), c) == True{} : Bool}, +hl: {B.Octets.len(data) == Nat.mul(count, bs) : Nat}) -> {D.MemDev.to_octets(IWP.wb(count, d, bs, j, data)) == D.Dev.patch(Nat.mul(j, bs), data, D.MemDev.to_octets(d)) : B.Octets}:
  match count:
    case 0n:
      %Equal.sym(B.Octets, data, B.Octets.empty(), IWP.len0(data, hl)) : {D.MemDev.to_octets(d) == D.Dev.patch(Nat.mul(j, bs), _, D.MemDev.to_octets(d)) : B.Octets}
      Equal.sym(B.Octets, D.Dev.patch(Nat.mul(j, bs), B.Octets.empty(), D.MemDev.to_octets(d)), D.MemDev.to_octets(d), IWP.patch_nil(Nat.mul(j, bs), D.MemDev.to_octets(d)))
    case 1n+ +p:
      +tk = B.Octets.take(bs, data)
      +dr = B.Octets.drop(bs, data)
      +u = D.MemDev.update(d, j, tk)
      +img = D.MemDev.to_octets(d)
      +ltk = IWP.take_len(bs, p, data, hl)
      +len_ok = IWP.eq_of(B.Octets.len(tk), D.MemDev.block_size(d), Equal.trans(Nat, B.Octets.len(tk), bs, D.MemDev.block_size(d), ltk, Equal.sym(Nat, D.MemDev.block_size(d), bs, hbs)))
      +hjc = IWP.lt_of_range(p, j, c, hr)
      +in_range = P.IOP.lt_rw_r(j, D.MemDev.block_count(d), c, hc, hjc)
      +ih = IWP.wb_img(p, u, bs, Nat.add(j, 1n), dr, c, BRL.valid_update(d, j, tk, hv), Equal.trans(Nat, D.MemDev.block_size(u), D.MemDev.block_size(d), bs, BDL.update_keeps_size(d, j, tk), hbs), Equal.trans(Nat, D.MemDev.block_count(u), D.MemDev.block_count(d), c, BDL.update_keeps_count(d, j, tk), hc), P.IOP.le_rw_l(Nat.add(p, Nat.add(j, 1n)), 1n+Nat.add(p, j), c, IWP.add_one_r(p, j), hr), IWP.drop_len(bs, p, data, hl))
      +eu = BRL.to_octets_update(d, j, tk, hv, len_ok, in_range)
      +e1 = Equal.trans(Nat, Nat.mul(Nat.add(j, 1n), bs), Nat.add(Nat.mul(j, bs), Nat.mul(1n, bs)), Nat.add(Nat.mul(j, bs), B.Octets.len(tk)), P.IOP.mul_add(j, 1n, bs), Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(j, bs), x), Nat.mul(1n, bs), B.Octets.len(tk), Equal.trans(Nat, Nat.mul(1n, bs), bs, B.Octets.len(tk), P.IOP.add_zero(bs), Equal.sym(Nat, B.Octets.len(tk), bs, ltk))))
      +hj = P.IOP.le_rw_r(Nat.mul(j, bs), B.Octets.len(img), Nat.mul(c, bs), IWP.img_len(d, bs, c, hv, hbs, hc), IWP.mul_mono(j, c, bs, IWP.lt_to_le(j, c, hjc)))
      %Equal.sym(B.Octets, D.MemDev.to_octets(IWP.wb(p, u, bs, Nat.add(j, 1n), dr)), D.Dev.patch(Nat.mul(Nat.add(j, 1n), bs), dr, D.MemDev.to_octets(u)), ih) : {_ == D.Dev.patch(Nat.mul(j, bs), data, img) : B.Octets}
      %Equal.sym(B.Octets, D.MemDev.to_octets(u), D.Dev.patch(Nat.mul(j, D.MemDev.block_size(d)), tk, img), eu) : {D.Dev.patch(Nat.mul(Nat.add(j, 1n), bs), dr, _) == D.Dev.patch(Nat.mul(j, bs), data, img) : B.Octets}
      %Equal.sym(Nat, D.MemDev.block_size(d), bs, hbs) : {D.Dev.patch(Nat.mul(Nat.add(j, 1n), bs), dr, D.Dev.patch(Nat.mul(j, _), tk, img)) == D.Dev.patch(Nat.mul(j, bs), data, img) : B.Octets}
      %Equal.sym(Nat, Nat.mul(Nat.add(j, 1n), bs), Nat.add(Nat.mul(j, bs), B.Octets.len(tk)), e1) : {D.Dev.patch(_, dr, D.Dev.patch(Nat.mul(j, bs), tk, img)) == D.Dev.patch(Nat.mul(j, bs), data, img) : B.Octets}
      %Equal.sym(B.Octets, D.Dev.patch(Nat.add(Nat.mul(j, bs), B.Octets.len(tk)), dr, D.Dev.patch(Nat.mul(j, bs), tk, img)), D.Dev.patch(Nat.mul(j, bs), B.Octets.append(tk, dr), img), BRL.patch_patch(Nat.mul(j, bs), tk, dr, img, hj)) : {_ == D.Dev.patch(Nat.mul(j, bs), data, img) : B.Octets}
      Equal.cong(B.Octets, B.Octets, x => D.Dev.patch(Nat.mul(j, bs), x, img), B.Octets.append(tk, dr), data, BL.octets_take_drop(bs, data))

# the laws for write_blocks

def IWP.wbl(-R: Type, -k: (Result<&2, &2, D.DevError, Unit> & B.Octets) -> IO.OP<R>, +d: D.MemDev, +count: Nat, +first: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}, +hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}) -> {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, D.MemDev.block_size(d), first, data)(R, x => k(Laws.outcome(x))) == k((Done{Unit{}}, D.Dev.patch(Nat.mul(first, D.MemDev.block_size(d)), data, D.MemDev.to_octets(d)))) : IO.OP<R>}:
  +bs = D.MemDev.block_size(d)
  +c = D.MemDev.block_count(d)
  +hr2 = P.IOP.le_rw_l(Nat.add(count, first), Nat.add(first, count), c, P.IOP.add_comm(count, first), hr)
  +w = IWP.wb(count, d, bs, first, data)
  Equal.trans(IO.OP<R>, V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, bs, first, data)(R, x => k(Laws.outcome(x))), k(Laws.outcome((w, Done{Unit{}}))), k((Done{Unit{}}, D.Dev.patch(Nat.mul(first, bs), data, D.MemDev.to_octets(d)))), IWP.wrun(R, x => k(Laws.outcome(x)), count, d, bs, first, data, c, {==}, {==}, hr2, hl), Equal.cong(B.Octets, IO.OP<R>, z => k((Done{Unit{}}, z)), D.MemDev.to_octets(w), D.Dev.patch(Nat.mul(first, bs), data, D.MemDev.to_octets(d)), IWP.wb_img(count, d, bs, first, data, c, hv, {==}, {==}, hr2, hl)))

def Laws.io_mem_write_blocks(R, k, d, count, first, data, hv, hr, hl):
  IWP.wbl(R, k, d, count, first, data, hv, hr, hl)

def IWP.wbs(-R: Type, -k: (Bool & (Nat & Nat)) -> IO.OP<R>, +d: D.MemDev, +count: Nat, +first: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}, +hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}) -> {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, D.MemDev.block_size(d), first, data)(R, x => k(Laws.shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))) == k(Laws.shape(d)) : IO.OP<R>}:
  +bs = D.MemDev.block_size(d)
  +c = D.MemDev.block_count(d)
  +hr2 = P.IOP.le_rw_l(Nat.add(count, first), Nat.add(first, count), c, P.IOP.add_comm(count, first), hr)
  +w = IWP.wb(count, d, bs, first, data)
  Equal.trans(IO.OP<R>, V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, bs, first, data)(R, x => k(Laws.shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))), k(Laws.shape(w)), k(Laws.shape(d)), IWP.wrun(R, x => k(Laws.shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x))), count, d, bs, first, data, c, {==}, {==}, hr2, hl), Equal.cong(Bool & (Nat & Nat), IO.OP<R>, z => k(z), Laws.shape(w), Laws.shape(d), IWP.wb_shape(count, d, bs, first, data, hv)))

def Laws.io_mem_write_blocks_shape(R, k, d, count, first, data, hv, hr, hl):
  IWP.wbs(R, k, d, count, first, data, hv, hr, hl)

def IWP.wb_read(+d: D.MemDev, +count: Nat, +first: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}, +hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}) -> {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, IWP.wb(count, d, D.MemDev.block_size(d), first, data), count, first) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}:
  +bs = D.MemDev.block_size(d)
  +c = D.MemDev.block_count(d)
  +img = D.MemDev.to_octets(d)
  +hr2 = P.IOP.le_rw_l(Nat.add(count, first), Nat.add(first, count), c, P.IOP.add_comm(count, first), hr)
  +w = IWP.wb(count, d, bs, first, data)
  +hvw = IWP.wb_valid(count, d, bs, first, data, hv)
  +hrw = P.IOP.le_rw_r(Nat.add(first, count), D.MemDev.block_count(w), c, IWP.wb_count(count, d, bs, first, data), hr)
  +hj = P.IOP.le_rw_r(Nat.mul(first, bs), B.Octets.len(img), Nat.mul(c, bs), IWP.img_len(d, bs, c, hv, {==}, {==}), IWP.mul_mono(first, c, bs, P.IOP.le_trans(first, Nat.add(first, count), c, P.IOP.le_add_r(first, count), hr)))
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, w, count, first), Done{B.Octets.slice(Nat.mul(first, D.MemDev.block_size(w)), Nat.mul(count, D.MemDev.block_size(w)), D.MemDev.to_octets(w))}, BRL.read_blocks_mem(w, count, first, hvw, hrw)) : {_ == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(Nat, D.MemDev.block_size(w), bs, IWP.wb_size(count, d, bs, first, data)) : {Done{B.Octets.slice(Nat.mul(first, _), Nat.mul(count, _), D.MemDev.to_octets(w))} == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(B.Octets, D.MemDev.to_octets(w), D.Dev.patch(Nat.mul(first, bs), data, img), IWP.wb_img(count, d, bs, first, data, c, hv, {==}, {==}, hr2, hl)) : {Done{B.Octets.slice(Nat.mul(first, bs), Nat.mul(count, bs), _)} == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  %hl : {Done{B.Octets.slice(Nat.mul(first, bs), _, D.Dev.patch(Nat.mul(first, bs), data, img))} == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, x => Done{x}, B.Octets.slice(Nat.mul(first, bs), B.Octets.len(data), D.Dev.patch(Nat.mul(first, bs), data, img)), data, BRL.patch_slice(Nat.mul(first, bs), data, img, hj))

def IWP.wbr(-R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, +d: D.MemDev, +count: Nat, +first: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}, +hl: {B.Octets.len(data) == Nat.mul(count, D.MemDev.block_size(d)) : Nat}) -> {V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, D.MemDev.block_size(d), first, data)(R, x => V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), first)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == k(Done{data}) : IO.OP<R>}:
  +bs = D.MemDev.block_size(d)
  +c = D.MemDev.block_count(d)
  +hr2 = P.IOP.le_rw_l(Nat.add(count, first), Nat.add(first, count), c, P.IOP.add_comm(count, first), hr)
  +w = IWP.wb(count, d, bs, first, data)
  Equal.trans(IO.OP<R>, V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d, bs, first, data)(R, x => V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), first)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))), V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, w, first)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), k(Done{data}), IWP.wrun(R, x => V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), first)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), count, d, bs, first, data, c, {==}, {==}, hr2, hl), Equal.trans(IO.OP<R>, V.IODev.read_blocks(~D.MemDev, ~M.IOMem.read_block, count, w, first)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), k(D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, w, count, first)), k(Done{data}), IWP.read_blocks(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)), count, w, first), Equal.cong(Result<&2, &2, D.DevError, B.Octets>, IO.OP<R>, z => k(z), D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, w, count, first), Done{data}, IWP.wb_read(d, count, first, data, hv, hr, hl))))

def Laws.io_mem_write_blocks_read(R, k, d, count, first, data, hv, hr, hl):
  IWP.wbr(R, k, d, count, first, data, hv, hr, hl)

# write_bytes on IOMem: the blocks around the data are read, then its
# span is written whole

def IWP.nz(+n: Nat, +h: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {n == 1n+P.IOP.pred(n) : Nat}:
  match n:
    case 0n:
      P.IOP.ex_falso({0n == 1n+P.IOP.pred(0n) : Nat}, P.IOP.bool_clash(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+ +q:
      {==}

def IWP.concat3(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.concat([a, b, c]) == B.Octets.append(a, B.Octets.append(b, c)) : B.Octets}:
  Equal.trans(B.Octets, B.Octets.concat([a, b, c]), B.Octets.append(a, B.Octets.concat([b, c])), B.Octets.append(a, B.Octets.append(b, c)), BL.octets_concat_cons(a, [b, c]), Equal.cong(B.Octets, B.Octets, x => B.Octets.append(a, x), B.Octets.concat([b, c]), B.Octets.append(b, c), Equal.trans(B.Octets, B.Octets.concat([b, c]), B.Octets.append(b, B.Octets.concat([c])), B.Octets.append(b, c), BL.octets_concat_cons(b, [c]), Equal.cong(B.Octets, B.Octets, y => B.Octets.append(b, y), B.Octets.concat([c]), c, Equal.trans(B.Octets, B.Octets.concat([c]), B.Octets.append(c, B.Octets.concat(Nil{})), c, BL.octets_concat_cons(c, Nil{}), BL.octets_append_empty_r(c))))))

# a block n < c of a c-block image lies inside it
def IWP.blk_in(+n: Nat, +bs: Nat, +c: Nat, +img: B.Octets, +hlen: {B.Octets.len(img) == Nat.mul(c, bs) : Nat}, +h: {Nat.is_lt(n, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mul(n, bs), bs), B.Octets.len(img)) == True{} : Bool}:
  P.IOP.le_rw_l(Nat.add(Nat.mul(n, bs), bs), Nat.add(bs, Nat.mul(n, bs)), B.Octets.len(img), P.IOP.add_comm(Nat.mul(n, bs), bs), P.IOP.le_rw_r(Nat.add(bs, Nat.mul(n, bs)), B.Octets.len(img), Nat.mul(c, bs), hlen, IWP.mul_mono(1n+n, c, bs, P.IOP.lt_le(n, c, h))))

# the bytes kept from the first block, and from the last
def IWP.head_eq(+x: Nat, +bs: Nat, +ks: Nat, +img: B.Octets, +hks: {Nat.is_lt(ks, bs) == True{} : Bool}) -> {B.Octets.take(ks, B.Octets.slice(x, bs, img)) == B.Octets.slice(x, ks, img) : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.take(ks, B.Octets.take(bs, B.Octets.drop(x, img))), B.Octets.take(Nat.min(ks, bs), B.Octets.drop(x, img)), BL.octets_take_take(ks, bs, B.Octets.drop(x, img))) : {_ == B.Octets.slice(x, ks, img) : B.Octets}
  %Equal.sym(Nat, Nat.min(ks, bs), ks, IWP.min_l(ks, bs, IWP.lt_to_le(ks, bs, hks))) : {B.Octets.take(_, B.Octets.drop(x, img)) == B.Octets.slice(x, ks, img) : B.Octets}
  {==}

def IWP.tail_eq(+y: Nat, +bs: Nat, +ls: Nat, +img: B.Octets, +hls: {Nat.is_lt(ls, bs) == True{} : Bool}) -> {B.Octets.drop(Nat.sub(bs, ls), B.Octets.slice(y, bs, img)) == B.Octets.slice(Nat.add(y, Nat.sub(bs, ls)), ls, img) : B.Octets}:
  +m = Nat.sub(bs, ls)
  %Equal.sym(B.Octets, B.Octets.drop(m, B.Octets.take(bs, B.Octets.drop(y, img))), B.Octets.take(Nat.sub(bs, m), B.Octets.drop(m, B.Octets.drop(y, img))), BL.octets_drop_take_comm(m, bs, B.Octets.drop(y, img))) : {_ == B.Octets.slice(Nat.add(y, m), ls, img) : B.Octets}
  %Equal.sym(Nat, Nat.sub(bs, m), ls, IWP.sub_sub(bs, ls, IWP.lt_to_le(ls, bs, hls))) : {B.Octets.take(_, B.Octets.drop(m, B.Octets.drop(y, img))) == B.Octets.slice(Nat.add(y, m), ls, img) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(m, B.Octets.drop(y, img)), B.Octets.drop(Nat.add(y, m), img), BL.octets_drop_drop(y, m, img)) : {B.Octets.take(ls, _) == B.Octets.slice(Nat.add(y, m), ls, img) : B.Octets}
  {==}

# the length of the span's blocks as written
def IWP.buf_len(+bs: Nat, +ks: Nat, +ls: Nat, +cs: Nat, +h: B.Octets, +t: B.Octets, +data: B.Octets, +hh: {B.Octets.len(h) == bs : Nat}, +ht: {B.Octets.len(t) == bs : Nat}, +hks: {Nat.is_lt(ks, bs) == True{} : Bool}, +hls: {Nat.is_lt(ls, bs) == True{} : Bool}, +hcov: {Nat.mul(cs, bs) == Nat.add(Nat.add(ks, B.Octets.len(data)), ls) : Nat}) -> {B.Octets.len(B.Octets.concat([B.Octets.take(ks, h), data, B.Octets.drop(Nat.sub(bs, ls), t)])) == Nat.mul(cs, bs) : Nat}:
  +a = B.Octets.take(ks, h)
  +z = B.Octets.drop(Nat.sub(bs, ls), t)
  +la = BL.octets_len_take_le(ks, h, P.IOP.le_rw_r(ks, B.Octets.len(h), bs, hh, IWP.lt_to_le(ks, bs, hks)))
  +lz = Equal.trans(Nat, B.Octets.len(z), Nat.sub(B.Octets.len(t), Nat.sub(bs, ls)), ls, BL.octets_len_drop(Nat.sub(bs, ls), t), Equal.trans(Nat, Nat.sub(B.Octets.len(t), Nat.sub(bs, ls)), Nat.sub(bs, Nat.sub(bs, ls)), ls, Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.sub(bs, ls)), B.Octets.len(t), bs, ht), IWP.sub_sub(bs, ls, IWP.lt_to_le(ls, bs, hls))))
  %Equal.sym(B.Octets, B.Octets.concat([a, data, z]), B.Octets.append(a, B.Octets.append(data, z)), IWP.concat3(a, data, z)) : {B.Octets.len(_) == Nat.mul(cs, bs) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(a, B.Octets.append(data, z))), Nat.add(B.Octets.len(a), B.Octets.len(B.Octets.append(data, z))), BL.octets_len_append(a, B.Octets.append(data, z))) : {_ == Nat.mul(cs, bs) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(data, z)), Nat.add(B.Octets.len(data), B.Octets.len(z)), BL.octets_len_append(data, z)) : {Nat.add(B.Octets.len(a), _) == Nat.mul(cs, bs) : Nat}
  %Equal.sym(Nat, B.Octets.len(a), ks, la) : {Nat.add(_, Nat.add(B.Octets.len(data), B.Octets.len(z))) == Nat.mul(cs, bs) : Nat}
  %Equal.sym(Nat, B.Octets.len(z), ls, lz) : {Nat.add(ks, Nat.add(B.Octets.len(data), _)) == Nat.mul(cs, bs) : Nat}
  %Equal.sym(Nat, Nat.mul(cs, bs), Nat.add(Nat.add(ks, B.Octets.len(data)), ls), hcov) : {Nat.add(ks, Nat.add(B.Octets.len(data), ls)) == _ : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(ks, B.Octets.len(data)), ls), Nat.add(ks, Nat.add(B.Octets.len(data), ls)), P.IOP.add_assoc(ks, B.Octets.len(data), ls))

# the last block's kept bytes start where the data ends:
# (fb + cp * bs) + (bs - ls) == (fb + ks) + L, when (1 + cp) * bs == (ks + L) + ls
def IWP.tail_off(+fb: Nat, +cp: Nat, +bs: Nat, +ks: Nat, +l: Nat, +ls: Nat, +hcov: {Nat.mul(1n+cp, bs) == Nat.add(Nat.add(ks, l), ls) : Nat}, +hls: {Nat.is_lt(ls, bs) == True{} : Bool}) -> {Nat.add(Nat.add(fb, Nat.mul(cp, bs)), Nat.sub(bs, ls)) == Nat.add(Nat.add(fb, ks), l) : Nat}:
  +x = Nat.mul(cp, bs)
  +m = Nat.sub(bs, ls)
  +ebs = P.IOP.sub_add(bs, ls, P.IOP.lt_up(ls, bs, hls))
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(x, m), ls), Nat.add(x, Nat.add(m, ls)), Nat.add(Nat.add(ks, l), ls), P.IOP.add_assoc(x, m, ls), Equal.trans(Nat, Nat.add(x, Nat.add(m, ls)), Nat.add(x, bs), Nat.add(Nat.add(ks, l), ls), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(m, ls), bs, ebs), Equal.trans(Nat, Nat.add(x, bs), Nat.add(bs, x), Nat.add(Nat.add(ks, l), ls), P.IOP.add_comm(x, bs), hcov)))
  +e2 = P.IOP.add_cancel(ls, Nat.add(x, m), Nat.add(ks, l), e1)
  Equal.trans(Nat, Nat.add(Nat.add(fb, x), m), Nat.add(fb, Nat.add(x, m)), Nat.add(Nat.add(fb, ks), l), P.IOP.add_assoc(fb, x, m), Equal.trans(Nat, Nat.add(fb, Nat.add(x, m)), Nat.add(fb, Nat.add(ks, l)), Nat.add(Nat.add(fb, ks), l), Equal.cong(Nat, Nat, z => Nat.add(fb, z), Nat.add(x, m), Nat.add(ks, l), e2), Equal.sym(Nat, Nat.add(Nat.add(fb, ks), l), Nat.add(fb, Nat.add(ks, l)), P.IOP.add_assoc(fb, ks, l))))

# the patched span lies inside the image
def IWP.keep_le(+f: Nat, +cs: Nat, +bs: Nat, +ks: Nat, +l: Nat, +ls: Nat, +c: Nat, +img: B.Octets, +hcov: {Nat.mul(cs, bs) == Nat.add(Nat.add(ks, l), ls) : Nat}, +hw: {Nat.is_le(Nat.add(f, cs), c) == True{} : Bool}, +hlen: {B.Octets.len(img) == Nat.mul(c, bs) : Nat}) -> {Nat.is_le(Nat.add(Nat.add(Nat.add(Nat.mul(f, bs), ks), l), ls), B.Octets.len(img)) == True{} : Bool}:
  +fb = Nat.mul(f, bs)
  +e = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(fb, ks), l), ls), Nat.add(Nat.add(fb, Nat.add(ks, l)), ls), Nat.mul(Nat.add(f, cs), bs), Equal.cong(Nat, Nat, z => Nat.add(z, ls), Nat.add(Nat.add(fb, ks), l), Nat.add(fb, Nat.add(ks, l)), P.IOP.add_assoc(fb, ks, l)), Equal.trans(Nat, Nat.add(Nat.add(fb, Nat.add(ks, l)), ls), Nat.add(fb, Nat.add(Nat.add(ks, l), ls)), Nat.mul(Nat.add(f, cs), bs), P.IOP.add_assoc(fb, Nat.add(ks, l), ls), Equal.trans(Nat, Nat.add(fb, Nat.add(Nat.add(ks, l), ls)), Nat.add(fb, Nat.mul(cs, bs)), Nat.mul(Nat.add(f, cs), bs), Equal.cong(Nat, Nat, z => Nat.add(fb, z), Nat.add(Nat.add(ks, l), ls), Nat.mul(cs, bs), Equal.sym(Nat, Nat.mul(cs, bs), Nat.add(Nat.add(ks, l), ls), hcov)), Equal.sym(Nat, Nat.mul(Nat.add(f, cs), bs), Nat.add(fb, Nat.mul(cs, bs)), P.IOP.mul_add(f, cs, bs)))))
  P.IOP.le_rw_l(Nat.add(Nat.add(Nat.add(fb, ks), l), ls), Nat.mul(Nat.add(f, cs), bs), B.Octets.len(img), e, P.IOP.le_rw_r(Nat.mul(Nat.add(f, cs), bs), B.Octets.len(img), Nat.mul(c, bs), hlen, IWP.mul_mono(Nat.add(f, cs), c, bs, hw)))

# a block of a valid device, with its block size named
def IWP.rb(+d: D.MemDev, +n: Nat, +bp: Nat, +ebs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +h: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}) -> {D.MemDev.read_block(d, n) == Done{B.Octets.slice(Nat.mul(n, 1n+bp), 1n+bp, D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}:
  %ebs : {D.MemDev.read_block(d, n) == Done{B.Octets.slice(Nat.mul(n, _), _, D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}
  BRL.read_block_mem(d, n, hv, h)

# The device a write of data at off leaves (e: whether data is empty; the
# block size is 1 + bp when it is not)

def IWP.buf(+d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets) -> B.Octets:
  +bs : Nat = 1n+bp
  +s = S.IOSpan.of(bs, off, B.Octets.len(data))
  +first = S.IOSpan.first(s)
  +count = S.IOSpan.count(s)
  +img = D.MemDev.to_octets(d)
  B.Octets.concat([B.Octets.take(S.IOSpan.skip(s), B.Octets.slice(Nat.mul(first, bs), bs, img)), data, B.Octets.drop(Nat.sub(bs, S.IOSpan.slack(s)), B.Octets.slice(Nat.mul(Nat.add(first, Nat.sub(count, 1n)), bs), bs, img))])

def IWP.wdev(e: Bool, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets) -> D.MemDev:
  match e:
    case True{}:
      d
    case False{}:
      +s = S.IOSpan.of(1n+bp, off, B.Octets.len(data))
      IWP.wb(S.IOSpan.count(s), d, 1n+bp, S.IOSpan.first(s), IWP.buf(d, bp, off, data))

# the two edges of the run, as write_bytes.go writes them
def IWP.r2(-R: Type, k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, r2: D.MemDev & Result<&2, &2, D.DevError, B.Octets>, +head: B.Octets, +bp: Nat, +off: Nat, +data: B.Octets) -> IO.OP<R>:
  +bs : Nat = 1n+bp
  +s = S.IOSpan.of(bs, off, B.Octets.len(data))
  +first = S.IOSpan.first(s)
  +count = S.IOSpan.count(s)
  V.IODev.write_bytes.edge(~D.MemDev, r2, d2 => tail => V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d2, bs, first, B.Octets.concat([B.Octets.take(S.IOSpan.skip(s), head), data, B.Octets.drop(Nat.sub(bs, S.IOSpan.slack(s)), tail)])))(R, k)

def IWP.r1(-R: Type, k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, r1: D.MemDev & Result<&2, &2, D.DevError, B.Octets>, +bp: Nat, +off: Nat, +data: B.Octets) -> IO.OP<R>:
  +bs : Nat = 1n+bp
  +s = S.IOSpan.of(bs, off, B.Octets.len(data))
  +first = S.IOSpan.first(s)
  +count = S.IOSpan.count(s)
  V.IODev.write_bytes.edge(~D.MemDev, r1, d1 => head => IO.bind(D.MemDev & Result<&2, &2, D.DevError, B.Octets>, D.MemDev & Result<&2, &2, D.DevError, Unit>, M.IOMem.read_block(d1, Nat.add(first, Nat.sub(count, 1n))), r2 => V.IODev.write_bytes.edge(~D.MemDev, r2, d2 => tail => V.IODev.write_blocks(~D.MemDev, ~M.IOMem.write_block, count, d2, bs, first, B.Octets.concat([B.Octets.take(S.IOSpan.skip(s), head), data, B.Octets.drop(Nat.sub(bs, S.IOSpan.slack(s)), tail)])))))(R, k)

# The span facts, for a nonempty write inside a valid device of 1 + bp byte
# blocks

def IWP.f_hr(+d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +ebs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), 1n+bp)) == True{} : Bool}:
  %ebs : {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), _)) == True{} : Bool}
  hr

# count == 1 + pred(count): a nonempty range spans a block
def IWP.f_ecs(+bp: Nat, +off: Nat, +data: B.Octets, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}) -> {S.IOSpan.count(S.IOSpan.of(1n+bp, off, B.Octets.len(data))) == 1n+P.IOP.pred(S.IOSpan.count(S.IOSpan.of(1n+bp, off, B.Octets.len(data)))) : Nat}:
  +l = B.Octets.len(data)
  +sp = S.IOSpan.of(1n+bp, off, l)
  +ks = S.IOSpan.skip(sp)
  +ls = S.IOSpan.slack(sp)
  +cs = S.IOSpan.count(sp)
  +lp = P.IOP.pred(l)
  IWP.succ_of(cs, Nat.add(Nat.add(ks, lp), ls), 1n+bp, Equal.trans(Nat, Nat.mul(cs, 1n+bp), Nat.add(Nat.add(ks, l), ls), 1n+Nat.add(Nat.add(ks, lp), ls), L.span_cover(bp, off, l), Equal.trans(Nat, Nat.add(Nat.add(ks, l), ls), Nat.add(Nat.add(ks, 1n+lp), ls), 1n+Nat.add(Nat.add(ks, lp), ls), Equal.cong(Nat, Nat, x => Nat.add(Nat.add(ks, x), ls), l, 1n+lp, IWP.nz(l, ee)), Equal.cong(Nat, Nat, x => Nat.add(x, ls), Nat.add(ks, 1n+lp), 1n+Nat.add(ks, lp), P.IOP.add_succ(ks, lp)))))

# the last block of the span is first + pred(count)
def IWP.f_last(+f: Nat, +cs: Nat, +ecs: {cs == 1n+P.IOP.pred(cs) : Nat}) -> {Nat.add(f, Nat.sub(cs, 1n)) == Nat.add(f, P.IOP.pred(cs)) : Nat}:
  %Equal.sym(Nat, cs, 1n+P.IOP.pred(cs), ecs) : {Nat.add(f, Nat.sub(_, 1n)) == Nat.add(f, P.IOP.pred(cs)) : Nat}
  Equal.cong(Nat, Nat, x => Nat.add(f, x), Nat.sub(P.IOP.pred(cs), 0n), P.IOP.pred(cs), P.IOP.sub_zero(P.IOP.pred(cs)))

# first + count <= c, with count == 1 + cp, is 1 + (first + cp) <= c
def IWP.f_hfc(+f: Nat, +cs: Nat, +c: Nat, +ecs: {cs == 1n+P.IOP.pred(cs) : Nat}, +hw: {Nat.is_le(Nat.add(f, cs), c) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(f, P.IOP.pred(cs)), c) == True{} : Bool}:
  P.IOP.le_rw_l(1n+Nat.add(f, P.IOP.pred(cs)), Nat.add(f, cs), c, Equal.trans(Nat, 1n+Nat.add(f, P.IOP.pred(cs)), Nat.add(f, 1n+P.IOP.pred(cs)), Nat.add(f, cs), Equal.sym(Nat, Nat.add(f, 1n+P.IOP.pred(cs)), 1n+Nat.add(f, P.IOP.pred(cs)), P.IOP.add_succ(f, P.IOP.pred(cs))), Equal.cong(Nat, Nat, x => Nat.add(f, x), 1n+P.IOP.pred(cs), cs, Equal.sym(Nat, cs, 1n+P.IOP.pred(cs), ecs))), hw)

def IWP.f_inf(+f: Nat, +cp: Nat, +c: Nat, +h: {Nat.is_le(1n+Nat.add(f, cp), c) == True{} : Bool}) -> {Nat.is_lt(f, c) == True{} : Bool}:
  P.IOP.le_lt(f, c, P.IOP.le_trans(1n+f, 1n+Nat.add(f, cp), c, P.IOP.le_add_r(f, cp), h))

# The run of a nonempty write inside a valid device of 1 + bp byte blocks:
# both edge blocks read whole, then the span written
def IWP.wreal(-R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +ebs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes.go(~D.MemDev, ~M.IOMem.read_block, ~M.IOMem.write_block, off, data, (d, 1n+bp))(R, k) == k((IWP.wdev(False{}, d, bp, off, data), Done{Unit{}})) : IO.OP<R>}:
  +bs : Nat = 1n+bp
  +l = B.Octets.len(data)
  +sp = S.IOSpan.of(bs, off, l)
  +f = S.IOSpan.first(sp)
  +ks = S.IOSpan.skip(sp)
  +cs = S.IOSpan.count(sp)
  +ls = S.IOSpan.slack(sp)
  +c = D.MemDev.block_count(d)
  +img = D.MemDev.to_octets(d)
  +cp = P.IOP.pred(cs)
  +last = Nat.add(f, Nat.sub(cs, 1n))
  +hw = L.span_within(bp, off, l, c, IWP.f_hr(d, bp, off, data, ebs, hr))
  +ecs = IWP.f_ecs(bp, off, data, ee)
  +hfc = IWP.f_hfc(f, cs, c, ecs, hw)
  +inf = IWP.f_inf(f, cp, c, hfc)
  +inl = P.IOP.lt_rw_l(last, Nat.add(f, cp), c, IWP.f_last(f, cs, ecs), P.IOP.le_lt(Nat.add(f, cp), c, hfc))
  +hlen = IWP.img_len(d, bs, c, hv, ebs, {==})
  +hd = B.Octets.slice(Nat.mul(f, bs), bs, img)
  +tl = B.Octets.slice(Nat.mul(last, bs), bs, img)
  +hh = BL.octets_len_slice_le(Nat.mul(f, bs), bs, img, IWP.blk_in(f, bs, c, img, hlen, inf))
  +ht = BL.octets_len_slice_le(Nat.mul(last, bs), bs, img, IWP.blk_in(last, bs, c, img, hlen, inl))
  +hlb = IWP.buf_len(bs, ks, ls, cs, hd, tl, data, hh, ht, L.span_skip(bp, off, l), L.span_slack(bp, off, l), L.span_cover(bp, off, l))
  +hrw = P.IOP.le_rw_l(Nat.add(cs, f), Nat.add(f, cs), c, P.IOP.add_comm(cs, f), hw)
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d, f), Done{hd}, IWP.rb(d, f, bp, ebs, hv, inf)) : {IWP.r1(R, k, (d, _), bp, off, data) == k((IWP.wdev(False{}, d, bp, off, data), Done{Unit{}})) : IO.OP<R>}
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d, last), Done{tl}, IWP.rb(d, last, bp, ebs, hv, inl)) : {IWP.r2(R, k, (d, _), hd, bp, off, data) == k((IWP.wdev(False{}, d, bp, off, data), Done{Unit{}})) : IO.OP<R>}
  IWP.wrun(R, k, cs, d, bs, f, IWP.buf(d, bp, off, data), c, ebs, {==}, hrw, hlb)

# its image: the span patched with the bytes around the data as they were,
# which is the data patched alone
def IWP.wreal_img(+d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +ebs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {D.MemDev.to_octets(IWP.wdev(False{}, d, bp, off, data)) == D.Dev.patch(off, data, D.MemDev.to_octets(d)) : B.Octets}:
  +bs : Nat = 1n+bp
  +l = B.Octets.len(data)
  +sp = S.IOSpan.of(bs, off, l)
  +f = S.IOSpan.first(sp)
  +ks = S.IOSpan.skip(sp)
  +cs = S.IOSpan.count(sp)
  +ls = S.IOSpan.slack(sp)
  +c = D.MemDev.block_count(d)
  +img = D.MemDev.to_octets(d)
  +cp = P.IOP.pred(cs)
  +last = Nat.add(f, Nat.sub(cs, 1n))
  +fb = Nat.mul(f, bs)
  +m = Nat.sub(bs, ls)
  +hw = L.span_within(bp, off, l, c, IWP.f_hr(d, bp, off, data, ebs, hr))
  +ecs = IWP.f_ecs(bp, off, data, ee)
  +hfc = IWP.f_hfc(f, cs, c, ecs, hw)
  +inf = IWP.f_inf(f, cp, c, hfc)
  +inl = P.IOP.lt_rw_l(last, Nat.add(f, cp), c, IWP.f_last(f, cs, ecs), P.IOP.le_lt(Nat.add(f, cp), c, hfc))
  +hlen = IWP.img_len(d, bs, c, hv, ebs, {==})
  +hd = B.Octets.slice(fb, bs, img)
  +tl = B.Octets.slice(Nat.mul(last, bs), bs, img)
  +hh = BL.octets_len_slice_le(fb, bs, img, IWP.blk_in(f, bs, c, img, hlen, inf))
  +ht = BL.octets_len_slice_le(Nat.mul(last, bs), bs, img, IWP.blk_in(last, bs, c, img, hlen, inl))
  +hlb = IWP.buf_len(bs, ks, ls, cs, hd, tl, data, hh, ht, L.span_skip(bp, off, l), L.span_slack(bp, off, l), L.span_cover(bp, off, l))
  +hrw = P.IOP.le_rw_l(Nat.add(cs, f), Nat.add(f, cs), c, P.IOP.add_comm(cs, f), hw)
  +buf = IWP.buf(d, bp, off, data)
  +s1 = B.Octets.slice(fb, ks, img)
  +s2 = B.Octets.slice(Nat.add(Nat.add(fb, ks), l), ls, img)
  +hcov1 = Equal.trans(Nat, Nat.mul(1n+cp, bs), Nat.mul(cs, bs), Nat.add(Nat.add(ks, l), ls), Equal.cong(Nat, Nat, x => Nat.mul(x, bs), 1n+cp, cs, Equal.sym(Nat, cs, 1n+cp, ecs)), L.span_cover(bp, off, l))
  +eoff2 = Equal.trans(Nat, Nat.add(Nat.mul(last, bs), m), Nat.add(Nat.add(fb, Nat.mul(cp, bs)), m), Nat.add(Nat.add(fb, ks), l), Equal.cong(Nat, Nat, x => Nat.add(x, m), Nat.mul(last, bs), Nat.add(fb, Nat.mul(cp, bs)), Equal.trans(Nat, Nat.mul(last, bs), Nat.mul(Nat.add(f, cp), bs), Nat.add(fb, Nat.mul(cp, bs)), Equal.cong(Nat, Nat, x => Nat.mul(x, bs), last, Nat.add(f, cp), IWP.f_last(f, cs, ecs)), P.IOP.mul_add(f, cp, bs))), IWP.tail_off(fb, cp, bs, ks, l, ls, hcov1, L.span_slack(bp, off, l)))
  +ebuf = Equal.trans(B.Octets, buf, B.Octets.append(B.Octets.take(ks, hd), B.Octets.append(data, B.Octets.drop(m, tl))), B.Octets.append(s1, B.Octets.append(data, s2)), IWP.concat3(B.Octets.take(ks, hd), data, B.Octets.drop(m, tl)), Equal.trans(B.Octets, B.Octets.append(B.Octets.take(ks, hd), B.Octets.append(data, B.Octets.drop(m, tl))), B.Octets.append(s1, B.Octets.append(data, B.Octets.drop(m, tl))), B.Octets.append(s1, B.Octets.append(data, s2)), Equal.cong(B.Octets, B.Octets, x => B.Octets.append(x, B.Octets.append(data, B.Octets.drop(m, tl))), B.Octets.take(ks, hd), s1, IWP.head_eq(fb, bs, ks, img, L.span_skip(bp, off, l))), Equal.cong(B.Octets, B.Octets, x => B.Octets.append(s1, B.Octets.append(data, x)), B.Octets.drop(m, tl), s2, Equal.trans(B.Octets, B.Octets.drop(m, tl), B.Octets.slice(Nat.add(Nat.mul(last, bs), m), ls, img), s2, IWP.tail_eq(Nat.mul(last, bs), bs, ls, img, L.span_slack(bp, off, l)), Equal.cong(Nat, B.Octets, x => B.Octets.slice(x, ls, img), Nat.add(Nat.mul(last, bs), m), Nat.add(Nat.add(fb, ks), l), eoff2)))))
  +hkeep = IWP.keep_le(f, cs, bs, ks, l, ls, c, img, L.span_cover(bp, off, l), hw, hlen)
  Equal.trans(B.Octets, D.MemDev.to_octets(IWP.wb(cs, d, bs, f, buf)), D.Dev.patch(fb, buf, img), D.Dev.patch(off, data, img), IWP.wb_img(cs, d, bs, f, buf, c, hv, ebs, {==}, hrw, hlb), Equal.trans(B.Octets, D.Dev.patch(fb, buf, img), D.Dev.patch(fb, B.Octets.append(s1, B.Octets.append(data, s2)), img), D.Dev.patch(off, data, img), Equal.cong(B.Octets, B.Octets, x => D.Dev.patch(fb, x, img), buf, B.Octets.append(s1, B.Octets.append(data, s2)), ebuf), Equal.trans(B.Octets, D.Dev.patch(fb, B.Octets.append(s1, B.Octets.append(data, s2)), img), D.Dev.patch(Nat.add(fb, ks), data, img), D.Dev.patch(off, data, img), BRL.patch_keep(fb, ks, data, ls, img, hkeep), Equal.cong(Nat, B.Octets, x => D.Dev.patch(x, data, img), Nat.add(fb, ks), off, L.span_start(bp, off, l)))))

# a nonempty write inside a device of 0-byte blocks cannot be
def IWP.bs0(+d: D.MemDev, +off: Nat, +data: B.Octets, +ebs: {D.MemDev.block_size(d) == 0n : Nat}, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> Empty:
  +l = B.Octets.len(data)
  +lp = P.IOP.pred(l)
  +c = D.MemDev.block_count(d)
  +e0 = Equal.trans(Nat, 0n, Nat.mul(c, 0n), Nat.mul(c, D.MemDev.block_size(d)), Equal.sym(Nat, Nat.mul(c, 0n), 0n, IWP.mul_zero(c)), Equal.cong(Nat, Nat, x => Nat.mul(c, x), 0n, D.MemDev.block_size(d), Equal.sym(Nat, D.MemDev.block_size(d), 0n, ebs)))
  +h1 = P.IOP.le_rw_l(Nat.add(off, 1n+lp), Nat.add(off, l), 0n, Equal.cong(Nat, Nat, x => Nat.add(off, x), 1n+lp, l, Equal.sym(Nat, l, 1n+lp, IWP.nz(l, ee))), P.IOP.le_rw_r(Nat.add(off, l), 0n, Nat.mul(c, D.MemDev.block_size(d)), e0, hr))
  P.IOP.bool_clash(P.IOP.le_rw_l(1n+Nat.add(off, lp), Nat.add(off, 1n+lp), 0n, Equal.sym(Nat, Nat.add(off, 1n+lp), 1n+Nat.add(off, lp), P.IOP.add_succ(off, lp)), h1))

# Every write inside a valid device: the run, and the device it leaves

def IWP.wrb_bs(bs: Nat, -R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +ebs: {D.MemDev.block_size(d) == bs : Nat}, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes.some(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, False{}, d, off, data)(R, k) == k((IWP.wdev(False{}, d, P.IOP.pred(D.MemDev.block_size(d)), off, data), Done{Unit{}})) : IO.OP<R>}:
  match bs:
    case 0n:
      Empty.absurd({V.IODev.write_bytes.some(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, False{}, d, off, data)(R, k) == k((IWP.wdev(False{}, d, P.IOP.pred(D.MemDev.block_size(d)), off, data), Done{Unit{}})) : IO.OP<R>}, IWP.bs0(d, off, data, ebs, ee, hr))
    case 1n+ +bp:
      %Equal.sym(Nat, D.MemDev.block_size(d), 1n+bp, ebs) : {V.IODev.write_bytes.go(~D.MemDev, ~M.IOMem.read_block, ~M.IOMem.write_block, off, data, (d, _))(R, k) == k((IWP.wdev(False{}, d, P.IOP.pred(_), off, data), Done{Unit{}})) : IO.OP<R>}
      IWP.wreal(R, k, d, bp, off, data, ebs, ee, hv, hr)

def IWP.wrb_e(e: Bool, -R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == e : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes.some(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, e, d, off, data)(R, k) == k((IWP.wdev(e, d, P.IOP.pred(D.MemDev.block_size(d)), off, data), Done{Unit{}})) : IO.OP<R>}:
  match e:
    case True{}:
      {==}
    case False{}:
      IWP.wrb_bs(D.MemDev.block_size(d), R, k, d, off, data, {==}, ee, hv, hr)

def IWP.wrb(-R: Type, -k: (D.MemDev & Result<&2, &2, D.DevError, Unit>) -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, k) == k((IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data), Done{Unit{}})) : IO.OP<R>}:
  IWP.wrb_e(Nat.is_eq(B.Octets.len(data), 0n), R, k, d, off, data, {==}, hv, hr)

def IWP.wimg_bs(bs: Nat, +d: D.MemDev, +off: Nat, +data: B.Octets, +ebs: {D.MemDev.block_size(d) == bs : Nat}, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {D.MemDev.to_octets(IWP.wdev(False{}, d, P.IOP.pred(D.MemDev.block_size(d)), off, data)) == D.Dev.patch(off, data, D.MemDev.to_octets(d)) : B.Octets}:
  match bs:
    case 0n:
      Empty.absurd({D.MemDev.to_octets(IWP.wdev(False{}, d, P.IOP.pred(D.MemDev.block_size(d)), off, data)) == D.Dev.patch(off, data, D.MemDev.to_octets(d)) : B.Octets}, IWP.bs0(d, off, data, ebs, ee, hr))
    case 1n+ +bp:
      %Equal.sym(Nat, D.MemDev.block_size(d), 1n+bp, ebs) : {D.MemDev.to_octets(IWP.wdev(False{}, d, P.IOP.pred(_), off, data)) == D.Dev.patch(off, data, D.MemDev.to_octets(d)) : B.Octets}
      IWP.wreal_img(d, bp, off, data, ebs, ee, hv, hr)

def IWP.wimg_e(e: Bool, +d: D.MemDev, +off: Nat, +data: B.Octets, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == e : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {D.MemDev.to_octets(IWP.wdev(e, d, P.IOP.pred(D.MemDev.block_size(d)), off, data)) == D.Dev.patch(off, data, D.MemDev.to_octets(d)) : B.Octets}:
  match e:
    case True{}:
      %Equal.sym(B.Octets, data, B.Octets.empty(), IWP.len0(data, IWP.eq_nat(B.Octets.len(data), 0n, ee))) : {D.MemDev.to_octets(d) == D.Dev.patch(off, _, D.MemDev.to_octets(d)) : B.Octets}
      Equal.sym(B.Octets, D.Dev.patch(off, B.Octets.empty(), D.MemDev.to_octets(d)), D.MemDev.to_octets(d), IWP.patch_nil(off, D.MemDev.to_octets(d)))
    case False{}:
      IWP.wimg_bs(D.MemDev.block_size(d), d, off, data, {==}, ee, hv, hr)

def IWP.wimg(+d: D.MemDev, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {D.MemDev.to_octets(IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data)) == D.Dev.patch(off, data, D.MemDev.to_octets(d)) : B.Octets}:
  IWP.wimg_e(Nat.is_eq(B.Octets.len(data), 0n), d, off, data, {==}, hv, hr)

def IWP.wdev_valid(e: Bool, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}) -> {D.MemDev.valid(IWP.wdev(e, d, bp, off, data)) == True{} : Bool}:
  match e:
    case True{}:
      hv
    case False{}:
      +s = S.IOSpan.of(1n+bp, off, B.Octets.len(data))
      IWP.wb_valid(S.IOSpan.count(s), d, 1n+bp, S.IOSpan.first(s), IWP.buf(d, bp, off, data), hv)

def IWP.wdev_size(e: Bool, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets) -> {D.MemDev.block_size(IWP.wdev(e, d, bp, off, data)) == D.MemDev.block_size(d) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      +s = S.IOSpan.of(1n+bp, off, B.Octets.len(data))
      IWP.wb_size(S.IOSpan.count(s), d, 1n+bp, S.IOSpan.first(s), IWP.buf(d, bp, off, data))

def IWP.wdev_count(e: Bool, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets) -> {D.MemDev.block_count(IWP.wdev(e, d, bp, off, data)) == D.MemDev.block_count(d) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      +s = S.IOSpan.of(1n+bp, off, B.Octets.len(data))
      IWP.wb_count(S.IOSpan.count(s), d, 1n+bp, S.IOSpan.first(s), IWP.buf(d, bp, off, data))

def IWP.wdev_shape(e: Bool, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}) -> {Laws.shape(IWP.wdev(e, d, bp, off, data)) == Laws.shape(d) : Bool & (Nat & Nat)}:
  match e:
    case True{}:
      {==}
    case False{}:
      +s = S.IOSpan.of(1n+bp, off, B.Octets.len(data))
      IWP.wb_shape(S.IOSpan.count(s), d, 1n+bp, S.IOSpan.first(s), IWP.buf(d, bp, off, data), hv)

# The laws for write_bytes

def IWP.l_bytes(-R: Type, -k: (Result<&2, &2, D.DevError, Unit> & B.Octets) -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(Laws.outcome(x))) == k((Done{Unit{}}, D.Dev.patch(off, data, D.MemDev.to_octets(d)))) : IO.OP<R>}:
  +w = IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data)
  Equal.trans(IO.OP<R>, V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(Laws.outcome(x))), k((Done{Unit{}}, D.MemDev.to_octets(w))), k((Done{Unit{}}, D.Dev.patch(off, data, D.MemDev.to_octets(d)))), IWP.wrb(R, x => k(Laws.outcome(x)), d, off, data, hv, hr), Equal.cong(B.Octets, IO.OP<R>, z => k((Done{Unit{}}, z)), D.MemDev.to_octets(w), D.Dev.patch(off, data, D.MemDev.to_octets(d)), IWP.wimg(d, off, data, hv, hr)))

def Laws.io_mem_write_bytes(R, k, d, off, data, hv, hr):
  IWP.l_bytes(R, k, d, off, data, hv, hr)

def IWP.l_shape(-R: Type, -k: (Bool & (Nat & Nat)) -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(Laws.shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))) == k(Laws.shape(d)) : IO.OP<R>}:
  +e = Nat.is_eq(B.Octets.len(data), 0n)
  +bpx = P.IOP.pred(D.MemDev.block_size(d))
  +w = IWP.wdev(e, d, bpx, off, data)
  Equal.trans(IO.OP<R>, V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(Laws.shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x)))), k(Laws.shape(w)), k(Laws.shape(d)), IWP.wrb(R, x => k(Laws.shape(Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x))), d, off, data, hv, hr), Equal.cong(Bool & (Nat & Nat), IO.OP<R>, z => k(z), Laws.shape(w), Laws.shape(d), IWP.wdev_shape(e, d, bpx, off, data, hv)))

def Laws.io_mem_write_bytes_shape(R, k, d, off, data, hv, hr):
  IWP.l_shape(R, k, d, off, data, hv, hr)

# what the device written reads, on a range inside it
def IWP.w_read(+d: D.MemDev, +off: Nat, +data: B.Octets, +i: Nat, +n: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}, +hi: {Nat.is_le(Nat.add(i, n), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data), i, n) == Done{B.Octets.slice(i, n, D.Dev.patch(off, data, D.MemDev.to_octets(d)))} : Result<&2, &2, D.DevError, B.Octets>}:
  +e = Nat.is_eq(B.Octets.len(data), 0n)
  +bpx = P.IOP.pred(D.MemDev.block_size(d))
  +w = IWP.wdev(e, d, bpx, off, data)
  +eq = Equal.trans(Nat, Nat.mul(D.MemDev.block_count(w), D.MemDev.block_size(w)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(w)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d)), Equal.cong(Nat, Nat, x => Nat.mul(x, D.MemDev.block_size(w)), D.MemDev.block_count(w), D.MemDev.block_count(d), IWP.wdev_count(e, d, bpx, off, data)), Equal.cong(Nat, Nat, x => Nat.mul(D.MemDev.block_count(d), x), D.MemDev.block_size(w), D.MemDev.block_size(d), IWP.wdev_size(e, d, bpx, off, data)))
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, w, i, n), Done{B.Octets.slice(i, n, D.MemDev.to_octets(w))}, BRL.read_bytes_mem(w, i, n, IWP.wdev_valid(e, d, bpx, off, data, hv), P.IOP.le_rw_r(Nat.add(i, n), Nat.mul(D.MemDev.block_count(w), D.MemDev.block_size(w)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d)), eq, hi))) : {_ == Done{B.Octets.slice(i, n, D.Dev.patch(off, data, D.MemDev.to_octets(d)))} : Result<&2, &2, D.DevError, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, x => Done{B.Octets.slice(i, n, x)}, D.MemDev.to_octets(w), D.Dev.patch(off, data, D.MemDev.to_octets(d)), IWP.wimg(d, off, data, hv, hr))

# the image's length bounds the write
def IWP.w_off(+d: D.MemDev, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {Nat.is_le(off, B.Octets.len(D.MemDev.to_octets(d))) == True{} : Bool}:
  P.IOP.le_trans(off, Nat.add(off, B.Octets.len(data)), B.Octets.len(D.MemDev.to_octets(d)), P.IOP.le_add_r(off, B.Octets.len(data)), P.IOP.le_rw_r(Nat.add(off, B.Octets.len(data)), B.Octets.len(D.MemDev.to_octets(d)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d)), BRL.to_octets_len(d, hv), hr))

# write_bytes then a read: the read of the device written
def IWP.w_then(-R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +i: Nat, +n: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == k(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data), i, n)) : IO.OP<R>}:
  +w = IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data)
  Equal.trans(IO.OP<R>, V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))), V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, w, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), k(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, w, i, n)), IWP.wrb(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), d, off, data, hv, hr), IWP.read_bytes(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)), w, i, n))

def IWP.l_read(-R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), off, B.Octets.len(data))(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == k(Done{data}) : IO.OP<R>}:
  +l = B.Octets.len(data)
  +w = IWP.wdev(Nat.is_eq(l, 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data)
  +img = D.MemDev.to_octets(d)
  Equal.trans(IO.OP<R>, V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), off, l)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))), k(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, w, off, l)), k(Done{data}), IWP.w_then(R, k, d, off, data, off, l, hv, hr), Equal.cong(Result<&2, &2, D.DevError, B.Octets>, IO.OP<R>, z => k(z), D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, w, off, l), Done{data}, Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, w, off, l), Done{B.Octets.slice(off, l, D.Dev.patch(off, data, img))}, Done{data}, IWP.w_read(d, off, data, off, l, hv, hr, hr), Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, x => Done{x}, B.Octets.slice(off, l, D.Dev.patch(off, data, img)), data, BRL.patch_slice(off, data, img, IWP.w_off(d, off, data, hv, hr))))))

def Laws.io_mem_write_read(R, k, d, off, data, hv, hr):
  IWP.l_read(R, k, d, off, data, hv, hr)

# outside the range written: the read is the device's before
def IWP.l_out(-R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +i: Nat, +n: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}, +hi: {Nat.is_le(Nat.add(i, n), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}, +hs: {B.Octets.slice(i, n, D.Dev.patch(off, data, D.MemDev.to_octets(d))) == B.Octets.slice(i, n, D.MemDev.to_octets(d)) : B.Octets}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))) : IO.OP<R>}:
  +w = IWP.wdev(Nat.is_eq(B.Octets.len(data), 0n), d, P.IOP.pred(D.MemDev.block_size(d)), off, data)
  +img = D.MemDev.to_octets(d)
  +rw = D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, w, i, n)
  +rd = D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, i, n)
  +er = Equal.trans(Result<&2, &2, D.DevError, B.Octets>, rw, Done{B.Octets.slice(i, n, D.Dev.patch(off, data, img))}, rd, IWP.w_read(d, off, data, i, n, hv, hr, hi), Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Done{B.Octets.slice(i, n, D.Dev.patch(off, data, img))}, Done{B.Octets.slice(i, n, img)}, rd, Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, x => Done{x}, B.Octets.slice(i, n, D.Dev.patch(off, data, img)), B.Octets.slice(i, n, img), hs), Equal.sym(Result<&2, &2, D.DevError, B.Octets>, rd, Done{B.Octets.slice(i, n, img)}, BRL.read_bytes_mem(d, i, n, hv, hi))))
  Equal.trans(IO.OP<R>, V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))), k(rw), V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), IWP.w_then(R, k, d, off, data, i, n, hv, hr), Equal.trans(IO.OP<R>, k(rw), k(rd), V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), Equal.cong(Result<&2, &2, D.DevError, B.Octets>, IO.OP<R>, z => k(z), rw, rd, er), Equal.sym(IO.OP<R>, V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))), k(rd), IWP.read_bytes(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)), d, i, n))))

def IWP.l_before(-R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +i: Nat, +n: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}, +h: {Nat.is_le(Nat.add(i, n), off) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))) : IO.OP<R>}:
  +mx = Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))
  +hi = P.IOP.le_trans(Nat.add(i, n), off, mx, h, P.IOP.le_trans(off, Nat.add(off, B.Octets.len(data)), mx, P.IOP.le_add_r(off, B.Octets.len(data)), hr))
  IWP.l_out(R, k, d, off, data, i, n, hv, hr, hi, BRL.patch_before(i, n, off, data, D.MemDev.to_octets(d), h, IWP.w_off(d, off, data, hv, hr)))

def Laws.io_mem_write_before(R, k, d, off, data, i, n, hv, hr, h):
  IWP.l_before(R, k, d, off, data, i, n, hv, hr, h)

def IWP.l_after(-R: Type, -k: Result<&2, &2, D.DevError, B.Octets> -> IO.OP<R>, +d: D.MemDev, +off: Nat, +data: B.Octets, +i: Nat, +n: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, B.Octets.len(data)), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}, +h: {Nat.is_le(Nat.add(off, B.Octets.len(data)), i) == True{} : Bool}, +hi: {Nat.is_le(Nat.add(i, n), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, Pair.fst(D.MemDev, Result<&2, &2, D.DevError, Unit>, x), i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y)))) == V.IODev.read_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, d, i, n)(R, y => k(Pair.snd(D.MemDev, Result<&2, &2, D.DevError, B.Octets>, y))) : IO.OP<R>}:
  IWP.l_out(R, k, d, off, data, i, n, hv, hr, hi, BRL.patch_after(i, n, off, data, D.MemDev.to_octets(d), h, IWP.w_off(d, off, data, hv, hr)))

def Laws.io_mem_write_after(R, k, d, off, data, i, n, hv, hr, h, hi):
  IWP.l_after(R, k, d, off, data, i, n, hv, hr, h, hi)

# past the end: the first block read fails, or the last does
def IWP.past(z: Bool, -R: Type, -k: (D.MemDev & Bool) -> IO.OP<R>, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +ez: {Nat.is_lt(S.IOSpan.first(S.IOSpan.of(1n+bp, off, B.Octets.len(data))), D.MemDev.block_count(d)) == z : Bool}, +ebs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +ee: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +hv: {D.MemDev.valid(d) == True{} : Bool}, +past: {Nat.is_lt(Nat.mul(D.MemDev.block_count(d), 1n+bp), Nat.add(off, B.Octets.len(data))) == True{} : Bool}) -> {V.IODev.write_bytes.go(~D.MemDev, ~M.IOMem.read_block, ~M.IOMem.write_block, off, data, (d, 1n+bp))(R, x => k(Laws.failed(x))) == k((d, True{})) : IO.OP<R>}:
  match z:
    case False{}:
      +bs : Nat = 1n+bp
      +l = B.Octets.len(data)
      +sp = S.IOSpan.of(bs, off, l)
      +f = S.IOSpan.first(sp)
      +cs = S.IOSpan.count(sp)
      +c = D.MemDev.block_count(d)
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d, f), Fail{D.DevOutOfRange{f}}, BRL.read_block_out(d, f, ez)) : {IWP.r1(R, x => k(Laws.failed(x)), (d, _), bp, off, data) == k((d, True{})) : IO.OP<R>}
      {==}
    case True{}:
      +bs : Nat = 1n+bp
      +l = B.Octets.len(data)
      +sp = S.IOSpan.of(bs, off, l)
      +f = S.IOSpan.first(sp)
      +cs = S.IOSpan.count(sp)
      +c = D.MemDev.block_count(d)
      +cp = P.IOP.pred(cs)
      +last = Nat.add(f, Nat.sub(cs, 1n))
      +ecs = IWP.f_ecs(bp, off, data, ee)
      +h1 = P.IOP.lt_rw_r(c, 1n+Nat.add(f, cp), Nat.add(f, cs), Equal.trans(Nat, 1n+Nat.add(f, cp), Nat.add(f, 1n+cp), Nat.add(f, cs), Equal.sym(Nat, Nat.add(f, 1n+cp), 1n+Nat.add(f, cp), P.IOP.add_succ(f, cp)), Equal.cong(Nat, Nat, x => Nat.add(f, x), 1n+cp, cs, Equal.sym(Nat, cs, 1n+cp, ecs))), L.span_past(bp, off, l, c, past))
      +hle = P.IOP.le_rw_r(c, last, Nat.add(f, cp), IWP.f_last(f, cs, ecs), P.IOP.lt_succ_le(c, Nat.add(f, cp), h1))
      +hd = B.Octets.slice(Nat.mul(f, bs), bs, D.MemDev.to_octets(d))
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d, f), Done{hd}, IWP.rb(d, f, bp, ebs, hv, ez)) : {IWP.r1(R, x => k(Laws.failed(x)), (d, _), bp, off, data) == k((d, True{})) : IO.OP<R>}
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d, last), Fail{D.DevOutOfRange{last}}, BRL.read_block_out(d, last, IWP.le_not_lt(c, last, hle))) : {IWP.r2(R, x => k(Laws.failed(x)), (d, _), hd, bp, off, data) == k((d, True{})) : IO.OP<R>}
      {==}

def IWP.l_past(-R: Type, -k: (D.MemDev & Bool) -> IO.OP<R>, +d: D.MemDev, +bp: Nat, +off: Nat, +data: B.Octets, +hv: {D.MemDev.valid(d) == True{} : Bool}, +hbs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +nz: {Nat.is_eq(B.Octets.len(data), 0n) == False{} : Bool}, +past: {Nat.is_lt(Nat.mul(D.MemDev.block_count(d), 1n+bp), Nat.add(off, B.Octets.len(data))) == True{} : Bool}) -> {V.IODev.write_bytes(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, d, off, data)(R, x => k(Laws.failed(x))) == k((d, True{})) : IO.OP<R>}:
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(data), 0n), False{}, nz) : {V.IODev.write_bytes.some(~D.MemDev, ~M.IOMem.block_size, ~M.IOMem.read_block, ~M.IOMem.write_block, _, d, off, data)(R, x => k(Laws.failed(x))) == k((d, True{})) : IO.OP<R>}
  %Equal.sym(Nat, D.MemDev.block_size(d), 1n+bp, hbs) : {V.IODev.write_bytes.go(~D.MemDev, ~M.IOMem.read_block, ~M.IOMem.write_block, off, data, (d, _))(R, x => k(Laws.failed(x))) == k((d, True{})) : IO.OP<R>}
  IWP.past(Nat.is_lt(S.IOSpan.first(S.IOSpan.of(1n+bp, off, B.Octets.len(data))), D.MemDev.block_count(d)), R, k, d, bp, off, data, {==}, hbs, nz, hv, past)

def Laws.io_mem_write_past_end(R, k, d, bp, off, data, hv, hbs, nz, past):
  IWP.l_past(R, k, d, bp, off, data, hv, hbs, nz, past)

# Vectors, by computation

def Laws.vector_fold():
  {==}

def Laws.vector_write_blocks():
  {==}
