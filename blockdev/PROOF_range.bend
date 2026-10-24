# Proofs of LAWS_range.bend. Internal lemmas are prefixed BR. (the Nat and
# division lemmas are iodev's, from its PROOF.bend, which has them from
# ext2's: blockdev cannot import either).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BPF
import ./blockdev.bend as D
import ./LAWS.bend as DL
import ./PROOF.bend as P
import ./LAWS_range.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP
import ../u32/LAWS_div.bend as UD
import ../u32/PROOF_div.bend as UDP

# Natural numbers, from Base's definitions of Nat.add, Nat.sub, Nat.mul and
# Nat.divmod

def BR.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def BR.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      BR.lt_succ(p)

def BR.bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def BR.bool_clash(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : BR.bool_disc(_)
  Unit{}

def BR.ex_falso(-A: Type, e: Empty) -> A:
  match e:

# x < y gives x < y + 1
def BR.lt_up(+x: Nat, +y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      BR.ex_falso({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, BR.bool_clash(h))
    case 1n+xp 1n+yp:
      BR.lt_up(xp, yp, h)

# bp - r < bp + 1
def BR.sub_lt(+bp: Nat, +r: Nat) -> {Nat.is_lt(Nat.sub(bp, r), 1n+bp) == True{} : Bool}:
  match bp r:
    case 0n _:
      {==}
    case 1n+b 0n:
      BR.lt_succ(b)
    case 1n+b 1n+q:
      BR.lt_up(Nat.sub(b, q), 1n+b, BR.sub_lt(b, q))

# Base's division: Nat.divmod(a, 1 + bp) runs go(a, bp, 0, 0), which counts
# m down and r up (m + r == bp throughout) and d once per full round.

# Spans. With a block of 1 + bp bytes, Nat.sub(1 + bp, 1) is Nat.sub(bp, 0),
# which is bp by BR.sub_zero.

def BR.slack_lt(+bp: Nat, +t: Nat) -> {Nat.is_lt(Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(t, 1n+bp)), 1n+bp) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, BR.sub_zero(bp)) : {Nat.is_lt(Nat.sub(_, Nat.mod(t, 1n+bp)), 1n+bp) == True{} : Bool}
  BR.sub_lt(bp, Nat.mod(t, 1n+bp))

def BR.lt0(+p: Nat, +h: {Nat.is_lt(p, 0n) == True{} : Bool}) -> Empty:
  BR.bool_clash(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{}, Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, P.IP.lt_zero(p)), h))

def BR.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      BR.eq_refl(p)

def BR.eq_of(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  BR.eq_refl(a)

# a <= b gives a + (b - a) == b
def BR.le_wit(a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n _:
      BR.sub_zero(b)
    case 1n+ +p 0n:
      BR.ex_falso({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, BR.bool_clash(h))
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, Nat.sub(q, p)), q, BR.le_wit(p, q, h))

def BR.lt_to_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  UO.nat_le_trans(a, 1n+a, b, P.IP.le_succ_r(a, a, UL.nat_le_refl(a)), P.IP.lt_le(a, b, h))

def BR.lt_le_no(+a: Nat, +b: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, a) == True{} : Bool}) -> Empty:
  BR.bool_clash(Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{}, Equal.sym(Bool, Nat.is_lt(a, a), False{}, P.BP.lt_irrefl(a)), UO.nat_lt_le_trans(a, b, a, h1, h2)))

def BR.lt_rw_l(-x: Nat, -y: Nat, -m: Nat, +e: {x == y : Nat}, +h: {Nat.is_lt(y, m) == True{} : Bool}) -> {Nat.is_lt(x, m) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(_, m) == True{} : Bool}
  h

# c + a < c + b is a < b
def BR.add_lt_l(c: Nat, -a: Nat, -b: Nat) -> {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == Nat.is_lt(a, b) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+ +p:
      BR.add_lt_l(p, a, b)

# x * (1 + bp) < y * (1 + bp) gives x < y
def BR.mul_lt_cancel(x: Nat, +y: Nat, +bp: Nat, +h: {Nat.is_lt(Nat.mul(x, 1n+bp), Nat.mul(y, 1n+bp)) == True{} : Bool}) -> {Nat.is_lt(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      BR.ex_falso({Nat.is_lt(0n, 0n) == True{} : Bool}, BR.bool_clash(h))
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      BR.ex_falso({Nat.is_lt(1n+p, 0n) == True{} : Bool}, BR.bool_clash(h))
    case 1n+ +p 1n+ +q:
      BR.mul_lt_cancel(p, q, bp, Equal.trans(Bool, Nat.is_lt(Nat.mul(p, 1n+bp), Nat.mul(q, 1n+bp)), Nat.is_lt(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), Nat.add(1n+bp, Nat.mul(q, 1n+bp))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), Nat.add(1n+bp, Nat.mul(q, 1n+bp))), Nat.is_lt(Nat.mul(p, 1n+bp), Nat.mul(q, 1n+bp)), BR.add_lt_l(1n+bp, Nat.mul(p, 1n+bp), Nat.mul(q, 1n+bp))), h))

# x < 1 + n gives x <= n
def BR.lt_succ_le(x: Nat, +n: Nat, +h: {Nat.is_lt(x, 1n+n) == True{} : Bool}) -> {Nat.is_le(x, n) == True{} : Bool}:
  match x n:
    case 0n _:
      P.IP.le_zero(n)
    case 1n+ +p 0n:
      BR.ex_falso({Nat.is_le(1n+p, 0n) == True{} : Bool}, BR.lt0(p, h))
    case 1n+ +p 1n+ +q:
      BR.lt_succ_le(p, q, h)

def BR.min_le(a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +p 0n:
      {==}
    case 1n+ +p 1n+ +q:
      BR.min_le(p, q)

def BR.min_l(a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +p 0n:
      BR.ex_falso({Nat.min(1n+p, 0n) == 1n+p : Nat}, BR.bool_clash(h))
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.min(p, q), p, BR.min_l(p, q, h))

def BR.max_r(a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +p 0n:
      BR.ex_falso({Nat.max(1n+p, 0n) == 0n : Nat}, BR.bool_clash(h))
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.max(p, q), q, BR.max_r(p, q, h))

def BR.max_l(a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      Empty.absurd({Nat.max(0n, 1n+q) == 0n : Nat}, P.BP.tf(h))
    case 1n+ +p 0n:
      {==}
    case 1n+ +p 1n+ +q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.max(p, q), p, BR.max_l(p, q, h))

# P <= Q and L < bs give P + L < bs + Q
def BR.lt_add_both(a: Nat, +b: Nat, +l: Nat, +bs: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_lt(l, bs) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, l), Nat.add(bs, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      UO.nat_lt_le_trans(l, bs, Nat.add(bs, b), h2, UO.nat_le_add_r(bs, b))
    case 1n+ +p 0n:
      BR.ex_falso({Nat.is_lt(Nat.add(1n+p, l), Nat.add(bs, 0n)) == True{} : Bool}, BR.bool_clash(h1))
    case 1n+ +p 1n+ +q:
      %Equal.sym(Nat, Nat.add(bs, 1n+q), 1n+Nat.add(bs, q), UL.nat_add_succ(bs, q)) : {Nat.is_lt(1n+Nat.add(p, l), _) == True{} : Bool}
      BR.lt_add_both(p, q, l, bs, h1, h2)

# The span of a range: with a block of bs = 1 + bp bytes, the range (off,
# len) starts s bytes into block f, covers c blocks and ends l bytes before
# their end (the expressions Dev.read_bytes computes)

def BR.span_eq(+bp: Nat, +off: Nat, +len: Nat) -> {Nat.mul(Nat.add(Nat.div(off, 1n+bp), Nat.div(Nat.add(Nat.add(Nat.mod(off, 1n+bp), len), Nat.sub(1n+bp, 1n)), 1n+bp)), 1n+bp) == Nat.add(Nat.add(off, len), Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(Nat.add(Nat.add(Nat.mod(off, 1n+bp), len), Nat.sub(1n+bp, 1n)), 1n+bp))) : Nat}:
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

# a range inside n blocks has its span inside them
def BR.span_le(+bp: Nat, +off: Nat, +len: Nat, +n: Nat, +hr: {Nat.is_le(Nat.add(off, len), Nat.mul(n, 1n+bp)) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.div(off, 1n+bp), Nat.div(Nat.add(Nat.add(Nat.mod(off, 1n+bp), len), Nat.sub(1n+bp, 1n)), 1n+bp)), n) == True{} : Bool}:
  +bs : Nat = 1n+bp
  +s = Nat.mod(off, bs)
  +f = Nat.div(off, bs)
  +t = Nat.add(Nat.add(s, len), Nat.sub(bs, 1n))
  +c = Nat.div(t, bs)
  +l = Nat.sub(Nat.sub(bs, 1n), Nat.mod(t, bs))
  BR.lt_succ_le(Nat.add(f, c), n, BR.mul_lt_cancel(Nat.add(f, c), 1n+n, bp, BR.lt_rw_l(Nat.mul(Nat.add(f, c), bs), Nat.add(Nat.add(off, len), l), Nat.add(bs, Nat.mul(n, bs)), BR.span_eq(bp, off, len), BR.lt_add_both(Nat.add(off, len), Nat.mul(n, bs), l, bs, hr, BR.slack_lt(bp, t)))))

# Octets

# a byte string of length 0 is the empty one
def BR.nil_of(xs: List<&2, U32>, +h: {B.len(xs) == 0n : Nat}) -> {B.Octets.of_list(xs) == B.Octets.empty() : B.Octets}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Empty.absurd({B.Octets.of_list(Con{x, t}) == B.Octets.empty() : B.Octets}, P.IP.sz(B.len(t), h))

def BR.len0(+o: B.Octets, +h: {B.Octets.len(o) == 0n : Nat}) -> {o == B.Octets.empty() : B.Octets}:
  Equal.trans(B.Octets, o, B.Octets.of_list(B.Octets.to_list(o)), B.Octets.empty(), Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)), BR.nil_of(B.Octets.to_list(o), Equal.trans(Nat, B.len(B.Octets.to_list(o)), B.Octets.len(o), 0n, Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)), h)))

def BR.take0(+o: B.Octets) -> {B.Octets.take(0n, o) == B.Octets.empty() : B.Octets}:
  BR.len0(B.Octets.take(0n, o), BL.octets_len_take(0n, o))

# the first len(x) bytes of x ++ r are x
def BR.slice_head(+x: B.Octets, +r: B.Octets) -> {B.Octets.slice(0n, B.Octets.len(x), B.Octets.append(x, r)) == x : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.slice(0n, B.Octets.len(x), B.Octets.append(x, r)), B.Octets.slice(0n, B.Octets.len(x), x), BL.octets_slice_append_le(0n, B.Octets.len(x), x, r, UL.nat_le_refl(B.Octets.len(x)))) : {_ == x : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(0n, x), x, BL.octets_drop_zero(x)) : {B.Octets.take(B.Octets.len(x), _) == x : B.Octets}
  BL.octets_take_len(x)

# the middle of a ++ (m ++ z)
def BR.slice_mid(+a: B.Octets, +m: B.Octets, +z: B.Octets) -> {B.Octets.slice(B.Octets.len(a), B.Octets.len(m), B.Octets.append(a, B.Octets.append(m, z))) == m : B.Octets}:
  %UL.nat_add_zero(B.Octets.len(a)) : {B.Octets.slice(_, B.Octets.len(m), B.Octets.append(a, B.Octets.append(m, z))) == m : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(a), 0n), B.Octets.len(m), B.Octets.append(a, B.Octets.append(m, z))), B.Octets.slice(0n, B.Octets.len(m), B.Octets.append(m, z)), BL.octets_slice_append_add(a, 0n, B.Octets.len(m), B.Octets.append(m, z))) : {_ == m : B.Octets}
  BR.slice_head(m, z)

# Pure devices: the blocks a device reads, joined (got: a read's block, or
# nothing if it failed)

def BR.got(r: Result<&2, &2, D.DevError, B.Octets>) -> B.Octets:
  match r:
    case Done{b}:
      b
    case Fail{e}:
      B.Octets.empty()

def BR.img(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +k: Nat, +d: T, +j: Nat) -> B.Octets:
  match k:
    case 0n:
      B.Octets.empty()
    case 1n+ +p:
      B.Octets.append(BR.got(read_block(d, j)), BR.img(~T, ~read_block, p, d, Nat.add(j, 1n)))

def BR.u_done(r: Result<&2, &2, D.DevError, B.Octets>, +bs: Nat, +e: {D.Dev.uniform.ok(r, bs) == True{} : Bool}) -> {r == Done{BR.got(r)} : Result<&2, &2, D.DevError, B.Octets>}:
  match r:
    case Done{b}:
      {==}
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{BR.got(Fail{x})} : Result<&2, &2, D.DevError, B.Octets>}, P.BP.ft(e))

def BR.u_len(r: Result<&2, &2, D.DevError, B.Octets>, +bs: Nat, +e: {D.Dev.uniform.ok(r, bs) == True{} : Bool}) -> {B.Octets.len(BR.got(r)) == bs : Nat}:
  match r:
    case Done{b}:
      P.IP.eq_nat(B.Octets.len(b), bs, e)
    case Fail{x}:
      Empty.absurd({B.Octets.len(BR.got(Fail{x})) == bs : Nat}, P.BP.ft(e))

def BR.u_rw(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, -a: Nat, -b: Nat, +d: T, +bs: Nat, +j: Nat, +e: {a == b : Nat}, +h: {D.Dev.uniform.go(~T, ~read_block, a, d, bs, j) == True{} : Bool}) -> {D.Dev.uniform.go(~T, ~read_block, b, d, bs, j) == True{} : Bool}:
  %e : {D.Dev.uniform.go(~T, ~read_block, _, d, bs, j) == True{} : Bool}
  h

def BR.u_bs(~T: Data, ~block_size: T -> Nat, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +n: Nat, +bp: Nat, +hbs: {block_size(d) == 1n+bp : Nat}, +hu: {D.Dev.uniform(~T, ~block_size, ~read_block, d, n) == True{} : Bool}) -> {D.Dev.uniform.go(~T, ~read_block, n, d, 1n+bp, 0n) == True{} : Bool}:
  %hbs : {D.Dev.uniform.go(~T, ~read_block, n, d, _, 0n) == True{} : Bool}
  hu

# uniform blocks read as their image
def BR.u1(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +k: Nat, +d: T, +bs: Nat, +j: Nat, +h: {D.Dev.uniform.go(~T, ~read_block, k, d, bs, j) == True{} : Bool}) -> {D.Dev.read_blocks(~T, ~read_block, d, k, j) == Done{BR.img(~T, ~read_block, k, d, j)} : Result<&2, &2, D.DevError, B.Octets>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +r = read_block(d, j)
      +h1 = P.BP.and_l(D.Dev.uniform.ok(r, bs), D.Dev.uniform.go(~T, ~read_block, p, d, bs, Nat.add(j, 1n)), h)
      +h2 = P.BP.and_r(D.Dev.uniform.ok(r, bs), D.Dev.uniform.go(~T, ~read_block, p, d, bs, Nat.add(j, 1n)), h)
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, r, Done{BR.got(r)}, BR.u_done(r, bs, h1)) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(j, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))) == Done{B.Octets.append(BR.got(r), BR.img(~T, ~read_block, p, d, Nat.add(j, 1n)))} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(j, 1n)), Done{BR.img(~T, ~read_block, p, d, Nat.add(j, 1n))}, BR.u1(~T, ~read_block, p, d, bs, Nat.add(j, 1n), h2)) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(BR.got(r), rest))) == Done{B.Octets.append(BR.got(r), BR.img(~T, ~read_block, p, d, Nat.add(j, 1n)))} : Result<&2, &2, D.DevError, B.Octets>}
      {==}

# uniform blocks are bs bytes each
def BR.u2(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +k: Nat, +d: T, +bs: Nat, +j: Nat, +h: {D.Dev.uniform.go(~T, ~read_block, k, d, bs, j) == True{} : Bool}) -> {B.Octets.len(BR.img(~T, ~read_block, k, d, j)) == Nat.mul(k, bs) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +r = read_block(d, j)
      +h1 = P.BP.and_l(D.Dev.uniform.ok(r, bs), D.Dev.uniform.go(~T, ~read_block, p, d, bs, Nat.add(j, 1n)), h)
      +h2 = P.BP.and_r(D.Dev.uniform.ok(r, bs), D.Dev.uniform.go(~T, ~read_block, p, d, bs, Nat.add(j, 1n)), h)
      +im = BR.img(~T, ~read_block, p, d, Nat.add(j, 1n))
      %Equal.sym(Nat, B.Octets.len(B.Octets.append(BR.got(r), im)), Nat.add(B.Octets.len(BR.got(r)), B.Octets.len(im)), BL.octets_len_append(BR.got(r), im)) : {_ == Nat.add(bs, Nat.mul(p, bs)) : Nat}
      %Equal.sym(Nat, B.Octets.len(BR.got(r)), bs, BR.u_len(r, bs, h1)) : {Nat.add(_, B.Octets.len(im)) == Nat.add(bs, Nat.mul(p, bs)) : Nat}
      %Equal.sym(Nat, B.Octets.len(im), Nat.mul(p, bs), BR.u2(~T, ~read_block, p, d, bs, Nat.add(j, 1n), h2)) : {Nat.add(bs, _) == Nat.add(bs, Nat.mul(p, bs)) : Nat}
      {==}

# the image of a + b blocks is the image of a then of b
def BR.u3(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +a: Nat, +b: Nat, +d: T, +j: Nat) -> {BR.img(~T, ~read_block, Nat.add(a, b), d, j) == B.Octets.append(BR.img(~T, ~read_block, a, d, j), BR.img(~T, ~read_block, b, d, Nat.add(j, a))) : B.Octets}:
  match a:
    case 0n:
      %Equal.sym(Nat, Nat.add(j, 0n), j, UL.nat_add_zero(j)) : {BR.img(~T, ~read_block, b, d, j) == B.Octets.append(B.Octets.empty(), BR.img(~T, ~read_block, b, d, _)) : B.Octets}
      Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), BR.img(~T, ~read_block, b, d, j)), BR.img(~T, ~read_block, b, d, j), BL.octets_append_empty_l(BR.img(~T, ~read_block, b, d, j)))
    case 1n+ +p:
      +g = BR.got(read_block(d, j))
      +x = BR.img(~T, ~read_block, p, d, Nat.add(j, 1n))
      +y = BR.img(~T, ~read_block, b, d, Nat.add(Nat.add(j, 1n), p))
      %Equal.sym(B.Octets, BR.img(~T, ~read_block, Nat.add(p, b), d, Nat.add(j, 1n)), B.Octets.append(x, y), BR.u3(~T, ~read_block, p, b, d, Nat.add(j, 1n))) : {B.Octets.append(g, _) == B.Octets.append(B.Octets.append(g, x), BR.img(~T, ~read_block, b, d, Nat.add(j, 1n+p))) : B.Octets}
      %UL.nat_add_assoc(j, 1n, p) : {B.Octets.append(g, B.Octets.append(x, y)) == B.Octets.append(B.Octets.append(g, x), BR.img(~T, ~read_block, b, d, _)) : B.Octets}
      Equal.sym(B.Octets, B.Octets.append(B.Octets.append(g, x), y), B.Octets.append(g, B.Octets.append(x, y)), BL.octets_append_assoc(g, x, y))

# uniform over a + b blocks is uniform over each part
def BR.u4a(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +a: Nat, +b: Nat, +d: T, +bs: Nat, +j: Nat, +h: {D.Dev.uniform.go(~T, ~read_block, Nat.add(a, b), d, bs, j) == True{} : Bool}) -> {D.Dev.uniform.go(~T, ~read_block, a, d, bs, j) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ +p:
      +ok = D.Dev.uniform.ok(read_block(d, j), bs)
      +h1 = P.BP.and_l(ok, D.Dev.uniform.go(~T, ~read_block, Nat.add(p, b), d, bs, Nat.add(j, 1n)), h)
      +h2 = P.BP.and_r(ok, D.Dev.uniform.go(~T, ~read_block, Nat.add(p, b), d, bs, Nat.add(j, 1n)), h)
      %Equal.sym(Bool, ok, True{}, h1) : {Bool.and(_, D.Dev.uniform.go(~T, ~read_block, p, d, bs, Nat.add(j, 1n))) == True{} : Bool}
      BR.u4a(~T, ~read_block, p, b, d, bs, Nat.add(j, 1n), h2)

def BR.u4b(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +a: Nat, +b: Nat, +d: T, +bs: Nat, +j: Nat, +h: {D.Dev.uniform.go(~T, ~read_block, Nat.add(a, b), d, bs, j) == True{} : Bool}) -> {D.Dev.uniform.go(~T, ~read_block, b, d, bs, Nat.add(j, a)) == True{} : Bool}:
  match a:
    case 0n:
      %Equal.sym(Nat, Nat.add(j, 0n), j, UL.nat_add_zero(j)) : {D.Dev.uniform.go(~T, ~read_block, b, d, bs, _) == True{} : Bool}
      h
    case 1n+ +p:
      +ok = D.Dev.uniform.ok(read_block(d, j), bs)
      +h2 = P.BP.and_r(ok, D.Dev.uniform.go(~T, ~read_block, Nat.add(p, b), d, bs, Nat.add(j, 1n)), h)
      %UL.nat_add_assoc(j, 1n, p) : {D.Dev.uniform.go(~T, ~read_block, b, d, bs, _) == True{} : Bool}
      BR.u4b(~T, ~read_block, p, b, d, bs, Nat.add(j, 1n), h2)

# The bytes of the blocks a range spans, against the whole image: the
# image of n blocks is the f blocks before the span, its c blocks, and the
# r blocks after
def BR.core_eq(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +bp: Nat, +n: Nat, +off: Nat, +len: Nat, +hu: {D.Dev.uniform.go(~T, ~read_block, n, d, 1n+bp, 0n) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, len), Nat.mul(n, 1n+bp)) == True{} : Bool}) -> {B.Octets.slice(off, len, BR.img(~T, ~read_block, n, d, 0n)) == B.Octets.slice(Nat.mod(off, 1n+bp), len, BR.img(~T, ~read_block, Nat.div(Nat.add(Nat.add(Nat.mod(off, 1n+bp), len), Nat.sub(1n+bp, 1n)), 1n+bp), d, Nat.div(off, 1n+bp))) : B.Octets}:
  +bs : Nat = 1n+bp
  +s = Nat.mod(off, bs)
  +f = Nat.div(off, bs)
  +t = Nat.add(Nat.add(s, len), Nat.sub(bs, 1n))
  +c = Nat.div(t, bs)
  +l = Nat.sub(Nat.sub(bs, 1n), Nat.mod(t, bs))
  +r = Nat.sub(n, Nat.add(f, c))
  +en = Equal.trans(Nat, Nat.add(f, Nat.add(c, r)), Nat.add(Nat.add(f, c), r), n, Equal.sym(Nat, Nat.add(Nat.add(f, c), r), Nat.add(f, Nat.add(c, r)), UL.nat_add_assoc(f, c, r)), BR.le_wit(Nat.add(f, c), n, BR.span_le(bp, off, len, n, hr)))
  +hn = BR.u_rw(~T, ~read_block, n, Nat.add(f, Nat.add(c, r)), d, bs, 0n, Equal.sym(Nat, Nat.add(f, Nat.add(c, r)), n, en), hu)
  +hf = BR.u4a(~T, ~read_block, f, Nat.add(c, r), d, bs, 0n, hn)
  +hcr = BR.u4b(~T, ~read_block, f, Nat.add(c, r), d, bs, 0n, hn)
  +hc = BR.u4a(~T, ~read_block, c, r, d, bs, f, hcr)
  +a = BR.img(~T, ~read_block, f, d, 0n)
  +m = BR.img(~T, ~read_block, c, d, f)
  +z = BR.img(~T, ~read_block, r, d, Nat.add(f, c))
  +eoff = Equal.trans(Nat, Nat.add(B.Octets.len(a), s), Nat.add(Nat.mul(f, bs), s), off, Equal.cong(Nat, Nat, x => Nat.add(x, s), B.Octets.len(a), Nat.mul(f, bs), BR.u2(~T, ~read_block, f, d, bs, 0n, hf)), UD.nat_div_mod(off, bp))
  +hle = P.IP.le_rw_r(Nat.add(s, len), B.Octets.len(m), Nat.mul(c, bs), BR.u2(~T, ~read_block, c, d, bs, f, hc), P.IP.le_rw_r(Nat.add(s, len), Nat.mul(c, bs), Nat.add(Nat.add(s, len), l), UD.nat_round_up(bp, Nat.add(s, len)), UO.nat_le_add_r(Nat.add(s, len), l)))
  %Equal.cong(Nat, B.Octets, k => BR.img(~T, ~read_block, k, d, 0n), Nat.add(f, Nat.add(c, r)), n, en) : {B.Octets.slice(off, len, _) == B.Octets.slice(s, len, m) : B.Octets}
  %Equal.sym(B.Octets, BR.img(~T, ~read_block, Nat.add(f, Nat.add(c, r)), d, 0n), B.Octets.append(a, BR.img(~T, ~read_block, Nat.add(c, r), d, f)), BR.u3(~T, ~read_block, f, Nat.add(c, r), d, 0n)) : {B.Octets.slice(off, len, _) == B.Octets.slice(s, len, m) : B.Octets}
  %Equal.sym(B.Octets, BR.img(~T, ~read_block, Nat.add(c, r), d, f), B.Octets.append(m, z), BR.u3(~T, ~read_block, c, r, d, f)) : {B.Octets.slice(off, len, B.Octets.append(a, _)) == B.Octets.slice(s, len, m) : B.Octets}
  %eoff : {B.Octets.slice(_, len, B.Octets.append(a, B.Octets.append(m, z))) == B.Octets.slice(s, len, m) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(a), s), len, B.Octets.append(a, B.Octets.append(m, z))), B.Octets.slice(s, len, B.Octets.append(m, z)), BL.octets_slice_append_add(a, s, len, B.Octets.append(m, z))) : {_ == B.Octets.slice(s, len, m) : B.Octets}
  BL.octets_slice_append_le(s, len, m, z, hle)

def BR.core(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +bp: Nat, +n: Nat, +off: Nat, +len: Nat, +hu: {D.Dev.uniform.go(~T, ~read_block, n, d, 1n+bp, 0n) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, len), Nat.mul(n, 1n+bp)) == True{} : Bool}) -> {D.Dev.read_bytes.go(~T, ~read_block, d, 1n+bp, off, len) == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), D.Dev.read_blocks(~T, ~read_block, d, n, 0n)) : Result<&2, &2, D.DevError, B.Octets>}:
  +bs : Nat = 1n+bp
  +s = Nat.mod(off, bs)
  +f = Nat.div(off, bs)
  +t = Nat.add(Nat.add(s, len), Nat.sub(bs, 1n))
  +c = Nat.div(t, bs)
  +r = Nat.sub(n, Nat.add(f, c))
  +en = Equal.trans(Nat, Nat.add(f, Nat.add(c, r)), Nat.add(Nat.add(f, c), r), n, Equal.sym(Nat, Nat.add(Nat.add(f, c), r), Nat.add(f, Nat.add(c, r)), UL.nat_add_assoc(f, c, r)), BR.le_wit(Nat.add(f, c), n, BR.span_le(bp, off, len, n, hr)))
  +hn = BR.u_rw(~T, ~read_block, n, Nat.add(f, Nat.add(c, r)), d, bs, 0n, Equal.sym(Nat, Nat.add(f, Nat.add(c, r)), n, en), hu)
  +hcr = BR.u4b(~T, ~read_block, f, Nat.add(c, r), d, bs, 0n, hn)
  +hc = BR.u4a(~T, ~read_block, c, r, d, bs, f, hcr)
  +m = BR.img(~T, ~read_block, c, d, f)
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~T, ~read_block, d, c, f), Done{m}, BR.u1(~T, ~read_block, c, d, bs, f, hc)) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(s, len, blocks))) == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), D.Dev.read_blocks(~T, ~read_block, d, n, 0n)) : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~T, ~read_block, d, n, 0n), Done{BR.img(~T, ~read_block, n, d, 0n)}, BR.u1(~T, ~read_block, n, d, bs, 0n, hu)) : {Done{B.Octets.slice(s, len, m)} == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), _) : Result<&2, &2, D.DevError, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, x => Done{x}, B.Octets.slice(s, len, m), B.Octets.slice(off, len, BR.img(~T, ~read_block, n, d, 0n)), Equal.sym(B.Octets, B.Octets.slice(off, len, BR.img(~T, ~read_block, n, d, 0n)), B.Octets.slice(s, len, m), BR.core_eq(~T, ~read_block, d, bp, n, off, len, hu, hr)))

def BR.image(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: D, +bp: Nat, +n: Nat, +off: Nat, +len: Nat, +hbs: {block_size(d) == 1n+bp : Nat}, +hu: {D.Dev.uniform(~D, ~block_size, ~read_block, d, n) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(off, len), Nat.mul(n, 1n+bp)) == True{} : Bool}) -> {D.Dev.read_bytes(~D, ~block_size, ~read_block, d, off, len) == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), D.Dev.read_blocks(~D, ~read_block, d, n, 0n)) : Result<&2, &2, D.DevError, B.Octets>}:
  match len:
    case 0n:
      +hu2 = BR.u_bs(~D, ~block_size, ~read_block, d, n, bp, hbs, hu)
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D, ~read_block, d, n, 0n), Done{BR.img(~D, ~read_block, n, d, 0n)}, BR.u1(~D, ~read_block, n, d, 1n+bp, 0n, hu2)) : {Done{B.Octets.empty()} == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, 0n, o), _) : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(B.Octets, B.Octets.take(0n, B.Octets.drop(off, BR.img(~D, ~read_block, n, d, 0n))), B.Octets.empty(), BR.take0(B.Octets.drop(off, BR.img(~D, ~read_block, n, d, 0n)))) : {Done{B.Octets.empty()} == Done{_} : Result<&2, &2, D.DevError, B.Octets>}
      {==}
    case 1n+ +lp:
      +hu2 = BR.u_bs(~D, ~block_size, ~read_block, d, n, bp, hbs, hu)
      %Equal.sym(Nat, block_size(d), 1n+bp, hbs) : {D.Dev.read_bytes.go(~D, ~read_block, d, _, off, 1n+lp) == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, 1n+lp, o), D.Dev.read_blocks(~D, ~read_block, d, n, 0n)) : Result<&2, &2, D.DevError, B.Octets>}
      BR.core(~D, ~read_block, d, bp, n, off, 1n+lp, hu2, hr)

def Laws.read_bytes_image(D, block_size, read_block, d, bp, n, off, len, hbs, hu, hr):
  BR.image(~D, ~block_size, ~read_block, d, bp, n, off, len, hbs, hu, hr)

# read_blocks is read_list joined

def BR.rl_step(+blk: B.Octets, q: Result<&2, &2, D.DevError, List<&2, B.Octets>>) -> {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), q), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest))) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, q, rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest}))) : Result<&2, &2, D.DevError, B.Octets>}:
  match q:
    case Done{xs}:
      %Equal.sym(B.Octets, B.Octets.concat(Con{blk, xs}), B.Octets.append(blk, B.Octets.concat(xs)), BL.octets_concat_cons(blk, xs)) : {Done{B.Octets.append(blk, B.Octets.concat(xs))} == Done{_} : Result<&2, &2, D.DevError, B.Octets>}
      {==}
    case Fail{e}:
      {==}

def BR.rl_head(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +p: Nat, +first: Nat, r: Result<&2, &2, D.DevError, B.Octets>, +ih: {D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(first, 1n)) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n))) : Result<&2, &2, D.DevError, B.Octets>}) -> {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, r, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), Result.bind(&2, &2, D.DevError, B.Octets, List<&2, B.Octets>, r, blk => Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest})))) : Result<&2, &2, D.DevError, B.Octets>}:
  match r:
    case Done{+blk}:
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(first, 1n)), Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n))), ih) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest))) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), Result.bind(&2, &2, D.DevError, List<&2, B.Octets>, List<&2, B.Octets>, D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, List<&2, B.Octets>, Con{blk, rest}))) : Result<&2, &2, D.DevError, B.Octets>}
      BR.rl_step(blk, D.Dev.read_list(~T, ~read_block, d, p, Nat.add(first, 1n)))
    case Fail{e}:
      {==}

def BR.read_list(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +count: Nat, +first: Nat) -> {D.Dev.read_blocks(~T, ~read_block, d, count, first) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), D.Dev.read_list(~T, ~read_block, d, count, first)) : Result<&2, &2, D.DevError, B.Octets>}:
  match count:
    case 0n:
      {==}
    case 1n+ +p:
      BR.rl_head(~T, ~read_block, d, p, first, read_block(d, first), BR.read_list(~T, ~read_block, d, p, Nat.add(first, 1n)))

def Laws.read_blocks_list(D, read_block, d, count, first):
  BR.read_list(~D, ~read_block, d, count, first)

# Patching an image

def BR.patch_len(+off: Nat, +data: B.Octets, +o: B.Octets, +h: {Nat.is_le(Nat.add(off, B.Octets.len(data)), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.len(D.Dev.patch(off, data, o)) == B.Octets.len(o) : Nat}:
  +l = B.Octets.len(data)
  +tk = B.Octets.take(off, o)
  +dr = B.Octets.drop(Nat.add(off, l), o)
  +hoff = UO.nat_le_trans(off, Nat.add(off, l), B.Octets.len(o), UO.nat_le_add_r(off, l), h)
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(tk, B.Octets.append(data, dr))), Nat.add(B.Octets.len(tk), B.Octets.len(B.Octets.append(data, dr))), BL.octets_len_append(tk, B.Octets.append(data, dr))) : {_ == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(data, dr)), Nat.add(l, B.Octets.len(dr)), BL.octets_len_append(data, dr)) : {Nat.add(B.Octets.len(tk), _) == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(tk), off, BL.octets_len_take_le(off, o, hoff)) : {Nat.add(_, Nat.add(l, B.Octets.len(dr))) == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(dr), Nat.sub(B.Octets.len(o), Nat.add(off, l)), BL.octets_len_drop(Nat.add(off, l), o)) : {Nat.add(off, Nat.add(l, _)) == B.Octets.len(o) : Nat}
  %UL.nat_add_assoc(off, l, Nat.sub(B.Octets.len(o), Nat.add(off, l))) : {_ == B.Octets.len(o) : Nat}
  BR.le_wit(Nat.add(off, l), B.Octets.len(o), h)

def Laws.patch_len(off, data, o, h):
  BR.patch_len(off, data, o, h)

def BR.patch_slice(+off: Nat, +data: B.Octets, +o: B.Octets, +h: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.slice(off, B.Octets.len(data), D.Dev.patch(off, data, o)) == data : B.Octets}:
  +l = B.Octets.len(data)
  +tk = B.Octets.take(off, o)
  +dr = B.Octets.drop(Nat.add(off, l), o)
  +et = Equal.trans(Nat, Nat.add(B.Octets.len(tk), 0n), B.Octets.len(tk), off, UL.nat_add_zero(B.Octets.len(tk)), BL.octets_len_take_le(off, o, h))
  %et : {B.Octets.slice(_, l, B.Octets.append(tk, B.Octets.append(data, dr))) == data : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(tk), 0n), l, B.Octets.append(tk, B.Octets.append(data, dr))), B.Octets.slice(0n, l, B.Octets.append(data, dr)), BL.octets_slice_append_add(tk, 0n, l, B.Octets.append(data, dr))) : {_ == data : B.Octets}
  BR.slice_head(data, dr)

def Laws.patch_slice(off, data, o, h):
  BR.patch_slice(off, data, o, h)

def BR.patch_before(+i: Nat, +n: Nat, +off: Nat, +data: B.Octets, +o: B.Octets, +h: {Nat.is_le(Nat.add(i, n), off) == True{} : Bool}, +ho: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.slice(i, n, D.Dev.patch(off, data, o)) == B.Octets.slice(i, n, o) : B.Octets}:
  +tk = B.Octets.take(off, o)
  +rest = B.Octets.append(data, B.Octets.drop(Nat.add(off, B.Octets.len(data)), o))
  +ht = P.IP.le_rw_r(Nat.add(i, n), B.Octets.len(tk), off, BL.octets_len_take_le(off, o, ho), h)
  %Equal.sym(B.Octets, B.Octets.slice(i, n, B.Octets.append(tk, rest)), B.Octets.slice(i, n, tk), BL.octets_slice_append_le(i, n, tk, rest, ht)) : {_ == B.Octets.slice(i, n, o) : B.Octets}
  BL.octets_slice_take(off, i, n, o, h)

def Laws.patch_before(i, n, off, data, o, h, ho):
  BR.patch_before(i, n, off, data, o, h, ho)

def BR.patch_after(+i: Nat, +n: Nat, +off: Nat, +data: B.Octets, +o: B.Octets, +h: {Nat.is_le(Nat.add(off, B.Octets.len(data)), i) == True{} : Bool}, +ho: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.slice(i, n, D.Dev.patch(off, data, o)) == B.Octets.slice(i, n, o) : B.Octets}:
  +l = B.Octets.len(data)
  +tk = B.Octets.take(off, o)
  +dr = B.Octets.drop(Nat.add(off, l), o)
  +j = Nat.sub(i, Nat.add(off, l))
  +ei = BR.le_wit(Nat.add(off, l), i, h)
  +e1 = Equal.trans(Nat, Nat.add(B.Octets.len(tk), Nat.add(l, j)), Nat.add(off, Nat.add(l, j)), i, Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(l, j)), B.Octets.len(tk), off, BL.octets_len_take_le(off, o, ho)), Equal.trans(Nat, Nat.add(off, Nat.add(l, j)), Nat.add(Nat.add(off, l), j), i, Equal.sym(Nat, Nat.add(Nat.add(off, l), j), Nat.add(off, Nat.add(l, j)), UL.nat_add_assoc(off, l, j)), ei))
  %e1 : {B.Octets.slice(_, n, B.Octets.append(tk, B.Octets.append(data, dr))) == B.Octets.slice(i, n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(tk), Nat.add(l, j)), n, B.Octets.append(tk, B.Octets.append(data, dr))), B.Octets.slice(Nat.add(l, j), n, B.Octets.append(data, dr)), BL.octets_slice_append_add(tk, Nat.add(l, j), n, B.Octets.append(data, dr))) : {_ == B.Octets.slice(i, n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(l, j), n, B.Octets.append(data, dr)), B.Octets.slice(j, n, dr), BL.octets_slice_append_add(data, j, n, dr)) : {_ == B.Octets.slice(i, n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(j, n, dr), B.Octets.slice(Nat.add(Nat.add(off, l), j), n, o), BL.octets_slice_drop(Nat.add(off, l), j, n, o)) : {_ == B.Octets.slice(i, n, o) : B.Octets}
  %ei : {B.Octets.slice(Nat.add(Nat.add(off, l), j), n, o) == B.Octets.slice(_, n, o) : B.Octets}
  {==}

def Laws.patch_after(i, n, off, data, o, h, ho):
  BR.patch_after(i, n, off, data, o, h, ho)

def BR.patch_patch(+off: Nat, +a: B.Octets, +b: B.Octets, +o: B.Octets, +h: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}) -> {D.Dev.patch(Nat.add(off, B.Octets.len(a)), b, D.Dev.patch(off, a, o)) == D.Dev.patch(off, B.Octets.append(a, b), o) : B.Octets}:
  +la = B.Octets.len(a)
  +lb = B.Octets.len(b)
  +tk = B.Octets.take(off, o)
  +r1 = B.Octets.drop(Nat.add(off, la), o)
  +p1 = B.Octets.append(tk, B.Octets.append(a, r1))
  +rhs = D.Dev.patch(off, B.Octets.append(a, b), o)
  +et = BL.octets_len_take_le(off, o, h)
  %et : {B.Octets.append(B.Octets.take(Nat.add(_, la), p1), B.Octets.append(b, B.Octets.drop(Nat.add(Nat.add(off, la), lb), p1))) == rhs : B.Octets}
  %Equal.sym(B.Octets, B.Octets.take(Nat.add(B.Octets.len(tk), la), p1), B.Octets.append(tk, B.Octets.take(la, B.Octets.append(a, r1))), BL.octets_take_append_add(tk, la, B.Octets.append(a, r1))) : {B.Octets.append(_, B.Octets.append(b, B.Octets.drop(Nat.add(Nat.add(off, la), lb), p1))) == rhs : B.Octets}
  %Equal.sym(B.Octets, B.Octets.take(la, B.Octets.append(a, r1)), a, BL.octets_take_append(a, r1)) : {B.Octets.append(B.Octets.append(tk, _), B.Octets.append(b, B.Octets.drop(Nat.add(Nat.add(off, la), lb), p1))) == rhs : B.Octets}
  +e1 = Equal.trans(Nat, Nat.add(B.Octets.len(tk), Nat.add(la, lb)), Nat.add(off, Nat.add(la, lb)), Nat.add(Nat.add(off, la), lb), Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(la, lb)), B.Octets.len(tk), off, et), Equal.sym(Nat, Nat.add(Nat.add(off, la), lb), Nat.add(off, Nat.add(la, lb)), UL.nat_add_assoc(off, la, lb)))
  %e1 : {B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, B.Octets.drop(_, p1))) == rhs : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(tk), Nat.add(la, lb)), p1), B.Octets.drop(Nat.add(la, lb), B.Octets.append(a, r1)), BL.octets_drop_append_add(tk, Nat.add(la, lb), B.Octets.append(a, r1))) : {B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, _)) == rhs : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(la, lb), B.Octets.append(a, r1)), B.Octets.drop(lb, r1), BL.octets_drop_append_add(a, lb, r1)) : {B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, _)) == rhs : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(lb, r1), B.Octets.drop(Nat.add(Nat.add(off, la), lb), o), BL.octets_drop_drop(Nat.add(off, la), lb, o)) : {B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, _)) == rhs : B.Octets}
  +dr = B.Octets.drop(Nat.add(Nat.add(off, la), lb), o)
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(a, b)), Nat.add(la, lb), BL.octets_len_append(a, b)) : {B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, dr)) == B.Octets.append(tk, B.Octets.append(B.Octets.append(a, b), B.Octets.drop(Nat.add(off, _), o))) : B.Octets}
  %UL.nat_add_assoc(off, la, lb) : {B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, dr)) == B.Octets.append(tk, B.Octets.append(B.Octets.append(a, b), B.Octets.drop(_, o))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(tk, a), B.Octets.append(b, dr)), B.Octets.append(tk, B.Octets.append(a, B.Octets.append(b, dr))), BL.octets_append_assoc(tk, a, B.Octets.append(b, dr))) : {_ == B.Octets.append(tk, B.Octets.append(B.Octets.append(a, b), dr)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(a, b), dr), B.Octets.append(a, B.Octets.append(b, dr)), BL.octets_append_assoc(a, b, dr)) : {B.Octets.append(tk, B.Octets.append(a, B.Octets.append(b, dr))) == B.Octets.append(tk, _) : B.Octets}
  {==}

def Laws.patch_patch(off, a, b, o, h):
  BR.patch_patch(off, a, b, o, h)

# take(a + i, o) is take(a, o) then the i bytes after
def BR.take_split(+a: Nat, +i: Nat, +o: B.Octets, +ha: {Nat.is_le(a, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.take(Nat.add(a, i), o) == B.Octets.append(B.Octets.take(a, o), B.Octets.slice(a, i, o)) : B.Octets}:
  +tk = B.Octets.take(a, o)
  %BL.octets_take_drop(a, o) : {B.Octets.take(Nat.add(a, i), _) == B.Octets.append(tk, B.Octets.slice(a, i, o)) : B.Octets}
  %BL.octets_len_take_le(a, o, ha) : {B.Octets.take(Nat.add(_, i), B.Octets.append(tk, B.Octets.drop(a, o))) == B.Octets.append(tk, B.Octets.slice(a, i, o)) : B.Octets}
  BL.octets_take_append_add(tk, i, B.Octets.drop(a, o))

# drop(m, o) is the j bytes from m then drop(m + j, o)
def BR.drop_split(+m: Nat, +j: Nat, +o: B.Octets) -> {B.Octets.drop(m, o) == B.Octets.append(B.Octets.slice(m, j, o), B.Octets.drop(Nat.add(m, j), o)) : B.Octets}:
  +x = B.Octets.drop(m, o)
  %BL.octets_drop_drop(m, j, o) : {x == B.Octets.append(B.Octets.take(j, x), _) : B.Octets}
  Equal.sym(B.Octets, B.Octets.append(B.Octets.take(j, x), B.Octets.drop(j, x)), x, BL.octets_take_drop(j, x))

def BR.patch_keep(+a: Nat, +i: Nat, +data: B.Octets, +j: Nat, +o: B.Octets, +h: {Nat.is_le(Nat.add(Nat.add(Nat.add(a, i), B.Octets.len(data)), j), B.Octets.len(o)) == True{} : Bool}) -> {D.Dev.patch(a, B.Octets.append(B.Octets.slice(a, i, o), B.Octets.append(data, B.Octets.slice(Nat.add(Nat.add(a, i), B.Octets.len(data)), j, o))), o) == D.Dev.patch(Nat.add(a, i), data, o) : B.Octets}:
  +l = B.Octets.len(data)
  +ai = Nat.add(a, i)
  +m = Nat.add(ai, l)
  +s1 = B.Octets.slice(a, i, o)
  +s2 = B.Octets.slice(m, j, o)
  +buf = B.Octets.append(s1, B.Octets.append(data, s2))
  +tk = B.Octets.take(a, o)
  +rest = B.Octets.drop(Nat.add(m, j), o)
  +hm = UO.nat_le_trans(m, Nat.add(m, j), B.Octets.len(o), UO.nat_le_add_r(m, j), h)
  +hai = UO.nat_le_trans(ai, m, B.Octets.len(o), UO.nat_le_add_r(ai, l), hm)
  +ha = UO.nat_le_trans(a, ai, B.Octets.len(o), UO.nat_le_add_r(a, i), hai)
  +l1 = BL.octets_len_slice_le(a, i, o, hai)
  +l2 = BL.octets_len_slice_le(m, j, o, h)
  +lb = Equal.trans(Nat, B.Octets.len(buf), Nat.add(B.Octets.len(s1), B.Octets.len(B.Octets.append(data, s2))), Nat.add(i, Nat.add(l, j)), BL.octets_len_append(s1, B.Octets.append(data, s2)), Equal.trans(Nat, Nat.add(B.Octets.len(s1), B.Octets.len(B.Octets.append(data, s2))), Nat.add(i, Nat.add(l, B.Octets.len(s2))), Nat.add(i, Nat.add(l, j)), Equal.trans(Nat, Nat.add(B.Octets.len(s1), B.Octets.len(B.Octets.append(data, s2))), Nat.add(i, B.Octets.len(B.Octets.append(data, s2))), Nat.add(i, Nat.add(l, B.Octets.len(s2))), Equal.cong(Nat, Nat, x => Nat.add(x, B.Octets.len(B.Octets.append(data, s2))), B.Octets.len(s1), i, l1), Equal.cong(Nat, Nat, x => Nat.add(i, x), B.Octets.len(B.Octets.append(data, s2)), Nat.add(l, B.Octets.len(s2)), BL.octets_len_append(data, s2))), Equal.cong(Nat, Nat, x => Nat.add(i, Nat.add(l, x)), B.Octets.len(s2), j, l2)))
  +ek = Equal.trans(Nat, Nat.add(a, B.Octets.len(buf)), Nat.add(a, Nat.add(i, Nat.add(l, j))), Nat.add(m, j), Equal.cong(Nat, Nat, x => Nat.add(a, x), B.Octets.len(buf), Nat.add(i, Nat.add(l, j)), lb), Equal.trans(Nat, Nat.add(a, Nat.add(i, Nat.add(l, j))), Nat.add(ai, Nat.add(l, j)), Nat.add(m, j), Equal.sym(Nat, Nat.add(ai, Nat.add(l, j)), Nat.add(a, Nat.add(i, Nat.add(l, j))), UL.nat_add_assoc(a, i, Nat.add(l, j))), Equal.sym(Nat, Nat.add(m, j), Nat.add(ai, Nat.add(l, j)), UL.nat_add_assoc(ai, l, j))))
  +rhs0 = B.Octets.append(B.Octets.take(ai, o), B.Octets.append(data, B.Octets.drop(m, o)))
  %Equal.sym(Nat, Nat.add(a, B.Octets.len(buf)), Nat.add(m, j), ek) : {B.Octets.append(tk, B.Octets.append(buf, B.Octets.drop(_, o))) == rhs0 : B.Octets}
  %Equal.sym(B.Octets, B.Octets.take(ai, o), B.Octets.append(tk, s1), BR.take_split(a, i, o, ha)) : {B.Octets.append(tk, B.Octets.append(buf, rest)) == B.Octets.append(_, B.Octets.append(data, B.Octets.drop(m, o))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(m, o), B.Octets.append(s2, rest), BR.drop_split(m, j, o)) : {B.Octets.append(tk, B.Octets.append(buf, rest)) == B.Octets.append(B.Octets.append(tk, s1), B.Octets.append(data, _)) : B.Octets}
  +w = B.Octets.append(data, B.Octets.append(s2, rest))
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(tk, s1), w), B.Octets.append(tk, B.Octets.append(s1, w)), BL.octets_append_assoc(tk, s1, w)) : {B.Octets.append(tk, B.Octets.append(buf, rest)) == _ : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(buf, rest), B.Octets.append(s1, B.Octets.append(B.Octets.append(data, s2), rest)), BL.octets_append_assoc(s1, B.Octets.append(data, s2), rest)) : {B.Octets.append(tk, _) == B.Octets.append(tk, B.Octets.append(s1, w)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(data, s2), rest), w, BL.octets_append_assoc(data, s2, rest)) : {B.Octets.append(tk, B.Octets.append(s1, _)) == B.Octets.append(tk, B.Octets.append(s1, w)) : B.Octets}
  {==}

def Laws.patch_keep(a, i, data, j, o, h):
  BR.patch_keep(a, i, data, j, o, h)

# More facts for MemDev

def BR.lt_rw_r(-k: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, h: {Nat.is_lt(k, y) == True{} : Bool}) -> {Nat.is_lt(k, x) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(k, _) == True{} : Bool}
  h

def BR.and_tt(+a: Bool, +b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# j + (k + (c - (j + k))) == c when j + k <= c
def BR.split3(+j: Nat, +k: Nat, +c: Nat, +h: {Nat.is_le(Nat.add(j, k), c) == True{} : Bool}) -> {Nat.add(j, Nat.add(k, Nat.sub(c, Nat.add(j, k)))) == c : Nat}:
  +r = Nat.sub(c, Nat.add(j, k))
  Equal.trans(Nat, Nat.add(j, Nat.add(k, r)), Nat.add(Nat.add(j, k), r), c, Equal.sym(Nat, Nat.add(Nat.add(j, k), r), Nat.add(j, Nat.add(k, r)), UL.nat_add_assoc(j, k, r)), BR.le_wit(Nat.add(j, k), c, h))

# uniform over n blocks: uniform over blocks j to j + k - 1, and they read as
# the slice of the image they name
def BR.u_sub(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +bs: Nat, +n: Nat, +j: Nat, +k: Nat, +hu: {D.Dev.uniform.go(~T, ~read_block, n, d, bs, 0n) == True{} : Bool}, +h: {Nat.is_le(Nat.add(j, k), n) == True{} : Bool}) -> {D.Dev.uniform.go(~T, ~read_block, k, d, bs, j) == True{} : Bool}:
  +r = Nat.sub(n, Nat.add(j, k))
  +hn = BR.u_rw(~T, ~read_block, n, Nat.add(j, Nat.add(k, r)), d, bs, 0n, Equal.sym(Nat, Nat.add(j, Nat.add(k, r)), n, BR.split3(j, k, n, h)), hu)
  BR.u4a(~T, ~read_block, k, r, d, bs, j, BR.u4b(~T, ~read_block, j, Nat.add(k, r), d, bs, 0n, hn))

def BR.img_slice(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +bs: Nat, +n: Nat, +j: Nat, +k: Nat, +hu: {D.Dev.uniform.go(~T, ~read_block, n, d, bs, 0n) == True{} : Bool}, +h: {Nat.is_le(Nat.add(j, k), n) == True{} : Bool}) -> {B.Octets.slice(Nat.mul(j, bs), Nat.mul(k, bs), BR.img(~T, ~read_block, n, d, 0n)) == BR.img(~T, ~read_block, k, d, j) : B.Octets}:
  +r = Nat.sub(n, Nat.add(j, k))
  +en = BR.split3(j, k, n, h)
  +hn = BR.u_rw(~T, ~read_block, n, Nat.add(j, Nat.add(k, r)), d, bs, 0n, Equal.sym(Nat, Nat.add(j, Nat.add(k, r)), n, en), hu)
  +hj = BR.u4a(~T, ~read_block, j, Nat.add(k, r), d, bs, 0n, hn)
  +hk = BR.u4a(~T, ~read_block, k, r, d, bs, j, BR.u4b(~T, ~read_block, j, Nat.add(k, r), d, bs, 0n, hn))
  +a = BR.img(~T, ~read_block, j, d, 0n)
  +m = BR.img(~T, ~read_block, k, d, j)
  +z = BR.img(~T, ~read_block, r, d, Nat.add(j, k))
  %Equal.cong(Nat, B.Octets, x => BR.img(~T, ~read_block, x, d, 0n), Nat.add(j, Nat.add(k, r)), n, en) : {B.Octets.slice(Nat.mul(j, bs), Nat.mul(k, bs), _) == m : B.Octets}
  %Equal.sym(B.Octets, BR.img(~T, ~read_block, Nat.add(j, Nat.add(k, r)), d, 0n), B.Octets.append(a, BR.img(~T, ~read_block, Nat.add(k, r), d, j)), BR.u3(~T, ~read_block, j, Nat.add(k, r), d, 0n)) : {B.Octets.slice(Nat.mul(j, bs), Nat.mul(k, bs), _) == m : B.Octets}
  %Equal.sym(B.Octets, BR.img(~T, ~read_block, Nat.add(k, r), d, j), B.Octets.append(m, z), BR.u3(~T, ~read_block, k, r, d, j)) : {B.Octets.slice(Nat.mul(j, bs), Nat.mul(k, bs), B.Octets.append(a, _)) == m : B.Octets}
  %BR.u2(~T, ~read_block, j, d, bs, 0n, hj) : {B.Octets.slice(_, Nat.mul(k, bs), B.Octets.append(a, B.Octets.append(m, z))) == m : B.Octets}
  %BR.u2(~T, ~read_block, k, d, bs, j, hk) : {B.Octets.slice(B.Octets.len(a), _, B.Octets.append(a, B.Octets.append(m, z))) == m : B.Octets}
  BR.slice_mid(a, m, z)

# MemDev: a read outside the device, and inside it

def BR.read_out(+bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +h: {Nat.is_lt(n, c) == False{} : Bool}) -> {D.MemDev.read_block(D.MemDev{bs, c, t}, n) == Fail{D.DevOutOfRange{n}} : Result<&2, &2, D.DevError, B.Octets>}:
  %Equal.sym(Bool, Nat.is_lt(n, c), False{}, h) : {D.MemDev.read.check(_, bs, t, n) == Fail{D.DevOutOfRange{n}} : Result<&2, &2, D.DevError, B.Octets>}
  {==}

def Laws.read_block_out(d, n, h):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BR.read_out(bs, c, t, n, h)

def BR.read_in(+bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +h: {Nat.is_lt(n, c) == True{} : Bool}) -> {D.MemDev.read_block(D.MemDev{bs, c, t}, n) == Done{D.MemDev.read.got(bs, D.MemTree.get(t, n))} : Result<&2, &2, D.DevError, B.Octets>}:
  %Equal.sym(Bool, Nat.is_lt(n, c), True{}, h) : {D.MemDev.read.check(_, bs, t, n) == Done{D.MemDev.read.got(bs, D.MemTree.get(t, n))} : Result<&2, &2, D.DevError, B.Octets>}
  {==}

# The image: to_octets(d) is the blocks d reads, joined

def BR.concat_go(+k: Nat, +bs: Nat, +t: D.MemTree, +acc: List<&2, B.Octets>) -> {B.Octets.concat(D.MemDev.blocks.go(k, bs, t, acc)) == B.Octets.append(B.Octets.concat(D.MemDev.blocks.go(k, bs, t, Nil{})), B.Octets.concat(acc)) : B.Octets}:
  match k:
    case 0n:
      Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), B.Octets.concat(acc)), B.Octets.concat(acc), BL.octets_append_empty_l(B.Octets.concat(acc)))
    case 1n+ +q:
      +b = D.MemDev.read.got(bs, D.MemTree.get(t, q))
      +x = B.Octets.concat(D.MemDev.blocks.go(q, bs, t, Nil{}))
      %Equal.sym(B.Octets, B.Octets.concat(D.MemDev.blocks.go(q, bs, t, Con{b, acc})), B.Octets.append(x, B.Octets.concat(Con{b, acc})), BR.concat_go(q, bs, t, Con{b, acc})) : {_ == B.Octets.append(B.Octets.concat(D.MemDev.blocks.go(q, bs, t, Con{b, Nil{}})), B.Octets.concat(acc)) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(D.MemDev.blocks.go(q, bs, t, Con{b, Nil{}})), B.Octets.append(x, B.Octets.concat(Con{b, Nil{}})), BR.concat_go(q, bs, t, Con{b, Nil{}})) : {B.Octets.append(x, B.Octets.concat(Con{b, acc})) == B.Octets.append(_, B.Octets.concat(acc)) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(Con{b, acc}), B.Octets.append(b, B.Octets.concat(acc)), BL.octets_concat_cons(b, acc)) : {B.Octets.append(x, _) == B.Octets.append(B.Octets.append(x, B.Octets.concat(Con{b, Nil{}})), B.Octets.concat(acc)) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(Con{b, Nil{}}), B.Octets.append(b, B.Octets.concat(Nil{})), BL.octets_concat_cons(b, Nil{})) : {B.Octets.append(x, B.Octets.append(b, B.Octets.concat(acc))) == B.Octets.append(B.Octets.append(x, _), B.Octets.concat(acc)) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.append(b, B.Octets.empty()), b, BL.octets_append_empty_r(b)) : {B.Octets.append(x, B.Octets.append(b, B.Octets.concat(acc))) == B.Octets.append(B.Octets.append(x, _), B.Octets.concat(acc)) : B.Octets}
      Equal.sym(B.Octets, B.Octets.append(B.Octets.append(x, b), B.Octets.concat(acc)), B.Octets.append(x, B.Octets.append(b, B.Octets.concat(acc))), BL.octets_append_assoc(x, b, B.Octets.concat(acc)))

def BR.mem_img(+k: Nat, +bs: Nat, +c: Nat, +t: D.MemTree, +h: {Nat.is_le(k, c) == True{} : Bool}) -> {BR.img(~D.MemDev, ~D.MemDev.read_block, k, D.MemDev{bs, c, t}, 0n) == B.Octets.concat(D.MemDev.blocks.go(k, bs, t, Nil{})) : B.Octets}:
  match k:
    case 0n:
      {==}
    case 1n+ +q:
      +d : D.MemDev = D.MemDev{bs, c, t}
      +b = D.MemDev.read.got(bs, D.MemTree.get(t, q))
      +hlt = P.IP.le_lt(q, c, h)
      +x = B.Octets.concat(D.MemDev.blocks.go(q, bs, t, Nil{}))
      %P.IP.add_one(q) : {BR.img(~D.MemDev, ~D.MemDev.read_block, _, d, 0n) == B.Octets.concat(D.MemDev.blocks.go(1n+q, bs, t, Nil{})) : B.Octets}
      %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, Nat.add(q, 1n), d, 0n), B.Octets.append(BR.img(~D.MemDev, ~D.MemDev.read_block, q, d, 0n), BR.img(~D.MemDev, ~D.MemDev.read_block, 1n, d, q)), BR.u3(~D.MemDev, ~D.MemDev.read_block, q, 1n, d, 0n)) : {_ == B.Octets.concat(D.MemDev.blocks.go(1n+q, bs, t, Nil{})) : B.Octets}
      %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, q, d, 0n), x, BR.mem_img(q, bs, c, t, BR.lt_to_le(q, c, hlt))) : {B.Octets.append(_, BR.img(~D.MemDev, ~D.MemDev.read_block, 1n, d, q)) == B.Octets.concat(D.MemDev.blocks.go(1n+q, bs, t, Nil{})) : B.Octets}
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d, q), Done{b}, BR.read_in(bs, c, t, q, hlt)) : {B.Octets.append(x, B.Octets.append(BR.got(_), B.Octets.empty())) == B.Octets.concat(D.MemDev.blocks.go(1n+q, bs, t, Nil{})) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(D.MemDev.blocks.go(q, bs, t, Con{b, Nil{}})), B.Octets.append(x, B.Octets.concat(Con{b, Nil{}})), BR.concat_go(q, bs, t, Con{b, Nil{}})) : {B.Octets.append(x, B.Octets.append(b, B.Octets.empty())) == _ : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(Con{b, Nil{}}), B.Octets.append(b, B.Octets.concat(Nil{})), BL.octets_concat_cons(b, Nil{})) : {B.Octets.append(x, B.Octets.append(b, B.Octets.empty())) == B.Octets.append(x, _) : B.Octets}
      {==}

def BR.to_img(+d: D.MemDev) -> {D.MemDev.to_octets(d) == BR.img(~D.MemDev, ~D.MemDev.read_block, D.MemDev.block_count(d), d, 0n) : B.Octets}:
  match d:
    case D.MemDev{+bs, +c, +t}:
      Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, c, D.MemDev{bs, c, t}, 0n), B.Octets.concat(D.MemDev.blocks.go(c, bs, t, Nil{})), BR.mem_img(c, bs, c, t, UL.nat_le_refl(c)))

# Validity: a tree whose leaves are whole blocks gives a valid device

def BR.tree_ok(t: D.MemTree, +bs: Nat) -> Bool:
  match t:
    case D.MemTEmpty{}:
      True{}
    case D.MemTLeaf{b}:
      Nat.is_eq(B.Octets.len(b), bs)
    case D.MemTNode{k, l, r}:
      Bool.and(BR.tree_ok(l, bs), BR.tree_ok(r, bs))

def BR.zeros_ok(+bs: Nat) -> {Nat.is_eq(B.Octets.len(B.Octets.zeros(bs)), bs) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.zeros(bs)), bs, BL.octets_len_zeros(bs)) : {Nat.is_eq(_, bs) == True{} : Bool}
  BR.eq_refl(bs)

def BR.leaf_ok(z: Bool, +b: B.Octets, +bs: Nat, +h: {Nat.is_eq(B.Octets.len(b), bs) == True{} : Bool}) -> {Nat.is_eq(B.Octets.len(D.MemDev.read.got(bs, D.MemTree.get.leaf(z, b))), bs) == True{} : Bool}:
  match z:
    case True{}:
      h
    case False{}:
      BR.zeros_ok(bs)

def BR.get_ok(t: D.MemTree, +n: Nat, z: Bool, +bs: Nat, +h: {BR.tree_ok(t, bs) == True{} : Bool}) -> {Nat.is_eq(B.Octets.len(D.MemDev.read.got(bs, D.MemTree.get.at(t, n, z))), bs) == True{} : Bool}:
  match t z:
    case D.MemTEmpty{} _:
      BR.zeros_ok(bs)
    case D.MemTLeaf{+b} _:
      BR.leaf_ok(Nat.is_eq(n, 0n), b, bs, h)
    case D.MemTNode{k, +l, +r} True{}:
      BR.get_ok(l, n, Nat.is_lt(n, D.MemTree.left_count(l)), bs, P.BP.and_l(BR.tree_ok(l, bs), BR.tree_ok(r, bs), h))
    case D.MemTNode{+k, +l, +r} False{}:
      BR.get_ok(r, Nat.sub(n, k), Nat.is_lt(Nat.sub(n, k), D.MemTree.left_count(r)), bs, P.BP.and_r(BR.tree_ok(l, bs), BR.tree_ok(r, bs), h))

def BR.mem_uniform(+k: Nat, +bs: Nat, +c: Nat, +t: D.MemTree, +j: Nat, +ht: {BR.tree_ok(t, bs) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(k, j), c) == True{} : Bool}) -> {D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, k, D.MemDev{bs, c, t}, bs, j) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +hlt = P.IP.lt_of_range(p, j, c, hr)
      %Equal.sym(Bool, Nat.is_lt(j, c), True{}, hlt) : {Bool.and(D.Dev.uniform.ok(D.MemDev.read.check(_, bs, t, j), bs), D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, p, D.MemDev{bs, c, t}, bs, Nat.add(j, 1n))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(D.MemDev.read.got(bs, D.MemTree.get(t, j))), bs), True{}, BR.get_ok(t, j, Nat.is_lt(j, D.MemTree.left_count(t)), bs, ht)) : {Bool.and(_, D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, p, D.MemDev{bs, c, t}, bs, Nat.add(j, 1n))) == True{} : Bool}
      BR.mem_uniform(p, bs, c, t, Nat.add(j, 1n), ht, P.IP.le_rw_l(Nat.add(p, Nat.add(j, 1n)), 1n+Nat.add(p, j), c, P.IP.add_one_r(p, j), hr))

def Laws.valid_blank(bs, count):
  BR.mem_uniform(count, bs, count, D.MemTEmpty{}, 0n, {==}, P.IP.le_rw_l(Nat.add(count, 0n), count, count, UL.nat_add_zero(count), UL.nat_le_refl(count)))

# of_octets: every block it cuts is a whole block, and the tree it builds
# holds only those

def BR.list_ok(xs: List<&2, B.Octets>, +bs: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{b, t}:
      Bool.and(Nat.is_eq(B.Octets.len(b), bs), BR.list_ok(t, bs))

def BR.built_ok(b: D.MemTBuilt, +bs: Nat) -> Bool:
  match b:
    case D.MemTBuilt{t, rest}:
      Bool.and(BR.tree_ok(t, bs), BR.list_ok(rest, bs))

def BR.fin_ok(+hh: Nat, +l: D.MemTree, b2: D.MemTBuilt, +bs: Nat, +el: {BR.tree_ok(l, bs) == True{} : Bool}, +e2: {BR.built_ok(b2, bs) == True{} : Bool}) -> {BR.built_ok(D.MemTree.build.fin(hh, l, b2), bs) == True{} : Bool}:
  match b2:
    case D.MemTBuilt{+r, +rest2}:
      %Equal.sym(Bool, BR.tree_ok(l, bs), True{}, el) : {Bool.and(Bool.and(_, BR.tree_ok(r, bs)), BR.list_ok(rest2, bs)) == True{} : Bool}
      e2

def BR.node_ok(+hh: Nat, b: D.MemTBuilt, +bs: Nat, +eb: {BR.built_ok(b, bs) == True{} : Bool}, +f: Nat, +m: Nat, ih: @ys: List<&2, B.Octets> -> {BR.list_ok(ys, bs) == True{} : Bool} -> {BR.built_ok(D.MemTree.build(f, m, ys), bs) == True{} : Bool}) -> {BR.built_ok(D.MemTree.build.node(hh, b, ys => D.MemTree.build(f, m, ys)), bs) == True{} : Bool}:
  match b:
    case D.MemTBuilt{+l, +rest}:
      BR.fin_ok(hh, l, D.MemTree.build(f, m, rest), bs, P.BP.and_l(BR.tree_ok(l, bs), BR.list_ok(rest, bs), eb), ih(rest, P.BP.and_r(BR.tree_ok(l, bs), BR.list_ok(rest, bs), eb)))

def BR.one_ok(xs: List<&2, B.Octets>, +bs: Nat, +h: {BR.list_ok(xs, bs) == True{} : Bool}) -> {BR.built_ok(D.MemTree.build.one(xs), bs) == True{} : Bool}:
  match xs:
    case Con{b, t}:
      h
    case Nil{}:
      {==}

def BR.build_ok(+f: Nat, +n: Nat, +xs: List<&2, B.Octets>, +bs: Nat, +h: {BR.list_ok(xs, bs) == True{} : Bool}) -> {BR.built_ok(D.MemTree.build(f, n, xs), bs) == True{} : Bool}:
  match f:
    case 0n:
      h
    case 1n+ +f2:
      match n:
        case 0n:
          h
        case 1n+ +p:
          match p:
            case 0n:
              BR.one_ok(xs, bs, h)
            case 1n+ +q:
              +nn : Nat = 1n+1n+q
              +hh = Nat.div(nn, 2n)
              BR.node_ok(hh, D.MemTree.build(f2, hh, xs), bs, BR.build_ok(f2, hh, xs, bs, h), f2, Nat.sub(nn, hh), ys => e => BR.build_ok(f2, Nat.sub(nn, hh), ys, bs, e))

def BR.blk_ok(+bs: Nat, +o: B.Octets) -> {Nat.is_eq(B.Octets.len(B.Octets.append(B.Octets.take(bs, o), B.Octets.zeros(Nat.sub(bs, B.Octets.len(B.Octets.take(bs, o)))))), bs) == True{} : Bool}:
  +tk = B.Octets.take(bs, o)
  +a = B.Octets.len(tk)
  +z = B.Octets.zeros(Nat.sub(bs, a))
  +hle = P.IP.le_rw_l(a, Nat.min(bs, B.Octets.len(o)), bs, BL.octets_len_take(bs, o), BR.min_le(bs, B.Octets.len(o)))
  BR.eq_of(B.Octets.len(B.Octets.append(tk, z)), bs, Equal.trans(Nat, B.Octets.len(B.Octets.append(tk, z)), Nat.add(a, B.Octets.len(z)), bs, BL.octets_len_append(tk, z), Equal.trans(Nat, Nat.add(a, B.Octets.len(z)), Nat.add(a, Nat.sub(bs, a)), bs, Equal.cong(Nat, Nat, x => Nat.add(a, x), B.Octets.len(z), Nat.sub(bs, a), BL.octets_len_zeros(Nat.sub(bs, a))), BR.le_wit(a, bs, hle))))

def BR.split_ok(n: Nat, +bs: Nat, +o: B.Octets, +acc: List<&2, B.Octets>, +h: {BR.list_ok(acc, bs) == True{} : Bool}) -> {BR.list_ok(D.MemDev.split.go(n, bs, o, acc), bs) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+p:
      +tk = B.Octets.take(bs, o)
      +blk = B.Octets.append(tk, B.Octets.zeros(Nat.sub(bs, B.Octets.len(tk))))
      BR.split_ok(p, bs, B.Octets.drop(bs, o), Con{blk, acc}, BR.and_tt(Nat.is_eq(B.Octets.len(blk), bs), BR.list_ok(acc, bs), BR.blk_ok(bs, o), h))

def BR.rev_ok(xs: List<&2, B.Octets>, +acc: List<&2, B.Octets>, +bs: Nat, +hx: {BR.list_ok(xs, bs) == True{} : Bool}, +ha: {BR.list_ok(acc, bs) == True{} : Bool}) -> {BR.list_ok(D.MemDev.blocks.rev_onto(xs, acc), bs) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+b, +t}:
      BR.rev_ok(t, Con{b, acc}, bs, P.BP.and_r(Nat.is_eq(B.Octets.len(b), bs), BR.list_ok(t, bs), hx), BR.and_tt(Nat.is_eq(B.Octets.len(b), bs), BR.list_ok(acc, bs), P.BP.and_l(Nat.is_eq(B.Octets.len(b), bs), BR.list_ok(t, bs), hx), ha))

def BR.fin_tree(b: D.MemTBuilt, +bs: Nat, +e: {BR.built_ok(b, bs) == True{} : Bool}) -> {BR.tree_ok(D.MemTree.of_list.fin(b), bs) == True{} : Bool}:
  match b:
    case D.MemTBuilt{+t, +rest}:
      P.BP.and_l(BR.tree_ok(t, bs), BR.list_ok(rest, bs), e)

def BR.valid_of_octets(+bs: Nat, +o: B.Octets) -> {D.MemDev.valid(D.MemDev.of_octets(bs, o)) == True{} : Bool}:
  +n = Nat.div(Nat.add(B.Octets.len(o), Nat.sub(bs, 1n)), bs)
  +ys = D.MemDev.split.go(n, bs, o, Nil{})
  +xs = D.MemDev.blocks.rev_onto(ys, Nil{})
  +ht = BR.fin_tree(D.MemTree.build(n, n, xs), bs, BR.build_ok(n, n, xs, bs, BR.rev_ok(ys, Nil{}, bs, BR.split_ok(n, bs, o, Nil{}, {==}), {==})))
  BR.mem_uniform(n, bs, n, D.MemTree.of_list(n, xs), 0n, ht, P.IP.le_rw_l(Nat.add(n, 0n), n, n, UL.nat_add_zero(n), UL.nat_le_refl(n)))

def Laws.valid_of_octets(bs, o):
  BR.valid_of_octets(bs, o)

# update keeps a device valid

def BR.ok_upd(z: Bool, +d: D.MemDev, +n: Nat, +data: B.Octets, +j: Nat, +ez: {Nat.is_eq(j, n) == z : Bool}, +len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}, +in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}, +h: {D.Dev.uniform.ok(D.MemDev.read_block(d, j), D.MemDev.block_size(d)) == True{} : Bool}) -> {D.Dev.uniform.ok(D.MemDev.read_block(D.MemDev.update(d, n, data), j), D.MemDev.block_size(d)) == True{} : Bool}:
  match z:
    case True{}:
      %Equal.sym(Nat, j, n, P.IP.eq_nat(j, n, ez)) : {D.Dev.uniform.ok(D.MemDev.read_block(D.MemDev.update(d, n, data), _), D.MemDev.block_size(d)) == True{} : Bool}
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(D.MemDev.update(d, n, data), n), Done{data}, DL.read_after_update(d, n, data, len_ok, in_range)) : {D.Dev.uniform.ok(_, D.MemDev.block_size(d)) == True{} : Bool}
      len_ok
    case False{}:
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(D.MemDev.update(d, n, data), j), D.MemDev.read_block(d, j), DL.update_other(d, n, j, data, ez)) : {D.Dev.uniform.ok(_, D.MemDev.block_size(d)) == True{} : Bool}
      h

def BR.go_upd(+k: Nat, +d: D.MemDev, +n: Nat, +data: B.Octets, +j: Nat, +len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}, +in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}, +h: {D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, k, d, D.MemDev.block_size(d), j) == True{} : Bool}) -> {D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, k, D.MemDev.update(d, n, data), D.MemDev.block_size(d), j) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +bs = D.MemDev.block_size(d)
      +u = D.MemDev.update(d, n, data)
      +ok = D.Dev.uniform.ok(D.MemDev.read_block(d, j), bs)
      +rest = D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, p, d, bs, Nat.add(j, 1n))
      BR.and_tt(D.Dev.uniform.ok(D.MemDev.read_block(u, j), bs), D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, p, u, bs, Nat.add(j, 1n)), BR.ok_upd(Nat.is_eq(j, n), d, n, data, j, {==}, len_ok, in_range, P.BP.and_l(ok, rest, h)), BR.go_upd(p, d, n, data, Nat.add(j, 1n), len_ok, in_range, P.BP.and_r(ok, rest, h)))

def BR.upd_valid(okb: Bool, +bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +data: B.Octets, +eok: {Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)) == okb : Bool}, +hv: {D.MemDev.valid(D.MemDev{bs, c, t}) == True{} : Bool}) -> {D.MemDev.valid(D.MemDev.update(D.MemDev{bs, c, t}, n, data)) == True{} : Bool}:
  match okb:
    case False{}:
      %Equal.sym(Bool, Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)), False{}, eok) : {D.MemDev.valid(D.MemDev.update.check(_, bs, c, t, n, data)) == True{} : Bool}
      hv
    case True{}:
      +d : D.MemDev = D.MemDev{bs, c, t}
      +u = D.MemDev.update(d, n, data)
      +len_ok = P.BP.and_l(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c), eok)
      +in_range = P.BP.and_r(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c), eok)
      %Equal.sym(Nat, D.MemDev.block_count(u), D.MemDev.block_count(d), DL.update_keeps_count(d, n, data)) : {D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, _, u, D.MemDev.block_size(u), 0n) == True{} : Bool}
      %Equal.sym(Nat, D.MemDev.block_size(u), D.MemDev.block_size(d), DL.update_keeps_size(d, n, data)) : {D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, D.MemDev.block_count(d), u, _, 0n) == True{} : Bool}
      BR.go_upd(c, d, n, data, 0n, len_ok, in_range, hv)

def Laws.valid_update(d, n, data, hv):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BR.upd_valid(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)), bs, c, t, n, data, {==}, hv)

# the image's length

def BR.to_len(+d: D.MemDev, +hv: {D.MemDev.valid(d) == True{} : Bool}) -> {B.Octets.len(D.MemDev.to_octets(d)) == Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d)) : Nat}:
  match d:
    case D.MemDev{+bs, +c, +t}:
      %Equal.sym(B.Octets, D.MemDev.to_octets(D.MemDev{bs, c, t}), BR.img(~D.MemDev, ~D.MemDev.read_block, c, D.MemDev{bs, c, t}, 0n), BR.to_img(D.MemDev{bs, c, t})) : {B.Octets.len(_) == Nat.mul(c, bs) : Nat}
      BR.u2(~D.MemDev, ~D.MemDev.read_block, c, D.MemDev{bs, c, t}, bs, 0n, hv)

def Laws.to_octets_len(d, hv):
  BR.to_len(d, hv)

# reads

def BR.blocks_mem(+d: D.MemDev, +count: Nat, +first: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +h: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}) -> {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first) == Done{B.Octets.slice(Nat.mul(first, D.MemDev.block_size(d)), Nat.mul(count, D.MemDev.block_size(d)), D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}:
  match d:
    case D.MemDev{+bs, +c, +t}:
      +dd : D.MemDev = D.MemDev{bs, c, t}
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, dd, count, first), Done{BR.img(~D.MemDev, ~D.MemDev.read_block, count, dd, first)}, BR.u1(~D.MemDev, ~D.MemDev.read_block, count, dd, bs, first, BR.u_sub(~D.MemDev, ~D.MemDev.read_block, dd, bs, c, first, count, hv, h))) : {_ == Done{B.Octets.slice(Nat.mul(first, bs), Nat.mul(count, bs), D.MemDev.to_octets(dd))} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(B.Octets, D.MemDev.to_octets(dd), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n), BR.to_img(dd)) : {Done{BR.img(~D.MemDev, ~D.MemDev.read_block, count, dd, first)} == Done{B.Octets.slice(Nat.mul(first, bs), Nat.mul(count, bs), _)} : Result<&2, &2, D.DevError, B.Octets>}
      Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, x => Done{x}, BR.img(~D.MemDev, ~D.MemDev.read_block, count, dd, first), B.Octets.slice(Nat.mul(first, bs), Nat.mul(count, bs), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n)), Equal.sym(B.Octets, B.Octets.slice(Nat.mul(first, bs), Nat.mul(count, bs), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n)), BR.img(~D.MemDev, ~D.MemDev.read_block, count, dd, first), BR.img_slice(~D.MemDev, ~D.MemDev.read_block, dd, bs, c, first, count, hv, h)))

def Laws.read_blocks_mem(d, count, first, hv, h):
  BR.blocks_mem(d, count, first, hv, h)

def BR.block_mem(+d: D.MemDev, +n: Nat, +hv: {D.MemDev.valid(d) == True{} : Bool}, +in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}) -> {D.MemDev.read_block(d, n) == Done{B.Octets.slice(Nat.mul(n, D.MemDev.block_size(d)), D.MemDev.block_size(d), D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}:
  match d:
    case D.MemDev{+bs, +c, +t}:
      +dd : D.MemDev = D.MemDev{bs, c, t}
      +h1 = P.IP.le_rw_l(Nat.add(n, 1n), 1n+n, c, P.IP.add_one(n), P.IP.lt_le(n, c, in_range))
      +hk = BR.u_sub(~D.MemDev, ~D.MemDev.read_block, dd, bs, c, n, 1n, hv, h1)
      +hok = P.BP.and_l(D.Dev.uniform.ok(D.MemDev.read_block(dd, n), bs), True{}, hk)
      +g = BR.got(D.MemDev.read_block(dd, n))
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(dd, n), Done{g}, BR.u_done(D.MemDev.read_block(dd, n), bs, hok)) : {_ == Done{B.Octets.slice(Nat.mul(n, bs), bs, D.MemDev.to_octets(dd))} : Result<&2, &2, D.DevError, B.Octets>}
      %UL.nat_add_zero(bs) : {Done{g} == Done{B.Octets.slice(Nat.mul(n, bs), _, D.MemDev.to_octets(dd))} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(B.Octets, D.MemDev.to_octets(dd), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n), BR.to_img(dd)) : {Done{g} == Done{B.Octets.slice(Nat.mul(n, bs), Nat.add(bs, 0n), _)} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(B.Octets, B.Octets.slice(Nat.mul(n, bs), Nat.mul(1n, bs), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n)), BR.img(~D.MemDev, ~D.MemDev.read_block, 1n, dd, n), BR.img_slice(~D.MemDev, ~D.MemDev.read_block, dd, bs, c, n, 1n, hv, h1)) : {Done{g} == Done{_} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(B.Octets, B.Octets.append(g, B.Octets.empty()), g, BL.octets_append_empty_r(g)) : {Done{g} == Done{_} : Result<&2, &2, D.DevError, B.Octets>}
      {==}

def Laws.read_block_mem(d, n, hv, in_range):
  BR.block_mem(d, n, hv, in_range)

def BR.map_mem(+bp: Nat, +c: Nat, +t: D.MemTree, +off: Nat, +len: Nat, +hv: {D.MemDev.valid(D.MemDev{1n+bp, c, t}) == True{} : Bool}) -> {Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{1n+bp, c, t}, c, 0n)) == Done{B.Octets.slice(off, len, D.MemDev.to_octets(D.MemDev{1n+bp, c, t}))} : Result<&2, &2, D.DevError, B.Octets>}:
  +dd : D.MemDev = D.MemDev{1n+bp, c, t}
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, dd, c, 0n), Done{BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n)}, BR.u1(~D.MemDev, ~D.MemDev.read_block, c, dd, 1n+bp, 0n, hv)) : {Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), _) == Done{B.Octets.slice(off, len, D.MemDev.to_octets(dd))} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(B.Octets, D.MemDev.to_octets(dd), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n), BR.to_img(dd)) : {Done{B.Octets.slice(off, len, BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n))} == Done{B.Octets.slice(off, len, _)} : Result<&2, &2, D.DevError, B.Octets>}
  {==}

def BR.le_zero_f(+off: Nat, +lp: Nat, +c: Nat) -> {Nat.is_le(Nat.add(off, 1n+lp), Nat.mul(c, 0n)) == False{} : Bool}:
  %Equal.sym(Nat, Nat.mul(c, 0n), 0n, UL.nat_mul_zero(c)) : {Nat.is_le(Nat.add(off, 1n+lp), _) == False{} : Bool}
  %Equal.sym(Nat, Nat.add(off, 1n+lp), 1n+Nat.add(off, lp), UL.nat_add_succ(off, lp)) : {Nat.is_le(_, 0n) == False{} : Bool}
  {==}

def BR.bytes_mem0(+c: Nat, +t: D.MemTree, +off: Nat, len: Nat, +h: {Nat.is_le(Nat.add(off, len), Nat.mul(c, 0n)) == True{} : Bool}) -> {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev{0n, c, t}, off, len) == Done{B.Octets.slice(off, len, D.MemDev.to_octets(D.MemDev{0n, c, t}))} : Result<&2, &2, D.DevError, B.Octets>}:
  match len:
    case 0n:
      +x = B.Octets.drop(off, D.MemDev.to_octets(D.MemDev{0n, c, t}))
      %Equal.sym(B.Octets, B.Octets.take(0n, x), B.Octets.empty(), BR.take0(x)) : {Done{B.Octets.empty()} == Done{_} : Result<&2, &2, D.DevError, B.Octets>}
      {==}
    case 1n+ +lp:
      Empty.absurd({D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev{0n, c, t}, off, 1n+lp) == Done{B.Octets.slice(off, 1n+lp, D.MemDev.to_octets(D.MemDev{0n, c, t}))} : Result<&2, &2, D.DevError, B.Octets>}, BR.bool_clash(Equal.trans(Bool, False{}, Nat.is_le(Nat.add(off, 1n+lp), Nat.mul(c, 0n)), True{}, Equal.sym(Bool, Nat.is_le(Nat.add(off, 1n+lp), Nat.mul(c, 0n)), False{}, BR.le_zero_f(off, lp, c)), h)))

def BR.bytes_mem2(bs: Nat, +c: Nat, +t: D.MemTree, +off: Nat, +len: Nat, +hv: {D.MemDev.valid(D.MemDev{bs, c, t}) == True{} : Bool}, +h: {Nat.is_le(Nat.add(off, len), Nat.mul(c, bs)) == True{} : Bool}) -> {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev{bs, c, t}, off, len) == Done{B.Octets.slice(off, len, D.MemDev.to_octets(D.MemDev{bs, c, t}))} : Result<&2, &2, D.DevError, B.Octets>}:
  match bs:
    case 0n:
      BR.bytes_mem0(c, t, off, len, h)
    case 1n+ +bp:
      +dd : D.MemDev = D.MemDev{1n+bp, c, t}
      Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dd, off, len), Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, dd, c, 0n)), Done{B.Octets.slice(off, len, D.MemDev.to_octets(dd))}, BR.image(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dd, bp, c, off, len, {==}, hv, h), BR.map_mem(bp, c, t, off, len, hv))

def Laws.read_bytes_mem(d, off, len, hv, h):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BR.bytes_mem2(bs, c, t, off, len, hv, h)

# past the end

def BR.rb_fail(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +p: Nat, +j: Nat, +e: D.DevError, +hf: {read_block(d, j) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}) -> {D.Dev.read_blocks(~T, ~read_block, d, 1n+p, j) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}:
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, read_block(d, j), Fail{e}, hf) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(j, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}
  {==}

def BR.rb_ok(~T: Data, ~read_block: T -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: T, +p: Nat, +j: Nat, +b: B.Octets, +e: D.DevError, +hd: {read_block(d, j) == Done{b} : Result<&2, &2, D.DevError, B.Octets>}, +hr: {D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(j, 1n)) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}) -> {D.Dev.read_blocks(~T, ~read_block, d, 1n+p, j) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}:
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, read_block(d, j), Done{b}, hd) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(j, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~T, ~read_block, d, p, Nat.add(j, 1n)), Fail{e}, hr) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(b, rest))) == Fail{e} : Result<&2, &2, D.DevError, B.Octets>}
  {==}

def BR.fb_last(z: Bool, +bs: Nat, +c: Nat, +t: D.MemTree, +j: Nat, +ez: {Nat.is_lt(j, c) == z : Bool}, +h: {Nat.is_le(c, Nat.add(j, 0n)) == True{} : Bool}) -> {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n, j) == Fail{D.DevOutOfRange{Nat.max(j, c)}} : Result<&2, &2, D.DevError, B.Octets>}:
  match z:
    case False{}:
      Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n, j), Fail{D.DevOutOfRange{j}}, Fail{D.DevOutOfRange{Nat.max(j, c)}}, BR.rb_fail(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 0n, j, D.DevOutOfRange{j}, BR.read_out(bs, c, t, j, ez)), Equal.cong(Nat, Result<&2, &2, D.DevError, B.Octets>, x => Fail{D.DevOutOfRange{x}}, j, Nat.max(j, c), Equal.sym(Nat, Nat.max(j, c), j, BR.max_l(j, c, ez))))
    case True{}:
      Empty.absurd({D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n, j) == Fail{D.DevOutOfRange{Nat.max(j, c)}} : Result<&2, &2, D.DevError, B.Octets>}, BR.lt_le_no(j, c, ez, P.IP.le_rw_r(c, j, Nat.add(j, 0n), Equal.sym(Nat, Nat.add(j, 0n), j, UL.nat_add_zero(j)), h)))

def BR.fb_step(z: Bool, +bs: Nat, +c: Nat, +t: D.MemTree, +j: Nat, +q: Nat, +ez: {Nat.is_lt(j, c) == z : Bool}, +ih: {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+q, Nat.add(j, 1n)) == Fail{D.DevOutOfRange{Nat.max(Nat.add(j, 1n), c)}} : Result<&2, &2, D.DevError, B.Octets>}) -> {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+1n+q, j) == Fail{D.DevOutOfRange{Nat.max(j, c)}} : Result<&2, &2, D.DevError, B.Octets>}:
  match z:
    case False{}:
      Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+1n+q, j), Fail{D.DevOutOfRange{j}}, Fail{D.DevOutOfRange{Nat.max(j, c)}}, BR.rb_fail(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+q, j, D.DevOutOfRange{j}, BR.read_out(bs, c, t, j, ez)), Equal.cong(Nat, Result<&2, &2, D.DevError, B.Octets>, x => Fail{D.DevOutOfRange{x}}, j, Nat.max(j, c), Equal.sym(Nat, Nat.max(j, c), j, BR.max_l(j, c, ez))))
    case True{}:
      +e1 = Equal.trans(Nat, Nat.max(Nat.add(j, 1n), c), c, Nat.max(j, c), BR.max_r(Nat.add(j, 1n), c, P.IP.le_rw_l(Nat.add(j, 1n), 1n+j, c, P.IP.add_one(j), P.IP.lt_le(j, c, ez))), Equal.sym(Nat, Nat.max(j, c), c, BR.max_r(j, c, BR.lt_to_le(j, c, ez))))
      BR.rb_ok(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+q, j, D.MemDev.read.got(bs, D.MemTree.get(t, j)), D.DevOutOfRange{Nat.max(j, c)}, BR.read_in(bs, c, t, j, ez), Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+q, Nat.add(j, 1n)), Fail{D.DevOutOfRange{Nat.max(Nat.add(j, 1n), c)}}, Fail{D.DevOutOfRange{Nat.max(j, c)}}, ih, Equal.cong(Nat, Result<&2, &2, D.DevError, B.Octets>, x => Fail{D.DevOutOfRange{x}}, Nat.max(Nat.add(j, 1n), c), Nat.max(j, c), e1)))

# 1 + p blocks from j, when the last of them, j + p, is past the end
def BR.fail_blocks(+p: Nat, +bs: Nat, +c: Nat, +t: D.MemTree, +j: Nat, +h: {Nat.is_le(c, Nat.add(j, p)) == True{} : Bool}) -> {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+p, j) == Fail{D.DevOutOfRange{Nat.max(j, c)}} : Result<&2, &2, D.DevError, B.Octets>}:
  match p:
    case 0n:
      BR.fb_last(Nat.is_lt(j, c), bs, c, t, j, {==}, h)
    case 1n+ +q:
      BR.fb_step(Nat.is_lt(j, c), bs, c, t, j, q, {==}, BR.fail_blocks(q, bs, c, t, Nat.add(j, 1n), P.IP.le_rw_r(c, Nat.add(Nat.add(j, 1n), q), Nat.add(j, 1n+q), UL.nat_add_assoc(j, 1n, q), h)))

def BR.past_go(cc: Nat, +cx: Nat, +f: Nat, +s: Nat, +l: Nat, +bs: Nat, +c: Nat, +t: D.MemTree, +bp: Nat, +lp: Nat, +ec: {cx == cc : Nat}, +hgt: {Nat.is_lt(c, Nat.add(f, cx)) == True{} : Bool}, +hcov: {Nat.mul(cx, 1n+bp) == Nat.add(Nat.add(s, 1n+lp), l) : Nat}) -> {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, cx, f), blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(s, 1n+lp, blocks))) == Fail{D.DevOutOfRange{Nat.max(f, c)}} : Result<&2, &2, D.DevError, B.Octets>}:
  match cc:
    case 0n:
      +e0 = Equal.trans(Nat, 0n, Nat.add(Nat.add(s, 1n+lp), l), 1n+Nat.add(Nat.add(s, lp), l), Equal.trans(Nat, 0n, Nat.mul(cx, 1n+bp), Nat.add(Nat.add(s, 1n+lp), l), Equal.cong(Nat, Nat, x => Nat.mul(x, 1n+bp), 0n, cx, Equal.sym(Nat, cx, 0n, ec)), hcov), Equal.cong(Nat, Nat, x => Nat.add(x, l), Nat.add(s, 1n+lp), 1n+Nat.add(s, lp), UL.nat_add_succ(s, lp)))
      Empty.absurd({Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, cx, f), blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(s, 1n+lp, blocks))) == Fail{D.DevOutOfRange{Nat.max(f, c)}} : Result<&2, &2, D.DevError, B.Octets>}, P.IP.sz(Nat.add(Nat.add(s, lp), l), Equal.sym(Nat, 0n, 1n+Nat.add(Nat.add(s, lp), l), e0)))
    case 1n+ +cp:
      +h1 = BR.lt_rw_r(c, Nat.add(f, 1n+cp), Nat.add(f, cx), Equal.cong(Nat, Nat, x => Nat.add(f, x), 1n+cp, cx, Equal.sym(Nat, cx, 1n+cp, ec)), hgt)
      +h2 = BR.lt_rw_r(c, 1n+Nat.add(f, cp), Nat.add(f, 1n+cp), Equal.sym(Nat, Nat.add(f, 1n+cp), 1n+Nat.add(f, cp), UL.nat_add_succ(f, cp)), h1)
      %Equal.sym(Nat, cx, 1n+cp, ec) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, _, f), blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(s, 1n+lp, blocks))) == Fail{D.DevOutOfRange{Nat.max(f, c)}} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+cp, f), Fail{D.DevOutOfRange{Nat.max(f, c)}}, BR.fail_blocks(cp, bs, c, t, f, BR.lt_succ_le(c, Nat.add(f, cp), h2))) : {Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, _, blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(s, 1n+lp, blocks))) == Fail{D.DevOutOfRange{Nat.max(f, c)}} : Result<&2, &2, D.DevError, B.Octets>}
      {==}

def BR.past(+bs: Nat, +c: Nat, +t: D.MemTree, +bp: Nat, +off: Nat, +lp: Nat, +h: {Nat.is_lt(Nat.mul(c, 1n+bp), Nat.add(off, 1n+lp)) == True{} : Bool}) -> {D.Dev.read_bytes.go(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, 1n+bp, off, 1n+lp) == Fail{D.DevOutOfRange{Nat.max(Nat.div(off, 1n+bp), c)}} : Result<&2, &2, D.DevError, B.Octets>}:
  +bsz : Nat = 1n+bp
  +len : Nat = 1n+lp
  +s = Nat.mod(off, bsz)
  +f = Nat.div(off, bsz)
  +tt = Nat.add(Nat.add(s, len), Nat.sub(bsz, 1n))
  +cx = Nat.div(tt, bsz)
  +l = Nat.sub(Nat.sub(bsz, 1n), Nat.mod(tt, bsz))
  +hgt = BR.mul_lt_cancel(c, Nat.add(f, cx), bp, BR.lt_rw_r(Nat.mul(c, bsz), Nat.mul(Nat.add(f, cx), bsz), Nat.add(Nat.add(off, len), l), BR.span_eq(bp, off, len), UO.nat_lt_le_trans(Nat.mul(c, bsz), Nat.add(off, len), Nat.add(Nat.add(off, len), l), h, UO.nat_le_add_r(Nat.add(off, len), l))))
  BR.past_go(cx, cx, f, s, l, bs, c, t, bp, lp, {==}, hgt, UD.nat_round_up(bp, Nat.add(s, len)))

def BR.past_end(+d: D.MemDev, +bp: Nat, +off: Nat, +lp: Nat, +hbs: {D.MemDev.block_size(d) == 1n+bp : Nat}, +h: {Nat.is_lt(Nat.mul(D.MemDev.block_count(d), 1n+bp), Nat.add(off, 1n+lp)) == True{} : Bool}) -> {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, off, 1n+lp) == Fail{D.DevOutOfRange{Nat.max(Nat.div(off, 1n+bp), D.MemDev.block_count(d))}} : Result<&2, &2, D.DevError, B.Octets>}:
  match d:
    case D.MemDev{+bs, +c, +t}:
      %Equal.sym(Nat, bs, 1n+bp, hbs) : {D.Dev.read_bytes.go(~D.MemDev, ~D.MemDev.read_block, D.MemDev{bs, c, t}, _, off, 1n+lp) == Fail{D.DevOutOfRange{Nat.max(Nat.div(off, 1n+bp), c)}} : Result<&2, &2, D.DevError, B.Octets>}
      BR.past(bs, c, t, bp, off, lp, h)

def Laws.read_bytes_past_end(d, bp, off, lp, hbs, h):
  BR.past_end(d, bp, off, lp, hbs, h)

# a block update patches the image

def BR.agree_lo(+k: Nat, +d: D.MemDev, +n: Nat, +data: B.Octets, +j: Nat, +h: {Nat.is_le(Nat.add(k, j), n) == True{} : Bool}) -> {BR.img(~D.MemDev, ~D.MemDev.read_block, k, D.MemDev.update(d, n, data), j) == BR.img(~D.MemDev, ~D.MemDev.read_block, k, d, j) : B.Octets}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +u = D.MemDev.update(d, n, data)
      +hlt = P.IP.lt_of_range(p, j, n, h)
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(u, j), D.MemDev.read_block(d, j), DL.update_other(d, n, j, data, P.IP.ne_gt(j, n, hlt))) : {B.Octets.append(BR.got(_), BR.img(~D.MemDev, ~D.MemDev.read_block, p, u, Nat.add(j, 1n))) == B.Octets.append(BR.got(D.MemDev.read_block(d, j)), BR.img(~D.MemDev, ~D.MemDev.read_block, p, d, Nat.add(j, 1n))) : B.Octets}
      %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, p, u, Nat.add(j, 1n)), BR.img(~D.MemDev, ~D.MemDev.read_block, p, d, Nat.add(j, 1n)), BR.agree_lo(p, d, n, data, Nat.add(j, 1n), P.IP.le_rw_l(Nat.add(p, Nat.add(j, 1n)), 1n+Nat.add(p, j), n, P.IP.add_one_r(p, j), h))) : {B.Octets.append(BR.got(D.MemDev.read_block(d, j)), _) == B.Octets.append(BR.got(D.MemDev.read_block(d, j)), BR.img(~D.MemDev, ~D.MemDev.read_block, p, d, Nat.add(j, 1n))) : B.Octets}
      {==}

def BR.agree_hi(+k: Nat, +d: D.MemDev, +n: Nat, +data: B.Octets, +j: Nat, +h: {Nat.is_lt(n, j) == True{} : Bool}) -> {BR.img(~D.MemDev, ~D.MemDev.read_block, k, D.MemDev.update(d, n, data), j) == BR.img(~D.MemDev, ~D.MemDev.read_block, k, d, j) : B.Octets}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +u = D.MemDev.update(d, n, data)
      %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(u, j), D.MemDev.read_block(d, j), DL.update_other(d, n, j, data, P.IP.ne_lt(j, n, h))) : {B.Octets.append(BR.got(_), BR.img(~D.MemDev, ~D.MemDev.read_block, p, u, Nat.add(j, 1n))) == B.Octets.append(BR.got(D.MemDev.read_block(d, j)), BR.img(~D.MemDev, ~D.MemDev.read_block, p, d, Nat.add(j, 1n))) : B.Octets}
      %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, p, u, Nat.add(j, 1n)), BR.img(~D.MemDev, ~D.MemDev.read_block, p, d, Nat.add(j, 1n)), BR.agree_hi(p, d, n, data, Nat.add(j, 1n), P.IP.lt_s1(n, j, h))) : {B.Octets.append(BR.got(D.MemDev.read_block(d, j)), _) == B.Octets.append(BR.got(D.MemDev.read_block(d, j)), BR.img(~D.MemDev, ~D.MemDev.read_block, p, d, Nat.add(j, 1n))) : B.Octets}
      {==}

def BR.patch_mid(+x: B.Octets, +y: B.Octets, +z: B.Octets, +b: B.Octets, +eb: {B.Octets.len(b) == B.Octets.len(y) : Nat}) -> {D.Dev.patch(B.Octets.len(x), b, B.Octets.append(x, B.Octets.append(y, z))) == B.Octets.append(x, B.Octets.append(b, z)) : B.Octets}:
  +w = B.Octets.append(x, B.Octets.append(y, z))
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(x), w), x, BL.octets_take_append(x, B.Octets.append(y, z))) : {B.Octets.append(_, B.Octets.append(b, B.Octets.drop(Nat.add(B.Octets.len(x), B.Octets.len(b)), w))) == B.Octets.append(x, B.Octets.append(b, z)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(x), B.Octets.len(b)), w), B.Octets.drop(B.Octets.len(b), B.Octets.append(y, z)), BL.octets_drop_append_add(x, B.Octets.len(b), B.Octets.append(y, z))) : {B.Octets.append(x, B.Octets.append(b, _)) == B.Octets.append(x, B.Octets.append(b, z)) : B.Octets}
  %Equal.sym(Nat, B.Octets.len(b), B.Octets.len(y), eb) : {B.Octets.append(x, B.Octets.append(b, B.Octets.drop(_, B.Octets.append(y, z)))) == B.Octets.append(x, B.Octets.append(b, z)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(y), B.Octets.append(y, z)), z, BL.octets_drop_append(y, z)) : {B.Octets.append(x, B.Octets.append(b, _)) == B.Octets.append(x, B.Octets.append(b, z)) : B.Octets}
  {==}

def BR.upd_img_u(+bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +data: B.Octets, +r: Nat, +ec: {Nat.add(n, 1n+r) == c : Nat}, +len_ok: {Nat.is_eq(B.Octets.len(data), bs) == True{} : Bool}, +in_range: {Nat.is_lt(n, c) == True{} : Bool}) -> {D.MemDev.to_octets(D.MemDev.update(D.MemDev{bs, c, t}, n, data)) == B.Octets.append(BR.img(~D.MemDev, ~D.MemDev.read_block, n, D.MemDev{bs, c, t}, 0n), B.Octets.append(data, BR.img(~D.MemDev, ~D.MemDev.read_block, r, D.MemDev{bs, c, t}, Nat.add(n, 1n)))) : B.Octets}:
  +dd : D.MemDev = D.MemDev{bs, c, t}
  +u = D.MemDev.update(dd, n, data)
  +rhs = B.Octets.append(BR.img(~D.MemDev, ~D.MemDev.read_block, n, dd, 0n), B.Octets.append(data, BR.img(~D.MemDev, ~D.MemDev.read_block, r, dd, Nat.add(n, 1n))))
  %Equal.sym(B.Octets, D.MemDev.to_octets(u), BR.img(~D.MemDev, ~D.MemDev.read_block, D.MemDev.block_count(u), u, 0n), BR.to_img(u)) : {_ == rhs : B.Octets}
  %Equal.sym(Nat, D.MemDev.block_count(u), D.MemDev.block_count(dd), DL.update_keeps_count(dd, n, data)) : {BR.img(~D.MemDev, ~D.MemDev.read_block, _, u, 0n) == rhs : B.Octets}
  %Equal.cong(Nat, B.Octets, k => BR.img(~D.MemDev, ~D.MemDev.read_block, k, u, 0n), Nat.add(n, 1n+r), c, ec) : {_ == rhs : B.Octets}
  %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, Nat.add(n, 1n+r), u, 0n), B.Octets.append(BR.img(~D.MemDev, ~D.MemDev.read_block, n, u, 0n), BR.img(~D.MemDev, ~D.MemDev.read_block, 1n+r, u, n)), BR.u3(~D.MemDev, ~D.MemDev.read_block, n, 1n+r, u, 0n)) : {_ == rhs : B.Octets}
  %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, n, u, 0n), BR.img(~D.MemDev, ~D.MemDev.read_block, n, dd, 0n), BR.agree_lo(n, dd, n, data, 0n, P.IP.le_rw_l(Nat.add(n, 0n), n, n, UL.nat_add_zero(n), UL.nat_le_refl(n)))) : {B.Octets.append(_, BR.img(~D.MemDev, ~D.MemDev.read_block, 1n+r, u, n)) == rhs : B.Octets}
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(u, n), Done{data}, DL.read_after_update(dd, n, data, len_ok, in_range)) : {B.Octets.append(BR.img(~D.MemDev, ~D.MemDev.read_block, n, dd, 0n), B.Octets.append(BR.got(_), BR.img(~D.MemDev, ~D.MemDev.read_block, r, u, Nat.add(n, 1n)))) == rhs : B.Octets}
  %Equal.sym(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, r, u, Nat.add(n, 1n)), BR.img(~D.MemDev, ~D.MemDev.read_block, r, dd, Nat.add(n, 1n)), BR.agree_hi(r, dd, n, data, Nat.add(n, 1n), P.IP.lt_s_s1(n))) : {B.Octets.append(BR.img(~D.MemDev, ~D.MemDev.read_block, n, dd, 0n), B.Octets.append(data, _)) == rhs : B.Octets}
  {==}

def BR.upd_img(+bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +data: B.Octets, +hv: {D.MemDev.valid(D.MemDev{bs, c, t}) == True{} : Bool}, +len_ok: {Nat.is_eq(B.Octets.len(data), bs) == True{} : Bool}, +in_range: {Nat.is_lt(n, c) == True{} : Bool}) -> {D.MemDev.to_octets(D.MemDev.update(D.MemDev{bs, c, t}, n, data)) == D.Dev.patch(Nat.mul(n, bs), data, D.MemDev.to_octets(D.MemDev{bs, c, t})) : B.Octets}:
  +dd : D.MemDev = D.MemDev{bs, c, t}
  +u = D.MemDev.update(dd, n, data)
  +r = Nat.sub(c, 1n+n)
  +ec = Equal.trans(Nat, Nat.add(n, 1n+r), 1n+Nat.add(n, r), c, UL.nat_add_succ(n, r), BR.le_wit(1n+n, c, P.IP.lt_le(n, c, in_range)))
  +hn = BR.u_rw(~D.MemDev, ~D.MemDev.read_block, c, Nat.add(n, 1n+r), dd, bs, 0n, Equal.sym(Nat, Nat.add(n, 1n+r), c, ec), hv)
  +hlo = BR.u4a(~D.MemDev, ~D.MemDev.read_block, n, 1n+r, dd, bs, 0n, hn)
  +hmid = BR.u4b(~D.MemDev, ~D.MemDev.read_block, n, 1n+r, dd, bs, 0n, hn)
  +hok = P.BP.and_l(D.Dev.uniform.ok(D.MemDev.read_block(dd, n), bs), D.Dev.uniform.go(~D.MemDev, ~D.MemDev.read_block, r, dd, bs, Nat.add(n, 1n)), hmid)
  +x = BR.img(~D.MemDev, ~D.MemDev.read_block, n, dd, 0n)
  +y = BR.got(D.MemDev.read_block(dd, n))
  +z = BR.img(~D.MemDev, ~D.MemDev.read_block, r, dd, Nat.add(n, 1n))
  +eimg = Equal.trans(B.Octets, D.MemDev.to_octets(dd), BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n), B.Octets.append(x, B.Octets.append(y, z)), BR.to_img(dd), Equal.trans(B.Octets, BR.img(~D.MemDev, ~D.MemDev.read_block, c, dd, 0n), BR.img(~D.MemDev, ~D.MemDev.read_block, Nat.add(n, 1n+r), dd, 0n), B.Octets.append(x, B.Octets.append(y, z)), Equal.cong(Nat, B.Octets, k => BR.img(~D.MemDev, ~D.MemDev.read_block, k, dd, 0n), c, Nat.add(n, 1n+r), Equal.sym(Nat, Nat.add(n, 1n+r), c, ec)), BR.u3(~D.MemDev, ~D.MemDev.read_block, n, 1n+r, dd, 0n)))
  +eu = BR.upd_img_u(bs, c, t, n, data, r, ec, len_ok, in_range)
  +eb = Equal.trans(Nat, B.Octets.len(data), bs, B.Octets.len(y), P.IP.eq_nat(B.Octets.len(data), bs, len_ok), Equal.sym(Nat, B.Octets.len(y), bs, BR.u_len(D.MemDev.read_block(dd, n), bs, hok)))
  %Equal.sym(B.Octets, D.MemDev.to_octets(u), B.Octets.append(x, B.Octets.append(data, z)), eu) : {_ == D.Dev.patch(Nat.mul(n, bs), data, D.MemDev.to_octets(dd)) : B.Octets}
  %Equal.sym(B.Octets, D.MemDev.to_octets(dd), B.Octets.append(x, B.Octets.append(y, z)), eimg) : {B.Octets.append(x, B.Octets.append(data, z)) == D.Dev.patch(Nat.mul(n, bs), data, _) : B.Octets}
  %BR.u2(~D.MemDev, ~D.MemDev.read_block, n, dd, bs, 0n, hlo) : {B.Octets.append(x, B.Octets.append(data, z)) == D.Dev.patch(_, data, B.Octets.append(x, B.Octets.append(y, z))) : B.Octets}
  Equal.sym(B.Octets, D.Dev.patch(B.Octets.len(x), data, B.Octets.append(x, B.Octets.append(y, z))), B.Octets.append(x, B.Octets.append(data, z)), BR.patch_mid(x, y, z, data, eb))

def Laws.to_octets_update(d, n, data, hv, len_ok, in_range):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BR.upd_img(bs, c, t, n, data, hv, len_ok, in_range)

# Vectors, by computation

def Laws.vector_valid():
  {==}

def Laws.vector_patch():
  {==}

def Laws.vector_past_end_block():
  {==}
