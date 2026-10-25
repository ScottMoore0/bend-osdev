# Proofs of LAWS_hkdf.bend, from bytes' laws.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./crypto.bend as Cr
import ./hmac.bend as Hm
import ./hkdf.bend as Hk
import ./LAWS_hkdf.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# How the proofs go. HKDF's loop is its blocks T(1), T(2), ... reversed onto
# an accumulator (hk.blocks_ts), so the output is the first len bytes of the
# first N blocks joined (hk.out), N = (len + dsize - 1) / dsize by Base's
# Nat.divmod. Each block is the digest of an outer HMAC input (hk.ins,
# hk.dl), so hd at those inputs gives every block dsize bytes (hk.tlen), and
# N blocks of dsize bytes are N dsize bytes (hk.cat_len), at least len
# (hk.ceil: quotient times divisor plus remainder is the dividend, kmath's
# division specification, with the remainder below the divisor). So the
# first len bytes are len bytes. For the prefix: more bytes need no fewer
# blocks (hk.nmono, the quotient never falling as the dividend grows), the
# blocks for n + j bytes are those for n and then more (hk.ts_split), and
# the first n of them already cover n bytes.


# Booleans, naturals, lists: discriminations

def hk.bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def hk.bd(h: {False{} == True{} : Bool}) -> Empty:
  %h : hk.bdisc(_)
  Unit{}

def hk.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, hk.bd(h))

def hk.ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def hk.nd(+p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : hk.ndisc(_)
  Unit{}

def hk.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# Arithmetic

def hk.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def hk.add_cancel_r(+x: Nat, +y: Nat, +r: Nat) -> {Nat.add(x, r) == Nat.add(y, r) : Nat} -> {x == y : Nat}:
  match r:
    case 0n:
      h => Equal.trans(Nat, x, Nat.add(x, 0n), y, Equal.sym(Nat, Nat.add(x, 0n), x, UL.nat_add_zero(x)), Equal.trans(Nat, Nat.add(x, 0n), Nat.add(y, 0n), y, h, UL.nat_add_zero(y)))
    case 1n+rp:
      h => hk.add_cancel_r(x, y, rp)(Equal.cong(Nat, Nat, z => hk.pred(z), 1n+Nat.add(x, rp), 1n+Nat.add(y, rp), Equal.trans(Nat, 1n+Nat.add(x, rp), Nat.add(x, 1n+rp), 1n+Nat.add(y, rp), Equal.sym(Nat, Nat.add(x, 1n+rp), 1n+Nat.add(x, rp), UL.nat_add_succ(x, rp)), Equal.trans(Nat, Nat.add(x, 1n+rp), Nat.add(y, 1n+rp), 1n+Nat.add(y, rp), h, UL.nat_add_succ(y, rp)))))

def hk.le_step(+x: Nat, +y: Nat) -> {Nat.is_le(x, y) == True{} : Bool} -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      h => {==}
    case 1n+xp 0n:
      h => hk.absurd({Nat.is_le(1n+xp, 1n) == True{} : Bool}, h)
    case 1n+xp 1n+yp:
      h => hk.le_step(xp, yp)(h)

def hk.le_trans(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(b, c) == True{} : Bool} -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      h1 => h2 => {==}
    case 0n _ 1n+cp:
      h1 => h2 => {==}
    case 1n+ap 0n _:
      h1 => h2 => hk.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, h1)
    case 1n+ap 1n+bp 0n:
      h1 => h2 => hk.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, h2)
    case 1n+ap 1n+bp 1n+cp:
      h1 => h2 => hk.le_trans(ap, bp, cp)(h1)(h2)

def hk.add_sub(+d: Nat, +n: Nat) -> {Nat.is_le(d, n) == True{} : Bool} -> {Nat.add(d, Nat.sub(n, d)) == n : Nat}:
  match d n:
    case 0n 0n:
      h => {==}
    case 0n 1n+np:
      h => {==}
    case 1n+dp 0n:
      h => hk.absurd({Nat.add(1n+dp, Nat.sub(0n, 1n+dp)) == 0n : Nat}, h)
    case 1n+dp 1n+np:
      h => %hk.add_sub(dp, np)(h) : {1n+Nat.add(dp, Nat.sub(np, dp)) == 1n+_ : Nat}
        {==}

def hk.min_add(+n: Nat, +j: Nat) -> {Nat.min(n, Nat.add(n, j)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %hk.min_add(p, j) : {1n+Nat.min(p, Nat.add(p, j)) == 1n+_ : Nat}
      {==}

# x + r = (l + s) + r gives l <= x
def hk.cancel.go(+x: Nat, +r: Nat, +l: Nat, +s: Nat, e: {Nat.add(x, r) == Nat.add(Nat.add(l, s), r) : Nat}) -> {Nat.is_le(l, x) == True{} : Bool}:
  %Equal.sym(Nat, x, Nat.add(l, s), hk.add_cancel_r(x, Nat.add(l, s), r)(e)) : {Nat.is_le(l, _) == True{} : Bool}
  UO.nat_le_add_r(l, s)

# x + r = l + q with r <= q gives l <= x
def hk.cancel(+x: Nat, +r: Nat, +l: Nat, +q: Nat) -> {Nat.add(x, r) == Nat.add(l, q) : Nat} -> {Nat.is_le(r, q) == True{} : Bool} -> {Nat.is_le(l, x) == True{} : Bool}:
  h1 => h2 => hk.cancel.go(x, r, l, Nat.sub(q, r), Equal.trans(Nat, Nat.add(x, r), Nat.add(l, q), Nat.add(Nat.add(l, Nat.sub(q, r)), r), h1, Equal.trans(Nat, Nat.add(l, q), Nat.add(l, Nat.add(r, Nat.sub(q, r))), Nat.add(Nat.add(l, Nat.sub(q, r)), r), Equal.cong(Nat, Nat, z => Nat.add(l, z), q, Nat.add(r, Nat.sub(q, r)), Equal.sym(Nat, Nat.add(r, Nat.sub(q, r)), q, hk.add_sub(r, q)(h2))), Equal.trans(Nat, Nat.add(l, Nat.add(r, Nat.sub(q, r))), Nat.add(l, Nat.add(Nat.sub(q, r), r)), Nat.add(Nat.add(l, Nat.sub(q, r)), r), Equal.cong(Nat, Nat, z => Nat.add(l, z), Nat.add(r, Nat.sub(q, r)), Nat.add(Nat.sub(q, r), r), UL.nat_add_comm(r, Nat.sub(q, r))), Equal.sym(Nat, Nat.add(Nat.add(l, Nat.sub(q, r)), r), Nat.add(l, Nat.add(Nat.sub(q, r), r)), UL.nat_add_assoc(l, Nat.sub(q, r), r))))))

# Base's division: m the steps left before the remainder wraps, d the
# quotient, r the remainder so far (m + r = q, for a divisor 1 + q)

def hk.mod_le(+a: Nat, +m: Nat, +d: Nat, +r: Nat, +q: Nat) -> {Nat.add(m, r) == q : Nat} -> {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r)), q) == True{} : Bool}:
  match a:
    case 0n:
      inv => %inv : {Nat.is_le(r, _) == True{} : Bool}
        UL.nat_le_add(r, m)
    case 1n+ap:
      match m:
        case 0n:
          inv => hk.mod_le(ap, r, 1n+d, 0n, q)(Equal.trans(Nat, Nat.add(r, 0n), r, q, UL.nat_add_zero(r), inv))
        case 1n+mp:
          inv => hk.mod_le(ap, mp, d, 1n+r, q)(Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), q, UL.nat_add_succ(mp, r), inv))

# quotient (1 + q) + remainder = dividend (kmath's division specification)
def hk.ds(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +q: Nat) -> {Nat.add(m, r) == q : Nat} -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+q), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(n, Nat.add(Nat.mul(d, 1n+q), r)) : Nat}:
  match n:
    case 0n:
      inv => {==}
    case 1n+np:
      match m:
        case 0n:
          +inv => Equal.trans(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+q), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))), Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+q), 0n)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), r)), hk.ds(np, r, 1n+d, 0n, q)(Equal.trans(Nat, Nat.add(r, 0n), r, q, UL.nat_add_zero(r), inv)), Equal.trans(Nat, Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+q), 0n)), Nat.add(np, Nat.mul(1n+d, 1n+q)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), r)), Equal.cong(Nat, Nat, z => Nat.add(np, z), Nat.add(Nat.mul(1n+d, 1n+q), 0n), Nat.mul(1n+d, 1n+q), UL.nat_add_zero(Nat.mul(1n+d, 1n+q))), Equal.trans(Nat, Nat.add(np, 1n+Nat.add(q, Nat.mul(d, 1n+q))), 1n+Nat.add(np, Nat.add(q, Nat.mul(d, 1n+q))), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), r)), UL.nat_add_succ(np, Nat.add(q, Nat.mul(d, 1n+q))), Equal.trans(Nat, 1n+Nat.add(np, Nat.add(q, Nat.mul(d, 1n+q))), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), q)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), r)), Equal.cong(Nat, Nat, z => 1n+Nat.add(np, z), Nat.add(q, Nat.mul(d, 1n+q)), Nat.add(Nat.mul(d, 1n+q), q), UL.nat_add_comm(q, Nat.mul(d, 1n+q))), Equal.cong(Nat, Nat, z => 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), z)), q, r, Equal.sym(Nat, r, q, inv))))))
        case 1n+mp:
          inv => Equal.trans(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+q), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))), Nat.add(np, Nat.add(Nat.mul(d, 1n+q), 1n+r)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), r)), hk.ds(np, mp, d, 1n+r, q)(Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), q, UL.nat_add_succ(mp, r), inv)), Equal.trans(Nat, Nat.add(np, Nat.add(Nat.mul(d, 1n+q), 1n+r)), Nat.add(np, 1n+Nat.add(Nat.mul(d, 1n+q), r)), 1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+q), r)), Equal.cong(Nat, Nat, z => Nat.add(np, z), Nat.add(Nat.mul(d, 1n+q), 1n+r), 1n+Nat.add(Nat.mul(d, 1n+q), r), UL.nat_add_succ(Nat.mul(d, 1n+q), r)), UL.nat_add_succ(np, Nat.add(Nat.mul(d, 1n+q), r))))

# the number of blocks covers the length: len <= ceil(len / (1 + q)) (1 + q)
def hk.ceil(+len: Nat, +q: Nat) -> {Nat.is_le(len, Nat.mul(Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q), 1n+q)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(q, 0n), q, hk.sub_zero(q)) : {Nat.is_le(len, Nat.mul(Nat.div(Nat.add(len, _), 1n+q), 1n+q)) == True{} : Bool}
  hk.cancel(Nat.mul(Nat.div(Nat.add(len, q), 1n+q), 1n+q), Nat.mod(Nat.add(len, q), 1n+q), len, q)(Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(Nat.add(len, q), 1n+q), 1n+q), Nat.mod(Nat.add(len, q), 1n+q)), Nat.add(Nat.add(len, q), Nat.add(Nat.mul(0n, 1n+q), 0n)), Nat.add(len, q), hk.ds(Nat.add(len, q), q, 0n, 0n, q)(UL.nat_add_zero(q)), UL.nat_add_zero(Nat.add(len, q))))(hk.mod_le(Nat.add(len, q), q, 0n, 0n, q)(UL.nat_add_zero(q)))

# the quotient never falls as the dividend grows
def hk.q_ge(+x: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(d, Pair.fst(Nat, Nat, Nat.divmod.go(x, m, d, r))) == True{} : Bool}:
  match x:
    case 0n:
      UL.nat_le_refl(d)
    case 1n+xp:
      match m:
        case 0n:
          hk.le_trans(d, 1n+d, Pair.fst(Nat, Nat, Nat.divmod.go(xp, r, 1n+d, 0n)))(hk.le_step(d, d)(UL.nat_le_refl(d)))(hk.q_ge(xp, r, 1n+d, 0n))
        case 1n+mp:
          hk.q_ge(xp, mp, d, 1n+r)

def hk.qmono(+a: Nat, +j: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(a, m, d, r)), Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(a, j), m, d, r))) == True{} : Bool}:
  match a:
    case 0n:
      hk.q_ge(j, m, d, r)
    case 1n+ap:
      match m:
        case 0n:
          hk.qmono(ap, j, r, 1n+d, 0n)
        case 1n+mp:
          hk.qmono(ap, j, mp, d, 1n+r)

# more bytes need no fewer blocks
def hk.nmono(+n: Nat, +j: Nat, +q: Nat) -> {Nat.is_le(Nat.div(Nat.add(n, Nat.sub(1n+q, 1n)), 1n+q), Nat.div(Nat.add(Nat.add(n, j), Nat.sub(1n+q, 1n)), 1n+q)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(q, 0n), q, hk.sub_zero(q)) : {Nat.is_le(Nat.div(Nat.add(n, _), 1n+q), Nat.div(Nat.add(Nat.add(n, j), _), 1n+q)) == True{} : Bool}
  %Equal.trans(Nat, Nat.add(Nat.add(n, q), j), Nat.add(n, Nat.add(q, j)), Nat.add(Nat.add(n, j), q), UL.nat_add_assoc(n, q, j), Equal.trans(Nat, Nat.add(n, Nat.add(q, j)), Nat.add(n, Nat.add(j, q)), Nat.add(Nat.add(n, j), q), Equal.cong(Nat, Nat, z => Nat.add(n, z), Nat.add(q, j), Nat.add(j, q), UL.nat_add_comm(q, j)), Equal.sym(Nat, Nat.add(Nat.add(n, j), q), Nat.add(n, Nat.add(j, q)), UL.nat_add_assoc(n, j, q)))) : {Nat.is_le(Nat.div(Nat.add(n, q), 1n+q), Nat.div(_, 1n+q)) == True{} : Bool}
  hk.qmono(Nat.add(n, q), j, q, 0n, 0n)

# Lists of Nat and of Octets

def hk.ldisc(l: List<&2, Nat>) -> Type:
  match l:
    case Nil{}:
      Empty
    case Con{a, t}:
      Unit

def hk.lnd(+a: Nat, +t: List<&2, Nat>, h: {Con{a, t} == Nil{} : List<&2, Nat>}) -> Empty:
  %h : hk.ldisc(_)
  Unit{}

def hk.nhd(l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{x, t}:
      x

def hk.ntl(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def hk.con2(+x: Nat, +y: Nat, +t: List<&2, Nat>, +u: List<&2, Nat>, ex: {x == y : Nat}, et: {t == u : List<&2, Nat>}) -> {Con{x, t} == Con{y, u} : List<&2, Nat>}:
  %ex : {Con{x, t} == Con{_, u} : List<&2, Nat>}
  %et : {Con{x, t} == Con{x, _} : List<&2, Nat>}
  {==}

def hk.lns(os: List<&2, B.Octets>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      Nil{}
    case Con{+o, t}:
      Con{B.Octets.len(o), hk.lns(t)}

def hk.nr(n: Nat, +d: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{d, hk.nr(p, d)}

def hk.app(a: List<&2, B.Octets>, b: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match a:
    case Nil{}:
      b
    case Con{x, t}:
      Con{x, hk.app(t, b)}

def hk.llen(os: List<&2, B.Octets>) -> Nat:
  match os:
    case Nil{}:
      0n
    case Con{o, t}:
      1n+hk.llen(t)

def hk.app_nil(+p: List<&2, B.Octets>) -> {hk.app(p, Nil{}) == p : List<&2, B.Octets>}:
  match p:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %hk.app_nil(t) : {Con{x, hk.app(t, Nil{})} == Con{x, _} : List<&2, B.Octets>}
      {==}

def hk.rro(+p: List<&2, B.Octets>, +c: List<&2, B.Octets>, +z: List<&2, B.Octets>) -> {Hk.cr.hkdf.rev(Hk.cr.hkdf.rev(p, c), z) == Hk.cr.hkdf.rev(c, hk.app(p, z)) : List<&2, B.Octets>}:
  match p:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      hk.rro(t, Con{x, c}, z)

def hk.rr(+p: List<&2, B.Octets>) -> {Hk.cr.hkdf.rev(Hk.cr.hkdf.rev(p, Nil{}), Nil{}) == p : List<&2, B.Octets>}:
  Equal.trans(List<&2, B.Octets>, Hk.cr.hkdf.rev(Hk.cr.hkdf.rev(p, Nil{}), Nil{}), hk.app(p, Nil{}), p, hk.rro(p, Nil{}, Nil{}), hk.app_nil(p))

# HKDF's blocks T(1), T(2), ..., structurally, and the outer HMAC inputs
# whose digests they are

def hk.ts(~digest: B.Octets -> B.Octets, n: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> List<&2, B.Octets>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +t = Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr]))))
      Con{t, hk.ts(~digest, p, kk, info, t, U32.add(ctr, 1))}

def hk.oin(~digest: B.Octets -> B.Octets, kk: Hm.CrHmacKey, +m: B.Octets) -> B.Octets:
  match kk:
    case Hm.CrHmacKey{i, o}:
      B.Octets.append(o, digest(B.Octets.append(i, m)))

def hk.ins(~digest: B.Octets -> B.Octets, n: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> List<&2, B.Octets>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{hk.oin(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), hk.ins(~digest, p, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1))}

# the rest of the blocks after the first a, for b more
def hk.tsr(~digest: B.Octets -> B.Octets, a: Nat, +b: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> List<&2, B.Octets>:
  match a:
    case 0n:
      hk.ts(~digest, b, kk, info, prev, ctr)
    case 1n+ap:
      hk.tsr(~digest, ap, b, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1))

# hkdf.bend's loop is the blocks reversed onto its accumulator
def hk.blocks_ts(~digest: B.Octets -> B.Octets, n: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32, +acc: List<&2, B.Octets>) -> {Hk.cr.hkdf.blocks(~digest, n, kk, info, prev, ctr, acc) == Hk.cr.hkdf.rev(hk.ts(~digest, n, kk, info, prev, ctr), acc) : List<&2, B.Octets>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      hk.blocks_ts(~digest, p, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1), Con{Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), acc})

# the inputs' digests are the blocks
def hk.dl2(~digest: B.Octets -> B.Octets, n: Nat, +i: B.Octets, +o: B.Octets, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> {Laws.crhk.dlens(~digest, hk.ins(~digest, n, Hm.CrHmacKey{i, o}, info, prev, ctr)) == hk.lns(hk.ts(~digest, n, Hm.CrHmacKey{i, o}, info, prev, ctr)) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %hk.dl2(~digest, p, i, o, info, Hm.CrHmac.mac(~digest, Hm.CrHmacKey{i, o}, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1)) : {Con{B.Octets.len(Hm.CrHmac.mac(~digest, Hm.CrHmacKey{i, o}, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr]))))), Laws.crhk.dlens(~digest, hk.ins(~digest, p, Hm.CrHmacKey{i, o}, info, Hm.CrHmac.mac(~digest, Hm.CrHmacKey{i, o}, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1)))} == Con{B.Octets.len(Hm.CrHmac.mac(~digest, Hm.CrHmacKey{i, o}, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr]))))), _} : List<&2, Nat>}
      {==}

def hk.dl(~digest: B.Octets -> B.Octets, kk: Hm.CrHmacKey, n: Nat, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> {Laws.crhk.dlens(~digest, hk.ins(~digest, n, kk, info, prev, ctr)) == hk.lns(hk.ts(~digest, n, kk, info, prev, ctr)) : List<&2, Nat>}:
  match kk:
    case Hm.CrHmacKey{i, o}:
      hk.dl2(~digest, n, i, o, info, prev, ctr)

def hk.rp(~digest: B.Octets -> B.Octets, n: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32, +d: Nat) -> {Laws.crhk.reps(d, hk.ins(~digest, n, kk, info, prev, ctr)) == hk.nr(n, d) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %hk.rp(~digest, p, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1), d) : {Con{d, Laws.crhk.reps(d, hk.ins(~digest, p, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1)))} == Con{d, _} : List<&2, Nat>}
      {==}

def hk.llen_ts(~digest: B.Octets -> B.Octets, n: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> {hk.llen(hk.ts(~digest, n, kk, info, prev, ctr)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %hk.llen_ts(~digest, p, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1)) : {1n+hk.llen(hk.ts(~digest, p, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1))) == 1n+_ : Nat}
      {==}

# the first a + b blocks are the first a, then the next b
def hk.ts_split(~digest: B.Octets -> B.Octets, a: Nat, +b: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, +prev: B.Octets, +ctr: U32) -> {hk.ts(~digest, Nat.add(a, b), kk, info, prev, ctr) == hk.app(hk.ts(~digest, a, kk, info, prev, ctr), hk.tsr(~digest, a, b, kk, info, prev, ctr)) : List<&2, B.Octets>}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %hk.ts_split(~digest, ap, b, kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1)) : {Con{Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), hk.ts(~digest, Nat.add(ap, b), kk, info, Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), U32.add(ctr, 1))} == Con{Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr])))), _} : List<&2, B.Octets>}
      {==}

# Lengths

# blocks of d bytes each, k of them: k d bytes joined
def hk.cat_len(os: List<&2, B.Octets>, +k: Nat, +d: Nat) -> {hk.lns(os) == hk.nr(k, d) : List<&2, Nat>} -> {B.Octets.len(B.Octets.concat(os)) == Nat.mul(k, d) : Nat}:
  match os:
    case Nil{}:
      match k:
        case 0n:
          h => {==}
        case 1n+kp:
          h => Empty.absurd({B.Octets.len(B.Octets.concat(Nil{})) == Nat.mul(1n+kp, d) : Nat}, hk.lnd(d, hk.nr(kp, d), Equal.sym(List<&2, Nat>, Nil{}, Con{d, hk.nr(kp, d)}, h)))
    case Con{+o, +t}:
      match k:
        case 0n:
          h => Empty.absurd({B.Octets.len(B.Octets.concat(Con{o, t})) == 0n : Nat}, hk.lnd(B.Octets.len(o), hk.lns(t), h))
        case 1n+kp:
          +h => Equal.trans(Nat, B.Octets.len(B.Octets.concat(Con{o, t})), B.Octets.len(B.Octets.append(o, B.Octets.concat(t))), Nat.add(d, Nat.mul(kp, d)), Equal.cong(B.Octets, Nat, y => B.Octets.len(y), B.Octets.concat(Con{o, t}), B.Octets.append(o, B.Octets.concat(t)), BL.octets_concat_cons(o, t)), Equal.trans(Nat, B.Octets.len(B.Octets.append(o, B.Octets.concat(t))), Nat.add(B.Octets.len(o), B.Octets.len(B.Octets.concat(t))), Nat.add(d, Nat.mul(kp, d)), BL.octets_len_append(o, B.Octets.concat(t)), Equal.trans(Nat, Nat.add(B.Octets.len(o), B.Octets.len(B.Octets.concat(t))), Nat.add(d, B.Octets.len(B.Octets.concat(t))), Nat.add(d, Nat.mul(kp, d)), Equal.cong(Nat, Nat, y => Nat.add(y, B.Octets.len(B.Octets.concat(t))), B.Octets.len(o), d, Equal.cong(List<&2, Nat>, Nat, l => hk.nhd(l), hk.lns(Con{o, t}), hk.nr(1n+kp, d), h)), Equal.cong(Nat, Nat, y => Nat.add(d, y), B.Octets.len(B.Octets.concat(t)), Nat.mul(kp, d), hk.cat_len(t, kp, d)(Equal.cong(List<&2, Nat>, List<&2, Nat>, l => hk.ntl(l), hk.lns(Con{o, t}), hk.nr(1n+kp, d), h))))))

def hk.cat_app(a: List<&2, B.Octets>, +b: List<&2, B.Octets>) -> {B.Octets.concat(hk.app(a, b)) == B.Octets.append(B.Octets.concat(a), B.Octets.concat(b)) : B.Octets}:
  match a:
    case Nil{}:
      Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), B.Octets.concat(b)), B.Octets.concat(b), BL.octets_append_empty_l(B.Octets.concat(b)))
    case Con{+x, +t}:
      Equal.trans(B.Octets, B.Octets.concat(Con{x, hk.app(t, b)}), B.Octets.append(x, B.Octets.concat(hk.app(t, b))), B.Octets.append(B.Octets.concat(Con{x, t}), B.Octets.concat(b)), BL.octets_concat_cons(x, hk.app(t, b)), Equal.trans(B.Octets, B.Octets.append(x, B.Octets.concat(hk.app(t, b))), B.Octets.append(x, B.Octets.append(B.Octets.concat(t), B.Octets.concat(b))), B.Octets.append(B.Octets.concat(Con{x, t}), B.Octets.concat(b)), Equal.cong(B.Octets, B.Octets, y => B.Octets.append(x, y), B.Octets.concat(hk.app(t, b)), B.Octets.append(B.Octets.concat(t), B.Octets.concat(b)), hk.cat_app(t, b)), Equal.trans(B.Octets, B.Octets.append(x, B.Octets.append(B.Octets.concat(t), B.Octets.concat(b))), B.Octets.append(B.Octets.append(x, B.Octets.concat(t)), B.Octets.concat(b)), B.Octets.append(B.Octets.concat(Con{x, t}), B.Octets.concat(b)), Equal.sym(B.Octets, B.Octets.append(B.Octets.append(x, B.Octets.concat(t)), B.Octets.concat(b)), B.Octets.append(x, B.Octets.append(B.Octets.concat(t), B.Octets.concat(b))), BL.octets_append_assoc(x, B.Octets.concat(t), B.Octets.concat(b))), Equal.cong(B.Octets, B.Octets, y => B.Octets.append(y, B.Octets.concat(b)), B.Octets.append(x, B.Octets.concat(t)), B.Octets.concat(Con{x, t}), Equal.sym(B.Octets, B.Octets.concat(Con{x, t}), B.Octets.append(x, B.Octets.concat(t)), BL.octets_concat_cons(x, t))))))

# the lengths of a joined list's first part
def hk.lpre(a: List<&2, B.Octets>, +b: List<&2, B.Octets>, +d: Nat, +k: Nat) -> {hk.lns(hk.app(a, b)) == hk.nr(k, d) : List<&2, Nat>} -> {hk.lns(a) == hk.nr(hk.llen(a), d) : List<&2, Nat>}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+x, +t}:
      match k:
        case 0n:
          h => Empty.absurd({hk.lns(Con{x, t}) == hk.nr(hk.llen(Con{x, t}), d) : List<&2, Nat>}, hk.lnd(B.Octets.len(x), hk.lns(hk.app(t, b)), h))
        case 1n+kp:
          +h => hk.con2(B.Octets.len(x), d, hk.lns(t), hk.nr(hk.llen(t), d), Equal.cong(List<&2, Nat>, Nat, l => hk.nhd(l), hk.lns(hk.app(Con{x, t}, b)), hk.nr(1n+kp, d), h), hk.lpre(t, b, d, kp)(Equal.cong(List<&2, Nat>, List<&2, Nat>, l => hk.ntl(l), hk.lns(hk.app(Con{x, t}, b)), hk.nr(1n+kp, d), h)))

# The derivation

# hkdf.bend's cr.hkdf.expand with the digest size an argument d
def hk.exp(~bsize: Nat, ~digest: B.Octets -> B.Octets, +d: Nat, ok: Bool, +prk: B.Octets, +info: B.Octets, +len: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match ok:
    case False{}:
      Fail{Cr.CrBadOutputLength{len}}
    case True{}:
      +n = Nat.div(Nat.add(len, Nat.sub(d, 1n)), d)
      +ts = Hk.cr.hkdf.blocks(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{})
      Done{B.Octets.take(len, B.Octets.concat(Hk.cr.hkdf.rev(ts, Nil{})))}

# cr.hkdf.expand is hk.exp at the template's digest size
def hk.bridge(~bsize: Nat, ~dsize: Nat, ~digest: B.Octets -> B.Octets, ok: Bool, +prk: B.Octets, +info: B.Octets, +len: Nat) -> {Hk.cr.hkdf.expand(~bsize, ~dsize, ~digest, ok, prk, info, len) == hk.exp(~bsize, ~digest, dsize, ok, prk, info, len) : Result<&2, &2, Cr.CrError, B.Octets>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

# the first n blocks
def hk.T(~bsize: Nat, ~digest: B.Octets -> B.Octets, +prk: B.Octets, +info: B.Octets, +n: Nat) -> List<&2, B.Octets>:
  hk.ts(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)

def hk.out(~bsize: Nat, ~digest: B.Octets -> B.Octets, +prk: B.Octets, +info: B.Octets, +n: Nat, +len: Nat) -> {B.Octets.take(len, B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))) == B.Octets.take(len, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, n))) : B.Octets}:
  %Equal.sym(List<&2, B.Octets>, Hk.cr.hkdf.blocks(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Hk.cr.hkdf.rev(hk.T(~bsize, ~digest, prk, info, n), Nil{}), hk.blocks_ts(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{})) : {B.Octets.take(len, B.Octets.concat(Hk.cr.hkdf.rev(_, Nil{}))) == B.Octets.take(len, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, n))) : B.Octets}
  %Equal.sym(List<&2, B.Octets>, Hk.cr.hkdf.rev(Hk.cr.hkdf.rev(hk.T(~bsize, ~digest, prk, info, n), Nil{}), Nil{}), hk.T(~bsize, ~digest, prk, info, n), hk.rr(hk.T(~bsize, ~digest, prk, info, n))) : {B.Octets.take(len, B.Octets.concat(_)) == B.Octets.take(len, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, n))) : B.Octets}
  {==}

# every block has 1 + q bytes, by hd at the blocks' outer HMAC inputs
def hk.tlen(~bsize: Nat, ~digest: B.Octets -> B.Octets, +q: Nat, hd: @xs: List<&2, B.Octets> -> {Laws.crhk.dlens(~digest, xs) == Laws.crhk.reps(1n+q, xs) : List<&2, Nat>}, +prk: B.Octets, +info: B.Octets, +n: Nat) -> {hk.lns(hk.T(~bsize, ~digest, prk, info, n)) == hk.nr(n, 1n+q) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, hk.lns(hk.T(~bsize, ~digest, prk, info, n)), Laws.crhk.dlens(~digest, hk.ins(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)), hk.nr(n, 1n+q), Equal.sym(List<&2, Nat>, Laws.crhk.dlens(~digest, hk.ins(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)), hk.lns(hk.T(~bsize, ~digest, prk, info, n)), hk.dl(~digest, Hm.CrHmac.key(~bsize, ~digest, prk), n, info, B.Octets.empty(), 1)), Equal.trans(List<&2, Nat>, Laws.crhk.dlens(~digest, hk.ins(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)), Laws.crhk.reps(1n+q, hk.ins(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)), hk.nr(n, 1n+q), hd(hk.ins(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)), hk.rp(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, 1n+q)))

# the blocks for len bytes cover len bytes
def hk.cover(~bsize: Nat, ~digest: B.Octets -> B.Octets, +q: Nat, +prk: B.Octets, +info: B.Octets, +len: Nat, ht: {hk.lns(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q))) == hk.nr(Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q), 1n+q) : List<&2, Nat>}) -> {Nat.is_le(len, B.Octets.len(B.Octets.concat(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q))))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.concat(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q)))), Nat.mul(Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q), 1n+q), hk.cat_len(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q)), Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q), 1n+q)(ht)) : {Nat.is_le(len, _) == True{} : Bool}
  hk.ceil(len, q)

def hk.len_ok(~bsize: Nat, ~digest: B.Octets -> B.Octets, ok: Bool, +d: Nat, hd: @xs: List<&2, B.Octets> -> {Laws.crhk.dlens(~digest, xs) == Laws.crhk.reps(d, xs) : List<&2, Nat>}, +prk: B.Octets, +info: B.Octets, +len: Nat) -> {Hk.cr.hkdf.ok(Nat.is_lt(0n, d), len, d) == ok : Bool} -> {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), hk.exp(~bsize, ~digest, d, ok, prk, info, len)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => len, hk.exp(~bsize, ~digest, d, ok, prk, info, len)) : Result<&2, &2, Cr.CrError, Nat>}:
  match ok:
    case False{}:
      e => {==}
    case True{}:
      match d:
        case 0n:
          e => hk.absurd({Done{B.Octets.len(B.Octets.take(len, B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, Nat.div(Nat.add(len, Nat.sub(0n, 1n)), 0n), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))))} == Done{len} : Result<&2, &2, Cr.CrError, Nat>}, e)
        case 1n+q:
          e => %Equal.sym(B.Octets, B.Octets.take(len, B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))), B.Octets.take(len, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q)))), hk.out(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q), len)) : {Done{B.Octets.len(_)} == Done{len} : Result<&2, &2, Cr.CrError, Nat>}
            %Equal.sym(Nat, B.Octets.len(B.Octets.take(len, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q))))), len, BL.octets_len_take_le(len, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q))), hk.cover(~bsize, ~digest, q, prk, info, len, hk.tlen(~bsize, ~digest, q, hd, prk, info, Nat.div(Nat.add(len, Nat.sub(1n+q, 1n)), 1n+q))))) : {Done{_} == Done{len} : Result<&2, &2, Cr.CrError, Nat>}
            {==}

def Laws.hkdf_length(bsize, dsize, digest, hd, ikm, salt, info, n):
  %Equal.sym(Result<&2, &2, Cr.CrError, B.Octets>, Hk.cr.hkdf.expand(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n), hk.exp(~bsize, ~digest, dsize, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n), hk.bridge(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n)) : {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), _) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, _) : Result<&2, &2, Cr.CrError, Nat>}
  hk.len_ok(~bsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), dsize, hd, Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n)({==})

# the prefix: from the blocks for n + j bytes, the first n
def hk.pre_core(~bsize: Nat, ~digest: B.Octets -> B.Octets, +q: Nat, hd: @xs: List<&2, B.Octets> -> {Laws.crhk.dlens(~digest, xs) == Laws.crhk.reps(1n+q, xs) : List<&2, Nat>}, +prk: B.Octets, +info: B.Octets, +n: Nat, +j: Nat) -> {Done{B.Octets.take(n, B.Octets.take(Nat.add(n, j), B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, Nat.div(Nat.add(Nat.add(n, j), Nat.sub(1n+q, 1n)), 1n+q), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))))} == hk.exp(~bsize, ~digest, 1n+q, True{}, prk, info, n) : Result<&2, &2, Cr.CrError, B.Octets>}:
  +nb = Nat.div(Nat.add(n, Nat.sub(1n+q, 1n)), 1n+q)
  +nb2 = Nat.div(Nat.add(Nat.add(n, j), Nat.sub(1n+q, 1n)), 1n+q)
  +ex = hk.add_sub(nb, nb2)(hk.nmono(n, j, q))
  # the blocks for n + j bytes are those for n, then more
  +sp = hk.ts_split(~digest, nb, Nat.sub(nb2, nb), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)
  +rest = hk.tsr(~digest, nb, Nat.sub(nb2, nb), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)
  # the first nb blocks have 1 + q bytes each
  +l2 = Equal.trans(List<&2, Nat>, hk.lns(hk.app(hk.T(~bsize, ~digest, prk, info, nb), rest)), hk.lns(hk.T(~bsize, ~digest, prk, info, nb2)), hk.nr(nb2, 1n+q), Equal.cong(List<&2, B.Octets>, List<&2, Nat>, l => hk.lns(l), hk.app(hk.T(~bsize, ~digest, prk, info, nb), rest), hk.T(~bsize, ~digest, prk, info, nb2), Equal.trans(List<&2, B.Octets>, hk.app(hk.T(~bsize, ~digest, prk, info, nb), rest), hk.T(~bsize, ~digest, prk, info, Nat.add(nb, Nat.sub(nb2, nb))), hk.T(~bsize, ~digest, prk, info, nb2), Equal.sym(List<&2, B.Octets>, hk.T(~bsize, ~digest, prk, info, Nat.add(nb, Nat.sub(nb2, nb))), hk.app(hk.T(~bsize, ~digest, prk, info, nb), rest), sp), Equal.cong(Nat, List<&2, B.Octets>, z => hk.T(~bsize, ~digest, prk, info, z), Nat.add(nb, Nat.sub(nb2, nb)), nb2, ex))), hk.tlen(~bsize, ~digest, q, hd, prk, info, nb2))
  +l1 = Equal.trans(List<&2, Nat>, hk.lns(hk.T(~bsize, ~digest, prk, info, nb)), hk.nr(hk.llen(hk.T(~bsize, ~digest, prk, info, nb)), 1n+q), hk.nr(nb, 1n+q), hk.lpre(hk.T(~bsize, ~digest, prk, info, nb), rest, 1n+q, nb2)(l2), Equal.cong(Nat, List<&2, Nat>, z => hk.nr(z, 1n+q), hk.llen(hk.T(~bsize, ~digest, prk, info, nb)), nb, hk.llen_ts(~digest, nb, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1)))
  +hle = hk.cover(~bsize, ~digest, q, prk, info, n, l1)
  # the blocks as their structural forms
  %Equal.sym(B.Octets, B.Octets.take(Nat.add(n, j), B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, nb2, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))), B.Octets.take(Nat.add(n, j), B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb2))), hk.out(~bsize, ~digest, prk, info, nb2, Nat.add(n, j))) : {Done{B.Octets.take(n, _)} == hk.exp(~bsize, ~digest, 1n+q, True{}, prk, info, n) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.take(n, B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, nb, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))), B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb))), hk.out(~bsize, ~digest, prk, info, nb, n)) : {Done{B.Octets.take(n, B.Octets.take(Nat.add(n, j), B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb2))))} == Done{_} : Result<&2, &2, Cr.CrError, B.Octets>}
  # the first n of the first n + j bytes are the first n
  %Equal.sym(B.Octets, B.Octets.take(n, B.Octets.take(Nat.add(n, j), B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb2)))), B.Octets.take(Nat.min(n, Nat.add(n, j)), B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb2))), BL.octets_take_take(n, Nat.add(n, j), B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb2)))) : {Done{_} == Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Nat, Nat.min(n, Nat.add(n, j)), n, hk.min_add(n, j)) : {Done{B.Octets.take(_, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb2)))} == Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  # and the blocks for n + j bytes start with those for n, which cover n
  %ex : {Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, _)))} == Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(List<&2, B.Octets>, hk.T(~bsize, ~digest, prk, info, Nat.add(nb, Nat.sub(nb2, nb))), hk.app(hk.T(~bsize, ~digest, prk, info, nb), rest), sp) : {Done{B.Octets.take(n, B.Octets.concat(_))} == Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.concat(hk.app(hk.T(~bsize, ~digest, prk, info, nb), rest)), B.Octets.append(B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)), B.Octets.concat(rest)), hk.cat_app(hk.T(~bsize, ~digest, prk, info, nb), rest)) : {Done{B.Octets.take(n, _)} == Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.take(n, B.Octets.append(B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)), B.Octets.concat(rest))), B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb))), BL.octets_take_append_le(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)), B.Octets.concat(rest), hle)) : {Done{_} == Done{B.Octets.take(n, B.Octets.concat(hk.T(~bsize, ~digest, prk, info, nb)))} : Result<&2, &2, Cr.CrError, B.Octets>}
  {==}

def hk.pre_ok(~bsize: Nat, ~digest: B.Octets -> B.Octets, ok: Bool, +d: Nat, hd: @xs: List<&2, B.Octets> -> {Laws.crhk.dlens(~digest, xs) == Laws.crhk.reps(d, xs) : List<&2, Nat>}, +prk: B.Octets, +info: B.Octets, +n: Nat, +j: Nat) -> {Hk.cr.hkdf.ok(Nat.is_lt(0n, d), Nat.add(n, j), d) == ok : Bool} -> {Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, o => B.Octets.take(n, o), hk.exp(~bsize, ~digest, d, ok, prk, info, Nat.add(n, j))) == Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, hk.exp(~bsize, ~digest, d, ok, prk, info, Nat.add(n, j)), o => hk.exp(~bsize, ~digest, d, Hk.cr.hkdf.ok(Nat.is_lt(0n, d), n, d), prk, info, n)) : Result<&2, &2, Cr.CrError, B.Octets>}:
  match ok:
    case False{}:
      e => {==}
    case True{}:
      match d:
        case 0n:
          e => hk.absurd({Done{B.Octets.take(n, B.Octets.take(Nat.add(n, j), B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, Nat.div(Nat.add(Nat.add(n, j), Nat.sub(0n, 1n)), 0n), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))))} == hk.exp(~bsize, ~digest, 0n, False{}, prk, info, n) : Result<&2, &2, Cr.CrError, B.Octets>}, e)
        case 1n+q:
          e => %Equal.sym(Bool, Nat.is_le(n, Nat.mul(255n, 1n+q)), True{}, hk.le_trans(n, Nat.add(n, j), Nat.mul(255n, 1n+q))(UO.nat_le_add_r(n, j))(e)) : {Done{B.Octets.take(n, B.Octets.take(Nat.add(n, j), B.Octets.concat(Hk.cr.hkdf.rev(Hk.cr.hkdf.blocks(~digest, Nat.div(Nat.add(Nat.add(n, j), Nat.sub(1n+q, 1n)), 1n+q), Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{}), Nil{}))))} == hk.exp(~bsize, ~digest, 1n+q, _, prk, info, n) : Result<&2, &2, Cr.CrError, B.Octets>}
            hk.pre_core(~bsize, ~digest, q, hd, prk, info, n, j)

def Laws.hkdf_prefix(bsize, dsize, digest, hd, ikm, salt, info, n, j):
  %Equal.sym(Result<&2, &2, Cr.CrError, B.Octets>, Hk.cr.hkdf.expand(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), Nat.add(n, j), dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, Nat.add(n, j)), hk.exp(~bsize, ~digest, dsize, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), Nat.add(n, j), dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, Nat.add(n, j)), hk.bridge(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), Nat.add(n, j), dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, Nat.add(n, j))) : {Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, o => B.Octets.take(n, o), _) == Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, _, o => Hk.cr.hkdf.expand(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n)) : Result<&2, &2, Cr.CrError, B.Octets>}
  %Equal.sym(Result<&2, &2, Cr.CrError, B.Octets>, Hk.cr.hkdf.expand(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n), hk.exp(~bsize, ~digest, dsize, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n), hk.bridge(~bsize, ~dsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), n, dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n)) : {Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, o => B.Octets.take(n, o), hk.exp(~bsize, ~digest, dsize, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), Nat.add(n, j), dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, Nat.add(n, j))) == Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, hk.exp(~bsize, ~digest, dsize, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), Nat.add(n, j), dsize), Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, Nat.add(n, j)), o => _) : Result<&2, &2, Cr.CrError, B.Octets>}
  hk.pre_ok(~bsize, ~digest, Hk.cr.hkdf.ok(Nat.is_lt(0n, dsize), Nat.add(n, j), dsize), dsize, hd, Hk.CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, n, j)({==})
