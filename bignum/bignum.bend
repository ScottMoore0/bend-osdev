# bend-osdev-bignum: natural numbers of any size, for public-key
# cryptography.
#
# A BnNat is a list of 16-bit limbs, least significant first (base 2^16:
# the product of two limbs, plus two more limbs, fits in a U32, and a limb is
# two bytes). The type is opaque: other packages use only the defs below.
# A value may carry zero limbs on top (a number reduced modulo n keeps n's
# length); every def accepts them, and equality is by value
# (BnNat.is_eq), not by representation.
#
# This file holds the numbers and their arithmetic: conversion to and from
# big-endian bytes (OS2IP and I2OSP, RFC 8017 section 4), hex text, compare,
# add, subtract, multiply, shift, divide. Modular arithmetic, Montgomery
# multiplication, primality and the Jacobi symbol are in their own files
# (README.md, "Files").
import Base
import ../bytes/bytes.bend as B

# A natural number (opaque): 16-bit limbs, least significant first
type BnNat is Data:
  BnNat{limbs: List<&2, U32>}

# A quotient and remainder (open)
type BnDivMod is Data:
  BnDivMod{q: BnNat, r: BnNat}

def BnDivMod.q(d: BnDivMod) -> BnNat:
  match d:
    case BnDivMod{q, r}:
      q

def BnDivMod.r(d: BnDivMod) -> BnNat:
  match d:
    case BnDivMod{q, r}:
      r

# hex text read (internal)
type BnNibs is Data:
  BnNibs{ok: Bool, ns: List<&2, U32>}

# ---------------------------------------------------------------- limbs

def bn.lone(z: Bool, +c: U32) -> List<&2, U32>:
  match z:
    case True{}:
      Nil{}
    case False{}:
      Con{c, Nil{}}

# xs + c
def bn.carry(xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Con{z, zs}:
      +t = (z + c : U32)
      Con{U32.and(65535, t), bn.carry(zs, U32.shrn(t, 16n))}
    case Nil{}:
      bn.lone(U32.is_zero(c), c)

# a + b + c
def bn.add(a: List<&2, U32>, b: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match a b:
    case Con{x, xs} Con{y, ys}:
      +t = (x + y + c : U32)
      Con{U32.and(65535, t), bn.add(xs, ys, U32.shrn(t, 16n))}
    case Nil{} ys:
      bn.carry(ys, c)
    case xs Nil{}:
      bn.carry(xs, c)

# a - b - w, for a >= b + w (as long as a; wraps otherwise)
def bn.sub(a: List<&2, U32>, b: List<&2, U32>, +w: U32) -> List<&2, U32>:
  match a b:
    case Con{x, xs} Con{y, ys}:
      +t = (x + 65536 - y - w : U32)
      Con{U32.and(65535, t), bn.sub(xs, ys, (1 - U32.shrn(t, 16n) : U32))}
    case Con{x, xs} Nil{}:
      +t = (x + 65536 - w : U32)
      Con{U32.and(65535, t), bn.sub(xs, Nil{}, (1 - U32.shrn(t, 16n) : U32))}
    case Nil{} ys:
      Nil{}

# acc + x * b + c
def bn.mac(b: List<&2, U32>, +x: U32, acc: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match b acc:
    case Con{y, ys} Con{z, zs}:
      +t = (z + x * y + c : U32)
      Con{U32.and(65535, t), bn.mac(ys, x, zs, U32.shrn(t, 16n))}
    case Con{y, ys} Nil{}:
      +t = (x * y + c : U32)
      Con{U32.and(65535, t), bn.mac(ys, x, Nil{}, U32.shrn(t, 16n))}
    case Nil{} zs:
      bn.carry(zs, c)

# a * b, schoolbook
def bn.mul(a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      bn.mac(b, x, Con{0, bn.mul(xs, b)}, 0)

def bn.allz(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(U32.is_zero(x), bn.allz(t))

def bn.cons(+x: U32, r: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Nil{}:
      bn.lone(U32.is_zero(x), x)
    case s:
      Con{x, s}

# without zero limbs on top
def bn.norm(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      bn.cons(x, bn.norm(t))

def bn.step(c: Cmp, acc: Cmp) -> Cmp:
  match c:
    case EQ{}:
      acc
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def bn.or_rest(z: Bool, acc: Cmp, other: Cmp) -> Cmp:
  match z:
    case True{}:
      acc
    case False{}:
      other

# compare, acc being the comparison of the limbs below
def bn.cmp(a: List<&2, U32>, b: List<&2, U32>, acc: Cmp) -> Cmp:
  match a b:
    case Con{x, xs} Con{y, ys}:
      bn.cmp(xs, ys, bn.step(U32.cmp(x, y), acc))
    case Nil{} Nil{}:
      acc
    case Nil{} ys:
      bn.or_rest(bn.allz(ys), acc, LT{})
    case xs Nil{}:
      bn.or_rest(bn.allz(xs), acc, GT{})

def bn.zeros(k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{0, bn.zeros(p)}

def bn.len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# the bits of a limb: the position of its highest set bit, plus one
def bn.wbits.pick(z: Bool, +i: Nat, rest: Nat) -> Nat:
  match z:
    case True{}:
      rest
    case False{}:
      i

def bn.wbits(+i: Nat, +x: U32) -> Nat:
  match i:
    case 0n:
      0n
    case 1n+p:
      bn.wbits.pick(U32.is_zero(U32.shrn(x, p)), i, bn.wbits(p, x))

def bn.top(xs: List<&2, U32>) -> U32:
  Maybe.default(&2, U32, List.last(&2, U32, xs), 0)

def bn.bitlen(xs: List<&2, U32>) -> Nat:
  +n = bn.norm(xs)
  Nat.add(Nat.mul(16n, Nat.sub(bn.len(n), 1n)), bn.wbits(16n, bn.top(n)))

# xs * 2 + c (c a bit)
def bn.shl1(xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Con{x, t}:
      +v = (U32.shln(x, 1n) + c : U32)
      Con{U32.and(65535, v), bn.shl1(t, U32.shrn(v, 16n))}
    case Nil{}:
      bn.lone(U32.is_zero(c), c)

def bn.hd(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

def bn.tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# xs / 2
def bn.shr1(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, +t}:
      Con{U32.or(U32.shrn(x, 1n), U32.shln(U32.and(1, bn.hd(t)), 15n)), bn.shr1(t)}

# xs * 2^s + c, for s below 16
def bn.shlb(xs: List<&2, U32>, +s: Nat, +c: U32) -> List<&2, U32>:
  match xs:
    case Con{x, t}:
      +v = U32.or(U32.shln(x, s), c)
      Con{U32.and(65535, v), bn.shlb(t, s, U32.shrn(v, 16n))}
    case Nil{}:
      bn.lone(U32.is_zero(c), c)

# xs / 2^s, for s below 16
def bn.shrb(xs: List<&2, U32>, +s: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, +t}:
      Con{U32.and(65535, U32.or(U32.shrn(x, s), U32.shln(bn.hd(t), Nat.sub(16n, s)))), bn.shrb(t, s)}

def bn.drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, xs, n)

def bn.ge(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      True{}

# Division by shift and subtract: r against s = b * 2^i for i from d down to
# 0, the quotient's bits collected most significant first
def bn.div.r(ge: Bool, r: List<&2, U32>, s: List<&2, U32>) -> List<&2, U32>:
  match ge:
    case True{}:
      bn.sub(r, s, 0)
    case False{}:
      r

def bn.div.bit(ge: Bool) -> U32:
  match ge:
    case True{}:
      1
    case False{}:
      0

def bn.div.go(i: Nat, +r: List<&2, U32>, +s: List<&2, U32>, q: List<&2, U32>) -> BnDivMod:
  match i:
    case 0n:
      +ge = bn.ge(bn.cmp(r, s, EQ{}))
      BnDivMod{BnNat{bn.shl1(q, bn.div.bit(ge))}, BnNat{bn.norm(bn.div.r(ge, r, s))}}
    case 1n+p:
      +ge = bn.ge(bn.cmp(r, s, EQ{}))
      bn.div.go(p, bn.div.r(ge, r, s), bn.shr1(s), bn.shl1(q, bn.div.bit(ge)))

def bn.shl(xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case s:
      List.append(&2, U32, bn.zeros(Nat.div(n, 16n)), bn.shlb(s, Nat.mod(n, 16n), 0))

def bn.shr(xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  bn.shrb(bn.drop(Nat.div(n, 16n), xs), Nat.mod(n, 16n))

def bn.divmod.go(small: Bool, +a: List<&2, U32>, +b: List<&2, U32>, +la: Nat, +lb: Nat) -> BnDivMod:
  match small:
    case True{}:
      BnDivMod{BnNat{Nil{}}, BnNat{a}}
    case False{}:
      +d = Nat.sub(la, lb)
      bn.div.go(d, bn.norm(a), bn.shl(bn.norm(b), d), Nil{})

# a = q b + r, r < b, for b above 0
def bn.divmod(+a: List<&2, U32>, +b: List<&2, U32>) -> BnDivMod:
  +la = bn.bitlen(a)
  +lb = bn.bitlen(b)
  bn.divmod.go(Nat.is_lt(la, lb), a, b, la, lb)

# ---------------------------------------------------------------- bytes

# little-endian bytes, two to a limb
def bn.pack(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Con{Maybe.default(&2, U32, B.le16.head([a, b]), 0), bn.pack(t)}
    case Con{a, Nil{}}:
      Con{Maybe.default(&2, U32, B.le16.head([a, 0]), 0), Nil{}}
    case Nil{}:
      Nil{}

def bn.unpack(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      B.append(B.le16(x), bn.unpack(t))

def bn.fit.end(z: Bool) -> Maybe<&2, List<&2, U32>>:
  match z:
    case True{}:
      Some{Nil{}}
    case False{}:
      None{}

# the first n little-endian bytes, padded with zeros; None if a byte past
# them is not zero
def bn.fit(n: Nat, xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match n xs:
    case 0n ys:
      bn.fit.end(bn.allz(ys))
    case 1n+p Nil{}:
      Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{0, t}, bn.fit(p, Nil{}))
    case 1n+p Con{y, ys}:
      Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{y, t}, bn.fit(p, ys))

# ---------------------------------------------------------------- hex

def bn.nib.go(d: Bool, l: Bool, u: Bool, +c: U32) -> Maybe<&2, U32>:
  match d l u:
    case True{} _ _:
      Some{(c - 48 : U32)}
    case False{} True{} _:
      Some{(c - 87 : U32)}
    case False{} False{} True{}:
      Some{(c - 55 : U32)}
    case False{} False{} False{}:
      None{}

def bn.nib(+c: U32) -> Maybe<&2, U32>:
  bn.nib.go(Bool.and(U32.is_le(48, c), U32.is_le(c, 57)), Bool.and(U32.is_le(97, c), U32.is_le(c, 102)), Bool.and(U32.is_le(65, c), U32.is_le(c, 70)), c)

def bn.nibs.ok(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

# the nibbles of a hex string, last first, and whether every character was a
# hex digit
def bn.nibs(s: String, ok: Bool, acc: List<&2, U32>) -> BnNibs:
  match s:
    case SNil{}:
      BnNibs{ok, acc}
    case SCon{Chr{c}, t}:
      +m = bn.nib(c)
      bn.nibs(t, Bool.and(ok, bn.nibs.ok(m)), Con{Maybe.default(&2, U32, m, 0), acc})

# nibbles, least significant first, four to a limb
def bn.group(ns: List<&2, U32>) -> List<&2, U32>:
  match ns:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Con{U32.or(U32.or(a, U32.shln(b, 4n)), U32.or(U32.shln(c, 8n), U32.shln(d, 12n))), bn.group(t)}
    case Con{a, Con{b, Con{c, Nil{}}}}:
      Con{U32.or(U32.or(a, U32.shln(b, 4n)), U32.shln(c, 8n)), Nil{}}
    case Con{a, Con{b, Nil{}}}:
      Con{U32.or(a, U32.shln(b, 4n)), Nil{}}
    case Con{a, Nil{}}:
      Con{a, Nil{}}
    case Nil{}:
      Nil{}

def bn.hexd.go(lt: Bool, +d: U32) -> Char:
  match lt:
    case True{}:
      Chr{(48 + d : U32)}
    case False{}:
      Chr{(87 + d : U32)}

def bn.hexd(+d: U32) -> Char:
  bn.hexd.go(U32.is_lt(d, 10), d)

def bn.hex4(+x: U32, acc: String) -> String:
  SCon{bn.hexd(U32.and(15, U32.shrn(x, 12n))), SCon{bn.hexd(U32.and(15, U32.shrn(x, 8n))), SCon{bn.hexd(U32.and(15, U32.shrn(x, 4n))), SCon{bn.hexd(U32.and(15, x)), acc}}}}

def bn.hextop.go(a: Bool, b: Bool, c: Bool, +x: U32, acc: String) -> String:
  match a b c:
    case True{} _ _:
      SCon{bn.hexd(x), acc}
    case False{} True{} _:
      SCon{bn.hexd(U32.shrn(x, 4n)), SCon{bn.hexd(U32.and(15, x)), acc}}
    case False{} False{} True{}:
      SCon{bn.hexd(U32.shrn(x, 8n)), SCon{bn.hexd(U32.and(15, U32.shrn(x, 4n))), SCon{bn.hexd(U32.and(15, x)), acc}}}
    case False{} False{} False{}:
      bn.hex4(x, acc)

def bn.hextop(+x: U32, acc: String) -> String:
  bn.hextop.go(U32.is_lt(x, 16), U32.is_lt(x, 256), U32.is_lt(x, 4096), x, acc)

# the limbs, least significant first, as text: the top one unpadded
def bn.hex(xs: List<&2, U32>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case Con{x, Nil{}}:
      bn.hextop(x, acc)
    case Con{x, t}:
      bn.hex(t, bn.hex4(x, acc))

# ---------------------------------------------------------------- BnNat

def bn.mask16(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.and(65535, x), bn.mask16(t)}

def BnNat.zero() -> BnNat:
  BnNat{Nil{}}

def BnNat.one() -> BnNat:
  BnNat{Con{1, Nil{}}}

# a U32 as a number
def BnNat.of_u32(+x: U32) -> BnNat:
  BnNat{bn.norm(Con{U32.and(65535, x), Con{U32.shrn(x, 16n), Nil{}}})}

# the low 32 bits
def BnNat.to_u32(x: BnNat) -> U32:
  match x:
    case BnNat{+ls}:
      U32.or(bn.hd(ls), U32.shln(bn.hd(bn.tl(ls)), 16n))

# a number from its limbs, least significant first (each masked to 16 bits):
# how generated tables of constants are written
def BnNat.of_limbs(xs: List<&2, U32>) -> BnNat:
  BnNat{bn.mask16(xs)}

# the limbs, least significant first, without zeros on top
def BnNat.to_limbs(x: BnNat) -> List<&2, U32>:
  match x:
    case BnNat{ls}:
      bn.norm(ls)

# OS2IP (RFC 8017, section 4.2): big-endian bytes as a number (with as
# many limbs as the bytes fill, leading zero bytes included)
def BnNat.of_octets(o: B.Octets) -> BnNat:
  BnNat{bn.pack(B.rev(B.Octets.to_list(o)))}

# I2OSP (RFC 8017, section 4.1): the number as n big-endian bytes, or None
# if it needs more ("integer too large")
def BnNat.to_octets(x: BnNat, n: Nat) -> Maybe<&2, B.Octets>:
  match x:
    case BnNat{ls}:
      Maybe.map(&2, List<&2, U32>, B.Octets, r => B.Octets.of_list(B.rev(r)), bn.fit(n, bn.unpack(ls)))

def BnNat.is_zero(x: BnNat) -> Bool:
  match x:
    case BnNat{ls}:
      bn.allz(ls)

def BnNat.is_odd(x: BnNat) -> Bool:
  match x:
    case BnNat{ls}:
      U32.is_eq(U32.and(1, bn.hd(ls)), 1)

# the number of bits, 0 for zero
def BnNat.bit_len(x: BnNat) -> Nat:
  match x:
    case BnNat{ls}:
      bn.bitlen(ls)

# the number of bytes in its shortest big-endian form, 0 for zero
def BnNat.byte_len(x: BnNat) -> Nat:
  Nat.div(Nat.add(BnNat.bit_len(x), 7n), 8n)

# the shortest big-endian form (I2OSP to byte_len bytes)
def BnNat.to_octets_min(+x: BnNat) -> B.Octets:
  Maybe.default(&2, B.Octets, BnNat.to_octets(x, BnNat.byte_len(x)), B.Octets.empty())

# bit i (bit 0 the least significant)
def BnNat.bit(x: BnNat, +i: Nat) -> Bool:
  match x:
    case BnNat{ls}:
      U32.is_eq(U32.and(1, U32.shrn(bn.hd(bn.drop(Nat.div(i, 16n), ls)), Nat.mod(i, 16n))), 1)

def BnNat.cmp(a: BnNat, b: BnNat) -> Cmp:
  match a b:
    case BnNat{x} BnNat{y}:
      bn.cmp(x, y, EQ{})

def BnNat.is_eq(a: BnNat, b: BnNat) -> Bool:
  Cmp.is_eq(BnNat.cmp(a, b))

def BnNat.is_lt(a: BnNat, b: BnNat) -> Bool:
  Cmp.is_lt(BnNat.cmp(a, b))

def BnNat.is_le(a: BnNat, b: BnNat) -> Bool:
  Bool.not(Cmp.is_gt(BnNat.cmp(a, b)))

def BnNat.add(a: BnNat, b: BnNat) -> BnNat:
  match a b:
    case BnNat{x} BnNat{y}:
      BnNat{bn.add(x, y, 0)}

def bn.sub.go(ge: Bool, x: List<&2, U32>, y: List<&2, U32>) -> BnNat:
  match ge:
    case True{}:
      BnNat{bn.norm(bn.sub(x, y, 0))}
    case False{}:
      BnNat{Nil{}}

# a - b, or 0 when b > a
def BnNat.sub(a: BnNat, b: BnNat) -> BnNat:
  match a b:
    case BnNat{+x} BnNat{+y}:
      bn.sub.go(bn.ge(bn.cmp(x, y, EQ{})), x, y)

def BnNat.mul(a: BnNat, b: BnNat) -> BnNat:
  match a b:
    case BnNat{x} BnNat{y}:
      BnNat{bn.mul(x, y)}

# x * 2^n
def BnNat.shl(x: BnNat, +n: Nat) -> BnNat:
  match x:
    case BnNat{ls}:
      BnNat{bn.shl(ls, n)}

# x / 2^n, rounded down
def BnNat.shr(x: BnNat, +n: Nat) -> BnNat:
  match x:
    case BnNat{ls}:
      BnNat{bn.shr(ls, n)}

def bn.divmod.zero(z: Bool, +x: List<&2, U32>, +y: List<&2, U32>) -> Maybe<&2, BnDivMod>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{bn.divmod(x, y)}

# a / b and a mod b, or None for b = 0
def BnNat.divmod(a: BnNat, b: BnNat) -> Maybe<&2, BnDivMod>:
  match a b:
    case BnNat{+x} BnNat{+y}:
      bn.divmod.zero(bn.allz(y), x, y)

def bn.mod.r(d: BnDivMod) -> BnNat:
  match d:
    case BnDivMod{q, r}:
      r

def bn.mod.zero(z: Bool, +x: List<&2, U32>, +y: List<&2, U32>) -> BnNat:
  match z:
    case True{}:
      BnNat{x}
    case False{}:
      bn.mod.r(bn.divmod(x, y))

# a mod m (a itself for m = 0)
def BnNat.mod(a: BnNat, m: BnNat) -> BnNat:
  match a m:
    case BnNat{+x} BnNat{+y}:
      bn.mod.zero(bn.allz(y), x, y)

def bn.div.q(m: Maybe<&2, BnDivMod>) -> BnNat:
  match m:
    case None{}:
      BnNat{Nil{}}
    case Some{BnDivMod{q, r}}:
      q

# a / b rounded down (0 for b = 0)
def BnNat.div(a: BnNat, b: BnNat) -> BnNat:
  bn.div.q(BnNat.divmod(a, b))

def bn.hex.nz(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "0"
    case s:
      bn.hex(s, SNil{})

# lowercase hex, without leading zeros ("0" for zero)
def BnNat.hex(x: BnNat) -> String:
  match x:
    case BnNat{ls}:
      bn.hex.nz(bn.norm(ls))

def bn.of_hex.go(r: BnNibs) -> Maybe<&2, BnNat>:
  match r:
    case BnNibs{True{}, Nil{}}:
      None{}
    case BnNibs{True{}, ns}:
      Some{BnNat{bn.norm(bn.group(ns))}}
    case BnNibs{False{}, ns}:
      None{}

# a number from hex text (either case, at least one digit), or None
def BnNat.of_hex(s: String) -> Maybe<&2, BnNat>:
  bn.of_hex.go(bn.nibs(s, True{}, Nil{}))
