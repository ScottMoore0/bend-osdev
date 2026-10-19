# bend-osdev-bch, the parameters of a binary BCH code and its generator
# polynomial.
#
# A binary BCH code (Massey, "Shift-Register Synthesis and BCH Decoding",
# 1969, section V) of length n = 2^m - 1 has as generator g(X) the
# minimum-degree polynomial over GF(2) with alpha^m0, alpha^(m0+1), ...,
# alpha^(m0+2t-1) as roots, alpha a primitive element of GF(2^m) (here the
# element x, so the field polynomial must be primitive); its designed
# distance is 2t + 1, so it corrects t errors. Over GF(2) a polynomial with
# a root r also has r^2 as a root (squaring is a field automorphism that
# fixes GF(2)), so g(X) is the product of (X + alpha^e) over every e in the
# cyclotomic cosets {j, 2j, 4j, ...} (mod n) of the exponents j = m0 ..
# m0 + 2t - 1 (Shan-Yuan Ho, "BCH Codes", April 24, 2010, section 2:
# Q(x) = p(x) p3(x) ... p(2t-1)(x)).
#
# The parameters are a field (bend-osdev-gf's GfmField), t and m0, with
# named defaults: the narrow-sense codes (m0 = 1) over GF(2^13) for 512-byte
# NAND sectors, and small codes over GF(8) and GF(16).
import Base
import ../gf/gfm.bend as M
import ../rs/poly.bend as P
import ../rs/arith.bend as A

type BchCode is Data:
  BchCode{field: M.GfmField, t: U32, m0: U32}

def Bch.code(f: M.GfmField, t: U32, m0: U32) -> BchCode:
  BchCode{f, t, m0}

def Bch.field(c: BchCode) -> M.GfmField:
  match c:
    case BchCode{f, t, m0}:
      f

def Bch.t(c: BchCode) -> U32:
  match c:
    case BchCode{f, t, m0}:
      t

def Bch.m0(c: BchCode) -> U32:
  match c:
    case BchCode{f, t, m0}:
      m0

# n = 2^m - 1
def Bch.n(c: BchCode) -> U32:
  M.Gfm.mask(Bch.field(c))

# Named codes

# narrow-sense, GF(2^13) with x^13 + x^4 + x^3 + x + 1 (gf's Gfm.bch13):
# the smallest m whose codewords (8191 bits) hold a 512-byte sector (4096
# bits) and 13t parity bits, for any t up to 16
def Bch.nand(t: U32) -> BchCode:
  BchCode{M.Gfm.bch13(), t, 1}

def Bch.nand_t4() -> BchCode:
  Bch.nand(4)

def Bch.nand_t8() -> BchCode:
  Bch.nand(8)

def Bch.nand_t16() -> BchCode:
  Bch.nand(16)

# GF(8) with x^3 + x + 1: the (7,4) code (t = 1), a Hamming code
def Bch.bch7_4() -> BchCode:
  BchCode{M.GfmField{3n, 11}, 1, 1}

# GF(16) with x^4 + x + 1: the (15,7) code (t = 2) and Ho's (15,5) code
# (t = 3)
def Bch.bch15_7() -> BchCode:
  BchCode{M.Gfm.gf16(), 2, 1}

def Bch.bch15_5() -> BchCode:
  BchCode{M.Gfm.gf16(), 3, 1}

# The roots of g(X)

# whether e is in the list
def bch.memb(+e: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(U32.is_eq(e, x), bch.memb(e, t))

def bch.dbl.fix(lt: Bool, +n: U32, +d: U32) -> U32:
  match lt:
    case True{}:
      d
    case False{}:
      U32.sub(d, n)

# 2e mod n, for e < n
def bch.dbl(+n: U32, +e: U32) -> U32:
  bch.dbl.fix(U32.is_lt(U32.add(e, e), n), n, U32.add(e, e))

# j mod n, for j < 2n
def bch.mod(+j: U32, +n: U32) -> U32:
  bch.dbl.fix(U32.is_lt(j, n), n, j)

# The roots found so far: their exponents e and the elements alpha^e
type BchRoots is Data:
  BchRoots{exps: List<&2, U32>, elts: List<&2, U32>}

def bch.add_root(+e: U32, +r: U32, acc: BchRoots) -> BchRoots:
  match acc:
    case BchRoots{es, rs}:
      BchRoots{Con{e, es}, Con{r, rs}}

def bch.seen(+e: U32, acc: BchRoots) -> Bool:
  match acc:
    case BchRoots{es, rs}:
      bch.memb(e, es)

# the coset of e (with r = alpha^e) added to acc: e, 2e, 4e, ... (and r,
# r^2, r^4, ...) until one is already there (at most k steps)
def bch.coset(k: Nat, seen: Bool, +f: M.GfmField, +n: U32, +e: U32, +r: U32, +acc: BchRoots) -> BchRoots:
  match k:
    case 0n:
      acc
    case 1n+j:
      match seen:
        case True{}:
          acc
        case False{}:
          +e2 = bch.dbl(n, e)
          +acc2 = bch.add_root(e, r, acc)
          bch.coset(j, bch.seen(e2, acc2), f, n, e2, M.Gfm.mul(f, r, r), acc2)

# the cosets of m0 .. m0 + 2t - 1 (mod n); r is alpha^j
def bch.exps(k: Nat, +f: M.GfmField, +n: U32, +j: U32, +r: U32, +acc: BchRoots) -> BchRoots:
  match k:
    case 0n:
      acc
    case 1n+i:
      +e = bch.mod(j, n)
      bch.exps(i, f, n, U32.add(j, 1), M.Gfm.mul(f, r, 2), bch.coset(1n+M.Gfm.m(f), bch.seen(e, acc), f, n, e, r, acc))

def Bch.roots(+c: BchCode) -> BchRoots:
  +f = Bch.field(c)
  bch.exps(U32.to_nat(U32.add(Bch.t(c), Bch.t(c))), f, Bch.n(c), Bch.m0(c), A.RsGf.pow_nat(f, 2, U32.to_nat(Bch.m0(c))), BchRoots{Nil{}, Nil{}})

def BchRoots.exps(r: BchRoots) -> List<&2, U32>:
  match r:
    case BchRoots{es, rs}:
      es

# the exponents of g's roots
def Bch.exponents(+c: BchCode) -> List<&2, U32>:
  BchRoots.exps(Bch.roots(c))

# a polynomial over GF(2^m) whose coefficients are 0 or 1, as bits
def bch.bits(p: List<&2, U32>) -> List<&2, Bool>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{Bool.not(U32.is_eq(a, 0)), bch.bits(t)}

# g(X) over GF(2), lowest coefficient first
def bch.gen.of(+f: M.GfmField, rs: BchRoots) -> List<&2, Bool>:
  match rs:
    case BchRoots{es, elts}:
      bch.bits(P.RsPoly.from_roots(f, elts))

def Bch.generator(+c: BchCode) -> List<&2, Bool>:
  bch.gen.of(Bch.field(c), Bch.roots(c))

# deg g: the number of parity bits
def Bch.parity_bits(+c: BchCode) -> Nat:
  List.length(&2, U32, Bch.exponents(c))
