# bend-osdev-bch: decoding binary BCH codes (Massey, "Shift-Register
# Synthesis and BCH Decoding", 1969, section V):
#
#   1. the syndromes S_m0 .. S_(m0+2t-1) of the received bits
#      (syndrome.bend);
#   2. the error locator C(D) = prod (1 - X_i D), the shortest LFSR that
#      generates the syndromes, by the Berlekamp-Massey algorithm (bend-
#      osdev-rs's bm.bend; Massey's corollary to Theorem 5: when the error
#      weight is at most t, C(D) is that LFSR); refused unless L <= t;
#   3. the error locations, the positions p with C(alpha^-p) = 0, by the
#      Chien search (bend-osdev-rs's chien.bend); refused unless C has L
#      such roots among the word's positions;
#   4. the corrected word: for binary codes the error values are all 1
#      (Massey, section V: "the error locators completely describe the
#      error pattern"), so each located bit is flipped.
#
# Bits are in order, highest power first; the last bit is position 0. A
# word may be shortened: it has more than deg(g) and at most n bits. Byte
# strings are read and written through bits.bend, with the bit order a
# parameter. A policy (BchOpts): whether to check that the corrected
# word's syndromes are zero (the default).
import Base
import ../bytes/bytes.bend as B
import ../gf/gfm.bend as M
import ../rs/poly.bend as P
import ../rs/arith.bend as A
import ../rs/bm.bend as Bm
import ../rs/chien.bend as Ch
import ./code.bend as C
import ./bits.bend as T
import ./encode.bend as E
import ./syndrome.bend as S

type BchOpts is Data:
  BchOpts{verify: Bool}

def Bch.opts() -> BchOpts:
  BchOpts{True{}}

# A corrected word and how many bits were flipped
type BchFixed is Data:
  BchFixed{bits: List<&2, Bool>, count: Nat}

# Stages 2 and 3: the error positions for these syndromes, in a word of
# npos bits

def bch.dec.found(ok: Bool, +ps: List<&2, U32>) -> Result<&2, &2, E.BchError, List<&2, U32>>:
  match ok:
    case True{}:
      Done{ps}
    case False{}:
      Fail{E.BchUncorrectable{}}

def bch.dec.chien(ok: Bool, +c: C.BchCode, +lam: List<&2, U32>, +l: Nat, +npos: U32) -> Result<&2, &2, E.BchError, List<&2, U32>>:
  match ok:
    case False{}:
      Fail{E.BchUncorrectable{}}
    case True{}:
      +f = C.Bch.field(c)
      +ps = Ch.RsChien.roots(f, lam, A.RsGf.inv(f, 2), npos)
      bch.dec.found(Nat.is_eq(List.length(&2, U32, ps), l), ps)

def bch.dec.bm(+c: C.BchCode, +npos: U32, lf: Bm.RsLfsr) -> Result<&2, &2, E.BchError, List<&2, U32>>:
  match lf:
    case Bm.RsLfsr{lam, +l}:
      bch.dec.chien(Nat.is_le(l, U32.to_nat(C.Bch.t(c))), c, lam, l, npos)

def bch.dec.plan(zero: Bool, +c: C.BchCode, +synd: List<&2, U32>, +npos: U32) -> Result<&2, &2, E.BchError, List<&2, U32>>:
  match zero:
    case True{}:
      Done{Nil{}}
    case False{}:
      bch.dec.bm(c, npos, Bm.RsBm.lfsr(C.Bch.field(c), synd))

# the error positions for these syndromes; none if they are all zero
def Bch.locate(+c: C.BchCode, +synd: List<&2, U32>, +npos: U32) -> Result<&2, &2, E.BchError, List<&2, U32>>:
  bch.dec.plan(P.RsPoly.is_zero(C.Bch.field(c), synd), c, synd, npos)

# Stage 4: flipping bits

def bch.flip.one(bits: List<&2, Bool>, i: Nat) -> List<&2, Bool>:
  match bits:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match i:
        case 0n:
          Con{Bool.not(b), t}
        case 1n+k:
          Con{b, bch.flip.one(t, k)}

def bch.flip.all(ps: List<&2, U32>, +npos: Nat, bits: List<&2, Bool>) -> List<&2, Bool>:
  match ps:
    case Nil{}:
      bits
    case Con{p, t}:
      bch.flip.all(t, npos, bch.flip.one(bits, Nat.sub(Nat.sub(npos, 1n), U32.to_nat(p))))

# the bits with those at the given positions (powers of X) flipped
def Bch.flip(ps: List<&2, U32>, +bits: List<&2, Bool>) -> List<&2, Bool>:
  bch.flip.all(ps, List.length(&2, Bool, bits), bits)

# Correcting and decoding bits

def bch.cor.verify(ok: Bool, +w: List<&2, Bool>, +count: Nat) -> Result<&2, &2, E.BchError, BchFixed>:
  match ok:
    case True{}:
      Done{BchFixed{w, count}}
    case False{}:
      Fail{E.BchUncorrectable{}}

def bch.cor.check(verify: Bool, +c: C.BchCode, +w: List<&2, Bool>) -> Bool:
  match verify:
    case True{}:
      P.RsPoly.is_zero(C.Bch.field(c), S.Bch.syndromes(c, w))
    case False{}:
      True{}

def bch.cor.fin(r: Result<&2, &2, E.BchError, List<&2, U32>>, opts: BchOpts, +c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, E.BchError, BchFixed>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+ps}:
      match opts:
        case BchOpts{verify}:
          +w = Bch.flip(ps, bits)
          bch.cor.verify(bch.cor.check(verify, c, w), w, List.length(&2, U32, ps))

def bch.cor.go(ok: Bool, +opts: BchOpts, +c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, E.BchError, BchFixed>:
  match ok:
    case False{}:
      Fail{E.BchBadLength{List.length(&2, Bool, bits)}}
    case True{}:
      bch.cor.fin(Bch.locate(c, S.Bch.syndromes(c, bits), U32.from_nat(List.length(&2, Bool, bits))), opts, c, bits)

# whether a word of len bits can be decoded: deg(g) < len <= n
def Bch.length_ok(+c: C.BchCode, +len: Nat) -> Bool:
  Bool.and(Nat.is_lt(C.Bch.parity_bits(c), len), Nat.is_le(len, U32.to_nat(C.Bch.n(c))))

# the received bits corrected, under a policy
def Bch.correct_with(+opts: BchOpts, +c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, E.BchError, BchFixed>:
  bch.cor.go(Bch.length_ok(c, List.length(&2, Bool, bits)), opts, c, bits)

def Bch.correct(+c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, E.BchError, BchFixed>:
  Bch.correct_with(Bch.opts(), c, bits)

def bch.dec.msg(+c: C.BchCode, r: Result<&2, &2, E.BchError, BchFixed>) -> Result<&2, &2, E.BchError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match x:
        case BchFixed{+w, n}:
          Done{List.take(&2, Bool, w, Nat.sub(List.length(&2, Bool, w), C.Bch.parity_bits(c)))}

# the data bits of a received word (data bits then parity bits)
def Bch.decode_bits(+c: C.BchCode, +bits: List<&2, Bool>) -> Result<&2, &2, E.BchError, List<&2, Bool>>:
  bch.dec.msg(c, Bch.correct(c, bits))

# a test helper: the bit at index i (0 the first) flipped
def Bch.flip_at(bits: List<&2, Bool>, i: Nat) -> List<&2, Bool>:
  bch.flip.one(bits, i)

# Byte strings (NAND sectors): data bytes and the parity packed into bytes

def bch.enc.oct(r: Result<&2, &2, E.BchError, List<&2, Bool>>, +o: T.BchOrder, +c: C.BchCode) -> Result<&2, &2, E.BchError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+w}:
      Done{T.Bch.octets_of(o, List.drop(&2, Bool, w, Nat.sub(List.length(&2, Bool, w), C.Bch.parity_bits(c))))}

# the ECC bytes of the data: its parity bits, packed (bit order o)
def Bch.encode_with(+o: T.BchOrder, +c: C.BchCode, +data: B.Octets) -> Result<&2, &2, E.BchError, B.Octets>:
  bch.enc.oct(E.Bch.encode_bits(c, T.Bch.bits_of(o, data)), o, c)

def Bch.encode(+c: C.BchCode, +data: B.Octets) -> Result<&2, &2, E.BchError, B.Octets>:
  Bch.encode_with(T.Bch.order(), c, data)

# The corrected data and ECC bytes, and how many bits were flipped
type BchDecoded is Data:
  BchDecoded{data: B.Octets, ecc: B.Octets, count: Nat}

def bch.dec.oct(r: Result<&2, &2, E.BchError, BchFixed>, +o: T.BchOrder, +nd: Nat, +npar: Nat, ecc: B.Octets) -> Result<&2, &2, E.BchError, BchDecoded>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match x:
        case BchFixed{+w, n}:
          Done{BchDecoded{T.Bch.octets_of(o, List.take(&2, Bool, w, nd)), T.Bch.octets_of(o, List.append(&2, Bool, List.drop(&2, Bool, w, nd), List.drop(&2, Bool, T.Bch.bits_of(o, ecc), npar))), n}}

# data bytes and their ECC bytes (as Bch.encode_with makes them) corrected;
# the ECC's padding bits are kept as they were
def Bch.decode_with(+o: T.BchOrder, +c: C.BchCode, +data: B.Octets, +ecc: B.Octets) -> Result<&2, &2, E.BchError, BchDecoded>:
  +db = T.Bch.bits_of(o, data)
  +npar = C.Bch.parity_bits(c)
  bch.dec.oct(Bch.correct(c, List.append(&2, Bool, db, List.take(&2, Bool, T.Bch.bits_of(o, ecc), npar))), o, List.length(&2, Bool, db), npar, ecc)

def Bch.decode(+c: C.BchCode, +data: B.Octets, +ecc: B.Octets) -> Result<&2, &2, E.BchError, BchDecoded>:
  Bch.decode_with(T.Bch.order(), c, data, ecc)
