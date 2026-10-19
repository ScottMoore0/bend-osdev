# bend-osdev-bch, syndromes: S_j = r(alpha^j) for j = m0 .. m0 + 2t - 1
# (Massey, 1969, section V, equations 22 and 23), each by Horner's rule over
# the received bits, highest power first. A codeword's syndromes are zero.
import Base
import ../gf/gfm.bend as M
import ../rs/arith.bend as A
import ./code.bend as C

def bch.b(+b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# r(x) for the bits r, highest power first
def bch.syn.one(bits: List<&2, Bool>, +f: M.GfmField, +x: U32, acc: U32) -> U32:
  match bits:
    case Nil{}:
      acc
    case Con{b, t}:
      bch.syn.one(t, f, x, M.Gfm.add(f, M.Gfm.mul(f, acc, x), bch.b(b)))

# the syndromes from x = alpha^j on, k of them
def bch.syn.all(k: Nat, +f: M.GfmField, +bits: List<&2, Bool>, +x: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+i:
      Con{bch.syn.one(bits, f, x, 0), bch.syn.all(i, f, bits, M.Gfm.mul(f, x, 2))}

# S_m0 .. S_(m0+2t-1)
def Bch.syndromes(+c: C.BchCode, +bits: List<&2, Bool>) -> List<&2, U32>:
  +f = C.Bch.field(c)
  bch.syn.all(U32.to_nat(U32.add(C.Bch.t(c), C.Bch.t(c))), f, bits, A.RsGf.pow_nat(f, 2, U32.to_nat(C.Bch.m0(c))))
