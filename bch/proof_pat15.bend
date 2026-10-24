# The (15,7) code's patterns of at most two flipped bits, each corrected
# alone, and the facts about GF(16) that the syndromes' linearity needs
# (this whole file is written by gen/proof.py: do not edit it).
#
#   * For a word x of 15 bits, chk15(x) flips the bits of x at the
#     decoder's error positions for x's syndromes (Bch.locate), and ok15(x)
#     says that this is the zero word. For each pattern e with at most two
#     bits set (121 of them) ok15(e) holds: the decoder finds exactly e's
#     errors. Each is computed in a def of its own (p15_<indexes>), on
#     literals (the proof kernel has a step budget per def). q15 takes a
#     pattern given as two flips (pat15: two indexes) apart: each index is
#     tried (0 to 14, or past the end, which flips nothing), the pattern
#     rewritten into its list of bits (t15_<i>_<j>, computed), and each
#     case is one of the patterns.
#   * GF(16), whose functions read their arguments modulo 2^4: e1, e2, eid
#     and a0 split the words into their 32 bits; dist<k> is
#     (x + y) k = x k + y k for each of the syndromes' points k = 2, 4, 8
#     and 3, from the elements' low four bits (nib), each value of x's
#     tried in a def of its own (dk<k>_<x>) and each of y's in a case.
import Base
import ../gf/gfm.bend as M
import ../rs/poly.bend as P
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as S
import ./bch.bend as D

# a list of bits plus another, bit by bit (the shorter as padded with zeros)
def xl(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case Nil{} _:
      b
    case Con{x, s} Nil{}:
      Con{x, s}
    case Con{x, s} Con{y, t}:
      Con{Bool.xor(x, y), xl(s, t)}

# the word of 15 bits with the bits at indexes i and j flipped
def pat15(i: Nat, j: Nat) -> List<&2, Bool>:
  xl(D.bch.flip.one(E.bch.falses(15n), i), D.bch.flip.one(E.bch.falses(15n), j))

# the flips for x's syndromes applied to x
def chk15r(r: Result<&2, &2, E.BchError, List<&2, U32>>, +x: List<&2, Bool>) -> Result<&2, &2, E.BchError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ps}:
      Done{D.Bch.flip(ps, x)}

def chk15(+x: List<&2, Bool>) -> Result<&2, &2, E.BchError, List<&2, Bool>>:
  chk15r(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), x), 15), x)

def ok15(+x: List<&2, Bool>) -> Type:
  {chk15(x) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}

# GF(16): elt (elt u + v) = elt (u + v)
def e1(u: U32, v: U32) -> {M.Gfm.elt(M.Gfm.gf16(), U32.xor(M.Gfm.elt(M.Gfm.gf16(), u), v)) == M.Gfm.elt(M.Gfm.gf16(), U32.xor(u, v)) : U32}:
  match u v:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# elt (u + elt v) = elt (u + v)
def e2(u: U32, v: U32) -> {M.Gfm.elt(M.Gfm.gf16(), U32.xor(u, M.Gfm.elt(M.Gfm.gf16(), v))) == M.Gfm.elt(M.Gfm.gf16(), U32.xor(u, v)) : U32}:
  match u v:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def eid(u: U32) -> {M.Gfm.elt(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), u)) == M.Gfm.elt(M.Gfm.gf16(), u) : U32}:
  match u:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# 0 + y = elt y
def a0(y: U32) -> {M.Gfm.add(M.Gfm.gf16(), 0, y) == M.Gfm.elt(M.Gfm.gf16(), y) : U32}:
  match y:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# an element from its four bits
def nib(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool) -> U32:
  U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, Word.zero(28n)}}}}}

# the product reads x modulo 2^4
def mm(x: U32, +k: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), k) == M.Gfm.mul(M.Gfm.gf16(), x, k) : U32}:
  match x:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the sum reads x and y modulo 2^4
def gm(+x: U32, +y: U32) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)) == M.Gfm.add(M.Gfm.gf16(), x, y) : U32}:
  Equal.trans(U32, M.Gfm.elt(M.Gfm.gf16(), U32.xor(M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y))), M.Gfm.elt(M.Gfm.gf16(), U32.xor(x, M.Gfm.elt(M.Gfm.gf16(), y))), M.Gfm.elt(M.Gfm.gf16(), U32.xor(x, y)), e1(x, M.Gfm.elt(M.Gfm.gf16(), y)), e2(x, y))

# (x + y) 2 = x 2 + y 2: each value of x's four bits, then of y's
def dk2_0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2_15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk2(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(a0, a1, a2, a3), nib(b0, b1, b2, b3)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(a0, a1, a2, a3), 2), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 2)) : U32}:
  match a0 a1 a2 a3:
    case False{} False{} False{} False{}:
      dk2_0(b0, b1, b2, b3)
    case True{} False{} False{} False{}:
      dk2_1(b0, b1, b2, b3)
    case False{} True{} False{} False{}:
      dk2_2(b0, b1, b2, b3)
    case True{} True{} False{} False{}:
      dk2_3(b0, b1, b2, b3)
    case False{} False{} True{} False{}:
      dk2_4(b0, b1, b2, b3)
    case True{} False{} True{} False{}:
      dk2_5(b0, b1, b2, b3)
    case False{} True{} True{} False{}:
      dk2_6(b0, b1, b2, b3)
    case True{} True{} True{} False{}:
      dk2_7(b0, b1, b2, b3)
    case False{} False{} False{} True{}:
      dk2_8(b0, b1, b2, b3)
    case True{} False{} False{} True{}:
      dk2_9(b0, b1, b2, b3)
    case False{} True{} False{} True{}:
      dk2_10(b0, b1, b2, b3)
    case True{} True{} False{} True{}:
      dk2_11(b0, b1, b2, b3)
    case False{} False{} True{} True{}:
      dk2_12(b0, b1, b2, b3)
    case True{} False{} True{} True{}:
      dk2_13(b0, b1, b2, b3)
    case False{} True{} True{} True{}:
      dk2_14(b0, b1, b2, b3)
    case True{} True{} True{} True{}:
      dk2_15(b0, b1, b2, b3)

def dn2(x: U32, y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 2), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), y), 2)) : U32}:
  match x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      dk2(a0, a1, a2, a3, b0, b1, b2, b3)

def dist2(+x: U32, +y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), x, y), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 2), M.Gfm.mul(M.Gfm.gf16(), y, 2)) : U32}:
  %gm(x, y) : {M.Gfm.mul(M.Gfm.gf16(), _, 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 2), M.Gfm.mul(M.Gfm.gf16(), y, 2)) : U32}
  %mm(x, 2) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 2) == M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.mul(M.Gfm.gf16(), y, 2)) : U32}
  %mm(y, 2) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 2) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 2), _) : U32}
  dn2(x, y)

# (x + y) 4 = x 4 + y 4: each value of x's four bits, then of y's
def dk4_0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4_15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk4(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(a0, a1, a2, a3), nib(b0, b1, b2, b3)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(a0, a1, a2, a3), 4), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 4)) : U32}:
  match a0 a1 a2 a3:
    case False{} False{} False{} False{}:
      dk4_0(b0, b1, b2, b3)
    case True{} False{} False{} False{}:
      dk4_1(b0, b1, b2, b3)
    case False{} True{} False{} False{}:
      dk4_2(b0, b1, b2, b3)
    case True{} True{} False{} False{}:
      dk4_3(b0, b1, b2, b3)
    case False{} False{} True{} False{}:
      dk4_4(b0, b1, b2, b3)
    case True{} False{} True{} False{}:
      dk4_5(b0, b1, b2, b3)
    case False{} True{} True{} False{}:
      dk4_6(b0, b1, b2, b3)
    case True{} True{} True{} False{}:
      dk4_7(b0, b1, b2, b3)
    case False{} False{} False{} True{}:
      dk4_8(b0, b1, b2, b3)
    case True{} False{} False{} True{}:
      dk4_9(b0, b1, b2, b3)
    case False{} True{} False{} True{}:
      dk4_10(b0, b1, b2, b3)
    case True{} True{} False{} True{}:
      dk4_11(b0, b1, b2, b3)
    case False{} False{} True{} True{}:
      dk4_12(b0, b1, b2, b3)
    case True{} False{} True{} True{}:
      dk4_13(b0, b1, b2, b3)
    case False{} True{} True{} True{}:
      dk4_14(b0, b1, b2, b3)
    case True{} True{} True{} True{}:
      dk4_15(b0, b1, b2, b3)

def dn4(x: U32, y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 4), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), y), 4)) : U32}:
  match x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      dk4(a0, a1, a2, a3, b0, b1, b2, b3)

def dist4(+x: U32, +y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), x, y), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 4), M.Gfm.mul(M.Gfm.gf16(), y, 4)) : U32}:
  %gm(x, y) : {M.Gfm.mul(M.Gfm.gf16(), _, 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 4), M.Gfm.mul(M.Gfm.gf16(), y, 4)) : U32}
  %mm(x, 4) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 4) == M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.mul(M.Gfm.gf16(), y, 4)) : U32}
  %mm(y, 4) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 4) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 4), _) : U32}
  dn4(x, y)

# (x + y) 8 = x 8 + y 8: each value of x's four bits, then of y's
def dk8_0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8_15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk8(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(a0, a1, a2, a3), nib(b0, b1, b2, b3)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(a0, a1, a2, a3), 8), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 8)) : U32}:
  match a0 a1 a2 a3:
    case False{} False{} False{} False{}:
      dk8_0(b0, b1, b2, b3)
    case True{} False{} False{} False{}:
      dk8_1(b0, b1, b2, b3)
    case False{} True{} False{} False{}:
      dk8_2(b0, b1, b2, b3)
    case True{} True{} False{} False{}:
      dk8_3(b0, b1, b2, b3)
    case False{} False{} True{} False{}:
      dk8_4(b0, b1, b2, b3)
    case True{} False{} True{} False{}:
      dk8_5(b0, b1, b2, b3)
    case False{} True{} True{} False{}:
      dk8_6(b0, b1, b2, b3)
    case True{} True{} True{} False{}:
      dk8_7(b0, b1, b2, b3)
    case False{} False{} False{} True{}:
      dk8_8(b0, b1, b2, b3)
    case True{} False{} False{} True{}:
      dk8_9(b0, b1, b2, b3)
    case False{} True{} False{} True{}:
      dk8_10(b0, b1, b2, b3)
    case True{} True{} False{} True{}:
      dk8_11(b0, b1, b2, b3)
    case False{} False{} True{} True{}:
      dk8_12(b0, b1, b2, b3)
    case True{} False{} True{} True{}:
      dk8_13(b0, b1, b2, b3)
    case False{} True{} True{} True{}:
      dk8_14(b0, b1, b2, b3)
    case True{} True{} True{} True{}:
      dk8_15(b0, b1, b2, b3)

def dn8(x: U32, y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 8), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), y), 8)) : U32}:
  match x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      dk8(a0, a1, a2, a3, b0, b1, b2, b3)

def dist8(+x: U32, +y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), x, y), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 8), M.Gfm.mul(M.Gfm.gf16(), y, 8)) : U32}:
  %gm(x, y) : {M.Gfm.mul(M.Gfm.gf16(), _, 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 8), M.Gfm.mul(M.Gfm.gf16(), y, 8)) : U32}
  %mm(x, 8) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 8) == M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.mul(M.Gfm.gf16(), y, 8)) : U32}
  %mm(y, 8) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 8) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 8), _) : U32}
  dn8(x, y)

# (x + y) 3 = x 3 + y 3: each value of x's four bits, then of y's
def dk3_0(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_1(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_2(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_3(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_4(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_5(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_6(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_7(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, False{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_8(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, False{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_9(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, False{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_10(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, False{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_11(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, False{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_12(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, False{}, True{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_13(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, False{}, True{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_14(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(False{}, True{}, True{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3_15(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(True{}, True{}, True{}, True{}), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def dk3(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), nib(a0, a1, a2, a3), nib(b0, b1, b2, b3)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), nib(a0, a1, a2, a3), 3), M.Gfm.mul(M.Gfm.gf16(), nib(b0, b1, b2, b3), 3)) : U32}:
  match a0 a1 a2 a3:
    case False{} False{} False{} False{}:
      dk3_0(b0, b1, b2, b3)
    case True{} False{} False{} False{}:
      dk3_1(b0, b1, b2, b3)
    case False{} True{} False{} False{}:
      dk3_2(b0, b1, b2, b3)
    case True{} True{} False{} False{}:
      dk3_3(b0, b1, b2, b3)
    case False{} False{} True{} False{}:
      dk3_4(b0, b1, b2, b3)
    case True{} False{} True{} False{}:
      dk3_5(b0, b1, b2, b3)
    case False{} True{} True{} False{}:
      dk3_6(b0, b1, b2, b3)
    case True{} True{} True{} False{}:
      dk3_7(b0, b1, b2, b3)
    case False{} False{} False{} True{}:
      dk3_8(b0, b1, b2, b3)
    case True{} False{} False{} True{}:
      dk3_9(b0, b1, b2, b3)
    case False{} True{} False{} True{}:
      dk3_10(b0, b1, b2, b3)
    case True{} True{} False{} True{}:
      dk3_11(b0, b1, b2, b3)
    case False{} False{} True{} True{}:
      dk3_12(b0, b1, b2, b3)
    case True{} False{} True{} True{}:
      dk3_13(b0, b1, b2, b3)
    case False{} True{} True{} True{}:
      dk3_14(b0, b1, b2, b3)
    case True{} True{} True{} True{}:
      dk3_15(b0, b1, b2, b3)

def dn3(x: U32, y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 3), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), y), 3)) : U32}:
  match x y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      dk3(a0, a1, a2, a3, b0, b1, b2, b3)

def dist3(+x: U32, +y: U32) -> {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), x, y), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 3), M.Gfm.mul(M.Gfm.gf16(), y, 3)) : U32}:
  %gm(x, y) : {M.Gfm.mul(M.Gfm.gf16(), _, 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), x, 3), M.Gfm.mul(M.Gfm.gf16(), y, 3)) : U32}
  %mm(x, 3) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 3) == M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.mul(M.Gfm.gf16(), y, 3)) : U32}
  %mm(y, 3) : {M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), M.Gfm.elt(M.Gfm.gf16(), y)), 3) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.elt(M.Gfm.gf16(), x), 3), _) : U32}
  dn3(x, y)

# The patterns

def p15_none() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_9() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_10() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_1() -> {chk15([True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_2() -> {chk15([True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_3() -> {chk15([True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_4() -> {chk15([True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_5() -> {chk15([True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_6() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_7() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_8() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_9() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_10() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_11() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_12() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_13() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_0_14() -> {chk15([True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_2() -> {chk15([False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_3() -> {chk15([False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_4() -> {chk15([False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_5() -> {chk15([False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_6() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_7() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_8() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_9() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_10() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_11() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_12() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_13() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_1_14() -> {chk15([False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_3() -> {chk15([False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_4() -> {chk15([False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_5() -> {chk15([False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_6() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_7() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_8() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_9() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_10() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_11() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_12() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_13() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_2_14() -> {chk15([False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_4() -> {chk15([False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_5() -> {chk15([False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_6() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_7() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_8() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_9() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_10() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_11() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_12() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_13() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_3_14() -> {chk15([False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_5() -> {chk15([False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_6() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_7() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_8() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_9() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_10() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_11() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_12() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_13() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_4_14() -> {chk15([False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_6() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_7() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_8() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_9() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_10() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_5_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_7() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_8() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_9() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_10() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_6_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_8() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_9() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_10() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_7_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8_9() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8_10() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_8_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_9_10() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_9_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_9_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_9_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_9_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_10_11() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_10_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_10_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_10_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_11_12() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_11_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_11_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_12_13() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_12_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

def p15_13_14() -> {chk15([False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}]) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  {==}

# A pattern's list of bits, for each pair of indexes

def t15_0_0() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 0n) : List<&2, Bool>}:
  {==}

def t15_0_1() -> {[True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 1n) : List<&2, Bool>}:
  {==}

def t15_0_2() -> {[True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 2n) : List<&2, Bool>}:
  {==}

def t15_0_3() -> {[True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 3n) : List<&2, Bool>}:
  {==}

def t15_0_4() -> {[True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 4n) : List<&2, Bool>}:
  {==}

def t15_0_5() -> {[True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 5n) : List<&2, Bool>}:
  {==}

def t15_0_6() -> {[True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 6n) : List<&2, Bool>}:
  {==}

def t15_0_7() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 7n) : List<&2, Bool>}:
  {==}

def t15_0_8() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 8n) : List<&2, Bool>}:
  {==}

def t15_0_9() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 9n) : List<&2, Bool>}:
  {==}

def t15_0_10() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(0n, 10n) : List<&2, Bool>}:
  {==}

def t15_0_11() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(0n, 11n) : List<&2, Bool>}:
  {==}

def t15_0_12() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(0n, 12n) : List<&2, Bool>}:
  {==}

def t15_0_13() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(0n, 13n) : List<&2, Bool>}:
  {==}

def t15_0_14() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(0n, 14n) : List<&2, Bool>}:
  {==}

def t15_0_far(l: Nat) -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(0n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_1_0() -> {[True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 0n) : List<&2, Bool>}:
  {==}

def t15_1_1() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 1n) : List<&2, Bool>}:
  {==}

def t15_1_2() -> {[False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 2n) : List<&2, Bool>}:
  {==}

def t15_1_3() -> {[False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 3n) : List<&2, Bool>}:
  {==}

def t15_1_4() -> {[False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 4n) : List<&2, Bool>}:
  {==}

def t15_1_5() -> {[False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 5n) : List<&2, Bool>}:
  {==}

def t15_1_6() -> {[False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 6n) : List<&2, Bool>}:
  {==}

def t15_1_7() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 7n) : List<&2, Bool>}:
  {==}

def t15_1_8() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 8n) : List<&2, Bool>}:
  {==}

def t15_1_9() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 9n) : List<&2, Bool>}:
  {==}

def t15_1_10() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(1n, 10n) : List<&2, Bool>}:
  {==}

def t15_1_11() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(1n, 11n) : List<&2, Bool>}:
  {==}

def t15_1_12() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(1n, 12n) : List<&2, Bool>}:
  {==}

def t15_1_13() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(1n, 13n) : List<&2, Bool>}:
  {==}

def t15_1_14() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(1n, 14n) : List<&2, Bool>}:
  {==}

def t15_1_far(l: Nat) -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(1n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_2_0() -> {[True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 0n) : List<&2, Bool>}:
  {==}

def t15_2_1() -> {[False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 1n) : List<&2, Bool>}:
  {==}

def t15_2_2() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 2n) : List<&2, Bool>}:
  {==}

def t15_2_3() -> {[False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 3n) : List<&2, Bool>}:
  {==}

def t15_2_4() -> {[False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 4n) : List<&2, Bool>}:
  {==}

def t15_2_5() -> {[False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 5n) : List<&2, Bool>}:
  {==}

def t15_2_6() -> {[False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 6n) : List<&2, Bool>}:
  {==}

def t15_2_7() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 7n) : List<&2, Bool>}:
  {==}

def t15_2_8() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 8n) : List<&2, Bool>}:
  {==}

def t15_2_9() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 9n) : List<&2, Bool>}:
  {==}

def t15_2_10() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(2n, 10n) : List<&2, Bool>}:
  {==}

def t15_2_11() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(2n, 11n) : List<&2, Bool>}:
  {==}

def t15_2_12() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(2n, 12n) : List<&2, Bool>}:
  {==}

def t15_2_13() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(2n, 13n) : List<&2, Bool>}:
  {==}

def t15_2_14() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(2n, 14n) : List<&2, Bool>}:
  {==}

def t15_2_far(l: Nat) -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(2n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_3_0() -> {[True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 0n) : List<&2, Bool>}:
  {==}

def t15_3_1() -> {[False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 1n) : List<&2, Bool>}:
  {==}

def t15_3_2() -> {[False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 2n) : List<&2, Bool>}:
  {==}

def t15_3_3() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 3n) : List<&2, Bool>}:
  {==}

def t15_3_4() -> {[False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 4n) : List<&2, Bool>}:
  {==}

def t15_3_5() -> {[False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 5n) : List<&2, Bool>}:
  {==}

def t15_3_6() -> {[False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 6n) : List<&2, Bool>}:
  {==}

def t15_3_7() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 7n) : List<&2, Bool>}:
  {==}

def t15_3_8() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 8n) : List<&2, Bool>}:
  {==}

def t15_3_9() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 9n) : List<&2, Bool>}:
  {==}

def t15_3_10() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(3n, 10n) : List<&2, Bool>}:
  {==}

def t15_3_11() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(3n, 11n) : List<&2, Bool>}:
  {==}

def t15_3_12() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(3n, 12n) : List<&2, Bool>}:
  {==}

def t15_3_13() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(3n, 13n) : List<&2, Bool>}:
  {==}

def t15_3_14() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(3n, 14n) : List<&2, Bool>}:
  {==}

def t15_3_far(l: Nat) -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(3n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_4_0() -> {[True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 0n) : List<&2, Bool>}:
  {==}

def t15_4_1() -> {[False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 1n) : List<&2, Bool>}:
  {==}

def t15_4_2() -> {[False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 2n) : List<&2, Bool>}:
  {==}

def t15_4_3() -> {[False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 3n) : List<&2, Bool>}:
  {==}

def t15_4_4() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 4n) : List<&2, Bool>}:
  {==}

def t15_4_5() -> {[False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 5n) : List<&2, Bool>}:
  {==}

def t15_4_6() -> {[False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 6n) : List<&2, Bool>}:
  {==}

def t15_4_7() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 7n) : List<&2, Bool>}:
  {==}

def t15_4_8() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 8n) : List<&2, Bool>}:
  {==}

def t15_4_9() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 9n) : List<&2, Bool>}:
  {==}

def t15_4_10() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(4n, 10n) : List<&2, Bool>}:
  {==}

def t15_4_11() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(4n, 11n) : List<&2, Bool>}:
  {==}

def t15_4_12() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(4n, 12n) : List<&2, Bool>}:
  {==}

def t15_4_13() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(4n, 13n) : List<&2, Bool>}:
  {==}

def t15_4_14() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(4n, 14n) : List<&2, Bool>}:
  {==}

def t15_4_far(l: Nat) -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(4n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_5_0() -> {[True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 0n) : List<&2, Bool>}:
  {==}

def t15_5_1() -> {[False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 1n) : List<&2, Bool>}:
  {==}

def t15_5_2() -> {[False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 2n) : List<&2, Bool>}:
  {==}

def t15_5_3() -> {[False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 3n) : List<&2, Bool>}:
  {==}

def t15_5_4() -> {[False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 4n) : List<&2, Bool>}:
  {==}

def t15_5_5() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 5n) : List<&2, Bool>}:
  {==}

def t15_5_6() -> {[False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 6n) : List<&2, Bool>}:
  {==}

def t15_5_7() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 7n) : List<&2, Bool>}:
  {==}

def t15_5_8() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 8n) : List<&2, Bool>}:
  {==}

def t15_5_9() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 9n) : List<&2, Bool>}:
  {==}

def t15_5_10() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(5n, 10n) : List<&2, Bool>}:
  {==}

def t15_5_11() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(5n, 11n) : List<&2, Bool>}:
  {==}

def t15_5_12() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(5n, 12n) : List<&2, Bool>}:
  {==}

def t15_5_13() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(5n, 13n) : List<&2, Bool>}:
  {==}

def t15_5_14() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(5n, 14n) : List<&2, Bool>}:
  {==}

def t15_5_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(5n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_6_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 0n) : List<&2, Bool>}:
  {==}

def t15_6_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 1n) : List<&2, Bool>}:
  {==}

def t15_6_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 2n) : List<&2, Bool>}:
  {==}

def t15_6_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 3n) : List<&2, Bool>}:
  {==}

def t15_6_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 4n) : List<&2, Bool>}:
  {==}

def t15_6_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 5n) : List<&2, Bool>}:
  {==}

def t15_6_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 6n) : List<&2, Bool>}:
  {==}

def t15_6_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 7n) : List<&2, Bool>}:
  {==}

def t15_6_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 8n) : List<&2, Bool>}:
  {==}

def t15_6_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 9n) : List<&2, Bool>}:
  {==}

def t15_6_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(6n, 10n) : List<&2, Bool>}:
  {==}

def t15_6_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(6n, 11n) : List<&2, Bool>}:
  {==}

def t15_6_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(6n, 12n) : List<&2, Bool>}:
  {==}

def t15_6_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(6n, 13n) : List<&2, Bool>}:
  {==}

def t15_6_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(6n, 14n) : List<&2, Bool>}:
  {==}

def t15_6_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(6n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_7_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 0n) : List<&2, Bool>}:
  {==}

def t15_7_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 1n) : List<&2, Bool>}:
  {==}

def t15_7_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 2n) : List<&2, Bool>}:
  {==}

def t15_7_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 3n) : List<&2, Bool>}:
  {==}

def t15_7_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 4n) : List<&2, Bool>}:
  {==}

def t15_7_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 5n) : List<&2, Bool>}:
  {==}

def t15_7_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 6n) : List<&2, Bool>}:
  {==}

def t15_7_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 7n) : List<&2, Bool>}:
  {==}

def t15_7_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 8n) : List<&2, Bool>}:
  {==}

def t15_7_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 9n) : List<&2, Bool>}:
  {==}

def t15_7_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(7n, 10n) : List<&2, Bool>}:
  {==}

def t15_7_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(7n, 11n) : List<&2, Bool>}:
  {==}

def t15_7_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(7n, 12n) : List<&2, Bool>}:
  {==}

def t15_7_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(7n, 13n) : List<&2, Bool>}:
  {==}

def t15_7_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(7n, 14n) : List<&2, Bool>}:
  {==}

def t15_7_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(7n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_8_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 0n) : List<&2, Bool>}:
  {==}

def t15_8_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 1n) : List<&2, Bool>}:
  {==}

def t15_8_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 2n) : List<&2, Bool>}:
  {==}

def t15_8_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 3n) : List<&2, Bool>}:
  {==}

def t15_8_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 4n) : List<&2, Bool>}:
  {==}

def t15_8_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 5n) : List<&2, Bool>}:
  {==}

def t15_8_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 6n) : List<&2, Bool>}:
  {==}

def t15_8_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 7n) : List<&2, Bool>}:
  {==}

def t15_8_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 8n) : List<&2, Bool>}:
  {==}

def t15_8_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 9n) : List<&2, Bool>}:
  {==}

def t15_8_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(8n, 10n) : List<&2, Bool>}:
  {==}

def t15_8_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(8n, 11n) : List<&2, Bool>}:
  {==}

def t15_8_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(8n, 12n) : List<&2, Bool>}:
  {==}

def t15_8_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(8n, 13n) : List<&2, Bool>}:
  {==}

def t15_8_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(8n, 14n) : List<&2, Bool>}:
  {==}

def t15_8_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(8n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_9_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 0n) : List<&2, Bool>}:
  {==}

def t15_9_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 1n) : List<&2, Bool>}:
  {==}

def t15_9_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 2n) : List<&2, Bool>}:
  {==}

def t15_9_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 3n) : List<&2, Bool>}:
  {==}

def t15_9_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 4n) : List<&2, Bool>}:
  {==}

def t15_9_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 5n) : List<&2, Bool>}:
  {==}

def t15_9_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 6n) : List<&2, Bool>}:
  {==}

def t15_9_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 7n) : List<&2, Bool>}:
  {==}

def t15_9_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 8n) : List<&2, Bool>}:
  {==}

def t15_9_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 9n) : List<&2, Bool>}:
  {==}

def t15_9_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}] == pat15(9n, 10n) : List<&2, Bool>}:
  {==}

def t15_9_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}] == pat15(9n, 11n) : List<&2, Bool>}:
  {==}

def t15_9_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}] == pat15(9n, 12n) : List<&2, Bool>}:
  {==}

def t15_9_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}] == pat15(9n, 13n) : List<&2, Bool>}:
  {==}

def t15_9_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}] == pat15(9n, 14n) : List<&2, Bool>}:
  {==}

def t15_9_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(9n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_10_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 0n) : List<&2, Bool>}:
  {==}

def t15_10_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 1n) : List<&2, Bool>}:
  {==}

def t15_10_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 2n) : List<&2, Bool>}:
  {==}

def t15_10_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 3n) : List<&2, Bool>}:
  {==}

def t15_10_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 4n) : List<&2, Bool>}:
  {==}

def t15_10_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 5n) : List<&2, Bool>}:
  {==}

def t15_10_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 6n) : List<&2, Bool>}:
  {==}

def t15_10_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 7n) : List<&2, Bool>}:
  {==}

def t15_10_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 8n) : List<&2, Bool>}:
  {==}

def t15_10_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 9n) : List<&2, Bool>}:
  {==}

def t15_10_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(10n, 10n) : List<&2, Bool>}:
  {==}

def t15_10_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}] == pat15(10n, 11n) : List<&2, Bool>}:
  {==}

def t15_10_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}] == pat15(10n, 12n) : List<&2, Bool>}:
  {==}

def t15_10_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}] == pat15(10n, 13n) : List<&2, Bool>}:
  {==}

def t15_10_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}] == pat15(10n, 14n) : List<&2, Bool>}:
  {==}

def t15_10_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(10n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_11_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 0n) : List<&2, Bool>}:
  {==}

def t15_11_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 1n) : List<&2, Bool>}:
  {==}

def t15_11_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 2n) : List<&2, Bool>}:
  {==}

def t15_11_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 3n) : List<&2, Bool>}:
  {==}

def t15_11_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 4n) : List<&2, Bool>}:
  {==}

def t15_11_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 5n) : List<&2, Bool>}:
  {==}

def t15_11_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 6n) : List<&2, Bool>}:
  {==}

def t15_11_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 7n) : List<&2, Bool>}:
  {==}

def t15_11_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 8n) : List<&2, Bool>}:
  {==}

def t15_11_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 9n) : List<&2, Bool>}:
  {==}

def t15_11_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}, False{}] == pat15(11n, 10n) : List<&2, Bool>}:
  {==}

def t15_11_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(11n, 11n) : List<&2, Bool>}:
  {==}

def t15_11_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}] == pat15(11n, 12n) : List<&2, Bool>}:
  {==}

def t15_11_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}] == pat15(11n, 13n) : List<&2, Bool>}:
  {==}

def t15_11_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}] == pat15(11n, 14n) : List<&2, Bool>}:
  {==}

def t15_11_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(11n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_12_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 0n) : List<&2, Bool>}:
  {==}

def t15_12_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 1n) : List<&2, Bool>}:
  {==}

def t15_12_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 2n) : List<&2, Bool>}:
  {==}

def t15_12_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 3n) : List<&2, Bool>}:
  {==}

def t15_12_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 4n) : List<&2, Bool>}:
  {==}

def t15_12_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 5n) : List<&2, Bool>}:
  {==}

def t15_12_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 6n) : List<&2, Bool>}:
  {==}

def t15_12_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 7n) : List<&2, Bool>}:
  {==}

def t15_12_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 8n) : List<&2, Bool>}:
  {==}

def t15_12_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 9n) : List<&2, Bool>}:
  {==}

def t15_12_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}] == pat15(12n, 10n) : List<&2, Bool>}:
  {==}

def t15_12_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}, False{}] == pat15(12n, 11n) : List<&2, Bool>}:
  {==}

def t15_12_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(12n, 12n) : List<&2, Bool>}:
  {==}

def t15_12_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}] == pat15(12n, 13n) : List<&2, Bool>}:
  {==}

def t15_12_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}] == pat15(12n, 14n) : List<&2, Bool>}:
  {==}

def t15_12_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(12n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_13_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 0n) : List<&2, Bool>}:
  {==}

def t15_13_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 1n) : List<&2, Bool>}:
  {==}

def t15_13_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 2n) : List<&2, Bool>}:
  {==}

def t15_13_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 3n) : List<&2, Bool>}:
  {==}

def t15_13_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 4n) : List<&2, Bool>}:
  {==}

def t15_13_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 5n) : List<&2, Bool>}:
  {==}

def t15_13_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 6n) : List<&2, Bool>}:
  {==}

def t15_13_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 7n) : List<&2, Bool>}:
  {==}

def t15_13_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 8n) : List<&2, Bool>}:
  {==}

def t15_13_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 9n) : List<&2, Bool>}:
  {==}

def t15_13_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}, False{}] == pat15(13n, 10n) : List<&2, Bool>}:
  {==}

def t15_13_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}, False{}] == pat15(13n, 11n) : List<&2, Bool>}:
  {==}

def t15_13_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}, False{}] == pat15(13n, 12n) : List<&2, Bool>}:
  {==}

def t15_13_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(13n, 13n) : List<&2, Bool>}:
  {==}

def t15_13_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}] == pat15(13n, 14n) : List<&2, Bool>}:
  {==}

def t15_13_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(13n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_14_0() -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 0n) : List<&2, Bool>}:
  {==}

def t15_14_1() -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 1n) : List<&2, Bool>}:
  {==}

def t15_14_2() -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 2n) : List<&2, Bool>}:
  {==}

def t15_14_3() -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 3n) : List<&2, Bool>}:
  {==}

def t15_14_4() -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 4n) : List<&2, Bool>}:
  {==}

def t15_14_5() -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 5n) : List<&2, Bool>}:
  {==}

def t15_14_6() -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 6n) : List<&2, Bool>}:
  {==}

def t15_14_7() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 7n) : List<&2, Bool>}:
  {==}

def t15_14_8() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 8n) : List<&2, Bool>}:
  {==}

def t15_14_9() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 9n) : List<&2, Bool>}:
  {==}

def t15_14_10() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, True{}] == pat15(14n, 10n) : List<&2, Bool>}:
  {==}

def t15_14_11() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, True{}] == pat15(14n, 11n) : List<&2, Bool>}:
  {==}

def t15_14_12() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, True{}] == pat15(14n, 12n) : List<&2, Bool>}:
  {==}

def t15_14_13() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, True{}] == pat15(14n, 13n) : List<&2, Bool>}:
  {==}

def t15_14_14() -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(14n, 14n) : List<&2, Bool>}:
  {==}

def t15_14_far(l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(14n, 15n+l) : List<&2, Bool>}:
  {==}

def t15_far_0(k: Nat) -> {[True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 0n) : List<&2, Bool>}:
  {==}

def t15_far_1(k: Nat) -> {[False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 1n) : List<&2, Bool>}:
  {==}

def t15_far_2(k: Nat) -> {[False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 2n) : List<&2, Bool>}:
  {==}

def t15_far_3(k: Nat) -> {[False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 3n) : List<&2, Bool>}:
  {==}

def t15_far_4(k: Nat) -> {[False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 4n) : List<&2, Bool>}:
  {==}

def t15_far_5(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 5n) : List<&2, Bool>}:
  {==}

def t15_far_6(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 6n) : List<&2, Bool>}:
  {==}

def t15_far_7(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 7n) : List<&2, Bool>}:
  {==}

def t15_far_8(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 8n) : List<&2, Bool>}:
  {==}

def t15_far_9(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 9n) : List<&2, Bool>}:
  {==}

def t15_far_10(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 10n) : List<&2, Bool>}:
  {==}

def t15_far_11(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}] == pat15(15n+k, 11n) : List<&2, Bool>}:
  {==}

def t15_far_12(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}, False{}] == pat15(15n+k, 12n) : List<&2, Bool>}:
  {==}

def t15_far_13(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}, False{}] == pat15(15n+k, 13n) : List<&2, Bool>}:
  {==}

def t15_far_14(k: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] == pat15(15n+k, 14n) : List<&2, Bool>}:
  {==}

def t15_far_far(k: Nat, l: Nat) -> {[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] == pat15(15n+k, 15n+l) : List<&2, Bool>}:
  {==}

# The indexes

def q15_0(j: Nat) -> ok15(pat15(0n, j)):
  match j:
    case 0n:
      %t15_0_0() : ok15(_)
      p15_none()
    case 1n:
      %t15_0_1() : ok15(_)
      p15_0_1()
    case 2n:
      %t15_0_2() : ok15(_)
      p15_0_2()
    case 3n:
      %t15_0_3() : ok15(_)
      p15_0_3()
    case 4n:
      %t15_0_4() : ok15(_)
      p15_0_4()
    case 5n:
      %t15_0_5() : ok15(_)
      p15_0_5()
    case 6n:
      %t15_0_6() : ok15(_)
      p15_0_6()
    case 7n:
      %t15_0_7() : ok15(_)
      p15_0_7()
    case 8n:
      %t15_0_8() : ok15(_)
      p15_0_8()
    case 9n:
      %t15_0_9() : ok15(_)
      p15_0_9()
    case 10n:
      %t15_0_10() : ok15(_)
      p15_0_10()
    case 11n:
      %t15_0_11() : ok15(_)
      p15_0_11()
    case 12n:
      %t15_0_12() : ok15(_)
      p15_0_12()
    case 13n:
      %t15_0_13() : ok15(_)
      p15_0_13()
    case 14n:
      %t15_0_14() : ok15(_)
      p15_0_14()
    case 15n+l:
      %t15_0_far(l) : ok15(_)
      p15_0()

def q15_1(j: Nat) -> ok15(pat15(1n, j)):
  match j:
    case 0n:
      %t15_1_0() : ok15(_)
      p15_0_1()
    case 1n:
      %t15_1_1() : ok15(_)
      p15_none()
    case 2n:
      %t15_1_2() : ok15(_)
      p15_1_2()
    case 3n:
      %t15_1_3() : ok15(_)
      p15_1_3()
    case 4n:
      %t15_1_4() : ok15(_)
      p15_1_4()
    case 5n:
      %t15_1_5() : ok15(_)
      p15_1_5()
    case 6n:
      %t15_1_6() : ok15(_)
      p15_1_6()
    case 7n:
      %t15_1_7() : ok15(_)
      p15_1_7()
    case 8n:
      %t15_1_8() : ok15(_)
      p15_1_8()
    case 9n:
      %t15_1_9() : ok15(_)
      p15_1_9()
    case 10n:
      %t15_1_10() : ok15(_)
      p15_1_10()
    case 11n:
      %t15_1_11() : ok15(_)
      p15_1_11()
    case 12n:
      %t15_1_12() : ok15(_)
      p15_1_12()
    case 13n:
      %t15_1_13() : ok15(_)
      p15_1_13()
    case 14n:
      %t15_1_14() : ok15(_)
      p15_1_14()
    case 15n+l:
      %t15_1_far(l) : ok15(_)
      p15_1()

def q15_2(j: Nat) -> ok15(pat15(2n, j)):
  match j:
    case 0n:
      %t15_2_0() : ok15(_)
      p15_0_2()
    case 1n:
      %t15_2_1() : ok15(_)
      p15_1_2()
    case 2n:
      %t15_2_2() : ok15(_)
      p15_none()
    case 3n:
      %t15_2_3() : ok15(_)
      p15_2_3()
    case 4n:
      %t15_2_4() : ok15(_)
      p15_2_4()
    case 5n:
      %t15_2_5() : ok15(_)
      p15_2_5()
    case 6n:
      %t15_2_6() : ok15(_)
      p15_2_6()
    case 7n:
      %t15_2_7() : ok15(_)
      p15_2_7()
    case 8n:
      %t15_2_8() : ok15(_)
      p15_2_8()
    case 9n:
      %t15_2_9() : ok15(_)
      p15_2_9()
    case 10n:
      %t15_2_10() : ok15(_)
      p15_2_10()
    case 11n:
      %t15_2_11() : ok15(_)
      p15_2_11()
    case 12n:
      %t15_2_12() : ok15(_)
      p15_2_12()
    case 13n:
      %t15_2_13() : ok15(_)
      p15_2_13()
    case 14n:
      %t15_2_14() : ok15(_)
      p15_2_14()
    case 15n+l:
      %t15_2_far(l) : ok15(_)
      p15_2()

def q15_3(j: Nat) -> ok15(pat15(3n, j)):
  match j:
    case 0n:
      %t15_3_0() : ok15(_)
      p15_0_3()
    case 1n:
      %t15_3_1() : ok15(_)
      p15_1_3()
    case 2n:
      %t15_3_2() : ok15(_)
      p15_2_3()
    case 3n:
      %t15_3_3() : ok15(_)
      p15_none()
    case 4n:
      %t15_3_4() : ok15(_)
      p15_3_4()
    case 5n:
      %t15_3_5() : ok15(_)
      p15_3_5()
    case 6n:
      %t15_3_6() : ok15(_)
      p15_3_6()
    case 7n:
      %t15_3_7() : ok15(_)
      p15_3_7()
    case 8n:
      %t15_3_8() : ok15(_)
      p15_3_8()
    case 9n:
      %t15_3_9() : ok15(_)
      p15_3_9()
    case 10n:
      %t15_3_10() : ok15(_)
      p15_3_10()
    case 11n:
      %t15_3_11() : ok15(_)
      p15_3_11()
    case 12n:
      %t15_3_12() : ok15(_)
      p15_3_12()
    case 13n:
      %t15_3_13() : ok15(_)
      p15_3_13()
    case 14n:
      %t15_3_14() : ok15(_)
      p15_3_14()
    case 15n+l:
      %t15_3_far(l) : ok15(_)
      p15_3()

def q15_4(j: Nat) -> ok15(pat15(4n, j)):
  match j:
    case 0n:
      %t15_4_0() : ok15(_)
      p15_0_4()
    case 1n:
      %t15_4_1() : ok15(_)
      p15_1_4()
    case 2n:
      %t15_4_2() : ok15(_)
      p15_2_4()
    case 3n:
      %t15_4_3() : ok15(_)
      p15_3_4()
    case 4n:
      %t15_4_4() : ok15(_)
      p15_none()
    case 5n:
      %t15_4_5() : ok15(_)
      p15_4_5()
    case 6n:
      %t15_4_6() : ok15(_)
      p15_4_6()
    case 7n:
      %t15_4_7() : ok15(_)
      p15_4_7()
    case 8n:
      %t15_4_8() : ok15(_)
      p15_4_8()
    case 9n:
      %t15_4_9() : ok15(_)
      p15_4_9()
    case 10n:
      %t15_4_10() : ok15(_)
      p15_4_10()
    case 11n:
      %t15_4_11() : ok15(_)
      p15_4_11()
    case 12n:
      %t15_4_12() : ok15(_)
      p15_4_12()
    case 13n:
      %t15_4_13() : ok15(_)
      p15_4_13()
    case 14n:
      %t15_4_14() : ok15(_)
      p15_4_14()
    case 15n+l:
      %t15_4_far(l) : ok15(_)
      p15_4()

def q15_5(j: Nat) -> ok15(pat15(5n, j)):
  match j:
    case 0n:
      %t15_5_0() : ok15(_)
      p15_0_5()
    case 1n:
      %t15_5_1() : ok15(_)
      p15_1_5()
    case 2n:
      %t15_5_2() : ok15(_)
      p15_2_5()
    case 3n:
      %t15_5_3() : ok15(_)
      p15_3_5()
    case 4n:
      %t15_5_4() : ok15(_)
      p15_4_5()
    case 5n:
      %t15_5_5() : ok15(_)
      p15_none()
    case 6n:
      %t15_5_6() : ok15(_)
      p15_5_6()
    case 7n:
      %t15_5_7() : ok15(_)
      p15_5_7()
    case 8n:
      %t15_5_8() : ok15(_)
      p15_5_8()
    case 9n:
      %t15_5_9() : ok15(_)
      p15_5_9()
    case 10n:
      %t15_5_10() : ok15(_)
      p15_5_10()
    case 11n:
      %t15_5_11() : ok15(_)
      p15_5_11()
    case 12n:
      %t15_5_12() : ok15(_)
      p15_5_12()
    case 13n:
      %t15_5_13() : ok15(_)
      p15_5_13()
    case 14n:
      %t15_5_14() : ok15(_)
      p15_5_14()
    case 15n+l:
      %t15_5_far(l) : ok15(_)
      p15_5()

def q15_6(j: Nat) -> ok15(pat15(6n, j)):
  match j:
    case 0n:
      %t15_6_0() : ok15(_)
      p15_0_6()
    case 1n:
      %t15_6_1() : ok15(_)
      p15_1_6()
    case 2n:
      %t15_6_2() : ok15(_)
      p15_2_6()
    case 3n:
      %t15_6_3() : ok15(_)
      p15_3_6()
    case 4n:
      %t15_6_4() : ok15(_)
      p15_4_6()
    case 5n:
      %t15_6_5() : ok15(_)
      p15_5_6()
    case 6n:
      %t15_6_6() : ok15(_)
      p15_none()
    case 7n:
      %t15_6_7() : ok15(_)
      p15_6_7()
    case 8n:
      %t15_6_8() : ok15(_)
      p15_6_8()
    case 9n:
      %t15_6_9() : ok15(_)
      p15_6_9()
    case 10n:
      %t15_6_10() : ok15(_)
      p15_6_10()
    case 11n:
      %t15_6_11() : ok15(_)
      p15_6_11()
    case 12n:
      %t15_6_12() : ok15(_)
      p15_6_12()
    case 13n:
      %t15_6_13() : ok15(_)
      p15_6_13()
    case 14n:
      %t15_6_14() : ok15(_)
      p15_6_14()
    case 15n+l:
      %t15_6_far(l) : ok15(_)
      p15_6()

def q15_7(j: Nat) -> ok15(pat15(7n, j)):
  match j:
    case 0n:
      %t15_7_0() : ok15(_)
      p15_0_7()
    case 1n:
      %t15_7_1() : ok15(_)
      p15_1_7()
    case 2n:
      %t15_7_2() : ok15(_)
      p15_2_7()
    case 3n:
      %t15_7_3() : ok15(_)
      p15_3_7()
    case 4n:
      %t15_7_4() : ok15(_)
      p15_4_7()
    case 5n:
      %t15_7_5() : ok15(_)
      p15_5_7()
    case 6n:
      %t15_7_6() : ok15(_)
      p15_6_7()
    case 7n:
      %t15_7_7() : ok15(_)
      p15_none()
    case 8n:
      %t15_7_8() : ok15(_)
      p15_7_8()
    case 9n:
      %t15_7_9() : ok15(_)
      p15_7_9()
    case 10n:
      %t15_7_10() : ok15(_)
      p15_7_10()
    case 11n:
      %t15_7_11() : ok15(_)
      p15_7_11()
    case 12n:
      %t15_7_12() : ok15(_)
      p15_7_12()
    case 13n:
      %t15_7_13() : ok15(_)
      p15_7_13()
    case 14n:
      %t15_7_14() : ok15(_)
      p15_7_14()
    case 15n+l:
      %t15_7_far(l) : ok15(_)
      p15_7()

def q15_8(j: Nat) -> ok15(pat15(8n, j)):
  match j:
    case 0n:
      %t15_8_0() : ok15(_)
      p15_0_8()
    case 1n:
      %t15_8_1() : ok15(_)
      p15_1_8()
    case 2n:
      %t15_8_2() : ok15(_)
      p15_2_8()
    case 3n:
      %t15_8_3() : ok15(_)
      p15_3_8()
    case 4n:
      %t15_8_4() : ok15(_)
      p15_4_8()
    case 5n:
      %t15_8_5() : ok15(_)
      p15_5_8()
    case 6n:
      %t15_8_6() : ok15(_)
      p15_6_8()
    case 7n:
      %t15_8_7() : ok15(_)
      p15_7_8()
    case 8n:
      %t15_8_8() : ok15(_)
      p15_none()
    case 9n:
      %t15_8_9() : ok15(_)
      p15_8_9()
    case 10n:
      %t15_8_10() : ok15(_)
      p15_8_10()
    case 11n:
      %t15_8_11() : ok15(_)
      p15_8_11()
    case 12n:
      %t15_8_12() : ok15(_)
      p15_8_12()
    case 13n:
      %t15_8_13() : ok15(_)
      p15_8_13()
    case 14n:
      %t15_8_14() : ok15(_)
      p15_8_14()
    case 15n+l:
      %t15_8_far(l) : ok15(_)
      p15_8()

def q15_9(j: Nat) -> ok15(pat15(9n, j)):
  match j:
    case 0n:
      %t15_9_0() : ok15(_)
      p15_0_9()
    case 1n:
      %t15_9_1() : ok15(_)
      p15_1_9()
    case 2n:
      %t15_9_2() : ok15(_)
      p15_2_9()
    case 3n:
      %t15_9_3() : ok15(_)
      p15_3_9()
    case 4n:
      %t15_9_4() : ok15(_)
      p15_4_9()
    case 5n:
      %t15_9_5() : ok15(_)
      p15_5_9()
    case 6n:
      %t15_9_6() : ok15(_)
      p15_6_9()
    case 7n:
      %t15_9_7() : ok15(_)
      p15_7_9()
    case 8n:
      %t15_9_8() : ok15(_)
      p15_8_9()
    case 9n:
      %t15_9_9() : ok15(_)
      p15_none()
    case 10n:
      %t15_9_10() : ok15(_)
      p15_9_10()
    case 11n:
      %t15_9_11() : ok15(_)
      p15_9_11()
    case 12n:
      %t15_9_12() : ok15(_)
      p15_9_12()
    case 13n:
      %t15_9_13() : ok15(_)
      p15_9_13()
    case 14n:
      %t15_9_14() : ok15(_)
      p15_9_14()
    case 15n+l:
      %t15_9_far(l) : ok15(_)
      p15_9()

def q15_10(j: Nat) -> ok15(pat15(10n, j)):
  match j:
    case 0n:
      %t15_10_0() : ok15(_)
      p15_0_10()
    case 1n:
      %t15_10_1() : ok15(_)
      p15_1_10()
    case 2n:
      %t15_10_2() : ok15(_)
      p15_2_10()
    case 3n:
      %t15_10_3() : ok15(_)
      p15_3_10()
    case 4n:
      %t15_10_4() : ok15(_)
      p15_4_10()
    case 5n:
      %t15_10_5() : ok15(_)
      p15_5_10()
    case 6n:
      %t15_10_6() : ok15(_)
      p15_6_10()
    case 7n:
      %t15_10_7() : ok15(_)
      p15_7_10()
    case 8n:
      %t15_10_8() : ok15(_)
      p15_8_10()
    case 9n:
      %t15_10_9() : ok15(_)
      p15_9_10()
    case 10n:
      %t15_10_10() : ok15(_)
      p15_none()
    case 11n:
      %t15_10_11() : ok15(_)
      p15_10_11()
    case 12n:
      %t15_10_12() : ok15(_)
      p15_10_12()
    case 13n:
      %t15_10_13() : ok15(_)
      p15_10_13()
    case 14n:
      %t15_10_14() : ok15(_)
      p15_10_14()
    case 15n+l:
      %t15_10_far(l) : ok15(_)
      p15_10()

def q15_11(j: Nat) -> ok15(pat15(11n, j)):
  match j:
    case 0n:
      %t15_11_0() : ok15(_)
      p15_0_11()
    case 1n:
      %t15_11_1() : ok15(_)
      p15_1_11()
    case 2n:
      %t15_11_2() : ok15(_)
      p15_2_11()
    case 3n:
      %t15_11_3() : ok15(_)
      p15_3_11()
    case 4n:
      %t15_11_4() : ok15(_)
      p15_4_11()
    case 5n:
      %t15_11_5() : ok15(_)
      p15_5_11()
    case 6n:
      %t15_11_6() : ok15(_)
      p15_6_11()
    case 7n:
      %t15_11_7() : ok15(_)
      p15_7_11()
    case 8n:
      %t15_11_8() : ok15(_)
      p15_8_11()
    case 9n:
      %t15_11_9() : ok15(_)
      p15_9_11()
    case 10n:
      %t15_11_10() : ok15(_)
      p15_10_11()
    case 11n:
      %t15_11_11() : ok15(_)
      p15_none()
    case 12n:
      %t15_11_12() : ok15(_)
      p15_11_12()
    case 13n:
      %t15_11_13() : ok15(_)
      p15_11_13()
    case 14n:
      %t15_11_14() : ok15(_)
      p15_11_14()
    case 15n+l:
      %t15_11_far(l) : ok15(_)
      p15_11()

def q15_12(j: Nat) -> ok15(pat15(12n, j)):
  match j:
    case 0n:
      %t15_12_0() : ok15(_)
      p15_0_12()
    case 1n:
      %t15_12_1() : ok15(_)
      p15_1_12()
    case 2n:
      %t15_12_2() : ok15(_)
      p15_2_12()
    case 3n:
      %t15_12_3() : ok15(_)
      p15_3_12()
    case 4n:
      %t15_12_4() : ok15(_)
      p15_4_12()
    case 5n:
      %t15_12_5() : ok15(_)
      p15_5_12()
    case 6n:
      %t15_12_6() : ok15(_)
      p15_6_12()
    case 7n:
      %t15_12_7() : ok15(_)
      p15_7_12()
    case 8n:
      %t15_12_8() : ok15(_)
      p15_8_12()
    case 9n:
      %t15_12_9() : ok15(_)
      p15_9_12()
    case 10n:
      %t15_12_10() : ok15(_)
      p15_10_12()
    case 11n:
      %t15_12_11() : ok15(_)
      p15_11_12()
    case 12n:
      %t15_12_12() : ok15(_)
      p15_none()
    case 13n:
      %t15_12_13() : ok15(_)
      p15_12_13()
    case 14n:
      %t15_12_14() : ok15(_)
      p15_12_14()
    case 15n+l:
      %t15_12_far(l) : ok15(_)
      p15_12()

def q15_13(j: Nat) -> ok15(pat15(13n, j)):
  match j:
    case 0n:
      %t15_13_0() : ok15(_)
      p15_0_13()
    case 1n:
      %t15_13_1() : ok15(_)
      p15_1_13()
    case 2n:
      %t15_13_2() : ok15(_)
      p15_2_13()
    case 3n:
      %t15_13_3() : ok15(_)
      p15_3_13()
    case 4n:
      %t15_13_4() : ok15(_)
      p15_4_13()
    case 5n:
      %t15_13_5() : ok15(_)
      p15_5_13()
    case 6n:
      %t15_13_6() : ok15(_)
      p15_6_13()
    case 7n:
      %t15_13_7() : ok15(_)
      p15_7_13()
    case 8n:
      %t15_13_8() : ok15(_)
      p15_8_13()
    case 9n:
      %t15_13_9() : ok15(_)
      p15_9_13()
    case 10n:
      %t15_13_10() : ok15(_)
      p15_10_13()
    case 11n:
      %t15_13_11() : ok15(_)
      p15_11_13()
    case 12n:
      %t15_13_12() : ok15(_)
      p15_12_13()
    case 13n:
      %t15_13_13() : ok15(_)
      p15_none()
    case 14n:
      %t15_13_14() : ok15(_)
      p15_13_14()
    case 15n+l:
      %t15_13_far(l) : ok15(_)
      p15_13()

def q15_14(j: Nat) -> ok15(pat15(14n, j)):
  match j:
    case 0n:
      %t15_14_0() : ok15(_)
      p15_0_14()
    case 1n:
      %t15_14_1() : ok15(_)
      p15_1_14()
    case 2n:
      %t15_14_2() : ok15(_)
      p15_2_14()
    case 3n:
      %t15_14_3() : ok15(_)
      p15_3_14()
    case 4n:
      %t15_14_4() : ok15(_)
      p15_4_14()
    case 5n:
      %t15_14_5() : ok15(_)
      p15_5_14()
    case 6n:
      %t15_14_6() : ok15(_)
      p15_6_14()
    case 7n:
      %t15_14_7() : ok15(_)
      p15_7_14()
    case 8n:
      %t15_14_8() : ok15(_)
      p15_8_14()
    case 9n:
      %t15_14_9() : ok15(_)
      p15_9_14()
    case 10n:
      %t15_14_10() : ok15(_)
      p15_10_14()
    case 11n:
      %t15_14_11() : ok15(_)
      p15_11_14()
    case 12n:
      %t15_14_12() : ok15(_)
      p15_12_14()
    case 13n:
      %t15_14_13() : ok15(_)
      p15_13_14()
    case 14n:
      %t15_14_14() : ok15(_)
      p15_none()
    case 15n+l:
      %t15_14_far(l) : ok15(_)
      p15_14()

def q15_far(k: Nat, j: Nat) -> ok15(pat15(15n+k, j)):
  match j:
    case 0n:
      %t15_far_0(k) : ok15(_)
      p15_0()
    case 1n:
      %t15_far_1(k) : ok15(_)
      p15_1()
    case 2n:
      %t15_far_2(k) : ok15(_)
      p15_2()
    case 3n:
      %t15_far_3(k) : ok15(_)
      p15_3()
    case 4n:
      %t15_far_4(k) : ok15(_)
      p15_4()
    case 5n:
      %t15_far_5(k) : ok15(_)
      p15_5()
    case 6n:
      %t15_far_6(k) : ok15(_)
      p15_6()
    case 7n:
      %t15_far_7(k) : ok15(_)
      p15_7()
    case 8n:
      %t15_far_8(k) : ok15(_)
      p15_8()
    case 9n:
      %t15_far_9(k) : ok15(_)
      p15_9()
    case 10n:
      %t15_far_10(k) : ok15(_)
      p15_10()
    case 11n:
      %t15_far_11(k) : ok15(_)
      p15_11()
    case 12n:
      %t15_far_12(k) : ok15(_)
      p15_12()
    case 13n:
      %t15_far_13(k) : ok15(_)
      p15_13()
    case 14n:
      %t15_far_14(k) : ok15(_)
      p15_14()
    case 15n+l:
      %t15_far_far(k, l) : ok15(_)
      p15_none()

# Every pattern of at most two flipped bits, given as two flips
def q15(i: Nat, +j: Nat) -> ok15(pat15(i, j)):
  match i:
    case 0n:
      q15_0(j)
    case 1n:
      q15_1(j)
    case 2n:
      q15_2(j)
    case 3n:
      q15_3(j)
    case 4n:
      q15_4(j)
    case 5n:
      q15_5(j)
    case 6n:
      q15_6(j)
    case 7n:
      q15_7(j)
    case 8n:
      q15_8(j)
    case 9n:
      q15_9(j)
    case 10n:
      q15_10(j)
    case 11n:
      q15_11(j)
    case 12n:
      q15_12(j)
    case 13n:
      q15_13(j)
    case 14n:
      q15_14(j)
    case 15n+k:
      q15_far(k, j)
