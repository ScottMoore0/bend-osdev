# Rs.small8's patterns of at most two errors, each corrected alone (this
# whole file is written by gen/proof.py: do not edit it).
#
# For a word x of 7 symbols, chk8(x) applies to x the decoder's
# corrections for x's syndromes (Rs.plan), and ok8(x) says that this is
# the zero word. For each pattern e with at most two nonzero symbols (1079
# of them) ok8(e) holds: the decoder finds exactly e's errors. Each is
# computed in a def of its own (p8_<e>), on literals: the proof kernel has
# a step budget per def, and computes literals far faster than words with
# unknown bits.
#
# q8 takes a pattern given as two changes (pat8: a value added at an
# index, twice) apart. Each value is read modulo 2^3, as the decoder reads
# it, so its low three bits are tried and the unknown others rewritten
# away (l8_<x>); then each index is tried (0 to 6, or past the end, which
# changes nothing), the pattern rewritten into its list of symbols
# (r8_<i>_<j>, from facts about single symbols: s8a, s8b, s8c), and each
# case is one of the patterns. b1 is a fact about elements that
# PROOF_errors.bend needs. The facts about elements are proved by
# splitting the words into their 32 bits.
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as Sy
import ./rs.bend as D

# the word of 7 symbols with x added at index i and y at index j
def pat8(i: Nat, +x: U32, j: Nat, +y: U32) -> List<&2, U32>:
  P.RsPoly.add(C.Rs.gf8(), D.Rs.inject(E.rs.zeros(7n), i, x), D.Rs.inject(E.rs.zeros(7n), j, y))

# the corrections for x's syndromes, applied to x
def chk8r(r: Result<&2, &2, E.RsError, List<&2, D.RsFix>>, +x: List<&2, U32>) -> Result<&2, &2, E.RsError, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fs}:
      Done{D.Rs.apply(C.Rs.small8(), fs, x)}

def chk8(+x: List<&2, U32>) -> Result<&2, &2, E.RsError, List<&2, U32>>:
  chk8r(D.Rs.plan(C.Rs.small8(), Sy.Rs.syndromes(C.Rs.small8(), x), Nil{}, 7), x)

def ok8(+x: List<&2, U32>) -> Type:
  {chk8(x) == Done{[0, 0, 0, 0, 0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}

# elt (u + v) = elt u + (0 + elt v)
def b1(u: U32, v: U32) -> {M.Gfm.elt(C.Rs.gf8(), U32.xor(u, v)) == M.Gfm.add(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), u), U32.xor(0, M.Gfm.elt(C.Rs.gf8(), v))) : U32}:
  match u v:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# x + 0 = x
def bx0(+b: Bool) -> {Bool.xor(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wx0(n: Nat, a: Word(n)) -> {Word.xor(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          %bx0(ah) : {WCon{Bool.xor(ah, False{}), Word.xor(p, at, Word.zero(p))} == WCon{_, at} : Word(1n+p)}
          %wx0(p, at) : {WCon{Bool.xor(ah, False{}), Word.xor(p, at, Word.zero(p))} == WCon{Bool.xor(ah, False{}), _} : Word(1n+p)}
          {==}

def ux0(a: U32) -> {U32.xor(a, 0) == a : U32}:
  match a:
    case U32{+x}:
      %wx0(32n, x) : {U32{Word.xor(32n, x, Word.zero(32n))} == U32{_} : U32}
      {==}

def b2e(u: U32) -> {M.Gfm.elt(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), U32.xor(0, u))) == M.Gfm.elt(C.Rs.gf8(), u) : U32}:
  match u:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def b2(+u: U32) -> {M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, u), 0)) == M.Gfm.elt(C.Rs.gf8(), u) : U32}:
  %Equal.sym(U32, U32.xor(U32.xor(0, u), 0), U32.xor(0, u), ux0(U32.xor(0, u))) : {M.Gfm.elt(C.Rs.gf8(), M.Gfm.elt(C.Rs.gf8(), _)) == M.Gfm.elt(C.Rs.gf8(), u) : U32}
  b2e(u)

def b3(u: U32) -> {M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), 0, U32.xor(0, u))) == M.Gfm.elt(C.Rs.gf8(), u) : U32}:
  match u:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def s8c(u: U32, v: U32) -> {M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, u), U32.xor(0, v))) == M.Gfm.add(C.Rs.gf8(), u, v) : U32}:
  match u v:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# a change x at index i, alone (s8a) or with y at another (s8b)
def s8a(+x: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)) == x : U32}:
  Equal.trans(U32, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), M.Gfm.elt(C.Rs.gf8(), x), x, b2(x), hx)

def s8b(+y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), 0, U32.xor(0, y))) == y : U32}:
  Equal.trans(U32, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), 0, U32.xor(0, y))), M.Gfm.elt(C.Rs.gf8(), y), y, b3(y), hy)

def l8_0(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {0 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_1(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {1 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_2(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {2 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_3(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {3 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_4(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {4 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_5(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {5 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_6(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {6 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def l8_7(+a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +a11: Bool, +a12: Bool, +a13: Bool, +a14: Bool, +a15: Bool, +a16: Bool, +a17: Bool, +a18: Bool, +a19: Bool, +a20: Bool, +a21: Bool, +a22: Bool, +a23: Bool, +a24: Bool, +a25: Bool, +a26: Bool, +a27: Bool, +a28: Bool, +a29: Bool, +a30: Bool, +a31: Bool) -> {7 == M.Gfm.elt(C.Rs.gf8(), U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  {==}

def ev8_0() -> {M.Gfm.elt(C.Rs.gf8(), 0) == 0 : U32}:
  {==}

def ev8_1() -> {M.Gfm.elt(C.Rs.gf8(), 1) == 1 : U32}:
  {==}

def ev8_2() -> {M.Gfm.elt(C.Rs.gf8(), 2) == 2 : U32}:
  {==}

def ev8_3() -> {M.Gfm.elt(C.Rs.gf8(), 3) == 3 : U32}:
  {==}

def ev8_4() -> {M.Gfm.elt(C.Rs.gf8(), 4) == 4 : U32}:
  {==}

def ev8_5() -> {M.Gfm.elt(C.Rs.gf8(), 5) == 5 : U32}:
  {==}

def ev8_6() -> {M.Gfm.elt(C.Rs.gf8(), 6) == 6 : U32}:
  {==}

def ev8_7() -> {M.Gfm.elt(C.Rs.gf8(), 7) == 7 : U32}:
  {==}

def xr8_0_0() -> {0 == M.Gfm.add(C.Rs.gf8(), 0, 0) : U32}:
  {==}

def xr8_0_1() -> {1 == M.Gfm.add(C.Rs.gf8(), 0, 1) : U32}:
  {==}

def xr8_0_2() -> {2 == M.Gfm.add(C.Rs.gf8(), 0, 2) : U32}:
  {==}

def xr8_0_3() -> {3 == M.Gfm.add(C.Rs.gf8(), 0, 3) : U32}:
  {==}

def xr8_0_4() -> {4 == M.Gfm.add(C.Rs.gf8(), 0, 4) : U32}:
  {==}

def xr8_0_5() -> {5 == M.Gfm.add(C.Rs.gf8(), 0, 5) : U32}:
  {==}

def xr8_0_6() -> {6 == M.Gfm.add(C.Rs.gf8(), 0, 6) : U32}:
  {==}

def xr8_0_7() -> {7 == M.Gfm.add(C.Rs.gf8(), 0, 7) : U32}:
  {==}

def xr8_1_0() -> {1 == M.Gfm.add(C.Rs.gf8(), 1, 0) : U32}:
  {==}

def xr8_1_1() -> {0 == M.Gfm.add(C.Rs.gf8(), 1, 1) : U32}:
  {==}

def xr8_1_2() -> {3 == M.Gfm.add(C.Rs.gf8(), 1, 2) : U32}:
  {==}

def xr8_1_3() -> {2 == M.Gfm.add(C.Rs.gf8(), 1, 3) : U32}:
  {==}

def xr8_1_4() -> {5 == M.Gfm.add(C.Rs.gf8(), 1, 4) : U32}:
  {==}

def xr8_1_5() -> {4 == M.Gfm.add(C.Rs.gf8(), 1, 5) : U32}:
  {==}

def xr8_1_6() -> {7 == M.Gfm.add(C.Rs.gf8(), 1, 6) : U32}:
  {==}

def xr8_1_7() -> {6 == M.Gfm.add(C.Rs.gf8(), 1, 7) : U32}:
  {==}

def xr8_2_0() -> {2 == M.Gfm.add(C.Rs.gf8(), 2, 0) : U32}:
  {==}

def xr8_2_1() -> {3 == M.Gfm.add(C.Rs.gf8(), 2, 1) : U32}:
  {==}

def xr8_2_2() -> {0 == M.Gfm.add(C.Rs.gf8(), 2, 2) : U32}:
  {==}

def xr8_2_3() -> {1 == M.Gfm.add(C.Rs.gf8(), 2, 3) : U32}:
  {==}

def xr8_2_4() -> {6 == M.Gfm.add(C.Rs.gf8(), 2, 4) : U32}:
  {==}

def xr8_2_5() -> {7 == M.Gfm.add(C.Rs.gf8(), 2, 5) : U32}:
  {==}

def xr8_2_6() -> {4 == M.Gfm.add(C.Rs.gf8(), 2, 6) : U32}:
  {==}

def xr8_2_7() -> {5 == M.Gfm.add(C.Rs.gf8(), 2, 7) : U32}:
  {==}

def xr8_3_0() -> {3 == M.Gfm.add(C.Rs.gf8(), 3, 0) : U32}:
  {==}

def xr8_3_1() -> {2 == M.Gfm.add(C.Rs.gf8(), 3, 1) : U32}:
  {==}

def xr8_3_2() -> {1 == M.Gfm.add(C.Rs.gf8(), 3, 2) : U32}:
  {==}

def xr8_3_3() -> {0 == M.Gfm.add(C.Rs.gf8(), 3, 3) : U32}:
  {==}

def xr8_3_4() -> {7 == M.Gfm.add(C.Rs.gf8(), 3, 4) : U32}:
  {==}

def xr8_3_5() -> {6 == M.Gfm.add(C.Rs.gf8(), 3, 5) : U32}:
  {==}

def xr8_3_6() -> {5 == M.Gfm.add(C.Rs.gf8(), 3, 6) : U32}:
  {==}

def xr8_3_7() -> {4 == M.Gfm.add(C.Rs.gf8(), 3, 7) : U32}:
  {==}

def xr8_4_0() -> {4 == M.Gfm.add(C.Rs.gf8(), 4, 0) : U32}:
  {==}

def xr8_4_1() -> {5 == M.Gfm.add(C.Rs.gf8(), 4, 1) : U32}:
  {==}

def xr8_4_2() -> {6 == M.Gfm.add(C.Rs.gf8(), 4, 2) : U32}:
  {==}

def xr8_4_3() -> {7 == M.Gfm.add(C.Rs.gf8(), 4, 3) : U32}:
  {==}

def xr8_4_4() -> {0 == M.Gfm.add(C.Rs.gf8(), 4, 4) : U32}:
  {==}

def xr8_4_5() -> {1 == M.Gfm.add(C.Rs.gf8(), 4, 5) : U32}:
  {==}

def xr8_4_6() -> {2 == M.Gfm.add(C.Rs.gf8(), 4, 6) : U32}:
  {==}

def xr8_4_7() -> {3 == M.Gfm.add(C.Rs.gf8(), 4, 7) : U32}:
  {==}

def xr8_5_0() -> {5 == M.Gfm.add(C.Rs.gf8(), 5, 0) : U32}:
  {==}

def xr8_5_1() -> {4 == M.Gfm.add(C.Rs.gf8(), 5, 1) : U32}:
  {==}

def xr8_5_2() -> {7 == M.Gfm.add(C.Rs.gf8(), 5, 2) : U32}:
  {==}

def xr8_5_3() -> {6 == M.Gfm.add(C.Rs.gf8(), 5, 3) : U32}:
  {==}

def xr8_5_4() -> {1 == M.Gfm.add(C.Rs.gf8(), 5, 4) : U32}:
  {==}

def xr8_5_5() -> {0 == M.Gfm.add(C.Rs.gf8(), 5, 5) : U32}:
  {==}

def xr8_5_6() -> {3 == M.Gfm.add(C.Rs.gf8(), 5, 6) : U32}:
  {==}

def xr8_5_7() -> {2 == M.Gfm.add(C.Rs.gf8(), 5, 7) : U32}:
  {==}

def xr8_6_0() -> {6 == M.Gfm.add(C.Rs.gf8(), 6, 0) : U32}:
  {==}

def xr8_6_1() -> {7 == M.Gfm.add(C.Rs.gf8(), 6, 1) : U32}:
  {==}

def xr8_6_2() -> {4 == M.Gfm.add(C.Rs.gf8(), 6, 2) : U32}:
  {==}

def xr8_6_3() -> {5 == M.Gfm.add(C.Rs.gf8(), 6, 3) : U32}:
  {==}

def xr8_6_4() -> {2 == M.Gfm.add(C.Rs.gf8(), 6, 4) : U32}:
  {==}

def xr8_6_5() -> {3 == M.Gfm.add(C.Rs.gf8(), 6, 5) : U32}:
  {==}

def xr8_6_6() -> {0 == M.Gfm.add(C.Rs.gf8(), 6, 6) : U32}:
  {==}

def xr8_6_7() -> {1 == M.Gfm.add(C.Rs.gf8(), 6, 7) : U32}:
  {==}

def xr8_7_0() -> {7 == M.Gfm.add(C.Rs.gf8(), 7, 0) : U32}:
  {==}

def xr8_7_1() -> {6 == M.Gfm.add(C.Rs.gf8(), 7, 1) : U32}:
  {==}

def xr8_7_2() -> {5 == M.Gfm.add(C.Rs.gf8(), 7, 2) : U32}:
  {==}

def xr8_7_3() -> {4 == M.Gfm.add(C.Rs.gf8(), 7, 3) : U32}:
  {==}

def xr8_7_4() -> {3 == M.Gfm.add(C.Rs.gf8(), 7, 4) : U32}:
  {==}

def xr8_7_5() -> {2 == M.Gfm.add(C.Rs.gf8(), 7, 5) : U32}:
  {==}

def xr8_7_6() -> {1 == M.Gfm.add(C.Rs.gf8(), 7, 6) : U32}:
  {==}

def xr8_7_7() -> {0 == M.Gfm.add(C.Rs.gf8(), 7, 7) : U32}:
  {==}

# A pattern's list of symbols, for each pair of indexes

def r8_0_0(+x: U32, +y: U32) -> {[M.Gfm.add(C.Rs.gf8(), x, y), 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 0n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[_, 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_0_1(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[x, y, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 1n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, y, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 1n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), _, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_0_2(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[x, 0, y, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 2n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, 0, y, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 2n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_0_3(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[x, 0, 0, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 3n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, 0, 0, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 3n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_0_4(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[x, 0, 0, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 4n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, 0, 0, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 4n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_0_5(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[x, 0, 0, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 5n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, 0, 0, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 5n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_0_6(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[x, 0, 0, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 6n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, 0, 0, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 6n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_0_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[x, 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[_, 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(0n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_1_0(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, x, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 0n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[y, _, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 0n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[_, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_1_1(+x: U32, +y: U32) -> {[0, M.Gfm.add(C.Rs.gf8(), x, y), 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 1n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[0, _, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_1_2(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, x, y, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 2n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, _, y, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 2n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_1_3(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, x, 0, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 3n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, _, 0, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 3n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_1_4(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, x, 0, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 4n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, _, 0, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 4n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_1_5(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, x, 0, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 5n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, _, 0, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 5n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_1_6(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, x, 0, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 6n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, _, 0, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 6n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_1_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[0, x, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, _, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(1n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_2_0(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, 0, x, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 0n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[y, 0, _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 0n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[_, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_2_1(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, y, x, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 1n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, y, _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 1n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, _, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_2_2(+x: U32, +y: U32) -> {[0, 0, M.Gfm.add(C.Rs.gf8(), x, y), 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 2n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[0, 0, _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_2_3(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, x, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 3n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, _, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 3n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_2_4(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, x, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 4n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, _, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 4n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_2_5(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, x, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 5n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, _, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 5n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_2_6(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, x, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 6n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, _, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 6n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_2_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[0, 0, x, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(2n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_3_0(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, 0, 0, x, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 0n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[y, 0, 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 0n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[_, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_3_1(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, y, 0, x, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 1n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, y, 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 1n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, _, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_3_2(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, y, x, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 2n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, y, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 2n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, _, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_3_3(+x: U32, +y: U32) -> {[0, 0, 0, M.Gfm.add(C.Rs.gf8(), x, y), 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 3n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[0, 0, 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_3_4(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, x, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 4n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, _, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 4n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_3_5(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, x, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 5n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, _, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 5n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_3_6(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, x, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 6n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, _, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 6n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_3_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[0, 0, 0, x, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(3n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_4_0(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, 0, 0, 0, x, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 0n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[y, 0, 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 0n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[_, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_4_1(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, y, 0, 0, x, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 1n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, y, 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 1n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, _, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_4_2(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, y, 0, x, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 2n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, y, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 2n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, _, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_4_3(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, y, x, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 3n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, y, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 3n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, _, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_4_4(+x: U32, +y: U32) -> {[0, 0, 0, 0, M.Gfm.add(C.Rs.gf8(), x, y), 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 4n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[0, 0, 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_4_5(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, x, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 5n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, _, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 5n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), _, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_4_6(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, x, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 6n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, _, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 6n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0, _] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_4_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[0, 0, 0, 0, x, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(4n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_5_0(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, 0, 0, 0, 0, x, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 0n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[y, 0, 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 0n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[_, 0, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_5_1(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, y, 0, 0, 0, x, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 1n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, y, 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 1n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, _, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_5_2(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, y, 0, 0, x, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 2n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, y, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 2n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, _, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_5_3(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, y, 0, x, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 3n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, y, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 3n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, _, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_5_4(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, y, x, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 4n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, y, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 4n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, 0, _, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_5_5(+x: U32, +y: U32) -> {[0, 0, 0, 0, 0, M.Gfm.add(C.Rs.gf8(), x, y), 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 5n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[0, 0, 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_5_6(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, 0, x, y] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 6n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, 0, _, y] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 6n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0)), _] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_5_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[0, 0, 0, 0, 0, x, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(5n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_6_0(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, 0, 0, 0, 0, 0, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 0n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[y, 0, 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 0n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[_, 0, 0, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0))] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_6_1(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, y, 0, 0, 0, 0, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 1n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, y, 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 1n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, _, 0, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0))] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_6_2(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, y, 0, 0, 0, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 2n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, y, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 2n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, _, 0, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0))] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_6_3(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, y, 0, 0, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 3n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, y, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 3n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, _, 0, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0))] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_6_4(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, y, 0, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 4n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, y, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 4n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, 0, _, 0, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0))] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_6_5(+x: U32, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, 0, y, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 5n, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, 0, y, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 5n, y)) : List<&2, U32>}
  %s8b(y, hy) : {[0, 0, 0, 0, 0, _, M.Gfm.elt(C.Rs.gf8(), M.Gfm.add(C.Rs.gf8(), U32.xor(0, x), 0))] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_6_6(+x: U32, +y: U32) -> {[0, 0, 0, 0, 0, 0, M.Gfm.add(C.Rs.gf8(), x, y)] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 6n, y)) : List<&2, U32>}:
  %s8c(x, y) : {[0, 0, 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_6_far(+x: U32, l: Nat, +y: U32, +hx: {M.Gfm.elt(C.Rs.gf8(), x) == x : U32}) -> {[0, 0, 0, 0, 0, 0, x] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 7n+l, y)) : List<&2, U32>}:
  %s8a(x, hx) : {[0, 0, 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(6n, x, 7n+l, y)) : List<&2, U32>}
  {==}

def r8_far_0(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[y, 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 0n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[_, 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 0n, y)) : List<&2, U32>}
  {==}

def r8_far_1(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, y, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 1n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[0, _, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 1n, y)) : List<&2, U32>}
  {==}

def r8_far_2(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, y, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 2n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[0, 0, _, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 2n, y)) : List<&2, U32>}
  {==}

def r8_far_3(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, y, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 3n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[0, 0, 0, _, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 3n, y)) : List<&2, U32>}
  {==}

def r8_far_4(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, y, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 4n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[0, 0, 0, 0, _, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 4n, y)) : List<&2, U32>}
  {==}

def r8_far_5(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, 0, y, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 5n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[0, 0, 0, 0, 0, _, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 5n, y)) : List<&2, U32>}
  {==}

def r8_far_6(k: Nat, +x: U32, +y: U32, +hy: {M.Gfm.elt(C.Rs.gf8(), y) == y : U32}) -> {[0, 0, 0, 0, 0, 0, y] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 6n, y)) : List<&2, U32>}:
  %s8b(y, hy) : {[0, 0, 0, 0, 0, 0, _] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 6n, y)) : List<&2, U32>}
  {==}

def r8_far_far(k: Nat, +x: U32, l: Nat, +y: U32) -> {[0, 0, 0, 0, 0, 0, 0] == E.Rs.mask(C.Rs.small8(), pat8(7n+k, x, 7n+l, y)) : List<&2, U32>}:
  {==}

# The patterns

def p8_0000000() -> ok8([0, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_0000001() -> ok8([0, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_0000002() -> ok8([0, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_0000003() -> ok8([0, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_0000004() -> ok8([0, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_0000005() -> ok8([0, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_0000006() -> ok8([0, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_0000007() -> ok8([0, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_0000010() -> ok8([0, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_0000020() -> ok8([0, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_0000030() -> ok8([0, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_0000040() -> ok8([0, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_0000050() -> ok8([0, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_0000060() -> ok8([0, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_0000070() -> ok8([0, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_0000100() -> ok8([0, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_0000200() -> ok8([0, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_0000300() -> ok8([0, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_0000400() -> ok8([0, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_0000500() -> ok8([0, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_0000600() -> ok8([0, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_0000700() -> ok8([0, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_0001000() -> ok8([0, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_0002000() -> ok8([0, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_0003000() -> ok8([0, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_0004000() -> ok8([0, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_0005000() -> ok8([0, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_0006000() -> ok8([0, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_0007000() -> ok8([0, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_0010000() -> ok8([0, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_0020000() -> ok8([0, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_0030000() -> ok8([0, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_0040000() -> ok8([0, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_0050000() -> ok8([0, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_0060000() -> ok8([0, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_0070000() -> ok8([0, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_0100000() -> ok8([0, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_0200000() -> ok8([0, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_0300000() -> ok8([0, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_0400000() -> ok8([0, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_0500000() -> ok8([0, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_0600000() -> ok8([0, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_0700000() -> ok8([0, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_1000000() -> ok8([1, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_2000000() -> ok8([2, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_3000000() -> ok8([3, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_4000000() -> ok8([4, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_5000000() -> ok8([5, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_6000000() -> ok8([6, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_7000000() -> ok8([7, 0, 0, 0, 0, 0, 0]):
  {==}

def p8_0000011() -> ok8([0, 0, 0, 0, 0, 1, 1]):
  {==}

def p8_0000012() -> ok8([0, 0, 0, 0, 0, 1, 2]):
  {==}

def p8_0000013() -> ok8([0, 0, 0, 0, 0, 1, 3]):
  {==}

def p8_0000014() -> ok8([0, 0, 0, 0, 0, 1, 4]):
  {==}

def p8_0000015() -> ok8([0, 0, 0, 0, 0, 1, 5]):
  {==}

def p8_0000016() -> ok8([0, 0, 0, 0, 0, 1, 6]):
  {==}

def p8_0000017() -> ok8([0, 0, 0, 0, 0, 1, 7]):
  {==}

def p8_0000021() -> ok8([0, 0, 0, 0, 0, 2, 1]):
  {==}

def p8_0000022() -> ok8([0, 0, 0, 0, 0, 2, 2]):
  {==}

def p8_0000023() -> ok8([0, 0, 0, 0, 0, 2, 3]):
  {==}

def p8_0000024() -> ok8([0, 0, 0, 0, 0, 2, 4]):
  {==}

def p8_0000025() -> ok8([0, 0, 0, 0, 0, 2, 5]):
  {==}

def p8_0000026() -> ok8([0, 0, 0, 0, 0, 2, 6]):
  {==}

def p8_0000027() -> ok8([0, 0, 0, 0, 0, 2, 7]):
  {==}

def p8_0000031() -> ok8([0, 0, 0, 0, 0, 3, 1]):
  {==}

def p8_0000032() -> ok8([0, 0, 0, 0, 0, 3, 2]):
  {==}

def p8_0000033() -> ok8([0, 0, 0, 0, 0, 3, 3]):
  {==}

def p8_0000034() -> ok8([0, 0, 0, 0, 0, 3, 4]):
  {==}

def p8_0000035() -> ok8([0, 0, 0, 0, 0, 3, 5]):
  {==}

def p8_0000036() -> ok8([0, 0, 0, 0, 0, 3, 6]):
  {==}

def p8_0000037() -> ok8([0, 0, 0, 0, 0, 3, 7]):
  {==}

def p8_0000041() -> ok8([0, 0, 0, 0, 0, 4, 1]):
  {==}

def p8_0000042() -> ok8([0, 0, 0, 0, 0, 4, 2]):
  {==}

def p8_0000043() -> ok8([0, 0, 0, 0, 0, 4, 3]):
  {==}

def p8_0000044() -> ok8([0, 0, 0, 0, 0, 4, 4]):
  {==}

def p8_0000045() -> ok8([0, 0, 0, 0, 0, 4, 5]):
  {==}

def p8_0000046() -> ok8([0, 0, 0, 0, 0, 4, 6]):
  {==}

def p8_0000047() -> ok8([0, 0, 0, 0, 0, 4, 7]):
  {==}

def p8_0000051() -> ok8([0, 0, 0, 0, 0, 5, 1]):
  {==}

def p8_0000052() -> ok8([0, 0, 0, 0, 0, 5, 2]):
  {==}

def p8_0000053() -> ok8([0, 0, 0, 0, 0, 5, 3]):
  {==}

def p8_0000054() -> ok8([0, 0, 0, 0, 0, 5, 4]):
  {==}

def p8_0000055() -> ok8([0, 0, 0, 0, 0, 5, 5]):
  {==}

def p8_0000056() -> ok8([0, 0, 0, 0, 0, 5, 6]):
  {==}

def p8_0000057() -> ok8([0, 0, 0, 0, 0, 5, 7]):
  {==}

def p8_0000061() -> ok8([0, 0, 0, 0, 0, 6, 1]):
  {==}

def p8_0000062() -> ok8([0, 0, 0, 0, 0, 6, 2]):
  {==}

def p8_0000063() -> ok8([0, 0, 0, 0, 0, 6, 3]):
  {==}

def p8_0000064() -> ok8([0, 0, 0, 0, 0, 6, 4]):
  {==}

def p8_0000065() -> ok8([0, 0, 0, 0, 0, 6, 5]):
  {==}

def p8_0000066() -> ok8([0, 0, 0, 0, 0, 6, 6]):
  {==}

def p8_0000067() -> ok8([0, 0, 0, 0, 0, 6, 7]):
  {==}

def p8_0000071() -> ok8([0, 0, 0, 0, 0, 7, 1]):
  {==}

def p8_0000072() -> ok8([0, 0, 0, 0, 0, 7, 2]):
  {==}

def p8_0000073() -> ok8([0, 0, 0, 0, 0, 7, 3]):
  {==}

def p8_0000074() -> ok8([0, 0, 0, 0, 0, 7, 4]):
  {==}

def p8_0000075() -> ok8([0, 0, 0, 0, 0, 7, 5]):
  {==}

def p8_0000076() -> ok8([0, 0, 0, 0, 0, 7, 6]):
  {==}

def p8_0000077() -> ok8([0, 0, 0, 0, 0, 7, 7]):
  {==}

def p8_0000101() -> ok8([0, 0, 0, 0, 1, 0, 1]):
  {==}

def p8_0000102() -> ok8([0, 0, 0, 0, 1, 0, 2]):
  {==}

def p8_0000103() -> ok8([0, 0, 0, 0, 1, 0, 3]):
  {==}

def p8_0000104() -> ok8([0, 0, 0, 0, 1, 0, 4]):
  {==}

def p8_0000105() -> ok8([0, 0, 0, 0, 1, 0, 5]):
  {==}

def p8_0000106() -> ok8([0, 0, 0, 0, 1, 0, 6]):
  {==}

def p8_0000107() -> ok8([0, 0, 0, 0, 1, 0, 7]):
  {==}

def p8_0000110() -> ok8([0, 0, 0, 0, 1, 1, 0]):
  {==}

def p8_0000120() -> ok8([0, 0, 0, 0, 1, 2, 0]):
  {==}

def p8_0000130() -> ok8([0, 0, 0, 0, 1, 3, 0]):
  {==}

def p8_0000140() -> ok8([0, 0, 0, 0, 1, 4, 0]):
  {==}

def p8_0000150() -> ok8([0, 0, 0, 0, 1, 5, 0]):
  {==}

def p8_0000160() -> ok8([0, 0, 0, 0, 1, 6, 0]):
  {==}

def p8_0000170() -> ok8([0, 0, 0, 0, 1, 7, 0]):
  {==}

def p8_0000201() -> ok8([0, 0, 0, 0, 2, 0, 1]):
  {==}

def p8_0000202() -> ok8([0, 0, 0, 0, 2, 0, 2]):
  {==}

def p8_0000203() -> ok8([0, 0, 0, 0, 2, 0, 3]):
  {==}

def p8_0000204() -> ok8([0, 0, 0, 0, 2, 0, 4]):
  {==}

def p8_0000205() -> ok8([0, 0, 0, 0, 2, 0, 5]):
  {==}

def p8_0000206() -> ok8([0, 0, 0, 0, 2, 0, 6]):
  {==}

def p8_0000207() -> ok8([0, 0, 0, 0, 2, 0, 7]):
  {==}

def p8_0000210() -> ok8([0, 0, 0, 0, 2, 1, 0]):
  {==}

def p8_0000220() -> ok8([0, 0, 0, 0, 2, 2, 0]):
  {==}

def p8_0000230() -> ok8([0, 0, 0, 0, 2, 3, 0]):
  {==}

def p8_0000240() -> ok8([0, 0, 0, 0, 2, 4, 0]):
  {==}

def p8_0000250() -> ok8([0, 0, 0, 0, 2, 5, 0]):
  {==}

def p8_0000260() -> ok8([0, 0, 0, 0, 2, 6, 0]):
  {==}

def p8_0000270() -> ok8([0, 0, 0, 0, 2, 7, 0]):
  {==}

def p8_0000301() -> ok8([0, 0, 0, 0, 3, 0, 1]):
  {==}

def p8_0000302() -> ok8([0, 0, 0, 0, 3, 0, 2]):
  {==}

def p8_0000303() -> ok8([0, 0, 0, 0, 3, 0, 3]):
  {==}

def p8_0000304() -> ok8([0, 0, 0, 0, 3, 0, 4]):
  {==}

def p8_0000305() -> ok8([0, 0, 0, 0, 3, 0, 5]):
  {==}

def p8_0000306() -> ok8([0, 0, 0, 0, 3, 0, 6]):
  {==}

def p8_0000307() -> ok8([0, 0, 0, 0, 3, 0, 7]):
  {==}

def p8_0000310() -> ok8([0, 0, 0, 0, 3, 1, 0]):
  {==}

def p8_0000320() -> ok8([0, 0, 0, 0, 3, 2, 0]):
  {==}

def p8_0000330() -> ok8([0, 0, 0, 0, 3, 3, 0]):
  {==}

def p8_0000340() -> ok8([0, 0, 0, 0, 3, 4, 0]):
  {==}

def p8_0000350() -> ok8([0, 0, 0, 0, 3, 5, 0]):
  {==}

def p8_0000360() -> ok8([0, 0, 0, 0, 3, 6, 0]):
  {==}

def p8_0000370() -> ok8([0, 0, 0, 0, 3, 7, 0]):
  {==}

def p8_0000401() -> ok8([0, 0, 0, 0, 4, 0, 1]):
  {==}

def p8_0000402() -> ok8([0, 0, 0, 0, 4, 0, 2]):
  {==}

def p8_0000403() -> ok8([0, 0, 0, 0, 4, 0, 3]):
  {==}

def p8_0000404() -> ok8([0, 0, 0, 0, 4, 0, 4]):
  {==}

def p8_0000405() -> ok8([0, 0, 0, 0, 4, 0, 5]):
  {==}

def p8_0000406() -> ok8([0, 0, 0, 0, 4, 0, 6]):
  {==}

def p8_0000407() -> ok8([0, 0, 0, 0, 4, 0, 7]):
  {==}

def p8_0000410() -> ok8([0, 0, 0, 0, 4, 1, 0]):
  {==}

def p8_0000420() -> ok8([0, 0, 0, 0, 4, 2, 0]):
  {==}

def p8_0000430() -> ok8([0, 0, 0, 0, 4, 3, 0]):
  {==}

def p8_0000440() -> ok8([0, 0, 0, 0, 4, 4, 0]):
  {==}

def p8_0000450() -> ok8([0, 0, 0, 0, 4, 5, 0]):
  {==}

def p8_0000460() -> ok8([0, 0, 0, 0, 4, 6, 0]):
  {==}

def p8_0000470() -> ok8([0, 0, 0, 0, 4, 7, 0]):
  {==}

def p8_0000501() -> ok8([0, 0, 0, 0, 5, 0, 1]):
  {==}

def p8_0000502() -> ok8([0, 0, 0, 0, 5, 0, 2]):
  {==}

def p8_0000503() -> ok8([0, 0, 0, 0, 5, 0, 3]):
  {==}

def p8_0000504() -> ok8([0, 0, 0, 0, 5, 0, 4]):
  {==}

def p8_0000505() -> ok8([0, 0, 0, 0, 5, 0, 5]):
  {==}

def p8_0000506() -> ok8([0, 0, 0, 0, 5, 0, 6]):
  {==}

def p8_0000507() -> ok8([0, 0, 0, 0, 5, 0, 7]):
  {==}

def p8_0000510() -> ok8([0, 0, 0, 0, 5, 1, 0]):
  {==}

def p8_0000520() -> ok8([0, 0, 0, 0, 5, 2, 0]):
  {==}

def p8_0000530() -> ok8([0, 0, 0, 0, 5, 3, 0]):
  {==}

def p8_0000540() -> ok8([0, 0, 0, 0, 5, 4, 0]):
  {==}

def p8_0000550() -> ok8([0, 0, 0, 0, 5, 5, 0]):
  {==}

def p8_0000560() -> ok8([0, 0, 0, 0, 5, 6, 0]):
  {==}

def p8_0000570() -> ok8([0, 0, 0, 0, 5, 7, 0]):
  {==}

def p8_0000601() -> ok8([0, 0, 0, 0, 6, 0, 1]):
  {==}

def p8_0000602() -> ok8([0, 0, 0, 0, 6, 0, 2]):
  {==}

def p8_0000603() -> ok8([0, 0, 0, 0, 6, 0, 3]):
  {==}

def p8_0000604() -> ok8([0, 0, 0, 0, 6, 0, 4]):
  {==}

def p8_0000605() -> ok8([0, 0, 0, 0, 6, 0, 5]):
  {==}

def p8_0000606() -> ok8([0, 0, 0, 0, 6, 0, 6]):
  {==}

def p8_0000607() -> ok8([0, 0, 0, 0, 6, 0, 7]):
  {==}

def p8_0000610() -> ok8([0, 0, 0, 0, 6, 1, 0]):
  {==}

def p8_0000620() -> ok8([0, 0, 0, 0, 6, 2, 0]):
  {==}

def p8_0000630() -> ok8([0, 0, 0, 0, 6, 3, 0]):
  {==}

def p8_0000640() -> ok8([0, 0, 0, 0, 6, 4, 0]):
  {==}

def p8_0000650() -> ok8([0, 0, 0, 0, 6, 5, 0]):
  {==}

def p8_0000660() -> ok8([0, 0, 0, 0, 6, 6, 0]):
  {==}

def p8_0000670() -> ok8([0, 0, 0, 0, 6, 7, 0]):
  {==}

def p8_0000701() -> ok8([0, 0, 0, 0, 7, 0, 1]):
  {==}

def p8_0000702() -> ok8([0, 0, 0, 0, 7, 0, 2]):
  {==}

def p8_0000703() -> ok8([0, 0, 0, 0, 7, 0, 3]):
  {==}

def p8_0000704() -> ok8([0, 0, 0, 0, 7, 0, 4]):
  {==}

def p8_0000705() -> ok8([0, 0, 0, 0, 7, 0, 5]):
  {==}

def p8_0000706() -> ok8([0, 0, 0, 0, 7, 0, 6]):
  {==}

def p8_0000707() -> ok8([0, 0, 0, 0, 7, 0, 7]):
  {==}

def p8_0000710() -> ok8([0, 0, 0, 0, 7, 1, 0]):
  {==}

def p8_0000720() -> ok8([0, 0, 0, 0, 7, 2, 0]):
  {==}

def p8_0000730() -> ok8([0, 0, 0, 0, 7, 3, 0]):
  {==}

def p8_0000740() -> ok8([0, 0, 0, 0, 7, 4, 0]):
  {==}

def p8_0000750() -> ok8([0, 0, 0, 0, 7, 5, 0]):
  {==}

def p8_0000760() -> ok8([0, 0, 0, 0, 7, 6, 0]):
  {==}

def p8_0000770() -> ok8([0, 0, 0, 0, 7, 7, 0]):
  {==}

def p8_0001001() -> ok8([0, 0, 0, 1, 0, 0, 1]):
  {==}

def p8_0001002() -> ok8([0, 0, 0, 1, 0, 0, 2]):
  {==}

def p8_0001003() -> ok8([0, 0, 0, 1, 0, 0, 3]):
  {==}

def p8_0001004() -> ok8([0, 0, 0, 1, 0, 0, 4]):
  {==}

def p8_0001005() -> ok8([0, 0, 0, 1, 0, 0, 5]):
  {==}

def p8_0001006() -> ok8([0, 0, 0, 1, 0, 0, 6]):
  {==}

def p8_0001007() -> ok8([0, 0, 0, 1, 0, 0, 7]):
  {==}

def p8_0001010() -> ok8([0, 0, 0, 1, 0, 1, 0]):
  {==}

def p8_0001020() -> ok8([0, 0, 0, 1, 0, 2, 0]):
  {==}

def p8_0001030() -> ok8([0, 0, 0, 1, 0, 3, 0]):
  {==}

def p8_0001040() -> ok8([0, 0, 0, 1, 0, 4, 0]):
  {==}

def p8_0001050() -> ok8([0, 0, 0, 1, 0, 5, 0]):
  {==}

def p8_0001060() -> ok8([0, 0, 0, 1, 0, 6, 0]):
  {==}

def p8_0001070() -> ok8([0, 0, 0, 1, 0, 7, 0]):
  {==}

def p8_0001100() -> ok8([0, 0, 0, 1, 1, 0, 0]):
  {==}

def p8_0001200() -> ok8([0, 0, 0, 1, 2, 0, 0]):
  {==}

def p8_0001300() -> ok8([0, 0, 0, 1, 3, 0, 0]):
  {==}

def p8_0001400() -> ok8([0, 0, 0, 1, 4, 0, 0]):
  {==}

def p8_0001500() -> ok8([0, 0, 0, 1, 5, 0, 0]):
  {==}

def p8_0001600() -> ok8([0, 0, 0, 1, 6, 0, 0]):
  {==}

def p8_0001700() -> ok8([0, 0, 0, 1, 7, 0, 0]):
  {==}

def p8_0002001() -> ok8([0, 0, 0, 2, 0, 0, 1]):
  {==}

def p8_0002002() -> ok8([0, 0, 0, 2, 0, 0, 2]):
  {==}

def p8_0002003() -> ok8([0, 0, 0, 2, 0, 0, 3]):
  {==}

def p8_0002004() -> ok8([0, 0, 0, 2, 0, 0, 4]):
  {==}

def p8_0002005() -> ok8([0, 0, 0, 2, 0, 0, 5]):
  {==}

def p8_0002006() -> ok8([0, 0, 0, 2, 0, 0, 6]):
  {==}

def p8_0002007() -> ok8([0, 0, 0, 2, 0, 0, 7]):
  {==}

def p8_0002010() -> ok8([0, 0, 0, 2, 0, 1, 0]):
  {==}

def p8_0002020() -> ok8([0, 0, 0, 2, 0, 2, 0]):
  {==}

def p8_0002030() -> ok8([0, 0, 0, 2, 0, 3, 0]):
  {==}

def p8_0002040() -> ok8([0, 0, 0, 2, 0, 4, 0]):
  {==}

def p8_0002050() -> ok8([0, 0, 0, 2, 0, 5, 0]):
  {==}

def p8_0002060() -> ok8([0, 0, 0, 2, 0, 6, 0]):
  {==}

def p8_0002070() -> ok8([0, 0, 0, 2, 0, 7, 0]):
  {==}

def p8_0002100() -> ok8([0, 0, 0, 2, 1, 0, 0]):
  {==}

def p8_0002200() -> ok8([0, 0, 0, 2, 2, 0, 0]):
  {==}

def p8_0002300() -> ok8([0, 0, 0, 2, 3, 0, 0]):
  {==}

def p8_0002400() -> ok8([0, 0, 0, 2, 4, 0, 0]):
  {==}

def p8_0002500() -> ok8([0, 0, 0, 2, 5, 0, 0]):
  {==}

def p8_0002600() -> ok8([0, 0, 0, 2, 6, 0, 0]):
  {==}

def p8_0002700() -> ok8([0, 0, 0, 2, 7, 0, 0]):
  {==}

def p8_0003001() -> ok8([0, 0, 0, 3, 0, 0, 1]):
  {==}

def p8_0003002() -> ok8([0, 0, 0, 3, 0, 0, 2]):
  {==}

def p8_0003003() -> ok8([0, 0, 0, 3, 0, 0, 3]):
  {==}

def p8_0003004() -> ok8([0, 0, 0, 3, 0, 0, 4]):
  {==}

def p8_0003005() -> ok8([0, 0, 0, 3, 0, 0, 5]):
  {==}

def p8_0003006() -> ok8([0, 0, 0, 3, 0, 0, 6]):
  {==}

def p8_0003007() -> ok8([0, 0, 0, 3, 0, 0, 7]):
  {==}

def p8_0003010() -> ok8([0, 0, 0, 3, 0, 1, 0]):
  {==}

def p8_0003020() -> ok8([0, 0, 0, 3, 0, 2, 0]):
  {==}

def p8_0003030() -> ok8([0, 0, 0, 3, 0, 3, 0]):
  {==}

def p8_0003040() -> ok8([0, 0, 0, 3, 0, 4, 0]):
  {==}

def p8_0003050() -> ok8([0, 0, 0, 3, 0, 5, 0]):
  {==}

def p8_0003060() -> ok8([0, 0, 0, 3, 0, 6, 0]):
  {==}

def p8_0003070() -> ok8([0, 0, 0, 3, 0, 7, 0]):
  {==}

def p8_0003100() -> ok8([0, 0, 0, 3, 1, 0, 0]):
  {==}

def p8_0003200() -> ok8([0, 0, 0, 3, 2, 0, 0]):
  {==}

def p8_0003300() -> ok8([0, 0, 0, 3, 3, 0, 0]):
  {==}

def p8_0003400() -> ok8([0, 0, 0, 3, 4, 0, 0]):
  {==}

def p8_0003500() -> ok8([0, 0, 0, 3, 5, 0, 0]):
  {==}

def p8_0003600() -> ok8([0, 0, 0, 3, 6, 0, 0]):
  {==}

def p8_0003700() -> ok8([0, 0, 0, 3, 7, 0, 0]):
  {==}

def p8_0004001() -> ok8([0, 0, 0, 4, 0, 0, 1]):
  {==}

def p8_0004002() -> ok8([0, 0, 0, 4, 0, 0, 2]):
  {==}

def p8_0004003() -> ok8([0, 0, 0, 4, 0, 0, 3]):
  {==}

def p8_0004004() -> ok8([0, 0, 0, 4, 0, 0, 4]):
  {==}

def p8_0004005() -> ok8([0, 0, 0, 4, 0, 0, 5]):
  {==}

def p8_0004006() -> ok8([0, 0, 0, 4, 0, 0, 6]):
  {==}

def p8_0004007() -> ok8([0, 0, 0, 4, 0, 0, 7]):
  {==}

def p8_0004010() -> ok8([0, 0, 0, 4, 0, 1, 0]):
  {==}

def p8_0004020() -> ok8([0, 0, 0, 4, 0, 2, 0]):
  {==}

def p8_0004030() -> ok8([0, 0, 0, 4, 0, 3, 0]):
  {==}

def p8_0004040() -> ok8([0, 0, 0, 4, 0, 4, 0]):
  {==}

def p8_0004050() -> ok8([0, 0, 0, 4, 0, 5, 0]):
  {==}

def p8_0004060() -> ok8([0, 0, 0, 4, 0, 6, 0]):
  {==}

def p8_0004070() -> ok8([0, 0, 0, 4, 0, 7, 0]):
  {==}

def p8_0004100() -> ok8([0, 0, 0, 4, 1, 0, 0]):
  {==}

def p8_0004200() -> ok8([0, 0, 0, 4, 2, 0, 0]):
  {==}

def p8_0004300() -> ok8([0, 0, 0, 4, 3, 0, 0]):
  {==}

def p8_0004400() -> ok8([0, 0, 0, 4, 4, 0, 0]):
  {==}

def p8_0004500() -> ok8([0, 0, 0, 4, 5, 0, 0]):
  {==}

def p8_0004600() -> ok8([0, 0, 0, 4, 6, 0, 0]):
  {==}

def p8_0004700() -> ok8([0, 0, 0, 4, 7, 0, 0]):
  {==}

def p8_0005001() -> ok8([0, 0, 0, 5, 0, 0, 1]):
  {==}

def p8_0005002() -> ok8([0, 0, 0, 5, 0, 0, 2]):
  {==}

def p8_0005003() -> ok8([0, 0, 0, 5, 0, 0, 3]):
  {==}

def p8_0005004() -> ok8([0, 0, 0, 5, 0, 0, 4]):
  {==}

def p8_0005005() -> ok8([0, 0, 0, 5, 0, 0, 5]):
  {==}

def p8_0005006() -> ok8([0, 0, 0, 5, 0, 0, 6]):
  {==}

def p8_0005007() -> ok8([0, 0, 0, 5, 0, 0, 7]):
  {==}

def p8_0005010() -> ok8([0, 0, 0, 5, 0, 1, 0]):
  {==}

def p8_0005020() -> ok8([0, 0, 0, 5, 0, 2, 0]):
  {==}

def p8_0005030() -> ok8([0, 0, 0, 5, 0, 3, 0]):
  {==}

def p8_0005040() -> ok8([0, 0, 0, 5, 0, 4, 0]):
  {==}

def p8_0005050() -> ok8([0, 0, 0, 5, 0, 5, 0]):
  {==}

def p8_0005060() -> ok8([0, 0, 0, 5, 0, 6, 0]):
  {==}

def p8_0005070() -> ok8([0, 0, 0, 5, 0, 7, 0]):
  {==}

def p8_0005100() -> ok8([0, 0, 0, 5, 1, 0, 0]):
  {==}

def p8_0005200() -> ok8([0, 0, 0, 5, 2, 0, 0]):
  {==}

def p8_0005300() -> ok8([0, 0, 0, 5, 3, 0, 0]):
  {==}

def p8_0005400() -> ok8([0, 0, 0, 5, 4, 0, 0]):
  {==}

def p8_0005500() -> ok8([0, 0, 0, 5, 5, 0, 0]):
  {==}

def p8_0005600() -> ok8([0, 0, 0, 5, 6, 0, 0]):
  {==}

def p8_0005700() -> ok8([0, 0, 0, 5, 7, 0, 0]):
  {==}

def p8_0006001() -> ok8([0, 0, 0, 6, 0, 0, 1]):
  {==}

def p8_0006002() -> ok8([0, 0, 0, 6, 0, 0, 2]):
  {==}

def p8_0006003() -> ok8([0, 0, 0, 6, 0, 0, 3]):
  {==}

def p8_0006004() -> ok8([0, 0, 0, 6, 0, 0, 4]):
  {==}

def p8_0006005() -> ok8([0, 0, 0, 6, 0, 0, 5]):
  {==}

def p8_0006006() -> ok8([0, 0, 0, 6, 0, 0, 6]):
  {==}

def p8_0006007() -> ok8([0, 0, 0, 6, 0, 0, 7]):
  {==}

def p8_0006010() -> ok8([0, 0, 0, 6, 0, 1, 0]):
  {==}

def p8_0006020() -> ok8([0, 0, 0, 6, 0, 2, 0]):
  {==}

def p8_0006030() -> ok8([0, 0, 0, 6, 0, 3, 0]):
  {==}

def p8_0006040() -> ok8([0, 0, 0, 6, 0, 4, 0]):
  {==}

def p8_0006050() -> ok8([0, 0, 0, 6, 0, 5, 0]):
  {==}

def p8_0006060() -> ok8([0, 0, 0, 6, 0, 6, 0]):
  {==}

def p8_0006070() -> ok8([0, 0, 0, 6, 0, 7, 0]):
  {==}

def p8_0006100() -> ok8([0, 0, 0, 6, 1, 0, 0]):
  {==}

def p8_0006200() -> ok8([0, 0, 0, 6, 2, 0, 0]):
  {==}

def p8_0006300() -> ok8([0, 0, 0, 6, 3, 0, 0]):
  {==}

def p8_0006400() -> ok8([0, 0, 0, 6, 4, 0, 0]):
  {==}

def p8_0006500() -> ok8([0, 0, 0, 6, 5, 0, 0]):
  {==}

def p8_0006600() -> ok8([0, 0, 0, 6, 6, 0, 0]):
  {==}

def p8_0006700() -> ok8([0, 0, 0, 6, 7, 0, 0]):
  {==}

def p8_0007001() -> ok8([0, 0, 0, 7, 0, 0, 1]):
  {==}

def p8_0007002() -> ok8([0, 0, 0, 7, 0, 0, 2]):
  {==}

def p8_0007003() -> ok8([0, 0, 0, 7, 0, 0, 3]):
  {==}

def p8_0007004() -> ok8([0, 0, 0, 7, 0, 0, 4]):
  {==}

def p8_0007005() -> ok8([0, 0, 0, 7, 0, 0, 5]):
  {==}

def p8_0007006() -> ok8([0, 0, 0, 7, 0, 0, 6]):
  {==}

def p8_0007007() -> ok8([0, 0, 0, 7, 0, 0, 7]):
  {==}

def p8_0007010() -> ok8([0, 0, 0, 7, 0, 1, 0]):
  {==}

def p8_0007020() -> ok8([0, 0, 0, 7, 0, 2, 0]):
  {==}

def p8_0007030() -> ok8([0, 0, 0, 7, 0, 3, 0]):
  {==}

def p8_0007040() -> ok8([0, 0, 0, 7, 0, 4, 0]):
  {==}

def p8_0007050() -> ok8([0, 0, 0, 7, 0, 5, 0]):
  {==}

def p8_0007060() -> ok8([0, 0, 0, 7, 0, 6, 0]):
  {==}

def p8_0007070() -> ok8([0, 0, 0, 7, 0, 7, 0]):
  {==}

def p8_0007100() -> ok8([0, 0, 0, 7, 1, 0, 0]):
  {==}

def p8_0007200() -> ok8([0, 0, 0, 7, 2, 0, 0]):
  {==}

def p8_0007300() -> ok8([0, 0, 0, 7, 3, 0, 0]):
  {==}

def p8_0007400() -> ok8([0, 0, 0, 7, 4, 0, 0]):
  {==}

def p8_0007500() -> ok8([0, 0, 0, 7, 5, 0, 0]):
  {==}

def p8_0007600() -> ok8([0, 0, 0, 7, 6, 0, 0]):
  {==}

def p8_0007700() -> ok8([0, 0, 0, 7, 7, 0, 0]):
  {==}

def p8_0010001() -> ok8([0, 0, 1, 0, 0, 0, 1]):
  {==}

def p8_0010002() -> ok8([0, 0, 1, 0, 0, 0, 2]):
  {==}

def p8_0010003() -> ok8([0, 0, 1, 0, 0, 0, 3]):
  {==}

def p8_0010004() -> ok8([0, 0, 1, 0, 0, 0, 4]):
  {==}

def p8_0010005() -> ok8([0, 0, 1, 0, 0, 0, 5]):
  {==}

def p8_0010006() -> ok8([0, 0, 1, 0, 0, 0, 6]):
  {==}

def p8_0010007() -> ok8([0, 0, 1, 0, 0, 0, 7]):
  {==}

def p8_0010010() -> ok8([0, 0, 1, 0, 0, 1, 0]):
  {==}

def p8_0010020() -> ok8([0, 0, 1, 0, 0, 2, 0]):
  {==}

def p8_0010030() -> ok8([0, 0, 1, 0, 0, 3, 0]):
  {==}

def p8_0010040() -> ok8([0, 0, 1, 0, 0, 4, 0]):
  {==}

def p8_0010050() -> ok8([0, 0, 1, 0, 0, 5, 0]):
  {==}

def p8_0010060() -> ok8([0, 0, 1, 0, 0, 6, 0]):
  {==}

def p8_0010070() -> ok8([0, 0, 1, 0, 0, 7, 0]):
  {==}

def p8_0010100() -> ok8([0, 0, 1, 0, 1, 0, 0]):
  {==}

def p8_0010200() -> ok8([0, 0, 1, 0, 2, 0, 0]):
  {==}

def p8_0010300() -> ok8([0, 0, 1, 0, 3, 0, 0]):
  {==}

def p8_0010400() -> ok8([0, 0, 1, 0, 4, 0, 0]):
  {==}

def p8_0010500() -> ok8([0, 0, 1, 0, 5, 0, 0]):
  {==}

def p8_0010600() -> ok8([0, 0, 1, 0, 6, 0, 0]):
  {==}

def p8_0010700() -> ok8([0, 0, 1, 0, 7, 0, 0]):
  {==}

def p8_0011000() -> ok8([0, 0, 1, 1, 0, 0, 0]):
  {==}

def p8_0012000() -> ok8([0, 0, 1, 2, 0, 0, 0]):
  {==}

def p8_0013000() -> ok8([0, 0, 1, 3, 0, 0, 0]):
  {==}

def p8_0014000() -> ok8([0, 0, 1, 4, 0, 0, 0]):
  {==}

def p8_0015000() -> ok8([0, 0, 1, 5, 0, 0, 0]):
  {==}

def p8_0016000() -> ok8([0, 0, 1, 6, 0, 0, 0]):
  {==}

def p8_0017000() -> ok8([0, 0, 1, 7, 0, 0, 0]):
  {==}

def p8_0020001() -> ok8([0, 0, 2, 0, 0, 0, 1]):
  {==}

def p8_0020002() -> ok8([0, 0, 2, 0, 0, 0, 2]):
  {==}

def p8_0020003() -> ok8([0, 0, 2, 0, 0, 0, 3]):
  {==}

def p8_0020004() -> ok8([0, 0, 2, 0, 0, 0, 4]):
  {==}

def p8_0020005() -> ok8([0, 0, 2, 0, 0, 0, 5]):
  {==}

def p8_0020006() -> ok8([0, 0, 2, 0, 0, 0, 6]):
  {==}

def p8_0020007() -> ok8([0, 0, 2, 0, 0, 0, 7]):
  {==}

def p8_0020010() -> ok8([0, 0, 2, 0, 0, 1, 0]):
  {==}

def p8_0020020() -> ok8([0, 0, 2, 0, 0, 2, 0]):
  {==}

def p8_0020030() -> ok8([0, 0, 2, 0, 0, 3, 0]):
  {==}

def p8_0020040() -> ok8([0, 0, 2, 0, 0, 4, 0]):
  {==}

def p8_0020050() -> ok8([0, 0, 2, 0, 0, 5, 0]):
  {==}

def p8_0020060() -> ok8([0, 0, 2, 0, 0, 6, 0]):
  {==}

def p8_0020070() -> ok8([0, 0, 2, 0, 0, 7, 0]):
  {==}

def p8_0020100() -> ok8([0, 0, 2, 0, 1, 0, 0]):
  {==}

def p8_0020200() -> ok8([0, 0, 2, 0, 2, 0, 0]):
  {==}

def p8_0020300() -> ok8([0, 0, 2, 0, 3, 0, 0]):
  {==}

def p8_0020400() -> ok8([0, 0, 2, 0, 4, 0, 0]):
  {==}

def p8_0020500() -> ok8([0, 0, 2, 0, 5, 0, 0]):
  {==}

def p8_0020600() -> ok8([0, 0, 2, 0, 6, 0, 0]):
  {==}

def p8_0020700() -> ok8([0, 0, 2, 0, 7, 0, 0]):
  {==}

def p8_0021000() -> ok8([0, 0, 2, 1, 0, 0, 0]):
  {==}

def p8_0022000() -> ok8([0, 0, 2, 2, 0, 0, 0]):
  {==}

def p8_0023000() -> ok8([0, 0, 2, 3, 0, 0, 0]):
  {==}

def p8_0024000() -> ok8([0, 0, 2, 4, 0, 0, 0]):
  {==}

def p8_0025000() -> ok8([0, 0, 2, 5, 0, 0, 0]):
  {==}

def p8_0026000() -> ok8([0, 0, 2, 6, 0, 0, 0]):
  {==}

def p8_0027000() -> ok8([0, 0, 2, 7, 0, 0, 0]):
  {==}

def p8_0030001() -> ok8([0, 0, 3, 0, 0, 0, 1]):
  {==}

def p8_0030002() -> ok8([0, 0, 3, 0, 0, 0, 2]):
  {==}

def p8_0030003() -> ok8([0, 0, 3, 0, 0, 0, 3]):
  {==}

def p8_0030004() -> ok8([0, 0, 3, 0, 0, 0, 4]):
  {==}

def p8_0030005() -> ok8([0, 0, 3, 0, 0, 0, 5]):
  {==}

def p8_0030006() -> ok8([0, 0, 3, 0, 0, 0, 6]):
  {==}

def p8_0030007() -> ok8([0, 0, 3, 0, 0, 0, 7]):
  {==}

def p8_0030010() -> ok8([0, 0, 3, 0, 0, 1, 0]):
  {==}

def p8_0030020() -> ok8([0, 0, 3, 0, 0, 2, 0]):
  {==}

def p8_0030030() -> ok8([0, 0, 3, 0, 0, 3, 0]):
  {==}

def p8_0030040() -> ok8([0, 0, 3, 0, 0, 4, 0]):
  {==}

def p8_0030050() -> ok8([0, 0, 3, 0, 0, 5, 0]):
  {==}

def p8_0030060() -> ok8([0, 0, 3, 0, 0, 6, 0]):
  {==}

def p8_0030070() -> ok8([0, 0, 3, 0, 0, 7, 0]):
  {==}

def p8_0030100() -> ok8([0, 0, 3, 0, 1, 0, 0]):
  {==}

def p8_0030200() -> ok8([0, 0, 3, 0, 2, 0, 0]):
  {==}

def p8_0030300() -> ok8([0, 0, 3, 0, 3, 0, 0]):
  {==}

def p8_0030400() -> ok8([0, 0, 3, 0, 4, 0, 0]):
  {==}

def p8_0030500() -> ok8([0, 0, 3, 0, 5, 0, 0]):
  {==}

def p8_0030600() -> ok8([0, 0, 3, 0, 6, 0, 0]):
  {==}

def p8_0030700() -> ok8([0, 0, 3, 0, 7, 0, 0]):
  {==}

def p8_0031000() -> ok8([0, 0, 3, 1, 0, 0, 0]):
  {==}

def p8_0032000() -> ok8([0, 0, 3, 2, 0, 0, 0]):
  {==}

def p8_0033000() -> ok8([0, 0, 3, 3, 0, 0, 0]):
  {==}

def p8_0034000() -> ok8([0, 0, 3, 4, 0, 0, 0]):
  {==}

def p8_0035000() -> ok8([0, 0, 3, 5, 0, 0, 0]):
  {==}

def p8_0036000() -> ok8([0, 0, 3, 6, 0, 0, 0]):
  {==}

def p8_0037000() -> ok8([0, 0, 3, 7, 0, 0, 0]):
  {==}

def p8_0040001() -> ok8([0, 0, 4, 0, 0, 0, 1]):
  {==}

def p8_0040002() -> ok8([0, 0, 4, 0, 0, 0, 2]):
  {==}

def p8_0040003() -> ok8([0, 0, 4, 0, 0, 0, 3]):
  {==}

def p8_0040004() -> ok8([0, 0, 4, 0, 0, 0, 4]):
  {==}

def p8_0040005() -> ok8([0, 0, 4, 0, 0, 0, 5]):
  {==}

def p8_0040006() -> ok8([0, 0, 4, 0, 0, 0, 6]):
  {==}

def p8_0040007() -> ok8([0, 0, 4, 0, 0, 0, 7]):
  {==}

def p8_0040010() -> ok8([0, 0, 4, 0, 0, 1, 0]):
  {==}

def p8_0040020() -> ok8([0, 0, 4, 0, 0, 2, 0]):
  {==}

def p8_0040030() -> ok8([0, 0, 4, 0, 0, 3, 0]):
  {==}

def p8_0040040() -> ok8([0, 0, 4, 0, 0, 4, 0]):
  {==}

def p8_0040050() -> ok8([0, 0, 4, 0, 0, 5, 0]):
  {==}

def p8_0040060() -> ok8([0, 0, 4, 0, 0, 6, 0]):
  {==}

def p8_0040070() -> ok8([0, 0, 4, 0, 0, 7, 0]):
  {==}

def p8_0040100() -> ok8([0, 0, 4, 0, 1, 0, 0]):
  {==}

def p8_0040200() -> ok8([0, 0, 4, 0, 2, 0, 0]):
  {==}

def p8_0040300() -> ok8([0, 0, 4, 0, 3, 0, 0]):
  {==}

def p8_0040400() -> ok8([0, 0, 4, 0, 4, 0, 0]):
  {==}

def p8_0040500() -> ok8([0, 0, 4, 0, 5, 0, 0]):
  {==}

def p8_0040600() -> ok8([0, 0, 4, 0, 6, 0, 0]):
  {==}

def p8_0040700() -> ok8([0, 0, 4, 0, 7, 0, 0]):
  {==}

def p8_0041000() -> ok8([0, 0, 4, 1, 0, 0, 0]):
  {==}

def p8_0042000() -> ok8([0, 0, 4, 2, 0, 0, 0]):
  {==}

def p8_0043000() -> ok8([0, 0, 4, 3, 0, 0, 0]):
  {==}

def p8_0044000() -> ok8([0, 0, 4, 4, 0, 0, 0]):
  {==}

def p8_0045000() -> ok8([0, 0, 4, 5, 0, 0, 0]):
  {==}

def p8_0046000() -> ok8([0, 0, 4, 6, 0, 0, 0]):
  {==}

def p8_0047000() -> ok8([0, 0, 4, 7, 0, 0, 0]):
  {==}

def p8_0050001() -> ok8([0, 0, 5, 0, 0, 0, 1]):
  {==}

def p8_0050002() -> ok8([0, 0, 5, 0, 0, 0, 2]):
  {==}

def p8_0050003() -> ok8([0, 0, 5, 0, 0, 0, 3]):
  {==}

def p8_0050004() -> ok8([0, 0, 5, 0, 0, 0, 4]):
  {==}

def p8_0050005() -> ok8([0, 0, 5, 0, 0, 0, 5]):
  {==}

def p8_0050006() -> ok8([0, 0, 5, 0, 0, 0, 6]):
  {==}

def p8_0050007() -> ok8([0, 0, 5, 0, 0, 0, 7]):
  {==}

def p8_0050010() -> ok8([0, 0, 5, 0, 0, 1, 0]):
  {==}

def p8_0050020() -> ok8([0, 0, 5, 0, 0, 2, 0]):
  {==}

def p8_0050030() -> ok8([0, 0, 5, 0, 0, 3, 0]):
  {==}

def p8_0050040() -> ok8([0, 0, 5, 0, 0, 4, 0]):
  {==}

def p8_0050050() -> ok8([0, 0, 5, 0, 0, 5, 0]):
  {==}

def p8_0050060() -> ok8([0, 0, 5, 0, 0, 6, 0]):
  {==}

def p8_0050070() -> ok8([0, 0, 5, 0, 0, 7, 0]):
  {==}

def p8_0050100() -> ok8([0, 0, 5, 0, 1, 0, 0]):
  {==}

def p8_0050200() -> ok8([0, 0, 5, 0, 2, 0, 0]):
  {==}

def p8_0050300() -> ok8([0, 0, 5, 0, 3, 0, 0]):
  {==}

def p8_0050400() -> ok8([0, 0, 5, 0, 4, 0, 0]):
  {==}

def p8_0050500() -> ok8([0, 0, 5, 0, 5, 0, 0]):
  {==}

def p8_0050600() -> ok8([0, 0, 5, 0, 6, 0, 0]):
  {==}

def p8_0050700() -> ok8([0, 0, 5, 0, 7, 0, 0]):
  {==}

def p8_0051000() -> ok8([0, 0, 5, 1, 0, 0, 0]):
  {==}

def p8_0052000() -> ok8([0, 0, 5, 2, 0, 0, 0]):
  {==}

def p8_0053000() -> ok8([0, 0, 5, 3, 0, 0, 0]):
  {==}

def p8_0054000() -> ok8([0, 0, 5, 4, 0, 0, 0]):
  {==}

def p8_0055000() -> ok8([0, 0, 5, 5, 0, 0, 0]):
  {==}

def p8_0056000() -> ok8([0, 0, 5, 6, 0, 0, 0]):
  {==}

def p8_0057000() -> ok8([0, 0, 5, 7, 0, 0, 0]):
  {==}

def p8_0060001() -> ok8([0, 0, 6, 0, 0, 0, 1]):
  {==}

def p8_0060002() -> ok8([0, 0, 6, 0, 0, 0, 2]):
  {==}

def p8_0060003() -> ok8([0, 0, 6, 0, 0, 0, 3]):
  {==}

def p8_0060004() -> ok8([0, 0, 6, 0, 0, 0, 4]):
  {==}

def p8_0060005() -> ok8([0, 0, 6, 0, 0, 0, 5]):
  {==}

def p8_0060006() -> ok8([0, 0, 6, 0, 0, 0, 6]):
  {==}

def p8_0060007() -> ok8([0, 0, 6, 0, 0, 0, 7]):
  {==}

def p8_0060010() -> ok8([0, 0, 6, 0, 0, 1, 0]):
  {==}

def p8_0060020() -> ok8([0, 0, 6, 0, 0, 2, 0]):
  {==}

def p8_0060030() -> ok8([0, 0, 6, 0, 0, 3, 0]):
  {==}

def p8_0060040() -> ok8([0, 0, 6, 0, 0, 4, 0]):
  {==}

def p8_0060050() -> ok8([0, 0, 6, 0, 0, 5, 0]):
  {==}

def p8_0060060() -> ok8([0, 0, 6, 0, 0, 6, 0]):
  {==}

def p8_0060070() -> ok8([0, 0, 6, 0, 0, 7, 0]):
  {==}

def p8_0060100() -> ok8([0, 0, 6, 0, 1, 0, 0]):
  {==}

def p8_0060200() -> ok8([0, 0, 6, 0, 2, 0, 0]):
  {==}

def p8_0060300() -> ok8([0, 0, 6, 0, 3, 0, 0]):
  {==}

def p8_0060400() -> ok8([0, 0, 6, 0, 4, 0, 0]):
  {==}

def p8_0060500() -> ok8([0, 0, 6, 0, 5, 0, 0]):
  {==}

def p8_0060600() -> ok8([0, 0, 6, 0, 6, 0, 0]):
  {==}

def p8_0060700() -> ok8([0, 0, 6, 0, 7, 0, 0]):
  {==}

def p8_0061000() -> ok8([0, 0, 6, 1, 0, 0, 0]):
  {==}

def p8_0062000() -> ok8([0, 0, 6, 2, 0, 0, 0]):
  {==}

def p8_0063000() -> ok8([0, 0, 6, 3, 0, 0, 0]):
  {==}

def p8_0064000() -> ok8([0, 0, 6, 4, 0, 0, 0]):
  {==}

def p8_0065000() -> ok8([0, 0, 6, 5, 0, 0, 0]):
  {==}

def p8_0066000() -> ok8([0, 0, 6, 6, 0, 0, 0]):
  {==}

def p8_0067000() -> ok8([0, 0, 6, 7, 0, 0, 0]):
  {==}

def p8_0070001() -> ok8([0, 0, 7, 0, 0, 0, 1]):
  {==}

def p8_0070002() -> ok8([0, 0, 7, 0, 0, 0, 2]):
  {==}

def p8_0070003() -> ok8([0, 0, 7, 0, 0, 0, 3]):
  {==}

def p8_0070004() -> ok8([0, 0, 7, 0, 0, 0, 4]):
  {==}

def p8_0070005() -> ok8([0, 0, 7, 0, 0, 0, 5]):
  {==}

def p8_0070006() -> ok8([0, 0, 7, 0, 0, 0, 6]):
  {==}

def p8_0070007() -> ok8([0, 0, 7, 0, 0, 0, 7]):
  {==}

def p8_0070010() -> ok8([0, 0, 7, 0, 0, 1, 0]):
  {==}

def p8_0070020() -> ok8([0, 0, 7, 0, 0, 2, 0]):
  {==}

def p8_0070030() -> ok8([0, 0, 7, 0, 0, 3, 0]):
  {==}

def p8_0070040() -> ok8([0, 0, 7, 0, 0, 4, 0]):
  {==}

def p8_0070050() -> ok8([0, 0, 7, 0, 0, 5, 0]):
  {==}

def p8_0070060() -> ok8([0, 0, 7, 0, 0, 6, 0]):
  {==}

def p8_0070070() -> ok8([0, 0, 7, 0, 0, 7, 0]):
  {==}

def p8_0070100() -> ok8([0, 0, 7, 0, 1, 0, 0]):
  {==}

def p8_0070200() -> ok8([0, 0, 7, 0, 2, 0, 0]):
  {==}

def p8_0070300() -> ok8([0, 0, 7, 0, 3, 0, 0]):
  {==}

def p8_0070400() -> ok8([0, 0, 7, 0, 4, 0, 0]):
  {==}

def p8_0070500() -> ok8([0, 0, 7, 0, 5, 0, 0]):
  {==}

def p8_0070600() -> ok8([0, 0, 7, 0, 6, 0, 0]):
  {==}

def p8_0070700() -> ok8([0, 0, 7, 0, 7, 0, 0]):
  {==}

def p8_0071000() -> ok8([0, 0, 7, 1, 0, 0, 0]):
  {==}

def p8_0072000() -> ok8([0, 0, 7, 2, 0, 0, 0]):
  {==}

def p8_0073000() -> ok8([0, 0, 7, 3, 0, 0, 0]):
  {==}

def p8_0074000() -> ok8([0, 0, 7, 4, 0, 0, 0]):
  {==}

def p8_0075000() -> ok8([0, 0, 7, 5, 0, 0, 0]):
  {==}

def p8_0076000() -> ok8([0, 0, 7, 6, 0, 0, 0]):
  {==}

def p8_0077000() -> ok8([0, 0, 7, 7, 0, 0, 0]):
  {==}

def p8_0100001() -> ok8([0, 1, 0, 0, 0, 0, 1]):
  {==}

def p8_0100002() -> ok8([0, 1, 0, 0, 0, 0, 2]):
  {==}

def p8_0100003() -> ok8([0, 1, 0, 0, 0, 0, 3]):
  {==}

def p8_0100004() -> ok8([0, 1, 0, 0, 0, 0, 4]):
  {==}

def p8_0100005() -> ok8([0, 1, 0, 0, 0, 0, 5]):
  {==}

def p8_0100006() -> ok8([0, 1, 0, 0, 0, 0, 6]):
  {==}

def p8_0100007() -> ok8([0, 1, 0, 0, 0, 0, 7]):
  {==}

def p8_0100010() -> ok8([0, 1, 0, 0, 0, 1, 0]):
  {==}

def p8_0100020() -> ok8([0, 1, 0, 0, 0, 2, 0]):
  {==}

def p8_0100030() -> ok8([0, 1, 0, 0, 0, 3, 0]):
  {==}

def p8_0100040() -> ok8([0, 1, 0, 0, 0, 4, 0]):
  {==}

def p8_0100050() -> ok8([0, 1, 0, 0, 0, 5, 0]):
  {==}

def p8_0100060() -> ok8([0, 1, 0, 0, 0, 6, 0]):
  {==}

def p8_0100070() -> ok8([0, 1, 0, 0, 0, 7, 0]):
  {==}

def p8_0100100() -> ok8([0, 1, 0, 0, 1, 0, 0]):
  {==}

def p8_0100200() -> ok8([0, 1, 0, 0, 2, 0, 0]):
  {==}

def p8_0100300() -> ok8([0, 1, 0, 0, 3, 0, 0]):
  {==}

def p8_0100400() -> ok8([0, 1, 0, 0, 4, 0, 0]):
  {==}

def p8_0100500() -> ok8([0, 1, 0, 0, 5, 0, 0]):
  {==}

def p8_0100600() -> ok8([0, 1, 0, 0, 6, 0, 0]):
  {==}

def p8_0100700() -> ok8([0, 1, 0, 0, 7, 0, 0]):
  {==}

def p8_0101000() -> ok8([0, 1, 0, 1, 0, 0, 0]):
  {==}

def p8_0102000() -> ok8([0, 1, 0, 2, 0, 0, 0]):
  {==}

def p8_0103000() -> ok8([0, 1, 0, 3, 0, 0, 0]):
  {==}

def p8_0104000() -> ok8([0, 1, 0, 4, 0, 0, 0]):
  {==}

def p8_0105000() -> ok8([0, 1, 0, 5, 0, 0, 0]):
  {==}

def p8_0106000() -> ok8([0, 1, 0, 6, 0, 0, 0]):
  {==}

def p8_0107000() -> ok8([0, 1, 0, 7, 0, 0, 0]):
  {==}

def p8_0110000() -> ok8([0, 1, 1, 0, 0, 0, 0]):
  {==}

def p8_0120000() -> ok8([0, 1, 2, 0, 0, 0, 0]):
  {==}

def p8_0130000() -> ok8([0, 1, 3, 0, 0, 0, 0]):
  {==}

def p8_0140000() -> ok8([0, 1, 4, 0, 0, 0, 0]):
  {==}

def p8_0150000() -> ok8([0, 1, 5, 0, 0, 0, 0]):
  {==}

def p8_0160000() -> ok8([0, 1, 6, 0, 0, 0, 0]):
  {==}

def p8_0170000() -> ok8([0, 1, 7, 0, 0, 0, 0]):
  {==}

def p8_0200001() -> ok8([0, 2, 0, 0, 0, 0, 1]):
  {==}

def p8_0200002() -> ok8([0, 2, 0, 0, 0, 0, 2]):
  {==}

def p8_0200003() -> ok8([0, 2, 0, 0, 0, 0, 3]):
  {==}

def p8_0200004() -> ok8([0, 2, 0, 0, 0, 0, 4]):
  {==}

def p8_0200005() -> ok8([0, 2, 0, 0, 0, 0, 5]):
  {==}

def p8_0200006() -> ok8([0, 2, 0, 0, 0, 0, 6]):
  {==}

def p8_0200007() -> ok8([0, 2, 0, 0, 0, 0, 7]):
  {==}

def p8_0200010() -> ok8([0, 2, 0, 0, 0, 1, 0]):
  {==}

def p8_0200020() -> ok8([0, 2, 0, 0, 0, 2, 0]):
  {==}

def p8_0200030() -> ok8([0, 2, 0, 0, 0, 3, 0]):
  {==}

def p8_0200040() -> ok8([0, 2, 0, 0, 0, 4, 0]):
  {==}

def p8_0200050() -> ok8([0, 2, 0, 0, 0, 5, 0]):
  {==}

def p8_0200060() -> ok8([0, 2, 0, 0, 0, 6, 0]):
  {==}

def p8_0200070() -> ok8([0, 2, 0, 0, 0, 7, 0]):
  {==}

def p8_0200100() -> ok8([0, 2, 0, 0, 1, 0, 0]):
  {==}

def p8_0200200() -> ok8([0, 2, 0, 0, 2, 0, 0]):
  {==}

def p8_0200300() -> ok8([0, 2, 0, 0, 3, 0, 0]):
  {==}

def p8_0200400() -> ok8([0, 2, 0, 0, 4, 0, 0]):
  {==}

def p8_0200500() -> ok8([0, 2, 0, 0, 5, 0, 0]):
  {==}

def p8_0200600() -> ok8([0, 2, 0, 0, 6, 0, 0]):
  {==}

def p8_0200700() -> ok8([0, 2, 0, 0, 7, 0, 0]):
  {==}

def p8_0201000() -> ok8([0, 2, 0, 1, 0, 0, 0]):
  {==}

def p8_0202000() -> ok8([0, 2, 0, 2, 0, 0, 0]):
  {==}

def p8_0203000() -> ok8([0, 2, 0, 3, 0, 0, 0]):
  {==}

def p8_0204000() -> ok8([0, 2, 0, 4, 0, 0, 0]):
  {==}

def p8_0205000() -> ok8([0, 2, 0, 5, 0, 0, 0]):
  {==}

def p8_0206000() -> ok8([0, 2, 0, 6, 0, 0, 0]):
  {==}

def p8_0207000() -> ok8([0, 2, 0, 7, 0, 0, 0]):
  {==}

def p8_0210000() -> ok8([0, 2, 1, 0, 0, 0, 0]):
  {==}

def p8_0220000() -> ok8([0, 2, 2, 0, 0, 0, 0]):
  {==}

def p8_0230000() -> ok8([0, 2, 3, 0, 0, 0, 0]):
  {==}

def p8_0240000() -> ok8([0, 2, 4, 0, 0, 0, 0]):
  {==}

def p8_0250000() -> ok8([0, 2, 5, 0, 0, 0, 0]):
  {==}

def p8_0260000() -> ok8([0, 2, 6, 0, 0, 0, 0]):
  {==}

def p8_0270000() -> ok8([0, 2, 7, 0, 0, 0, 0]):
  {==}

def p8_0300001() -> ok8([0, 3, 0, 0, 0, 0, 1]):
  {==}

def p8_0300002() -> ok8([0, 3, 0, 0, 0, 0, 2]):
  {==}

def p8_0300003() -> ok8([0, 3, 0, 0, 0, 0, 3]):
  {==}

def p8_0300004() -> ok8([0, 3, 0, 0, 0, 0, 4]):
  {==}

def p8_0300005() -> ok8([0, 3, 0, 0, 0, 0, 5]):
  {==}

def p8_0300006() -> ok8([0, 3, 0, 0, 0, 0, 6]):
  {==}

def p8_0300007() -> ok8([0, 3, 0, 0, 0, 0, 7]):
  {==}

def p8_0300010() -> ok8([0, 3, 0, 0, 0, 1, 0]):
  {==}

def p8_0300020() -> ok8([0, 3, 0, 0, 0, 2, 0]):
  {==}

def p8_0300030() -> ok8([0, 3, 0, 0, 0, 3, 0]):
  {==}

def p8_0300040() -> ok8([0, 3, 0, 0, 0, 4, 0]):
  {==}

def p8_0300050() -> ok8([0, 3, 0, 0, 0, 5, 0]):
  {==}

def p8_0300060() -> ok8([0, 3, 0, 0, 0, 6, 0]):
  {==}

def p8_0300070() -> ok8([0, 3, 0, 0, 0, 7, 0]):
  {==}

def p8_0300100() -> ok8([0, 3, 0, 0, 1, 0, 0]):
  {==}

def p8_0300200() -> ok8([0, 3, 0, 0, 2, 0, 0]):
  {==}

def p8_0300300() -> ok8([0, 3, 0, 0, 3, 0, 0]):
  {==}

def p8_0300400() -> ok8([0, 3, 0, 0, 4, 0, 0]):
  {==}

def p8_0300500() -> ok8([0, 3, 0, 0, 5, 0, 0]):
  {==}

def p8_0300600() -> ok8([0, 3, 0, 0, 6, 0, 0]):
  {==}

def p8_0300700() -> ok8([0, 3, 0, 0, 7, 0, 0]):
  {==}

def p8_0301000() -> ok8([0, 3, 0, 1, 0, 0, 0]):
  {==}

def p8_0302000() -> ok8([0, 3, 0, 2, 0, 0, 0]):
  {==}

def p8_0303000() -> ok8([0, 3, 0, 3, 0, 0, 0]):
  {==}

def p8_0304000() -> ok8([0, 3, 0, 4, 0, 0, 0]):
  {==}

def p8_0305000() -> ok8([0, 3, 0, 5, 0, 0, 0]):
  {==}

def p8_0306000() -> ok8([0, 3, 0, 6, 0, 0, 0]):
  {==}

def p8_0307000() -> ok8([0, 3, 0, 7, 0, 0, 0]):
  {==}

def p8_0310000() -> ok8([0, 3, 1, 0, 0, 0, 0]):
  {==}

def p8_0320000() -> ok8([0, 3, 2, 0, 0, 0, 0]):
  {==}

def p8_0330000() -> ok8([0, 3, 3, 0, 0, 0, 0]):
  {==}

def p8_0340000() -> ok8([0, 3, 4, 0, 0, 0, 0]):
  {==}

def p8_0350000() -> ok8([0, 3, 5, 0, 0, 0, 0]):
  {==}

def p8_0360000() -> ok8([0, 3, 6, 0, 0, 0, 0]):
  {==}

def p8_0370000() -> ok8([0, 3, 7, 0, 0, 0, 0]):
  {==}

def p8_0400001() -> ok8([0, 4, 0, 0, 0, 0, 1]):
  {==}

def p8_0400002() -> ok8([0, 4, 0, 0, 0, 0, 2]):
  {==}

def p8_0400003() -> ok8([0, 4, 0, 0, 0, 0, 3]):
  {==}

def p8_0400004() -> ok8([0, 4, 0, 0, 0, 0, 4]):
  {==}

def p8_0400005() -> ok8([0, 4, 0, 0, 0, 0, 5]):
  {==}

def p8_0400006() -> ok8([0, 4, 0, 0, 0, 0, 6]):
  {==}

def p8_0400007() -> ok8([0, 4, 0, 0, 0, 0, 7]):
  {==}

def p8_0400010() -> ok8([0, 4, 0, 0, 0, 1, 0]):
  {==}

def p8_0400020() -> ok8([0, 4, 0, 0, 0, 2, 0]):
  {==}

def p8_0400030() -> ok8([0, 4, 0, 0, 0, 3, 0]):
  {==}

def p8_0400040() -> ok8([0, 4, 0, 0, 0, 4, 0]):
  {==}

def p8_0400050() -> ok8([0, 4, 0, 0, 0, 5, 0]):
  {==}

def p8_0400060() -> ok8([0, 4, 0, 0, 0, 6, 0]):
  {==}

def p8_0400070() -> ok8([0, 4, 0, 0, 0, 7, 0]):
  {==}

def p8_0400100() -> ok8([0, 4, 0, 0, 1, 0, 0]):
  {==}

def p8_0400200() -> ok8([0, 4, 0, 0, 2, 0, 0]):
  {==}

def p8_0400300() -> ok8([0, 4, 0, 0, 3, 0, 0]):
  {==}

def p8_0400400() -> ok8([0, 4, 0, 0, 4, 0, 0]):
  {==}

def p8_0400500() -> ok8([0, 4, 0, 0, 5, 0, 0]):
  {==}

def p8_0400600() -> ok8([0, 4, 0, 0, 6, 0, 0]):
  {==}

def p8_0400700() -> ok8([0, 4, 0, 0, 7, 0, 0]):
  {==}

def p8_0401000() -> ok8([0, 4, 0, 1, 0, 0, 0]):
  {==}

def p8_0402000() -> ok8([0, 4, 0, 2, 0, 0, 0]):
  {==}

def p8_0403000() -> ok8([0, 4, 0, 3, 0, 0, 0]):
  {==}

def p8_0404000() -> ok8([0, 4, 0, 4, 0, 0, 0]):
  {==}

def p8_0405000() -> ok8([0, 4, 0, 5, 0, 0, 0]):
  {==}

def p8_0406000() -> ok8([0, 4, 0, 6, 0, 0, 0]):
  {==}

def p8_0407000() -> ok8([0, 4, 0, 7, 0, 0, 0]):
  {==}

def p8_0410000() -> ok8([0, 4, 1, 0, 0, 0, 0]):
  {==}

def p8_0420000() -> ok8([0, 4, 2, 0, 0, 0, 0]):
  {==}

def p8_0430000() -> ok8([0, 4, 3, 0, 0, 0, 0]):
  {==}

def p8_0440000() -> ok8([0, 4, 4, 0, 0, 0, 0]):
  {==}

def p8_0450000() -> ok8([0, 4, 5, 0, 0, 0, 0]):
  {==}

def p8_0460000() -> ok8([0, 4, 6, 0, 0, 0, 0]):
  {==}

def p8_0470000() -> ok8([0, 4, 7, 0, 0, 0, 0]):
  {==}

def p8_0500001() -> ok8([0, 5, 0, 0, 0, 0, 1]):
  {==}

def p8_0500002() -> ok8([0, 5, 0, 0, 0, 0, 2]):
  {==}

def p8_0500003() -> ok8([0, 5, 0, 0, 0, 0, 3]):
  {==}

def p8_0500004() -> ok8([0, 5, 0, 0, 0, 0, 4]):
  {==}

def p8_0500005() -> ok8([0, 5, 0, 0, 0, 0, 5]):
  {==}

def p8_0500006() -> ok8([0, 5, 0, 0, 0, 0, 6]):
  {==}

def p8_0500007() -> ok8([0, 5, 0, 0, 0, 0, 7]):
  {==}

def p8_0500010() -> ok8([0, 5, 0, 0, 0, 1, 0]):
  {==}

def p8_0500020() -> ok8([0, 5, 0, 0, 0, 2, 0]):
  {==}

def p8_0500030() -> ok8([0, 5, 0, 0, 0, 3, 0]):
  {==}

def p8_0500040() -> ok8([0, 5, 0, 0, 0, 4, 0]):
  {==}

def p8_0500050() -> ok8([0, 5, 0, 0, 0, 5, 0]):
  {==}

def p8_0500060() -> ok8([0, 5, 0, 0, 0, 6, 0]):
  {==}

def p8_0500070() -> ok8([0, 5, 0, 0, 0, 7, 0]):
  {==}

def p8_0500100() -> ok8([0, 5, 0, 0, 1, 0, 0]):
  {==}

def p8_0500200() -> ok8([0, 5, 0, 0, 2, 0, 0]):
  {==}

def p8_0500300() -> ok8([0, 5, 0, 0, 3, 0, 0]):
  {==}

def p8_0500400() -> ok8([0, 5, 0, 0, 4, 0, 0]):
  {==}

def p8_0500500() -> ok8([0, 5, 0, 0, 5, 0, 0]):
  {==}

def p8_0500600() -> ok8([0, 5, 0, 0, 6, 0, 0]):
  {==}

def p8_0500700() -> ok8([0, 5, 0, 0, 7, 0, 0]):
  {==}

def p8_0501000() -> ok8([0, 5, 0, 1, 0, 0, 0]):
  {==}

def p8_0502000() -> ok8([0, 5, 0, 2, 0, 0, 0]):
  {==}

def p8_0503000() -> ok8([0, 5, 0, 3, 0, 0, 0]):
  {==}

def p8_0504000() -> ok8([0, 5, 0, 4, 0, 0, 0]):
  {==}

def p8_0505000() -> ok8([0, 5, 0, 5, 0, 0, 0]):
  {==}

def p8_0506000() -> ok8([0, 5, 0, 6, 0, 0, 0]):
  {==}

def p8_0507000() -> ok8([0, 5, 0, 7, 0, 0, 0]):
  {==}

def p8_0510000() -> ok8([0, 5, 1, 0, 0, 0, 0]):
  {==}

def p8_0520000() -> ok8([0, 5, 2, 0, 0, 0, 0]):
  {==}

def p8_0530000() -> ok8([0, 5, 3, 0, 0, 0, 0]):
  {==}

def p8_0540000() -> ok8([0, 5, 4, 0, 0, 0, 0]):
  {==}

def p8_0550000() -> ok8([0, 5, 5, 0, 0, 0, 0]):
  {==}

def p8_0560000() -> ok8([0, 5, 6, 0, 0, 0, 0]):
  {==}

def p8_0570000() -> ok8([0, 5, 7, 0, 0, 0, 0]):
  {==}

def p8_0600001() -> ok8([0, 6, 0, 0, 0, 0, 1]):
  {==}

def p8_0600002() -> ok8([0, 6, 0, 0, 0, 0, 2]):
  {==}

def p8_0600003() -> ok8([0, 6, 0, 0, 0, 0, 3]):
  {==}

def p8_0600004() -> ok8([0, 6, 0, 0, 0, 0, 4]):
  {==}

def p8_0600005() -> ok8([0, 6, 0, 0, 0, 0, 5]):
  {==}

def p8_0600006() -> ok8([0, 6, 0, 0, 0, 0, 6]):
  {==}

def p8_0600007() -> ok8([0, 6, 0, 0, 0, 0, 7]):
  {==}

def p8_0600010() -> ok8([0, 6, 0, 0, 0, 1, 0]):
  {==}

def p8_0600020() -> ok8([0, 6, 0, 0, 0, 2, 0]):
  {==}

def p8_0600030() -> ok8([0, 6, 0, 0, 0, 3, 0]):
  {==}

def p8_0600040() -> ok8([0, 6, 0, 0, 0, 4, 0]):
  {==}

def p8_0600050() -> ok8([0, 6, 0, 0, 0, 5, 0]):
  {==}

def p8_0600060() -> ok8([0, 6, 0, 0, 0, 6, 0]):
  {==}

def p8_0600070() -> ok8([0, 6, 0, 0, 0, 7, 0]):
  {==}

def p8_0600100() -> ok8([0, 6, 0, 0, 1, 0, 0]):
  {==}

def p8_0600200() -> ok8([0, 6, 0, 0, 2, 0, 0]):
  {==}

def p8_0600300() -> ok8([0, 6, 0, 0, 3, 0, 0]):
  {==}

def p8_0600400() -> ok8([0, 6, 0, 0, 4, 0, 0]):
  {==}

def p8_0600500() -> ok8([0, 6, 0, 0, 5, 0, 0]):
  {==}

def p8_0600600() -> ok8([0, 6, 0, 0, 6, 0, 0]):
  {==}

def p8_0600700() -> ok8([0, 6, 0, 0, 7, 0, 0]):
  {==}

def p8_0601000() -> ok8([0, 6, 0, 1, 0, 0, 0]):
  {==}

def p8_0602000() -> ok8([0, 6, 0, 2, 0, 0, 0]):
  {==}

def p8_0603000() -> ok8([0, 6, 0, 3, 0, 0, 0]):
  {==}

def p8_0604000() -> ok8([0, 6, 0, 4, 0, 0, 0]):
  {==}

def p8_0605000() -> ok8([0, 6, 0, 5, 0, 0, 0]):
  {==}

def p8_0606000() -> ok8([0, 6, 0, 6, 0, 0, 0]):
  {==}

def p8_0607000() -> ok8([0, 6, 0, 7, 0, 0, 0]):
  {==}

def p8_0610000() -> ok8([0, 6, 1, 0, 0, 0, 0]):
  {==}

def p8_0620000() -> ok8([0, 6, 2, 0, 0, 0, 0]):
  {==}

def p8_0630000() -> ok8([0, 6, 3, 0, 0, 0, 0]):
  {==}

def p8_0640000() -> ok8([0, 6, 4, 0, 0, 0, 0]):
  {==}

def p8_0650000() -> ok8([0, 6, 5, 0, 0, 0, 0]):
  {==}

def p8_0660000() -> ok8([0, 6, 6, 0, 0, 0, 0]):
  {==}

def p8_0670000() -> ok8([0, 6, 7, 0, 0, 0, 0]):
  {==}

def p8_0700001() -> ok8([0, 7, 0, 0, 0, 0, 1]):
  {==}

def p8_0700002() -> ok8([0, 7, 0, 0, 0, 0, 2]):
  {==}

def p8_0700003() -> ok8([0, 7, 0, 0, 0, 0, 3]):
  {==}

def p8_0700004() -> ok8([0, 7, 0, 0, 0, 0, 4]):
  {==}

def p8_0700005() -> ok8([0, 7, 0, 0, 0, 0, 5]):
  {==}

def p8_0700006() -> ok8([0, 7, 0, 0, 0, 0, 6]):
  {==}

def p8_0700007() -> ok8([0, 7, 0, 0, 0, 0, 7]):
  {==}

def p8_0700010() -> ok8([0, 7, 0, 0, 0, 1, 0]):
  {==}

def p8_0700020() -> ok8([0, 7, 0, 0, 0, 2, 0]):
  {==}

def p8_0700030() -> ok8([0, 7, 0, 0, 0, 3, 0]):
  {==}

def p8_0700040() -> ok8([0, 7, 0, 0, 0, 4, 0]):
  {==}

def p8_0700050() -> ok8([0, 7, 0, 0, 0, 5, 0]):
  {==}

def p8_0700060() -> ok8([0, 7, 0, 0, 0, 6, 0]):
  {==}

def p8_0700070() -> ok8([0, 7, 0, 0, 0, 7, 0]):
  {==}

def p8_0700100() -> ok8([0, 7, 0, 0, 1, 0, 0]):
  {==}

def p8_0700200() -> ok8([0, 7, 0, 0, 2, 0, 0]):
  {==}

def p8_0700300() -> ok8([0, 7, 0, 0, 3, 0, 0]):
  {==}

def p8_0700400() -> ok8([0, 7, 0, 0, 4, 0, 0]):
  {==}

def p8_0700500() -> ok8([0, 7, 0, 0, 5, 0, 0]):
  {==}

def p8_0700600() -> ok8([0, 7, 0, 0, 6, 0, 0]):
  {==}

def p8_0700700() -> ok8([0, 7, 0, 0, 7, 0, 0]):
  {==}

def p8_0701000() -> ok8([0, 7, 0, 1, 0, 0, 0]):
  {==}

def p8_0702000() -> ok8([0, 7, 0, 2, 0, 0, 0]):
  {==}

def p8_0703000() -> ok8([0, 7, 0, 3, 0, 0, 0]):
  {==}

def p8_0704000() -> ok8([0, 7, 0, 4, 0, 0, 0]):
  {==}

def p8_0705000() -> ok8([0, 7, 0, 5, 0, 0, 0]):
  {==}

def p8_0706000() -> ok8([0, 7, 0, 6, 0, 0, 0]):
  {==}

def p8_0707000() -> ok8([0, 7, 0, 7, 0, 0, 0]):
  {==}

def p8_0710000() -> ok8([0, 7, 1, 0, 0, 0, 0]):
  {==}

def p8_0720000() -> ok8([0, 7, 2, 0, 0, 0, 0]):
  {==}

def p8_0730000() -> ok8([0, 7, 3, 0, 0, 0, 0]):
  {==}

def p8_0740000() -> ok8([0, 7, 4, 0, 0, 0, 0]):
  {==}

def p8_0750000() -> ok8([0, 7, 5, 0, 0, 0, 0]):
  {==}

def p8_0760000() -> ok8([0, 7, 6, 0, 0, 0, 0]):
  {==}

def p8_0770000() -> ok8([0, 7, 7, 0, 0, 0, 0]):
  {==}

def p8_1000001() -> ok8([1, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_1000002() -> ok8([1, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_1000003() -> ok8([1, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_1000004() -> ok8([1, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_1000005() -> ok8([1, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_1000006() -> ok8([1, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_1000007() -> ok8([1, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_1000010() -> ok8([1, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_1000020() -> ok8([1, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_1000030() -> ok8([1, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_1000040() -> ok8([1, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_1000050() -> ok8([1, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_1000060() -> ok8([1, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_1000070() -> ok8([1, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_1000100() -> ok8([1, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_1000200() -> ok8([1, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_1000300() -> ok8([1, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_1000400() -> ok8([1, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_1000500() -> ok8([1, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_1000600() -> ok8([1, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_1000700() -> ok8([1, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_1001000() -> ok8([1, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_1002000() -> ok8([1, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_1003000() -> ok8([1, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_1004000() -> ok8([1, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_1005000() -> ok8([1, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_1006000() -> ok8([1, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_1007000() -> ok8([1, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_1010000() -> ok8([1, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_1020000() -> ok8([1, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_1030000() -> ok8([1, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_1040000() -> ok8([1, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_1050000() -> ok8([1, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_1060000() -> ok8([1, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_1070000() -> ok8([1, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_1100000() -> ok8([1, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_1200000() -> ok8([1, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_1300000() -> ok8([1, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_1400000() -> ok8([1, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_1500000() -> ok8([1, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_1600000() -> ok8([1, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_1700000() -> ok8([1, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_2000001() -> ok8([2, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_2000002() -> ok8([2, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_2000003() -> ok8([2, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_2000004() -> ok8([2, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_2000005() -> ok8([2, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_2000006() -> ok8([2, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_2000007() -> ok8([2, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_2000010() -> ok8([2, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_2000020() -> ok8([2, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_2000030() -> ok8([2, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_2000040() -> ok8([2, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_2000050() -> ok8([2, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_2000060() -> ok8([2, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_2000070() -> ok8([2, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_2000100() -> ok8([2, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_2000200() -> ok8([2, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_2000300() -> ok8([2, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_2000400() -> ok8([2, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_2000500() -> ok8([2, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_2000600() -> ok8([2, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_2000700() -> ok8([2, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_2001000() -> ok8([2, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_2002000() -> ok8([2, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_2003000() -> ok8([2, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_2004000() -> ok8([2, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_2005000() -> ok8([2, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_2006000() -> ok8([2, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_2007000() -> ok8([2, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_2010000() -> ok8([2, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_2020000() -> ok8([2, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_2030000() -> ok8([2, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_2040000() -> ok8([2, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_2050000() -> ok8([2, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_2060000() -> ok8([2, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_2070000() -> ok8([2, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_2100000() -> ok8([2, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_2200000() -> ok8([2, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_2300000() -> ok8([2, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_2400000() -> ok8([2, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_2500000() -> ok8([2, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_2600000() -> ok8([2, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_2700000() -> ok8([2, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_3000001() -> ok8([3, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_3000002() -> ok8([3, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_3000003() -> ok8([3, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_3000004() -> ok8([3, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_3000005() -> ok8([3, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_3000006() -> ok8([3, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_3000007() -> ok8([3, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_3000010() -> ok8([3, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_3000020() -> ok8([3, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_3000030() -> ok8([3, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_3000040() -> ok8([3, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_3000050() -> ok8([3, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_3000060() -> ok8([3, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_3000070() -> ok8([3, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_3000100() -> ok8([3, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_3000200() -> ok8([3, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_3000300() -> ok8([3, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_3000400() -> ok8([3, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_3000500() -> ok8([3, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_3000600() -> ok8([3, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_3000700() -> ok8([3, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_3001000() -> ok8([3, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_3002000() -> ok8([3, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_3003000() -> ok8([3, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_3004000() -> ok8([3, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_3005000() -> ok8([3, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_3006000() -> ok8([3, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_3007000() -> ok8([3, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_3010000() -> ok8([3, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_3020000() -> ok8([3, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_3030000() -> ok8([3, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_3040000() -> ok8([3, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_3050000() -> ok8([3, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_3060000() -> ok8([3, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_3070000() -> ok8([3, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_3100000() -> ok8([3, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_3200000() -> ok8([3, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_3300000() -> ok8([3, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_3400000() -> ok8([3, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_3500000() -> ok8([3, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_3600000() -> ok8([3, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_3700000() -> ok8([3, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_4000001() -> ok8([4, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_4000002() -> ok8([4, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_4000003() -> ok8([4, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_4000004() -> ok8([4, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_4000005() -> ok8([4, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_4000006() -> ok8([4, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_4000007() -> ok8([4, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_4000010() -> ok8([4, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_4000020() -> ok8([4, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_4000030() -> ok8([4, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_4000040() -> ok8([4, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_4000050() -> ok8([4, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_4000060() -> ok8([4, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_4000070() -> ok8([4, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_4000100() -> ok8([4, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_4000200() -> ok8([4, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_4000300() -> ok8([4, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_4000400() -> ok8([4, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_4000500() -> ok8([4, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_4000600() -> ok8([4, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_4000700() -> ok8([4, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_4001000() -> ok8([4, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_4002000() -> ok8([4, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_4003000() -> ok8([4, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_4004000() -> ok8([4, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_4005000() -> ok8([4, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_4006000() -> ok8([4, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_4007000() -> ok8([4, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_4010000() -> ok8([4, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_4020000() -> ok8([4, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_4030000() -> ok8([4, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_4040000() -> ok8([4, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_4050000() -> ok8([4, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_4060000() -> ok8([4, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_4070000() -> ok8([4, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_4100000() -> ok8([4, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_4200000() -> ok8([4, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_4300000() -> ok8([4, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_4400000() -> ok8([4, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_4500000() -> ok8([4, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_4600000() -> ok8([4, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_4700000() -> ok8([4, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_5000001() -> ok8([5, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_5000002() -> ok8([5, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_5000003() -> ok8([5, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_5000004() -> ok8([5, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_5000005() -> ok8([5, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_5000006() -> ok8([5, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_5000007() -> ok8([5, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_5000010() -> ok8([5, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_5000020() -> ok8([5, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_5000030() -> ok8([5, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_5000040() -> ok8([5, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_5000050() -> ok8([5, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_5000060() -> ok8([5, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_5000070() -> ok8([5, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_5000100() -> ok8([5, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_5000200() -> ok8([5, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_5000300() -> ok8([5, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_5000400() -> ok8([5, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_5000500() -> ok8([5, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_5000600() -> ok8([5, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_5000700() -> ok8([5, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_5001000() -> ok8([5, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_5002000() -> ok8([5, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_5003000() -> ok8([5, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_5004000() -> ok8([5, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_5005000() -> ok8([5, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_5006000() -> ok8([5, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_5007000() -> ok8([5, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_5010000() -> ok8([5, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_5020000() -> ok8([5, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_5030000() -> ok8([5, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_5040000() -> ok8([5, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_5050000() -> ok8([5, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_5060000() -> ok8([5, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_5070000() -> ok8([5, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_5100000() -> ok8([5, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_5200000() -> ok8([5, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_5300000() -> ok8([5, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_5400000() -> ok8([5, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_5500000() -> ok8([5, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_5600000() -> ok8([5, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_5700000() -> ok8([5, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_6000001() -> ok8([6, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_6000002() -> ok8([6, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_6000003() -> ok8([6, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_6000004() -> ok8([6, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_6000005() -> ok8([6, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_6000006() -> ok8([6, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_6000007() -> ok8([6, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_6000010() -> ok8([6, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_6000020() -> ok8([6, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_6000030() -> ok8([6, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_6000040() -> ok8([6, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_6000050() -> ok8([6, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_6000060() -> ok8([6, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_6000070() -> ok8([6, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_6000100() -> ok8([6, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_6000200() -> ok8([6, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_6000300() -> ok8([6, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_6000400() -> ok8([6, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_6000500() -> ok8([6, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_6000600() -> ok8([6, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_6000700() -> ok8([6, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_6001000() -> ok8([6, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_6002000() -> ok8([6, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_6003000() -> ok8([6, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_6004000() -> ok8([6, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_6005000() -> ok8([6, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_6006000() -> ok8([6, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_6007000() -> ok8([6, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_6010000() -> ok8([6, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_6020000() -> ok8([6, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_6030000() -> ok8([6, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_6040000() -> ok8([6, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_6050000() -> ok8([6, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_6060000() -> ok8([6, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_6070000() -> ok8([6, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_6100000() -> ok8([6, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_6200000() -> ok8([6, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_6300000() -> ok8([6, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_6400000() -> ok8([6, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_6500000() -> ok8([6, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_6600000() -> ok8([6, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_6700000() -> ok8([6, 7, 0, 0, 0, 0, 0]):
  {==}

def p8_7000001() -> ok8([7, 0, 0, 0, 0, 0, 1]):
  {==}

def p8_7000002() -> ok8([7, 0, 0, 0, 0, 0, 2]):
  {==}

def p8_7000003() -> ok8([7, 0, 0, 0, 0, 0, 3]):
  {==}

def p8_7000004() -> ok8([7, 0, 0, 0, 0, 0, 4]):
  {==}

def p8_7000005() -> ok8([7, 0, 0, 0, 0, 0, 5]):
  {==}

def p8_7000006() -> ok8([7, 0, 0, 0, 0, 0, 6]):
  {==}

def p8_7000007() -> ok8([7, 0, 0, 0, 0, 0, 7]):
  {==}

def p8_7000010() -> ok8([7, 0, 0, 0, 0, 1, 0]):
  {==}

def p8_7000020() -> ok8([7, 0, 0, 0, 0, 2, 0]):
  {==}

def p8_7000030() -> ok8([7, 0, 0, 0, 0, 3, 0]):
  {==}

def p8_7000040() -> ok8([7, 0, 0, 0, 0, 4, 0]):
  {==}

def p8_7000050() -> ok8([7, 0, 0, 0, 0, 5, 0]):
  {==}

def p8_7000060() -> ok8([7, 0, 0, 0, 0, 6, 0]):
  {==}

def p8_7000070() -> ok8([7, 0, 0, 0, 0, 7, 0]):
  {==}

def p8_7000100() -> ok8([7, 0, 0, 0, 1, 0, 0]):
  {==}

def p8_7000200() -> ok8([7, 0, 0, 0, 2, 0, 0]):
  {==}

def p8_7000300() -> ok8([7, 0, 0, 0, 3, 0, 0]):
  {==}

def p8_7000400() -> ok8([7, 0, 0, 0, 4, 0, 0]):
  {==}

def p8_7000500() -> ok8([7, 0, 0, 0, 5, 0, 0]):
  {==}

def p8_7000600() -> ok8([7, 0, 0, 0, 6, 0, 0]):
  {==}

def p8_7000700() -> ok8([7, 0, 0, 0, 7, 0, 0]):
  {==}

def p8_7001000() -> ok8([7, 0, 0, 1, 0, 0, 0]):
  {==}

def p8_7002000() -> ok8([7, 0, 0, 2, 0, 0, 0]):
  {==}

def p8_7003000() -> ok8([7, 0, 0, 3, 0, 0, 0]):
  {==}

def p8_7004000() -> ok8([7, 0, 0, 4, 0, 0, 0]):
  {==}

def p8_7005000() -> ok8([7, 0, 0, 5, 0, 0, 0]):
  {==}

def p8_7006000() -> ok8([7, 0, 0, 6, 0, 0, 0]):
  {==}

def p8_7007000() -> ok8([7, 0, 0, 7, 0, 0, 0]):
  {==}

def p8_7010000() -> ok8([7, 0, 1, 0, 0, 0, 0]):
  {==}

def p8_7020000() -> ok8([7, 0, 2, 0, 0, 0, 0]):
  {==}

def p8_7030000() -> ok8([7, 0, 3, 0, 0, 0, 0]):
  {==}

def p8_7040000() -> ok8([7, 0, 4, 0, 0, 0, 0]):
  {==}

def p8_7050000() -> ok8([7, 0, 5, 0, 0, 0, 0]):
  {==}

def p8_7060000() -> ok8([7, 0, 6, 0, 0, 0, 0]):
  {==}

def p8_7070000() -> ok8([7, 0, 7, 0, 0, 0, 0]):
  {==}

def p8_7100000() -> ok8([7, 1, 0, 0, 0, 0, 0]):
  {==}

def p8_7200000() -> ok8([7, 2, 0, 0, 0, 0, 0]):
  {==}

def p8_7300000() -> ok8([7, 3, 0, 0, 0, 0, 0]):
  {==}

def p8_7400000() -> ok8([7, 4, 0, 0, 0, 0, 0]):
  {==}

def p8_7500000() -> ok8([7, 5, 0, 0, 0, 0, 0]):
  {==}

def p8_7600000() -> ok8([7, 6, 0, 0, 0, 0, 0]):
  {==}

def p8_7700000() -> ok8([7, 7, 0, 0, 0, 0, 0]):
  {==}

# The indexes, for each pair of values

def q8_0_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 0) : ok8(_)
          %xr8_0_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_0_2(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_0_3(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_0_4(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_0_5(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_0_6(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_0_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_1_1(0, 0) : ok8(_)
          %xr8_0_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_1_3(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_1_4(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_1_5(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_1_6(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_1_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_2_1(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_2_2(0, 0) : ok8(_)
          %xr8_0_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_2_4(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_2_5(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_2_6(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_2_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_3_1(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_3_2(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_3_3(0, 0) : ok8(_)
          %xr8_0_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_3_5(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_3_6(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_3_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_4_1(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_4_2(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_4_3(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_4_4(0, 0) : ok8(_)
          %xr8_0_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_4_6(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_4_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_5_1(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_5_2(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_5_3(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_5_4(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_5_5(0, 0) : ok8(_)
          %xr8_0_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_5_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_6_1(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_6_2(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_6_3(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_6_4(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_6_5(0, 0, ev8_0(), ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_6_6(0, 0) : ok8(_)
          %xr8_0_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(0, l, 0, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 0, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 0, l, 0) : ok8(_)
          p8_0000000()

def q8_0_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 1) : ok8(_)
          %xr8_0_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_0_2(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_0_3(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_0_4(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_0_5(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_0_6(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_0_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_1_1(0, 1) : ok8(_)
          %xr8_0_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_1_3(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_1_4(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_1_5(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_1_6(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_1_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_2_1(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_2_2(0, 1) : ok8(_)
          %xr8_0_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_2_4(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_2_5(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_2_6(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_2_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_3_1(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_3_2(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_3_3(0, 1) : ok8(_)
          %xr8_0_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_3_5(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_3_6(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_3_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_4_1(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_4_2(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_4_3(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_4_4(0, 1) : ok8(_)
          %xr8_0_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_4_6(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_4_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_5_1(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_5_2(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_5_3(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_5_4(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_5_5(0, 1) : ok8(_)
          %xr8_0_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_5_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_6_1(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_6_2(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_6_3(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_6_4(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_6_5(0, 1, ev8_0(), ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_6_6(0, 1) : ok8(_)
          %xr8_0_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(0, l, 1, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 0, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 0, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 0, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 0, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 0, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 0, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 0, l, 1) : ok8(_)
          p8_0000000()

def q8_0_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 2) : ok8(_)
          %xr8_0_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_0_2(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_0_3(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_0_4(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_0_5(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_0_6(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_0_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_1_1(0, 2) : ok8(_)
          %xr8_0_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_1_3(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_1_4(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_1_5(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_1_6(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_1_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_2_1(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_2_2(0, 2) : ok8(_)
          %xr8_0_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_2_4(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_2_5(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_2_6(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_2_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_3_1(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_3_2(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_3_3(0, 2) : ok8(_)
          %xr8_0_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_3_5(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_3_6(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_3_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_4_1(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_4_2(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_4_3(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_4_4(0, 2) : ok8(_)
          %xr8_0_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_4_6(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_4_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_5_1(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_5_2(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_5_3(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_5_4(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_5_5(0, 2) : ok8(_)
          %xr8_0_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_5_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_6_1(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_6_2(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_6_3(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_6_4(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_6_5(0, 2, ev8_0(), ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_6_6(0, 2) : ok8(_)
          %xr8_0_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(0, l, 2, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 0, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 0, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 0, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 0, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 0, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 0, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 0, l, 2) : ok8(_)
          p8_0000000()

def q8_0_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 3) : ok8(_)
          %xr8_0_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_0_2(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_0_3(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_0_4(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_0_5(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_0_6(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_0_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_1_1(0, 3) : ok8(_)
          %xr8_0_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_1_3(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_1_4(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_1_5(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_1_6(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_1_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_2_1(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_2_2(0, 3) : ok8(_)
          %xr8_0_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_2_4(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_2_5(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_2_6(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_2_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_3_1(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_3_2(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_3_3(0, 3) : ok8(_)
          %xr8_0_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_3_5(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_3_6(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_3_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_4_1(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_4_2(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_4_3(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_4_4(0, 3) : ok8(_)
          %xr8_0_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_4_6(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_4_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_5_1(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_5_2(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_5_3(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_5_4(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_5_5(0, 3) : ok8(_)
          %xr8_0_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_5_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_6_1(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_6_2(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_6_3(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_6_4(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_6_5(0, 3, ev8_0(), ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_6_6(0, 3) : ok8(_)
          %xr8_0_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(0, l, 3, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 0, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 0, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 0, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 0, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 0, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 0, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 0, l, 3) : ok8(_)
          p8_0000000()

def q8_0_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 4) : ok8(_)
          %xr8_0_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_0_2(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_0_3(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_0_4(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_0_5(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_0_6(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_0_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_1_1(0, 4) : ok8(_)
          %xr8_0_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_1_3(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_1_4(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_1_5(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_1_6(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_1_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_2_1(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_2_2(0, 4) : ok8(_)
          %xr8_0_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_2_4(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_2_5(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_2_6(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_2_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_3_1(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_3_2(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_3_3(0, 4) : ok8(_)
          %xr8_0_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_3_5(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_3_6(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_3_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_4_1(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_4_2(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_4_3(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_4_4(0, 4) : ok8(_)
          %xr8_0_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_4_6(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_4_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_5_1(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_5_2(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_5_3(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_5_4(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_5_5(0, 4) : ok8(_)
          %xr8_0_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_5_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_6_1(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_6_2(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_6_3(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_6_4(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_6_5(0, 4, ev8_0(), ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_6_6(0, 4) : ok8(_)
          %xr8_0_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(0, l, 4, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 0, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 0, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 0, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 0, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 0, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 0, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 0, l, 4) : ok8(_)
          p8_0000000()

def q8_0_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 5) : ok8(_)
          %xr8_0_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_0_2(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_0_3(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_0_4(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_0_5(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_0_6(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_0_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_1_1(0, 5) : ok8(_)
          %xr8_0_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_1_3(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_1_4(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_1_5(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_1_6(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_1_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_2_1(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_2_2(0, 5) : ok8(_)
          %xr8_0_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_2_4(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_2_5(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_2_6(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_2_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_3_1(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_3_2(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_3_3(0, 5) : ok8(_)
          %xr8_0_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_3_5(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_3_6(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_3_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_4_1(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_4_2(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_4_3(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_4_4(0, 5) : ok8(_)
          %xr8_0_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_4_6(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_4_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_5_1(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_5_2(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_5_3(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_5_4(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_5_5(0, 5) : ok8(_)
          %xr8_0_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_5_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_6_1(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_6_2(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_6_3(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_6_4(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_6_5(0, 5, ev8_0(), ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_6_6(0, 5) : ok8(_)
          %xr8_0_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(0, l, 5, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 0, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 0, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 0, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 0, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 0, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 0, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 0, l, 5) : ok8(_)
          p8_0000000()

def q8_0_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 6) : ok8(_)
          %xr8_0_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_0_2(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_0_3(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_0_4(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_0_5(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_0_6(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_0_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_1_1(0, 6) : ok8(_)
          %xr8_0_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_1_3(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_1_4(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_1_5(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_1_6(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_1_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_2_1(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_2_2(0, 6) : ok8(_)
          %xr8_0_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_2_4(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_2_5(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_2_6(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_2_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_3_1(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_3_2(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_3_3(0, 6) : ok8(_)
          %xr8_0_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_3_5(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_3_6(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_3_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_4_1(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_4_2(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_4_3(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_4_4(0, 6) : ok8(_)
          %xr8_0_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_4_6(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_4_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_5_1(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_5_2(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_5_3(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_5_4(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_5_5(0, 6) : ok8(_)
          %xr8_0_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_5_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_6_1(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_6_2(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_6_3(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_6_4(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_6_5(0, 6, ev8_0(), ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_6_6(0, 6) : ok8(_)
          %xr8_0_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(0, l, 6, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 0, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 0, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 0, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 0, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 0, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 0, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 0, l, 6) : ok8(_)
          p8_0000000()

def q8_0_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(0, 7) : ok8(_)
          %xr8_0_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_0_2(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_0_3(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_0_4(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_0_5(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_0_6(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_0_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_1_1(0, 7) : ok8(_)
          %xr8_0_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_1_3(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_1_4(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_1_5(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_1_6(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_1_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_2_1(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_2_2(0, 7) : ok8(_)
          %xr8_0_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_2_4(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_2_5(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_2_6(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_2_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_3_1(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_3_2(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_3_3(0, 7) : ok8(_)
          %xr8_0_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_3_5(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_3_6(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_3_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_4_1(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_4_2(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_4_3(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_4_4(0, 7) : ok8(_)
          %xr8_0_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_4_6(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_4_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_5_1(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_5_2(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_5_3(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_5_4(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_5_5(0, 7) : ok8(_)
          %xr8_0_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_5_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_6_1(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_6_2(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_6_3(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_6_4(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_6_5(0, 7, ev8_0(), ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_6_6(0, 7) : ok8(_)
          %xr8_0_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(0, l, 7, ev8_0()) : ok8(_)
          p8_0000000()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 0, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 0, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 0, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 0, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 0, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 0, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 0, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 0, l, 7) : ok8(_)
          p8_0000000()

def q8_1_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 0) : ok8(_)
          %xr8_1_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_1000000()
        case 2n:
          %r8_0_2(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_1000000()
        case 3n:
          %r8_0_3(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_1000000()
        case 4n:
          %r8_0_4(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_1000000()
        case 5n:
          %r8_0_5(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_1000000()
        case 6n:
          %r8_0_6(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_1000000()
        case 7n+l:
          %r8_0_far(1, l, 0, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0100000()
        case 1n:
          %r8_1_1(1, 0) : ok8(_)
          %xr8_1_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0100000()
        case 3n:
          %r8_1_3(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0100000()
        case 4n:
          %r8_1_4(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0100000()
        case 5n:
          %r8_1_5(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0100000()
        case 6n:
          %r8_1_6(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0100000()
        case 7n+l:
          %r8_1_far(1, l, 0, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0010000()
        case 1n:
          %r8_2_1(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0010000()
        case 2n:
          %r8_2_2(1, 0) : ok8(_)
          %xr8_1_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0010000()
        case 4n:
          %r8_2_4(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0010000()
        case 5n:
          %r8_2_5(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0010000()
        case 6n:
          %r8_2_6(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0010000()
        case 7n+l:
          %r8_2_far(1, l, 0, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0001000()
        case 1n:
          %r8_3_1(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0001000()
        case 2n:
          %r8_3_2(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0001000()
        case 3n:
          %r8_3_3(1, 0) : ok8(_)
          %xr8_1_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0001000()
        case 5n:
          %r8_3_5(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0001000()
        case 6n:
          %r8_3_6(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0001000()
        case 7n+l:
          %r8_3_far(1, l, 0, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000100()
        case 1n:
          %r8_4_1(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000100()
        case 2n:
          %r8_4_2(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000100()
        case 3n:
          %r8_4_3(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000100()
        case 4n:
          %r8_4_4(1, 0) : ok8(_)
          %xr8_1_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000100()
        case 6n:
          %r8_4_6(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000100()
        case 7n+l:
          %r8_4_far(1, l, 0, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000010()
        case 1n:
          %r8_5_1(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000010()
        case 2n:
          %r8_5_2(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000010()
        case 3n:
          %r8_5_3(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000010()
        case 4n:
          %r8_5_4(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000010()
        case 5n:
          %r8_5_5(1, 0) : ok8(_)
          %xr8_1_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000010()
        case 7n+l:
          %r8_5_far(1, l, 0, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000001()
        case 1n:
          %r8_6_1(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000001()
        case 2n:
          %r8_6_2(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000001()
        case 3n:
          %r8_6_3(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000001()
        case 4n:
          %r8_6_4(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000001()
        case 5n:
          %r8_6_5(1, 0, ev8_1(), ev8_0()) : ok8(_)
          p8_0000001()
        case 6n:
          %r8_6_6(1, 0) : ok8(_)
          %xr8_1_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(1, l, 0, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 1, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 1, l, 0) : ok8(_)
          p8_0000000()

def q8_1_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 1) : ok8(_)
          %xr8_1_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1100000()
        case 2n:
          %r8_0_2(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1010000()
        case 3n:
          %r8_0_3(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1001000()
        case 4n:
          %r8_0_4(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1000100()
        case 5n:
          %r8_0_5(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1000010()
        case 6n:
          %r8_0_6(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1000001()
        case 7n+l:
          %r8_0_far(1, l, 1, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1100000()
        case 1n:
          %r8_1_1(1, 1) : ok8(_)
          %xr8_1_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0110000()
        case 3n:
          %r8_1_3(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0101000()
        case 4n:
          %r8_1_4(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0100100()
        case 5n:
          %r8_1_5(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0100010()
        case 6n:
          %r8_1_6(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0100001()
        case 7n+l:
          %r8_1_far(1, l, 1, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1010000()
        case 1n:
          %r8_2_1(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0110000()
        case 2n:
          %r8_2_2(1, 1) : ok8(_)
          %xr8_1_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0011000()
        case 4n:
          %r8_2_4(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0010100()
        case 5n:
          %r8_2_5(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0010010()
        case 6n:
          %r8_2_6(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0010001()
        case 7n+l:
          %r8_2_far(1, l, 1, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1001000()
        case 1n:
          %r8_3_1(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0101000()
        case 2n:
          %r8_3_2(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0011000()
        case 3n:
          %r8_3_3(1, 1) : ok8(_)
          %xr8_1_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0001100()
        case 5n:
          %r8_3_5(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0001010()
        case 6n:
          %r8_3_6(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0001001()
        case 7n+l:
          %r8_3_far(1, l, 1, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1000100()
        case 1n:
          %r8_4_1(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0100100()
        case 2n:
          %r8_4_2(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0010100()
        case 3n:
          %r8_4_3(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0001100()
        case 4n:
          %r8_4_4(1, 1) : ok8(_)
          %xr8_1_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0000110()
        case 6n:
          %r8_4_6(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0000101()
        case 7n+l:
          %r8_4_far(1, l, 1, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1000010()
        case 1n:
          %r8_5_1(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0100010()
        case 2n:
          %r8_5_2(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0010010()
        case 3n:
          %r8_5_3(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0001010()
        case 4n:
          %r8_5_4(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0000110()
        case 5n:
          %r8_5_5(1, 1) : ok8(_)
          %xr8_1_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0000011()
        case 7n+l:
          %r8_5_far(1, l, 1, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_1000001()
        case 1n:
          %r8_6_1(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0100001()
        case 2n:
          %r8_6_2(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0010001()
        case 3n:
          %r8_6_3(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0001001()
        case 4n:
          %r8_6_4(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0000101()
        case 5n:
          %r8_6_5(1, 1, ev8_1(), ev8_1()) : ok8(_)
          p8_0000011()
        case 6n:
          %r8_6_6(1, 1) : ok8(_)
          %xr8_1_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(1, l, 1, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 1, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 1, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 1, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 1, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 1, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 1, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 1, l, 1) : ok8(_)
          p8_0000000()

def q8_1_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 2) : ok8(_)
          %xr8_1_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_1200000()
        case 2n:
          %r8_0_2(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_1020000()
        case 3n:
          %r8_0_3(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_1002000()
        case 4n:
          %r8_0_4(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_1000200()
        case 5n:
          %r8_0_5(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_1000020()
        case 6n:
          %r8_0_6(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_1000002()
        case 7n+l:
          %r8_0_far(1, l, 2, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_2100000()
        case 1n:
          %r8_1_1(1, 2) : ok8(_)
          %xr8_1_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0120000()
        case 3n:
          %r8_1_3(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0102000()
        case 4n:
          %r8_1_4(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0100200()
        case 5n:
          %r8_1_5(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0100020()
        case 6n:
          %r8_1_6(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0100002()
        case 7n+l:
          %r8_1_far(1, l, 2, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_2010000()
        case 1n:
          %r8_2_1(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0210000()
        case 2n:
          %r8_2_2(1, 2) : ok8(_)
          %xr8_1_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0012000()
        case 4n:
          %r8_2_4(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0010200()
        case 5n:
          %r8_2_5(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0010020()
        case 6n:
          %r8_2_6(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0010002()
        case 7n+l:
          %r8_2_far(1, l, 2, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_2001000()
        case 1n:
          %r8_3_1(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0201000()
        case 2n:
          %r8_3_2(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0021000()
        case 3n:
          %r8_3_3(1, 2) : ok8(_)
          %xr8_1_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0001200()
        case 5n:
          %r8_3_5(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0001020()
        case 6n:
          %r8_3_6(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0001002()
        case 7n+l:
          %r8_3_far(1, l, 2, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_2000100()
        case 1n:
          %r8_4_1(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0200100()
        case 2n:
          %r8_4_2(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0020100()
        case 3n:
          %r8_4_3(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0002100()
        case 4n:
          %r8_4_4(1, 2) : ok8(_)
          %xr8_1_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0000120()
        case 6n:
          %r8_4_6(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0000102()
        case 7n+l:
          %r8_4_far(1, l, 2, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_2000010()
        case 1n:
          %r8_5_1(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0200010()
        case 2n:
          %r8_5_2(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0020010()
        case 3n:
          %r8_5_3(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0002010()
        case 4n:
          %r8_5_4(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0000210()
        case 5n:
          %r8_5_5(1, 2) : ok8(_)
          %xr8_1_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0000012()
        case 7n+l:
          %r8_5_far(1, l, 2, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_2000001()
        case 1n:
          %r8_6_1(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0200001()
        case 2n:
          %r8_6_2(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0020001()
        case 3n:
          %r8_6_3(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0002001()
        case 4n:
          %r8_6_4(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0000201()
        case 5n:
          %r8_6_5(1, 2, ev8_1(), ev8_2()) : ok8(_)
          p8_0000021()
        case 6n:
          %r8_6_6(1, 2) : ok8(_)
          %xr8_1_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(1, l, 2, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 1, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 1, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 1, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 1, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 1, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 1, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 1, l, 2) : ok8(_)
          p8_0000000()

def q8_1_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 3) : ok8(_)
          %xr8_1_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_1300000()
        case 2n:
          %r8_0_2(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_1030000()
        case 3n:
          %r8_0_3(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_1003000()
        case 4n:
          %r8_0_4(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_1000300()
        case 5n:
          %r8_0_5(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_1000030()
        case 6n:
          %r8_0_6(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_1000003()
        case 7n+l:
          %r8_0_far(1, l, 3, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_3100000()
        case 1n:
          %r8_1_1(1, 3) : ok8(_)
          %xr8_1_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0130000()
        case 3n:
          %r8_1_3(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0103000()
        case 4n:
          %r8_1_4(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0100300()
        case 5n:
          %r8_1_5(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0100030()
        case 6n:
          %r8_1_6(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0100003()
        case 7n+l:
          %r8_1_far(1, l, 3, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_3010000()
        case 1n:
          %r8_2_1(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0310000()
        case 2n:
          %r8_2_2(1, 3) : ok8(_)
          %xr8_1_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0013000()
        case 4n:
          %r8_2_4(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0010300()
        case 5n:
          %r8_2_5(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0010030()
        case 6n:
          %r8_2_6(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0010003()
        case 7n+l:
          %r8_2_far(1, l, 3, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_3001000()
        case 1n:
          %r8_3_1(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0301000()
        case 2n:
          %r8_3_2(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0031000()
        case 3n:
          %r8_3_3(1, 3) : ok8(_)
          %xr8_1_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0001300()
        case 5n:
          %r8_3_5(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0001030()
        case 6n:
          %r8_3_6(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0001003()
        case 7n+l:
          %r8_3_far(1, l, 3, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_3000100()
        case 1n:
          %r8_4_1(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0300100()
        case 2n:
          %r8_4_2(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0030100()
        case 3n:
          %r8_4_3(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0003100()
        case 4n:
          %r8_4_4(1, 3) : ok8(_)
          %xr8_1_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0000130()
        case 6n:
          %r8_4_6(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0000103()
        case 7n+l:
          %r8_4_far(1, l, 3, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_3000010()
        case 1n:
          %r8_5_1(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0300010()
        case 2n:
          %r8_5_2(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0030010()
        case 3n:
          %r8_5_3(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0003010()
        case 4n:
          %r8_5_4(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0000310()
        case 5n:
          %r8_5_5(1, 3) : ok8(_)
          %xr8_1_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0000013()
        case 7n+l:
          %r8_5_far(1, l, 3, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_3000001()
        case 1n:
          %r8_6_1(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0300001()
        case 2n:
          %r8_6_2(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0030001()
        case 3n:
          %r8_6_3(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0003001()
        case 4n:
          %r8_6_4(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0000301()
        case 5n:
          %r8_6_5(1, 3, ev8_1(), ev8_3()) : ok8(_)
          p8_0000031()
        case 6n:
          %r8_6_6(1, 3) : ok8(_)
          %xr8_1_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(1, l, 3, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 1, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 1, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 1, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 1, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 1, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 1, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 1, l, 3) : ok8(_)
          p8_0000000()

def q8_1_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 4) : ok8(_)
          %xr8_1_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_1400000()
        case 2n:
          %r8_0_2(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_1040000()
        case 3n:
          %r8_0_3(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_1004000()
        case 4n:
          %r8_0_4(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_1000400()
        case 5n:
          %r8_0_5(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_1000040()
        case 6n:
          %r8_0_6(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_1000004()
        case 7n+l:
          %r8_0_far(1, l, 4, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_4100000()
        case 1n:
          %r8_1_1(1, 4) : ok8(_)
          %xr8_1_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0140000()
        case 3n:
          %r8_1_3(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0104000()
        case 4n:
          %r8_1_4(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0100400()
        case 5n:
          %r8_1_5(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0100040()
        case 6n:
          %r8_1_6(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0100004()
        case 7n+l:
          %r8_1_far(1, l, 4, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_4010000()
        case 1n:
          %r8_2_1(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0410000()
        case 2n:
          %r8_2_2(1, 4) : ok8(_)
          %xr8_1_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0014000()
        case 4n:
          %r8_2_4(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0010400()
        case 5n:
          %r8_2_5(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0010040()
        case 6n:
          %r8_2_6(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0010004()
        case 7n+l:
          %r8_2_far(1, l, 4, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_4001000()
        case 1n:
          %r8_3_1(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0401000()
        case 2n:
          %r8_3_2(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0041000()
        case 3n:
          %r8_3_3(1, 4) : ok8(_)
          %xr8_1_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0001400()
        case 5n:
          %r8_3_5(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0001040()
        case 6n:
          %r8_3_6(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0001004()
        case 7n+l:
          %r8_3_far(1, l, 4, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_4000100()
        case 1n:
          %r8_4_1(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0400100()
        case 2n:
          %r8_4_2(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0040100()
        case 3n:
          %r8_4_3(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0004100()
        case 4n:
          %r8_4_4(1, 4) : ok8(_)
          %xr8_1_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0000140()
        case 6n:
          %r8_4_6(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0000104()
        case 7n+l:
          %r8_4_far(1, l, 4, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_4000010()
        case 1n:
          %r8_5_1(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0400010()
        case 2n:
          %r8_5_2(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0040010()
        case 3n:
          %r8_5_3(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0004010()
        case 4n:
          %r8_5_4(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0000410()
        case 5n:
          %r8_5_5(1, 4) : ok8(_)
          %xr8_1_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0000014()
        case 7n+l:
          %r8_5_far(1, l, 4, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_4000001()
        case 1n:
          %r8_6_1(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0400001()
        case 2n:
          %r8_6_2(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0040001()
        case 3n:
          %r8_6_3(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0004001()
        case 4n:
          %r8_6_4(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0000401()
        case 5n:
          %r8_6_5(1, 4, ev8_1(), ev8_4()) : ok8(_)
          p8_0000041()
        case 6n:
          %r8_6_6(1, 4) : ok8(_)
          %xr8_1_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(1, l, 4, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 1, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 1, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 1, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 1, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 1, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 1, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 1, l, 4) : ok8(_)
          p8_0000000()

def q8_1_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 5) : ok8(_)
          %xr8_1_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_1500000()
        case 2n:
          %r8_0_2(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_1050000()
        case 3n:
          %r8_0_3(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_1005000()
        case 4n:
          %r8_0_4(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_1000500()
        case 5n:
          %r8_0_5(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_1000050()
        case 6n:
          %r8_0_6(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_1000005()
        case 7n+l:
          %r8_0_far(1, l, 5, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_5100000()
        case 1n:
          %r8_1_1(1, 5) : ok8(_)
          %xr8_1_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0150000()
        case 3n:
          %r8_1_3(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0105000()
        case 4n:
          %r8_1_4(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0100500()
        case 5n:
          %r8_1_5(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0100050()
        case 6n:
          %r8_1_6(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0100005()
        case 7n+l:
          %r8_1_far(1, l, 5, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_5010000()
        case 1n:
          %r8_2_1(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0510000()
        case 2n:
          %r8_2_2(1, 5) : ok8(_)
          %xr8_1_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0015000()
        case 4n:
          %r8_2_4(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0010500()
        case 5n:
          %r8_2_5(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0010050()
        case 6n:
          %r8_2_6(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0010005()
        case 7n+l:
          %r8_2_far(1, l, 5, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_5001000()
        case 1n:
          %r8_3_1(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0501000()
        case 2n:
          %r8_3_2(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0051000()
        case 3n:
          %r8_3_3(1, 5) : ok8(_)
          %xr8_1_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0001500()
        case 5n:
          %r8_3_5(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0001050()
        case 6n:
          %r8_3_6(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0001005()
        case 7n+l:
          %r8_3_far(1, l, 5, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_5000100()
        case 1n:
          %r8_4_1(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0500100()
        case 2n:
          %r8_4_2(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0050100()
        case 3n:
          %r8_4_3(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0005100()
        case 4n:
          %r8_4_4(1, 5) : ok8(_)
          %xr8_1_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0000150()
        case 6n:
          %r8_4_6(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0000105()
        case 7n+l:
          %r8_4_far(1, l, 5, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_5000010()
        case 1n:
          %r8_5_1(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0500010()
        case 2n:
          %r8_5_2(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0050010()
        case 3n:
          %r8_5_3(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0005010()
        case 4n:
          %r8_5_4(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0000510()
        case 5n:
          %r8_5_5(1, 5) : ok8(_)
          %xr8_1_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0000015()
        case 7n+l:
          %r8_5_far(1, l, 5, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_5000001()
        case 1n:
          %r8_6_1(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0500001()
        case 2n:
          %r8_6_2(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0050001()
        case 3n:
          %r8_6_3(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0005001()
        case 4n:
          %r8_6_4(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0000501()
        case 5n:
          %r8_6_5(1, 5, ev8_1(), ev8_5()) : ok8(_)
          p8_0000051()
        case 6n:
          %r8_6_6(1, 5) : ok8(_)
          %xr8_1_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(1, l, 5, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 1, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 1, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 1, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 1, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 1, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 1, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 1, l, 5) : ok8(_)
          p8_0000000()

def q8_1_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 6) : ok8(_)
          %xr8_1_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_1600000()
        case 2n:
          %r8_0_2(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_1060000()
        case 3n:
          %r8_0_3(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_1006000()
        case 4n:
          %r8_0_4(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_1000600()
        case 5n:
          %r8_0_5(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_1000060()
        case 6n:
          %r8_0_6(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_1000006()
        case 7n+l:
          %r8_0_far(1, l, 6, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_6100000()
        case 1n:
          %r8_1_1(1, 6) : ok8(_)
          %xr8_1_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0160000()
        case 3n:
          %r8_1_3(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0106000()
        case 4n:
          %r8_1_4(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0100600()
        case 5n:
          %r8_1_5(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0100060()
        case 6n:
          %r8_1_6(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0100006()
        case 7n+l:
          %r8_1_far(1, l, 6, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_6010000()
        case 1n:
          %r8_2_1(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0610000()
        case 2n:
          %r8_2_2(1, 6) : ok8(_)
          %xr8_1_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0016000()
        case 4n:
          %r8_2_4(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0010600()
        case 5n:
          %r8_2_5(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0010060()
        case 6n:
          %r8_2_6(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0010006()
        case 7n+l:
          %r8_2_far(1, l, 6, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_6001000()
        case 1n:
          %r8_3_1(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0601000()
        case 2n:
          %r8_3_2(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0061000()
        case 3n:
          %r8_3_3(1, 6) : ok8(_)
          %xr8_1_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0001600()
        case 5n:
          %r8_3_5(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0001060()
        case 6n:
          %r8_3_6(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0001006()
        case 7n+l:
          %r8_3_far(1, l, 6, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_6000100()
        case 1n:
          %r8_4_1(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0600100()
        case 2n:
          %r8_4_2(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0060100()
        case 3n:
          %r8_4_3(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0006100()
        case 4n:
          %r8_4_4(1, 6) : ok8(_)
          %xr8_1_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0000160()
        case 6n:
          %r8_4_6(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0000106()
        case 7n+l:
          %r8_4_far(1, l, 6, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_6000010()
        case 1n:
          %r8_5_1(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0600010()
        case 2n:
          %r8_5_2(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0060010()
        case 3n:
          %r8_5_3(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0006010()
        case 4n:
          %r8_5_4(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0000610()
        case 5n:
          %r8_5_5(1, 6) : ok8(_)
          %xr8_1_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0000016()
        case 7n+l:
          %r8_5_far(1, l, 6, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_6000001()
        case 1n:
          %r8_6_1(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0600001()
        case 2n:
          %r8_6_2(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0060001()
        case 3n:
          %r8_6_3(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0006001()
        case 4n:
          %r8_6_4(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0000601()
        case 5n:
          %r8_6_5(1, 6, ev8_1(), ev8_6()) : ok8(_)
          p8_0000061()
        case 6n:
          %r8_6_6(1, 6) : ok8(_)
          %xr8_1_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(1, l, 6, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 1, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 1, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 1, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 1, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 1, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 1, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 1, l, 6) : ok8(_)
          p8_0000000()

def q8_1_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(1, 7) : ok8(_)
          %xr8_1_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_1700000()
        case 2n:
          %r8_0_2(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_1070000()
        case 3n:
          %r8_0_3(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_1007000()
        case 4n:
          %r8_0_4(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_1000700()
        case 5n:
          %r8_0_5(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_1000070()
        case 6n:
          %r8_0_6(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_1000007()
        case 7n+l:
          %r8_0_far(1, l, 7, ev8_1()) : ok8(_)
          p8_1000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_7100000()
        case 1n:
          %r8_1_1(1, 7) : ok8(_)
          %xr8_1_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0170000()
        case 3n:
          %r8_1_3(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0107000()
        case 4n:
          %r8_1_4(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0100700()
        case 5n:
          %r8_1_5(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0100070()
        case 6n:
          %r8_1_6(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0100007()
        case 7n+l:
          %r8_1_far(1, l, 7, ev8_1()) : ok8(_)
          p8_0100000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_7010000()
        case 1n:
          %r8_2_1(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0710000()
        case 2n:
          %r8_2_2(1, 7) : ok8(_)
          %xr8_1_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0017000()
        case 4n:
          %r8_2_4(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0010700()
        case 5n:
          %r8_2_5(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0010070()
        case 6n:
          %r8_2_6(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0010007()
        case 7n+l:
          %r8_2_far(1, l, 7, ev8_1()) : ok8(_)
          p8_0010000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_7001000()
        case 1n:
          %r8_3_1(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0701000()
        case 2n:
          %r8_3_2(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0071000()
        case 3n:
          %r8_3_3(1, 7) : ok8(_)
          %xr8_1_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0001700()
        case 5n:
          %r8_3_5(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0001070()
        case 6n:
          %r8_3_6(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0001007()
        case 7n+l:
          %r8_3_far(1, l, 7, ev8_1()) : ok8(_)
          p8_0001000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_7000100()
        case 1n:
          %r8_4_1(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0700100()
        case 2n:
          %r8_4_2(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0070100()
        case 3n:
          %r8_4_3(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0007100()
        case 4n:
          %r8_4_4(1, 7) : ok8(_)
          %xr8_1_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0000170()
        case 6n:
          %r8_4_6(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0000107()
        case 7n+l:
          %r8_4_far(1, l, 7, ev8_1()) : ok8(_)
          p8_0000100()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_7000010()
        case 1n:
          %r8_5_1(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0700010()
        case 2n:
          %r8_5_2(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0070010()
        case 3n:
          %r8_5_3(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0007010()
        case 4n:
          %r8_5_4(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0000710()
        case 5n:
          %r8_5_5(1, 7) : ok8(_)
          %xr8_1_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0000017()
        case 7n+l:
          %r8_5_far(1, l, 7, ev8_1()) : ok8(_)
          p8_0000010()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_7000001()
        case 1n:
          %r8_6_1(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0700001()
        case 2n:
          %r8_6_2(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0070001()
        case 3n:
          %r8_6_3(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0007001()
        case 4n:
          %r8_6_4(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0000701()
        case 5n:
          %r8_6_5(1, 7, ev8_1(), ev8_7()) : ok8(_)
          p8_0000071()
        case 6n:
          %r8_6_6(1, 7) : ok8(_)
          %xr8_1_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(1, l, 7, ev8_1()) : ok8(_)
          p8_0000001()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 1, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 1, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 1, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 1, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 1, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 1, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 1, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 1, l, 7) : ok8(_)
          p8_0000000()

def q8_2_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 0) : ok8(_)
          %xr8_2_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_2000000()
        case 2n:
          %r8_0_2(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_2000000()
        case 3n:
          %r8_0_3(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_2000000()
        case 4n:
          %r8_0_4(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_2000000()
        case 5n:
          %r8_0_5(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_2000000()
        case 6n:
          %r8_0_6(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_2000000()
        case 7n+l:
          %r8_0_far(2, l, 0, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0200000()
        case 1n:
          %r8_1_1(2, 0) : ok8(_)
          %xr8_2_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0200000()
        case 3n:
          %r8_1_3(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0200000()
        case 4n:
          %r8_1_4(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0200000()
        case 5n:
          %r8_1_5(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0200000()
        case 6n:
          %r8_1_6(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0200000()
        case 7n+l:
          %r8_1_far(2, l, 0, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0020000()
        case 1n:
          %r8_2_1(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0020000()
        case 2n:
          %r8_2_2(2, 0) : ok8(_)
          %xr8_2_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0020000()
        case 4n:
          %r8_2_4(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0020000()
        case 5n:
          %r8_2_5(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0020000()
        case 6n:
          %r8_2_6(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0020000()
        case 7n+l:
          %r8_2_far(2, l, 0, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0002000()
        case 1n:
          %r8_3_1(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0002000()
        case 2n:
          %r8_3_2(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0002000()
        case 3n:
          %r8_3_3(2, 0) : ok8(_)
          %xr8_2_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0002000()
        case 5n:
          %r8_3_5(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0002000()
        case 6n:
          %r8_3_6(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0002000()
        case 7n+l:
          %r8_3_far(2, l, 0, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000200()
        case 1n:
          %r8_4_1(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000200()
        case 2n:
          %r8_4_2(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000200()
        case 3n:
          %r8_4_3(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000200()
        case 4n:
          %r8_4_4(2, 0) : ok8(_)
          %xr8_2_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000200()
        case 6n:
          %r8_4_6(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000200()
        case 7n+l:
          %r8_4_far(2, l, 0, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000020()
        case 1n:
          %r8_5_1(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000020()
        case 2n:
          %r8_5_2(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000020()
        case 3n:
          %r8_5_3(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000020()
        case 4n:
          %r8_5_4(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000020()
        case 5n:
          %r8_5_5(2, 0) : ok8(_)
          %xr8_2_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000020()
        case 7n+l:
          %r8_5_far(2, l, 0, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000002()
        case 1n:
          %r8_6_1(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000002()
        case 2n:
          %r8_6_2(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000002()
        case 3n:
          %r8_6_3(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000002()
        case 4n:
          %r8_6_4(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000002()
        case 5n:
          %r8_6_5(2, 0, ev8_2(), ev8_0()) : ok8(_)
          p8_0000002()
        case 6n:
          %r8_6_6(2, 0) : ok8(_)
          %xr8_2_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(2, l, 0, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 2, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 2, l, 0) : ok8(_)
          p8_0000000()

def q8_2_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 1) : ok8(_)
          %xr8_2_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_2100000()
        case 2n:
          %r8_0_2(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_2010000()
        case 3n:
          %r8_0_3(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_2001000()
        case 4n:
          %r8_0_4(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_2000100()
        case 5n:
          %r8_0_5(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_2000010()
        case 6n:
          %r8_0_6(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_2000001()
        case 7n+l:
          %r8_0_far(2, l, 1, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_1200000()
        case 1n:
          %r8_1_1(2, 1) : ok8(_)
          %xr8_2_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0210000()
        case 3n:
          %r8_1_3(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0201000()
        case 4n:
          %r8_1_4(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0200100()
        case 5n:
          %r8_1_5(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0200010()
        case 6n:
          %r8_1_6(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0200001()
        case 7n+l:
          %r8_1_far(2, l, 1, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_1020000()
        case 1n:
          %r8_2_1(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0120000()
        case 2n:
          %r8_2_2(2, 1) : ok8(_)
          %xr8_2_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0021000()
        case 4n:
          %r8_2_4(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0020100()
        case 5n:
          %r8_2_5(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0020010()
        case 6n:
          %r8_2_6(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0020001()
        case 7n+l:
          %r8_2_far(2, l, 1, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_1002000()
        case 1n:
          %r8_3_1(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0102000()
        case 2n:
          %r8_3_2(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0012000()
        case 3n:
          %r8_3_3(2, 1) : ok8(_)
          %xr8_2_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0002100()
        case 5n:
          %r8_3_5(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0002010()
        case 6n:
          %r8_3_6(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0002001()
        case 7n+l:
          %r8_3_far(2, l, 1, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_1000200()
        case 1n:
          %r8_4_1(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0100200()
        case 2n:
          %r8_4_2(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0010200()
        case 3n:
          %r8_4_3(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0001200()
        case 4n:
          %r8_4_4(2, 1) : ok8(_)
          %xr8_2_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0000210()
        case 6n:
          %r8_4_6(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0000201()
        case 7n+l:
          %r8_4_far(2, l, 1, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_1000020()
        case 1n:
          %r8_5_1(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0100020()
        case 2n:
          %r8_5_2(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0010020()
        case 3n:
          %r8_5_3(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0001020()
        case 4n:
          %r8_5_4(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0000120()
        case 5n:
          %r8_5_5(2, 1) : ok8(_)
          %xr8_2_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0000021()
        case 7n+l:
          %r8_5_far(2, l, 1, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_1000002()
        case 1n:
          %r8_6_1(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0100002()
        case 2n:
          %r8_6_2(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0010002()
        case 3n:
          %r8_6_3(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0001002()
        case 4n:
          %r8_6_4(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0000102()
        case 5n:
          %r8_6_5(2, 1, ev8_2(), ev8_1()) : ok8(_)
          p8_0000012()
        case 6n:
          %r8_6_6(2, 1) : ok8(_)
          %xr8_2_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(2, l, 1, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 2, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 2, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 2, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 2, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 2, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 2, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 2, l, 1) : ok8(_)
          p8_0000000()

def q8_2_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 2) : ok8(_)
          %xr8_2_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2200000()
        case 2n:
          %r8_0_2(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2020000()
        case 3n:
          %r8_0_3(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2002000()
        case 4n:
          %r8_0_4(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2000200()
        case 5n:
          %r8_0_5(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2000020()
        case 6n:
          %r8_0_6(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2000002()
        case 7n+l:
          %r8_0_far(2, l, 2, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2200000()
        case 1n:
          %r8_1_1(2, 2) : ok8(_)
          %xr8_2_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0220000()
        case 3n:
          %r8_1_3(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0202000()
        case 4n:
          %r8_1_4(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0200200()
        case 5n:
          %r8_1_5(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0200020()
        case 6n:
          %r8_1_6(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0200002()
        case 7n+l:
          %r8_1_far(2, l, 2, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2020000()
        case 1n:
          %r8_2_1(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0220000()
        case 2n:
          %r8_2_2(2, 2) : ok8(_)
          %xr8_2_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0022000()
        case 4n:
          %r8_2_4(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0020200()
        case 5n:
          %r8_2_5(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0020020()
        case 6n:
          %r8_2_6(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0020002()
        case 7n+l:
          %r8_2_far(2, l, 2, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2002000()
        case 1n:
          %r8_3_1(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0202000()
        case 2n:
          %r8_3_2(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0022000()
        case 3n:
          %r8_3_3(2, 2) : ok8(_)
          %xr8_2_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0002200()
        case 5n:
          %r8_3_5(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0002020()
        case 6n:
          %r8_3_6(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0002002()
        case 7n+l:
          %r8_3_far(2, l, 2, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2000200()
        case 1n:
          %r8_4_1(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0200200()
        case 2n:
          %r8_4_2(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0020200()
        case 3n:
          %r8_4_3(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0002200()
        case 4n:
          %r8_4_4(2, 2) : ok8(_)
          %xr8_2_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0000220()
        case 6n:
          %r8_4_6(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0000202()
        case 7n+l:
          %r8_4_far(2, l, 2, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2000020()
        case 1n:
          %r8_5_1(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0200020()
        case 2n:
          %r8_5_2(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0020020()
        case 3n:
          %r8_5_3(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0002020()
        case 4n:
          %r8_5_4(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0000220()
        case 5n:
          %r8_5_5(2, 2) : ok8(_)
          %xr8_2_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0000022()
        case 7n+l:
          %r8_5_far(2, l, 2, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_2000002()
        case 1n:
          %r8_6_1(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0200002()
        case 2n:
          %r8_6_2(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0020002()
        case 3n:
          %r8_6_3(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0002002()
        case 4n:
          %r8_6_4(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0000202()
        case 5n:
          %r8_6_5(2, 2, ev8_2(), ev8_2()) : ok8(_)
          p8_0000022()
        case 6n:
          %r8_6_6(2, 2) : ok8(_)
          %xr8_2_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(2, l, 2, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 2, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 2, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 2, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 2, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 2, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 2, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 2, l, 2) : ok8(_)
          p8_0000000()

def q8_2_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 3) : ok8(_)
          %xr8_2_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_2300000()
        case 2n:
          %r8_0_2(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_2030000()
        case 3n:
          %r8_0_3(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_2003000()
        case 4n:
          %r8_0_4(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_2000300()
        case 5n:
          %r8_0_5(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_2000030()
        case 6n:
          %r8_0_6(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_2000003()
        case 7n+l:
          %r8_0_far(2, l, 3, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_3200000()
        case 1n:
          %r8_1_1(2, 3) : ok8(_)
          %xr8_2_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0230000()
        case 3n:
          %r8_1_3(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0203000()
        case 4n:
          %r8_1_4(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0200300()
        case 5n:
          %r8_1_5(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0200030()
        case 6n:
          %r8_1_6(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0200003()
        case 7n+l:
          %r8_1_far(2, l, 3, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_3020000()
        case 1n:
          %r8_2_1(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0320000()
        case 2n:
          %r8_2_2(2, 3) : ok8(_)
          %xr8_2_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0023000()
        case 4n:
          %r8_2_4(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0020300()
        case 5n:
          %r8_2_5(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0020030()
        case 6n:
          %r8_2_6(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0020003()
        case 7n+l:
          %r8_2_far(2, l, 3, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_3002000()
        case 1n:
          %r8_3_1(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0302000()
        case 2n:
          %r8_3_2(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0032000()
        case 3n:
          %r8_3_3(2, 3) : ok8(_)
          %xr8_2_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0002300()
        case 5n:
          %r8_3_5(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0002030()
        case 6n:
          %r8_3_6(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0002003()
        case 7n+l:
          %r8_3_far(2, l, 3, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_3000200()
        case 1n:
          %r8_4_1(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0300200()
        case 2n:
          %r8_4_2(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0030200()
        case 3n:
          %r8_4_3(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0003200()
        case 4n:
          %r8_4_4(2, 3) : ok8(_)
          %xr8_2_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0000230()
        case 6n:
          %r8_4_6(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0000203()
        case 7n+l:
          %r8_4_far(2, l, 3, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_3000020()
        case 1n:
          %r8_5_1(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0300020()
        case 2n:
          %r8_5_2(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0030020()
        case 3n:
          %r8_5_3(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0003020()
        case 4n:
          %r8_5_4(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0000320()
        case 5n:
          %r8_5_5(2, 3) : ok8(_)
          %xr8_2_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0000023()
        case 7n+l:
          %r8_5_far(2, l, 3, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_3000002()
        case 1n:
          %r8_6_1(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0300002()
        case 2n:
          %r8_6_2(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0030002()
        case 3n:
          %r8_6_3(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0003002()
        case 4n:
          %r8_6_4(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0000302()
        case 5n:
          %r8_6_5(2, 3, ev8_2(), ev8_3()) : ok8(_)
          p8_0000032()
        case 6n:
          %r8_6_6(2, 3) : ok8(_)
          %xr8_2_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(2, l, 3, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 2, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 2, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 2, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 2, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 2, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 2, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 2, l, 3) : ok8(_)
          p8_0000000()

def q8_2_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 4) : ok8(_)
          %xr8_2_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_2400000()
        case 2n:
          %r8_0_2(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_2040000()
        case 3n:
          %r8_0_3(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_2004000()
        case 4n:
          %r8_0_4(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_2000400()
        case 5n:
          %r8_0_5(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_2000040()
        case 6n:
          %r8_0_6(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_2000004()
        case 7n+l:
          %r8_0_far(2, l, 4, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_4200000()
        case 1n:
          %r8_1_1(2, 4) : ok8(_)
          %xr8_2_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0240000()
        case 3n:
          %r8_1_3(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0204000()
        case 4n:
          %r8_1_4(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0200400()
        case 5n:
          %r8_1_5(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0200040()
        case 6n:
          %r8_1_6(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0200004()
        case 7n+l:
          %r8_1_far(2, l, 4, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_4020000()
        case 1n:
          %r8_2_1(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0420000()
        case 2n:
          %r8_2_2(2, 4) : ok8(_)
          %xr8_2_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0024000()
        case 4n:
          %r8_2_4(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0020400()
        case 5n:
          %r8_2_5(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0020040()
        case 6n:
          %r8_2_6(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0020004()
        case 7n+l:
          %r8_2_far(2, l, 4, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_4002000()
        case 1n:
          %r8_3_1(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0402000()
        case 2n:
          %r8_3_2(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0042000()
        case 3n:
          %r8_3_3(2, 4) : ok8(_)
          %xr8_2_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0002400()
        case 5n:
          %r8_3_5(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0002040()
        case 6n:
          %r8_3_6(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0002004()
        case 7n+l:
          %r8_3_far(2, l, 4, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_4000200()
        case 1n:
          %r8_4_1(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0400200()
        case 2n:
          %r8_4_2(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0040200()
        case 3n:
          %r8_4_3(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0004200()
        case 4n:
          %r8_4_4(2, 4) : ok8(_)
          %xr8_2_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0000240()
        case 6n:
          %r8_4_6(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0000204()
        case 7n+l:
          %r8_4_far(2, l, 4, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_4000020()
        case 1n:
          %r8_5_1(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0400020()
        case 2n:
          %r8_5_2(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0040020()
        case 3n:
          %r8_5_3(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0004020()
        case 4n:
          %r8_5_4(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0000420()
        case 5n:
          %r8_5_5(2, 4) : ok8(_)
          %xr8_2_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0000024()
        case 7n+l:
          %r8_5_far(2, l, 4, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_4000002()
        case 1n:
          %r8_6_1(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0400002()
        case 2n:
          %r8_6_2(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0040002()
        case 3n:
          %r8_6_3(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0004002()
        case 4n:
          %r8_6_4(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0000402()
        case 5n:
          %r8_6_5(2, 4, ev8_2(), ev8_4()) : ok8(_)
          p8_0000042()
        case 6n:
          %r8_6_6(2, 4) : ok8(_)
          %xr8_2_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(2, l, 4, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 2, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 2, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 2, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 2, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 2, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 2, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 2, l, 4) : ok8(_)
          p8_0000000()

def q8_2_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 5) : ok8(_)
          %xr8_2_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_2500000()
        case 2n:
          %r8_0_2(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_2050000()
        case 3n:
          %r8_0_3(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_2005000()
        case 4n:
          %r8_0_4(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_2000500()
        case 5n:
          %r8_0_5(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_2000050()
        case 6n:
          %r8_0_6(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_2000005()
        case 7n+l:
          %r8_0_far(2, l, 5, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_5200000()
        case 1n:
          %r8_1_1(2, 5) : ok8(_)
          %xr8_2_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0250000()
        case 3n:
          %r8_1_3(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0205000()
        case 4n:
          %r8_1_4(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0200500()
        case 5n:
          %r8_1_5(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0200050()
        case 6n:
          %r8_1_6(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0200005()
        case 7n+l:
          %r8_1_far(2, l, 5, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_5020000()
        case 1n:
          %r8_2_1(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0520000()
        case 2n:
          %r8_2_2(2, 5) : ok8(_)
          %xr8_2_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0025000()
        case 4n:
          %r8_2_4(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0020500()
        case 5n:
          %r8_2_5(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0020050()
        case 6n:
          %r8_2_6(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0020005()
        case 7n+l:
          %r8_2_far(2, l, 5, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_5002000()
        case 1n:
          %r8_3_1(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0502000()
        case 2n:
          %r8_3_2(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0052000()
        case 3n:
          %r8_3_3(2, 5) : ok8(_)
          %xr8_2_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0002500()
        case 5n:
          %r8_3_5(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0002050()
        case 6n:
          %r8_3_6(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0002005()
        case 7n+l:
          %r8_3_far(2, l, 5, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_5000200()
        case 1n:
          %r8_4_1(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0500200()
        case 2n:
          %r8_4_2(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0050200()
        case 3n:
          %r8_4_3(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0005200()
        case 4n:
          %r8_4_4(2, 5) : ok8(_)
          %xr8_2_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0000250()
        case 6n:
          %r8_4_6(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0000205()
        case 7n+l:
          %r8_4_far(2, l, 5, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_5000020()
        case 1n:
          %r8_5_1(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0500020()
        case 2n:
          %r8_5_2(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0050020()
        case 3n:
          %r8_5_3(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0005020()
        case 4n:
          %r8_5_4(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0000520()
        case 5n:
          %r8_5_5(2, 5) : ok8(_)
          %xr8_2_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0000025()
        case 7n+l:
          %r8_5_far(2, l, 5, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_5000002()
        case 1n:
          %r8_6_1(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0500002()
        case 2n:
          %r8_6_2(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0050002()
        case 3n:
          %r8_6_3(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0005002()
        case 4n:
          %r8_6_4(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0000502()
        case 5n:
          %r8_6_5(2, 5, ev8_2(), ev8_5()) : ok8(_)
          p8_0000052()
        case 6n:
          %r8_6_6(2, 5) : ok8(_)
          %xr8_2_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(2, l, 5, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 2, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 2, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 2, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 2, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 2, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 2, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 2, l, 5) : ok8(_)
          p8_0000000()

def q8_2_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 6) : ok8(_)
          %xr8_2_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_2600000()
        case 2n:
          %r8_0_2(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_2060000()
        case 3n:
          %r8_0_3(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_2006000()
        case 4n:
          %r8_0_4(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_2000600()
        case 5n:
          %r8_0_5(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_2000060()
        case 6n:
          %r8_0_6(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_2000006()
        case 7n+l:
          %r8_0_far(2, l, 6, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_6200000()
        case 1n:
          %r8_1_1(2, 6) : ok8(_)
          %xr8_2_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0260000()
        case 3n:
          %r8_1_3(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0206000()
        case 4n:
          %r8_1_4(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0200600()
        case 5n:
          %r8_1_5(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0200060()
        case 6n:
          %r8_1_6(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0200006()
        case 7n+l:
          %r8_1_far(2, l, 6, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_6020000()
        case 1n:
          %r8_2_1(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0620000()
        case 2n:
          %r8_2_2(2, 6) : ok8(_)
          %xr8_2_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0026000()
        case 4n:
          %r8_2_4(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0020600()
        case 5n:
          %r8_2_5(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0020060()
        case 6n:
          %r8_2_6(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0020006()
        case 7n+l:
          %r8_2_far(2, l, 6, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_6002000()
        case 1n:
          %r8_3_1(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0602000()
        case 2n:
          %r8_3_2(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0062000()
        case 3n:
          %r8_3_3(2, 6) : ok8(_)
          %xr8_2_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0002600()
        case 5n:
          %r8_3_5(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0002060()
        case 6n:
          %r8_3_6(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0002006()
        case 7n+l:
          %r8_3_far(2, l, 6, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_6000200()
        case 1n:
          %r8_4_1(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0600200()
        case 2n:
          %r8_4_2(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0060200()
        case 3n:
          %r8_4_3(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0006200()
        case 4n:
          %r8_4_4(2, 6) : ok8(_)
          %xr8_2_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0000260()
        case 6n:
          %r8_4_6(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0000206()
        case 7n+l:
          %r8_4_far(2, l, 6, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_6000020()
        case 1n:
          %r8_5_1(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0600020()
        case 2n:
          %r8_5_2(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0060020()
        case 3n:
          %r8_5_3(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0006020()
        case 4n:
          %r8_5_4(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0000620()
        case 5n:
          %r8_5_5(2, 6) : ok8(_)
          %xr8_2_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0000026()
        case 7n+l:
          %r8_5_far(2, l, 6, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_6000002()
        case 1n:
          %r8_6_1(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0600002()
        case 2n:
          %r8_6_2(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0060002()
        case 3n:
          %r8_6_3(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0006002()
        case 4n:
          %r8_6_4(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0000602()
        case 5n:
          %r8_6_5(2, 6, ev8_2(), ev8_6()) : ok8(_)
          p8_0000062()
        case 6n:
          %r8_6_6(2, 6) : ok8(_)
          %xr8_2_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(2, l, 6, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 2, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 2, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 2, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 2, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 2, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 2, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 2, l, 6) : ok8(_)
          p8_0000000()

def q8_2_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(2, 7) : ok8(_)
          %xr8_2_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_2700000()
        case 2n:
          %r8_0_2(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_2070000()
        case 3n:
          %r8_0_3(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_2007000()
        case 4n:
          %r8_0_4(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_2000700()
        case 5n:
          %r8_0_5(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_2000070()
        case 6n:
          %r8_0_6(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_2000007()
        case 7n+l:
          %r8_0_far(2, l, 7, ev8_2()) : ok8(_)
          p8_2000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_7200000()
        case 1n:
          %r8_1_1(2, 7) : ok8(_)
          %xr8_2_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0270000()
        case 3n:
          %r8_1_3(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0207000()
        case 4n:
          %r8_1_4(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0200700()
        case 5n:
          %r8_1_5(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0200070()
        case 6n:
          %r8_1_6(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0200007()
        case 7n+l:
          %r8_1_far(2, l, 7, ev8_2()) : ok8(_)
          p8_0200000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_7020000()
        case 1n:
          %r8_2_1(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0720000()
        case 2n:
          %r8_2_2(2, 7) : ok8(_)
          %xr8_2_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0027000()
        case 4n:
          %r8_2_4(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0020700()
        case 5n:
          %r8_2_5(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0020070()
        case 6n:
          %r8_2_6(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0020007()
        case 7n+l:
          %r8_2_far(2, l, 7, ev8_2()) : ok8(_)
          p8_0020000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_7002000()
        case 1n:
          %r8_3_1(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0702000()
        case 2n:
          %r8_3_2(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0072000()
        case 3n:
          %r8_3_3(2, 7) : ok8(_)
          %xr8_2_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0002700()
        case 5n:
          %r8_3_5(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0002070()
        case 6n:
          %r8_3_6(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0002007()
        case 7n+l:
          %r8_3_far(2, l, 7, ev8_2()) : ok8(_)
          p8_0002000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_7000200()
        case 1n:
          %r8_4_1(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0700200()
        case 2n:
          %r8_4_2(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0070200()
        case 3n:
          %r8_4_3(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0007200()
        case 4n:
          %r8_4_4(2, 7) : ok8(_)
          %xr8_2_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0000270()
        case 6n:
          %r8_4_6(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0000207()
        case 7n+l:
          %r8_4_far(2, l, 7, ev8_2()) : ok8(_)
          p8_0000200()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_7000020()
        case 1n:
          %r8_5_1(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0700020()
        case 2n:
          %r8_5_2(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0070020()
        case 3n:
          %r8_5_3(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0007020()
        case 4n:
          %r8_5_4(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0000720()
        case 5n:
          %r8_5_5(2, 7) : ok8(_)
          %xr8_2_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0000027()
        case 7n+l:
          %r8_5_far(2, l, 7, ev8_2()) : ok8(_)
          p8_0000020()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_7000002()
        case 1n:
          %r8_6_1(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0700002()
        case 2n:
          %r8_6_2(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0070002()
        case 3n:
          %r8_6_3(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0007002()
        case 4n:
          %r8_6_4(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0000702()
        case 5n:
          %r8_6_5(2, 7, ev8_2(), ev8_7()) : ok8(_)
          p8_0000072()
        case 6n:
          %r8_6_6(2, 7) : ok8(_)
          %xr8_2_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(2, l, 7, ev8_2()) : ok8(_)
          p8_0000002()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 2, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 2, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 2, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 2, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 2, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 2, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 2, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 2, l, 7) : ok8(_)
          p8_0000000()

def q8_3_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 0) : ok8(_)
          %xr8_3_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_3000000()
        case 2n:
          %r8_0_2(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_3000000()
        case 3n:
          %r8_0_3(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_3000000()
        case 4n:
          %r8_0_4(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_3000000()
        case 5n:
          %r8_0_5(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_3000000()
        case 6n:
          %r8_0_6(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_3000000()
        case 7n+l:
          %r8_0_far(3, l, 0, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0300000()
        case 1n:
          %r8_1_1(3, 0) : ok8(_)
          %xr8_3_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0300000()
        case 3n:
          %r8_1_3(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0300000()
        case 4n:
          %r8_1_4(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0300000()
        case 5n:
          %r8_1_5(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0300000()
        case 6n:
          %r8_1_6(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0300000()
        case 7n+l:
          %r8_1_far(3, l, 0, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0030000()
        case 1n:
          %r8_2_1(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0030000()
        case 2n:
          %r8_2_2(3, 0) : ok8(_)
          %xr8_3_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0030000()
        case 4n:
          %r8_2_4(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0030000()
        case 5n:
          %r8_2_5(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0030000()
        case 6n:
          %r8_2_6(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0030000()
        case 7n+l:
          %r8_2_far(3, l, 0, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0003000()
        case 1n:
          %r8_3_1(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0003000()
        case 2n:
          %r8_3_2(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0003000()
        case 3n:
          %r8_3_3(3, 0) : ok8(_)
          %xr8_3_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0003000()
        case 5n:
          %r8_3_5(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0003000()
        case 6n:
          %r8_3_6(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0003000()
        case 7n+l:
          %r8_3_far(3, l, 0, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000300()
        case 1n:
          %r8_4_1(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000300()
        case 2n:
          %r8_4_2(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000300()
        case 3n:
          %r8_4_3(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000300()
        case 4n:
          %r8_4_4(3, 0) : ok8(_)
          %xr8_3_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000300()
        case 6n:
          %r8_4_6(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000300()
        case 7n+l:
          %r8_4_far(3, l, 0, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000030()
        case 1n:
          %r8_5_1(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000030()
        case 2n:
          %r8_5_2(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000030()
        case 3n:
          %r8_5_3(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000030()
        case 4n:
          %r8_5_4(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000030()
        case 5n:
          %r8_5_5(3, 0) : ok8(_)
          %xr8_3_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000030()
        case 7n+l:
          %r8_5_far(3, l, 0, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000003()
        case 1n:
          %r8_6_1(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000003()
        case 2n:
          %r8_6_2(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000003()
        case 3n:
          %r8_6_3(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000003()
        case 4n:
          %r8_6_4(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000003()
        case 5n:
          %r8_6_5(3, 0, ev8_3(), ev8_0()) : ok8(_)
          p8_0000003()
        case 6n:
          %r8_6_6(3, 0) : ok8(_)
          %xr8_3_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(3, l, 0, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 3, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 3, l, 0) : ok8(_)
          p8_0000000()

def q8_3_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 1) : ok8(_)
          %xr8_3_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_3100000()
        case 2n:
          %r8_0_2(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_3010000()
        case 3n:
          %r8_0_3(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_3001000()
        case 4n:
          %r8_0_4(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_3000100()
        case 5n:
          %r8_0_5(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_3000010()
        case 6n:
          %r8_0_6(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_3000001()
        case 7n+l:
          %r8_0_far(3, l, 1, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_1300000()
        case 1n:
          %r8_1_1(3, 1) : ok8(_)
          %xr8_3_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0310000()
        case 3n:
          %r8_1_3(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0301000()
        case 4n:
          %r8_1_4(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0300100()
        case 5n:
          %r8_1_5(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0300010()
        case 6n:
          %r8_1_6(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0300001()
        case 7n+l:
          %r8_1_far(3, l, 1, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_1030000()
        case 1n:
          %r8_2_1(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0130000()
        case 2n:
          %r8_2_2(3, 1) : ok8(_)
          %xr8_3_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0031000()
        case 4n:
          %r8_2_4(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0030100()
        case 5n:
          %r8_2_5(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0030010()
        case 6n:
          %r8_2_6(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0030001()
        case 7n+l:
          %r8_2_far(3, l, 1, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_1003000()
        case 1n:
          %r8_3_1(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0103000()
        case 2n:
          %r8_3_2(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0013000()
        case 3n:
          %r8_3_3(3, 1) : ok8(_)
          %xr8_3_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0003100()
        case 5n:
          %r8_3_5(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0003010()
        case 6n:
          %r8_3_6(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0003001()
        case 7n+l:
          %r8_3_far(3, l, 1, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_1000300()
        case 1n:
          %r8_4_1(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0100300()
        case 2n:
          %r8_4_2(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0010300()
        case 3n:
          %r8_4_3(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0001300()
        case 4n:
          %r8_4_4(3, 1) : ok8(_)
          %xr8_3_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0000310()
        case 6n:
          %r8_4_6(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0000301()
        case 7n+l:
          %r8_4_far(3, l, 1, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_1000030()
        case 1n:
          %r8_5_1(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0100030()
        case 2n:
          %r8_5_2(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0010030()
        case 3n:
          %r8_5_3(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0001030()
        case 4n:
          %r8_5_4(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0000130()
        case 5n:
          %r8_5_5(3, 1) : ok8(_)
          %xr8_3_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0000031()
        case 7n+l:
          %r8_5_far(3, l, 1, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_1000003()
        case 1n:
          %r8_6_1(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0100003()
        case 2n:
          %r8_6_2(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0010003()
        case 3n:
          %r8_6_3(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0001003()
        case 4n:
          %r8_6_4(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0000103()
        case 5n:
          %r8_6_5(3, 1, ev8_3(), ev8_1()) : ok8(_)
          p8_0000013()
        case 6n:
          %r8_6_6(3, 1) : ok8(_)
          %xr8_3_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(3, l, 1, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 3, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 3, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 3, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 3, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 3, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 3, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 3, l, 1) : ok8(_)
          p8_0000000()

def q8_3_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 2) : ok8(_)
          %xr8_3_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_3200000()
        case 2n:
          %r8_0_2(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_3020000()
        case 3n:
          %r8_0_3(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_3002000()
        case 4n:
          %r8_0_4(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_3000200()
        case 5n:
          %r8_0_5(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_3000020()
        case 6n:
          %r8_0_6(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_3000002()
        case 7n+l:
          %r8_0_far(3, l, 2, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_2300000()
        case 1n:
          %r8_1_1(3, 2) : ok8(_)
          %xr8_3_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0320000()
        case 3n:
          %r8_1_3(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0302000()
        case 4n:
          %r8_1_4(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0300200()
        case 5n:
          %r8_1_5(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0300020()
        case 6n:
          %r8_1_6(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0300002()
        case 7n+l:
          %r8_1_far(3, l, 2, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_2030000()
        case 1n:
          %r8_2_1(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0230000()
        case 2n:
          %r8_2_2(3, 2) : ok8(_)
          %xr8_3_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0032000()
        case 4n:
          %r8_2_4(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0030200()
        case 5n:
          %r8_2_5(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0030020()
        case 6n:
          %r8_2_6(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0030002()
        case 7n+l:
          %r8_2_far(3, l, 2, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_2003000()
        case 1n:
          %r8_3_1(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0203000()
        case 2n:
          %r8_3_2(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0023000()
        case 3n:
          %r8_3_3(3, 2) : ok8(_)
          %xr8_3_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0003200()
        case 5n:
          %r8_3_5(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0003020()
        case 6n:
          %r8_3_6(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0003002()
        case 7n+l:
          %r8_3_far(3, l, 2, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_2000300()
        case 1n:
          %r8_4_1(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0200300()
        case 2n:
          %r8_4_2(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0020300()
        case 3n:
          %r8_4_3(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0002300()
        case 4n:
          %r8_4_4(3, 2) : ok8(_)
          %xr8_3_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0000320()
        case 6n:
          %r8_4_6(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0000302()
        case 7n+l:
          %r8_4_far(3, l, 2, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_2000030()
        case 1n:
          %r8_5_1(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0200030()
        case 2n:
          %r8_5_2(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0020030()
        case 3n:
          %r8_5_3(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0002030()
        case 4n:
          %r8_5_4(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0000230()
        case 5n:
          %r8_5_5(3, 2) : ok8(_)
          %xr8_3_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0000032()
        case 7n+l:
          %r8_5_far(3, l, 2, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_2000003()
        case 1n:
          %r8_6_1(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0200003()
        case 2n:
          %r8_6_2(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0020003()
        case 3n:
          %r8_6_3(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0002003()
        case 4n:
          %r8_6_4(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0000203()
        case 5n:
          %r8_6_5(3, 2, ev8_3(), ev8_2()) : ok8(_)
          p8_0000023()
        case 6n:
          %r8_6_6(3, 2) : ok8(_)
          %xr8_3_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(3, l, 2, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 3, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 3, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 3, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 3, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 3, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 3, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 3, l, 2) : ok8(_)
          p8_0000000()

def q8_3_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 3) : ok8(_)
          %xr8_3_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3300000()
        case 2n:
          %r8_0_2(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3030000()
        case 3n:
          %r8_0_3(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3003000()
        case 4n:
          %r8_0_4(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3000300()
        case 5n:
          %r8_0_5(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3000030()
        case 6n:
          %r8_0_6(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3000003()
        case 7n+l:
          %r8_0_far(3, l, 3, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3300000()
        case 1n:
          %r8_1_1(3, 3) : ok8(_)
          %xr8_3_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0330000()
        case 3n:
          %r8_1_3(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0303000()
        case 4n:
          %r8_1_4(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0300300()
        case 5n:
          %r8_1_5(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0300030()
        case 6n:
          %r8_1_6(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0300003()
        case 7n+l:
          %r8_1_far(3, l, 3, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3030000()
        case 1n:
          %r8_2_1(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0330000()
        case 2n:
          %r8_2_2(3, 3) : ok8(_)
          %xr8_3_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0033000()
        case 4n:
          %r8_2_4(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0030300()
        case 5n:
          %r8_2_5(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0030030()
        case 6n:
          %r8_2_6(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0030003()
        case 7n+l:
          %r8_2_far(3, l, 3, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3003000()
        case 1n:
          %r8_3_1(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0303000()
        case 2n:
          %r8_3_2(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0033000()
        case 3n:
          %r8_3_3(3, 3) : ok8(_)
          %xr8_3_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0003300()
        case 5n:
          %r8_3_5(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0003030()
        case 6n:
          %r8_3_6(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0003003()
        case 7n+l:
          %r8_3_far(3, l, 3, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3000300()
        case 1n:
          %r8_4_1(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0300300()
        case 2n:
          %r8_4_2(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0030300()
        case 3n:
          %r8_4_3(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0003300()
        case 4n:
          %r8_4_4(3, 3) : ok8(_)
          %xr8_3_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0000330()
        case 6n:
          %r8_4_6(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0000303()
        case 7n+l:
          %r8_4_far(3, l, 3, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3000030()
        case 1n:
          %r8_5_1(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0300030()
        case 2n:
          %r8_5_2(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0030030()
        case 3n:
          %r8_5_3(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0003030()
        case 4n:
          %r8_5_4(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0000330()
        case 5n:
          %r8_5_5(3, 3) : ok8(_)
          %xr8_3_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0000033()
        case 7n+l:
          %r8_5_far(3, l, 3, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_3000003()
        case 1n:
          %r8_6_1(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0300003()
        case 2n:
          %r8_6_2(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0030003()
        case 3n:
          %r8_6_3(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0003003()
        case 4n:
          %r8_6_4(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0000303()
        case 5n:
          %r8_6_5(3, 3, ev8_3(), ev8_3()) : ok8(_)
          p8_0000033()
        case 6n:
          %r8_6_6(3, 3) : ok8(_)
          %xr8_3_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(3, l, 3, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 3, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 3, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 3, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 3, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 3, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 3, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 3, l, 3) : ok8(_)
          p8_0000000()

def q8_3_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 4) : ok8(_)
          %xr8_3_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_3400000()
        case 2n:
          %r8_0_2(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_3040000()
        case 3n:
          %r8_0_3(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_3004000()
        case 4n:
          %r8_0_4(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_3000400()
        case 5n:
          %r8_0_5(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_3000040()
        case 6n:
          %r8_0_6(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_3000004()
        case 7n+l:
          %r8_0_far(3, l, 4, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_4300000()
        case 1n:
          %r8_1_1(3, 4) : ok8(_)
          %xr8_3_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0340000()
        case 3n:
          %r8_1_3(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0304000()
        case 4n:
          %r8_1_4(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0300400()
        case 5n:
          %r8_1_5(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0300040()
        case 6n:
          %r8_1_6(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0300004()
        case 7n+l:
          %r8_1_far(3, l, 4, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_4030000()
        case 1n:
          %r8_2_1(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0430000()
        case 2n:
          %r8_2_2(3, 4) : ok8(_)
          %xr8_3_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0034000()
        case 4n:
          %r8_2_4(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0030400()
        case 5n:
          %r8_2_5(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0030040()
        case 6n:
          %r8_2_6(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0030004()
        case 7n+l:
          %r8_2_far(3, l, 4, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_4003000()
        case 1n:
          %r8_3_1(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0403000()
        case 2n:
          %r8_3_2(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0043000()
        case 3n:
          %r8_3_3(3, 4) : ok8(_)
          %xr8_3_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0003400()
        case 5n:
          %r8_3_5(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0003040()
        case 6n:
          %r8_3_6(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0003004()
        case 7n+l:
          %r8_3_far(3, l, 4, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_4000300()
        case 1n:
          %r8_4_1(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0400300()
        case 2n:
          %r8_4_2(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0040300()
        case 3n:
          %r8_4_3(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0004300()
        case 4n:
          %r8_4_4(3, 4) : ok8(_)
          %xr8_3_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0000340()
        case 6n:
          %r8_4_6(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0000304()
        case 7n+l:
          %r8_4_far(3, l, 4, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_4000030()
        case 1n:
          %r8_5_1(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0400030()
        case 2n:
          %r8_5_2(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0040030()
        case 3n:
          %r8_5_3(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0004030()
        case 4n:
          %r8_5_4(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0000430()
        case 5n:
          %r8_5_5(3, 4) : ok8(_)
          %xr8_3_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0000034()
        case 7n+l:
          %r8_5_far(3, l, 4, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_4000003()
        case 1n:
          %r8_6_1(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0400003()
        case 2n:
          %r8_6_2(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0040003()
        case 3n:
          %r8_6_3(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0004003()
        case 4n:
          %r8_6_4(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0000403()
        case 5n:
          %r8_6_5(3, 4, ev8_3(), ev8_4()) : ok8(_)
          p8_0000043()
        case 6n:
          %r8_6_6(3, 4) : ok8(_)
          %xr8_3_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(3, l, 4, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 3, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 3, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 3, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 3, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 3, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 3, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 3, l, 4) : ok8(_)
          p8_0000000()

def q8_3_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 5) : ok8(_)
          %xr8_3_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_3500000()
        case 2n:
          %r8_0_2(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_3050000()
        case 3n:
          %r8_0_3(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_3005000()
        case 4n:
          %r8_0_4(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_3000500()
        case 5n:
          %r8_0_5(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_3000050()
        case 6n:
          %r8_0_6(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_3000005()
        case 7n+l:
          %r8_0_far(3, l, 5, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_5300000()
        case 1n:
          %r8_1_1(3, 5) : ok8(_)
          %xr8_3_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0350000()
        case 3n:
          %r8_1_3(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0305000()
        case 4n:
          %r8_1_4(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0300500()
        case 5n:
          %r8_1_5(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0300050()
        case 6n:
          %r8_1_6(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0300005()
        case 7n+l:
          %r8_1_far(3, l, 5, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_5030000()
        case 1n:
          %r8_2_1(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0530000()
        case 2n:
          %r8_2_2(3, 5) : ok8(_)
          %xr8_3_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0035000()
        case 4n:
          %r8_2_4(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0030500()
        case 5n:
          %r8_2_5(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0030050()
        case 6n:
          %r8_2_6(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0030005()
        case 7n+l:
          %r8_2_far(3, l, 5, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_5003000()
        case 1n:
          %r8_3_1(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0503000()
        case 2n:
          %r8_3_2(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0053000()
        case 3n:
          %r8_3_3(3, 5) : ok8(_)
          %xr8_3_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0003500()
        case 5n:
          %r8_3_5(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0003050()
        case 6n:
          %r8_3_6(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0003005()
        case 7n+l:
          %r8_3_far(3, l, 5, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_5000300()
        case 1n:
          %r8_4_1(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0500300()
        case 2n:
          %r8_4_2(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0050300()
        case 3n:
          %r8_4_3(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0005300()
        case 4n:
          %r8_4_4(3, 5) : ok8(_)
          %xr8_3_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0000350()
        case 6n:
          %r8_4_6(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0000305()
        case 7n+l:
          %r8_4_far(3, l, 5, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_5000030()
        case 1n:
          %r8_5_1(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0500030()
        case 2n:
          %r8_5_2(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0050030()
        case 3n:
          %r8_5_3(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0005030()
        case 4n:
          %r8_5_4(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0000530()
        case 5n:
          %r8_5_5(3, 5) : ok8(_)
          %xr8_3_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0000035()
        case 7n+l:
          %r8_5_far(3, l, 5, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_5000003()
        case 1n:
          %r8_6_1(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0500003()
        case 2n:
          %r8_6_2(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0050003()
        case 3n:
          %r8_6_3(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0005003()
        case 4n:
          %r8_6_4(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0000503()
        case 5n:
          %r8_6_5(3, 5, ev8_3(), ev8_5()) : ok8(_)
          p8_0000053()
        case 6n:
          %r8_6_6(3, 5) : ok8(_)
          %xr8_3_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(3, l, 5, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 3, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 3, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 3, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 3, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 3, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 3, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 3, l, 5) : ok8(_)
          p8_0000000()

def q8_3_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 6) : ok8(_)
          %xr8_3_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_3600000()
        case 2n:
          %r8_0_2(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_3060000()
        case 3n:
          %r8_0_3(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_3006000()
        case 4n:
          %r8_0_4(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_3000600()
        case 5n:
          %r8_0_5(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_3000060()
        case 6n:
          %r8_0_6(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_3000006()
        case 7n+l:
          %r8_0_far(3, l, 6, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_6300000()
        case 1n:
          %r8_1_1(3, 6) : ok8(_)
          %xr8_3_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0360000()
        case 3n:
          %r8_1_3(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0306000()
        case 4n:
          %r8_1_4(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0300600()
        case 5n:
          %r8_1_5(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0300060()
        case 6n:
          %r8_1_6(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0300006()
        case 7n+l:
          %r8_1_far(3, l, 6, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_6030000()
        case 1n:
          %r8_2_1(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0630000()
        case 2n:
          %r8_2_2(3, 6) : ok8(_)
          %xr8_3_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0036000()
        case 4n:
          %r8_2_4(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0030600()
        case 5n:
          %r8_2_5(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0030060()
        case 6n:
          %r8_2_6(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0030006()
        case 7n+l:
          %r8_2_far(3, l, 6, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_6003000()
        case 1n:
          %r8_3_1(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0603000()
        case 2n:
          %r8_3_2(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0063000()
        case 3n:
          %r8_3_3(3, 6) : ok8(_)
          %xr8_3_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0003600()
        case 5n:
          %r8_3_5(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0003060()
        case 6n:
          %r8_3_6(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0003006()
        case 7n+l:
          %r8_3_far(3, l, 6, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_6000300()
        case 1n:
          %r8_4_1(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0600300()
        case 2n:
          %r8_4_2(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0060300()
        case 3n:
          %r8_4_3(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0006300()
        case 4n:
          %r8_4_4(3, 6) : ok8(_)
          %xr8_3_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0000360()
        case 6n:
          %r8_4_6(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0000306()
        case 7n+l:
          %r8_4_far(3, l, 6, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_6000030()
        case 1n:
          %r8_5_1(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0600030()
        case 2n:
          %r8_5_2(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0060030()
        case 3n:
          %r8_5_3(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0006030()
        case 4n:
          %r8_5_4(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0000630()
        case 5n:
          %r8_5_5(3, 6) : ok8(_)
          %xr8_3_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0000036()
        case 7n+l:
          %r8_5_far(3, l, 6, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_6000003()
        case 1n:
          %r8_6_1(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0600003()
        case 2n:
          %r8_6_2(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0060003()
        case 3n:
          %r8_6_3(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0006003()
        case 4n:
          %r8_6_4(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0000603()
        case 5n:
          %r8_6_5(3, 6, ev8_3(), ev8_6()) : ok8(_)
          p8_0000063()
        case 6n:
          %r8_6_6(3, 6) : ok8(_)
          %xr8_3_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(3, l, 6, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 3, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 3, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 3, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 3, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 3, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 3, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 3, l, 6) : ok8(_)
          p8_0000000()

def q8_3_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(3, 7) : ok8(_)
          %xr8_3_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_3700000()
        case 2n:
          %r8_0_2(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_3070000()
        case 3n:
          %r8_0_3(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_3007000()
        case 4n:
          %r8_0_4(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_3000700()
        case 5n:
          %r8_0_5(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_3000070()
        case 6n:
          %r8_0_6(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_3000007()
        case 7n+l:
          %r8_0_far(3, l, 7, ev8_3()) : ok8(_)
          p8_3000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_7300000()
        case 1n:
          %r8_1_1(3, 7) : ok8(_)
          %xr8_3_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0370000()
        case 3n:
          %r8_1_3(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0307000()
        case 4n:
          %r8_1_4(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0300700()
        case 5n:
          %r8_1_5(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0300070()
        case 6n:
          %r8_1_6(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0300007()
        case 7n+l:
          %r8_1_far(3, l, 7, ev8_3()) : ok8(_)
          p8_0300000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_7030000()
        case 1n:
          %r8_2_1(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0730000()
        case 2n:
          %r8_2_2(3, 7) : ok8(_)
          %xr8_3_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0037000()
        case 4n:
          %r8_2_4(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0030700()
        case 5n:
          %r8_2_5(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0030070()
        case 6n:
          %r8_2_6(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0030007()
        case 7n+l:
          %r8_2_far(3, l, 7, ev8_3()) : ok8(_)
          p8_0030000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_7003000()
        case 1n:
          %r8_3_1(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0703000()
        case 2n:
          %r8_3_2(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0073000()
        case 3n:
          %r8_3_3(3, 7) : ok8(_)
          %xr8_3_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0003700()
        case 5n:
          %r8_3_5(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0003070()
        case 6n:
          %r8_3_6(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0003007()
        case 7n+l:
          %r8_3_far(3, l, 7, ev8_3()) : ok8(_)
          p8_0003000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_7000300()
        case 1n:
          %r8_4_1(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0700300()
        case 2n:
          %r8_4_2(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0070300()
        case 3n:
          %r8_4_3(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0007300()
        case 4n:
          %r8_4_4(3, 7) : ok8(_)
          %xr8_3_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0000370()
        case 6n:
          %r8_4_6(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0000307()
        case 7n+l:
          %r8_4_far(3, l, 7, ev8_3()) : ok8(_)
          p8_0000300()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_7000030()
        case 1n:
          %r8_5_1(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0700030()
        case 2n:
          %r8_5_2(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0070030()
        case 3n:
          %r8_5_3(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0007030()
        case 4n:
          %r8_5_4(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0000730()
        case 5n:
          %r8_5_5(3, 7) : ok8(_)
          %xr8_3_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0000037()
        case 7n+l:
          %r8_5_far(3, l, 7, ev8_3()) : ok8(_)
          p8_0000030()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_7000003()
        case 1n:
          %r8_6_1(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0700003()
        case 2n:
          %r8_6_2(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0070003()
        case 3n:
          %r8_6_3(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0007003()
        case 4n:
          %r8_6_4(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0000703()
        case 5n:
          %r8_6_5(3, 7, ev8_3(), ev8_7()) : ok8(_)
          p8_0000073()
        case 6n:
          %r8_6_6(3, 7) : ok8(_)
          %xr8_3_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(3, l, 7, ev8_3()) : ok8(_)
          p8_0000003()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 3, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 3, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 3, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 3, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 3, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 3, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 3, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 3, l, 7) : ok8(_)
          p8_0000000()

def q8_4_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 0) : ok8(_)
          %xr8_4_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_4000000()
        case 2n:
          %r8_0_2(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_4000000()
        case 3n:
          %r8_0_3(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_4000000()
        case 4n:
          %r8_0_4(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_4000000()
        case 5n:
          %r8_0_5(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_4000000()
        case 6n:
          %r8_0_6(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_4000000()
        case 7n+l:
          %r8_0_far(4, l, 0, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0400000()
        case 1n:
          %r8_1_1(4, 0) : ok8(_)
          %xr8_4_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0400000()
        case 3n:
          %r8_1_3(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0400000()
        case 4n:
          %r8_1_4(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0400000()
        case 5n:
          %r8_1_5(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0400000()
        case 6n:
          %r8_1_6(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0400000()
        case 7n+l:
          %r8_1_far(4, l, 0, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0040000()
        case 1n:
          %r8_2_1(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0040000()
        case 2n:
          %r8_2_2(4, 0) : ok8(_)
          %xr8_4_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0040000()
        case 4n:
          %r8_2_4(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0040000()
        case 5n:
          %r8_2_5(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0040000()
        case 6n:
          %r8_2_6(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0040000()
        case 7n+l:
          %r8_2_far(4, l, 0, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0004000()
        case 1n:
          %r8_3_1(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0004000()
        case 2n:
          %r8_3_2(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0004000()
        case 3n:
          %r8_3_3(4, 0) : ok8(_)
          %xr8_4_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0004000()
        case 5n:
          %r8_3_5(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0004000()
        case 6n:
          %r8_3_6(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0004000()
        case 7n+l:
          %r8_3_far(4, l, 0, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000400()
        case 1n:
          %r8_4_1(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000400()
        case 2n:
          %r8_4_2(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000400()
        case 3n:
          %r8_4_3(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000400()
        case 4n:
          %r8_4_4(4, 0) : ok8(_)
          %xr8_4_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000400()
        case 6n:
          %r8_4_6(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000400()
        case 7n+l:
          %r8_4_far(4, l, 0, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000040()
        case 1n:
          %r8_5_1(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000040()
        case 2n:
          %r8_5_2(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000040()
        case 3n:
          %r8_5_3(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000040()
        case 4n:
          %r8_5_4(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000040()
        case 5n:
          %r8_5_5(4, 0) : ok8(_)
          %xr8_4_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000040()
        case 7n+l:
          %r8_5_far(4, l, 0, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000004()
        case 1n:
          %r8_6_1(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000004()
        case 2n:
          %r8_6_2(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000004()
        case 3n:
          %r8_6_3(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000004()
        case 4n:
          %r8_6_4(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000004()
        case 5n:
          %r8_6_5(4, 0, ev8_4(), ev8_0()) : ok8(_)
          p8_0000004()
        case 6n:
          %r8_6_6(4, 0) : ok8(_)
          %xr8_4_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(4, l, 0, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 4, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 4, l, 0) : ok8(_)
          p8_0000000()

def q8_4_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 1) : ok8(_)
          %xr8_4_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_4100000()
        case 2n:
          %r8_0_2(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_4010000()
        case 3n:
          %r8_0_3(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_4001000()
        case 4n:
          %r8_0_4(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_4000100()
        case 5n:
          %r8_0_5(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_4000010()
        case 6n:
          %r8_0_6(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_4000001()
        case 7n+l:
          %r8_0_far(4, l, 1, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_1400000()
        case 1n:
          %r8_1_1(4, 1) : ok8(_)
          %xr8_4_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0410000()
        case 3n:
          %r8_1_3(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0401000()
        case 4n:
          %r8_1_4(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0400100()
        case 5n:
          %r8_1_5(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0400010()
        case 6n:
          %r8_1_6(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0400001()
        case 7n+l:
          %r8_1_far(4, l, 1, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_1040000()
        case 1n:
          %r8_2_1(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0140000()
        case 2n:
          %r8_2_2(4, 1) : ok8(_)
          %xr8_4_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0041000()
        case 4n:
          %r8_2_4(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0040100()
        case 5n:
          %r8_2_5(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0040010()
        case 6n:
          %r8_2_6(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0040001()
        case 7n+l:
          %r8_2_far(4, l, 1, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_1004000()
        case 1n:
          %r8_3_1(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0104000()
        case 2n:
          %r8_3_2(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0014000()
        case 3n:
          %r8_3_3(4, 1) : ok8(_)
          %xr8_4_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0004100()
        case 5n:
          %r8_3_5(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0004010()
        case 6n:
          %r8_3_6(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0004001()
        case 7n+l:
          %r8_3_far(4, l, 1, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_1000400()
        case 1n:
          %r8_4_1(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0100400()
        case 2n:
          %r8_4_2(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0010400()
        case 3n:
          %r8_4_3(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0001400()
        case 4n:
          %r8_4_4(4, 1) : ok8(_)
          %xr8_4_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0000410()
        case 6n:
          %r8_4_6(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0000401()
        case 7n+l:
          %r8_4_far(4, l, 1, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_1000040()
        case 1n:
          %r8_5_1(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0100040()
        case 2n:
          %r8_5_2(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0010040()
        case 3n:
          %r8_5_3(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0001040()
        case 4n:
          %r8_5_4(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0000140()
        case 5n:
          %r8_5_5(4, 1) : ok8(_)
          %xr8_4_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0000041()
        case 7n+l:
          %r8_5_far(4, l, 1, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_1000004()
        case 1n:
          %r8_6_1(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0100004()
        case 2n:
          %r8_6_2(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0010004()
        case 3n:
          %r8_6_3(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0001004()
        case 4n:
          %r8_6_4(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0000104()
        case 5n:
          %r8_6_5(4, 1, ev8_4(), ev8_1()) : ok8(_)
          p8_0000014()
        case 6n:
          %r8_6_6(4, 1) : ok8(_)
          %xr8_4_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(4, l, 1, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 4, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 4, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 4, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 4, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 4, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 4, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 4, l, 1) : ok8(_)
          p8_0000000()

def q8_4_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 2) : ok8(_)
          %xr8_4_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_4200000()
        case 2n:
          %r8_0_2(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_4020000()
        case 3n:
          %r8_0_3(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_4002000()
        case 4n:
          %r8_0_4(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_4000200()
        case 5n:
          %r8_0_5(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_4000020()
        case 6n:
          %r8_0_6(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_4000002()
        case 7n+l:
          %r8_0_far(4, l, 2, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_2400000()
        case 1n:
          %r8_1_1(4, 2) : ok8(_)
          %xr8_4_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0420000()
        case 3n:
          %r8_1_3(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0402000()
        case 4n:
          %r8_1_4(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0400200()
        case 5n:
          %r8_1_5(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0400020()
        case 6n:
          %r8_1_6(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0400002()
        case 7n+l:
          %r8_1_far(4, l, 2, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_2040000()
        case 1n:
          %r8_2_1(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0240000()
        case 2n:
          %r8_2_2(4, 2) : ok8(_)
          %xr8_4_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0042000()
        case 4n:
          %r8_2_4(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0040200()
        case 5n:
          %r8_2_5(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0040020()
        case 6n:
          %r8_2_6(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0040002()
        case 7n+l:
          %r8_2_far(4, l, 2, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_2004000()
        case 1n:
          %r8_3_1(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0204000()
        case 2n:
          %r8_3_2(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0024000()
        case 3n:
          %r8_3_3(4, 2) : ok8(_)
          %xr8_4_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0004200()
        case 5n:
          %r8_3_5(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0004020()
        case 6n:
          %r8_3_6(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0004002()
        case 7n+l:
          %r8_3_far(4, l, 2, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_2000400()
        case 1n:
          %r8_4_1(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0200400()
        case 2n:
          %r8_4_2(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0020400()
        case 3n:
          %r8_4_3(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0002400()
        case 4n:
          %r8_4_4(4, 2) : ok8(_)
          %xr8_4_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0000420()
        case 6n:
          %r8_4_6(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0000402()
        case 7n+l:
          %r8_4_far(4, l, 2, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_2000040()
        case 1n:
          %r8_5_1(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0200040()
        case 2n:
          %r8_5_2(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0020040()
        case 3n:
          %r8_5_3(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0002040()
        case 4n:
          %r8_5_4(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0000240()
        case 5n:
          %r8_5_5(4, 2) : ok8(_)
          %xr8_4_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0000042()
        case 7n+l:
          %r8_5_far(4, l, 2, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_2000004()
        case 1n:
          %r8_6_1(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0200004()
        case 2n:
          %r8_6_2(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0020004()
        case 3n:
          %r8_6_3(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0002004()
        case 4n:
          %r8_6_4(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0000204()
        case 5n:
          %r8_6_5(4, 2, ev8_4(), ev8_2()) : ok8(_)
          p8_0000024()
        case 6n:
          %r8_6_6(4, 2) : ok8(_)
          %xr8_4_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(4, l, 2, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 4, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 4, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 4, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 4, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 4, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 4, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 4, l, 2) : ok8(_)
          p8_0000000()

def q8_4_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 3) : ok8(_)
          %xr8_4_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_4300000()
        case 2n:
          %r8_0_2(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_4030000()
        case 3n:
          %r8_0_3(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_4003000()
        case 4n:
          %r8_0_4(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_4000300()
        case 5n:
          %r8_0_5(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_4000030()
        case 6n:
          %r8_0_6(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_4000003()
        case 7n+l:
          %r8_0_far(4, l, 3, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_3400000()
        case 1n:
          %r8_1_1(4, 3) : ok8(_)
          %xr8_4_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0430000()
        case 3n:
          %r8_1_3(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0403000()
        case 4n:
          %r8_1_4(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0400300()
        case 5n:
          %r8_1_5(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0400030()
        case 6n:
          %r8_1_6(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0400003()
        case 7n+l:
          %r8_1_far(4, l, 3, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_3040000()
        case 1n:
          %r8_2_1(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0340000()
        case 2n:
          %r8_2_2(4, 3) : ok8(_)
          %xr8_4_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0043000()
        case 4n:
          %r8_2_4(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0040300()
        case 5n:
          %r8_2_5(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0040030()
        case 6n:
          %r8_2_6(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0040003()
        case 7n+l:
          %r8_2_far(4, l, 3, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_3004000()
        case 1n:
          %r8_3_1(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0304000()
        case 2n:
          %r8_3_2(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0034000()
        case 3n:
          %r8_3_3(4, 3) : ok8(_)
          %xr8_4_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0004300()
        case 5n:
          %r8_3_5(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0004030()
        case 6n:
          %r8_3_6(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0004003()
        case 7n+l:
          %r8_3_far(4, l, 3, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_3000400()
        case 1n:
          %r8_4_1(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0300400()
        case 2n:
          %r8_4_2(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0030400()
        case 3n:
          %r8_4_3(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0003400()
        case 4n:
          %r8_4_4(4, 3) : ok8(_)
          %xr8_4_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0000430()
        case 6n:
          %r8_4_6(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0000403()
        case 7n+l:
          %r8_4_far(4, l, 3, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_3000040()
        case 1n:
          %r8_5_1(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0300040()
        case 2n:
          %r8_5_2(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0030040()
        case 3n:
          %r8_5_3(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0003040()
        case 4n:
          %r8_5_4(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0000340()
        case 5n:
          %r8_5_5(4, 3) : ok8(_)
          %xr8_4_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0000043()
        case 7n+l:
          %r8_5_far(4, l, 3, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_3000004()
        case 1n:
          %r8_6_1(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0300004()
        case 2n:
          %r8_6_2(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0030004()
        case 3n:
          %r8_6_3(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0003004()
        case 4n:
          %r8_6_4(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0000304()
        case 5n:
          %r8_6_5(4, 3, ev8_4(), ev8_3()) : ok8(_)
          p8_0000034()
        case 6n:
          %r8_6_6(4, 3) : ok8(_)
          %xr8_4_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(4, l, 3, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 4, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 4, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 4, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 4, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 4, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 4, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 4, l, 3) : ok8(_)
          p8_0000000()

def q8_4_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 4) : ok8(_)
          %xr8_4_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4400000()
        case 2n:
          %r8_0_2(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4040000()
        case 3n:
          %r8_0_3(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4004000()
        case 4n:
          %r8_0_4(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4000400()
        case 5n:
          %r8_0_5(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4000040()
        case 6n:
          %r8_0_6(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4000004()
        case 7n+l:
          %r8_0_far(4, l, 4, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4400000()
        case 1n:
          %r8_1_1(4, 4) : ok8(_)
          %xr8_4_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0440000()
        case 3n:
          %r8_1_3(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0404000()
        case 4n:
          %r8_1_4(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0400400()
        case 5n:
          %r8_1_5(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0400040()
        case 6n:
          %r8_1_6(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0400004()
        case 7n+l:
          %r8_1_far(4, l, 4, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4040000()
        case 1n:
          %r8_2_1(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0440000()
        case 2n:
          %r8_2_2(4, 4) : ok8(_)
          %xr8_4_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0044000()
        case 4n:
          %r8_2_4(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0040400()
        case 5n:
          %r8_2_5(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0040040()
        case 6n:
          %r8_2_6(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0040004()
        case 7n+l:
          %r8_2_far(4, l, 4, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4004000()
        case 1n:
          %r8_3_1(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0404000()
        case 2n:
          %r8_3_2(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0044000()
        case 3n:
          %r8_3_3(4, 4) : ok8(_)
          %xr8_4_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0004400()
        case 5n:
          %r8_3_5(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0004040()
        case 6n:
          %r8_3_6(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0004004()
        case 7n+l:
          %r8_3_far(4, l, 4, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4000400()
        case 1n:
          %r8_4_1(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0400400()
        case 2n:
          %r8_4_2(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0040400()
        case 3n:
          %r8_4_3(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0004400()
        case 4n:
          %r8_4_4(4, 4) : ok8(_)
          %xr8_4_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0000440()
        case 6n:
          %r8_4_6(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0000404()
        case 7n+l:
          %r8_4_far(4, l, 4, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4000040()
        case 1n:
          %r8_5_1(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0400040()
        case 2n:
          %r8_5_2(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0040040()
        case 3n:
          %r8_5_3(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0004040()
        case 4n:
          %r8_5_4(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0000440()
        case 5n:
          %r8_5_5(4, 4) : ok8(_)
          %xr8_4_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0000044()
        case 7n+l:
          %r8_5_far(4, l, 4, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_4000004()
        case 1n:
          %r8_6_1(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0400004()
        case 2n:
          %r8_6_2(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0040004()
        case 3n:
          %r8_6_3(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0004004()
        case 4n:
          %r8_6_4(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0000404()
        case 5n:
          %r8_6_5(4, 4, ev8_4(), ev8_4()) : ok8(_)
          p8_0000044()
        case 6n:
          %r8_6_6(4, 4) : ok8(_)
          %xr8_4_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(4, l, 4, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 4, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 4, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 4, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 4, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 4, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 4, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 4, l, 4) : ok8(_)
          p8_0000000()

def q8_4_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 5) : ok8(_)
          %xr8_4_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_4500000()
        case 2n:
          %r8_0_2(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_4050000()
        case 3n:
          %r8_0_3(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_4005000()
        case 4n:
          %r8_0_4(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_4000500()
        case 5n:
          %r8_0_5(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_4000050()
        case 6n:
          %r8_0_6(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_4000005()
        case 7n+l:
          %r8_0_far(4, l, 5, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_5400000()
        case 1n:
          %r8_1_1(4, 5) : ok8(_)
          %xr8_4_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0450000()
        case 3n:
          %r8_1_3(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0405000()
        case 4n:
          %r8_1_4(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0400500()
        case 5n:
          %r8_1_5(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0400050()
        case 6n:
          %r8_1_6(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0400005()
        case 7n+l:
          %r8_1_far(4, l, 5, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_5040000()
        case 1n:
          %r8_2_1(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0540000()
        case 2n:
          %r8_2_2(4, 5) : ok8(_)
          %xr8_4_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0045000()
        case 4n:
          %r8_2_4(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0040500()
        case 5n:
          %r8_2_5(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0040050()
        case 6n:
          %r8_2_6(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0040005()
        case 7n+l:
          %r8_2_far(4, l, 5, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_5004000()
        case 1n:
          %r8_3_1(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0504000()
        case 2n:
          %r8_3_2(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0054000()
        case 3n:
          %r8_3_3(4, 5) : ok8(_)
          %xr8_4_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0004500()
        case 5n:
          %r8_3_5(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0004050()
        case 6n:
          %r8_3_6(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0004005()
        case 7n+l:
          %r8_3_far(4, l, 5, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_5000400()
        case 1n:
          %r8_4_1(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0500400()
        case 2n:
          %r8_4_2(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0050400()
        case 3n:
          %r8_4_3(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0005400()
        case 4n:
          %r8_4_4(4, 5) : ok8(_)
          %xr8_4_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0000450()
        case 6n:
          %r8_4_6(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0000405()
        case 7n+l:
          %r8_4_far(4, l, 5, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_5000040()
        case 1n:
          %r8_5_1(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0500040()
        case 2n:
          %r8_5_2(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0050040()
        case 3n:
          %r8_5_3(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0005040()
        case 4n:
          %r8_5_4(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0000540()
        case 5n:
          %r8_5_5(4, 5) : ok8(_)
          %xr8_4_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0000045()
        case 7n+l:
          %r8_5_far(4, l, 5, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_5000004()
        case 1n:
          %r8_6_1(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0500004()
        case 2n:
          %r8_6_2(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0050004()
        case 3n:
          %r8_6_3(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0005004()
        case 4n:
          %r8_6_4(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0000504()
        case 5n:
          %r8_6_5(4, 5, ev8_4(), ev8_5()) : ok8(_)
          p8_0000054()
        case 6n:
          %r8_6_6(4, 5) : ok8(_)
          %xr8_4_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(4, l, 5, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 4, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 4, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 4, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 4, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 4, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 4, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 4, l, 5) : ok8(_)
          p8_0000000()

def q8_4_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 6) : ok8(_)
          %xr8_4_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_4600000()
        case 2n:
          %r8_0_2(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_4060000()
        case 3n:
          %r8_0_3(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_4006000()
        case 4n:
          %r8_0_4(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_4000600()
        case 5n:
          %r8_0_5(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_4000060()
        case 6n:
          %r8_0_6(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_4000006()
        case 7n+l:
          %r8_0_far(4, l, 6, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_6400000()
        case 1n:
          %r8_1_1(4, 6) : ok8(_)
          %xr8_4_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0460000()
        case 3n:
          %r8_1_3(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0406000()
        case 4n:
          %r8_1_4(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0400600()
        case 5n:
          %r8_1_5(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0400060()
        case 6n:
          %r8_1_6(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0400006()
        case 7n+l:
          %r8_1_far(4, l, 6, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_6040000()
        case 1n:
          %r8_2_1(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0640000()
        case 2n:
          %r8_2_2(4, 6) : ok8(_)
          %xr8_4_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0046000()
        case 4n:
          %r8_2_4(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0040600()
        case 5n:
          %r8_2_5(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0040060()
        case 6n:
          %r8_2_6(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0040006()
        case 7n+l:
          %r8_2_far(4, l, 6, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_6004000()
        case 1n:
          %r8_3_1(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0604000()
        case 2n:
          %r8_3_2(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0064000()
        case 3n:
          %r8_3_3(4, 6) : ok8(_)
          %xr8_4_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0004600()
        case 5n:
          %r8_3_5(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0004060()
        case 6n:
          %r8_3_6(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0004006()
        case 7n+l:
          %r8_3_far(4, l, 6, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_6000400()
        case 1n:
          %r8_4_1(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0600400()
        case 2n:
          %r8_4_2(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0060400()
        case 3n:
          %r8_4_3(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0006400()
        case 4n:
          %r8_4_4(4, 6) : ok8(_)
          %xr8_4_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0000460()
        case 6n:
          %r8_4_6(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0000406()
        case 7n+l:
          %r8_4_far(4, l, 6, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_6000040()
        case 1n:
          %r8_5_1(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0600040()
        case 2n:
          %r8_5_2(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0060040()
        case 3n:
          %r8_5_3(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0006040()
        case 4n:
          %r8_5_4(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0000640()
        case 5n:
          %r8_5_5(4, 6) : ok8(_)
          %xr8_4_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0000046()
        case 7n+l:
          %r8_5_far(4, l, 6, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_6000004()
        case 1n:
          %r8_6_1(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0600004()
        case 2n:
          %r8_6_2(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0060004()
        case 3n:
          %r8_6_3(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0006004()
        case 4n:
          %r8_6_4(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0000604()
        case 5n:
          %r8_6_5(4, 6, ev8_4(), ev8_6()) : ok8(_)
          p8_0000064()
        case 6n:
          %r8_6_6(4, 6) : ok8(_)
          %xr8_4_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(4, l, 6, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 4, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 4, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 4, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 4, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 4, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 4, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 4, l, 6) : ok8(_)
          p8_0000000()

def q8_4_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(4, 7) : ok8(_)
          %xr8_4_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_4700000()
        case 2n:
          %r8_0_2(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_4070000()
        case 3n:
          %r8_0_3(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_4007000()
        case 4n:
          %r8_0_4(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_4000700()
        case 5n:
          %r8_0_5(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_4000070()
        case 6n:
          %r8_0_6(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_4000007()
        case 7n+l:
          %r8_0_far(4, l, 7, ev8_4()) : ok8(_)
          p8_4000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_7400000()
        case 1n:
          %r8_1_1(4, 7) : ok8(_)
          %xr8_4_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0470000()
        case 3n:
          %r8_1_3(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0407000()
        case 4n:
          %r8_1_4(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0400700()
        case 5n:
          %r8_1_5(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0400070()
        case 6n:
          %r8_1_6(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0400007()
        case 7n+l:
          %r8_1_far(4, l, 7, ev8_4()) : ok8(_)
          p8_0400000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_7040000()
        case 1n:
          %r8_2_1(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0740000()
        case 2n:
          %r8_2_2(4, 7) : ok8(_)
          %xr8_4_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0047000()
        case 4n:
          %r8_2_4(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0040700()
        case 5n:
          %r8_2_5(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0040070()
        case 6n:
          %r8_2_6(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0040007()
        case 7n+l:
          %r8_2_far(4, l, 7, ev8_4()) : ok8(_)
          p8_0040000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_7004000()
        case 1n:
          %r8_3_1(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0704000()
        case 2n:
          %r8_3_2(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0074000()
        case 3n:
          %r8_3_3(4, 7) : ok8(_)
          %xr8_4_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0004700()
        case 5n:
          %r8_3_5(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0004070()
        case 6n:
          %r8_3_6(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0004007()
        case 7n+l:
          %r8_3_far(4, l, 7, ev8_4()) : ok8(_)
          p8_0004000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_7000400()
        case 1n:
          %r8_4_1(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0700400()
        case 2n:
          %r8_4_2(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0070400()
        case 3n:
          %r8_4_3(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0007400()
        case 4n:
          %r8_4_4(4, 7) : ok8(_)
          %xr8_4_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0000470()
        case 6n:
          %r8_4_6(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0000407()
        case 7n+l:
          %r8_4_far(4, l, 7, ev8_4()) : ok8(_)
          p8_0000400()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_7000040()
        case 1n:
          %r8_5_1(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0700040()
        case 2n:
          %r8_5_2(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0070040()
        case 3n:
          %r8_5_3(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0007040()
        case 4n:
          %r8_5_4(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0000740()
        case 5n:
          %r8_5_5(4, 7) : ok8(_)
          %xr8_4_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0000047()
        case 7n+l:
          %r8_5_far(4, l, 7, ev8_4()) : ok8(_)
          p8_0000040()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_7000004()
        case 1n:
          %r8_6_1(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0700004()
        case 2n:
          %r8_6_2(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0070004()
        case 3n:
          %r8_6_3(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0007004()
        case 4n:
          %r8_6_4(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0000704()
        case 5n:
          %r8_6_5(4, 7, ev8_4(), ev8_7()) : ok8(_)
          p8_0000074()
        case 6n:
          %r8_6_6(4, 7) : ok8(_)
          %xr8_4_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(4, l, 7, ev8_4()) : ok8(_)
          p8_0000004()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 4, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 4, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 4, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 4, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 4, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 4, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 4, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 4, l, 7) : ok8(_)
          p8_0000000()

def q8_5_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 0) : ok8(_)
          %xr8_5_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_5000000()
        case 2n:
          %r8_0_2(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_5000000()
        case 3n:
          %r8_0_3(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_5000000()
        case 4n:
          %r8_0_4(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_5000000()
        case 5n:
          %r8_0_5(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_5000000()
        case 6n:
          %r8_0_6(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_5000000()
        case 7n+l:
          %r8_0_far(5, l, 0, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0500000()
        case 1n:
          %r8_1_1(5, 0) : ok8(_)
          %xr8_5_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0500000()
        case 3n:
          %r8_1_3(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0500000()
        case 4n:
          %r8_1_4(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0500000()
        case 5n:
          %r8_1_5(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0500000()
        case 6n:
          %r8_1_6(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0500000()
        case 7n+l:
          %r8_1_far(5, l, 0, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0050000()
        case 1n:
          %r8_2_1(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0050000()
        case 2n:
          %r8_2_2(5, 0) : ok8(_)
          %xr8_5_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0050000()
        case 4n:
          %r8_2_4(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0050000()
        case 5n:
          %r8_2_5(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0050000()
        case 6n:
          %r8_2_6(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0050000()
        case 7n+l:
          %r8_2_far(5, l, 0, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0005000()
        case 1n:
          %r8_3_1(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0005000()
        case 2n:
          %r8_3_2(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0005000()
        case 3n:
          %r8_3_3(5, 0) : ok8(_)
          %xr8_5_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0005000()
        case 5n:
          %r8_3_5(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0005000()
        case 6n:
          %r8_3_6(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0005000()
        case 7n+l:
          %r8_3_far(5, l, 0, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000500()
        case 1n:
          %r8_4_1(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000500()
        case 2n:
          %r8_4_2(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000500()
        case 3n:
          %r8_4_3(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000500()
        case 4n:
          %r8_4_4(5, 0) : ok8(_)
          %xr8_5_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000500()
        case 6n:
          %r8_4_6(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000500()
        case 7n+l:
          %r8_4_far(5, l, 0, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000050()
        case 1n:
          %r8_5_1(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000050()
        case 2n:
          %r8_5_2(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000050()
        case 3n:
          %r8_5_3(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000050()
        case 4n:
          %r8_5_4(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000050()
        case 5n:
          %r8_5_5(5, 0) : ok8(_)
          %xr8_5_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000050()
        case 7n+l:
          %r8_5_far(5, l, 0, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000005()
        case 1n:
          %r8_6_1(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000005()
        case 2n:
          %r8_6_2(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000005()
        case 3n:
          %r8_6_3(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000005()
        case 4n:
          %r8_6_4(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000005()
        case 5n:
          %r8_6_5(5, 0, ev8_5(), ev8_0()) : ok8(_)
          p8_0000005()
        case 6n:
          %r8_6_6(5, 0) : ok8(_)
          %xr8_5_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(5, l, 0, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 5, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 5, l, 0) : ok8(_)
          p8_0000000()

def q8_5_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 1) : ok8(_)
          %xr8_5_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_5100000()
        case 2n:
          %r8_0_2(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_5010000()
        case 3n:
          %r8_0_3(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_5001000()
        case 4n:
          %r8_0_4(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_5000100()
        case 5n:
          %r8_0_5(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_5000010()
        case 6n:
          %r8_0_6(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_5000001()
        case 7n+l:
          %r8_0_far(5, l, 1, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_1500000()
        case 1n:
          %r8_1_1(5, 1) : ok8(_)
          %xr8_5_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0510000()
        case 3n:
          %r8_1_3(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0501000()
        case 4n:
          %r8_1_4(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0500100()
        case 5n:
          %r8_1_5(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0500010()
        case 6n:
          %r8_1_6(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0500001()
        case 7n+l:
          %r8_1_far(5, l, 1, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_1050000()
        case 1n:
          %r8_2_1(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0150000()
        case 2n:
          %r8_2_2(5, 1) : ok8(_)
          %xr8_5_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0051000()
        case 4n:
          %r8_2_4(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0050100()
        case 5n:
          %r8_2_5(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0050010()
        case 6n:
          %r8_2_6(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0050001()
        case 7n+l:
          %r8_2_far(5, l, 1, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_1005000()
        case 1n:
          %r8_3_1(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0105000()
        case 2n:
          %r8_3_2(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0015000()
        case 3n:
          %r8_3_3(5, 1) : ok8(_)
          %xr8_5_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0005100()
        case 5n:
          %r8_3_5(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0005010()
        case 6n:
          %r8_3_6(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0005001()
        case 7n+l:
          %r8_3_far(5, l, 1, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_1000500()
        case 1n:
          %r8_4_1(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0100500()
        case 2n:
          %r8_4_2(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0010500()
        case 3n:
          %r8_4_3(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0001500()
        case 4n:
          %r8_4_4(5, 1) : ok8(_)
          %xr8_5_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0000510()
        case 6n:
          %r8_4_6(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0000501()
        case 7n+l:
          %r8_4_far(5, l, 1, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_1000050()
        case 1n:
          %r8_5_1(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0100050()
        case 2n:
          %r8_5_2(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0010050()
        case 3n:
          %r8_5_3(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0001050()
        case 4n:
          %r8_5_4(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0000150()
        case 5n:
          %r8_5_5(5, 1) : ok8(_)
          %xr8_5_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0000051()
        case 7n+l:
          %r8_5_far(5, l, 1, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_1000005()
        case 1n:
          %r8_6_1(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0100005()
        case 2n:
          %r8_6_2(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0010005()
        case 3n:
          %r8_6_3(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0001005()
        case 4n:
          %r8_6_4(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0000105()
        case 5n:
          %r8_6_5(5, 1, ev8_5(), ev8_1()) : ok8(_)
          p8_0000015()
        case 6n:
          %r8_6_6(5, 1) : ok8(_)
          %xr8_5_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(5, l, 1, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 5, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 5, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 5, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 5, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 5, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 5, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 5, l, 1) : ok8(_)
          p8_0000000()

def q8_5_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 2) : ok8(_)
          %xr8_5_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_5200000()
        case 2n:
          %r8_0_2(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_5020000()
        case 3n:
          %r8_0_3(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_5002000()
        case 4n:
          %r8_0_4(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_5000200()
        case 5n:
          %r8_0_5(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_5000020()
        case 6n:
          %r8_0_6(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_5000002()
        case 7n+l:
          %r8_0_far(5, l, 2, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_2500000()
        case 1n:
          %r8_1_1(5, 2) : ok8(_)
          %xr8_5_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0520000()
        case 3n:
          %r8_1_3(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0502000()
        case 4n:
          %r8_1_4(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0500200()
        case 5n:
          %r8_1_5(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0500020()
        case 6n:
          %r8_1_6(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0500002()
        case 7n+l:
          %r8_1_far(5, l, 2, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_2050000()
        case 1n:
          %r8_2_1(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0250000()
        case 2n:
          %r8_2_2(5, 2) : ok8(_)
          %xr8_5_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0052000()
        case 4n:
          %r8_2_4(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0050200()
        case 5n:
          %r8_2_5(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0050020()
        case 6n:
          %r8_2_6(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0050002()
        case 7n+l:
          %r8_2_far(5, l, 2, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_2005000()
        case 1n:
          %r8_3_1(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0205000()
        case 2n:
          %r8_3_2(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0025000()
        case 3n:
          %r8_3_3(5, 2) : ok8(_)
          %xr8_5_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0005200()
        case 5n:
          %r8_3_5(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0005020()
        case 6n:
          %r8_3_6(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0005002()
        case 7n+l:
          %r8_3_far(5, l, 2, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_2000500()
        case 1n:
          %r8_4_1(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0200500()
        case 2n:
          %r8_4_2(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0020500()
        case 3n:
          %r8_4_3(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0002500()
        case 4n:
          %r8_4_4(5, 2) : ok8(_)
          %xr8_5_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0000520()
        case 6n:
          %r8_4_6(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0000502()
        case 7n+l:
          %r8_4_far(5, l, 2, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_2000050()
        case 1n:
          %r8_5_1(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0200050()
        case 2n:
          %r8_5_2(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0020050()
        case 3n:
          %r8_5_3(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0002050()
        case 4n:
          %r8_5_4(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0000250()
        case 5n:
          %r8_5_5(5, 2) : ok8(_)
          %xr8_5_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0000052()
        case 7n+l:
          %r8_5_far(5, l, 2, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_2000005()
        case 1n:
          %r8_6_1(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0200005()
        case 2n:
          %r8_6_2(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0020005()
        case 3n:
          %r8_6_3(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0002005()
        case 4n:
          %r8_6_4(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0000205()
        case 5n:
          %r8_6_5(5, 2, ev8_5(), ev8_2()) : ok8(_)
          p8_0000025()
        case 6n:
          %r8_6_6(5, 2) : ok8(_)
          %xr8_5_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(5, l, 2, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 5, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 5, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 5, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 5, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 5, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 5, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 5, l, 2) : ok8(_)
          p8_0000000()

def q8_5_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 3) : ok8(_)
          %xr8_5_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_5300000()
        case 2n:
          %r8_0_2(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_5030000()
        case 3n:
          %r8_0_3(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_5003000()
        case 4n:
          %r8_0_4(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_5000300()
        case 5n:
          %r8_0_5(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_5000030()
        case 6n:
          %r8_0_6(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_5000003()
        case 7n+l:
          %r8_0_far(5, l, 3, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_3500000()
        case 1n:
          %r8_1_1(5, 3) : ok8(_)
          %xr8_5_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0530000()
        case 3n:
          %r8_1_3(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0503000()
        case 4n:
          %r8_1_4(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0500300()
        case 5n:
          %r8_1_5(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0500030()
        case 6n:
          %r8_1_6(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0500003()
        case 7n+l:
          %r8_1_far(5, l, 3, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_3050000()
        case 1n:
          %r8_2_1(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0350000()
        case 2n:
          %r8_2_2(5, 3) : ok8(_)
          %xr8_5_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0053000()
        case 4n:
          %r8_2_4(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0050300()
        case 5n:
          %r8_2_5(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0050030()
        case 6n:
          %r8_2_6(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0050003()
        case 7n+l:
          %r8_2_far(5, l, 3, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_3005000()
        case 1n:
          %r8_3_1(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0305000()
        case 2n:
          %r8_3_2(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0035000()
        case 3n:
          %r8_3_3(5, 3) : ok8(_)
          %xr8_5_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0005300()
        case 5n:
          %r8_3_5(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0005030()
        case 6n:
          %r8_3_6(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0005003()
        case 7n+l:
          %r8_3_far(5, l, 3, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_3000500()
        case 1n:
          %r8_4_1(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0300500()
        case 2n:
          %r8_4_2(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0030500()
        case 3n:
          %r8_4_3(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0003500()
        case 4n:
          %r8_4_4(5, 3) : ok8(_)
          %xr8_5_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0000530()
        case 6n:
          %r8_4_6(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0000503()
        case 7n+l:
          %r8_4_far(5, l, 3, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_3000050()
        case 1n:
          %r8_5_1(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0300050()
        case 2n:
          %r8_5_2(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0030050()
        case 3n:
          %r8_5_3(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0003050()
        case 4n:
          %r8_5_4(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0000350()
        case 5n:
          %r8_5_5(5, 3) : ok8(_)
          %xr8_5_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0000053()
        case 7n+l:
          %r8_5_far(5, l, 3, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_3000005()
        case 1n:
          %r8_6_1(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0300005()
        case 2n:
          %r8_6_2(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0030005()
        case 3n:
          %r8_6_3(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0003005()
        case 4n:
          %r8_6_4(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0000305()
        case 5n:
          %r8_6_5(5, 3, ev8_5(), ev8_3()) : ok8(_)
          p8_0000035()
        case 6n:
          %r8_6_6(5, 3) : ok8(_)
          %xr8_5_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(5, l, 3, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 5, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 5, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 5, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 5, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 5, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 5, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 5, l, 3) : ok8(_)
          p8_0000000()

def q8_5_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 4) : ok8(_)
          %xr8_5_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_5400000()
        case 2n:
          %r8_0_2(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_5040000()
        case 3n:
          %r8_0_3(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_5004000()
        case 4n:
          %r8_0_4(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_5000400()
        case 5n:
          %r8_0_5(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_5000040()
        case 6n:
          %r8_0_6(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_5000004()
        case 7n+l:
          %r8_0_far(5, l, 4, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_4500000()
        case 1n:
          %r8_1_1(5, 4) : ok8(_)
          %xr8_5_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0540000()
        case 3n:
          %r8_1_3(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0504000()
        case 4n:
          %r8_1_4(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0500400()
        case 5n:
          %r8_1_5(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0500040()
        case 6n:
          %r8_1_6(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0500004()
        case 7n+l:
          %r8_1_far(5, l, 4, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_4050000()
        case 1n:
          %r8_2_1(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0450000()
        case 2n:
          %r8_2_2(5, 4) : ok8(_)
          %xr8_5_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0054000()
        case 4n:
          %r8_2_4(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0050400()
        case 5n:
          %r8_2_5(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0050040()
        case 6n:
          %r8_2_6(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0050004()
        case 7n+l:
          %r8_2_far(5, l, 4, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_4005000()
        case 1n:
          %r8_3_1(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0405000()
        case 2n:
          %r8_3_2(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0045000()
        case 3n:
          %r8_3_3(5, 4) : ok8(_)
          %xr8_5_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0005400()
        case 5n:
          %r8_3_5(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0005040()
        case 6n:
          %r8_3_6(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0005004()
        case 7n+l:
          %r8_3_far(5, l, 4, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_4000500()
        case 1n:
          %r8_4_1(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0400500()
        case 2n:
          %r8_4_2(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0040500()
        case 3n:
          %r8_4_3(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0004500()
        case 4n:
          %r8_4_4(5, 4) : ok8(_)
          %xr8_5_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0000540()
        case 6n:
          %r8_4_6(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0000504()
        case 7n+l:
          %r8_4_far(5, l, 4, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_4000050()
        case 1n:
          %r8_5_1(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0400050()
        case 2n:
          %r8_5_2(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0040050()
        case 3n:
          %r8_5_3(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0004050()
        case 4n:
          %r8_5_4(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0000450()
        case 5n:
          %r8_5_5(5, 4) : ok8(_)
          %xr8_5_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0000054()
        case 7n+l:
          %r8_5_far(5, l, 4, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_4000005()
        case 1n:
          %r8_6_1(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0400005()
        case 2n:
          %r8_6_2(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0040005()
        case 3n:
          %r8_6_3(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0004005()
        case 4n:
          %r8_6_4(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0000405()
        case 5n:
          %r8_6_5(5, 4, ev8_5(), ev8_4()) : ok8(_)
          p8_0000045()
        case 6n:
          %r8_6_6(5, 4) : ok8(_)
          %xr8_5_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(5, l, 4, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 5, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 5, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 5, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 5, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 5, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 5, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 5, l, 4) : ok8(_)
          p8_0000000()

def q8_5_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 5) : ok8(_)
          %xr8_5_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5500000()
        case 2n:
          %r8_0_2(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5050000()
        case 3n:
          %r8_0_3(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5005000()
        case 4n:
          %r8_0_4(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5000500()
        case 5n:
          %r8_0_5(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5000050()
        case 6n:
          %r8_0_6(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5000005()
        case 7n+l:
          %r8_0_far(5, l, 5, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5500000()
        case 1n:
          %r8_1_1(5, 5) : ok8(_)
          %xr8_5_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0550000()
        case 3n:
          %r8_1_3(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0505000()
        case 4n:
          %r8_1_4(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0500500()
        case 5n:
          %r8_1_5(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0500050()
        case 6n:
          %r8_1_6(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0500005()
        case 7n+l:
          %r8_1_far(5, l, 5, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5050000()
        case 1n:
          %r8_2_1(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0550000()
        case 2n:
          %r8_2_2(5, 5) : ok8(_)
          %xr8_5_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0055000()
        case 4n:
          %r8_2_4(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0050500()
        case 5n:
          %r8_2_5(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0050050()
        case 6n:
          %r8_2_6(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0050005()
        case 7n+l:
          %r8_2_far(5, l, 5, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5005000()
        case 1n:
          %r8_3_1(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0505000()
        case 2n:
          %r8_3_2(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0055000()
        case 3n:
          %r8_3_3(5, 5) : ok8(_)
          %xr8_5_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0005500()
        case 5n:
          %r8_3_5(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0005050()
        case 6n:
          %r8_3_6(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0005005()
        case 7n+l:
          %r8_3_far(5, l, 5, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5000500()
        case 1n:
          %r8_4_1(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0500500()
        case 2n:
          %r8_4_2(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0050500()
        case 3n:
          %r8_4_3(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0005500()
        case 4n:
          %r8_4_4(5, 5) : ok8(_)
          %xr8_5_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0000550()
        case 6n:
          %r8_4_6(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0000505()
        case 7n+l:
          %r8_4_far(5, l, 5, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5000050()
        case 1n:
          %r8_5_1(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0500050()
        case 2n:
          %r8_5_2(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0050050()
        case 3n:
          %r8_5_3(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0005050()
        case 4n:
          %r8_5_4(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0000550()
        case 5n:
          %r8_5_5(5, 5) : ok8(_)
          %xr8_5_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0000055()
        case 7n+l:
          %r8_5_far(5, l, 5, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_5000005()
        case 1n:
          %r8_6_1(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0500005()
        case 2n:
          %r8_6_2(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0050005()
        case 3n:
          %r8_6_3(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0005005()
        case 4n:
          %r8_6_4(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0000505()
        case 5n:
          %r8_6_5(5, 5, ev8_5(), ev8_5()) : ok8(_)
          p8_0000055()
        case 6n:
          %r8_6_6(5, 5) : ok8(_)
          %xr8_5_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(5, l, 5, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 5, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 5, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 5, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 5, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 5, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 5, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 5, l, 5) : ok8(_)
          p8_0000000()

def q8_5_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 6) : ok8(_)
          %xr8_5_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_5600000()
        case 2n:
          %r8_0_2(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_5060000()
        case 3n:
          %r8_0_3(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_5006000()
        case 4n:
          %r8_0_4(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_5000600()
        case 5n:
          %r8_0_5(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_5000060()
        case 6n:
          %r8_0_6(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_5000006()
        case 7n+l:
          %r8_0_far(5, l, 6, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_6500000()
        case 1n:
          %r8_1_1(5, 6) : ok8(_)
          %xr8_5_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0560000()
        case 3n:
          %r8_1_3(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0506000()
        case 4n:
          %r8_1_4(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0500600()
        case 5n:
          %r8_1_5(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0500060()
        case 6n:
          %r8_1_6(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0500006()
        case 7n+l:
          %r8_1_far(5, l, 6, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_6050000()
        case 1n:
          %r8_2_1(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0650000()
        case 2n:
          %r8_2_2(5, 6) : ok8(_)
          %xr8_5_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0056000()
        case 4n:
          %r8_2_4(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0050600()
        case 5n:
          %r8_2_5(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0050060()
        case 6n:
          %r8_2_6(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0050006()
        case 7n+l:
          %r8_2_far(5, l, 6, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_6005000()
        case 1n:
          %r8_3_1(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0605000()
        case 2n:
          %r8_3_2(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0065000()
        case 3n:
          %r8_3_3(5, 6) : ok8(_)
          %xr8_5_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0005600()
        case 5n:
          %r8_3_5(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0005060()
        case 6n:
          %r8_3_6(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0005006()
        case 7n+l:
          %r8_3_far(5, l, 6, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_6000500()
        case 1n:
          %r8_4_1(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0600500()
        case 2n:
          %r8_4_2(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0060500()
        case 3n:
          %r8_4_3(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0006500()
        case 4n:
          %r8_4_4(5, 6) : ok8(_)
          %xr8_5_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0000560()
        case 6n:
          %r8_4_6(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0000506()
        case 7n+l:
          %r8_4_far(5, l, 6, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_6000050()
        case 1n:
          %r8_5_1(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0600050()
        case 2n:
          %r8_5_2(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0060050()
        case 3n:
          %r8_5_3(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0006050()
        case 4n:
          %r8_5_4(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0000650()
        case 5n:
          %r8_5_5(5, 6) : ok8(_)
          %xr8_5_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0000056()
        case 7n+l:
          %r8_5_far(5, l, 6, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_6000005()
        case 1n:
          %r8_6_1(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0600005()
        case 2n:
          %r8_6_2(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0060005()
        case 3n:
          %r8_6_3(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0006005()
        case 4n:
          %r8_6_4(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0000605()
        case 5n:
          %r8_6_5(5, 6, ev8_5(), ev8_6()) : ok8(_)
          p8_0000065()
        case 6n:
          %r8_6_6(5, 6) : ok8(_)
          %xr8_5_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(5, l, 6, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 5, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 5, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 5, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 5, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 5, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 5, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 5, l, 6) : ok8(_)
          p8_0000000()

def q8_5_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(5, 7) : ok8(_)
          %xr8_5_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_5700000()
        case 2n:
          %r8_0_2(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_5070000()
        case 3n:
          %r8_0_3(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_5007000()
        case 4n:
          %r8_0_4(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_5000700()
        case 5n:
          %r8_0_5(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_5000070()
        case 6n:
          %r8_0_6(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_5000007()
        case 7n+l:
          %r8_0_far(5, l, 7, ev8_5()) : ok8(_)
          p8_5000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_7500000()
        case 1n:
          %r8_1_1(5, 7) : ok8(_)
          %xr8_5_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0570000()
        case 3n:
          %r8_1_3(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0507000()
        case 4n:
          %r8_1_4(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0500700()
        case 5n:
          %r8_1_5(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0500070()
        case 6n:
          %r8_1_6(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0500007()
        case 7n+l:
          %r8_1_far(5, l, 7, ev8_5()) : ok8(_)
          p8_0500000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_7050000()
        case 1n:
          %r8_2_1(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0750000()
        case 2n:
          %r8_2_2(5, 7) : ok8(_)
          %xr8_5_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0057000()
        case 4n:
          %r8_2_4(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0050700()
        case 5n:
          %r8_2_5(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0050070()
        case 6n:
          %r8_2_6(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0050007()
        case 7n+l:
          %r8_2_far(5, l, 7, ev8_5()) : ok8(_)
          p8_0050000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_7005000()
        case 1n:
          %r8_3_1(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0705000()
        case 2n:
          %r8_3_2(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0075000()
        case 3n:
          %r8_3_3(5, 7) : ok8(_)
          %xr8_5_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0005700()
        case 5n:
          %r8_3_5(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0005070()
        case 6n:
          %r8_3_6(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0005007()
        case 7n+l:
          %r8_3_far(5, l, 7, ev8_5()) : ok8(_)
          p8_0005000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_7000500()
        case 1n:
          %r8_4_1(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0700500()
        case 2n:
          %r8_4_2(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0070500()
        case 3n:
          %r8_4_3(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0007500()
        case 4n:
          %r8_4_4(5, 7) : ok8(_)
          %xr8_5_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0000570()
        case 6n:
          %r8_4_6(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0000507()
        case 7n+l:
          %r8_4_far(5, l, 7, ev8_5()) : ok8(_)
          p8_0000500()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_7000050()
        case 1n:
          %r8_5_1(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0700050()
        case 2n:
          %r8_5_2(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0070050()
        case 3n:
          %r8_5_3(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0007050()
        case 4n:
          %r8_5_4(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0000750()
        case 5n:
          %r8_5_5(5, 7) : ok8(_)
          %xr8_5_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0000057()
        case 7n+l:
          %r8_5_far(5, l, 7, ev8_5()) : ok8(_)
          p8_0000050()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_7000005()
        case 1n:
          %r8_6_1(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0700005()
        case 2n:
          %r8_6_2(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0070005()
        case 3n:
          %r8_6_3(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0007005()
        case 4n:
          %r8_6_4(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0000705()
        case 5n:
          %r8_6_5(5, 7, ev8_5(), ev8_7()) : ok8(_)
          p8_0000075()
        case 6n:
          %r8_6_6(5, 7) : ok8(_)
          %xr8_5_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(5, l, 7, ev8_5()) : ok8(_)
          p8_0000005()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 5, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 5, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 5, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 5, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 5, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 5, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 5, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 5, l, 7) : ok8(_)
          p8_0000000()

def q8_6_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 0) : ok8(_)
          %xr8_6_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_6000000()
        case 2n:
          %r8_0_2(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_6000000()
        case 3n:
          %r8_0_3(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_6000000()
        case 4n:
          %r8_0_4(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_6000000()
        case 5n:
          %r8_0_5(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_6000000()
        case 6n:
          %r8_0_6(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_6000000()
        case 7n+l:
          %r8_0_far(6, l, 0, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0600000()
        case 1n:
          %r8_1_1(6, 0) : ok8(_)
          %xr8_6_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0600000()
        case 3n:
          %r8_1_3(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0600000()
        case 4n:
          %r8_1_4(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0600000()
        case 5n:
          %r8_1_5(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0600000()
        case 6n:
          %r8_1_6(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0600000()
        case 7n+l:
          %r8_1_far(6, l, 0, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0060000()
        case 1n:
          %r8_2_1(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0060000()
        case 2n:
          %r8_2_2(6, 0) : ok8(_)
          %xr8_6_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0060000()
        case 4n:
          %r8_2_4(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0060000()
        case 5n:
          %r8_2_5(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0060000()
        case 6n:
          %r8_2_6(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0060000()
        case 7n+l:
          %r8_2_far(6, l, 0, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0006000()
        case 1n:
          %r8_3_1(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0006000()
        case 2n:
          %r8_3_2(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0006000()
        case 3n:
          %r8_3_3(6, 0) : ok8(_)
          %xr8_6_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0006000()
        case 5n:
          %r8_3_5(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0006000()
        case 6n:
          %r8_3_6(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0006000()
        case 7n+l:
          %r8_3_far(6, l, 0, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000600()
        case 1n:
          %r8_4_1(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000600()
        case 2n:
          %r8_4_2(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000600()
        case 3n:
          %r8_4_3(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000600()
        case 4n:
          %r8_4_4(6, 0) : ok8(_)
          %xr8_6_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000600()
        case 6n:
          %r8_4_6(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000600()
        case 7n+l:
          %r8_4_far(6, l, 0, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000060()
        case 1n:
          %r8_5_1(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000060()
        case 2n:
          %r8_5_2(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000060()
        case 3n:
          %r8_5_3(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000060()
        case 4n:
          %r8_5_4(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000060()
        case 5n:
          %r8_5_5(6, 0) : ok8(_)
          %xr8_6_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000060()
        case 7n+l:
          %r8_5_far(6, l, 0, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000006()
        case 1n:
          %r8_6_1(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000006()
        case 2n:
          %r8_6_2(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000006()
        case 3n:
          %r8_6_3(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000006()
        case 4n:
          %r8_6_4(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000006()
        case 5n:
          %r8_6_5(6, 0, ev8_6(), ev8_0()) : ok8(_)
          p8_0000006()
        case 6n:
          %r8_6_6(6, 0) : ok8(_)
          %xr8_6_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(6, l, 0, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 6, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 6, l, 0) : ok8(_)
          p8_0000000()

def q8_6_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 1) : ok8(_)
          %xr8_6_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_6100000()
        case 2n:
          %r8_0_2(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_6010000()
        case 3n:
          %r8_0_3(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_6001000()
        case 4n:
          %r8_0_4(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_6000100()
        case 5n:
          %r8_0_5(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_6000010()
        case 6n:
          %r8_0_6(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_6000001()
        case 7n+l:
          %r8_0_far(6, l, 1, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_1600000()
        case 1n:
          %r8_1_1(6, 1) : ok8(_)
          %xr8_6_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0610000()
        case 3n:
          %r8_1_3(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0601000()
        case 4n:
          %r8_1_4(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0600100()
        case 5n:
          %r8_1_5(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0600010()
        case 6n:
          %r8_1_6(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0600001()
        case 7n+l:
          %r8_1_far(6, l, 1, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_1060000()
        case 1n:
          %r8_2_1(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0160000()
        case 2n:
          %r8_2_2(6, 1) : ok8(_)
          %xr8_6_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0061000()
        case 4n:
          %r8_2_4(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0060100()
        case 5n:
          %r8_2_5(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0060010()
        case 6n:
          %r8_2_6(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0060001()
        case 7n+l:
          %r8_2_far(6, l, 1, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_1006000()
        case 1n:
          %r8_3_1(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0106000()
        case 2n:
          %r8_3_2(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0016000()
        case 3n:
          %r8_3_3(6, 1) : ok8(_)
          %xr8_6_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0006100()
        case 5n:
          %r8_3_5(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0006010()
        case 6n:
          %r8_3_6(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0006001()
        case 7n+l:
          %r8_3_far(6, l, 1, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_1000600()
        case 1n:
          %r8_4_1(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0100600()
        case 2n:
          %r8_4_2(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0010600()
        case 3n:
          %r8_4_3(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0001600()
        case 4n:
          %r8_4_4(6, 1) : ok8(_)
          %xr8_6_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0000610()
        case 6n:
          %r8_4_6(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0000601()
        case 7n+l:
          %r8_4_far(6, l, 1, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_1000060()
        case 1n:
          %r8_5_1(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0100060()
        case 2n:
          %r8_5_2(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0010060()
        case 3n:
          %r8_5_3(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0001060()
        case 4n:
          %r8_5_4(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0000160()
        case 5n:
          %r8_5_5(6, 1) : ok8(_)
          %xr8_6_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0000061()
        case 7n+l:
          %r8_5_far(6, l, 1, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_1000006()
        case 1n:
          %r8_6_1(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0100006()
        case 2n:
          %r8_6_2(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0010006()
        case 3n:
          %r8_6_3(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0001006()
        case 4n:
          %r8_6_4(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0000106()
        case 5n:
          %r8_6_5(6, 1, ev8_6(), ev8_1()) : ok8(_)
          p8_0000016()
        case 6n:
          %r8_6_6(6, 1) : ok8(_)
          %xr8_6_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(6, l, 1, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 6, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 6, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 6, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 6, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 6, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 6, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 6, l, 1) : ok8(_)
          p8_0000000()

def q8_6_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 2) : ok8(_)
          %xr8_6_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_6200000()
        case 2n:
          %r8_0_2(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_6020000()
        case 3n:
          %r8_0_3(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_6002000()
        case 4n:
          %r8_0_4(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_6000200()
        case 5n:
          %r8_0_5(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_6000020()
        case 6n:
          %r8_0_6(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_6000002()
        case 7n+l:
          %r8_0_far(6, l, 2, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_2600000()
        case 1n:
          %r8_1_1(6, 2) : ok8(_)
          %xr8_6_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0620000()
        case 3n:
          %r8_1_3(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0602000()
        case 4n:
          %r8_1_4(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0600200()
        case 5n:
          %r8_1_5(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0600020()
        case 6n:
          %r8_1_6(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0600002()
        case 7n+l:
          %r8_1_far(6, l, 2, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_2060000()
        case 1n:
          %r8_2_1(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0260000()
        case 2n:
          %r8_2_2(6, 2) : ok8(_)
          %xr8_6_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0062000()
        case 4n:
          %r8_2_4(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0060200()
        case 5n:
          %r8_2_5(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0060020()
        case 6n:
          %r8_2_6(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0060002()
        case 7n+l:
          %r8_2_far(6, l, 2, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_2006000()
        case 1n:
          %r8_3_1(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0206000()
        case 2n:
          %r8_3_2(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0026000()
        case 3n:
          %r8_3_3(6, 2) : ok8(_)
          %xr8_6_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0006200()
        case 5n:
          %r8_3_5(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0006020()
        case 6n:
          %r8_3_6(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0006002()
        case 7n+l:
          %r8_3_far(6, l, 2, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_2000600()
        case 1n:
          %r8_4_1(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0200600()
        case 2n:
          %r8_4_2(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0020600()
        case 3n:
          %r8_4_3(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0002600()
        case 4n:
          %r8_4_4(6, 2) : ok8(_)
          %xr8_6_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0000620()
        case 6n:
          %r8_4_6(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0000602()
        case 7n+l:
          %r8_4_far(6, l, 2, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_2000060()
        case 1n:
          %r8_5_1(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0200060()
        case 2n:
          %r8_5_2(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0020060()
        case 3n:
          %r8_5_3(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0002060()
        case 4n:
          %r8_5_4(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0000260()
        case 5n:
          %r8_5_5(6, 2) : ok8(_)
          %xr8_6_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0000062()
        case 7n+l:
          %r8_5_far(6, l, 2, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_2000006()
        case 1n:
          %r8_6_1(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0200006()
        case 2n:
          %r8_6_2(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0020006()
        case 3n:
          %r8_6_3(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0002006()
        case 4n:
          %r8_6_4(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0000206()
        case 5n:
          %r8_6_5(6, 2, ev8_6(), ev8_2()) : ok8(_)
          p8_0000026()
        case 6n:
          %r8_6_6(6, 2) : ok8(_)
          %xr8_6_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(6, l, 2, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 6, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 6, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 6, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 6, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 6, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 6, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 6, l, 2) : ok8(_)
          p8_0000000()

def q8_6_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 3) : ok8(_)
          %xr8_6_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_6300000()
        case 2n:
          %r8_0_2(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_6030000()
        case 3n:
          %r8_0_3(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_6003000()
        case 4n:
          %r8_0_4(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_6000300()
        case 5n:
          %r8_0_5(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_6000030()
        case 6n:
          %r8_0_6(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_6000003()
        case 7n+l:
          %r8_0_far(6, l, 3, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_3600000()
        case 1n:
          %r8_1_1(6, 3) : ok8(_)
          %xr8_6_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0630000()
        case 3n:
          %r8_1_3(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0603000()
        case 4n:
          %r8_1_4(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0600300()
        case 5n:
          %r8_1_5(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0600030()
        case 6n:
          %r8_1_6(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0600003()
        case 7n+l:
          %r8_1_far(6, l, 3, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_3060000()
        case 1n:
          %r8_2_1(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0360000()
        case 2n:
          %r8_2_2(6, 3) : ok8(_)
          %xr8_6_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0063000()
        case 4n:
          %r8_2_4(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0060300()
        case 5n:
          %r8_2_5(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0060030()
        case 6n:
          %r8_2_6(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0060003()
        case 7n+l:
          %r8_2_far(6, l, 3, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_3006000()
        case 1n:
          %r8_3_1(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0306000()
        case 2n:
          %r8_3_2(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0036000()
        case 3n:
          %r8_3_3(6, 3) : ok8(_)
          %xr8_6_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0006300()
        case 5n:
          %r8_3_5(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0006030()
        case 6n:
          %r8_3_6(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0006003()
        case 7n+l:
          %r8_3_far(6, l, 3, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_3000600()
        case 1n:
          %r8_4_1(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0300600()
        case 2n:
          %r8_4_2(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0030600()
        case 3n:
          %r8_4_3(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0003600()
        case 4n:
          %r8_4_4(6, 3) : ok8(_)
          %xr8_6_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0000630()
        case 6n:
          %r8_4_6(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0000603()
        case 7n+l:
          %r8_4_far(6, l, 3, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_3000060()
        case 1n:
          %r8_5_1(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0300060()
        case 2n:
          %r8_5_2(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0030060()
        case 3n:
          %r8_5_3(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0003060()
        case 4n:
          %r8_5_4(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0000360()
        case 5n:
          %r8_5_5(6, 3) : ok8(_)
          %xr8_6_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0000063()
        case 7n+l:
          %r8_5_far(6, l, 3, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_3000006()
        case 1n:
          %r8_6_1(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0300006()
        case 2n:
          %r8_6_2(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0030006()
        case 3n:
          %r8_6_3(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0003006()
        case 4n:
          %r8_6_4(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0000306()
        case 5n:
          %r8_6_5(6, 3, ev8_6(), ev8_3()) : ok8(_)
          p8_0000036()
        case 6n:
          %r8_6_6(6, 3) : ok8(_)
          %xr8_6_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(6, l, 3, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 6, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 6, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 6, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 6, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 6, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 6, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 6, l, 3) : ok8(_)
          p8_0000000()

def q8_6_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 4) : ok8(_)
          %xr8_6_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_6400000()
        case 2n:
          %r8_0_2(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_6040000()
        case 3n:
          %r8_0_3(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_6004000()
        case 4n:
          %r8_0_4(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_6000400()
        case 5n:
          %r8_0_5(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_6000040()
        case 6n:
          %r8_0_6(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_6000004()
        case 7n+l:
          %r8_0_far(6, l, 4, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_4600000()
        case 1n:
          %r8_1_1(6, 4) : ok8(_)
          %xr8_6_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0640000()
        case 3n:
          %r8_1_3(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0604000()
        case 4n:
          %r8_1_4(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0600400()
        case 5n:
          %r8_1_5(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0600040()
        case 6n:
          %r8_1_6(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0600004()
        case 7n+l:
          %r8_1_far(6, l, 4, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_4060000()
        case 1n:
          %r8_2_1(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0460000()
        case 2n:
          %r8_2_2(6, 4) : ok8(_)
          %xr8_6_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0064000()
        case 4n:
          %r8_2_4(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0060400()
        case 5n:
          %r8_2_5(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0060040()
        case 6n:
          %r8_2_6(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0060004()
        case 7n+l:
          %r8_2_far(6, l, 4, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_4006000()
        case 1n:
          %r8_3_1(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0406000()
        case 2n:
          %r8_3_2(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0046000()
        case 3n:
          %r8_3_3(6, 4) : ok8(_)
          %xr8_6_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0006400()
        case 5n:
          %r8_3_5(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0006040()
        case 6n:
          %r8_3_6(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0006004()
        case 7n+l:
          %r8_3_far(6, l, 4, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_4000600()
        case 1n:
          %r8_4_1(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0400600()
        case 2n:
          %r8_4_2(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0040600()
        case 3n:
          %r8_4_3(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0004600()
        case 4n:
          %r8_4_4(6, 4) : ok8(_)
          %xr8_6_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0000640()
        case 6n:
          %r8_4_6(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0000604()
        case 7n+l:
          %r8_4_far(6, l, 4, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_4000060()
        case 1n:
          %r8_5_1(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0400060()
        case 2n:
          %r8_5_2(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0040060()
        case 3n:
          %r8_5_3(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0004060()
        case 4n:
          %r8_5_4(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0000460()
        case 5n:
          %r8_5_5(6, 4) : ok8(_)
          %xr8_6_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0000064()
        case 7n+l:
          %r8_5_far(6, l, 4, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_4000006()
        case 1n:
          %r8_6_1(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0400006()
        case 2n:
          %r8_6_2(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0040006()
        case 3n:
          %r8_6_3(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0004006()
        case 4n:
          %r8_6_4(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0000406()
        case 5n:
          %r8_6_5(6, 4, ev8_6(), ev8_4()) : ok8(_)
          p8_0000046()
        case 6n:
          %r8_6_6(6, 4) : ok8(_)
          %xr8_6_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(6, l, 4, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 6, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 6, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 6, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 6, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 6, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 6, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 6, l, 4) : ok8(_)
          p8_0000000()

def q8_6_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 5) : ok8(_)
          %xr8_6_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_6500000()
        case 2n:
          %r8_0_2(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_6050000()
        case 3n:
          %r8_0_3(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_6005000()
        case 4n:
          %r8_0_4(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_6000500()
        case 5n:
          %r8_0_5(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_6000050()
        case 6n:
          %r8_0_6(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_6000005()
        case 7n+l:
          %r8_0_far(6, l, 5, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_5600000()
        case 1n:
          %r8_1_1(6, 5) : ok8(_)
          %xr8_6_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0650000()
        case 3n:
          %r8_1_3(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0605000()
        case 4n:
          %r8_1_4(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0600500()
        case 5n:
          %r8_1_5(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0600050()
        case 6n:
          %r8_1_6(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0600005()
        case 7n+l:
          %r8_1_far(6, l, 5, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_5060000()
        case 1n:
          %r8_2_1(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0560000()
        case 2n:
          %r8_2_2(6, 5) : ok8(_)
          %xr8_6_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0065000()
        case 4n:
          %r8_2_4(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0060500()
        case 5n:
          %r8_2_5(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0060050()
        case 6n:
          %r8_2_6(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0060005()
        case 7n+l:
          %r8_2_far(6, l, 5, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_5006000()
        case 1n:
          %r8_3_1(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0506000()
        case 2n:
          %r8_3_2(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0056000()
        case 3n:
          %r8_3_3(6, 5) : ok8(_)
          %xr8_6_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0006500()
        case 5n:
          %r8_3_5(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0006050()
        case 6n:
          %r8_3_6(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0006005()
        case 7n+l:
          %r8_3_far(6, l, 5, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_5000600()
        case 1n:
          %r8_4_1(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0500600()
        case 2n:
          %r8_4_2(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0050600()
        case 3n:
          %r8_4_3(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0005600()
        case 4n:
          %r8_4_4(6, 5) : ok8(_)
          %xr8_6_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0000650()
        case 6n:
          %r8_4_6(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0000605()
        case 7n+l:
          %r8_4_far(6, l, 5, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_5000060()
        case 1n:
          %r8_5_1(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0500060()
        case 2n:
          %r8_5_2(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0050060()
        case 3n:
          %r8_5_3(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0005060()
        case 4n:
          %r8_5_4(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0000560()
        case 5n:
          %r8_5_5(6, 5) : ok8(_)
          %xr8_6_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0000065()
        case 7n+l:
          %r8_5_far(6, l, 5, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_5000006()
        case 1n:
          %r8_6_1(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0500006()
        case 2n:
          %r8_6_2(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0050006()
        case 3n:
          %r8_6_3(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0005006()
        case 4n:
          %r8_6_4(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0000506()
        case 5n:
          %r8_6_5(6, 5, ev8_6(), ev8_5()) : ok8(_)
          p8_0000056()
        case 6n:
          %r8_6_6(6, 5) : ok8(_)
          %xr8_6_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(6, l, 5, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 6, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 6, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 6, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 6, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 6, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 6, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 6, l, 5) : ok8(_)
          p8_0000000()

def q8_6_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 6) : ok8(_)
          %xr8_6_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6600000()
        case 2n:
          %r8_0_2(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6060000()
        case 3n:
          %r8_0_3(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6006000()
        case 4n:
          %r8_0_4(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6000600()
        case 5n:
          %r8_0_5(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6000060()
        case 6n:
          %r8_0_6(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6000006()
        case 7n+l:
          %r8_0_far(6, l, 6, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6600000()
        case 1n:
          %r8_1_1(6, 6) : ok8(_)
          %xr8_6_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0660000()
        case 3n:
          %r8_1_3(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0606000()
        case 4n:
          %r8_1_4(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0600600()
        case 5n:
          %r8_1_5(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0600060()
        case 6n:
          %r8_1_6(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0600006()
        case 7n+l:
          %r8_1_far(6, l, 6, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6060000()
        case 1n:
          %r8_2_1(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0660000()
        case 2n:
          %r8_2_2(6, 6) : ok8(_)
          %xr8_6_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0066000()
        case 4n:
          %r8_2_4(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0060600()
        case 5n:
          %r8_2_5(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0060060()
        case 6n:
          %r8_2_6(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0060006()
        case 7n+l:
          %r8_2_far(6, l, 6, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6006000()
        case 1n:
          %r8_3_1(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0606000()
        case 2n:
          %r8_3_2(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0066000()
        case 3n:
          %r8_3_3(6, 6) : ok8(_)
          %xr8_6_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0006600()
        case 5n:
          %r8_3_5(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0006060()
        case 6n:
          %r8_3_6(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0006006()
        case 7n+l:
          %r8_3_far(6, l, 6, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6000600()
        case 1n:
          %r8_4_1(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0600600()
        case 2n:
          %r8_4_2(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0060600()
        case 3n:
          %r8_4_3(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0006600()
        case 4n:
          %r8_4_4(6, 6) : ok8(_)
          %xr8_6_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0000660()
        case 6n:
          %r8_4_6(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0000606()
        case 7n+l:
          %r8_4_far(6, l, 6, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6000060()
        case 1n:
          %r8_5_1(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0600060()
        case 2n:
          %r8_5_2(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0060060()
        case 3n:
          %r8_5_3(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0006060()
        case 4n:
          %r8_5_4(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0000660()
        case 5n:
          %r8_5_5(6, 6) : ok8(_)
          %xr8_6_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0000066()
        case 7n+l:
          %r8_5_far(6, l, 6, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_6000006()
        case 1n:
          %r8_6_1(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0600006()
        case 2n:
          %r8_6_2(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0060006()
        case 3n:
          %r8_6_3(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0006006()
        case 4n:
          %r8_6_4(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0000606()
        case 5n:
          %r8_6_5(6, 6, ev8_6(), ev8_6()) : ok8(_)
          p8_0000066()
        case 6n:
          %r8_6_6(6, 6) : ok8(_)
          %xr8_6_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(6, l, 6, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 6, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 6, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 6, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 6, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 6, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 6, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 6, l, 6) : ok8(_)
          p8_0000000()

def q8_6_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(6, 7) : ok8(_)
          %xr8_6_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_6700000()
        case 2n:
          %r8_0_2(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_6070000()
        case 3n:
          %r8_0_3(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_6007000()
        case 4n:
          %r8_0_4(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_6000700()
        case 5n:
          %r8_0_5(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_6000070()
        case 6n:
          %r8_0_6(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_6000007()
        case 7n+l:
          %r8_0_far(6, l, 7, ev8_6()) : ok8(_)
          p8_6000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_7600000()
        case 1n:
          %r8_1_1(6, 7) : ok8(_)
          %xr8_6_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0670000()
        case 3n:
          %r8_1_3(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0607000()
        case 4n:
          %r8_1_4(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0600700()
        case 5n:
          %r8_1_5(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0600070()
        case 6n:
          %r8_1_6(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0600007()
        case 7n+l:
          %r8_1_far(6, l, 7, ev8_6()) : ok8(_)
          p8_0600000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_7060000()
        case 1n:
          %r8_2_1(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0760000()
        case 2n:
          %r8_2_2(6, 7) : ok8(_)
          %xr8_6_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0067000()
        case 4n:
          %r8_2_4(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0060700()
        case 5n:
          %r8_2_5(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0060070()
        case 6n:
          %r8_2_6(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0060007()
        case 7n+l:
          %r8_2_far(6, l, 7, ev8_6()) : ok8(_)
          p8_0060000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_7006000()
        case 1n:
          %r8_3_1(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0706000()
        case 2n:
          %r8_3_2(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0076000()
        case 3n:
          %r8_3_3(6, 7) : ok8(_)
          %xr8_6_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0006700()
        case 5n:
          %r8_3_5(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0006070()
        case 6n:
          %r8_3_6(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0006007()
        case 7n+l:
          %r8_3_far(6, l, 7, ev8_6()) : ok8(_)
          p8_0006000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_7000600()
        case 1n:
          %r8_4_1(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0700600()
        case 2n:
          %r8_4_2(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0070600()
        case 3n:
          %r8_4_3(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0007600()
        case 4n:
          %r8_4_4(6, 7) : ok8(_)
          %xr8_6_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0000670()
        case 6n:
          %r8_4_6(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0000607()
        case 7n+l:
          %r8_4_far(6, l, 7, ev8_6()) : ok8(_)
          p8_0000600()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_7000060()
        case 1n:
          %r8_5_1(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0700060()
        case 2n:
          %r8_5_2(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0070060()
        case 3n:
          %r8_5_3(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0007060()
        case 4n:
          %r8_5_4(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0000760()
        case 5n:
          %r8_5_5(6, 7) : ok8(_)
          %xr8_6_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0000067()
        case 7n+l:
          %r8_5_far(6, l, 7, ev8_6()) : ok8(_)
          p8_0000060()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_7000006()
        case 1n:
          %r8_6_1(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0700006()
        case 2n:
          %r8_6_2(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0070006()
        case 3n:
          %r8_6_3(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0007006()
        case 4n:
          %r8_6_4(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0000706()
        case 5n:
          %r8_6_5(6, 7, ev8_6(), ev8_7()) : ok8(_)
          p8_0000076()
        case 6n:
          %r8_6_6(6, 7) : ok8(_)
          %xr8_6_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(6, l, 7, ev8_6()) : ok8(_)
          p8_0000006()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 6, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 6, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 6, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 6, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 6, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 6, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 6, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 6, l, 7) : ok8(_)
          p8_0000000()

def q8_7_0(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 0))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 0) : ok8(_)
          %xr8_7_0() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_7000000()
        case 1n:
          %r8_0_1(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_7000000()
        case 2n:
          %r8_0_2(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_7000000()
        case 3n:
          %r8_0_3(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_7000000()
        case 4n:
          %r8_0_4(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_7000000()
        case 5n:
          %r8_0_5(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_7000000()
        case 6n:
          %r8_0_6(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_7000000()
        case 7n+l:
          %r8_0_far(7, l, 0, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0700000()
        case 1n:
          %r8_1_1(7, 0) : ok8(_)
          %xr8_7_0() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0700000()
        case 2n:
          %r8_1_2(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0700000()
        case 3n:
          %r8_1_3(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0700000()
        case 4n:
          %r8_1_4(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0700000()
        case 5n:
          %r8_1_5(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0700000()
        case 6n:
          %r8_1_6(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0700000()
        case 7n+l:
          %r8_1_far(7, l, 0, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0070000()
        case 1n:
          %r8_2_1(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0070000()
        case 2n:
          %r8_2_2(7, 0) : ok8(_)
          %xr8_7_0() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0070000()
        case 3n:
          %r8_2_3(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0070000()
        case 4n:
          %r8_2_4(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0070000()
        case 5n:
          %r8_2_5(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0070000()
        case 6n:
          %r8_2_6(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0070000()
        case 7n+l:
          %r8_2_far(7, l, 0, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0007000()
        case 1n:
          %r8_3_1(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0007000()
        case 2n:
          %r8_3_2(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0007000()
        case 3n:
          %r8_3_3(7, 0) : ok8(_)
          %xr8_7_0() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0007000()
        case 4n:
          %r8_3_4(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0007000()
        case 5n:
          %r8_3_5(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0007000()
        case 6n:
          %r8_3_6(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0007000()
        case 7n+l:
          %r8_3_far(7, l, 0, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000700()
        case 1n:
          %r8_4_1(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000700()
        case 2n:
          %r8_4_2(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000700()
        case 3n:
          %r8_4_3(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000700()
        case 4n:
          %r8_4_4(7, 0) : ok8(_)
          %xr8_7_0() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000700()
        case 5n:
          %r8_4_5(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000700()
        case 6n:
          %r8_4_6(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000700()
        case 7n+l:
          %r8_4_far(7, l, 0, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000070()
        case 1n:
          %r8_5_1(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000070()
        case 2n:
          %r8_5_2(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000070()
        case 3n:
          %r8_5_3(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000070()
        case 4n:
          %r8_5_4(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000070()
        case 5n:
          %r8_5_5(7, 0) : ok8(_)
          %xr8_7_0() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000070()
        case 6n:
          %r8_5_6(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000070()
        case 7n+l:
          %r8_5_far(7, l, 0, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000007()
        case 1n:
          %r8_6_1(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000007()
        case 2n:
          %r8_6_2(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000007()
        case 3n:
          %r8_6_3(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000007()
        case 4n:
          %r8_6_4(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000007()
        case 5n:
          %r8_6_5(7, 0, ev8_7(), ev8_0()) : ok8(_)
          p8_0000007()
        case 6n:
          %r8_6_6(7, 0) : ok8(_)
          %xr8_7_0() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000007()
        case 7n+l:
          %r8_6_far(7, l, 0, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 1n:
          %r8_far_1(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 2n:
          %r8_far_2(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 3n:
          %r8_far_3(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 4n:
          %r8_far_4(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 5n:
          %r8_far_5(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 6n:
          %r8_far_6(k, 7, 0, ev8_0()) : ok8(_)
          p8_0000000()
        case 7n+l:
          %r8_far_far(k, 7, l, 0) : ok8(_)
          p8_0000000()

def q8_7_1(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 1))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 1) : ok8(_)
          %xr8_7_1() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_6000000()
        case 1n:
          %r8_0_1(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_7100000()
        case 2n:
          %r8_0_2(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_7010000()
        case 3n:
          %r8_0_3(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_7001000()
        case 4n:
          %r8_0_4(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_7000100()
        case 5n:
          %r8_0_5(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_7000010()
        case 6n:
          %r8_0_6(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_7000001()
        case 7n+l:
          %r8_0_far(7, l, 1, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_1700000()
        case 1n:
          %r8_1_1(7, 1) : ok8(_)
          %xr8_7_1() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0600000()
        case 2n:
          %r8_1_2(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0710000()
        case 3n:
          %r8_1_3(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0701000()
        case 4n:
          %r8_1_4(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0700100()
        case 5n:
          %r8_1_5(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0700010()
        case 6n:
          %r8_1_6(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0700001()
        case 7n+l:
          %r8_1_far(7, l, 1, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_1070000()
        case 1n:
          %r8_2_1(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0170000()
        case 2n:
          %r8_2_2(7, 1) : ok8(_)
          %xr8_7_1() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0060000()
        case 3n:
          %r8_2_3(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0071000()
        case 4n:
          %r8_2_4(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0070100()
        case 5n:
          %r8_2_5(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0070010()
        case 6n:
          %r8_2_6(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0070001()
        case 7n+l:
          %r8_2_far(7, l, 1, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_1007000()
        case 1n:
          %r8_3_1(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0107000()
        case 2n:
          %r8_3_2(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0017000()
        case 3n:
          %r8_3_3(7, 1) : ok8(_)
          %xr8_7_1() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0006000()
        case 4n:
          %r8_3_4(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0007100()
        case 5n:
          %r8_3_5(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0007010()
        case 6n:
          %r8_3_6(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0007001()
        case 7n+l:
          %r8_3_far(7, l, 1, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_1000700()
        case 1n:
          %r8_4_1(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0100700()
        case 2n:
          %r8_4_2(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0010700()
        case 3n:
          %r8_4_3(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0001700()
        case 4n:
          %r8_4_4(7, 1) : ok8(_)
          %xr8_7_1() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000600()
        case 5n:
          %r8_4_5(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0000710()
        case 6n:
          %r8_4_6(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0000701()
        case 7n+l:
          %r8_4_far(7, l, 1, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_1000070()
        case 1n:
          %r8_5_1(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0100070()
        case 2n:
          %r8_5_2(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0010070()
        case 3n:
          %r8_5_3(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0001070()
        case 4n:
          %r8_5_4(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0000170()
        case 5n:
          %r8_5_5(7, 1) : ok8(_)
          %xr8_7_1() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000060()
        case 6n:
          %r8_5_6(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0000071()
        case 7n+l:
          %r8_5_far(7, l, 1, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_1000007()
        case 1n:
          %r8_6_1(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0100007()
        case 2n:
          %r8_6_2(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0010007()
        case 3n:
          %r8_6_3(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0001007()
        case 4n:
          %r8_6_4(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0000107()
        case 5n:
          %r8_6_5(7, 1, ev8_7(), ev8_1()) : ok8(_)
          p8_0000017()
        case 6n:
          %r8_6_6(7, 1) : ok8(_)
          %xr8_7_1() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000006()
        case 7n+l:
          %r8_6_far(7, l, 1, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 1, ev8_1()) : ok8(_)
          p8_1000000()
        case 1n:
          %r8_far_1(k, 7, 1, ev8_1()) : ok8(_)
          p8_0100000()
        case 2n:
          %r8_far_2(k, 7, 1, ev8_1()) : ok8(_)
          p8_0010000()
        case 3n:
          %r8_far_3(k, 7, 1, ev8_1()) : ok8(_)
          p8_0001000()
        case 4n:
          %r8_far_4(k, 7, 1, ev8_1()) : ok8(_)
          p8_0000100()
        case 5n:
          %r8_far_5(k, 7, 1, ev8_1()) : ok8(_)
          p8_0000010()
        case 6n:
          %r8_far_6(k, 7, 1, ev8_1()) : ok8(_)
          p8_0000001()
        case 7n+l:
          %r8_far_far(k, 7, l, 1) : ok8(_)
          p8_0000000()

def q8_7_2(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 2))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 2) : ok8(_)
          %xr8_7_2() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_5000000()
        case 1n:
          %r8_0_1(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_7200000()
        case 2n:
          %r8_0_2(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_7020000()
        case 3n:
          %r8_0_3(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_7002000()
        case 4n:
          %r8_0_4(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_7000200()
        case 5n:
          %r8_0_5(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_7000020()
        case 6n:
          %r8_0_6(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_7000002()
        case 7n+l:
          %r8_0_far(7, l, 2, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_2700000()
        case 1n:
          %r8_1_1(7, 2) : ok8(_)
          %xr8_7_2() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0500000()
        case 2n:
          %r8_1_2(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0720000()
        case 3n:
          %r8_1_3(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0702000()
        case 4n:
          %r8_1_4(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0700200()
        case 5n:
          %r8_1_5(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0700020()
        case 6n:
          %r8_1_6(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0700002()
        case 7n+l:
          %r8_1_far(7, l, 2, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_2070000()
        case 1n:
          %r8_2_1(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0270000()
        case 2n:
          %r8_2_2(7, 2) : ok8(_)
          %xr8_7_2() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0050000()
        case 3n:
          %r8_2_3(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0072000()
        case 4n:
          %r8_2_4(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0070200()
        case 5n:
          %r8_2_5(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0070020()
        case 6n:
          %r8_2_6(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0070002()
        case 7n+l:
          %r8_2_far(7, l, 2, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_2007000()
        case 1n:
          %r8_3_1(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0207000()
        case 2n:
          %r8_3_2(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0027000()
        case 3n:
          %r8_3_3(7, 2) : ok8(_)
          %xr8_7_2() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0005000()
        case 4n:
          %r8_3_4(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0007200()
        case 5n:
          %r8_3_5(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0007020()
        case 6n:
          %r8_3_6(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0007002()
        case 7n+l:
          %r8_3_far(7, l, 2, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_2000700()
        case 1n:
          %r8_4_1(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0200700()
        case 2n:
          %r8_4_2(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0020700()
        case 3n:
          %r8_4_3(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0002700()
        case 4n:
          %r8_4_4(7, 2) : ok8(_)
          %xr8_7_2() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000500()
        case 5n:
          %r8_4_5(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0000720()
        case 6n:
          %r8_4_6(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0000702()
        case 7n+l:
          %r8_4_far(7, l, 2, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_2000070()
        case 1n:
          %r8_5_1(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0200070()
        case 2n:
          %r8_5_2(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0020070()
        case 3n:
          %r8_5_3(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0002070()
        case 4n:
          %r8_5_4(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0000270()
        case 5n:
          %r8_5_5(7, 2) : ok8(_)
          %xr8_7_2() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000050()
        case 6n:
          %r8_5_6(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0000072()
        case 7n+l:
          %r8_5_far(7, l, 2, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_2000007()
        case 1n:
          %r8_6_1(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0200007()
        case 2n:
          %r8_6_2(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0020007()
        case 3n:
          %r8_6_3(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0002007()
        case 4n:
          %r8_6_4(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0000207()
        case 5n:
          %r8_6_5(7, 2, ev8_7(), ev8_2()) : ok8(_)
          p8_0000027()
        case 6n:
          %r8_6_6(7, 2) : ok8(_)
          %xr8_7_2() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000005()
        case 7n+l:
          %r8_6_far(7, l, 2, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 2, ev8_2()) : ok8(_)
          p8_2000000()
        case 1n:
          %r8_far_1(k, 7, 2, ev8_2()) : ok8(_)
          p8_0200000()
        case 2n:
          %r8_far_2(k, 7, 2, ev8_2()) : ok8(_)
          p8_0020000()
        case 3n:
          %r8_far_3(k, 7, 2, ev8_2()) : ok8(_)
          p8_0002000()
        case 4n:
          %r8_far_4(k, 7, 2, ev8_2()) : ok8(_)
          p8_0000200()
        case 5n:
          %r8_far_5(k, 7, 2, ev8_2()) : ok8(_)
          p8_0000020()
        case 6n:
          %r8_far_6(k, 7, 2, ev8_2()) : ok8(_)
          p8_0000002()
        case 7n+l:
          %r8_far_far(k, 7, l, 2) : ok8(_)
          p8_0000000()

def q8_7_3(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 3))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 3) : ok8(_)
          %xr8_7_3() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_4000000()
        case 1n:
          %r8_0_1(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_7300000()
        case 2n:
          %r8_0_2(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_7030000()
        case 3n:
          %r8_0_3(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_7003000()
        case 4n:
          %r8_0_4(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_7000300()
        case 5n:
          %r8_0_5(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_7000030()
        case 6n:
          %r8_0_6(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_7000003()
        case 7n+l:
          %r8_0_far(7, l, 3, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_3700000()
        case 1n:
          %r8_1_1(7, 3) : ok8(_)
          %xr8_7_3() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0400000()
        case 2n:
          %r8_1_2(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0730000()
        case 3n:
          %r8_1_3(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0703000()
        case 4n:
          %r8_1_4(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0700300()
        case 5n:
          %r8_1_5(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0700030()
        case 6n:
          %r8_1_6(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0700003()
        case 7n+l:
          %r8_1_far(7, l, 3, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_3070000()
        case 1n:
          %r8_2_1(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0370000()
        case 2n:
          %r8_2_2(7, 3) : ok8(_)
          %xr8_7_3() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0040000()
        case 3n:
          %r8_2_3(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0073000()
        case 4n:
          %r8_2_4(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0070300()
        case 5n:
          %r8_2_5(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0070030()
        case 6n:
          %r8_2_6(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0070003()
        case 7n+l:
          %r8_2_far(7, l, 3, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_3007000()
        case 1n:
          %r8_3_1(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0307000()
        case 2n:
          %r8_3_2(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0037000()
        case 3n:
          %r8_3_3(7, 3) : ok8(_)
          %xr8_7_3() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0004000()
        case 4n:
          %r8_3_4(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0007300()
        case 5n:
          %r8_3_5(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0007030()
        case 6n:
          %r8_3_6(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0007003()
        case 7n+l:
          %r8_3_far(7, l, 3, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_3000700()
        case 1n:
          %r8_4_1(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0300700()
        case 2n:
          %r8_4_2(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0030700()
        case 3n:
          %r8_4_3(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0003700()
        case 4n:
          %r8_4_4(7, 3) : ok8(_)
          %xr8_7_3() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000400()
        case 5n:
          %r8_4_5(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0000730()
        case 6n:
          %r8_4_6(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0000703()
        case 7n+l:
          %r8_4_far(7, l, 3, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_3000070()
        case 1n:
          %r8_5_1(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0300070()
        case 2n:
          %r8_5_2(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0030070()
        case 3n:
          %r8_5_3(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0003070()
        case 4n:
          %r8_5_4(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0000370()
        case 5n:
          %r8_5_5(7, 3) : ok8(_)
          %xr8_7_3() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000040()
        case 6n:
          %r8_5_6(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0000073()
        case 7n+l:
          %r8_5_far(7, l, 3, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_3000007()
        case 1n:
          %r8_6_1(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0300007()
        case 2n:
          %r8_6_2(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0030007()
        case 3n:
          %r8_6_3(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0003007()
        case 4n:
          %r8_6_4(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0000307()
        case 5n:
          %r8_6_5(7, 3, ev8_7(), ev8_3()) : ok8(_)
          p8_0000037()
        case 6n:
          %r8_6_6(7, 3) : ok8(_)
          %xr8_7_3() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000004()
        case 7n+l:
          %r8_6_far(7, l, 3, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 3, ev8_3()) : ok8(_)
          p8_3000000()
        case 1n:
          %r8_far_1(k, 7, 3, ev8_3()) : ok8(_)
          p8_0300000()
        case 2n:
          %r8_far_2(k, 7, 3, ev8_3()) : ok8(_)
          p8_0030000()
        case 3n:
          %r8_far_3(k, 7, 3, ev8_3()) : ok8(_)
          p8_0003000()
        case 4n:
          %r8_far_4(k, 7, 3, ev8_3()) : ok8(_)
          p8_0000300()
        case 5n:
          %r8_far_5(k, 7, 3, ev8_3()) : ok8(_)
          p8_0000030()
        case 6n:
          %r8_far_6(k, 7, 3, ev8_3()) : ok8(_)
          p8_0000003()
        case 7n+l:
          %r8_far_far(k, 7, l, 3) : ok8(_)
          p8_0000000()

def q8_7_4(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 4))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 4) : ok8(_)
          %xr8_7_4() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_3000000()
        case 1n:
          %r8_0_1(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_7400000()
        case 2n:
          %r8_0_2(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_7040000()
        case 3n:
          %r8_0_3(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_7004000()
        case 4n:
          %r8_0_4(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_7000400()
        case 5n:
          %r8_0_5(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_7000040()
        case 6n:
          %r8_0_6(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_7000004()
        case 7n+l:
          %r8_0_far(7, l, 4, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_4700000()
        case 1n:
          %r8_1_1(7, 4) : ok8(_)
          %xr8_7_4() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0300000()
        case 2n:
          %r8_1_2(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0740000()
        case 3n:
          %r8_1_3(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0704000()
        case 4n:
          %r8_1_4(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0700400()
        case 5n:
          %r8_1_5(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0700040()
        case 6n:
          %r8_1_6(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0700004()
        case 7n+l:
          %r8_1_far(7, l, 4, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_4070000()
        case 1n:
          %r8_2_1(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0470000()
        case 2n:
          %r8_2_2(7, 4) : ok8(_)
          %xr8_7_4() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0030000()
        case 3n:
          %r8_2_3(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0074000()
        case 4n:
          %r8_2_4(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0070400()
        case 5n:
          %r8_2_5(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0070040()
        case 6n:
          %r8_2_6(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0070004()
        case 7n+l:
          %r8_2_far(7, l, 4, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_4007000()
        case 1n:
          %r8_3_1(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0407000()
        case 2n:
          %r8_3_2(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0047000()
        case 3n:
          %r8_3_3(7, 4) : ok8(_)
          %xr8_7_4() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0003000()
        case 4n:
          %r8_3_4(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0007400()
        case 5n:
          %r8_3_5(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0007040()
        case 6n:
          %r8_3_6(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0007004()
        case 7n+l:
          %r8_3_far(7, l, 4, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_4000700()
        case 1n:
          %r8_4_1(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0400700()
        case 2n:
          %r8_4_2(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0040700()
        case 3n:
          %r8_4_3(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0004700()
        case 4n:
          %r8_4_4(7, 4) : ok8(_)
          %xr8_7_4() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000300()
        case 5n:
          %r8_4_5(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0000740()
        case 6n:
          %r8_4_6(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0000704()
        case 7n+l:
          %r8_4_far(7, l, 4, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_4000070()
        case 1n:
          %r8_5_1(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0400070()
        case 2n:
          %r8_5_2(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0040070()
        case 3n:
          %r8_5_3(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0004070()
        case 4n:
          %r8_5_4(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0000470()
        case 5n:
          %r8_5_5(7, 4) : ok8(_)
          %xr8_7_4() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000030()
        case 6n:
          %r8_5_6(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0000074()
        case 7n+l:
          %r8_5_far(7, l, 4, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_4000007()
        case 1n:
          %r8_6_1(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0400007()
        case 2n:
          %r8_6_2(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0040007()
        case 3n:
          %r8_6_3(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0004007()
        case 4n:
          %r8_6_4(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0000407()
        case 5n:
          %r8_6_5(7, 4, ev8_7(), ev8_4()) : ok8(_)
          p8_0000047()
        case 6n:
          %r8_6_6(7, 4) : ok8(_)
          %xr8_7_4() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000003()
        case 7n+l:
          %r8_6_far(7, l, 4, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 4, ev8_4()) : ok8(_)
          p8_4000000()
        case 1n:
          %r8_far_1(k, 7, 4, ev8_4()) : ok8(_)
          p8_0400000()
        case 2n:
          %r8_far_2(k, 7, 4, ev8_4()) : ok8(_)
          p8_0040000()
        case 3n:
          %r8_far_3(k, 7, 4, ev8_4()) : ok8(_)
          p8_0004000()
        case 4n:
          %r8_far_4(k, 7, 4, ev8_4()) : ok8(_)
          p8_0000400()
        case 5n:
          %r8_far_5(k, 7, 4, ev8_4()) : ok8(_)
          p8_0000040()
        case 6n:
          %r8_far_6(k, 7, 4, ev8_4()) : ok8(_)
          p8_0000004()
        case 7n+l:
          %r8_far_far(k, 7, l, 4) : ok8(_)
          p8_0000000()

def q8_7_5(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 5))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 5) : ok8(_)
          %xr8_7_5() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_2000000()
        case 1n:
          %r8_0_1(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_7500000()
        case 2n:
          %r8_0_2(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_7050000()
        case 3n:
          %r8_0_3(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_7005000()
        case 4n:
          %r8_0_4(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_7000500()
        case 5n:
          %r8_0_5(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_7000050()
        case 6n:
          %r8_0_6(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_7000005()
        case 7n+l:
          %r8_0_far(7, l, 5, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_5700000()
        case 1n:
          %r8_1_1(7, 5) : ok8(_)
          %xr8_7_5() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0200000()
        case 2n:
          %r8_1_2(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0750000()
        case 3n:
          %r8_1_3(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0705000()
        case 4n:
          %r8_1_4(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0700500()
        case 5n:
          %r8_1_5(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0700050()
        case 6n:
          %r8_1_6(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0700005()
        case 7n+l:
          %r8_1_far(7, l, 5, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_5070000()
        case 1n:
          %r8_2_1(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0570000()
        case 2n:
          %r8_2_2(7, 5) : ok8(_)
          %xr8_7_5() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0020000()
        case 3n:
          %r8_2_3(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0075000()
        case 4n:
          %r8_2_4(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0070500()
        case 5n:
          %r8_2_5(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0070050()
        case 6n:
          %r8_2_6(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0070005()
        case 7n+l:
          %r8_2_far(7, l, 5, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_5007000()
        case 1n:
          %r8_3_1(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0507000()
        case 2n:
          %r8_3_2(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0057000()
        case 3n:
          %r8_3_3(7, 5) : ok8(_)
          %xr8_7_5() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0002000()
        case 4n:
          %r8_3_4(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0007500()
        case 5n:
          %r8_3_5(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0007050()
        case 6n:
          %r8_3_6(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0007005()
        case 7n+l:
          %r8_3_far(7, l, 5, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_5000700()
        case 1n:
          %r8_4_1(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0500700()
        case 2n:
          %r8_4_2(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0050700()
        case 3n:
          %r8_4_3(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0005700()
        case 4n:
          %r8_4_4(7, 5) : ok8(_)
          %xr8_7_5() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000200()
        case 5n:
          %r8_4_5(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0000750()
        case 6n:
          %r8_4_6(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0000705()
        case 7n+l:
          %r8_4_far(7, l, 5, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_5000070()
        case 1n:
          %r8_5_1(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0500070()
        case 2n:
          %r8_5_2(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0050070()
        case 3n:
          %r8_5_3(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0005070()
        case 4n:
          %r8_5_4(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0000570()
        case 5n:
          %r8_5_5(7, 5) : ok8(_)
          %xr8_7_5() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000020()
        case 6n:
          %r8_5_6(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0000075()
        case 7n+l:
          %r8_5_far(7, l, 5, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_5000007()
        case 1n:
          %r8_6_1(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0500007()
        case 2n:
          %r8_6_2(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0050007()
        case 3n:
          %r8_6_3(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0005007()
        case 4n:
          %r8_6_4(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0000507()
        case 5n:
          %r8_6_5(7, 5, ev8_7(), ev8_5()) : ok8(_)
          p8_0000057()
        case 6n:
          %r8_6_6(7, 5) : ok8(_)
          %xr8_7_5() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000002()
        case 7n+l:
          %r8_6_far(7, l, 5, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 5, ev8_5()) : ok8(_)
          p8_5000000()
        case 1n:
          %r8_far_1(k, 7, 5, ev8_5()) : ok8(_)
          p8_0500000()
        case 2n:
          %r8_far_2(k, 7, 5, ev8_5()) : ok8(_)
          p8_0050000()
        case 3n:
          %r8_far_3(k, 7, 5, ev8_5()) : ok8(_)
          p8_0005000()
        case 4n:
          %r8_far_4(k, 7, 5, ev8_5()) : ok8(_)
          p8_0000500()
        case 5n:
          %r8_far_5(k, 7, 5, ev8_5()) : ok8(_)
          p8_0000050()
        case 6n:
          %r8_far_6(k, 7, 5, ev8_5()) : ok8(_)
          p8_0000005()
        case 7n+l:
          %r8_far_far(k, 7, l, 5) : ok8(_)
          p8_0000000()

def q8_7_6(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 6))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 6) : ok8(_)
          %xr8_7_6() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_1000000()
        case 1n:
          %r8_0_1(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_7600000()
        case 2n:
          %r8_0_2(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_7060000()
        case 3n:
          %r8_0_3(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_7006000()
        case 4n:
          %r8_0_4(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_7000600()
        case 5n:
          %r8_0_5(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_7000060()
        case 6n:
          %r8_0_6(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_7000006()
        case 7n+l:
          %r8_0_far(7, l, 6, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_6700000()
        case 1n:
          %r8_1_1(7, 6) : ok8(_)
          %xr8_7_6() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0100000()
        case 2n:
          %r8_1_2(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0760000()
        case 3n:
          %r8_1_3(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0706000()
        case 4n:
          %r8_1_4(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0700600()
        case 5n:
          %r8_1_5(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0700060()
        case 6n:
          %r8_1_6(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0700006()
        case 7n+l:
          %r8_1_far(7, l, 6, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_6070000()
        case 1n:
          %r8_2_1(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0670000()
        case 2n:
          %r8_2_2(7, 6) : ok8(_)
          %xr8_7_6() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0010000()
        case 3n:
          %r8_2_3(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0076000()
        case 4n:
          %r8_2_4(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0070600()
        case 5n:
          %r8_2_5(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0070060()
        case 6n:
          %r8_2_6(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0070006()
        case 7n+l:
          %r8_2_far(7, l, 6, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_6007000()
        case 1n:
          %r8_3_1(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0607000()
        case 2n:
          %r8_3_2(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0067000()
        case 3n:
          %r8_3_3(7, 6) : ok8(_)
          %xr8_7_6() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0001000()
        case 4n:
          %r8_3_4(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0007600()
        case 5n:
          %r8_3_5(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0007060()
        case 6n:
          %r8_3_6(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0007006()
        case 7n+l:
          %r8_3_far(7, l, 6, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_6000700()
        case 1n:
          %r8_4_1(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0600700()
        case 2n:
          %r8_4_2(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0060700()
        case 3n:
          %r8_4_3(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0006700()
        case 4n:
          %r8_4_4(7, 6) : ok8(_)
          %xr8_7_6() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000100()
        case 5n:
          %r8_4_5(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0000760()
        case 6n:
          %r8_4_6(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0000706()
        case 7n+l:
          %r8_4_far(7, l, 6, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_6000070()
        case 1n:
          %r8_5_1(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0600070()
        case 2n:
          %r8_5_2(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0060070()
        case 3n:
          %r8_5_3(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0006070()
        case 4n:
          %r8_5_4(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0000670()
        case 5n:
          %r8_5_5(7, 6) : ok8(_)
          %xr8_7_6() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000010()
        case 6n:
          %r8_5_6(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0000076()
        case 7n+l:
          %r8_5_far(7, l, 6, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_6000007()
        case 1n:
          %r8_6_1(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0600007()
        case 2n:
          %r8_6_2(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0060007()
        case 3n:
          %r8_6_3(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0006007()
        case 4n:
          %r8_6_4(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0000607()
        case 5n:
          %r8_6_5(7, 6, ev8_7(), ev8_6()) : ok8(_)
          p8_0000067()
        case 6n:
          %r8_6_6(7, 6) : ok8(_)
          %xr8_7_6() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000001()
        case 7n+l:
          %r8_6_far(7, l, 6, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 6, ev8_6()) : ok8(_)
          p8_6000000()
        case 1n:
          %r8_far_1(k, 7, 6, ev8_6()) : ok8(_)
          p8_0600000()
        case 2n:
          %r8_far_2(k, 7, 6, ev8_6()) : ok8(_)
          p8_0060000()
        case 3n:
          %r8_far_3(k, 7, 6, ev8_6()) : ok8(_)
          p8_0006000()
        case 4n:
          %r8_far_4(k, 7, 6, ev8_6()) : ok8(_)
          p8_0000600()
        case 5n:
          %r8_far_5(k, 7, 6, ev8_6()) : ok8(_)
          p8_0000060()
        case 6n:
          %r8_far_6(k, 7, 6, ev8_6()) : ok8(_)
          p8_0000006()
        case 7n+l:
          %r8_far_far(k, 7, l, 6) : ok8(_)
          p8_0000000()

def q8_7_7(i: Nat, j: Nat) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, 7))):
  match i:
    case 0n:
      match j:
        case 0n:
          %r8_0_0(7, 7) : ok8(_)
          %xr8_7_7() : ok8([_, 0, 0, 0, 0, 0, 0])
          p8_0000000()
        case 1n:
          %r8_0_1(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7700000()
        case 2n:
          %r8_0_2(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7070000()
        case 3n:
          %r8_0_3(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7007000()
        case 4n:
          %r8_0_4(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7000700()
        case 5n:
          %r8_0_5(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7000070()
        case 6n:
          %r8_0_6(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7000007()
        case 7n+l:
          %r8_0_far(7, l, 7, ev8_7()) : ok8(_)
          p8_7000000()
    case 1n:
      match j:
        case 0n:
          %r8_1_0(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7700000()
        case 1n:
          %r8_1_1(7, 7) : ok8(_)
          %xr8_7_7() : ok8([0, _, 0, 0, 0, 0, 0])
          p8_0000000()
        case 2n:
          %r8_1_2(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0770000()
        case 3n:
          %r8_1_3(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0707000()
        case 4n:
          %r8_1_4(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0700700()
        case 5n:
          %r8_1_5(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0700070()
        case 6n:
          %r8_1_6(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0700007()
        case 7n+l:
          %r8_1_far(7, l, 7, ev8_7()) : ok8(_)
          p8_0700000()
    case 2n:
      match j:
        case 0n:
          %r8_2_0(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7070000()
        case 1n:
          %r8_2_1(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0770000()
        case 2n:
          %r8_2_2(7, 7) : ok8(_)
          %xr8_7_7() : ok8([0, 0, _, 0, 0, 0, 0])
          p8_0000000()
        case 3n:
          %r8_2_3(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0077000()
        case 4n:
          %r8_2_4(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0070700()
        case 5n:
          %r8_2_5(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0070070()
        case 6n:
          %r8_2_6(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0070007()
        case 7n+l:
          %r8_2_far(7, l, 7, ev8_7()) : ok8(_)
          p8_0070000()
    case 3n:
      match j:
        case 0n:
          %r8_3_0(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7007000()
        case 1n:
          %r8_3_1(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0707000()
        case 2n:
          %r8_3_2(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0077000()
        case 3n:
          %r8_3_3(7, 7) : ok8(_)
          %xr8_7_7() : ok8([0, 0, 0, _, 0, 0, 0])
          p8_0000000()
        case 4n:
          %r8_3_4(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0007700()
        case 5n:
          %r8_3_5(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0007070()
        case 6n:
          %r8_3_6(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0007007()
        case 7n+l:
          %r8_3_far(7, l, 7, ev8_7()) : ok8(_)
          p8_0007000()
    case 4n:
      match j:
        case 0n:
          %r8_4_0(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7000700()
        case 1n:
          %r8_4_1(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0700700()
        case 2n:
          %r8_4_2(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0070700()
        case 3n:
          %r8_4_3(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0007700()
        case 4n:
          %r8_4_4(7, 7) : ok8(_)
          %xr8_7_7() : ok8([0, 0, 0, 0, _, 0, 0])
          p8_0000000()
        case 5n:
          %r8_4_5(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0000770()
        case 6n:
          %r8_4_6(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0000707()
        case 7n+l:
          %r8_4_far(7, l, 7, ev8_7()) : ok8(_)
          p8_0000700()
    case 5n:
      match j:
        case 0n:
          %r8_5_0(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7000070()
        case 1n:
          %r8_5_1(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0700070()
        case 2n:
          %r8_5_2(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0070070()
        case 3n:
          %r8_5_3(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0007070()
        case 4n:
          %r8_5_4(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0000770()
        case 5n:
          %r8_5_5(7, 7) : ok8(_)
          %xr8_7_7() : ok8([0, 0, 0, 0, 0, _, 0])
          p8_0000000()
        case 6n:
          %r8_5_6(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0000077()
        case 7n+l:
          %r8_5_far(7, l, 7, ev8_7()) : ok8(_)
          p8_0000070()
    case 6n:
      match j:
        case 0n:
          %r8_6_0(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_7000007()
        case 1n:
          %r8_6_1(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0700007()
        case 2n:
          %r8_6_2(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0070007()
        case 3n:
          %r8_6_3(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0007007()
        case 4n:
          %r8_6_4(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0000707()
        case 5n:
          %r8_6_5(7, 7, ev8_7(), ev8_7()) : ok8(_)
          p8_0000077()
        case 6n:
          %r8_6_6(7, 7) : ok8(_)
          %xr8_7_7() : ok8([0, 0, 0, 0, 0, 0, _])
          p8_0000000()
        case 7n+l:
          %r8_6_far(7, l, 7, ev8_7()) : ok8(_)
          p8_0000007()
    case 7n+k:
      match j:
        case 0n:
          %r8_far_0(k, 7, 7, ev8_7()) : ok8(_)
          p8_7000000()
        case 1n:
          %r8_far_1(k, 7, 7, ev8_7()) : ok8(_)
          p8_0700000()
        case 2n:
          %r8_far_2(k, 7, 7, ev8_7()) : ok8(_)
          p8_0070000()
        case 3n:
          %r8_far_3(k, 7, 7, ev8_7()) : ok8(_)
          p8_0007000()
        case 4n:
          %r8_far_4(k, 7, 7, ev8_7()) : ok8(_)
          p8_0000700()
        case 5n:
          %r8_far_5(k, 7, 7, ev8_7()) : ok8(_)
          p8_0000070()
        case 6n:
          %r8_far_6(k, 7, 7, ev8_7()) : ok8(_)
          p8_0000007()
        case 7n+l:
          %r8_far_far(k, 7, l, 7) : ok8(_)
          p8_0000000()

# The second value's low bits

def q8_0(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 0, j, _)))
      q8_0_7(i, j)

def q8_1(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 1, j, _)))
      q8_1_7(i, j)

def q8_2(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 2, j, _)))
      q8_2_7(i, j)

def q8_3(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 3, j, _)))
      q8_3_7(i, j)

def q8_4(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 4, j, _)))
      q8_4_7(i, j)

def q8_5(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 5, j, _)))
      q8_5_7(i, j)

def q8_6(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 6, j, _)))
      q8_6_7(i, j)

def q8_7(+i: Nat, +j: Nat, v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match v:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_0(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_1(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_2(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_3(i, j)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_4(i, j)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_5(i, j)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_6(i, j)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, 7, j, _)))
      q8_7_7(i, j)

# Every pattern of at most two errors, given as two changes
def q8(+i: Nat, u: U32, +j: Nat, +v: U32) -> ok8(E.Rs.mask(C.Rs.small8(), pat8(i, M.Gfm.elt(C.Rs.gf8(), u), j, M.Gfm.elt(C.Rs.gf8(), v)))):
  match u:
    case U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_0(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_0(i, j, v)
    case U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_1(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_1(i, j, v)
    case U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_2(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_2(i, j, v)
    case U32{WCon{True{}, WCon{True{}, WCon{False{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_3(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_3(i, j, v)
    case U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_4(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_4(i, j, v)
    case U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_5(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_5(i, j, v)
    case U32{WCon{False{}, WCon{True{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_6(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_6(i, j, v)
    case U32{WCon{True{}, WCon{True{}, WCon{True{}, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %l8_7(a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31) : ok8(E.Rs.mask(C.Rs.small8(), pat8(i, _, j, M.Gfm.elt(C.Rs.gf8(), v))))
      q8_7(i, j, v)
