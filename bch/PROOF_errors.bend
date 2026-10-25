# Proofs of LAWS_errors.bend: the (15,7) code corrects every pattern of at
# most two flipped bits.
#
#   * The syndromes are linear in the bits: Horner's rule over the bits,
#     with (x + y) k = x k + y k for each of the syndromes' points k
#     (proof_pat15.bend's dist_k, tried on every pair of elements); a
#     codeword's syndromes are zero (LAWS.bend's small15_syndromes), so a
#     codeword plus e (bit by bit) has e's syndromes, and the decoder's
#     error positions (Bch.locate) are e's. Flipping bits of a sum flips
#     the second word's, so the corrected word is the codeword plus e
#     corrected, whose syndromes are e corrected's: the decoder treats
#     w + e as it treats e (small15_decode_shift).
#   * A codeword with two bits flipped is the codeword plus the pattern of
#     the two flips (proof_pat15.bend's pat15). Each of the 121 patterns of
#     at most two flipped bits, corrected alone, gives the zero word
#     (proof_pat15.bend's q15, a computation in a def of its own for each
#     pattern; gen/proof.py writes the file), so it decodes to the zero
#     message (bche.ga), and the reduction does the rest
#     (small15_two_errors).
import Base
import ../gf/gfm.bend as M
import ../rs/poly.bend as P
import ../rs/arith.bend as A
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as S
import ./bch.bend as D
import ./LAWS.bend as BL
import ./PROOF.bend as BP
import ./proof_pat15.bend as Pt
import ./LAWS_errors.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Contradictions, lengths, and Done's argument

def bche.rdisc(r: Result<&2, &2, E.BchError, List<&2, Bool>>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def bche.fd(-er: E.BchError, -z: List<&2, Bool>, +h: {Fail{er} == Done{z} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> Empty:
  %h : bche.rdisc(_)
  Unit{}

def bche.val(r: Result<&2, &2, E.BchError, List<&2, Bool>>) -> List<&2, Bool>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{x}:
      x

def bche.dinj(-a: List<&2, Bool>, -b: List<&2, Bool>, h: {Done{a} == Done{b} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> {a == b : List<&2, Bool>}:
  Equal.cong(Result<&2, &2, E.BchError, List<&2, Bool>>, List<&2, Bool>, r => bche.val(r), Done{a}, Done{b}, h)

def bche.ndisc(+n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def bche.succ_zero(-n: Nat, +e: {1n+n == 0n : Nat}) -> Empty:
  %e : bche.ndisc(_)
  Unit{}

def bche.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def bche.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => bche.pred(n), 1n+a, 1n+b, e)

# Bits

def bche.bxf(+b: Bool) -> {Bool.xor(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bche.bxt(+b: Bool) -> {Bool.xor(b, True{}) == Bool.not(b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bche.bxn(+a: Bool, +b: Bool) -> {Bool.not(Bool.xor(a, b)) == Bool.xor(a, Bool.not(b)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bche.bx_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# a bit as an element: (p + q) = p + q
def bche.bxor(+p: Bool, +q: Bool) -> {S.bch.b(Bool.xor(p, q)) == M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q)) : U32}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Words

def bche.wx_assoc(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{ah, at} WCon{bh, bt} WCon{ch, ct}:
          %bche.bx_assoc(ah, bh, ch) : {WCon{Bool.xor(Bool.xor(ah, bh), ch), Word.xor(p, Word.xor(p, at, bt), ct)} == WCon{_, Word.xor(p, at, Word.xor(p, bt, ct))} : Word(1n+p)}
          %bche.wx_assoc(p, at, bt, ct) : {WCon{Bool.xor(Bool.xor(ah, bh), ch), Word.xor(p, Word.xor(p, at, bt), ct)} == WCon{Bool.xor(Bool.xor(ah, bh), ch), _} : Word(1n+p)}
          {==}

def bche.ux_assoc(a: U32, b: U32, c: U32) -> {U32.xor(U32.xor(a, b), c) == U32.xor(a, U32.xor(b, c)) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      %bche.wx_assoc(32n, x, y, z) : {U32{Word.xor(32n, Word.xor(32n, x, y), z)} == U32{_} : U32}
      {==}

# GF(16) addition: a commutative, associative operation

def bche.add_comm(+a: U32, +b: U32) -> {M.Gfm.add(M.Gfm.gf16(), a, b) == M.Gfm.add(M.Gfm.gf16(), b, a) : U32}:
  %UL.u32_xor_comm(b, a) : {M.Gfm.elt(M.Gfm.gf16(), _) == M.Gfm.elt(M.Gfm.gf16(), U32.xor(b, a)) : U32}
  {==}

def bche.add_assoc(+a: U32, +b: U32, +c: U32) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, b), c) == M.Gfm.add(M.Gfm.gf16(), a, M.Gfm.add(M.Gfm.gf16(), b, c)) : U32}:
  %Equal.sym(U32, M.Gfm.elt(M.Gfm.gf16(), U32.xor(M.Gfm.elt(M.Gfm.gf16(), U32.xor(a, b)), c)), M.Gfm.elt(M.Gfm.gf16(), U32.xor(U32.xor(a, b), c)), Pt.e1(U32.xor(a, b), c)) : {_ == M.Gfm.elt(M.Gfm.gf16(), U32.xor(a, M.Gfm.elt(M.Gfm.gf16(), U32.xor(b, c)))) : U32}
  %Equal.sym(U32, M.Gfm.elt(M.Gfm.gf16(), U32.xor(a, M.Gfm.elt(M.Gfm.gf16(), U32.xor(b, c)))), M.Gfm.elt(M.Gfm.gf16(), U32.xor(a, U32.xor(b, c))), Pt.e2(a, U32.xor(b, c))) : {M.Gfm.elt(M.Gfm.gf16(), U32.xor(U32.xor(a, b), c)) == _ : U32}
  %bche.ux_assoc(a, b, c) : {M.Gfm.elt(M.Gfm.gf16(), U32.xor(U32.xor(a, b), c)) == M.Gfm.elt(M.Gfm.gf16(), _) : U32}
  {==}

def bche.add_sw(+a: U32, +b: U32, +c: U32) -> {M.Gfm.add(M.Gfm.gf16(), a, M.Gfm.add(M.Gfm.gf16(), b, c)) == M.Gfm.add(M.Gfm.gf16(), b, M.Gfm.add(M.Gfm.gf16(), a, c)) : U32}:
  %bche.add_assoc(a, b, c) : {_ == M.Gfm.add(M.Gfm.gf16(), b, M.Gfm.add(M.Gfm.gf16(), a, c)) : U32}
  %bche.add_comm(b, a) : {M.Gfm.add(M.Gfm.gf16(), _, c) == M.Gfm.add(M.Gfm.gf16(), b, M.Gfm.add(M.Gfm.gf16(), a, c)) : U32}
  bche.add_assoc(b, a, c)

# (a + b) + (c + d) = (a + c) + (b + d)
def bche.add_sh(+a: U32, +b: U32, +c: U32, +d: U32) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, b), M.Gfm.add(M.Gfm.gf16(), c, d)) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, c), M.Gfm.add(M.Gfm.gf16(), b, d)) : U32}:
  %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, b), M.Gfm.add(M.Gfm.gf16(), c, d)), M.Gfm.add(M.Gfm.gf16(), a, M.Gfm.add(M.Gfm.gf16(), b, M.Gfm.add(M.Gfm.gf16(), c, d))), bche.add_assoc(a, b, M.Gfm.add(M.Gfm.gf16(), c, d))) : {_ == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, c), M.Gfm.add(M.Gfm.gf16(), b, d)) : U32}
  %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), b, M.Gfm.add(M.Gfm.gf16(), c, d)), M.Gfm.add(M.Gfm.gf16(), c, M.Gfm.add(M.Gfm.gf16(), b, d)), bche.add_sw(b, c, d)) : {M.Gfm.add(M.Gfm.gf16(), a, _) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, c), M.Gfm.add(M.Gfm.gf16(), b, d)) : U32}
  Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a, c), M.Gfm.add(M.Gfm.gf16(), b, d)), M.Gfm.add(M.Gfm.gf16(), a, M.Gfm.add(M.Gfm.gf16(), c, M.Gfm.add(M.Gfm.gf16(), b, d))), bche.add_assoc(a, c, M.Gfm.add(M.Gfm.gf16(), b, d)))

# Syndromes: Horner's rule over the bits is linear

# the Horner step at 2: (a1 + a2) 2 + (p + q) = (a1 2 + p) + (a2 2 + q)
def bche.hacc_2(+a1: U32, +a2: U32, +p: Bool, +q: Bool) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 2), S.bch.b(Bool.xor(p, q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(q))) : U32}:
  %Equal.sym(U32, S.bch.b(Bool.xor(p, q)), M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q)), bche.bxor(p, q)) : {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 2), _) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(q))) : U32}
  %Equal.sym(U32, M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 2), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), M.Gfm.mul(M.Gfm.gf16(), a2, 2)), Pt.dist2(a1, a2)) : {M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(q))) : U32}
  bche.add_sh(M.Gfm.mul(M.Gfm.gf16(), a1, 2), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(p), S.bch.b(q))

def bche.hlin_2(w1: List<&2, Bool>, w2: List<&2, Bool>, +a1: U32, +a2: U32, +same: {List.length(&2, Bool, w1) == List.length(&2, Bool, w2) : Nat}) -> {S.bch.syn.one(Pt.xl(w1, w2), M.Gfm.gf16(), 2, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(w1, M.Gfm.gf16(), 2, a1), S.bch.syn.one(w2, M.Gfm.gf16(), 2, a2)) : U32}:
  match w1 w2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Nil{}, Con{y, t}), M.Gfm.gf16(), 2, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 2, a1), S.bch.syn.one(Con{y, t}, M.Gfm.gf16(), 2, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Con{x, s}, Nil{}), M.Gfm.gf16(), 2, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Con{x, s}, M.Gfm.gf16(), 2, a1), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 2, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 2), S.bch.b(Bool.xor(x, y))), M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(y))), bche.hacc_2(a1, a2, x, y)) : {S.bch.syn.one(Pt.xl(s, t), M.Gfm.gf16(), 2, _) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(s, M.Gfm.gf16(), 2, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), S.bch.b(x))), S.bch.syn.one(t, M.Gfm.gf16(), 2, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(y)))) : U32}
      bche.hlin_2(s, t, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 2), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 2), S.bch.b(y)), bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same))

# the Horner step at 4: (a1 + a2) 4 + (p + q) = (a1 4 + p) + (a2 4 + q)
def bche.hacc_4(+a1: U32, +a2: U32, +p: Bool, +q: Bool) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 4), S.bch.b(Bool.xor(p, q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(q))) : U32}:
  %Equal.sym(U32, S.bch.b(Bool.xor(p, q)), M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q)), bche.bxor(p, q)) : {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 4), _) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(q))) : U32}
  %Equal.sym(U32, M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 4), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), M.Gfm.mul(M.Gfm.gf16(), a2, 4)), Pt.dist4(a1, a2)) : {M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(q))) : U32}
  bche.add_sh(M.Gfm.mul(M.Gfm.gf16(), a1, 4), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(p), S.bch.b(q))

def bche.hlin_4(w1: List<&2, Bool>, w2: List<&2, Bool>, +a1: U32, +a2: U32, +same: {List.length(&2, Bool, w1) == List.length(&2, Bool, w2) : Nat}) -> {S.bch.syn.one(Pt.xl(w1, w2), M.Gfm.gf16(), 4, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(w1, M.Gfm.gf16(), 4, a1), S.bch.syn.one(w2, M.Gfm.gf16(), 4, a2)) : U32}:
  match w1 w2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Nil{}, Con{y, t}), M.Gfm.gf16(), 4, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 4, a1), S.bch.syn.one(Con{y, t}, M.Gfm.gf16(), 4, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Con{x, s}, Nil{}), M.Gfm.gf16(), 4, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Con{x, s}, M.Gfm.gf16(), 4, a1), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 4, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 4), S.bch.b(Bool.xor(x, y))), M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(y))), bche.hacc_4(a1, a2, x, y)) : {S.bch.syn.one(Pt.xl(s, t), M.Gfm.gf16(), 4, _) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(s, M.Gfm.gf16(), 4, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), S.bch.b(x))), S.bch.syn.one(t, M.Gfm.gf16(), 4, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(y)))) : U32}
      bche.hlin_4(s, t, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 4), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 4), S.bch.b(y)), bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same))

# the Horner step at 8: (a1 + a2) 8 + (p + q) = (a1 8 + p) + (a2 8 + q)
def bche.hacc_8(+a1: U32, +a2: U32, +p: Bool, +q: Bool) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 8), S.bch.b(Bool.xor(p, q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(q))) : U32}:
  %Equal.sym(U32, S.bch.b(Bool.xor(p, q)), M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q)), bche.bxor(p, q)) : {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 8), _) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(q))) : U32}
  %Equal.sym(U32, M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 8), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), M.Gfm.mul(M.Gfm.gf16(), a2, 8)), Pt.dist8(a1, a2)) : {M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(q))) : U32}
  bche.add_sh(M.Gfm.mul(M.Gfm.gf16(), a1, 8), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(p), S.bch.b(q))

def bche.hlin_8(w1: List<&2, Bool>, w2: List<&2, Bool>, +a1: U32, +a2: U32, +same: {List.length(&2, Bool, w1) == List.length(&2, Bool, w2) : Nat}) -> {S.bch.syn.one(Pt.xl(w1, w2), M.Gfm.gf16(), 8, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(w1, M.Gfm.gf16(), 8, a1), S.bch.syn.one(w2, M.Gfm.gf16(), 8, a2)) : U32}:
  match w1 w2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Nil{}, Con{y, t}), M.Gfm.gf16(), 8, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 8, a1), S.bch.syn.one(Con{y, t}, M.Gfm.gf16(), 8, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Con{x, s}, Nil{}), M.Gfm.gf16(), 8, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Con{x, s}, M.Gfm.gf16(), 8, a1), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 8, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 8), S.bch.b(Bool.xor(x, y))), M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(y))), bche.hacc_8(a1, a2, x, y)) : {S.bch.syn.one(Pt.xl(s, t), M.Gfm.gf16(), 8, _) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(s, M.Gfm.gf16(), 8, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), S.bch.b(x))), S.bch.syn.one(t, M.Gfm.gf16(), 8, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(y)))) : U32}
      bche.hlin_8(s, t, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 8), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 8), S.bch.b(y)), bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same))

# the Horner step at 3: (a1 + a2) 3 + (p + q) = (a1 3 + p) + (a2 3 + q)
def bche.hacc_3(+a1: U32, +a2: U32, +p: Bool, +q: Bool) -> {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 3), S.bch.b(Bool.xor(p, q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(q))) : U32}:
  %Equal.sym(U32, S.bch.b(Bool.xor(p, q)), M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q)), bche.bxor(p, q)) : {M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 3), _) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(q))) : U32}
  %Equal.sym(U32, M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 3), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), M.Gfm.mul(M.Gfm.gf16(), a2, 3)), Pt.dist3(a1, a2)) : {M.Gfm.add(M.Gfm.gf16(), _, M.Gfm.add(M.Gfm.gf16(), S.bch.b(p), S.bch.b(q))) == M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), S.bch.b(p)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(q))) : U32}
  bche.add_sh(M.Gfm.mul(M.Gfm.gf16(), a1, 3), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(p), S.bch.b(q))

def bche.hlin_3(w1: List<&2, Bool>, w2: List<&2, Bool>, +a1: U32, +a2: U32, +same: {List.length(&2, Bool, w1) == List.length(&2, Bool, w2) : Nat}) -> {S.bch.syn.one(Pt.xl(w1, w2), M.Gfm.gf16(), 3, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(w1, M.Gfm.gf16(), 3, a1), S.bch.syn.one(w2, M.Gfm.gf16(), 3, a2)) : U32}:
  match w1 w2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Nil{}, Con{y, t}), M.Gfm.gf16(), 3, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 3, a1), S.bch.syn.one(Con{y, t}, M.Gfm.gf16(), 3, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({S.bch.syn.one(Pt.xl(Con{x, s}, Nil{}), M.Gfm.gf16(), 3, M.Gfm.add(M.Gfm.gf16(), a1, a2)) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(Con{x, s}, M.Gfm.gf16(), 3, a1), S.bch.syn.one(Nil{}, M.Gfm.gf16(), 3, a2)) : U32}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{+x, +s} Con{+y, +t}:
      %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), a1, a2), 3), S.bch.b(Bool.xor(x, y))), M.Gfm.add(M.Gfm.gf16(), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(y))), bche.hacc_3(a1, a2, x, y)) : {S.bch.syn.one(Pt.xl(s, t), M.Gfm.gf16(), 3, _) == M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(s, M.Gfm.gf16(), 3, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), S.bch.b(x))), S.bch.syn.one(t, M.Gfm.gf16(), 3, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(y)))) : U32}
      bche.hlin_3(s, t, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a1, 3), S.bch.b(x)), M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), a2, 3), S.bch.b(y)), bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same))

# The code's facts, computed apart: the kernel computes closed terms far
# faster than terms with unknowns

def bche.k4() -> {4n == U32.to_nat(U32.add(C.Bch.t(C.Bch.bch15_7()), C.Bch.t(C.Bch.bch15_7()))) : Nat}:
  {==}

def bche.f16() -> {M.Gfm.gf16() == C.Bch.field(C.Bch.bch15_7()) : M.GfmField}:
  {==}

def bche.x2() -> {2 == A.RsGf.pow_nat(C.Bch.field(C.Bch.bch15_7()), 2, U32.to_nat(C.Bch.m0(C.Bch.bch15_7()))) : U32}:
  {==}

def bche.m4() -> {4 == M.Gfm.mul(M.Gfm.gf16(), 2, 2) : U32}:
  {==}

def bche.m8() -> {8 == M.Gfm.mul(M.Gfm.gf16(), 4, 2) : U32}:
  {==}

def bche.m3() -> {3 == M.Gfm.mul(M.Gfm.gf16(), 8, 2) : U32}:
  {==}

def bche.pb8() -> {8n == C.Bch.parity_bits(C.Bch.bch15_7()) : Nat}:
  {==}

def bche.lok() -> {D.Bch.length_ok(C.Bch.bch15_7(), 15n) == True{} : Bool}:
  {==}

def bche.fn15() -> {15 == U32.from_nat(15n) : U32}:
  {==}

def bche.syn_unf(+x: List<&2, Bool>) -> {S.bch.syn.all(U32.to_nat(U32.add(C.Bch.t(C.Bch.bch15_7()), C.Bch.t(C.Bch.bch15_7()))), C.Bch.field(C.Bch.bch15_7()), x, A.RsGf.pow_nat(C.Bch.field(C.Bch.bch15_7()), 2, U32.to_nat(C.Bch.m0(C.Bch.bch15_7())))) == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}:
  {==}

# the syndromes are Horner's rule at 2, 4, 8 and 3
def bche.syn16(+x: List<&2, Bool>) -> {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}:
  %bche.syn_unf(x) : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == _ : List<&2, U32>}
  %bche.k4() : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == S.bch.syn.all(_, C.Bch.field(C.Bch.bch15_7()), x, A.RsGf.pow_nat(C.Bch.field(C.Bch.bch15_7()), 2, U32.to_nat(C.Bch.m0(C.Bch.bch15_7())))) : List<&2, U32>}
  %bche.x2() : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == S.bch.syn.all(4n, C.Bch.field(C.Bch.bch15_7()), x, _) : List<&2, U32>}
  %bche.f16() : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == S.bch.syn.all(4n, _, x, 2) : List<&2, U32>}
  %bche.m4() : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == Con{S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.all(3n, M.Gfm.gf16(), x, _)} : List<&2, U32>}
  %bche.m8() : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == Con{S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), Con{S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.all(2n, M.Gfm.gf16(), x, _)}} : List<&2, U32>}
  %bche.m3() : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] == Con{S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), Con{S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), Con{S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.all(1n, M.Gfm.gf16(), x, _)}}} : List<&2, U32>}
  {==}

def bche.synlin(+a: List<&2, Bool>, +b: List<&2, Bool>, +same: {List.length(&2, Bool, a) == List.length(&2, Bool, b) : Nat}) -> {S.Bch.syndromes(C.Bch.bch15_7(), Pt.xl(a, b)) == P.RsPoly.add(M.Gfm.gf16(), S.Bch.syndromes(C.Bch.bch15_7(), a), S.Bch.syndromes(C.Bch.bch15_7(), b)) : List<&2, U32>}:
  %bche.syn16(Pt.xl(a, b)) : {_ == P.RsPoly.add(M.Gfm.gf16(), S.Bch.syndromes(C.Bch.bch15_7(), a), S.Bch.syndromes(C.Bch.bch15_7(), b)) : List<&2, U32>}
  %bche.syn16(a) : {[S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 2, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 4, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 8, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 3, 0)] == P.RsPoly.add(M.Gfm.gf16(), _, S.Bch.syndromes(C.Bch.bch15_7(), b)) : List<&2, U32>}
  %bche.syn16(b) : {[S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 2, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 4, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 8, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 3, 0)] == P.RsPoly.add(M.Gfm.gf16(), [S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(a, M.Gfm.gf16(), 3, 0)], _) : List<&2, U32>}
  %Equal.sym(U32, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 2, M.Gfm.add(M.Gfm.gf16(), 0, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 2, 0)), bche.hlin_2(a, b, 0, 0, same)) : {[_, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 4, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 8, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 3, 0)] == P.RsPoly.add(M.Gfm.gf16(), [S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(a, M.Gfm.gf16(), 3, 0)], [S.bch.syn.one(b, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 8, 0), S.bch.syn.one(b, M.Gfm.gf16(), 3, 0)]) : List<&2, U32>}
  %Equal.sym(U32, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 4, M.Gfm.add(M.Gfm.gf16(), 0, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0)), bche.hlin_4(a, b, 0, 0, same)) : {[M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 2, 0)), _, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 8, 0), S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 3, 0)] == P.RsPoly.add(M.Gfm.gf16(), [S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(a, M.Gfm.gf16(), 3, 0)], [S.bch.syn.one(b, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 8, 0), S.bch.syn.one(b, M.Gfm.gf16(), 3, 0)]) : List<&2, U32>}
  %Equal.sym(U32, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 8, M.Gfm.add(M.Gfm.gf16(), 0, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(b, M.Gfm.gf16(), 8, 0)), bche.hlin_8(a, b, 0, 0, same)) : {[M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 2, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0)), _, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 3, 0)] == P.RsPoly.add(M.Gfm.gf16(), [S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(a, M.Gfm.gf16(), 3, 0)], [S.bch.syn.one(b, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 8, 0), S.bch.syn.one(b, M.Gfm.gf16(), 3, 0)]) : List<&2, U32>}
  %Equal.sym(U32, S.bch.syn.one(Pt.xl(a, b), M.Gfm.gf16(), 3, M.Gfm.add(M.Gfm.gf16(), 0, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 3, 0), S.bch.syn.one(b, M.Gfm.gf16(), 3, 0)), bche.hlin_3(a, b, 0, 0, same)) : {[M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 2, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0)), M.Gfm.add(M.Gfm.gf16(), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(b, M.Gfm.gf16(), 8, 0)), _] == P.RsPoly.add(M.Gfm.gf16(), [S.bch.syn.one(a, M.Gfm.gf16(), 2, 0), S.bch.syn.one(a, M.Gfm.gf16(), 4, 0), S.bch.syn.one(a, M.Gfm.gf16(), 8, 0), S.bch.syn.one(a, M.Gfm.gf16(), 3, 0)], [S.bch.syn.one(b, M.Gfm.gf16(), 2, 0), S.bch.syn.one(b, M.Gfm.gf16(), 4, 0), S.bch.syn.one(b, M.Gfm.gf16(), 8, 0), S.bch.syn.one(b, M.Gfm.gf16(), 3, 0)]) : List<&2, U32>}
  {==}

def bche.e0() -> {M.Gfm.elt(M.Gfm.gf16(), 0) == 0 : U32}:
  {==}

# Horner's rule gives an element
def bche.eso(w: List<&2, Bool>, +k: U32, +acc: U32, +h: {M.Gfm.elt(M.Gfm.gf16(), acc) == acc : U32}) -> {M.Gfm.elt(M.Gfm.gf16(), S.bch.syn.one(w, M.Gfm.gf16(), k, acc)) == S.bch.syn.one(w, M.Gfm.gf16(), k, acc) : U32}:
  match w:
    case Nil{}:
      h
    case Con{+s, +t}:
      bche.eso(t, k, M.Gfm.add(M.Gfm.gf16(), M.Gfm.mul(M.Gfm.gf16(), acc, k), S.bch.b(s)), Pt.eid(U32.xor(M.Gfm.mul(M.Gfm.gf16(), acc, k), S.bch.b(s))))

def bche.a0s(+x: List<&2, Bool>, +k: U32) -> {M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), k, 0)) == S.bch.syn.one(x, M.Gfm.gf16(), k, 0) : U32}:
  Equal.trans(U32, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), k, 0)), M.Gfm.elt(M.Gfm.gf16(), S.bch.syn.one(x, M.Gfm.gf16(), k, 0)), S.bch.syn.one(x, M.Gfm.gf16(), k, 0), Pt.a0(S.bch.syn.one(x, M.Gfm.gf16(), k, 0)), bche.eso(x, k, 0, bche.e0()))

def bche.z4(+x: List<&2, Bool>) -> {P.RsPoly.add(M.Gfm.gf16(), [0, 0, 0, 0], S.Bch.syndromes(C.Bch.bch15_7(), x)) == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}:
  %bche.syn16(x) : {P.RsPoly.add(M.Gfm.gf16(), [0, 0, 0, 0], _) == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}
  %bche.syn16(x) : {P.RsPoly.add(M.Gfm.gf16(), [0, 0, 0, 0], [S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)]) == _ : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 2, 0)), S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), bche.a0s(x, 2)) : {[_, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 4, 0)), M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 8, 0)), M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 3, 0))] == [S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 4, 0)), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), bche.a0s(x, 4)) : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), _, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 8, 0)), M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 3, 0))] == [S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 8, 0)), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), bche.a0s(x, 8)) : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), _, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 3, 0))] == [S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] : List<&2, U32>}
  %Equal.sym(U32, M.Gfm.add(M.Gfm.gf16(), 0, S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0), bche.a0s(x, 3)) : {[S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), _] == [S.bch.syn.one(x, M.Gfm.gf16(), 2, 0), S.bch.syn.one(x, M.Gfm.gf16(), 4, 0), S.bch.syn.one(x, M.Gfm.gf16(), 8, 0), S.bch.syn.one(x, M.Gfm.gf16(), 3, 0)] : List<&2, U32>}
  {==}

# a word with zero syndromes plus x has x's syndromes
def bche.ss(+w: List<&2, Bool>, +x: List<&2, Bool>, +hw: {S.Bch.syndromes(C.Bch.bch15_7(), w) == [0, 0, 0, 0] : List<&2, U32>}, +same: {List.length(&2, Bool, w) == List.length(&2, Bool, x) : Nat}) -> {S.Bch.syndromes(C.Bch.bch15_7(), Pt.xl(w, x)) == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, S.Bch.syndromes(C.Bch.bch15_7(), Pt.xl(w, x)), P.RsPoly.add(M.Gfm.gf16(), S.Bch.syndromes(C.Bch.bch15_7(), w), S.Bch.syndromes(C.Bch.bch15_7(), x)), bche.synlin(w, x, same)) : {_ == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, S.Bch.syndromes(C.Bch.bch15_7(), w), [0, 0, 0, 0], hw) : {P.RsPoly.add(M.Gfm.gf16(), _, S.Bch.syndromes(C.Bch.bch15_7(), x)) == S.Bch.syndromes(C.Bch.bch15_7(), x) : List<&2, U32>}
  bche.z4(x)

# Sums of bit lists

def bche.xl_len(a: List<&2, Bool>, b: List<&2, Bool>, +same: {List.length(&2, Bool, a) == List.length(&2, Bool, b) : Nat}) -> {List.length(&2, Bool, Pt.xl(a, b)) == List.length(&2, Bool, a) : Nat}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({List.length(&2, Bool, Pt.xl(Nil{}, Con{y, t})) == List.length(&2, Bool, Nil{}) : Nat}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({List.length(&2, Bool, Pt.xl(Con{x, s}, Nil{})) == List.length(&2, Bool, Con{x, s}) : Nat}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{x, +s} Con{y, +t}:
      %bche.xl_len(s, t, bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same)) : {1n+List.length(&2, Bool, Pt.xl(s, t)) == 1n+_ : Nat}
      {==}

# x plus zeros is x
def bche.xz(t: List<&2, Bool>) -> {Pt.xl(t, E.bch.falses(List.length(&2, Bool, t))) == t : List<&2, Bool>}:
  match t:
    case Nil{}:
      {==}
    case Con{+s, +r}:
      %bche.bxf(s) : {Con{Bool.xor(s, False{}), Pt.xl(r, E.bch.falses(List.length(&2, Bool, r)))} == Con{_, r} : List<&2, Bool>}
      %bche.xz(r) : {Con{Bool.xor(s, False{}), Pt.xl(r, E.bch.falses(List.length(&2, Bool, r)))} == Con{Bool.xor(s, False{}), _} : List<&2, Bool>}
      {==}

def bche.xassoc(a: List<&2, Bool>, b: List<&2, Bool>, d: List<&2, Bool>) -> {Pt.xl(Pt.xl(a, b), d) == Pt.xl(a, Pt.xl(b, d)) : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +s}:
      match b:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          match d:
            case Nil{}:
              {==}
            case Con{+z, +r}:
              %bche.bx_assoc(x, y, z) : {Con{Bool.xor(Bool.xor(x, y), z), Pt.xl(Pt.xl(s, t), r)} == Con{_, Pt.xl(s, Pt.xl(t, r))} : List<&2, Bool>}
              %bche.xassoc(s, t, r) : {Con{Bool.xor(Bool.xor(x, y), z), Pt.xl(Pt.xl(s, t), r)} == Con{Bool.xor(Bool.xor(x, y), z), _} : List<&2, Bool>}
              {==}

def bche.ta(x: List<&2, Bool>, y: List<&2, Bool>, n: Nat, +same: {List.length(&2, Bool, x) == List.length(&2, Bool, y) : Nat}) -> {List.take(&2, Bool, Pt.xl(x, y), n) == Pt.xl(List.take(&2, Bool, x, n), List.take(&2, Bool, y, n)) : List<&2, Bool>}:
  match x y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      Empty.absurd({List.take(&2, Bool, Pt.xl(Nil{}, Con{b, t}), n) == Pt.xl(List.take(&2, Bool, Nil{}, n), List.take(&2, Bool, Con{b, t}, n)) : List<&2, Bool>}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{a, s} Nil{}:
      Empty.absurd({List.take(&2, Bool, Pt.xl(Con{a, s}, Nil{}), n) == Pt.xl(List.take(&2, Bool, Con{a, s}, n), List.take(&2, Bool, Nil{}, n)) : List<&2, Bool>}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{+a, +s} Con{+b, +t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          %bche.ta(s, t, k, bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same)) : {Con{Bool.xor(a, b), List.take(&2, Bool, Pt.xl(s, t), k)} == Con{Bool.xor(a, b), _} : List<&2, Bool>}
          {==}

# Flipped bits as a sum

def bche.fone_len(w: List<&2, Bool>, i: Nat) -> {List.length(&2, Bool, D.bch.flip.one(w, i)) == List.length(&2, Bool, w) : Nat}:
  match w:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match i:
        case 0n:
          {==}
        case 1n+k:
          %bche.fone_len(t, k) : {1n+List.length(&2, Bool, D.bch.flip.one(t, k)) == 1n+_ : Nat}
          {==}

# a word with the bit at index i flipped is the word plus that flip
def bche.fo1(w: List<&2, Bool>, i: Nat) -> {D.bch.flip.one(w, i) == Pt.xl(w, D.bch.flip.one(E.bch.falses(List.length(&2, Bool, w)), i)) : List<&2, Bool>}:
  match w:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      match i:
        case 0n:
          %bche.bxt(s) : {Con{_, t} == Con{Bool.xor(s, True{}), Pt.xl(t, E.bch.falses(List.length(&2, Bool, t)))} : List<&2, Bool>}
          %bche.xz(t) : {Con{Bool.xor(s, True{}), _} == Con{Bool.xor(s, True{}), Pt.xl(t, E.bch.falses(List.length(&2, Bool, t)))} : List<&2, Bool>}
          {==}
        case 1n+k:
          %bche.bxf(s) : {Con{_, D.bch.flip.one(t, k)} == Con{Bool.xor(s, False{}), Pt.xl(t, D.bch.flip.one(E.bch.falses(List.length(&2, Bool, t)), k))} : List<&2, Bool>}
          %bche.fo1(t, k) : {Con{Bool.xor(s, False{}), D.bch.flip.one(t, k)} == Con{Bool.xor(s, False{}), _} : List<&2, Bool>}
          {==}

def bche.plen(+i: Nat, +j: Nat) -> {List.length(&2, Bool, Pt.pat15(i, j)) == 15n : Nat}:
  Equal.trans(Nat, List.length(&2, Bool, Pt.pat15(i, j)), List.length(&2, Bool, D.bch.flip.one(E.bch.falses(15n), i)), 15n, bche.xl_len(D.bch.flip.one(E.bch.falses(15n), i), D.bch.flip.one(E.bch.falses(15n), j), Equal.trans(Nat, List.length(&2, Bool, D.bch.flip.one(E.bch.falses(15n), i)), 15n, List.length(&2, Bool, D.bch.flip.one(E.bch.falses(15n), j)), bche.fone_len(E.bch.falses(15n), i), Equal.sym(Nat, List.length(&2, Bool, D.bch.flip.one(E.bch.falses(15n), j)), 15n, bche.fone_len(E.bch.falses(15n), j)))), bche.fone_len(E.bch.falses(15n), i))

# a word of 15 bits with two flipped: the word plus the pattern of the flips
def bche.dm(+w: List<&2, Bool>, +i: Nat, +j: Nat, +h15: {List.length(&2, Bool, w) == 15n : Nat}) -> {D.bch.flip.one(D.bch.flip.one(w, i), j) == Pt.xl(w, Pt.pat15(i, j)) : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, D.bch.flip.one(D.bch.flip.one(w, i), j), Pt.xl(D.bch.flip.one(w, i), D.bch.flip.one(E.bch.falses(List.length(&2, Bool, D.bch.flip.one(w, i))), j)), bche.fo1(D.bch.flip.one(w, i), j)) : {_ == Pt.xl(w, Pt.pat15(i, j)) : List<&2, Bool>}
  %Equal.sym(Nat, List.length(&2, Bool, D.bch.flip.one(w, i)), 15n, Equal.trans(Nat, List.length(&2, Bool, D.bch.flip.one(w, i)), List.length(&2, Bool, w), 15n, bche.fone_len(w, i), h15)) : {Pt.xl(D.bch.flip.one(w, i), D.bch.flip.one(E.bch.falses(_), j)) == Pt.xl(w, Pt.pat15(i, j)) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, D.bch.flip.one(w, i), Pt.xl(w, D.bch.flip.one(E.bch.falses(List.length(&2, Bool, w)), i)), bche.fo1(w, i)) : {Pt.xl(_, D.bch.flip.one(E.bch.falses(15n), j)) == Pt.xl(w, Pt.pat15(i, j)) : List<&2, Bool>}
  %Equal.sym(Nat, List.length(&2, Bool, w), 15n, h15) : {Pt.xl(Pt.xl(w, D.bch.flip.one(E.bch.falses(_), i)), D.bch.flip.one(E.bch.falses(15n), j)) == Pt.xl(w, Pt.pat15(i, j)) : List<&2, Bool>}
  bche.xassoc(w, D.bch.flip.one(E.bch.falses(15n), i), D.bch.flip.one(E.bch.falses(15n), j))

# Flipping bits of a sum flips the second word's

def bche.flo(w: List<&2, Bool>, e: List<&2, Bool>, i: Nat, +same: {List.length(&2, Bool, w) == List.length(&2, Bool, e) : Nat}) -> {D.bch.flip.one(Pt.xl(w, e), i) == Pt.xl(w, D.bch.flip.one(e, i)) : List<&2, Bool>}:
  match w e:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({D.bch.flip.one(Pt.xl(Nil{}, Con{y, t}), i) == Pt.xl(Nil{}, D.bch.flip.one(Con{y, t}, i)) : List<&2, Bool>}, bche.succ_zero(List.length(&2, Bool, t), Equal.sym(Nat, 0n, 1n+List.length(&2, Bool, t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({D.bch.flip.one(Pt.xl(Con{x, s}, Nil{}), i) == Pt.xl(Con{x, s}, D.bch.flip.one(Nil{}, i)) : List<&2, Bool>}, bche.succ_zero(List.length(&2, Bool, s), same))
    case Con{+x, +s} Con{+y, +t}:
      match i:
        case 0n:
          %bche.bxn(x, y) : {Con{Bool.not(Bool.xor(x, y)), Pt.xl(s, t)} == Con{_, Pt.xl(s, t)} : List<&2, Bool>}
          {==}
        case 1n+k:
          %bche.flo(s, t, k, bche.succ_inj(List.length(&2, Bool, s), List.length(&2, Bool, t), same)) : {Con{Bool.xor(x, y), D.bch.flip.one(Pt.xl(s, t), k)} == Con{Bool.xor(x, y), _} : List<&2, Bool>}
          {==}

def bche.fla_len(ps: List<&2, U32>, +n: Nat, +w: List<&2, Bool>) -> {List.length(&2, Bool, D.bch.flip.all(ps, n, w)) == List.length(&2, Bool, w) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, t}:
      Equal.trans(Nat, List.length(&2, Bool, D.bch.flip.all(t, n, D.bch.flip.one(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p))))), List.length(&2, Bool, D.bch.flip.one(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)))), List.length(&2, Bool, w), bche.fla_len(t, n, D.bch.flip.one(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)))), bche.fone_len(w, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p))))

def bche.fla(ps: List<&2, U32>, +n: Nat, +w: List<&2, Bool>, +e: List<&2, Bool>, +same: {List.length(&2, Bool, w) == List.length(&2, Bool, e) : Nat}) -> {D.bch.flip.all(ps, n, Pt.xl(w, e)) == Pt.xl(w, D.bch.flip.all(ps, n, e)) : List<&2, Bool>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, t}:
      %Equal.sym(List<&2, Bool>, D.bch.flip.one(Pt.xl(w, e), Nat.sub(Nat.sub(n, 1n), U32.to_nat(p))), Pt.xl(w, D.bch.flip.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)))), bche.flo(w, e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)), same)) : {D.bch.flip.all(t, n, _) == Pt.xl(w, D.bch.flip.all(t, n, D.bch.flip.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p))))) : List<&2, Bool>}
      bche.fla(t, n, w, D.bch.flip.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p))), Equal.trans(Nat, List.length(&2, Bool, w), List.length(&2, Bool, e), List.length(&2, Bool, D.bch.flip.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)))), same, Equal.sym(Nat, List.length(&2, Bool, D.bch.flip.one(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p)))), List.length(&2, Bool, e), bche.fone_len(e, Nat.sub(Nat.sub(n, 1n), U32.to_nat(p))))))

def bche.flp(+ps: List<&2, U32>, +w: List<&2, Bool>, +e: List<&2, Bool>, +same: {List.length(&2, Bool, w) == List.length(&2, Bool, e) : Nat}) -> {D.Bch.flip(ps, Pt.xl(w, e)) == Pt.xl(w, D.Bch.flip(ps, e)) : List<&2, Bool>}:
  %Equal.sym(Nat, List.length(&2, Bool, Pt.xl(w, e)), List.length(&2, Bool, e), Equal.trans(Nat, List.length(&2, Bool, Pt.xl(w, e)), List.length(&2, Bool, w), List.length(&2, Bool, e), bche.xl_len(w, e, same), same)) : {D.bch.flip.all(ps, _, Pt.xl(w, e)) == Pt.xl(w, D.bch.flip.all(ps, List.length(&2, Bool, e), e)) : List<&2, Bool>}
  bche.fla(ps, List.length(&2, Bool, e), w, e, same)

def bche.flp_len(+ps: List<&2, U32>, +x: List<&2, Bool>) -> {List.length(&2, Bool, D.Bch.flip(ps, x)) == List.length(&2, Bool, x) : Nat}:
  bche.fla_len(ps, List.length(&2, Bool, x), x)

# Decoding a word of 15 bits, its steps written out

# for any code whose words of 15 bits have the right length (the code a
# parameter, so that the kernel computes nothing about it here)
def bche.unfg(+cc: C.BchCode, +w: List<&2, Bool>, +hl: {List.length(&2, Bool, w) == 15n : Nat}, +hlok: {D.Bch.length_ok(cc, 15n) == True{} : Bool}) -> {D.Bch.decode_bits(cc, w) == D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), 15), D.Bch.opts(), cc, w)) : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  %Equal.sym(Nat, List.length(&2, Bool, w), 15n, hl) : {D.bch.dec.msg(cc, D.bch.cor.go(D.Bch.length_ok(cc, _), D.Bch.opts(), cc, w)) == D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), 15), D.Bch.opts(), cc, w)) : Result<&2, &2, E.BchError, List<&2, Bool>>}
  %Equal.sym(Bool, D.Bch.length_ok(cc, 15n), True{}, hlok) : {D.bch.dec.msg(cc, D.bch.cor.go(_, D.Bch.opts(), cc, w)) == D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), 15), D.Bch.opts(), cc, w)) : Result<&2, &2, E.BchError, List<&2, Bool>>}
  %Equal.sym(Nat, List.length(&2, Bool, w), 15n, hl) : {D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), U32.from_nat(_)), D.Bch.opts(), cc, w)) == D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), 15), D.Bch.opts(), cc, w)) : Result<&2, &2, E.BchError, List<&2, Bool>>}
  %bche.fn15() : {D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), _), D.Bch.opts(), cc, w)) == D.bch.dec.msg(cc, D.bch.cor.fin(D.Bch.locate(cc, S.Bch.syndromes(cc, w), 15), D.Bch.opts(), cc, w)) : Result<&2, &2, E.BchError, List<&2, Bool>>}
  {==}

# decoding a word of 15 bits, its steps written out
def bche.unf(+w: List<&2, Bool>, +hl: {List.length(&2, Bool, w) == 15n : Nat}) -> {D.Bch.decode_bits(C.Bch.bch15_7(), w) == D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), w), 15), D.Bch.opts(), C.Bch.bch15_7(), w)) : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  bche.unfg(C.Bch.bch15_7(), w, hl, bche.lok())

# the zero word passes the final check (closed: the kernel computes closed
# terms far faster than terms with unknowns)
def bche.zck() -> {D.bch.cor.check(True{}, C.Bch.bch15_7(), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == True{} : Bool}:
  {==}

# a pattern that the decoder's flips turn into the zero word (chk15)
# decodes to the zero message
def bche.gar(r: Result<&2, &2, E.BchError, List<&2, U32>>, +x: List<&2, Bool>, +h: {Pt.chk15r(r, x) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(r, D.Bch.opts(), C.Bch.bch15_7(), x)) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  match r:
    case Fail{er}:
      Empty.absurd({D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(Fail{er}, D.Bch.opts(), C.Bch.bch15_7(), x)) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}, bche.fd(er, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], h))
    case Done{+ps}:
      %Equal.sym(List<&2, Bool>, D.Bch.flip(ps, x), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], bche.dinj(D.Bch.flip(ps, x), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], h)) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(D.bch.cor.check(True{}, C.Bch.bch15_7(), _), D.Bch.flip(ps, x), List.length(&2, U32, ps))) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(List<&2, Bool>, D.Bch.flip(ps, x), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], bche.dinj(D.Bch.flip(ps, x), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], h)) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(D.bch.cor.check(True{}, C.Bch.bch15_7(), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]), _, List.length(&2, U32, ps))) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(Bool, D.bch.cor.check(True{}, C.Bch.bch15_7(), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]), True{}, bche.zck()) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(_, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], List.length(&2, U32, ps))) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %bche.pb8() : {Done{List.take(&2, Bool, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], Nat.sub(List.length(&2, Bool, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]), _))} == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      {==}

def bche.ga(+e: List<&2, Bool>, +he: {List.length(&2, Bool, e) == 15n : Nat}, h: {Pt.chk15(e) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> {D.Bch.decode_bits(C.Bch.bch15_7(), e) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  %Equal.sym(Result<&2, &2, E.BchError, List<&2, Bool>>, D.Bch.decode_bits(C.Bch.bch15_7(), e), D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), e), 15), D.Bch.opts(), C.Bch.bch15_7(), e)), bche.unf(e, he)) : {_ == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  bche.gar(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), e), 15), e, h)

# The decoder treats w + x as it treats x, when w's syndromes are zero

def bche.t7(+z: List<&2, Bool>, +h15: {List.length(&2, Bool, z) == 15n : Nat}, ht: {List.take(&2, Bool, z, Nat.sub(List.length(&2, Bool, z), C.Bch.parity_bits(C.Bch.bch15_7()))) == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}) -> {List.take(&2, Bool, z, 7n) == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}:
  %h15 : {List.take(&2, Bool, z, Nat.sub(_, 8n)) == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}
  %Equal.sym(Nat, 8n, C.Bch.parity_bits(C.Bch.bch15_7()), bche.pb8()) : {List.take(&2, Bool, z, Nat.sub(List.length(&2, Bool, z), _)) == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}
  ht

# the final check passes for both or for neither
def bche.h2(b: Bool, +w: List<&2, Bool>, +z: List<&2, Bool>, +n: Nat, +hl: {List.length(&2, Bool, w) == 15n : Nat}, +same: {List.length(&2, Bool, w) == List.length(&2, Bool, z) : Nat}, h: {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(b, z, n)) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(b, Pt.xl(w, z), n)) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  match b:
    case False{}:
      Empty.absurd({D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(False{}, Pt.xl(w, z), n)) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}, bche.fd(E.BchUncorrectable{}, [False{}, False{}, False{}, False{}, False{}, False{}, False{}], h))
    case True{}:
      %bche.pb8() : {Done{List.take(&2, Bool, Pt.xl(w, z), Nat.sub(List.length(&2, Bool, Pt.xl(w, z)), _))} == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(Nat, List.length(&2, Bool, Pt.xl(w, z)), 15n, Equal.trans(Nat, List.length(&2, Bool, Pt.xl(w, z)), List.length(&2, Bool, w), 15n, bche.xl_len(w, z, same), hl)) : {Done{List.take(&2, Bool, Pt.xl(w, z), Nat.sub(_, 8n))} == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(List<&2, Bool>, List.take(&2, Bool, Pt.xl(w, z), 7n), Pt.xl(List.take(&2, Bool, w, 7n), List.take(&2, Bool, z, 7n)), bche.ta(w, z, 7n, same)) : {Done{_} == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(List<&2, Bool>, List.take(&2, Bool, z, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}], bche.t7(z, Equal.trans(Nat, List.length(&2, Bool, z), List.length(&2, Bool, w), 15n, Equal.sym(Nat, List.length(&2, Bool, w), List.length(&2, Bool, z), same), hl), bche.dinj(List.take(&2, Bool, z, Nat.sub(List.length(&2, Bool, z), C.Bch.parity_bits(C.Bch.bch15_7()))), [False{}, False{}, False{}, False{}, False{}, False{}, False{}], h))) : {Done{Pt.xl(List.take(&2, Bool, w, 7n), _)} == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      {==}

# the error positions are the same for both (r): a failure fails both
def bche.h(r: Result<&2, &2, E.BchError, List<&2, U32>>, +w: List<&2, Bool>, +x: List<&2, Bool>, +hw: {S.Bch.syndromes(C.Bch.bch15_7(), w) == [0, 0, 0, 0] : List<&2, U32>}, +hl: {List.length(&2, Bool, w) == 15n : Nat}, +same: {List.length(&2, Bool, w) == List.length(&2, Bool, x) : Nat}, h: {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(r, D.Bch.opts(), C.Bch.bch15_7(), x)) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(r, D.Bch.opts(), C.Bch.bch15_7(), Pt.xl(w, x))) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  match r:
    case Fail{er}:
      Empty.absurd({D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(Fail{er}, D.Bch.opts(), C.Bch.bch15_7(), Pt.xl(w, x))) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}, bche.fd(er, [False{}, False{}, False{}, False{}, False{}, False{}, False{}], h))
    case Done{+ps}:
      %Equal.sym(List<&2, Bool>, D.Bch.flip(ps, Pt.xl(w, x)), Pt.xl(w, D.Bch.flip(ps, x)), bche.flp(ps, w, x, same)) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(D.bch.cor.check(True{}, C.Bch.bch15_7(), _), D.Bch.flip(ps, Pt.xl(w, x)), List.length(&2, U32, ps))) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(List<&2, Bool>, D.Bch.flip(ps, Pt.xl(w, x)), Pt.xl(w, D.Bch.flip(ps, x)), bche.flp(ps, w, x, same)) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(D.bch.cor.check(True{}, C.Bch.bch15_7(), Pt.xl(w, D.Bch.flip(ps, x))), _, List.length(&2, U32, ps))) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      %Equal.sym(List<&2, U32>, S.Bch.syndromes(C.Bch.bch15_7(), Pt.xl(w, D.Bch.flip(ps, x))), S.Bch.syndromes(C.Bch.bch15_7(), D.Bch.flip(ps, x)), bche.ss(w, D.Bch.flip(ps, x), hw, Equal.trans(Nat, List.length(&2, Bool, w), List.length(&2, Bool, x), List.length(&2, Bool, D.Bch.flip(ps, x)), same, Equal.sym(Nat, List.length(&2, Bool, D.Bch.flip(ps, x)), List.length(&2, Bool, x), bche.flp_len(ps, x))))) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.verify(P.RsPoly.is_zero(C.Bch.field(C.Bch.bch15_7()), _), Pt.xl(w, D.Bch.flip(ps, x)), List.length(&2, U32, ps))) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
      bche.h2(P.RsPoly.is_zero(C.Bch.field(C.Bch.bch15_7()), S.Bch.syndromes(C.Bch.bch15_7(), D.Bch.flip(ps, x))), w, D.Bch.flip(ps, x), List.length(&2, U32, ps), hl, Equal.trans(Nat, List.length(&2, Bool, w), List.length(&2, Bool, x), List.length(&2, Bool, D.Bch.flip(ps, x)), same, Equal.sym(Nat, List.length(&2, Bool, D.Bch.flip(ps, x)), List.length(&2, Bool, x), bche.flp_len(ps, x))), h)

def bche.ds(+w: List<&2, Bool>, +e: List<&2, Bool>, +hw: {S.Bch.syndromes(C.Bch.bch15_7(), w) == [0, 0, 0, 0] : List<&2, U32>}, +hl: {List.length(&2, Bool, w) == 15n : Nat}, +he: {List.length(&2, Bool, e) == 15n : Nat}, hz: {D.Bch.decode_bits(C.Bch.bch15_7(), e) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}) -> {D.Bch.decode_bits(C.Bch.bch15_7(), Pt.xl(w, e)) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  %Equal.sym(Result<&2, &2, E.BchError, List<&2, Bool>>, D.Bch.decode_bits(C.Bch.bch15_7(), Pt.xl(w, e)), D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), Pt.xl(w, e)), 15), D.Bch.opts(), C.Bch.bch15_7(), Pt.xl(w, e))), bche.unf(Pt.xl(w, e), Equal.trans(Nat, List.length(&2, Bool, Pt.xl(w, e)), List.length(&2, Bool, w), 15n, bche.xl_len(w, e, Equal.trans(Nat, List.length(&2, Bool, w), 15n, List.length(&2, Bool, e), hl, Equal.sym(Nat, List.length(&2, Bool, e), 15n, he))), hl))) : {_ == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  %Equal.sym(List<&2, U32>, S.Bch.syndromes(C.Bch.bch15_7(), Pt.xl(w, e)), S.Bch.syndromes(C.Bch.bch15_7(), e), bche.ss(w, e, hw, Equal.trans(Nat, List.length(&2, Bool, w), 15n, List.length(&2, Bool, e), hl, Equal.sym(Nat, List.length(&2, Bool, e), 15n, he)))) : {D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(D.Bch.locate(C.Bch.bch15_7(), _, 15), D.Bch.opts(), C.Bch.bch15_7(), Pt.xl(w, e))) == Done{Pt.xl(List.take(&2, Bool, w, 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  bche.h(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), e), 15), w, e, hw, hl, Equal.trans(Nat, List.length(&2, Bool, w), 15n, List.length(&2, Bool, e), hl, Equal.sym(Nat, List.length(&2, Bool, e), 15n, he)), Equal.trans(Result<&2, &2, E.BchError, List<&2, Bool>>, D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), e), 15), D.Bch.opts(), C.Bch.bch15_7(), e)), D.Bch.decode_bits(C.Bch.bch15_7(), e), Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]}, Equal.sym(Result<&2, &2, E.BchError, List<&2, Bool>>, D.Bch.decode_bits(C.Bch.bch15_7(), e), D.bch.dec.msg(C.Bch.bch15_7(), D.bch.cor.fin(D.Bch.locate(C.Bch.bch15_7(), S.Bch.syndromes(C.Bch.bch15_7(), e), 15), D.Bch.opts(), C.Bch.bch15_7(), e)), bche.unf(e, he)), hz))

# Codewords of 7 data bits

def bche.app1_len(t: List<&2, Bool>, +x: Bool) -> {List.length(&2, Bool, List.append(&2, Bool, t, [x])) == 1n+List.length(&2, Bool, t) : Nat}:
  match t:
    case Nil{}:
      {==}
    case Con{h, +r}:
      %bche.app1_len(r, x) : {1n+List.length(&2, Bool, List.append(&2, Bool, r, [x])) == 1n+_ : Nat}
      {==}

def bche.app_len(a: List<&2, Bool>, +b: List<&2, Bool>) -> {List.length(&2, Bool, List.append(&2, Bool, a, b)) == Nat.add(List.length(&2, Bool, a), List.length(&2, Bool, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %bche.app_len(t, b) : {1n+List.length(&2, Bool, List.append(&2, Bool, t, b)) == 1n+_ : Nat}
      {==}

def bche.up_len(reg: List<&2, Bool>) -> {List.length(&2, Bool, E.bch.up(reg)) == List.length(&2, Bool, reg) : Nat}:
  match reg:
    case Nil{}:
      {==}
    case Con{r, +t}:
      bche.app1_len(t, False{})

def bche.addif_len(+fb: Bool, a: List<&2, Bool>, g: List<&2, Bool>) -> {List.length(&2, Bool, E.bch.addif(fb, a, g)) == List.length(&2, Bool, a) : Nat}:
  match a g:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{x, +s} Con{y, +t}:
      %bche.addif_len(fb, s, t) : {1n+List.length(&2, Bool, E.bch.addif(fb, s, t)) == 1n+_ : Nat}
      {==}

def bche.run_len(bits: List<&2, Bool>, +gd: List<&2, Bool>, +reg: List<&2, Bool>) -> {List.length(&2, Bool, E.bch.enc.run(bits, gd, reg)) == List.length(&2, Bool, reg) : Nat}:
  match bits:
    case Nil{}:
      {==}
    case Con{+b, t}:
      Equal.trans(Nat, List.length(&2, Bool, E.bch.enc.run(t, gd, E.bch.enc.step(gd, reg, b))), List.length(&2, Bool, E.bch.enc.step(gd, reg, b)), List.length(&2, Bool, reg), bche.run_len(t, gd, E.bch.enc.step(gd, reg, b)), Equal.trans(Nat, List.length(&2, Bool, E.bch.enc.step(gd, reg, b)), List.length(&2, Bool, E.bch.up(reg)), List.length(&2, Bool, reg), bche.addif_len(Bool.xor(b, E.bch.top(reg)), E.bch.up(reg), gd), bche.up_len(reg)))

def bche.cwlen(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {List.length(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m)) == 15n : Nat}:
  %Equal.sym(Nat, List.length(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m)), Nat.add(List.length(&2, Bool, m), List.length(&2, Bool, E.Bch.parity(C.Bch.bch15_7(), m))), bche.app_len(m, E.Bch.parity(C.Bch.bch15_7(), m))) : {_ == 15n : Nat}
  %Equal.sym(Nat, List.length(&2, Bool, m), 7n, n7) : {Nat.add(_, List.length(&2, Bool, E.Bch.parity(C.Bch.bch15_7(), m))) == 15n : Nat}
  %Equal.sym(Nat, List.length(&2, Bool, E.bch.enc.run(m, E.Bch.gen_desc(C.Bch.bch15_7()), E.bch.falses(C.Bch.parity_bits(C.Bch.bch15_7())))), List.length(&2, Bool, E.bch.falses(C.Bch.parity_bits(C.Bch.bch15_7()))), bche.run_len(m, E.Bch.gen_desc(C.Bch.bch15_7()), E.bch.falses(C.Bch.parity_bits(C.Bch.bch15_7())))) : {Nat.add(7n, _) == 15n : Nat}
  %bche.pb8() : {Nat.add(7n, List.length(&2, Bool, E.bch.falses(_))) == 15n : Nat}
  {==}

def bche.short7(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {Nat.is_le(List.length(&2, Bool, m), 7n) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Bool, m), 7n, n7) : {Nat.is_le(_, 7n) == True{} : Bool}
  {==}

def bche.hw(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {S.Bch.syndromes(C.Bch.bch15_7(), E.Bch.codeword(C.Bch.bch15_7(), m)) == [0, 0, 0, 0] : List<&2, U32>}:
  BL.small15_syndromes(m, bche.short7(m, n7))

# zeros of equal lengths
def bche.fz(+n1: Nat, +n2: Nat, +h: {n1 == n2 : Nat}) -> {E.bch.falses(n1) == E.bch.falses(n2) : List<&2, Bool>}:
  %h : {E.bch.falses(n1) == E.bch.falses(_) : List<&2, Bool>}
  {==}

# the codeword plus zeros
def bche.cwx(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == E.Bch.codeword(C.Bch.bch15_7(), m) : List<&2, Bool>}:
  %bche.fz(List.length(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m)), 15n, bche.cwlen(m, n7)) : {Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), _) == E.Bch.codeword(C.Bch.bch15_7(), m) : List<&2, Bool>}
  bche.xz(E.Bch.codeword(C.Bch.bch15_7(), m))

def bche.flipcw(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}, +ps: List<&2, U32>) -> {D.Bch.flip(ps, E.Bch.codeword(C.Bch.bch15_7(), m)) == Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])) : List<&2, Bool>}:
  %bche.cwx(m, n7) : {D.Bch.flip(ps, _) == Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])) : List<&2, Bool>}
  bche.flp(ps, E.Bch.codeword(C.Bch.bch15_7(), m), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}], bche.cwlen(m, n7))

def bche.tm(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {List.take(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m), 7n) == m : List<&2, Bool>}:
  %n7 : {List.take(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m), _) == m : List<&2, Bool>}
  BL.codeword_message(C.Bch.bch15_7(), m)

def bche.xmz(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {Pt.xl(m, [False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == m : List<&2, Bool>}:
  %bche.fz(List.length(&2, Bool, m), 7n, n7) : {Pt.xl(m, _) == m : List<&2, Bool>}
  bche.xz(m)

def bche.tail(+m: List<&2, Bool>, +n7: {List.length(&2, Bool, m) == 7n : Nat}) -> {Done{Pt.xl(List.take(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m), 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}:
  %Equal.sym(List<&2, Bool>, List.take(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m), 7n), m, bche.tm(m, n7)) : {Done{Pt.xl(_, [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  %bche.xmz(m, n7) : {Done{Pt.xl(m, [False{}, False{}, False{}, False{}, False{}, False{}, False{}])} == Done{_} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  {==}

# Laws

def Laws.small15_syndromes_shift(m, n7, ps):
  %Equal.sym(List<&2, Bool>, D.Bch.flip(ps, E.Bch.codeword(C.Bch.bch15_7(), m)), Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])), bche.flipcw(m, n7, ps)) : {S.Bch.syndromes(C.Bch.bch15_7(), _) == S.Bch.syndromes(C.Bch.bch15_7(), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])) : List<&2, U32>}
  bche.ss(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]), bche.hw(m, n7), Equal.trans(Nat, List.length(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m)), 15n, List.length(&2, Bool, D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])), bche.cwlen(m, n7), Equal.sym(Nat, List.length(&2, Bool, D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])), 15n, bche.flp_len(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]))))

def Laws.small15_decode_shift(m, n7, ps, zero):
  %Equal.sym(List<&2, Bool>, D.Bch.flip(ps, E.Bch.codeword(C.Bch.bch15_7(), m)), Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])), bche.flipcw(m, n7, ps)) : {D.Bch.decode_bits(C.Bch.bch15_7(), _) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  Equal.trans(Result<&2, &2, E.BchError, List<&2, Bool>>, D.Bch.decode_bits(C.Bch.bch15_7(), Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]))), Done{Pt.xl(List.take(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m), 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])}, Done{m}, bche.ds(E.Bch.codeword(C.Bch.bch15_7(), m), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]), bche.hw(m, n7), bche.cwlen(m, n7), bche.flp_len(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]), zero), bche.tail(m, n7))

def bche.dmf(+w: List<&2, Bool>, +i: Nat, +j: Nat, +h15: {List.length(&2, Bool, w) == 15n : Nat}) -> {D.Bch.flip_at(D.Bch.flip_at(w, i), j) == Pt.xl(w, Pt.pat15(i, j)) : List<&2, Bool>}:
  bche.dm(w, i, j, h15)

def Laws.small15_two_errors(m, n7, i, j):
  %Equal.sym(List<&2, Bool>, D.Bch.flip_at(D.Bch.flip_at(E.Bch.codeword(C.Bch.bch15_7(), m), i), j), Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), Pt.pat15(i, j)), bche.dmf(E.Bch.codeword(C.Bch.bch15_7(), m), i, j, bche.cwlen(m, n7))) : {D.Bch.decode_bits(C.Bch.bch15_7(), _) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  Equal.trans(Result<&2, &2, E.BchError, List<&2, Bool>>, D.Bch.decode_bits(C.Bch.bch15_7(), Pt.xl(E.Bch.codeword(C.Bch.bch15_7(), m), Pt.pat15(i, j))), Done{Pt.xl(List.take(&2, Bool, E.Bch.codeword(C.Bch.bch15_7(), m), 7n), [False{}, False{}, False{}, False{}, False{}, False{}, False{}])}, Done{m}, bche.ds(E.Bch.codeword(C.Bch.bch15_7(), m), Pt.pat15(i, j), bche.hw(m, n7), bche.cwlen(m, n7), bche.plen(i, j), bche.ga(Pt.pat15(i, j), bche.plen(i, j), Pt.q15(i, j))), bche.tail(m, n7))
