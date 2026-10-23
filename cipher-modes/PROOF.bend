import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../word64/word64.bend as W
import ./cipher-modes.bend as M
import ./aes.bend as X
import ./pkcs7.bend as P
import ./cbc.bend as C
import ./xts.bend as T
import ./ccm.bend as CC
import ./cmac.bend as CM
import ./aes_modes.bend as D
import ./LAWS.bend as Laws

# How the proofs go. The modes work on blocks; the byte layer splits a byte
# string into blocks and joins blocks back. The lemmas below show:
#   * XOR with the same block twice is the identity (bit by bit);
#   * a word split into bytes and joined back is the word, and the bytes of a
#     joined word are the (masked) bytes (bit slicing, every bit symbolic);
#   * splitting joined blocks gives the blocks back, and joining a split
#     byte string gives it back (induction, 16 bytes at a time);
#   * every to_list of an Octets is masked (the bytes interface laws
#     octets_of_to and octets_to_of), so the bytes a mode reads back are the
#     bytes it wrote.
# Nothing here looks inside Octets: only the bytes laws and its list layer.

# XOR

def bx.bool(a: Bool, b: Bool) -> {Bool.xor(a, Bool.xor(a, b)) == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def bx.word(n: Nat, a: Word(n), b: Word(n)) -> {Word.xor(n, a, Word.xor(n, a, b)) == b : Word(n)}:
  match n:
    case 0n:
      match b:
        case WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %bx.bool(ah, bh) : {WCon{Bool.xor(ah, Bool.xor(ah, bh)), Word.xor(p, at, Word.xor(p, at, bt))} == WCon{_, bt} : Word(1n+p)}
          %bx.word(p, at, bt) : {WCon{Bool.xor(ah, Bool.xor(ah, bh)), Word.xor(p, at, Word.xor(p, at, bt))} == WCon{Bool.xor(ah, Bool.xor(ah, bh)), _} : Word(1n+p)}
          {==}

def bx.u32(a: U32, b: U32) -> {U32.xor(a, U32.xor(a, b)) == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %bx.word(32n, x, y) : {U32{Word.xor(32n, x, Word.xor(32n, x, y))} == U32{_} : U32}
      {==}

# xor(a, xor(a, b)) == b on blocks
def bx.block(+a: M.CmBlock, +b: M.CmBlock) -> {M.CmBlock.xor(a, M.CmBlock.xor(a, b)) == b : M.CmBlock}:
  match a b:
    case M.CmBlock{a0, a1, a2, a3} M.CmBlock{b0, b1, b2, b3}:
      %bx.u32(a0, b0) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{_, b1, b2, b3} : M.CmBlock}
      %bx.u32(a1, b1) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{U32.xor(a0, U32.xor(a0, b0)), _, b2, b3} : M.CmBlock}
      %bx.u32(a2, b2) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{U32.xor(a0, U32.xor(a0, b0)), U32.xor(a1, U32.xor(a1, b1)), _, b3} : M.CmBlock}
      %bx.u32(a3, b3) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{U32.xor(a0, U32.xor(a0, b0)), U32.xor(a1, U32.xor(a1, b1)), U32.xor(a2, U32.xor(a2, b2)), _} : M.CmBlock}
      {==}

# Bits: each lemma splits its words into their 32 bits, so the slicing
# computes

def bits.word_bytes(w: U32) -> {M.cm.word(M.cm.b0(w), M.cm.b1(w), M.cm.b2(w), M.cm.b3(w)) == w : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte0_word(a: U32, b: U32, c: U32, d: U32) -> {M.cm.b0(M.cm.word(a, b, c, d)) == B.byte(a) : U32}:
  match a b c d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte1_word(a: U32, b: U32, c: U32, d: U32) -> {M.cm.b1(M.cm.word(a, b, c, d)) == B.byte(b) : U32}:
  match a b c d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte2_word(a: U32, b: U32, c: U32, d: U32) -> {M.cm.b2(M.cm.word(a, b, c, d)) == B.byte(c) : U32}:
  match a b c d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte3_word(a: U32, b: U32, c: U32, d: U32) -> {M.cm.b3(M.cm.word(a, b, c, d)) == B.byte(d) : U32}:
  match a b c d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte_b0(w: U32) -> {B.byte(M.cm.b0(w)) == M.cm.b0(w) : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte_b1(w: U32) -> {B.byte(M.cm.b1(w)) == M.cm.b1(w) : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte_b2(w: U32) -> {B.byte(M.cm.b2(w)) == M.cm.b2(w) : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte_b3(w: U32) -> {B.byte(M.cm.b3(w)) == M.cm.b3(w) : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def bits.byte_byte(y: U32) -> {B.byte(B.byte(y)) == B.byte(y) : U32}:
  match y:
    case U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}
# Splits

def sp.cons_blocks(b: M.CmBlock, s: M.CmSplit) -> {M.cm.split.blocks(M.cm.split.cons(b, s)) == Con{b, M.cm.split.blocks(s)} : List<&2, M.CmBlock>}:
  match s:
    case M.CmSplit{bs, t}:
      {==}

def sp.cons_tail(b: M.CmBlock, s: M.CmSplit) -> {M.cm.split.tail(M.cm.split.cons(b, s)) == M.cm.split.tail(s) : List<&2, U32>}:
  match s:
    case M.CmSplit{bs, t}:
      {==}

def sp.eta(s: M.CmSplit) -> {M.CmSplit{M.cm.split.blocks(s), M.cm.split.tail(s)} == s : M.CmSplit}:
  match s:
    case M.CmSplit{bs, t}:
      {==}

# Arithmetic: n + 16 and n leave the same remainder mod 16

def sp.disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def sp.absurd(p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : sp.disc(_)
  Unit{}

def sp.absurd_tail(p: Nat, xs: List<&2, U32>, h: {1n+p == 0n : Nat}) -> {M.cm.split.tail(M.cm.split(B.mask(xs))) == Nil{} : List<&2, U32>}:
  Empty.absurd({M.cm.split.tail(M.cm.split(B.mask(xs))) == Nil{} : List<&2, U32>}, sp.absurd(p, h))

def sp.snd_go(n: Nat, m: Nat, d1: Nat, d2: Nat, r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d1, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d2, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          sp.snd_go(np, r, 1n+d1, 1n+d2, 0n)
        case 1n+mp:
          sp.snd_go(np, mp, d1, d2, 1n+r)

def sp.mod16(n: Nat) -> {Nat.mod(Nat.add(16n, n), 16n) == Nat.mod(n, 16n) : Nat}:
  sp.snd_go(n, 15n, 1n, 0n, 0n)


# Booleans: False is not True

def bo.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def bo.empty(h: {False{} == True{} : Bool}) -> Empty:
  %h : bo.disc(_)
  Unit{}

def bo.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, bo.empty(h))

# Lists of bytes (the bytes list layer)

def li.mask_mask(zs: List<&2, U32>) -> {B.mask(B.mask(zs)) == B.mask(zs) : List<&2, U32>}:
  match zs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      %bits.byte_byte(z) : {Con{B.byte(B.byte(z)), B.mask(B.mask(t))} == Con{_, B.mask(t)} : List<&2, U32>}
      %li.mask_mask(t) : {Con{B.byte(B.byte(z)), B.mask(B.mask(t))} == Con{B.byte(B.byte(z)), _} : List<&2, U32>}
      {==}

def li.take_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.take(B.len(a), B.append(a, b)) == a : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, U32>, B.take(B.len(t), B.append(t, b)), t, li.take_append(t, b)) : {Con{h, _} == Con{h, t} : List<&2, U32>}
      {==}

def li.drop_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.drop(B.len(a), B.append(a, b)) == b : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      li.drop_append(t, b)

def li.mask_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.mask(B.append(a, b)) == B.append(B.mask(a), B.mask(b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %li.mask_append(t, b) : {Con{B.byte(h), B.mask(B.append(t, b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def li.mask_drop(+n: Nat, +xs: List<&2, U32>) -> {B.mask(B.drop(n, xs)) == B.drop(n, B.mask(xs)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          li.mask_drop(p, t)

def li.mask_take(+n: Nat, +xs: List<&2, U32>) -> {B.mask(B.take(n, xs)) == B.take(n, B.mask(xs)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          %li.mask_take(p, t) : {Con{B.byte(h), B.mask(B.take(p, t))} == Con{B.byte(h), _} : List<&2, U32>}
          {==}

def li.len_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %li.len_append(t, b) : {1n+B.len(B.append(t, b)) == 1n+_ : Nat}
      {==}

def li.len_drop(+n: Nat, +xs: List<&2, U32>) -> {B.len(B.drop(n, xs)) == Nat.sub(B.len(xs), n) : Nat}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          li.len_drop(p, t)

def li.len_take(+n: Nat, +xs: List<&2, U32>) -> {Nat.is_le(n, B.len(xs)) == True{} : Bool} -> {B.len(B.take(n, xs)) == n : Nat}:
  match n:
    case 0n:
      h => {==}
    case 1n+p:
      match xs:
        case Nil{}:
          h => bo.absurd({B.len(B.take(1n+p, Nil{})) == 1n+p : Nat}, h)
        case Con{+x, +t}:
          h => %li.len_take(p, t)(h) : {1n+B.len(B.take(p, t)) == 1n+_ : Nat}
            {==}

# Naturals

def na.add_sub(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+bp:
      h => {==}
    case 1n+ap 0n:
      h => bo.absurd({Nat.add(1n+ap, Nat.sub(0n, 1n+ap)) == 0n : Nat}, h)
    case 1n+ap 1n+bp:
      h => %na.add_sub(ap, bp)(h) : {1n+Nat.add(ap, Nat.sub(bp, ap)) == 1n+_ : Nat}
        {==}

def na.lt_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      h => bo.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+bp:
      h => {==}
    case 1n+ap 0n:
      h => bo.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, h)
    case 1n+ap 1n+bp:
      h => na.lt_le(ap, bp)(h)

# Blocks in lists

def sp.hd(bs: List<&2, M.CmBlock>) -> M.CmBlock:
  match bs:
    case Nil{}:
      M.CmBlock.zero()
    case Con{b, t}:
      b

def sp.tl(bs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      t

# splitting the bytes of a block gives the block back
def sp.blk(b: M.CmBlock, rest: List<&2, U32>) -> {M.cm.split(M.cm.bytes_onto(b, rest)) == M.cm.split.cons(b, M.cm.split(rest)) : M.CmSplit}:
  match b:
    case M.CmBlock{U32{WCon{p0, WCon{p1, WCon{p2, WCon{p3, WCon{p4, WCon{p5, WCon{p6, WCon{p7, WCon{p8, WCon{p9, WCon{p10, WCon{p11, WCon{p12, WCon{p13, WCon{p14, WCon{p15, WCon{p16, WCon{p17, WCon{p18, WCon{p19, WCon{p20, WCon{p21, WCon{p22, WCon{p23, WCon{p24, WCon{p25, WCon{p26, WCon{p27, WCon{p28, WCon{p29, WCon{p30, WCon{p31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{q0, WCon{q1, WCon{q2, WCon{q3, WCon{q4, WCon{q5, WCon{q6, WCon{q7, WCon{q8, WCon{q9, WCon{q10, WCon{q11, WCon{q12, WCon{q13, WCon{q14, WCon{q15, WCon{q16, WCon{q17, WCon{q18, WCon{q19, WCon{q20, WCon{q21, WCon{q22, WCon{q23, WCon{q24, WCon{q25, WCon{q26, WCon{q27, WCon{q28, WCon{q29, WCon{q30, WCon{q31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{r0, WCon{r1, WCon{r2, WCon{r3, WCon{r4, WCon{r5, WCon{r6, WCon{r7, WCon{r8, WCon{r9, WCon{r10, WCon{r11, WCon{r12, WCon{r13, WCon{r14, WCon{r15, WCon{r16, WCon{r17, WCon{r18, WCon{r19, WCon{r20, WCon{r21, WCon{r22, WCon{r23, WCon{r24, WCon{r25, WCon{r26, WCon{r27, WCon{r28, WCon{r29, WCon{r30, WCon{r31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the bytes of a block are bytes: masking changes nothing
def sp.mask_blk(b: M.CmBlock, rest: List<&2, U32>) -> {B.mask(M.cm.bytes_onto(b, rest)) == M.cm.bytes_onto(b, B.mask(rest)) : List<&2, U32>}:
  match b:
    case M.CmBlock{U32{WCon{p0, WCon{p1, WCon{p2, WCon{p3, WCon{p4, WCon{p5, WCon{p6, WCon{p7, WCon{p8, WCon{p9, WCon{p10, WCon{p11, WCon{p12, WCon{p13, WCon{p14, WCon{p15, WCon{p16, WCon{p17, WCon{p18, WCon{p19, WCon{p20, WCon{p21, WCon{p22, WCon{p23, WCon{p24, WCon{p25, WCon{p26, WCon{p27, WCon{p28, WCon{p29, WCon{p30, WCon{p31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{q0, WCon{q1, WCon{q2, WCon{q3, WCon{q4, WCon{q5, WCon{q6, WCon{q7, WCon{q8, WCon{q9, WCon{q10, WCon{q11, WCon{q12, WCon{q13, WCon{q14, WCon{q15, WCon{q16, WCon{q17, WCon{q18, WCon{q19, WCon{q20, WCon{q21, WCon{q22, WCon{q23, WCon{q24, WCon{q25, WCon{q26, WCon{q27, WCon{q28, WCon{q29, WCon{q30, WCon{q31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{r0, WCon{r1, WCon{r2, WCon{r3, WCon{r4, WCon{r5, WCon{r6, WCon{r7, WCon{r8, WCon{r9, WCon{r10, WCon{r11, WCon{r12, WCon{r13, WCon{r14, WCon{r15, WCon{r16, WCon{r17, WCon{r18, WCon{r19, WCon{r20, WCon{r21, WCon{r22, WCon{r23, WCon{r24, WCon{r25, WCon{r26, WCon{r27, WCon{r28, WCon{r29, WCon{r30, WCon{r31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the block of 16 bytes, as bytes again
def sp.blk16(y0: U32, y1: U32, y2: U32, y3: U32, y4: U32, y5: U32, y6: U32, y7: U32, y8: U32, y9: U32, y10: U32, y11: U32, y12: U32, y13: U32, y14: U32, y15: U32, rest: List<&2, U32>) -> {M.cm.bytes_onto(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), rest) == Con{B.byte(y0), Con{B.byte(y1), Con{B.byte(y2), Con{B.byte(y3), Con{B.byte(y4), Con{B.byte(y5), Con{B.byte(y6), Con{B.byte(y7), Con{B.byte(y8), Con{B.byte(y9), Con{B.byte(y10), Con{B.byte(y11), Con{B.byte(y12), Con{B.byte(y13), Con{B.byte(y14), Con{B.byte(y15), rest}}}}}}}}}}}}}}}} : List<&2, U32>}:
  match y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15:
    case U32{WCon{y00, WCon{y01, WCon{y02, WCon{y03, WCon{y04, WCon{y05, WCon{y06, WCon{y07, WCon{y08, WCon{y09, WCon{y010, WCon{y011, WCon{y012, WCon{y013, WCon{y014, WCon{y015, WCon{y016, WCon{y017, WCon{y018, WCon{y019, WCon{y020, WCon{y021, WCon{y022, WCon{y023, WCon{y024, WCon{y025, WCon{y026, WCon{y027, WCon{y028, WCon{y029, WCon{y030, WCon{y031, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y110, WCon{y111, WCon{y112, WCon{y113, WCon{y114, WCon{y115, WCon{y116, WCon{y117, WCon{y118, WCon{y119, WCon{y120, WCon{y121, WCon{y122, WCon{y123, WCon{y124, WCon{y125, WCon{y126, WCon{y127, WCon{y128, WCon{y129, WCon{y130, WCon{y131, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y210, WCon{y211, WCon{y212, WCon{y213, WCon{y214, WCon{y215, WCon{y216, WCon{y217, WCon{y218, WCon{y219, WCon{y220, WCon{y221, WCon{y222, WCon{y223, WCon{y224, WCon{y225, WCon{y226, WCon{y227, WCon{y228, WCon{y229, WCon{y230, WCon{y231, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y30, WCon{y31, WCon{y32, WCon{y33, WCon{y34, WCon{y35, WCon{y36, WCon{y37, WCon{y38, WCon{y39, WCon{y310, WCon{y311, WCon{y312, WCon{y313, WCon{y314, WCon{y315, WCon{y316, WCon{y317, WCon{y318, WCon{y319, WCon{y320, WCon{y321, WCon{y322, WCon{y323, WCon{y324, WCon{y325, WCon{y326, WCon{y327, WCon{y328, WCon{y329, WCon{y330, WCon{y331, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y40, WCon{y41, WCon{y42, WCon{y43, WCon{y44, WCon{y45, WCon{y46, WCon{y47, WCon{y48, WCon{y49, WCon{y410, WCon{y411, WCon{y412, WCon{y413, WCon{y414, WCon{y415, WCon{y416, WCon{y417, WCon{y418, WCon{y419, WCon{y420, WCon{y421, WCon{y422, WCon{y423, WCon{y424, WCon{y425, WCon{y426, WCon{y427, WCon{y428, WCon{y429, WCon{y430, WCon{y431, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y50, WCon{y51, WCon{y52, WCon{y53, WCon{y54, WCon{y55, WCon{y56, WCon{y57, WCon{y58, WCon{y59, WCon{y510, WCon{y511, WCon{y512, WCon{y513, WCon{y514, WCon{y515, WCon{y516, WCon{y517, WCon{y518, WCon{y519, WCon{y520, WCon{y521, WCon{y522, WCon{y523, WCon{y524, WCon{y525, WCon{y526, WCon{y527, WCon{y528, WCon{y529, WCon{y530, WCon{y531, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y60, WCon{y61, WCon{y62, WCon{y63, WCon{y64, WCon{y65, WCon{y66, WCon{y67, WCon{y68, WCon{y69, WCon{y610, WCon{y611, WCon{y612, WCon{y613, WCon{y614, WCon{y615, WCon{y616, WCon{y617, WCon{y618, WCon{y619, WCon{y620, WCon{y621, WCon{y622, WCon{y623, WCon{y624, WCon{y625, WCon{y626, WCon{y627, WCon{y628, WCon{y629, WCon{y630, WCon{y631, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y70, WCon{y71, WCon{y72, WCon{y73, WCon{y74, WCon{y75, WCon{y76, WCon{y77, WCon{y78, WCon{y79, WCon{y710, WCon{y711, WCon{y712, WCon{y713, WCon{y714, WCon{y715, WCon{y716, WCon{y717, WCon{y718, WCon{y719, WCon{y720, WCon{y721, WCon{y722, WCon{y723, WCon{y724, WCon{y725, WCon{y726, WCon{y727, WCon{y728, WCon{y729, WCon{y730, WCon{y731, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y80, WCon{y81, WCon{y82, WCon{y83, WCon{y84, WCon{y85, WCon{y86, WCon{y87, WCon{y88, WCon{y89, WCon{y810, WCon{y811, WCon{y812, WCon{y813, WCon{y814, WCon{y815, WCon{y816, WCon{y817, WCon{y818, WCon{y819, WCon{y820, WCon{y821, WCon{y822, WCon{y823, WCon{y824, WCon{y825, WCon{y826, WCon{y827, WCon{y828, WCon{y829, WCon{y830, WCon{y831, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y90, WCon{y91, WCon{y92, WCon{y93, WCon{y94, WCon{y95, WCon{y96, WCon{y97, WCon{y98, WCon{y99, WCon{y910, WCon{y911, WCon{y912, WCon{y913, WCon{y914, WCon{y915, WCon{y916, WCon{y917, WCon{y918, WCon{y919, WCon{y920, WCon{y921, WCon{y922, WCon{y923, WCon{y924, WCon{y925, WCon{y926, WCon{y927, WCon{y928, WCon{y929, WCon{y930, WCon{y931, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y100, WCon{y101, WCon{y102, WCon{y103, WCon{y104, WCon{y105, WCon{y106, WCon{y107, WCon{y108, WCon{y109, WCon{y1010, WCon{y1011, WCon{y1012, WCon{y1013, WCon{y1014, WCon{y1015, WCon{y1016, WCon{y1017, WCon{y1018, WCon{y1019, WCon{y1020, WCon{y1021, WCon{y1022, WCon{y1023, WCon{y1024, WCon{y1025, WCon{y1026, WCon{y1027, WCon{y1028, WCon{y1029, WCon{y1030, WCon{y1031, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y110, WCon{y111, WCon{y112, WCon{y113, WCon{y114, WCon{y115, WCon{y116, WCon{y117, WCon{y118, WCon{y119, WCon{y1110, WCon{y1111, WCon{y1112, WCon{y1113, WCon{y1114, WCon{y1115, WCon{y1116, WCon{y1117, WCon{y1118, WCon{y1119, WCon{y1120, WCon{y1121, WCon{y1122, WCon{y1123, WCon{y1124, WCon{y1125, WCon{y1126, WCon{y1127, WCon{y1128, WCon{y1129, WCon{y1130, WCon{y1131, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y120, WCon{y121, WCon{y122, WCon{y123, WCon{y124, WCon{y125, WCon{y126, WCon{y127, WCon{y128, WCon{y129, WCon{y1210, WCon{y1211, WCon{y1212, WCon{y1213, WCon{y1214, WCon{y1215, WCon{y1216, WCon{y1217, WCon{y1218, WCon{y1219, WCon{y1220, WCon{y1221, WCon{y1222, WCon{y1223, WCon{y1224, WCon{y1225, WCon{y1226, WCon{y1227, WCon{y1228, WCon{y1229, WCon{y1230, WCon{y1231, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y130, WCon{y131, WCon{y132, WCon{y133, WCon{y134, WCon{y135, WCon{y136, WCon{y137, WCon{y138, WCon{y139, WCon{y1310, WCon{y1311, WCon{y1312, WCon{y1313, WCon{y1314, WCon{y1315, WCon{y1316, WCon{y1317, WCon{y1318, WCon{y1319, WCon{y1320, WCon{y1321, WCon{y1322, WCon{y1323, WCon{y1324, WCon{y1325, WCon{y1326, WCon{y1327, WCon{y1328, WCon{y1329, WCon{y1330, WCon{y1331, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y140, WCon{y141, WCon{y142, WCon{y143, WCon{y144, WCon{y145, WCon{y146, WCon{y147, WCon{y148, WCon{y149, WCon{y1410, WCon{y1411, WCon{y1412, WCon{y1413, WCon{y1414, WCon{y1415, WCon{y1416, WCon{y1417, WCon{y1418, WCon{y1419, WCon{y1420, WCon{y1421, WCon{y1422, WCon{y1423, WCon{y1424, WCon{y1425, WCon{y1426, WCon{y1427, WCon{y1428, WCon{y1429, WCon{y1430, WCon{y1431, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y150, WCon{y151, WCon{y152, WCon{y153, WCon{y154, WCon{y155, WCon{y156, WCon{y157, WCon{y158, WCon{y159, WCon{y1510, WCon{y1511, WCon{y1512, WCon{y1513, WCon{y1514, WCon{y1515, WCon{y1516, WCon{y1517, WCon{y1518, WCon{y1519, WCon{y1520, WCon{y1521, WCon{y1522, WCon{y1523, WCon{y1524, WCon{y1525, WCon{y1526, WCon{y1527, WCon{y1528, WCon{y1529, WCon{y1530, WCon{y1531, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# a masked list is its blocks and its tail joined back
def sp.join_split(ys: List<&2, U32>) -> {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), M.cm.split.tail(M.cm.split(B.mask(ys)))) == B.mask(ys) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          {==}
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              {==}
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  {==}
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      {==}
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          {==}
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              {==}
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  {==}
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      {==}
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          {==}
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              {==}
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  {==}
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      {==}
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          {==}
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              {==}
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  {==}
                                                                case Con{+y15, +t}:
                                                                  %Equal.sym(List<&2, M.CmBlock>, M.cm.split.blocks(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), Con{M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split.blocks(M.cm.split(B.mask(t)))}, sp.cons_blocks(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {M.cm.join_onto(_, M.cm.split.tail(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t))))) == Con{B.byte(y0), Con{B.byte(y1), Con{B.byte(y2), Con{B.byte(y3), Con{B.byte(y4), Con{B.byte(y5), Con{B.byte(y6), Con{B.byte(y7), Con{B.byte(y8), Con{B.byte(y9), Con{B.byte(y10), Con{B.byte(y11), Con{B.byte(y12), Con{B.byte(y13), Con{B.byte(y14), Con{B.byte(y15), B.mask(t)}}}}}}}}}}}}}}}} : List<&2, U32>}
                                                                  %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), M.cm.split.tail(M.cm.split(B.mask(t))), sp.cons_tail(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {M.cm.join_onto(Con{M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split.blocks(M.cm.split(B.mask(t)))}, _) == Con{B.byte(y0), Con{B.byte(y1), Con{B.byte(y2), Con{B.byte(y3), Con{B.byte(y4), Con{B.byte(y5), Con{B.byte(y6), Con{B.byte(y7), Con{B.byte(y8), Con{B.byte(y9), Con{B.byte(y10), Con{B.byte(y11), Con{B.byte(y12), Con{B.byte(y13), Con{B.byte(y14), Con{B.byte(y15), B.mask(t)}}}}}}}}}}}}}}}} : List<&2, U32>}
                                                                  %Equal.sym(List<&2, U32>, M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(t))), M.cm.split.tail(M.cm.split(B.mask(t)))), B.mask(t), sp.join_split(t)) : {M.cm.bytes_onto(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), _) == Con{B.byte(y0), Con{B.byte(y1), Con{B.byte(y2), Con{B.byte(y3), Con{B.byte(y4), Con{B.byte(y5), Con{B.byte(y6), Con{B.byte(y7), Con{B.byte(y8), Con{B.byte(y9), Con{B.byte(y10), Con{B.byte(y11), Con{B.byte(y12), Con{B.byte(y13), Con{B.byte(y14), Con{B.byte(y15), B.mask(t)}}}}}}}}}}}}}}}} : List<&2, U32>}
                                                                  sp.blk16(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, B.mask(t))

# a list of whole blocks splits with no tail
def sp.mod_tail(ys: List<&2, U32>) -> {Nat.mod(B.len(ys), 16n) == 0n : Nat} -> {M.cm.split.tail(M.cm.split(B.mask(ys))) == Nil{} : List<&2, U32>}:
  match ys:
    case Nil{}:
      h => {==}
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => sp.absurd_tail(0n, Con{y0, Nil{}}, h)
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => sp.absurd_tail(1n, Con{y0, Con{y1, Nil{}}}, h)
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => sp.absurd_tail(2n, Con{y0, Con{y1, Con{y2, Nil{}}}}, h)
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => sp.absurd_tail(3n, Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}, h)
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => sp.absurd_tail(4n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}, h)
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => sp.absurd_tail(5n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}, h)
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => sp.absurd_tail(6n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}, h)
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => sp.absurd_tail(7n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}, h)
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => sp.absurd_tail(8n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}, h)
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => sp.absurd_tail(9n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}, h)
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => sp.absurd_tail(10n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}, h)
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => sp.absurd_tail(11n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}, h)
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => sp.absurd_tail(12n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}, h)
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => sp.absurd_tail(13n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}, h)
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => sp.absurd_tail(14n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}, h)
                                                                case Con{+y15, +t}:
                                                                  h => %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), M.cm.split.tail(M.cm.split(B.mask(t))), sp.cons_tail(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {_ == Nil{} : List<&2, U32>}
                                                                    sp.mod_tail(t)(Equal.trans(Nat, Nat.mod(B.len(t), 16n), Nat.mod(Nat.add(16n, B.len(t)), 16n), 0n, Equal.sym(Nat, Nat.mod(Nat.add(16n, B.len(t)), 16n), Nat.mod(B.len(t), 16n), sp.mod16(B.len(t))), h))

# the bytes of the block of any 16 values are those values, masked
def sp.blk16g(z0: U32, z1: U32, z2: U32, z3: U32, z4: U32, z5: U32, z6: U32, z7: U32, z8: U32, z9: U32, z10: U32, z11: U32, z12: U32, z13: U32, z14: U32, z15: U32, rest: List<&2, U32>) -> {M.cm.bytes_onto(M.cm.block16(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15), rest) == Con{B.byte(z0), Con{B.byte(z1), Con{B.byte(z2), Con{B.byte(z3), Con{B.byte(z4), Con{B.byte(z5), Con{B.byte(z6), Con{B.byte(z7), Con{B.byte(z8), Con{B.byte(z9), Con{B.byte(z10), Con{B.byte(z11), Con{B.byte(z12), Con{B.byte(z13), Con{B.byte(z14), Con{B.byte(z15), rest}}}}}}}}}}}}}}}} : List<&2, U32>}:
  match z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15:
    case U32{WCon{z00, WCon{z01, WCon{z02, WCon{z03, WCon{z04, WCon{z05, WCon{z06, WCon{z07, WCon{z08, WCon{z09, WCon{z010, WCon{z011, WCon{z012, WCon{z013, WCon{z014, WCon{z015, WCon{z016, WCon{z017, WCon{z018, WCon{z019, WCon{z020, WCon{z021, WCon{z022, WCon{z023, WCon{z024, WCon{z025, WCon{z026, WCon{z027, WCon{z028, WCon{z029, WCon{z030, WCon{z031, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z10, WCon{z11, WCon{z12, WCon{z13, WCon{z14, WCon{z15, WCon{z16, WCon{z17, WCon{z18, WCon{z19, WCon{z110, WCon{z111, WCon{z112, WCon{z113, WCon{z114, WCon{z115, WCon{z116, WCon{z117, WCon{z118, WCon{z119, WCon{z120, WCon{z121, WCon{z122, WCon{z123, WCon{z124, WCon{z125, WCon{z126, WCon{z127, WCon{z128, WCon{z129, WCon{z130, WCon{z131, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z20, WCon{z21, WCon{z22, WCon{z23, WCon{z24, WCon{z25, WCon{z26, WCon{z27, WCon{z28, WCon{z29, WCon{z210, WCon{z211, WCon{z212, WCon{z213, WCon{z214, WCon{z215, WCon{z216, WCon{z217, WCon{z218, WCon{z219, WCon{z220, WCon{z221, WCon{z222, WCon{z223, WCon{z224, WCon{z225, WCon{z226, WCon{z227, WCon{z228, WCon{z229, WCon{z230, WCon{z231, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z30, WCon{z31, WCon{z32, WCon{z33, WCon{z34, WCon{z35, WCon{z36, WCon{z37, WCon{z38, WCon{z39, WCon{z310, WCon{z311, WCon{z312, WCon{z313, WCon{z314, WCon{z315, WCon{z316, WCon{z317, WCon{z318, WCon{z319, WCon{z320, WCon{z321, WCon{z322, WCon{z323, WCon{z324, WCon{z325, WCon{z326, WCon{z327, WCon{z328, WCon{z329, WCon{z330, WCon{z331, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z40, WCon{z41, WCon{z42, WCon{z43, WCon{z44, WCon{z45, WCon{z46, WCon{z47, WCon{z48, WCon{z49, WCon{z410, WCon{z411, WCon{z412, WCon{z413, WCon{z414, WCon{z415, WCon{z416, WCon{z417, WCon{z418, WCon{z419, WCon{z420, WCon{z421, WCon{z422, WCon{z423, WCon{z424, WCon{z425, WCon{z426, WCon{z427, WCon{z428, WCon{z429, WCon{z430, WCon{z431, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z50, WCon{z51, WCon{z52, WCon{z53, WCon{z54, WCon{z55, WCon{z56, WCon{z57, WCon{z58, WCon{z59, WCon{z510, WCon{z511, WCon{z512, WCon{z513, WCon{z514, WCon{z515, WCon{z516, WCon{z517, WCon{z518, WCon{z519, WCon{z520, WCon{z521, WCon{z522, WCon{z523, WCon{z524, WCon{z525, WCon{z526, WCon{z527, WCon{z528, WCon{z529, WCon{z530, WCon{z531, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z60, WCon{z61, WCon{z62, WCon{z63, WCon{z64, WCon{z65, WCon{z66, WCon{z67, WCon{z68, WCon{z69, WCon{z610, WCon{z611, WCon{z612, WCon{z613, WCon{z614, WCon{z615, WCon{z616, WCon{z617, WCon{z618, WCon{z619, WCon{z620, WCon{z621, WCon{z622, WCon{z623, WCon{z624, WCon{z625, WCon{z626, WCon{z627, WCon{z628, WCon{z629, WCon{z630, WCon{z631, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z70, WCon{z71, WCon{z72, WCon{z73, WCon{z74, WCon{z75, WCon{z76, WCon{z77, WCon{z78, WCon{z79, WCon{z710, WCon{z711, WCon{z712, WCon{z713, WCon{z714, WCon{z715, WCon{z716, WCon{z717, WCon{z718, WCon{z719, WCon{z720, WCon{z721, WCon{z722, WCon{z723, WCon{z724, WCon{z725, WCon{z726, WCon{z727, WCon{z728, WCon{z729, WCon{z730, WCon{z731, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z80, WCon{z81, WCon{z82, WCon{z83, WCon{z84, WCon{z85, WCon{z86, WCon{z87, WCon{z88, WCon{z89, WCon{z810, WCon{z811, WCon{z812, WCon{z813, WCon{z814, WCon{z815, WCon{z816, WCon{z817, WCon{z818, WCon{z819, WCon{z820, WCon{z821, WCon{z822, WCon{z823, WCon{z824, WCon{z825, WCon{z826, WCon{z827, WCon{z828, WCon{z829, WCon{z830, WCon{z831, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z90, WCon{z91, WCon{z92, WCon{z93, WCon{z94, WCon{z95, WCon{z96, WCon{z97, WCon{z98, WCon{z99, WCon{z910, WCon{z911, WCon{z912, WCon{z913, WCon{z914, WCon{z915, WCon{z916, WCon{z917, WCon{z918, WCon{z919, WCon{z920, WCon{z921, WCon{z922, WCon{z923, WCon{z924, WCon{z925, WCon{z926, WCon{z927, WCon{z928, WCon{z929, WCon{z930, WCon{z931, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z100, WCon{z101, WCon{z102, WCon{z103, WCon{z104, WCon{z105, WCon{z106, WCon{z107, WCon{z108, WCon{z109, WCon{z1010, WCon{z1011, WCon{z1012, WCon{z1013, WCon{z1014, WCon{z1015, WCon{z1016, WCon{z1017, WCon{z1018, WCon{z1019, WCon{z1020, WCon{z1021, WCon{z1022, WCon{z1023, WCon{z1024, WCon{z1025, WCon{z1026, WCon{z1027, WCon{z1028, WCon{z1029, WCon{z1030, WCon{z1031, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z110, WCon{z111, WCon{z112, WCon{z113, WCon{z114, WCon{z115, WCon{z116, WCon{z117, WCon{z118, WCon{z119, WCon{z1110, WCon{z1111, WCon{z1112, WCon{z1113, WCon{z1114, WCon{z1115, WCon{z1116, WCon{z1117, WCon{z1118, WCon{z1119, WCon{z1120, WCon{z1121, WCon{z1122, WCon{z1123, WCon{z1124, WCon{z1125, WCon{z1126, WCon{z1127, WCon{z1128, WCon{z1129, WCon{z1130, WCon{z1131, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z120, WCon{z121, WCon{z122, WCon{z123, WCon{z124, WCon{z125, WCon{z126, WCon{z127, WCon{z128, WCon{z129, WCon{z1210, WCon{z1211, WCon{z1212, WCon{z1213, WCon{z1214, WCon{z1215, WCon{z1216, WCon{z1217, WCon{z1218, WCon{z1219, WCon{z1220, WCon{z1221, WCon{z1222, WCon{z1223, WCon{z1224, WCon{z1225, WCon{z1226, WCon{z1227, WCon{z1228, WCon{z1229, WCon{z1230, WCon{z1231, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z130, WCon{z131, WCon{z132, WCon{z133, WCon{z134, WCon{z135, WCon{z136, WCon{z137, WCon{z138, WCon{z139, WCon{z1310, WCon{z1311, WCon{z1312, WCon{z1313, WCon{z1314, WCon{z1315, WCon{z1316, WCon{z1317, WCon{z1318, WCon{z1319, WCon{z1320, WCon{z1321, WCon{z1322, WCon{z1323, WCon{z1324, WCon{z1325, WCon{z1326, WCon{z1327, WCon{z1328, WCon{z1329, WCon{z1330, WCon{z1331, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z140, WCon{z141, WCon{z142, WCon{z143, WCon{z144, WCon{z145, WCon{z146, WCon{z147, WCon{z148, WCon{z149, WCon{z1410, WCon{z1411, WCon{z1412, WCon{z1413, WCon{z1414, WCon{z1415, WCon{z1416, WCon{z1417, WCon{z1418, WCon{z1419, WCon{z1420, WCon{z1421, WCon{z1422, WCon{z1423, WCon{z1424, WCon{z1425, WCon{z1426, WCon{z1427, WCon{z1428, WCon{z1429, WCon{z1430, WCon{z1431, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z150, WCon{z151, WCon{z152, WCon{z153, WCon{z154, WCon{z155, WCon{z156, WCon{z157, WCon{z158, WCon{z159, WCon{z1510, WCon{z1511, WCon{z1512, WCon{z1513, WCon{z1514, WCon{z1515, WCon{z1516, WCon{z1517, WCon{z1518, WCon{z1519, WCon{z1520, WCon{z1521, WCon{z1522, WCon{z1523, WCon{z1524, WCon{z1525, WCon{z1526, WCon{z1527, WCon{z1528, WCon{z1529, WCon{z1530, WCon{z1531, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# the tail of a split has fewer than 16 bytes
def sp.tail_short(ys: List<&2, U32>) -> {Nat.is_lt(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          {==}
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              {==}
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  {==}
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      {==}
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          {==}
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              {==}
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  {==}
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      {==}
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          {==}
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              {==}
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  {==}
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      {==}
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          {==}
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              {==}
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  {==}
                                                                case Con{+y15, +t}:
                                                                  %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), M.cm.split.tail(M.cm.split(B.mask(t))), sp.cons_tail(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {Nat.is_lt(B.len(_), 16n) == True{} : Bool}
                                                                  sp.tail_short(t)

# the tail of a masked split is masked
def sp.tail_masked(ys: List<&2, U32>) -> {B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))) == M.cm.split.tail(M.cm.split(B.mask(ys))) : List<&2, U32>}:
  match ys:
    case Nil{}:
      li.mask_mask(Nil{})
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          li.mask_mask(Con{y0, Nil{}})
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              li.mask_mask(Con{y0, Con{y1, Nil{}}})
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  li.mask_mask(Con{y0, Con{y1, Con{y2, Nil{}}}})
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}})
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}})
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}})
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}})
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}})
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}})
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}})
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}})
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}})
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}})
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}})
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  li.mask_mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}})
                                                                case Con{+y15, +t}:
                                                                  %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), M.cm.split.tail(M.cm.split(B.mask(t))), sp.cons_tail(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {B.mask(_) == _ : List<&2, U32>}
                                                                  sp.tail_masked(t)

# a byte string of at least 16 bytes has a first block
def sp.nonempty(ys: List<&2, U32>) -> {Nat.is_le(16n, B.len(ys)) == True{} : Bool} -> {Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(ys)))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(ys))))} == M.cm.split.blocks(M.cm.split(B.mask(ys))) : List<&2, M.CmBlock>}:
  match ys:
    case Nil{}:
      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Nil{})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Nil{}))))} == M.cm.split.blocks(M.cm.split(B.mask(Nil{}))) : List<&2, M.CmBlock>}, h)
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Nil{}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Nil{}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Nil{}}))) : List<&2, M.CmBlock>}, h)
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Nil{}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Nil{}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Nil{}}}))) : List<&2, M.CmBlock>}, h)
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}}))) : List<&2, M.CmBlock>}, h)
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}))) : List<&2, M.CmBlock>}, h)
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}))) : List<&2, M.CmBlock>}, h)
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}))) : List<&2, M.CmBlock>}, h)
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                                case Con{+y15, +t}:
                                                                  h => %Equal.sym(List<&2, M.CmBlock>, M.cm.split.blocks(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), Con{M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split.blocks(M.cm.split(B.mask(t)))}, sp.cons_blocks(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {Con{sp.hd(_), sp.tl(_)} == _ : List<&2, M.CmBlock>}
                                                                    {==}

# fewer than 16 bytes are all tail
def sp.short_split(ys: List<&2, U32>) -> {Nat.is_lt(B.len(ys), 16n) == True{} : Bool} -> {M.cm.split(ys) == M.CmSplit{Nil{}, ys} : M.CmSplit}:
  match ys:
    case Nil{}:
      h => {==}
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => {==}
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => {==}
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => {==}
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => {==}
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => {==}
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => {==}
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => {==}
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => {==}
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => {==}
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => {==}
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => {==}
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => {==}
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => {==}
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => {==}
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => {==}
                                                                case Con{+y15, +t}:
                                                                  match t:
                                                                    case Nil{}:
                                                                      h => bo.absurd({M.cm.split(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Nil{}}}}}}}}}}}}}}}}}) == M.CmSplit{Nil{}, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Nil{}}}}}}}}}}}}}}}}}} : M.CmSplit}, h)
                                                                    case Con{+z, +zs}:
                                                                      h => bo.absurd({M.cm.split(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Con{z, zs}}}}}}}}}}}}}}}}}) == M.CmSplit{Nil{}, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Con{z, zs}}}}}}}}}}}}}}}}}} : M.CmSplit}, h)

# a block of exactly 16 bytes gives them back, masked
def sp.bb16(ys: List<&2, U32>) -> {Nat.is_eq(B.len(ys), 16n) == True{} : Bool} -> {M.cm.bytes_of(M.cm.block_of(ys)) == B.mask(ys) : List<&2, U32>}:
  match ys:
    case Nil{}:
      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Nil{})) == B.mask(Nil{}) : List<&2, U32>}, h)
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Nil{}})) == B.mask(Con{y0, Nil{}}) : List<&2, U32>}, h)
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Nil{}}})) == B.mask(Con{y0, Con{y1, Nil{}}}) : List<&2, U32>}, h)
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Nil{}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}}) : List<&2, U32>}, h)
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}) : List<&2, U32>}, h)
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}) : List<&2, U32>}, h)
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}) : List<&2, U32>}, h)
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}) : List<&2, U32>}, h)
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}) : List<&2, U32>}, h)
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}) : List<&2, U32>}, h)
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}) : List<&2, U32>}, h)
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                                case Con{+y15, +t}:
                                                                  match t:
                                                                    case Nil{}:
                                                                      h => sp.blk16g(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, Nil{})
                                                                    case Con{+z, +zs}:
                                                                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Con{z, zs}}}}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Con{z, zs}}}}}}}}}}}}}}}}}) : List<&2, U32>}, h)

# the block of a block's bytes is the block
def sp.block_bytes(b: M.CmBlock) -> {M.cm.block_of(M.cm.bytes_of(b)) == b : M.CmBlock}:
  match b:
    case M.CmBlock{U32{WCon{p0, WCon{p1, WCon{p2, WCon{p3, WCon{p4, WCon{p5, WCon{p6, WCon{p7, WCon{p8, WCon{p9, WCon{p10, WCon{p11, WCon{p12, WCon{p13, WCon{p14, WCon{p15, WCon{p16, WCon{p17, WCon{p18, WCon{p19, WCon{p20, WCon{p21, WCon{p22, WCon{p23, WCon{p24, WCon{p25, WCon{p26, WCon{p27, WCon{p28, WCon{p29, WCon{p30, WCon{p31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{q0, WCon{q1, WCon{q2, WCon{q3, WCon{q4, WCon{q5, WCon{q6, WCon{q7, WCon{q8, WCon{q9, WCon{q10, WCon{q11, WCon{q12, WCon{q13, WCon{q14, WCon{q15, WCon{q16, WCon{q17, WCon{q18, WCon{q19, WCon{q20, WCon{q21, WCon{q22, WCon{q23, WCon{q24, WCon{q25, WCon{q26, WCon{q27, WCon{q28, WCon{q29, WCon{q30, WCon{q31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{r0, WCon{r1, WCon{r2, WCon{r3, WCon{r4, WCon{r5, WCon{r6, WCon{r7, WCon{r8, WCon{r9, WCon{r10, WCon{r11, WCon{r12, WCon{r13, WCon{r14, WCon{r15, WCon{r16, WCon{r17, WCon{r18, WCon{r19, WCon{r20, WCon{r21, WCon{r22, WCon{r23, WCon{r24, WCon{r25, WCon{r26, WCon{r27, WCon{r28, WCon{r29, WCon{r30, WCon{r31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# Joining and splitting

def sp.split_join(bs: List<&2, M.CmBlock>) -> {M.cm.split(M.cm.join_onto(bs, Nil{})) == M.CmSplit{bs, Nil{}} : M.CmSplit}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(M.CmSplit, M.cm.split(M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{}))), M.cm.split.cons(b, M.cm.split(M.cm.join_onto(t, Nil{}))), sp.blk(b, M.cm.join_onto(t, Nil{}))) : {_ == M.CmSplit{Con{b, t}, Nil{}} : M.CmSplit}
      %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(t, Nil{})), M.CmSplit{t, Nil{}}, sp.split_join(t)) : {M.cm.split.cons(b, _) == M.CmSplit{Con{b, t}, Nil{}} : M.CmSplit}
      {==}

def sp.mask_join(bs: List<&2, M.CmBlock>) -> {B.mask(M.cm.join_onto(bs, Nil{})) == M.cm.join_onto(bs, Nil{}) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{}))), M.cm.bytes_onto(b, B.mask(M.cm.join_onto(t, Nil{}))), sp.mask_blk(b, M.cm.join_onto(t, Nil{}))) : {_ == M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{})) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(t, Nil{})), M.cm.join_onto(t, Nil{}), sp.mask_join(t)) : {M.cm.bytes_onto(b, _) == M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{})) : List<&2, U32>}
      {==}

# Every Octets is masked: to_list(o) = to_list(of_list(to_list(o))) = mask(to_list(o))
def oc.masked(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.mask(B.Octets.to_list(o)), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o))), Equal.cong(B.Octets, List<&2, U32>, x => B.Octets.to_list(x), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)))

def oc.len(+o: B.Octets, +n: Nat, h: {B.Octets.len(o) == n : Nat}) -> {B.len(B.Octets.to_list(o)) == n : Nat}:
  Equal.trans(Nat, B.len(B.Octets.to_list(o)), B.Octets.len(o), n, Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)), h)

def oc.mod(+o: B.Octets, h: {Nat.mod(B.Octets.len(o), 16n) == 0n : Nat}) -> {Nat.mod(B.len(B.Octets.to_list(o)), 16n) == 0n : Nat}:
  Equal.trans(Nat, Nat.mod(B.len(B.Octets.to_list(o)), 16n), Nat.mod(B.Octets.len(o), 16n), 0n, Equal.sym(Nat, Nat.mod(B.Octets.len(o), 16n), Nat.mod(B.len(B.Octets.to_list(o)), 16n), Equal.cong(Nat, Nat, n => Nat.mod(n, 16n), B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o))), h)

# a 16-byte IV is the block of its bytes
def cbcp.iv(+iv: B.Octets, h: {B.Octets.len(iv) == 16n : Nat}) -> {C.cbc.iv(iv) == Done{M.cm.block_of(B.Octets.to_list(iv))} : Result<&2, &2, M.CmError, M.CmBlock>}:
  %Equal.sym(Nat, B.len(B.Octets.to_list(iv)), 16n, oc.len(iv, 16n, h)) : {M.cm.need_block.pick(Nat.is_eq(_, 16n), B.Octets.to_list(iv), M.CmBadIvLength{B.len(B.Octets.to_list(iv))}) == Done{M.cm.block_of(B.Octets.to_list(iv))} : Result<&2, &2, M.CmError, M.CmBlock>}
  {==}


# The tail-recursive forms the modes run are the structural ones, for every
# input: each loop with an accumulator is its structural form reversed onto
# the accumulator, and reversing twice gives the order back. Then the byte
# layers built from them are the structural byte layers, and so are the
# public defs (Cbc.encrypt == Cbc.encrypt.ref, ...).

def tr.add_succ(+a: Nat, +n: Nat) -> {Nat.add(a, 1n+n) == 1n+Nat.add(a, n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(q, 1n+n), 1n+Nat.add(q, n), tr.add_succ(q, n))

def tr.add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(q, 0n), q, tr.add_zero(q))

def tr.rr(xs: List<&2, M.CmBlock>, acc: List<&2, M.CmBlock>, b: List<&2, M.CmBlock>) -> {M.cm.blocks.rev_onto(M.cm.blocks.rev_onto(xs, acc), b) == M.cm.blocks.rev_onto(acc, List.append(&2, M.CmBlock, xs, b)) : List<&2, M.CmBlock>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      tr.rr(t, Con{h, acc}, b)

def tr.append_eq(+xs: List<&2, M.CmBlock>, +ys: List<&2, M.CmBlock>) -> {List.append(&2, M.CmBlock, xs, ys) == M.cm.blocks.append(xs, ys) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, M.cm.blocks.append(xs, ys), List.append(&2, M.CmBlock, xs, ys), tr.rr(xs, Nil{}, ys))

def tr.len_go(+bs: List<&2, M.CmBlock>, +n: Nat) -> {M.cm.blocks.len.go(bs, n) == Nat.add(List.length(&2, M.CmBlock, bs), n) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, M.cm.blocks.len.go(t, 1n+n), Nat.add(List.length(&2, M.CmBlock, t), 1n+n), 1n+Nat.add(List.length(&2, M.CmBlock, t), n), tr.len_go(t, 1n+n), tr.add_succ(List.length(&2, M.CmBlock, t), n))

def tr.len_eq(+bs: List<&2, M.CmBlock>) -> {List.length(&2, M.CmBlock, bs) == M.cm.blocks.len(bs) : Nat}:
  Equal.sym(Nat, M.cm.blocks.len(bs), List.length(&2, M.CmBlock, bs), Equal.trans(Nat, M.cm.blocks.len.go(bs, 0n), Nat.add(List.length(&2, M.CmBlock, bs), 0n), List.length(&2, M.CmBlock, bs), tr.len_go(bs, 0n), tr.add_zero(List.length(&2, M.CmBlock, bs))))

# Splitting: the blocks so far, reversed in acc, go in front of the
# structural split's blocks

def tr.split_fin(acc: List<&2, M.CmBlock>, s: M.CmSplit) -> M.CmSplit:
  match s:
    case M.CmSplit{bs, t}:
      M.CmSplit{M.cm.blocks.rev_onto(acc, bs), t}

def tr.split_fin_cons(+b: M.CmBlock, +acc: List<&2, M.CmBlock>, +s: M.CmSplit) -> {tr.split_fin(Con{b, acc}, s) == tr.split_fin(acc, M.cm.split.cons(b, s)) : M.CmSplit}:
  match s:
    case M.CmSplit{bs, t}:
      {==}

def tr.split_fin_nil(+s: M.CmSplit) -> {tr.split_fin(Nil{}, s) == s : M.CmSplit}:
  match s:
    case M.CmSplit{bs, t}:
      {==}

def tr.split_go(+xs: List<&2, U32>, +acc: List<&2, M.CmBlock>) -> {M.cm.split.go(xs, acc) == tr.split_fin(acc, M.cm.split(xs)) : M.CmSplit}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          {==}
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              {==}
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  {==}
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      {==}
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          {==}
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              {==}
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  {==}
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      {==}
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          {==}
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              {==}
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  {==}
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      {==}
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          {==}
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              {==}
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  {==}
                                                                case Con{+y15, +t}:
                                                                  Equal.trans(M.CmSplit, M.cm.split.go(t, Con{M.cm.block16(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15), acc}), tr.split_fin(Con{M.cm.block16(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15), acc}, M.cm.split(t)), tr.split_fin(acc, M.cm.split.cons(M.cm.block16(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15), M.cm.split(t))), tr.split_go(t, Con{M.cm.block16(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15), acc}), tr.split_fin_cons(M.cm.block16(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15), acc, M.cm.split(t)))

def tr.split_eq(+xs: List<&2, U32>) -> {M.cm.split(xs) == M.cm.split.fast(xs) : M.CmSplit}:
  Equal.sym(M.CmSplit, M.cm.split.fast(xs), M.cm.split(xs), Equal.trans(M.CmSplit, M.cm.split.go(xs, Nil{}), tr.split_fin(Nil{}, M.cm.split(xs)), M.cm.split(xs), tr.split_go(xs, Nil{}), tr.split_fin_nil(M.cm.split(xs))))

# Joining

def tr.join_go(xs: List<&2, M.CmBlock>, rs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.join.go(M.cm.blocks.rev_onto(xs, rs), rest) == M.cm.join.go(rs, M.cm.join_onto(xs, rest)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      tr.join_go(t, Con{x, rs}, rest)

def tr.join_eq(+bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.join_onto(bs, rest) == M.cm.join_onto.fast(bs, rest) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, M.cm.join_onto.fast(bs, rest), M.cm.join_onto(bs, rest), tr.join_go(bs, Nil{}, rest))

# The modes on blocks

def tr.cbc_enc_go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {C.cbc.enc.go(~K, ~enc, k, bs, iv, acc) == M.cm.blocks.rev_onto(acc, C.cbc.enc(~K, ~enc, k, bs, iv)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      tr.cbc_enc_go(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p)), Con{enc(k, M.CmBlock.xor(iv, p)), acc})

def tr.cbc_enc_eq(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> {C.cbc.enc(~K, ~enc, k, bs, iv) == C.cbc.enc.fast(~K, ~enc, k, bs, iv) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, C.cbc.enc.fast(~K, ~enc, k, bs, iv), C.cbc.enc(~K, ~enc, k, bs, iv), tr.cbc_enc_go(~K, ~enc, k, bs, iv, Nil{}))

def tr.cbc_dec_go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {C.cbc.dec.go(~K, ~dec, k, bs, iv, acc) == M.cm.blocks.rev_onto(acc, C.cbc.dec(~K, ~dec, k, bs, iv)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      tr.cbc_dec_go(~K, ~dec, k, t, c, Con{M.CmBlock.xor(iv, dec(k, c)), acc})

def tr.cbc_dec_eq(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> {C.cbc.dec(~K, ~dec, k, bs, iv) == C.cbc.dec.fast(~K, ~dec, k, bs, iv) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, C.cbc.dec.fast(~K, ~dec, k, bs, iv), C.cbc.dec(~K, ~dec, k, bs, iv), tr.cbc_dec_go(~K, ~dec, k, bs, iv, Nil{}))

def tr.xts_enc_go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {T.xts.enc.go(~K, ~enc, k, bs, t, acc) == M.cm.blocks.rev_onto(acc, T.xts.enc(~K, ~enc, k, bs, t)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      tr.xts_enc_go(~K, ~enc, k, rest, T.Xts.mul_alpha(t), Con{T.xts.benc(~K, ~enc, k, p, t), acc})

def tr.xts_enc_eq(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {T.xts.enc(~K, ~enc, k, bs, t) == T.xts.enc.fast(~K, ~enc, k, bs, t) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, T.xts.enc.fast(~K, ~enc, k, bs, t), T.xts.enc(~K, ~enc, k, bs, t), tr.xts_enc_go(~K, ~enc, k, bs, t, Nil{}))

def tr.xts_dec_go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {T.xts.dec.go(~K, ~dec, k, bs, t, acc) == M.cm.blocks.rev_onto(acc, T.xts.dec(~K, ~dec, k, bs, t)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      tr.xts_dec_go(~K, ~dec, k, rest, T.Xts.mul_alpha(t), Con{T.xts.bdec(~K, ~dec, k, c, t), acc})

def tr.xts_dec_eq(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {T.xts.dec(~K, ~dec, k, bs, t) == T.xts.dec.fast(~K, ~dec, k, bs, t) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, T.xts.dec.fast(~K, ~dec, k, bs, t), T.xts.dec(~K, ~dec, k, bs, t), tr.xts_dec_go(~K, ~dec, k, bs, t, Nil{}))

def tr.init_go(rest: List<&2, M.CmBlock>, +p: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {T.xts.init.go(rest, p, acc) == M.cm.blocks.rev_onto(acc, T.xts.init(rest, p)) : List<&2, M.CmBlock>}:
  match rest:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      tr.init_go(r, q, Con{p, acc})

def tr.init_eq(+rest: List<&2, M.CmBlock>, +p: M.CmBlock) -> {T.xts.init(rest, p) == T.xts.init.fast(rest, p) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, T.xts.init.fast(rest, p), T.xts.init(rest, p), tr.init_go(rest, p, Nil{}))

# The byte layers

def tr.cbc_e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +v: M.CmBlock, s: M.CmSplit, +n: Nat) -> {C.cbc.e2(~K, ~enc, k, v, s, n) == C.cbc.e2.fast(~K, ~enc, k, v, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{+bs, tail}:
      match tail:
        case Nil{}:
          %tr.cbc_enc_eq(~K, ~enc, k, bs, v) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, bs, v), Nil{}))} == Done{B.Octets.of_list(M.cm.join_onto.fast(_, Nil{}))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.join_eq(C.cbc.enc(~K, ~enc, k, bs, v), Nil{}) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, bs, v), Nil{}))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}
        case Con{h, t}:
          {==}

def tr.cbc_e1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {C.cbc.e1(~K, ~enc, k, r, xs) == C.cbc.e1.fast(~K, ~enc, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      %tr.split_eq(xs) : {C.cbc.e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.e2.fast(~K, ~enc, k, v, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {C.cbc.e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.e2.fast(~K, ~enc, k, v, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.cbc_e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs))

def tr.cbc_d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +v: M.CmBlock, s: M.CmSplit, +n: Nat) -> {C.cbc.d2(~K, ~dec, k, v, s, n) == C.cbc.d2.fast(~K, ~dec, k, v, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{+bs, tail}:
      match tail:
        case Nil{}:
          %tr.cbc_dec_eq(~K, ~dec, k, bs, v) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.dec(~K, ~dec, k, bs, v), Nil{}))} == Done{B.Octets.of_list(M.cm.join_onto.fast(_, Nil{}))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.join_eq(C.cbc.dec(~K, ~dec, k, bs, v), Nil{}) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.dec(~K, ~dec, k, bs, v), Nil{}))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}
        case Con{h, t}:
          {==}

def tr.cbc_d1(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {C.cbc.d1(~K, ~dec, k, r, xs) == C.cbc.d1.fast(~K, ~dec, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      %tr.split_eq(xs) : {C.cbc.d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.d2.fast(~K, ~dec, k, v, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {C.cbc.d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.d2.fast(~K, ~dec, k, v, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.cbc_d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs))

def tr.cbc_encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +m: B.Octets) -> {C.Cbc.encrypt.ref(~K, ~enc, k, iv, m) == C.Cbc.encrypt(~K, ~enc, k, iv, m) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.cbc_e1(~K, ~enc, k, C.cbc.iv(iv), B.Octets.to_list(m))

def tr.cbc_decrypt(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +c: B.Octets) -> {C.Cbc.decrypt.ref(~K, ~dec, k, iv, c) == C.Cbc.decrypt(~K, ~dec, k, iv, c) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.cbc_d1(~K, ~dec, k, C.cbc.iv(iv), B.Octets.to_list(c))

def tr.xts_eout(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> {T.xts.eout(~K, ~enc, k, t, init, last, tail) == T.xts.eout.fast(~K, ~enc, k, t, init, last, tail) : List<&2, U32>}:
  %tr.len_eq(init) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == M.cm.join_onto.fast(M.cm.blocks.append(T.xts.enc.fast(~K, ~enc, k, init, t), Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(_, t)), Nil{}}), T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(_, t))) : List<&2, U32>}
  %tr.xts_enc_eq(~K, ~enc, k, init, t) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == M.cm.join_onto.fast(M.cm.blocks.append(_, Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t)), Nil{}}), T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : List<&2, U32>}
  %tr.append_eq(T.xts.enc(~K, ~enc, k, init, t), Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t)), Nil{}}) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == M.cm.join_onto.fast(_, T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : List<&2, U32>}
  %tr.join_eq(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k, init, t), Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t)), Nil{}}), T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == _ : List<&2, U32>}
  {==}

def tr.xts_dout(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> {T.xts.dout(~K, ~dec, k, t, init, last, tail) == T.xts.dout.fast(~K, ~dec, k, t, init, last, tail) : List<&2, U32>}:
  %tr.len_eq(init) : {T.xts.dout(~K, ~dec, k, t, init, last, tail) == M.cm.join_onto.fast(T.xts.dec.fast(~K, ~dec, k, init, t), T.xts.dsteal(~K, ~dec, k, last, tail, T.xts.alpha_n(_, t))) : List<&2, U32>}
  %tr.xts_dec_eq(~K, ~dec, k, init, t) : {T.xts.dout(~K, ~dec, k, t, init, last, tail) == M.cm.join_onto.fast(_, T.xts.dsteal(~K, ~dec, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : List<&2, U32>}
  %tr.join_eq(T.xts.dec(~K, ~dec, k, init, t), T.xts.dsteal(~K, ~dec, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : {T.xts.dout(~K, ~dec, k, t, init, last, tail) == _ : List<&2, U32>}
  {==}

def tr.xts_e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> {T.xts.e2(~K, ~enc, k, t, s, n) == T.xts.e2.fast(~K, ~enc, k, t, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{bs, +tail}:
      match bs:
        case Nil{}:
          {==}
        case Con{+p, +rest}:
          %tr.init_eq(rest, p) : {Done{B.Octets.of_list(T.xts.eout(~K, ~enc, k, t, T.xts.init(rest, p), T.xts.last(rest, p), tail))} == Done{B.Octets.of_list(T.xts.eout.fast(~K, ~enc, k, t, _, T.xts.last(rest, p), tail))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.xts_eout(~K, ~enc, k, t, T.xts.init(rest, p), T.xts.last(rest, p), tail) : {Done{B.Octets.of_list(T.xts.eout(~K, ~enc, k, t, T.xts.init(rest, p), T.xts.last(rest, p), tail))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}

def tr.xts_d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> {T.xts.d2(~K, ~dec, k, t, s, n) == T.xts.d2.fast(~K, ~dec, k, t, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{bs, +tail}:
      match bs:
        case Nil{}:
          {==}
        case Con{+c, +rest}:
          %tr.init_eq(rest, c) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, T.xts.init(rest, c), T.xts.last(rest, c), tail))} == Done{B.Octets.of_list(T.xts.dout.fast(~K, ~dec, k, t, _, T.xts.last(rest, c), tail))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.xts_dout(~K, ~dec, k, t, T.xts.init(rest, c), T.xts.last(rest, c), tail) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, T.xts.init(rest, c), T.xts.last(rest, c), tail))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}

def tr.xts_e1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {T.xts.e1(~K, ~enc, k, r, xs) == T.xts.e1.fast(~K, ~enc, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+t}:
      %tr.split_eq(xs) : {T.xts.e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs)) == T.xts.e2.fast(~K, ~enc, k, t, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {T.xts.e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs)) == T.xts.e2.fast(~K, ~enc, k, t, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.xts_e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs))

def tr.xts_d1(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {T.xts.d1(~K, ~dec, k, r, xs) == T.xts.d1.fast(~K, ~dec, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+t}:
      %tr.split_eq(xs) : {T.xts.d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs)) == T.xts.d2.fast(~K, ~dec, k, t, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {T.xts.d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs)) == T.xts.d2.fast(~K, ~dec, k, t, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.xts_d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs))

def tr.xts_encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, +i: B.Octets, +p: B.Octets) -> {T.Xts.encrypt.ref(~K, ~enc, k1, k2, i, p) == T.Xts.encrypt(~K, ~enc, k1, k2, i, p) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.xts_e1(~K, ~enc, k1, T.xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(p))

def tr.xts_decrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, +i: B.Octets, +c: B.Octets) -> {T.Xts.decrypt.ref(~K, ~enc, ~dec, k1, k2, i, c) == T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.xts_d1(~K, ~dec, k1, T.xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(c))

# a bind whose continuations agree on every value agrees
def tr.bind_cong(r: Result<&2, &2, M.CmError, B.Octets>, f: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, g: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, h: @c: B.Octets -> {f(c) == g(c) : Result<&2, &2, M.CmError, B.Octets>}) -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, f) == Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, g) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{c}:
      h(c)


# CCM: the tail-recursive forms are the structural ones, piece by piece

def tr.pad(+xs: List<&2, U32>) -> {CC.ccm.pad(xs) == CC.ccm.pad.fast(xs) : List<&2, U32>}:
  %BL.len_fast(xs) : {CC.ccm.pad(xs) == B.append.fast(xs, B.zeros(Nat.mod(Nat.sub(16n, Nat.mod(_, 16n)), 16n))) : List<&2, U32>}
  %BL.append_fast(xs, B.zeros(Nat.mod(Nat.sub(16n, Nat.mod(B.len(xs), 16n)), 16n))) : {CC.ccm.pad(xs) == _ : List<&2, U32>}
  {==}

def tr.aad(empty: Bool, +a: List<&2, U32>) -> {CC.ccm.aad.pick(empty, a) == CC.ccm.aad.pick.fast(empty, a) : List<&2, U32>}:
  match empty:
    case True{}:
      {==}
    case False{}:
      %BL.len_fast(a) : {CC.ccm.aad.pick(False{}, a) == CC.ccm.pad.fast(B.append(CC.ccm.alen.pick(U32.is_lt(U32.from_nat(_), 65280), U32.from_nat(_)), a)) : List<&2, U32>}
      %tr.pad(B.append(CC.ccm.alen.pick(U32.is_lt(U32.from_nat(B.len(a)), 65280), U32.from_nat(B.len(a))), a)) : {CC.ccm.aad.pick(False{}, a) == _ : List<&2, U32>}
      {==}

def tr.mac(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nonce: List<&2, U32>, +a: List<&2, U32>, +p: List<&2, U32>) -> {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.mac.fast(~K, ~enc, k, m, l, nonce, a, p) : M.CmBlock}:
  %BL.len_fast(a) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(_, 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len.fast(p))))}, B.append.fast(CC.ccm.aad.pick.fast(Nat.is_eq(_, 0n), a), CC.ccm.pad.fast(p))))), M.CmBlock.zero()) : M.CmBlock}
  %BL.len_fast(p) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(_)))}, B.append.fast(CC.ccm.aad.pick.fast(Nat.is_eq(B.len(a), 0n), a), CC.ccm.pad.fast(p))))), M.CmBlock.zero()) : M.CmBlock}
  %tr.pad(p) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, B.append.fast(CC.ccm.aad.pick.fast(Nat.is_eq(B.len(a), 0n), a), _)))), M.CmBlock.zero()) : M.CmBlock}
  %tr.aad(Nat.is_eq(B.len(a), 0n), a) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, B.append.fast(_, CC.ccm.pad(p))))), M.CmBlock.zero()) : M.CmBlock}
  %BL.append_fast(CC.ccm.aad.pick(Nat.is_eq(B.len(a), 0n), a), CC.ccm.pad(p)) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, _))), M.CmBlock.zero()) : M.CmBlock}
  %tr.split_eq(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, B.append(CC.ccm.aad.pick(Nat.is_eq(B.len(a), 0n), a), CC.ccm.pad(p)))) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(_), M.CmBlock.zero()) : M.CmBlock}
  {==}

def tr.tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nonce: List<&2, U32>, +a: List<&2, U32>, +p: List<&2, U32>) -> {CC.ccm.tag(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.tag.fast(~K, ~enc, k, m, l, nonce, a, p) : List<&2, U32>}:
  %tr.mac(~K, ~enc, k, m, l, nonce, a, p) : {CC.ccm.tag(~K, ~enc, k, m, l, nonce, a, p) == B.take(m, M.cm.bytes_of(_)) : List<&2, U32>}
  {==}

def tr.ctrb_go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32, +acc: List<&2, M.CmBlock>) -> {CC.ccm.ctrb.go(~K, ~enc, k, bs, a0, i, acc) == M.cm.blocks.rev_onto(acc, CC.ccm.ctrb(~K, ~enc, k, bs, a0, i)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      tr.ctrb_go(~K, ~enc, k, rest, a0, U32.add(i, 1), Con{M.CmBlock.xor(b, enc(k, CC.ccm.ai(a0, i))), acc})

def tr.ctrb_eq(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> {CC.ccm.ctrb(~K, ~enc, k, bs, a0, i) == CC.ccm.ctrb.fast(~K, ~enc, k, bs, a0, i) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, CC.ccm.ctrb.fast(~K, ~enc, k, bs, a0, i), CC.ccm.ctrb(~K, ~enc, k, bs, a0, i), tr.ctrb_go(~K, ~enc, k, bs, a0, i, Nil{}))

def tr.xcrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, s: M.CmSplit) -> {CC.ccm.xcrypt(~K, ~enc, k, a0, s) == CC.ccm.xcrypt.fast(~K, ~enc, k, a0, s) : List<&2, U32>}:
  match s:
    case M.CmSplit{+bs, +tail}:
      %tr.len_eq(bs) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.CmSplit{bs, tail}) == M.cm.join_onto.fast(CC.ccm.ctrb.fast(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(_))))))) : List<&2, U32>}
      %tr.ctrb_eq(~K, ~enc, k, bs, a0, 1) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.CmSplit{bs, tail}) == M.cm.join_onto.fast(_, M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs)))))))) : List<&2, U32>}
      %tr.join_eq(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs)))))))) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.CmSplit{bs, tail}) == _ : List<&2, U32>}
      {==}

def tr.ebody(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == CC.ccm.ebody.fast(~K, ~enc, k, m, nv, av, pv) : List<&2, U32>}:
  %tr.split_eq(pv) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == B.append.fast(CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), _), M.cm.xor_bytes(CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %tr.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == B.append.fast(_, M.cm.xor_bytes(CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %tr.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == B.append.fast(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(_, M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %BL.append_fast(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == _ : List<&2, U32>}
  {==}

def tr.e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, r: Result<&2, &2, M.CmError, Unit>) -> {CC.ccm.e2(~K, ~enc, k, m, nv, av, pv, r) == CC.ccm.e2.fast(~K, ~enc, k, m, nv, av, pv, r) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      %tr.ebody(~K, ~enc, k, m, nv, av, pv) : {Done{B.Octets.of_list(CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
      {==}

def tr.ccm_encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nonce: B.Octets, +aad: B.Octets, +p: B.Octets) -> {CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p) == CC.Ccm.encrypt(~K, ~enc, k, m, nonce, aad, p) : Result<&2, &2, M.CmError, B.Octets>}:
  %BL.len_fast(B.Octets.to_list(p)) : {CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p) == CC.ccm.e2.fast(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), _)) : Result<&2, &2, M.CmError, B.Octets>}
  tr.e2(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))))

def tr.dbody(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>) -> {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.dbody.fast(~K, ~enc, k, m, nv, av, cv) : Result<&2, &2, M.CmError, B.Octets>}:
  %BL.len_fast(cv) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(_, m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(B.take.fast(Nat.sub(_, m), cv))))), CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(B.take.fast(Nat.sub(_, m), cv)))) : Result<&2, &2, M.CmError, B.Octets>}
  %BL.take_fast(Nat.sub(B.len(cv), m), cv) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(_)))), CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(_))) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.split_eq(B.take(Nat.sub(B.len(cv), m), cv)) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), _))), CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), _)) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(B.take(Nat.sub(B.len(cv), m), cv))) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, _)), _) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(B.take(Nat.sub(B.len(cv), m), cv)))) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), _), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(B.take(Nat.sub(B.len(cv), m), cv)))) : Result<&2, &2, M.CmError, B.Octets>}
  {==}

def tr.d3(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>, r: Result<&2, &2, M.CmError, Unit>) -> {CC.ccm.d3(~K, ~enc, k, m, nv, av, cv, r) == CC.ccm.d3.fast(~K, ~enc, k, m, nv, av, cv, r) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      tr.dbody(~K, ~enc, k, m, nv, av, cv)

def tr.d2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ok: Bool, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>) -> {CC.ccm.d2(~K, ~enc, ok, k, m, nv, av, cv) == CC.ccm.d2.fast(~K, ~enc, ok, k, m, nv, av, cv) : Result<&2, &2, M.CmError, B.Octets>}:
  match ok:
    case False{}:
      %BL.len_fast(cv) : {CC.ccm.d2(~K, ~enc, False{}, k, m, nv, av, cv) == Fail{M.CmTooShort{_}} : Result<&2, &2, M.CmError, B.Octets>}
      {==}
    case True{}:
      %BL.len_fast(cv) : {CC.ccm.d2(~K, ~enc, True{}, k, m, nv, av, cv) == CC.ccm.d3.fast(~K, ~enc, k, m, nv, av, cv, CC.ccm.checks(m, B.len(nv), Nat.sub(_, m))) : Result<&2, &2, M.CmError, B.Octets>}
      tr.d3(~K, ~enc, k, m, nv, av, cv, CC.ccm.checks(m, B.len(nv), Nat.sub(B.len(cv), m)))

def tr.ccm_decrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nonce: B.Octets, +aad: B.Octets, +c: B.Octets) -> {CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c) == CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c) : Result<&2, &2, M.CmError, B.Octets>}:
  %BL.len_fast(B.Octets.to_list(c)) : {CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c) == CC.ccm.d2.fast(~K, ~enc, Nat.is_le(m, _), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(c)) : Result<&2, &2, M.CmError, B.Octets>}
  tr.d2(~K, ~enc, Nat.is_le(m, B.len(B.Octets.to_list(c))), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(c))

# The round trips' hypothesis: the law's inv at the list of blocks the mode
# gives the cipher, an equation (so copyable) that the inductions below take
# apart a block at a time

def cmp.head(d: M.CmBlock, xs: List<&2, M.CmBlock>) -> M.CmBlock:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      h

def cmp.tail(xs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def li.con_hd(+a: M.CmBlock, +s: List<&2, M.CmBlock>, +b: M.CmBlock, +t: List<&2, M.CmBlock>, +e: {Con{a, s} == Con{b, t} : List<&2, M.CmBlock>}) -> {a == b : M.CmBlock}:
  %e : {a == cmp.head(b, _) : M.CmBlock}
  {==}

def li.con_tl(+a: M.CmBlock, +s: List<&2, M.CmBlock>, +b: M.CmBlock, +t: List<&2, M.CmBlock>, +e: {Con{a, s} == Con{b, t} : List<&2, M.CmBlock>}) -> {s == t : List<&2, M.CmBlock>}:
  %e : {s == cmp.tail(_) : List<&2, M.CmBlock>}
  {==}

# the first block's round trip, and the rest's
def cmp.hd(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +x: M.CmBlock, +xs: List<&2, M.CmBlock>, +h: {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, Con{x, xs}) == Con{x, xs} : List<&2, M.CmBlock>}) -> {dec(k, enc(k, x)) == x : M.CmBlock}:
  li.con_hd(dec(k, enc(k, x)), M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs), x, xs, h)

def cmp.tl(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +x: M.CmBlock, +xs: List<&2, M.CmBlock>, +h: {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, Con{x, xs}) == Con{x, xs} : List<&2, M.CmBlock>}) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}:
  li.con_tl(dec(k, enc(k, x)), M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs), x, xs, h)

# the round trip of a ++ b gives a's, and b's
def cmp.app_l(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, a: List<&2, M.CmBlock>, +b: List<&2, M.CmBlock>) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, List.append(&2, M.CmBlock, a, b)) == List.append(&2, M.CmBlock, a, b) : List<&2, M.CmBlock>} -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, a) == a : List<&2, M.CmBlock>}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      +h => %Equal.sym(M.CmBlock, dec(k, enc(k, x)), x, cmp.hd(~K, ~enc, ~dec, k, x, List.append(&2, M.CmBlock, r, b), h)) : {Con{_, M.CmBlock.dec_enc(~K, ~enc, ~dec, k, r)} == Con{x, r} : List<&2, M.CmBlock>}
        %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~K, ~enc, ~dec, k, r), r, cmp.app_l(~K, ~enc, ~dec, k, r, b)(cmp.tl(~K, ~enc, ~dec, k, x, List.append(&2, M.CmBlock, r, b), h))) : {Con{x, _} == Con{x, r} : List<&2, M.CmBlock>}
        {==}

def cmp.app_r(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, a: List<&2, M.CmBlock>, +b: List<&2, M.CmBlock>) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, List.append(&2, M.CmBlock, a, b)) == List.append(&2, M.CmBlock, a, b) : List<&2, M.CmBlock>} -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, b) == b : List<&2, M.CmBlock>}:
  match a:
    case Nil{}:
      h => h
    case Con{+x, +r}:
      h => cmp.app_r(~K, ~enc, ~dec, k, r, b)(cmp.tl(~K, ~enc, ~dec, k, x, List.append(&2, M.CmBlock, r, b), h))

# the blocks CBC encryption gives the cipher: each plaintext block XOR the
# block before it (the IV first)
def cbcp.ins(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      Con{M.CmBlock.xor(iv, p), cbcp.ins(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p)))}

# the blocks XTS gives the cipher under k1: each block XOR its tweak
def xtsp.ins(bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      Con{M.CmBlock.xor(p, t), xtsp.ins(rest, T.Xts.mul_alpha(t))}

# and ciphertext stealing's: the last whole block XOR its tweak, then (with a
# tail) the block the tail steals into XOR the next tweak
def xtsp.sins(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  match tl:
    case Nil{}:
      Con{M.CmBlock.xor(p, t), Nil{}}
    case Con{+h, +r}:
      Con{M.CmBlock.xor(p, t), Con{M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}}}

# CBC on blocks

def cbcp.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, cbcp.ins(~K, ~enc, k, bs, iv)) == cbcp.ins(~K, ~enc, k, bs, iv) : List<&2, M.CmBlock>} -> {C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, bs, iv), iv) == bs : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+p, +t}:
      +h => %Equal.sym(M.CmBlock, dec(k, enc(k, M.CmBlock.xor(iv, p))), M.CmBlock.xor(iv, p), cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(iv, p), cbcp.ins(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), h)) : {Con{M.CmBlock.xor(iv, _), C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), enc(k, M.CmBlock.xor(iv, p)))} == Con{p, t} : List<&2, M.CmBlock>}
        %bx.block(iv, p) : {Con{M.CmBlock.xor(iv, M.CmBlock.xor(iv, p)), C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), enc(k, M.CmBlock.xor(iv, p)))} == Con{_, t} : List<&2, M.CmBlock>}
        %cbcp.go(~K, ~enc, ~dec, k, t, enc(k, M.CmBlock.xor(iv, p)))(cmp.tl(~K, ~enc, ~dec, k, M.CmBlock.xor(iv, p), cbcp.ins(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), h)) : {Con{M.CmBlock.xor(iv, M.CmBlock.xor(iv, p)), C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), enc(k, M.CmBlock.xor(iv, p)))} == Con{M.CmBlock.xor(iv, M.CmBlock.xor(iv, p)), _} : List<&2, M.CmBlock>}
        {==}

def Laws.cbc_blocks_round_trip(K, enc, dec, k, inv, iv, bs):
  +v = iv
  +b = bs
  # the tail-recursive forms are the structural ones
  %tr.cbc_enc_eq(~K, ~enc, k, b, v) : {C.cbc.dec.fast(~K, ~dec, k, _, iv) == bs : List<&2, M.CmBlock>}
  %tr.cbc_dec_eq(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, b, v), v) : {_ == bs : List<&2, M.CmBlock>}
  cbcp.go(~K, ~enc, ~dec, k, b, v)(inv(cbcp.ins(~K, ~enc, k, b, v)))

def Laws.cbc_round_trip(K, enc, dec, k, inv, iv, m, hi, hm):
  +et = sp.mod_tail(B.Octets.to_list(m))(oc.mod(m, hm))
  # the public defs are the structural ones
  %tr.cbc_encrypt(~K, ~enc, k, iv, m) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, c => C.Cbc.decrypt(~K, ~dec, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %tr.bind_cong(C.Cbc.encrypt.ref(~K, ~enc, k, iv, m), c => C.Cbc.decrypt.ref(~K, ~dec, k, iv, c), c => C.Cbc.decrypt(~K, ~dec, k, iv, c), c => tr.cbc_decrypt(~K, ~dec, k, iv, c)) : {_ == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the IV is a block
  %Equal.sym(Result<&2, &2, M.CmError, M.CmBlock>, C.cbc.iv(iv), Done{M.cm.block_of(B.Octets.to_list(iv))}, cbcp.iv(iv, hi)) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e1(~K, ~enc, k, _, B.Octets.to_list(m)), c => C.cbc.d1(~K, ~dec, k, _, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the message is masked
  %oc.masked(m) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e2(~K, ~enc, k, M.cm.block_of(B.Octets.to_list(iv)), M.cm.split(_), B.len(B.Octets.to_list(m))), c => C.cbc.d1(~K, ~dec, k, Done{M.cm.block_of(B.Octets.to_list(iv))}, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # its split is its blocks and tail
  %sp.eta(M.cm.split(B.mask(B.Octets.to_list(m)))) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e2(~K, ~enc, k, M.cm.block_of(B.Octets.to_list(iv)), _, B.len(B.Octets.to_list(m))), c => C.cbc.d1(~K, ~dec, k, Done{M.cm.block_of(B.Octets.to_list(iv))}, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # whole blocks leave no tail, so encryption succeeds
  %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(m)))), Nil{}, et) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e2(~K, ~enc, k, M.cm.block_of(B.Octets.to_list(iv)), M.CmSplit{M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), _}, B.len(B.Octets.to_list(m))), c => C.cbc.d1(~K, ~dec, k, Done{M.cm.block_of(B.Octets.to_list(iv))}, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # decryption reads the ciphertext's bytes back, masked
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))), B.mask(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{})), BL.octets_to_of(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))) : {C.cbc.d2(~K, ~dec, k, M.cm.block_of(B.Octets.to_list(iv)), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # which they already are
  %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{})), M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}), sp.mask_join(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))))) : {C.cbc.d2(~K, ~dec, k, M.cm.block_of(B.Octets.to_list(iv)), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # and they split into the ciphertext blocks
  %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{})), M.CmSplit{C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}}, sp.split_join(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))))) : {C.cbc.d2(~K, ~dec, k, M.cm.block_of(B.Octets.to_list(iv)), _, B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # CBC on blocks
  %Equal.sym(List<&2, M.CmBlock>, C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), M.cm.block_of(B.Octets.to_list(iv))), M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), cbcp.go(~K, ~enc, ~dec, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv)))(inv(cbcp.ins(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv)))))) : {Done{B.Octets.of_list(M.cm.join_onto(_, Nil{}))} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the plaintext blocks and the empty tail
  %et : {Done{B.Octets.of_list(M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), _))} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # join back to the message
  %Equal.sym(List<&2, U32>, M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(m))))), B.mask(B.Octets.to_list(m)), sp.join_split(B.Octets.to_list(m))) : {Done{B.Octets.of_list(_)} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, U32>, B.mask(B.Octets.to_list(m)), B.Octets.to_list(m), oc.masked(m)) : {Done{B.Octets.of_list(_)} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(m)), m, BL.octets_of_to(m)) : {Done{_} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  {==}

# XOR, cancelling on the right: xor(xor(a, b), b) == a

def bx.rbool(a: Bool, b: Bool) -> {Bool.xor(Bool.xor(a, b), b) == a : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def bx.rword(n: Nat, a: Word(n), b: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %bx.rbool(ah, bh) : {WCon{Bool.xor(Bool.xor(ah, bh), bh), Word.xor(p, Word.xor(p, at, bt), bt)} == WCon{_, at} : Word(1n+p)}
          %bx.rword(p, at, bt) : {WCon{Bool.xor(Bool.xor(ah, bh), bh), Word.xor(p, Word.xor(p, at, bt), bt)} == WCon{Bool.xor(Bool.xor(ah, bh), bh), _} : Word(1n+p)}
          {==}

def bx.ru32(a: U32, b: U32) -> {U32.xor(U32.xor(a, b), b) == a : U32}:
  match a b:
    case U32{x} U32{y}:
      %bx.rword(32n, x, y) : {U32{Word.xor(32n, Word.xor(32n, x, y), y)} == U32{_} : U32}
      {==}

def bx.rblock(+a: M.CmBlock, +b: M.CmBlock) -> {M.CmBlock.xor(M.CmBlock.xor(a, b), b) == a : M.CmBlock}:
  match a b:
    case M.CmBlock{a0, a1, a2, a3} M.CmBlock{b0, b1, b2, b3}:
      %bx.ru32(a0, b0) : {M.CmBlock.xor(M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3}), M.CmBlock{b0, b1, b2, b3}) == M.CmBlock{_, a1, a2, a3} : M.CmBlock}
      %bx.ru32(a1, b1) : {M.CmBlock.xor(M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3}), M.CmBlock{b0, b1, b2, b3}) == M.CmBlock{U32.xor(U32.xor(a0, b0), b0), _, a2, a3} : M.CmBlock}
      %bx.ru32(a2, b2) : {M.CmBlock.xor(M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3}), M.CmBlock{b0, b1, b2, b3}) == M.CmBlock{U32.xor(U32.xor(a0, b0), b0), U32.xor(U32.xor(a1, b1), b1), _, a3} : M.CmBlock}
      %bx.ru32(a3, b3) : {M.CmBlock.xor(M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3}), M.CmBlock{b0, b1, b2, b3}) == M.CmBlock{U32.xor(U32.xor(a0, b0), b0), U32.xor(U32.xor(a1, b1), b1), U32.xor(U32.xor(a2, b2), b2), _} : M.CmBlock}
      {==}

# XTS on blocks

# one block under one tweak: D(E(p xor t) xor t xor t) xor t == p
def xtsp.blk(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, +t: M.CmBlock, hb: {dec(k, enc(k, M.CmBlock.xor(p, t))) == M.CmBlock.xor(p, t) : M.CmBlock}) -> {T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t) == p : M.CmBlock}:
  %Equal.sym(M.CmBlock, M.CmBlock.xor(M.CmBlock.xor(enc(k, M.CmBlock.xor(p, t)), t), t), enc(k, M.CmBlock.xor(p, t)), bx.rblock(enc(k, M.CmBlock.xor(p, t)), t)) : {M.CmBlock.xor(dec(k, _), t) == p : M.CmBlock}
  %Equal.sym(M.CmBlock, dec(k, enc(k, M.CmBlock.xor(p, t))), M.CmBlock.xor(p, t), hb) : {M.CmBlock.xor(_, t) == p : M.CmBlock}
  bx.rblock(p, t)

def xtsp.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xtsp.ins(bs, t)) == xtsp.ins(bs, t) : List<&2, M.CmBlock>} -> {T.xts.dec(~K, ~dec, k, T.xts.enc(~K, ~enc, k, bs, t), t) == bs : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+p, +rest}:
      +h => %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t), p, xtsp.blk(~K, ~enc, ~dec, k, p, t, cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), xtsp.ins(rest, T.Xts.mul_alpha(t)), h))) : {Con{_, T.xts.dec(~K, ~dec, k, T.xts.enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t)), T.Xts.mul_alpha(t))} == Con{p, rest} : List<&2, M.CmBlock>}
        %Equal.sym(List<&2, M.CmBlock>, T.xts.dec(~K, ~dec, k, T.xts.enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t)), T.Xts.mul_alpha(t)), rest, xtsp.go(~K, ~enc, ~dec, k, rest, T.Xts.mul_alpha(t))(cmp.tl(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), xtsp.ins(rest, T.Xts.mul_alpha(t)), h))) : {Con{p, _} == Con{p, rest} : List<&2, M.CmBlock>}
        {==}

def Laws.xts_blocks_round_trip(K, enc, dec, k1, inv, t, bs):
  +v = t
  +b = bs
  # the tail-recursive forms are the structural ones
  %tr.xts_enc_eq(~K, ~enc, k1, b, v) : {T.xts.dec.fast(~K, ~dec, k1, _, t) == bs : List<&2, M.CmBlock>}
  %tr.xts_dec_eq(~K, ~dec, k1, T.xts.enc(~K, ~enc, k1, b, v), v) : {_ == bs : List<&2, M.CmBlock>}
  xtsp.go(~K, ~enc, ~dec, k1, b, v)(inv(xtsp.ins(b, v)))

# CMAC: the state after a ++ b is the state after a, then b

def cmacp.feed(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, xs: List<&2, U32>, s: CM.CmacState, ys: List<&2, U32>) -> {CM.cmac.feed(~K, ~enc, k, B.append(xs, ys), s) == CM.cmac.feed(~K, ~enc, k, ys, CM.cmac.feed(~K, ~enc, k, xs, s)) : CM.CmacState}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      cmacp.feed(~K, ~enc, k, t, CM.cmac.step(~K, ~enc, k, s, h), ys)

def Laws.cmac_streaming(K, enc, k, s, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {CM.cmac.feed(~K, ~enc, k, _, s) == CM.cmac.feed(~K, ~enc, k, B.Octets.to_list(b), CM.cmac.feed(~K, ~enc, k, B.Octets.to_list(a), s)) : CM.CmacState}
  cmacp.feed(~K, ~enc, k, B.Octets.to_list(a), s, B.Octets.to_list(b))


# More on joining and splitting

def sp.mask_join_onto(bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {B.mask(M.cm.join_onto(bs, rest)) == M.cm.join_onto(bs, B.mask(rest)) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, M.cm.join_onto(t, rest))), M.cm.bytes_onto(b, B.mask(M.cm.join_onto(t, rest))), sp.mask_blk(b, M.cm.join_onto(t, rest))) : {_ == M.cm.bytes_onto(b, M.cm.join_onto(t, B.mask(rest))) : List<&2, U32>}
      %sp.mask_join_onto(t, rest) : {M.cm.bytes_onto(b, B.mask(M.cm.join_onto(t, rest))) == M.cm.bytes_onto(b, _) : List<&2, U32>}
      {==}

# blocks joined in front of a short tail split back into those blocks and tail
def sp.split_join_short(bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.split(rest) == M.CmSplit{Nil{}, rest} : M.CmSplit} -> {M.cm.split(M.cm.join_onto(bs, rest)) == M.CmSplit{bs, rest} : M.CmSplit}:
  match bs:
    case Nil{}:
      h => h
    case Con{+b, +t}:
      h => %Equal.sym(M.CmSplit, M.cm.split(M.cm.bytes_onto(b, M.cm.join_onto(t, rest))), M.cm.split.cons(b, M.cm.split(M.cm.join_onto(t, rest))), sp.blk(b, M.cm.join_onto(t, rest))) : {_ == M.CmSplit{Con{b, t}, rest} : M.CmSplit}
        %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(t, rest)), M.CmSplit{t, rest}, sp.split_join_short(t, rest)(h)) : {M.cm.split.cons(b, _) == M.CmSplit{Con{b, t}, rest} : M.CmSplit}
        {==}

def sp.join_append(bs: List<&2, M.CmBlock>, +x: M.CmBlock, +rest: List<&2, U32>) -> {M.cm.join_onto(List.append(&2, M.CmBlock, bs, Con{x, Nil{}}), rest) == M.cm.join_onto(bs, M.cm.bytes_onto(x, rest)) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %sp.join_append(t, x, rest) : {M.cm.bytes_onto(b, M.cm.join_onto(List.append(&2, M.CmBlock, t, Con{x, Nil{}}), rest)) == M.cm.bytes_onto(b, _) : List<&2, U32>}
      {==}

# The last block and the others

def li.init_app(es: List<&2, M.CmBlock>, +x: M.CmBlock, +e: M.CmBlock) -> {T.xts.init(List.append(&2, M.CmBlock, es, Con{x, Nil{}}), e) == Con{e, es} : List<&2, M.CmBlock>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e2, +es2}:
      %li.init_app(es2, x, e2) : {Con{e, T.xts.init(List.append(&2, M.CmBlock, es2, Con{x, Nil{}}), e2)} == Con{e, _} : List<&2, M.CmBlock>}
      {==}

def li.last_app(es: List<&2, M.CmBlock>, +x: M.CmBlock, +e: M.CmBlock) -> {T.xts.last(List.append(&2, M.CmBlock, es, Con{x, Nil{}}), e) == x : M.CmBlock}:
  match es:
    case Nil{}:
      {==}
    case Con{+e2, +es2}:
      li.last_app(es2, x, e2)

def li.init_last(rest: List<&2, M.CmBlock>, +p: M.CmBlock) -> {List.append(&2, M.CmBlock, T.xts.init(rest, p), Con{T.xts.last(rest, p), Nil{}}) == Con{p, rest} : List<&2, M.CmBlock>}:
  match rest:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      %li.init_last(r, q) : {Con{p, List.append(&2, M.CmBlock, T.xts.init(r, q), Con{T.xts.last(r, q), Nil{}})} == Con{p, _} : List<&2, M.CmBlock>}
      {==}

def li.len_enc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k, bs, t)) == List.length(&2, M.CmBlock, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      %li.len_enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t)) : {1n+List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t))) == 1n+_ : Nat}
      {==}

# The byte layer

def oc.le16(+o: B.Octets, h: {Nat.is_le(16n, B.Octets.len(o)) == True{} : Bool}) -> {Nat.is_le(16n, B.len(B.Octets.to_list(o))) == True{} : Bool}:
  %BL.octets_len_list(o) : {Nat.is_le(16n, _) == True{} : Bool}
  h

def xtsp.tweak(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k2: K, +i: B.Octets, h: {B.Octets.len(i) == 16n : Nat}) -> {T.xts.tweak(~K, ~enc, k2, i) == Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))} : Result<&2, &2, M.CmError, M.CmBlock>}:
  %Equal.sym(Nat, B.len(B.Octets.to_list(i)), 16n, oc.len(i, 16n, h)) : {T.xts.tweak.go(~K, ~enc, k2, M.cm.need_block.pick(Nat.is_eq(_, 16n), B.Octets.to_list(i), M.CmBadTweakLength{B.len(B.Octets.to_list(i))})) == Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))} : Result<&2, &2, M.CmError, M.CmBlock>}
  {==}

# the final partial ciphertext block is masked, and splits into no blocks
def xtsp.mask_steal_t(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> {B.mask(T.xts.steal_t(~K, ~enc, k, p, tl, t)) == T.xts.steal_t(~K, ~enc, k, p, tl, t) : List<&2, U32>}:
  match tl:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      %Equal.sym(List<&2, U32>, B.mask(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), B.take(B.len(Con{h, r}), B.mask(M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), li.mask_take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))) : {_ == B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(T.xts.benc(~K, ~enc, k, p, t), Nil{})), M.cm.bytes_onto(T.xts.benc(~K, ~enc, k, p, t), B.mask(Nil{})), sp.mask_blk(T.xts.benc(~K, ~enc, k, p, t), Nil{})) : {B.take(B.len(Con{h, r}), _) == B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))) : List<&2, U32>}
      {==}

def xtsp.lt_take(+n: Nat, +b: M.CmBlock, +h: {Nat.is_lt(n, 16n) == True{} : Bool}) -> {Nat.is_lt(B.len(B.take(n, M.cm.bytes_of(b))), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(B.take(n, M.cm.bytes_of(b))), n, li.len_take(n, M.cm.bytes_of(b))(na.lt_le(n, 16n)(h))) : {Nat.is_lt(_, 16n) == True{} : Bool}
  h

def xtsp.split_steal_t(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> {Nat.is_lt(B.len(tl), 16n) == True{} : Bool} -> {M.cm.split(T.xts.steal_t(~K, ~enc, k, p, tl, t)) == M.CmSplit{Nil{}, T.xts.steal_t(~K, ~enc, k, p, tl, t)} : M.CmSplit}:
  match tl:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      h => sp.short_split(B.take(B.len(Con{x, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))(xtsp.lt_take(B.len(Con{x, r}), T.xts.benc(~K, ~enc, k, p, t), h))

# the bytes the stealing passes through: tl, then the stolen tail of b
def xtsp.len16(+tl: List<&2, U32>, +b: M.CmBlock, h: {Nat.is_lt(B.len(tl), 16n) == True{} : Bool}) -> {Nat.is_eq(B.len(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), Nat.add(B.len(tl), B.len(B.drop(B.len(tl), M.cm.bytes_of(b)))), li.len_append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))) : {Nat.is_eq(_, 16n) == True{} : Bool}
  %Equal.sym(Nat, B.len(B.drop(B.len(tl), M.cm.bytes_of(b))), Nat.sub(16n, B.len(tl)), li.len_drop(B.len(tl), M.cm.bytes_of(b))) : {Nat.is_eq(Nat.add(B.len(tl), _), 16n) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(B.len(tl), Nat.sub(16n, B.len(tl))), 16n, na.add_sub(B.len(tl), 16n)(na.lt_le(B.len(tl), 16n)(h))) : {Nat.is_eq(_, 16n) == True{} : Bool}
  {==}

def xtsp.maskY(+tl: List<&2, U32>, +b: M.CmBlock, hm: {B.mask(tl) == tl : List<&2, U32>}) -> {B.mask(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), B.append(B.mask(tl), B.mask(B.drop(B.len(tl), M.cm.bytes_of(b)))), li.mask_append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))) : {_ == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(B.drop(B.len(tl), M.cm.bytes_of(b))), B.drop(B.len(tl), B.mask(M.cm.bytes_of(b))), li.mask_drop(B.len(tl), M.cm.bytes_of(b))) : {B.append(B.mask(tl), _) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, Nil{})), M.cm.bytes_onto(b, B.mask(Nil{})), sp.mask_blk(b, Nil{})) : {B.append(B.mask(tl), B.drop(B.len(tl), _)) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(tl), tl, hm) : {B.append(_, B.drop(B.len(tl), M.cm.bytes_of(b))) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  {==}

def xtsp.ppY(+tl: List<&2, U32>, +b: M.CmBlock, hm: {B.mask(tl) == tl : List<&2, U32>}, hl: {Nat.is_lt(B.len(tl), 16n) == True{} : Bool}) -> {M.cm.bytes_of(M.cm.block_of(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))))) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, M.cm.bytes_of(M.cm.block_of(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))))), B.mask(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))), sp.bb16(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))))(xtsp.len16(tl, b, hl)), xtsp.maskY(tl, b, hm))

# Ciphertext stealing undoes itself: the last whole block p and a tail tl
# (masked, fewer than 16 bytes), encrypted by steal_c and steal_t and
# decrypted by dsteal, come back as p's bytes and then tl
def xtsp.steal(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xtsp.sins(~K, ~enc, k, p, tl, t)) == xtsp.sins(~K, ~enc, k, p, tl, t) : List<&2, M.CmBlock>} -> {B.mask(tl) == tl : List<&2, U32>} -> {Nat.is_lt(B.len(tl), 16n) == True{} : Bool} -> {T.xts.dsteal(~K, ~dec, k, T.xts.steal_c(~K, ~enc, k, p, tl, t), T.xts.steal_t(~K, ~enc, k, p, tl, t), t) == M.cm.bytes_onto(p, tl) : List<&2, U32>}:
  match tl:
    case Nil{}:
      hs => hm => hl => %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t), p, xtsp.blk(~K, ~enc, ~dec, k, p, t, cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), Nil{}, hs))) : {M.cm.bytes_of(_) == M.cm.bytes_onto(p, Nil{}) : List<&2, U32>}
        {==}
    case Con{+h, +r}:
      +hs => +hm => +hl => %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), T.Xts.mul_alpha(t)), M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), xtsp.blk(~K, ~enc, ~dec, k, M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t), cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}, cmp.tl(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), Con{M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}}, hs)))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), M.cm.bytes_of(_)))), t), B.take(B.len(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), M.cm.bytes_of(_))) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(Nat, B.len(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), B.len(Con{h, r}), li.len_take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))(na.lt_le(B.len(Con{h, r}), 16n)(hl))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(_, M.cm.bytes_of(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))))))), t), B.take(_, M.cm.bytes_of(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))))))) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, M.cm.bytes_of(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))))), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), xtsp.ppY(Con{h, r}, T.xts.benc(~K, ~enc, k, p, t), hm, hl)) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(Con{h, r}), _))), t), B.take(B.len(Con{h, r}), _)) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, B.take(B.len(Con{h, r}), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), Con{h, r}, li.take_append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(Con{h, r}), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))))), t), _) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, B.drop(B.len(Con{h, r}), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), li.drop_append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), _)), t), Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)), BL.take_drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(_), t), Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(M.CmBlock, M.cm.block_of(M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), T.xts.benc(~K, ~enc, k, p, t), sp.block_bytes(T.xts.benc(~K, ~enc, k, p, t))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, _, t), Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t), p, xtsp.blk(~K, ~enc, ~dec, k, p, t, cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), Con{M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}}, hs))) : {M.cm.bytes_onto(_, Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
        {==}

def xtsp.d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, ec: List<&2, M.CmBlock>, +sc: M.CmBlock, +st: List<&2, U32>, +n: Nat) -> {T.xts.d2(~K, ~dec, k, t, M.CmSplit{List.append(&2, M.CmBlock, ec, Con{sc, Nil{}}), st}, n) == Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, ec, sc, st))} : Result<&2, &2, M.CmError, B.Octets>}:
  match ec:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %Equal.sym(List<&2, M.CmBlock>, T.xts.init(List.append(&2, M.CmBlock, es, Con{sc, Nil{}}), e), Con{e, es}, li.init_app(es, sc, e)) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, _, T.xts.last(List.append(&2, M.CmBlock, es, Con{sc, Nil{}}), e), st))} == Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, Con{e, es}, sc, st))} : Result<&2, &2, M.CmError, B.Octets>}
      %Equal.sym(M.CmBlock, T.xts.last(List.append(&2, M.CmBlock, es, Con{sc, Nil{}}), e), sc, li.last_app(es, sc, e)) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, Con{e, es}, _, st))} == Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, Con{e, es}, sc, st))} : Result<&2, &2, M.CmError, B.Octets>}
      {==}

def Laws.xts_round_trip(K, enc, dec, k1, k2, inv, i, p, hi, hp):
  # the hypothesis, at the blocks the cipher is given: ciphertext stealing's, then the others
  +hh = inv(List.append(&2, M.CmBlock, xtsp.sins(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.ins(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))
  +hne = sp.nonempty(B.Octets.to_list(p))(oc.le16(p, hp))
  +mo = Equal.trans(List<&2, U32>, B.mask(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), B.mask(T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), sp.mask_join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), Equal.cong(List<&2, U32>, List<&2, U32>, x => M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), x), B.mask(T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.mask_steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))
  # the public defs are the structural ones
  %tr.xts_encrypt(~K, ~enc, k1, k2, i, p) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, c => T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  %tr.bind_cong(T.Xts.encrypt.ref(~K, ~enc, k1, k2, i, p), c => T.Xts.decrypt.ref(~K, ~enc, ~dec, k1, k2, i, c), c => T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c), c => tr.xts_decrypt(~K, ~enc, ~dec, k1, k2, i, c)) : {_ == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # the tweak
  %Equal.sym(Result<&2, &2, M.CmError, M.CmBlock>, T.xts.tweak(~K, ~enc, k2, i), Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, xtsp.tweak(~K, ~enc, k2, i, hi)) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e1(~K, ~enc, k1, _, B.Octets.to_list(p)), c => T.xts.d1(~K, ~dec, k1, _, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # the data unit is masked
  %oc.masked(p) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e2(~K, ~enc, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.cm.split(_), B.len(B.Octets.to_list(p))), c => T.xts.d1(~K, ~dec, k1, Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # its blocks and tail
  %sp.eta(M.cm.split(B.mask(B.Octets.to_list(p)))) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e2(~K, ~enc, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), _, B.len(B.Octets.to_list(p))), c => T.xts.d1(~K, ~dec, k1, Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # at least one block, so encryption succeeds
  %hne : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e2(~K, ~enc, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.CmSplit{_, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))}, B.len(B.Octets.to_list(p))), c => T.xts.d1(~K, ~dec, k1, Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # decryption reads the ciphertext back, masked
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))), B.mask(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), BL.octets_to_of(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))) : {T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # which it already is
  %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), mo) : {T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # it splits into the ciphertext blocks and the partial block
  %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.CmSplit{List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))}, sp.split_join_short(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))(xtsp.split_steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))(sp.tail_short(B.Octets.to_list(p))))) : {T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), _, B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # decryption takes the last block apart
  %Equal.sym(Result<&2, &2, M.CmError, B.Octets>, T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.CmSplit{List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))}, B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))), Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))}, xtsp.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))))))) : {_ == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # XTS on blocks
  %Equal.sym(List<&2, M.CmBlock>, T.xts.dec(~K, ~dec, k1, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), xtsp.go(~K, ~enc, ~dec, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))(cmp.app_r(~K, ~enc, ~dec, k1, xtsp.sins(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.ins(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), hh))) : {Done{B.Octets.of_list(M.cm.join_onto(_, T.xts.dsteal(~K, ~dec, k1, T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # as many ciphertext blocks as plaintext blocks: the same last tweak
  %Equal.sym(Nat, List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), li.len_enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))) : {Done{B.Octets.of_list(M.cm.join_onto(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), T.xts.dsteal(~K, ~dec, k1, T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.alpha_n(_, enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # ciphertext stealing undoes itself
  %Equal.sym(List<&2, U32>, T.xts.dsteal(~K, ~dec, k1, T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), M.cm.bytes_onto(T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))), xtsp.steal(~K, ~enc, ~dec, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))(cmp.app_l(~K, ~enc, ~dec, k1, xtsp.sins(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.ins(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), hh))(sp.tail_masked(B.Octets.to_list(p)))(sp.tail_short(B.Octets.to_list(p)))) : {Done{B.Octets.of_list(M.cm.join_onto(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), _))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # the blocks back together
  %sp.join_append(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))) : {Done{B.Octets.of_list(_)} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, M.CmBlock>, List.append(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), Con{T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), Nil{}}), Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))}, li.init_last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))) : {Done{B.Octets.of_list(M.cm.join_onto(_, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, M.CmBlock>, Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))}, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))), hne) : {Done{B.Octets.of_list(M.cm.join_onto(_, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # and with the tail, the data unit
  %Equal.sym(List<&2, U32>, M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))), B.mask(B.Octets.to_list(p)), sp.join_split(B.Octets.to_list(p))) : {Done{B.Octets.of_list(_)} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, U32>, B.mask(B.Octets.to_list(p)), B.Octets.to_list(p), oc.masked(p)) : {Done{B.Octets.of_list(_)} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(p)), p, BL.octets_of_to(p)) : {Done{_} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  {==}
# XOR with a byte twice, and with itself

def bx.wself(n: Nat, w: Word(n)) -> {Word.xor(n, w, w) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{h, t}:
          match h:
            case False{}:
              %bx.wself(p, t) : {WCon{False{}, Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
              {==}
            case True{}:
              %bx.wself(p, t) : {WCon{False{}, Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
              {==}

def bits.xor_self(a: U32) -> {B.byte(U32.xor(a, a)) == 0 : U32}:
  match a:
    case U32{x}:
      %Equal.sym(Word(32n), Word.xor(32n, x, x), Word.zero(32n), bx.wself(32n, x)) : {B.byte(U32{_}) == 0 : U32}
      {==}

def bits.xor_xor(a: U32, y: U32) -> {B.byte(U32.xor(B.byte(U32.xor(a, y)), y)) == B.byte(a) : U32}:
  match a y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Word(8n), Word.xor(8n, Word.xor(8n, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WNil{}}}}}}}}}), WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WNil{}}}}}}}}}), WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, bx.rword(8n, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WNil{}}}}}}}}})) : {U32{W.W64.bits.cat(8n, 24n, _, Word.zero(24n))} == B.byte(U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}
      {==}


def li.mask_xor(xs: List<&2, U32>, ys: List<&2, U32>) -> {B.mask(M.cm.xor_bytes(xs, ys)) == M.cm.xor_bytes(xs, ys) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +s}:
      match ys:
        case Nil{}:
          {==}
        case Con{+b, +t}:
          %bits.byte_byte(U32.xor(a, b)) : {Con{B.byte(B.byte(U32.xor(a, b))), B.mask(M.cm.xor_bytes(s, t))} == Con{_, M.cm.xor_bytes(s, t)} : List<&2, U32>}
          %li.mask_xor(s, t) : {Con{B.byte(B.byte(U32.xor(a, b))), B.mask(M.cm.xor_bytes(s, t))} == Con{B.byte(B.byte(U32.xor(a, b))), _} : List<&2, U32>}
          {==}

def li.len_xor(xs: List<&2, U32>, ys: List<&2, U32>) -> {Nat.is_le(B.len(xs), B.len(ys)) == True{} : Bool} -> {B.len(M.cm.xor_bytes(xs, ys)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+a, +s}:
      match ys:
        case Nil{}:
          h => bo.absurd({B.len(M.cm.xor_bytes(Con{a, s}, Nil{})) == B.len(Con{a, s}) : Nat}, h)
        case Con{+b, +t}:
          h => %li.len_xor(s, t)(h) : {1n+B.len(M.cm.xor_bytes(s, t)) == 1n+_ : Nat}
            {==}

def li.xor_xor(xs: List<&2, U32>, ys: List<&2, U32>) -> {Nat.is_le(B.len(xs), B.len(ys)) == True{} : Bool} -> {M.cm.xor_bytes(M.cm.xor_bytes(xs, ys), ys) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+a, +s}:
      match ys:
        case Nil{}:
          h => bo.absurd({M.cm.xor_bytes(M.cm.xor_bytes(Con{a, s}, Nil{}), Nil{}) == B.mask(Con{a, s}) : List<&2, U32>}, h)
        case Con{+b, +t}:
          h => %Equal.sym(U32, B.byte(U32.xor(B.byte(U32.xor(a, b)), b)), B.byte(a), bits.xor_xor(a, b)) : {Con{_, M.cm.xor_bytes(M.cm.xor_bytes(s, t), t)} == Con{B.byte(a), B.mask(s)} : List<&2, U32>}
            %Equal.sym(List<&2, U32>, M.cm.xor_bytes(M.cm.xor_bytes(s, t), t), B.mask(s), li.xor_xor(s, t)(h)) : {Con{B.byte(a), _} == Con{B.byte(a), B.mask(s)} : List<&2, U32>}
            {==}

def li.len_bytes(+b: M.CmBlock, +rest: List<&2, U32>) -> {B.len(M.cm.bytes_onto(b, rest)) == Nat.add(16n, B.len(rest)) : Nat}:
  {==}

def na.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %na.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def na.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %na.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def na.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (a + b) - b == a
def na.sub_add(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, na.add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      na.sub_zero(a)
    case 1n+p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), na.add_succ(a, p)) : {Nat.sub(_, 1n+p) == a : Nat}
      na.sub_add(a, p)

def na.le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      {==}

# b <= a + b
def na.le_add(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, na.add_zero(a)) : {Nat.is_le(0n, _) == True{} : Bool}
      na.le_zero(a)
    case 1n+p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), na.add_succ(a, p)) : {Nat.is_le(1n+p, _) == True{} : Bool}
      na.le_add(a, p)

def bo.and_r(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case False{}:
      h => bo.absurd({b == True{} : Bool}, h)
    case True{}:
      h => h

def bo.and_l(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}:
  match a:
    case False{}:
      h => bo.absurd({False{} == True{} : Bool}, h)
    case True{}:
      h => {==}

def rs.disc(r: Result<&2, &2, M.CmError, Unit>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{u}:
      Empty

def rs.empty(+e: M.CmError, +u: Unit, h: {Fail{e} == Done{u} : Result<&2, &2, M.CmError, Unit>}) -> Empty:
  %h : rs.disc(_)
  Unit{}

def rs.absurd(-A: Type, +e: M.CmError, +u: Unit, h: {Fail{e} == Done{u} : Result<&2, &2, M.CmError, Unit>}) -> A:
  Empty.absurd(A, rs.empty(e, u, h))


# CCM

# checks that pass mean a tag of at most 16 bytes
def ccmp.tag_le.go(b: Bool, +m: Nat, +nl: Nat, +n: Nat, +u: Unit) -> {CC.ccm.tag_ok(m) == b : Bool} -> {CC.ccm.checks(m, nl, n) == Done{u} : Result<&2, &2, M.CmError, Unit>} -> {Nat.is_le(m, 16n) == True{} : Bool}:
  match b:
    case False{}:
      eb => h => rs.absurd({Nat.is_le(m, 16n) == True{} : Bool}, M.CmBadTagLength{m}, u, Equal.trans(Result<&2, &2, M.CmError, Unit>, CC.ccm.checks.tag(False{}, m, nl, n), CC.ccm.checks.tag(CC.ccm.tag_ok(m), m, nl, n), Done{u}, Equal.cong(Bool, Result<&2, &2, M.CmError, Unit>, x => CC.ccm.checks.tag(x, m, nl, n), False{}, CC.ccm.tag_ok(m), Equal.sym(Bool, CC.ccm.tag_ok(m), False{}, eb)), h))
    case True{}:
      eb => h => bo.and_l(Nat.is_le(m, 16n), Nat.is_eq(Nat.mod(m, 2n), 0n))(bo.and_r(Nat.is_le(4n, m), Bool.and(Nat.is_le(m, 16n), Nat.is_eq(Nat.mod(m, 2n), 0n)))(eb))

def ccmp.tag_le(+m: Nat, +nl: Nat, +n: Nat, +u: Unit, h: {CC.ccm.checks(m, nl, n) == Done{u} : Result<&2, &2, M.CmError, Unit>}) -> {Nat.is_le(m, 16n) == True{} : Bool}:
  ccmp.tag_le.go(CC.ccm.tag_ok(m), m, nl, n, u)({==})(h)

def ccmp.diff_self(xs: List<&2, U32>) -> {M.cm.diff(xs, xs, 0) == 0 : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +s}:
      %Equal.sym(U32, B.byte(U32.xor(a, a)), 0, bits.xor_self(a)) : {M.cm.diff(s, s, U32.or(0, _)) == 0 : U32}
      ccmp.diff_self(s)

def ccmp.ct_refl(+xs: List<&2, U32>) -> {M.cm.ct_eq(xs, xs) == True{} : Bool}:
  %Equal.sym(U32, M.cm.diff(xs, xs, 0), 0, ccmp.diff_self(xs)) : {U32.is_eq(_, 0) == True{} : Bool}
  {==}

def ccmp.len_ctrb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> {List.length(&2, M.CmBlock, CC.ccm.ctrb(~K, ~enc, k, bs, a0, i)) == List.length(&2, M.CmBlock, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      %ccmp.len_ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)) : {1n+List.length(&2, M.CmBlock, CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1))) == 1n+_ : Nat}
      {==}

# CTR twice is the identity on blocks
def ccmp.ctrb2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> {CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, bs, a0, i), a0, i) == bs : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      %Equal.sym(M.CmBlock, M.CmBlock.xor(M.CmBlock.xor(b, enc(k, CC.ccm.ai(a0, i))), enc(k, CC.ccm.ai(a0, i))), b, bx.rblock(b, enc(k, CC.ccm.ai(a0, i)))) : {Con{_, CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)), a0, U32.add(i, 1))} == Con{b, rest} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)), a0, U32.add(i, 1)), rest, ccmp.ctrb2(~K, ~enc, k, rest, a0, U32.add(i, 1))) : {Con{b, _} == Con{b, rest} : List<&2, M.CmBlock>}
      {==}

def ccmp.mask_xcrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, s: M.CmSplit) -> {B.mask(CC.ccm.xcrypt(~K, ~enc, k, a0, s)) == CC.ccm.xcrypt(~K, ~enc, k, a0, s) : List<&2, U32>}:
  match s:
    case M.CmSplit{+bs, +tail}:
      %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))), M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), B.mask(M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))), sp.mask_join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))) : {_ == M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs)))))))) : List<&2, U32>}
      %li.mask_xor(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))) : {M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), B.mask(M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))) == M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), _) : List<&2, U32>}
      {==}

def ccmp.len_join(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32, +x: List<&2, U32>, +y: List<&2, U32>, h: {B.len(x) == B.len(y) : Nat}) -> {B.len(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, i), x)) == B.len(M.cm.join_onto(bs, y)) : Nat}:
  match bs:
    case Nil{}:
      h
    case Con{+b, +rest}:
      %Equal.sym(Nat, B.len(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)), x)), B.len(M.cm.join_onto(rest, y)), ccmp.len_join(~K, ~enc, k, rest, a0, U32.add(i, 1), x, y, h)) : {Nat.add(16n, _) == Nat.add(16n, B.len(M.cm.join_onto(rest, y))) : Nat}
      {==}
# the CTR tail is as short as the plaintext tail
def ccmp.xt_short(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +ys: List<&2, U32>) -> {Nat.is_lt(B.len(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))), B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), li.len_xor(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))(na.lt_le(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n)(sp.tail_short(ys)))) : {Nat.is_lt(_, 16n) == True{} : Bool}
  sp.tail_short(ys)

# CTR from counter 1 undoes itself (on a masked byte string)
def ccmp.xx(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +ys: List<&2, U32>) -> {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.mask(ys))))) == B.mask(ys) : List<&2, U32>}:
  %sp.eta(M.cm.split(B.mask(ys))) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, _))) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))), M.CmSplit{CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))}, sp.split_join_short(CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))(sp.short_split(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))(ccmp.xt_short(~K, ~enc, k, a0, ys)))) : {CC.ccm.xcrypt(~K, ~enc, k, a0, _) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, M.CmBlock, CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1)), List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))), ccmp.len_ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1)) : {M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), a0, 1), M.cm.xor_bytes(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(_))))))) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(List<&2, M.CmBlock>, CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), a0, 1), M.cm.split.blocks(M.cm.split(B.mask(ys))), ccmp.ctrb2(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1)) : {M.cm.join_onto(_, M.cm.xor_bytes(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, M.cm.xor_bytes(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))), li.xor_xor(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))(na.lt_le(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n)(sp.tail_short(ys)))) : {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), _) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))), M.cm.split.tail(M.cm.split(B.mask(ys))), sp.tail_masked(ys)) : {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), _) == B.mask(ys) : List<&2, U32>}
  sp.join_split(ys)

# and keeps its length
def ccmp.len_xc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +ys: List<&2, U32>) -> {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.mask(ys)))) == B.len(B.mask(ys)) : Nat}:
  %sp.eta(M.cm.split(B.mask(ys))) : {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, _)) == B.len(B.mask(ys)) : Nat}
  %sp.join_split(ys) : {B.len(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))) == B.len(_) : Nat}
  ccmp.len_join(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1, M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.split.tail(M.cm.split(B.mask(ys))), li.len_xor(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))(na.lt_le(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n)(sp.tail_short(ys))))

def ccmp.xxp(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +p: B.Octets) -> {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.Octets.to_list(p))))) == B.Octets.to_list(p) : List<&2, U32>}:
  %oc.masked(p) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(_)))) == _ : List<&2, U32>}
  ccmp.xx(~K, ~enc, k, a0, B.Octets.to_list(p))

def ccmp.len_xcp(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +p: B.Octets) -> {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.Octets.to_list(p)))) == B.len(B.Octets.to_list(p)) : Nat}:
  %oc.masked(p) : {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(_))) == B.len(_) : Nat}
  ccmp.len_xc(~K, ~enc, k, a0, B.Octets.to_list(p))

def ccmp.len_tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, h: {Nat.is_le(m, 16n) == True{} : Bool}) -> {B.len(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)) == m : Nat}:
  li.len_take(m, M.cm.bytes_of(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv)))(h)

def ccmp.le_tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, +h: {Nat.is_le(m, 16n) == True{} : Bool}) -> {Nat.is_le(B.len(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), m, ccmp.len_tag(~K, ~enc, k, m, l, nv, av, pv, h)) : {Nat.is_le(_, 16n) == True{} : Bool}
  h

def ccmp.mask_tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> {B.mask(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)) == CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), B.take(m, B.mask(M.cm.bytes_of(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv)))), li.mask_take(m, M.cm.bytes_of(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv)))) : {_ == CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv), Nil{})), M.cm.bytes_onto(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv), B.mask(Nil{})), sp.mask_blk(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv), Nil{})) : {B.take(m, _) == CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv) : List<&2, U32>}
  {==}

def ccmp.mask_eb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> {B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.mask(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), li.mask_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) : {_ == B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %ccmp.mask_xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)) : {B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.mask(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == B.append(_, M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %li.mask_xor(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))) : {B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.mask(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), _) : List<&2, U32>}
  {==}

def ccmp.len_eb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, +h: {Nat.is_le(m, 16n) == True{} : Bool}) -> {B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}:
  %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.len(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), li.len_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) : {_ == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}
  %Equal.sym(Nat, B.len(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))), B.len(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv)), li.len_xor(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))(ccmp.le_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv, h))) : {Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), _) == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}
  %Equal.sym(Nat, B.len(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv)), m, ccmp.len_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv, h)) : {Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), _) == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}
  {==}

# decryption accepts what encryption produced, whatever the parameter checks answer
def ccmp.main(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nonce: B.Octets, +aad: B.Octets, +p: B.Octets, r: Result<&2, &2, M.CmError, Unit>) -> {CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))) == r : Result<&2, &2, M.CmError, Unit>} -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.ccm.e2(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), r), c => CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, CC.ccm.e2(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), r)) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      h => {==}
    case Done{+u}:
      +h => +hm = ccmp.tag_le(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p)), u, h)
        +leb = ccmp.len_eb(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), hm)
        # decryption reads the ciphertext back, masked
        %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))), B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), BL.octets_to_of(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))) : {CC.ccm.d2(~K, ~enc, Nat.is_le(m, B.len(_)), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # which it already is
        %Equal.sym(List<&2, U32>, B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), ccmp.mask_eb(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))) : {CC.ccm.d2(~K, ~enc, Nat.is_le(m, B.len(_)), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # it is longer than the tag
        %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), leb) : {CC.ccm.d2(~K, ~enc, Nat.is_le(m, _), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Bool, Nat.is_le(m, Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)), True{}, na.le_add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)) : {CC.ccm.d2(~K, ~enc, _, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # its body is as long as the message
        %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), leb) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), Nat.sub(_, m))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Nat, Nat.sub(Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), m), B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), na.sub_add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), _)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Nat, B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.len(B.Octets.to_list(p)), ccmp.len_xcp(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), p)) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), _)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # so its checks pass as encryption's did
        %Equal.sym(Result<&2, &2, M.CmError, Unit>, CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))), Done{u}, h) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # the body and the tag apart
        %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), leb) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(_, m), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(Nat.sub(_, m), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(Nat.sub(_, m), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Nat, Nat.sub(Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), m), B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), na.sub_add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(_, B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(_, B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(_, B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(List<&2, U32>, B.take(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), li.take_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(_)))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(_))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(List<&2, U32>, B.drop(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), li.drop_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(_, M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # CTR undoes itself: the plaintext
        %Equal.sym(List<&2, U32>, CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))))), B.Octets.to_list(p), ccmp.xxp(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), p)) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), _)), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # the received tag, unmasked from S_0
        %Equal.sym(List<&2, U32>, M.cm.xor_bytes(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), B.mask(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), li.xor_xor(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))(ccmp.le_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), hm))) : {CC.ccm.open(M.cm.ct_eq(_, CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), B.Octets.to_list(p)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(List<&2, U32>, B.mask(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), ccmp.mask_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))) : {CC.ccm.open(M.cm.ct_eq(_, CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), B.Octets.to_list(p)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # matches the tag recomputed
        %Equal.sym(Bool, M.cm.ct_eq(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), True{}, ccmp.ct_refl(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)))) : {CC.ccm.open(_, B.Octets.to_list(p)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(p)), p, BL.octets_of_to(p)) : {Done{_} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        {==}

def Laws.ccm_round_trip(K, enc, k, m, nonce, aad, p):
  # the public defs are the structural ones
  %tr.ccm_encrypt(~K, ~enc, k, m, nonce, aad, p) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, c => CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, _) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.bind_cong(CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p), c => CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c), c => CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c), c => tr.ccm_decrypt(~K, ~enc, k, m, nonce, aad, c)) : {_ == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p)) : Result<&2, &2, M.CmError, B.Octets>}
  ccmp.main(~K, ~enc, k, m, nonce, aad, p, CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))))({==})

# A block through Octets and back

def Laws.block_octets_round_trip(b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(M.cm.bytes_of(b))), B.mask(M.cm.bytes_of(b)), BL.octets_to_of(M.cm.bytes_of(b))) : {M.CmBlock.of_octets.pick(Nat.is_eq(B.len(_), 16n), _) == Some{b} : Maybe<&2, M.CmBlock>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, Nil{})), M.cm.bytes_onto(b, B.mask(Nil{})), sp.mask_blk(b, Nil{})) : {M.CmBlock.of_octets.pick(Nat.is_eq(B.len(_), 16n), _) == Some{b} : Maybe<&2, M.CmBlock>}
  %Equal.sym(M.CmBlock, M.cm.block_of(M.cm.bytes_of(b)), b, sp.block_bytes(b)) : {Some{_} == Some{b} : Maybe<&2, M.CmBlock>}
  {==}

# Vectors

def Laws.aes128_fips197_c1():
  {==}

def Laws.aes_bad_key_length():
  {==}

def Laws.cbc_sp800_38a_f21_block1():
  {==}

def Laws.cbc_not_whole_blocks():
  {==}

def Laws.cbc_short_iv():
  {==}

def Laws.pkcs7_pad_empty():
  {==}

def Laws.pkcs7_pad_15():
  {==}

def Laws.pkcs7_unpad_15():
  {==}

def Laws.pkcs7_unpad_zero():
  {==}

def Laws.pkcs7_unpad_mixed():
  {==}

def Laws.xts_short():
  {==}

def Laws.xts_sector():
  {==}

def Laws.ccm_bad_tag_length():
  {==}

def Laws.ccm_bad_nonce_length():
  {==}

def Laws.cmac_rfc4493_k1():
  {==}
