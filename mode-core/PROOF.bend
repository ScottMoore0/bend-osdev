# Proofs of mode-core's laws. block_octets_round_trip is the block's own
# law; the others are the lemmas the modes share, proved here once (each
# def Laws.x at the end of the file is the lemma above it).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./mode-core.bend as M
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
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

# the block of a block's bytes is the block
def sp.block_bytes(b: M.CmBlock) -> {M.cm.block_of(M.cm.bytes_of(b)) == b : M.CmBlock}:
  match b:
    case M.CmBlock{U32{WCon{p0, WCon{p1, WCon{p2, WCon{p3, WCon{p4, WCon{p5, WCon{p6, WCon{p7, WCon{p8, WCon{p9, WCon{p10, WCon{p11, WCon{p12, WCon{p13, WCon{p14, WCon{p15, WCon{p16, WCon{p17, WCon{p18, WCon{p19, WCon{p20, WCon{p21, WCon{p22, WCon{p23, WCon{p24, WCon{p25, WCon{p26, WCon{p27, WCon{p28, WCon{p29, WCon{p30, WCon{p31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{q0, WCon{q1, WCon{q2, WCon{q3, WCon{q4, WCon{q5, WCon{q6, WCon{q7, WCon{q8, WCon{q9, WCon{q10, WCon{q11, WCon{q12, WCon{q13, WCon{q14, WCon{q15, WCon{q16, WCon{q17, WCon{q18, WCon{q19, WCon{q20, WCon{q21, WCon{q22, WCon{q23, WCon{q24, WCon{q25, WCon{q26, WCon{q27, WCon{q28, WCon{q29, WCon{q30, WCon{q31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{r0, WCon{r1, WCon{r2, WCon{r3, WCon{r4, WCon{r5, WCon{r6, WCon{r7, WCon{r8, WCon{r9, WCon{r10, WCon{r11, WCon{r12, WCon{r13, WCon{r14, WCon{r15, WCon{r16, WCon{r17, WCon{r18, WCon{r19, WCon{r20, WCon{r21, WCon{r22, WCon{r23, WCon{r24, WCon{r25, WCon{r26, WCon{r27, WCon{r28, WCon{r29, WCon{r30, WCon{r31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# Every Octets is masked: to_list(o) = to_list(of_list(to_list(o))) = mask(to_list(o))
def oc.masked(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.mask(B.Octets.to_list(o)), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o))), Equal.cong(B.Octets, List<&2, U32>, x => B.Octets.to_list(x), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)))

def oc.len(+o: B.Octets, +n: Nat, h: {B.Octets.len(o) == n : Nat}) -> {B.len(B.Octets.to_list(o)) == n : Nat}:
  Equal.trans(Nat, B.len(B.Octets.to_list(o)), B.Octets.len(o), n, Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)), h)

def tr.len_go(+bs: List<&2, M.CmBlock>, +n: Nat) -> {M.cm.blocks.len.go(bs, n) == Nat.add(List.length(&2, M.CmBlock, bs), n) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, M.cm.blocks.len.go(t, 1n+n), Nat.add(List.length(&2, M.CmBlock, t), 1n+n), 1n+Nat.add(List.length(&2, M.CmBlock, t), n), tr.len_go(t, 1n+n), UL.nat_add_succ(List.length(&2, M.CmBlock, t), n))

def tr.len_eq(+bs: List<&2, M.CmBlock>) -> {List.length(&2, M.CmBlock, bs) == M.cm.blocks.len(bs) : Nat}:
  Equal.sym(Nat, M.cm.blocks.len(bs), List.length(&2, M.CmBlock, bs), Equal.trans(Nat, M.cm.blocks.len.go(bs, 0n), Nat.add(List.length(&2, M.CmBlock, bs), 0n), List.length(&2, M.CmBlock, bs), tr.len_go(bs, 0n), UL.nat_add_zero(List.length(&2, M.CmBlock, bs))))

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

# a bind whose continuations agree on every value agrees
def tr.bind_cong(r: Result<&2, &2, M.CmError, B.Octets>, f: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, g: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, h: @c: B.Octets -> {f(c) == g(c) : Result<&2, &2, M.CmError, B.Octets>}) -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, f) == Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, g) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{c}:
      h(c)

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

def li.len_bytes(+b: M.CmBlock, +rest: List<&2, U32>) -> {B.len(M.cm.bytes_onto(b, rest)) == Nat.add(16n, B.len(rest)) : Nat}:
  {==}

# A block through Octets and back

def Laws.block_octets_round_trip(b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(M.cm.bytes_of(b))), B.mask(M.cm.bytes_of(b)), BL.octets_to_of(M.cm.bytes_of(b))) : {M.CmBlock.of_octets.pick(Nat.is_eq(B.len(_), 16n), _) == Some{b} : Maybe<&2, M.CmBlock>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, Nil{})), M.cm.bytes_onto(b, B.mask(Nil{})), sp.mask_blk(b, Nil{})) : {M.CmBlock.of_octets.pick(Nat.is_eq(B.len(_), 16n), _) == Some{b} : Maybe<&2, M.CmBlock>}
  %Equal.sym(M.CmBlock, M.cm.block_of(M.cm.bytes_of(b)), b, sp.block_bytes(b)) : {Some{_} == Some{b} : Maybe<&2, M.CmBlock>}
  {==}

# The laws of the lemmas the modes share: each is the lemma above

def Laws.byte_byte(y):
  bits.byte_byte(y)

def Laws.split_cons_blocks(b, s):
  sp.cons_blocks(b, s)

def Laws.split_cons_tail(b, s):
  sp.cons_tail(b, s)

def Laws.split_eta(s):
  sp.eta(s)

def Laws.list_take_append(a, b):
  li.take_append(a, b)

def Laws.list_drop_append(a, b):
  li.drop_append(a, b)

def Laws.list_mask_append(a, b):
  li.mask_append(a, b)

def Laws.list_mask_take(n, xs):
  li.mask_take(n, xs)

def Laws.list_len_append(a, b):
  li.len_append(a, b)

def Laws.list_len_take(n, xs, h1):
  li.len_take(n, xs)(h1)

def Laws.nat_lt_le(a, b, h1):
  na.lt_le(a, b)(h1)

def Laws.split_bytes_onto(b, rest):
  sp.blk(b, rest)

def Laws.mask_bytes_onto(b, rest):
  sp.mask_blk(b, rest)

def Laws.join_split(ys):
  sp.join_split(ys)

def Laws.bytes_onto_block16(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, rest):
  sp.blk16g(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, rest)

def Laws.split_tail_short(ys):
  sp.tail_short(ys)

def Laws.split_tail_masked(ys):
  sp.tail_masked(ys)

def Laws.split_short(ys, h1):
  sp.short_split(ys)(h1)

def Laws.block_of_bytes_of(b):
  sp.block_bytes(b)

def Laws.octets_masked(o):
  oc.masked(o)

def Laws.octets_len(o, n, h):
  oc.len(o, n, h)

def Laws.blocks_len_fast(bs):
  tr.len_eq(bs)

def Laws.split_fast(xs):
  tr.split_eq(xs)

def Laws.join_onto_fast(bs, rest):
  tr.join_eq(bs, rest)

def Laws.bind_cong(r, f, g, h):
  tr.bind_cong(r, f, g, h)

def Laws.dec_enc_head(K, enc, dec, k, x, xs, h):
  cmp.hd(~K, ~enc, ~dec, k, x, xs, h)

def Laws.dec_enc_tail(K, enc, dec, k, x, xs, h):
  cmp.tl(~K, ~enc, ~dec, k, x, xs, h)

def Laws.word_xor_xor(n, a, b):
  bx.rword(n, a, b)

def Laws.u32_xor_xor(a, b):
  bx.ru32(a, b)

def Laws.block_xor_xor(a, b):
  bx.rblock(a, b)

def Laws.mask_join_onto(bs, rest):
  sp.mask_join_onto(bs, rest)

def Laws.split_join_short(bs, rest, h1):
  sp.split_join_short(bs, rest)(h1)
