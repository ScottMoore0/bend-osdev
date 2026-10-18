# bend-osdev-legacy-ciphers: the older block and stream ciphers a kernel's
# crypto layer still carries (DES, 3DES, SM4, Camellia, Serpent, Twofish,
# RC4), one file per cipher. This file holds what they share: the package's
# error type, the 64-bit block, and word helpers.
#
# The 128-bit block ciphers (sm4.bend, camellia.bend, serpent.bend,
# twofish.bend) work on cipher-modes' CmBlock, so they plug into every mode
# there as the template arguments ~K, ~enc, ~dec. DES and 3DES have 64-bit
# blocks: LcBlock64 below, and the 64-bit modes in modes64.bend.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W

# Every failure the package reports
type LcError is Data:
  LcBadKeyLength{got: Nat}
  LcBadIvLength{got: Nat}
  LcNotBlockMultiple{len: Nat}

# A 64-bit block: two 32-bit words, big-endian (hi holds bytes 0 to 3, byte 0
# in its top 8 bits). Every value of the type is a block, so "decryption
# inverts encryption" can be stated for every block. The type is open: a
# cipher may build and match blocks directly.
type LcBlock64 is Data:
  LcBlock64{hi: U32, lo: U32}

def LcBlock64.zero() -> LcBlock64:
  LcBlock64{0, 0}

def LcBlock64.xor(a: LcBlock64, b: LcBlock64) -> LcBlock64:
  match a b:
    case LcBlock64{a0, a1} LcBlock64{b0, b1}:
      LcBlock64{U32.xor(a0, b0), U32.xor(a1, b1)}

# Words, natively: fast, for the parts of a cipher no proof inverts (round
# functions and key schedules). n is 1 to 31.

def lc.rotl(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shln(x, n), U32.shrn(x, Nat.sub(32n, n)))

# byte n of x, counting from the least significant (n = 0 to 3)
def lc.byte(x: U32, n: Nat) -> U32:
  U32.and(255, U32.shrn(x, Nat.mul(8n, n)))

# the word with bytes a (most significant), b, c, d
def lc.be(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(U32.shln(U32.and(255, a), 24n), U32.shln(U32.and(255, b), 16n)), U32.or(U32.shln(U32.and(255, c), 8n), U32.and(255, d)))

# the word with bytes a (least significant), b, c, d
def lc.le(a: U32, b: U32, c: U32, d: U32) -> U32:
  lc.be(d, c, b, a)

# bit i of x (0 the least significant), as 0 or 1
def lc.bit(x: U32, i: Nat) -> U32:
  U32.and(1, U32.shrn(x, i))

# element n of a list of words (0 past the end)
def lc.at(xs: List<&2, U32>, n: Nat) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      match n:
        case 0n:
          h
        case 1n+p:
          lc.at(t, p)

# Words as bits: for the steps a proof must undo (rotations, byte swaps, bit
# permutations). They are built by slicing a word's bits (bend-osdev-word64's
# W64.bits), so a proof about a symbolic word computes through them; they are
# slower than the native forms above.

# the (m + n)-bit word w rotated left by n
def lc.wrotl(+m: Nat, +n: Nat, +w: Word(Nat.add(m, n))) -> Word(Nat.add(n, m)):
  W.W64.bits.cat(n, m, W.W64.bits.hi(m, n, w), W.W64.bits.lo(m, n, w))

def lc.rotl1.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(31n, 1n, w)}

def lc.rotl3.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(29n, 3n, w)}

def lc.rotl5.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(27n, 5n, w)}

def lc.rotl7.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(25n, 7n, w)}

def lc.rotl10.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(22n, 10n, w)}

def lc.rotl13.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(19n, 13n, w)}

def lc.rotl19.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(13n, 19n, w)}

def lc.rotl22.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(10n, 22n, w)}

def lc.rotl25.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(7n, 25n, w)}

def lc.rotl27.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(5n, 27n, w)}

def lc.rotl29.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(3n, 29n, w)}

def lc.rotl31.bits(x: U32) -> U32:
  match x:
    case U32{+w}:
      U32{lc.wrotl(1n, 31n, w)}

# the low 8 bits of a word, as bits, and the byte with these bits
def lc.bits8(b: U32) -> Word(8n):
  match b:
    case U32{w}:
      W.W64.bits.lo(8n, 24n, w)

def lc.of8(s: Word(8n)) -> U32:
  U32{W.W64.bits.cat(8n, 24n, s, Word.zero(24n))}

# the word with bytes a (most significant), b, c, d, by bits
def lc.be.bits(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32{W.W64.bits.cat(8n, 24n, lc.bits8(d), W.W64.bits.cat(8n, 16n, lc.bits8(c), W.W64.bits.cat(8n, 8n, lc.bits8(b), lc.bits8(a))))}

# the bytes of w, by bits: b0 the most significant
def lc.b0.bits(w: U32) -> U32:
  match w:
    case U32{x}:
      lc.of8(W.W64.bits.hi(8n, 8n, W.W64.bits.hi(8n, 16n, W.W64.bits.hi(8n, 24n, x))))

def lc.b1.bits(w: U32) -> U32:
  match w:
    case U32{x}:
      lc.of8(W.W64.bits.lo(8n, 8n, W.W64.bits.hi(8n, 16n, W.W64.bits.hi(8n, 24n, x))))

def lc.b2.bits(w: U32) -> U32:
  match w:
    case U32{x}:
      lc.of8(W.W64.bits.lo(8n, 16n, W.W64.bits.hi(8n, 24n, x)))

def lc.b3.bits(w: U32) -> U32:
  match w:
    case U32{x}:
      lc.of8(W.W64.bits.lo(8n, 24n, x))

# the word with its bytes in reverse order (big-endian to little-endian)
def lc.bswap.bits(+w: U32) -> U32:
  lc.be.bits(lc.b3.bits(w), lc.b2.bits(w), lc.b1.bits(w), lc.b0.bits(w))

# the bits of a word, most significant first, in front of acc
def lc.msb.go(n: Nat, w: Word(n), acc: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      acc
    case 1n+p:
      match w:
        case WCon{h, t}:
          lc.msb.go(p, t, Con{h, acc})

def lc.msb(x: U32, acc: List<&2, Bool>) -> List<&2, Bool>:
  match x:
    case U32{w}:
      lc.msb.go(32n, w, acc)

# bs reversed, in front of acc
def lc.rev_bits(bs: List<&2, Bool>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      acc
    case Con{h, t}:
      lc.rev_bits(t, Con{h, acc})

# all but the first n of bs
def lc.drop_bits(n: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      bs
    case 1n+p:
      match bs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          lc.drop_bits(p, t)

# the n-bit word whose bits, least significant first, are the first n of bs
# (False past the end)
def lc.word_lsb(n: Nat, bs: List<&2, Bool>) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match bs:
        case Nil{}:
          WCon{False{}, lc.word_lsb(p, Nil{})}
        case Con{h, t}:
          WCon{h, lc.word_lsb(p, t)}

# the element i of bs (False past the end)
def lc.nth(bs: List<&2, Bool>, i: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          lc.nth(t, p)

# Tables: a complete binary tree of words, read by the bits of an index. Bend
# 2.0.37 recomputes a table def at every call, so a cipher builds its tables
# once, when its key is made, and keeps them in the key.

type LcTab is Data:
  LcLeaf{v: U32}
  LcNode{l: LcTab, r: LcTab}

def lc.tab.leaves(xs: List<&2, U32>) -> List<&2, LcTab>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{LcLeaf{h}, lc.tab.leaves(t)}

def lc.tab.pairs(ts: List<&2, LcTab>) -> List<&2, LcTab>:
  match ts:
    case Con{a, Con{b, t}}:
      Con{LcNode{a, b}, lc.tab.pairs(t)}
    case _:
      Nil{}

def lc.tab.up(n: Nat, ts: List<&2, LcTab>) -> List<&2, LcTab>:
  match n:
    case 0n:
      ts
    case 1n+p:
      lc.tab.up(p, lc.tab.pairs(ts))

def lc.tab.root(ts: List<&2, LcTab>) -> LcTab:
  match ts:
    case Nil{}:
      LcLeaf{0}
    case Con{h, t}:
      h

# the table of the 2^d words xs (entry i is element i)
def lc.tab(d: Nat, xs: List<&2, U32>) -> LcTab:
  lc.tab.root(lc.tab.up(d, lc.tab.leaves(xs)))

def lc.tab.pick(one: Bool, l: LcTab, r: LcTab) -> LcTab:
  match one:
    case True{}:
      r
    case False{}:
      l

# entry i of a table of depth d (i below 2^d)
def lc.tab.get(d: Nat, t: LcTab, +i: U32) -> U32:
  match d:
    case 0n:
      match t:
        case LcLeaf{v}:
          v
        case LcNode{l, r}:
          0
    case 1n+(+p):
      match t:
        case LcLeaf{v}:
          v
        case LcNode{l, r}:
          lc.tab.get(p, lc.tab.pick(U32.is_eq(lc.bit(i, p), 1), l, r), i)

# Blocks as byte strings (built on bits, so the round trip is provable)

# the 8 bytes of a block in front of rest
def lc.block_bytes(b: LcBlock64, rest: List<&2, U32>) -> List<&2, U32>:
  match b:
    case LcBlock64{+hi, +lo}:
      Con{lc.b0.bits(hi), Con{lc.b1.bits(hi), Con{lc.b2.bits(hi), Con{lc.b3.bits(hi), Con{lc.b0.bits(lo), Con{lc.b1.bits(lo), Con{lc.b2.bits(lo), Con{lc.b3.bits(lo), rest}}}}}}}}

def lc.block8(a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32) -> LcBlock64:
  LcBlock64{lc.be.bits(a0, a1, a2, a3), lc.be.bits(a4, a5, a6, a7)}

def LcBlock64.to_octets(b: LcBlock64) -> B.Octets:
  B.Octets.of_list(lc.block_bytes(b, Nil{}))

def lc.block_of(xs: List<&2, U32>) -> Maybe<&2, LcBlock64>:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}:
      Some{lc.block8(a0, a1, a2, a3, a4, a5, a6, a7)}
    case _:
      None{}

# an 8-byte string as a block (big-endian words); None for any other length
def LcBlock64.of_octets(o: B.Octets) -> Maybe<&2, LcBlock64>:
  lc.block_of(B.Octets.to_list(o))

def LcBlock64.hex(b: LcBlock64) -> String:
  B.hex(lc.block_bytes(b, Nil{}))
