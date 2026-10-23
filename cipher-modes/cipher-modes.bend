# bend-osdev-cipher-modes: block-cipher modes of operation over any 128-bit
# block cipher. This file holds what every mode shares: the 128-bit block, the
# package's error type, and the byte-level helpers the modes are built from.
#
# The block cipher is a parameter. Every mode takes it as template arguments:
#   ~K: Data                          the cipher's key (an expanded key schedule)
#   ~enc: K -> CmBlock -> CmBlock     encryption of one block
#   ~dec: K -> CmBlock -> CmBlock     decryption of one block (CBC, XTS only)
# and the key itself as +k: K. The modes never look inside K, so they run on
# any cipher with 128-bit blocks; aes.bend supplies AES-128 and AES-256.
#
# A CmBlock is four 32-bit words, big-endian: w0 holds bytes 0 to 3 of the
# block, byte 0 in its top 8 bits. Every value of the type is a block (there is
# no out-of-range byte), so a cipher's "decryption inverts encryption" can be
# stated for every block. The type is open: a cipher adapter may build and
# match blocks directly.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W

type CmBlock is Data:
  CmBlock{w0: U32, w1: U32, w2: U32, w3: U32}

# Every failure a mode can report
type CmError is Data:
  CmBadKeyLength{got: Nat}
  CmBadIvLength{got: Nat}
  CmBadTweakLength{got: Nat}
  CmBadNonceLength{got: Nat}
  CmBadTagLength{got: Nat}
  CmBadBlockSize{got: Nat}
  CmNotBlockMultiple{len: Nat}
  CmTooShort{len: Nat}
  CmTooLong{len: Nat}
  CmBadPadding{}
  CmTagMismatch{}

# Blocks

def CmBlock.zero() -> CmBlock:
  CmBlock{0, 0, 0, 0}

def CmBlock.xor(a: CmBlock, b: CmBlock) -> CmBlock:
  match a b:
    case CmBlock{a0, a1, a2, a3} CmBlock{b0, b1, b2, b3}:
      CmBlock{U32.xor(a0, b0), U32.xor(a1, b1), U32.xor(a2, b2), U32.xor(a3, b3)}

# Each block of xs encrypted under k and decrypted again: xs itself for
# every list exactly where decryption undoes encryption at k, which is how
# the round-trip laws (LAWS.bend) take that property of the cipher
def CmBlock.dec_enc(~K: Data, ~enc: K -> CmBlock -> CmBlock, ~dec: K -> CmBlock -> CmBlock, +k: K, xs: List<&2, CmBlock>) -> List<&2, CmBlock>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{dec(k, enc(k, x)), CmBlock.dec_enc(~K, ~enc, ~dec, k, t)}

# Bytes and words (internal). Words are split into bytes and joined back by
# bit slicing (bend-osdev-word64's W64.bits), not by shifts and masks, so that
# the round trips can be proved for every word.

# a byte (the low 8 bits of x), as bend-osdev-bytes masks it
def cm.byte(x: U32) -> U32:
  B.byte(x)

def cm.bits8(b: U32) -> Word(8n):
  match b:
    case U32{w}:
      W.W64.bits.lo(8n, 24n, w)

def cm.of8(s: Word(8n)) -> U32:
  U32{W.W64.bits.cat(8n, 24n, s, Word.zero(24n))}

# the word with bytes a, b, c, d, most significant first
def cm.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32{W.W64.bits.cat(8n, 24n, cm.bits8(d), W.W64.bits.cat(8n, 16n, cm.bits8(c), W.W64.bits.cat(8n, 8n, cm.bits8(b), cm.bits8(a))))}

# the bytes of w, most significant first
def cm.b0(w: U32) -> U32:
  match w:
    case U32{x}:
      cm.of8(W.W64.bits.hi(8n, 8n, W.W64.bits.hi(8n, 16n, W.W64.bits.hi(8n, 24n, x))))

def cm.b1(w: U32) -> U32:
  match w:
    case U32{x}:
      cm.of8(W.W64.bits.lo(8n, 8n, W.W64.bits.hi(8n, 16n, W.W64.bits.hi(8n, 24n, x))))

def cm.b2(w: U32) -> U32:
  match w:
    case U32{x}:
      cm.of8(W.W64.bits.lo(8n, 16n, W.W64.bits.hi(8n, 24n, x)))

def cm.b3(w: U32) -> U32:
  match w:
    case U32{x}:
      cm.of8(W.W64.bits.lo(8n, 24n, x))

# the four bytes of w, most significant first, in front of rest
def cm.unword(+w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  Con{cm.b0(w), Con{cm.b1(w), Con{cm.b2(w), Con{cm.b3(w), rest}}}}

def cm.w0(b: CmBlock) -> U32:
  match b:
    case CmBlock{w0, w1, w2, w3}:
      w0

def cm.w1(b: CmBlock) -> U32:
  match b:
    case CmBlock{w0, w1, w2, w3}:
      w1

def cm.w2(b: CmBlock) -> U32:
  match b:
    case CmBlock{w0, w1, w2, w3}:
      w2

def cm.w3(b: CmBlock) -> U32:
  match b:
    case CmBlock{w0, w1, w2, w3}:
      w3

# the 16 bytes of a block in front of rest (always 16 cells, whatever b is)
def cm.bytes_onto(+b: CmBlock, rest: List<&2, U32>) -> List<&2, U32>:
  cm.unword(cm.w0(b), cm.unword(cm.w1(b), cm.unword(cm.w2(b), cm.unword(cm.w3(b), rest))))

def cm.bytes_of(b: CmBlock) -> List<&2, U32>:
  cm.bytes_onto(b, Nil{})

def cm.block16(a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32, a8: U32, a9: U32, a10: U32, a11: U32, a12: U32, a13: U32, a14: U32, a15: U32) -> CmBlock:
  CmBlock{cm.word(a0, a1, a2, a3), cm.word(a4, a5, a6, a7), cm.word(a8, a9, a10, a11), cm.word(a12, a13, a14, a15)}

def cm.block_of.full(xs: List<&2, U32>) -> CmBlock:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, t}}}}}}}}}}}}}}}}:
      cm.block16(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15)
    case _:
      CmBlock.zero()

# the block of the first 16 bytes of xs, zero-filled if xs is shorter
def cm.block_of(xs: List<&2, U32>) -> CmBlock:
  cm.block_of.full(B.append(B.take(16n, xs), B.zeros(16n)))

# A byte string as its whole blocks and the 0 to 15 bytes after them
type CmSplit is Data:
  CmSplit{blocks: List<&2, CmBlock>, tail: List<&2, U32>}

def cm.split.cons(b: CmBlock, s: CmSplit) -> CmSplit:
  match s:
    case CmSplit{bs, t}:
      CmSplit{Con{b, bs}, t}

def cm.split(+xs: List<&2, U32>) -> CmSplit:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, t}}}}}}}}}}}}}}}}:
      cm.split.cons(cm.block16(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15), cm.split(t))
    case _:
      CmSplit{Nil{}, xs}

def cm.split.blocks(s: CmSplit) -> List<&2, CmBlock>:
  match s:
    case CmSplit{bs, t}:
      bs

def cm.split.tail(s: CmSplit) -> List<&2, U32>:
  match s:
    case CmSplit{bs, t}:
      t

# the bytes of the blocks bs, in front of rest
def cm.join_onto(bs: List<&2, CmBlock>, rest: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      rest
    case Con{b, t}:
      cm.bytes_onto(b, cm.join_onto(t, rest))

def cm.join(bs: List<&2, CmBlock>) -> List<&2, U32>:
  cm.join_onto(bs, Nil{})

# byte-wise XOR, as long as the shorter list
def cm.xor_bytes(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      Con{cm.byte(U32.xor(a, b)), cm.xor_bytes(s, t)}
    case _ _:
      Nil{}

# the OR of the byte-wise XORs: 0 exactly when the lists agree, computed
# without stopping at the first difference
# The same, tail-recursive. Bend 2.0.37's runtime overflows its stack at some
# tens of thousands of nested non-tail calls, so the structural forms above,
# which the proofs reason about, cannot run on long messages; the modes run
# these instead, and PROOF.bend proves each equal to its structural form for
# every input.

# the blocks of bs in reverse order, in front of acc
def cm.blocks.rev_onto(bs: List<&2, CmBlock>, acc: List<&2, CmBlock>) -> List<&2, CmBlock>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      cm.blocks.rev_onto(t, Con{b, acc})

def cm.blocks.len.go(bs: List<&2, CmBlock>, n: Nat) -> Nat:
  match bs:
    case Nil{}:
      n
    case Con{b, t}:
      cm.blocks.len.go(t, 1n+n)

# the number of blocks (List.length)
def cm.blocks.len(bs: List<&2, CmBlock>) -> Nat:
  cm.blocks.len.go(bs, 0n)

# xs, then ys (List.append)
def cm.blocks.append(xs: List<&2, CmBlock>, ys: List<&2, CmBlock>) -> List<&2, CmBlock>:
  cm.blocks.rev_onto(cm.blocks.rev_onto(xs, Nil{}), ys)

# the blocks split so far are kept reversed in acc (cm.split)
def cm.split.go(+xs: List<&2, U32>, acc: List<&2, CmBlock>) -> CmSplit:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, t}}}}}}}}}}}}}}}}:
      cm.split.go(t, Con{cm.block16(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15), acc})
    case _:
      CmSplit{cm.blocks.rev_onto(acc, Nil{}), xs}

def cm.split.fast(+xs: List<&2, U32>) -> CmSplit:
  cm.split.go(xs, Nil{})

# the bytes of the blocks rs (last first) in front of acc
def cm.join.go(rs: List<&2, CmBlock>, acc: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      acc
    case Con{b, t}:
      cm.join.go(t, cm.bytes_onto(b, acc))

# cm.join_onto
def cm.join_onto.fast(bs: List<&2, CmBlock>, rest: List<&2, U32>) -> List<&2, U32>:
  cm.join.go(cm.blocks.rev_onto(bs, Nil{}), rest)

def cm.xor_bytes.go(xs: List<&2, U32>, ys: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{a, s} Con{b, t}:
      cm.xor_bytes.go(s, t, Con{cm.byte(U32.xor(a, b)), acc})
    case _ _:
      B.rev(acc)

# cm.xor_bytes
def cm.xor_bytes.fast(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  cm.xor_bytes.go(xs, ys, Nil{})

def cm.diff(xs: List<&2, U32>, ys: List<&2, U32>, acc: U32) -> U32:
  match xs ys:
    case Con{a, s} Con{b, t}:
      cm.diff(s, t, U32.or(acc, cm.byte(U32.xor(a, b))))
    case Nil{} Nil{}:
      acc
    case _ _:
      1

# equality of two byte lists with no early exit of the same length (a tag check)
def cm.ct_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  U32.is_eq(cm.diff(xs, ys, 0), 0)

# 0 for a 0 bit, all ones for a 1 bit (the low bit of b)
def cm.mask(b: U32) -> U32:
  U32.sub(0, U32.and(1, b))

# Checks, as steps of a Result block

def cm.check(ok: Bool, e: CmError) -> Result<&2, &2, CmError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# a 16-byte value as a block, or the error e
def cm.need_block.pick(ok: Bool, xs: List<&2, U32>, e: CmError) -> Result<&2, &2, CmError, CmBlock>:
  match ok:
    case True{}:
      Done{cm.block_of(xs)}
    case False{}:
      Fail{e}

def cm.need_block(+xs: List<&2, U32>, e: CmError) -> Result<&2, &2, CmError, CmBlock>:
  cm.need_block.pick(Nat.is_eq(B.len(xs), 16n), xs, e)

# Blocks as byte strings

def CmBlock.to_octets(b: CmBlock) -> B.Octets:
  B.Octets.of_list(cm.bytes_of(b))

def CmBlock.of_octets.pick(ok: Bool, xs: List<&2, U32>) -> Maybe<&2, CmBlock>:
  match ok:
    case True{}:
      Some{cm.block_of(xs)}
    case False{}:
      None{}

# a 16-byte string as a block; None for any other length
def CmBlock.of_octets(o: B.Octets) -> Maybe<&2, CmBlock>:
  +xs = B.Octets.to_list(o)
  CmBlock.of_octets.pick(Nat.is_eq(B.len(xs), 16n), xs)

def CmBlock.hex(b: CmBlock) -> String:
  B.hex(cm.bytes_of(b))
