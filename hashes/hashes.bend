# bend-osdev-hashes: the Merkle-Damgard engine every hash of this package
# streams through, and the word types and byte orders they share.
#
# A hash of this shape keeps a chaining value (any type C) and compresses
# the message a block at a time (~compress: C -> the block's bytes -> C).
# The engine holds the bytes of the unfinished block, how many there are,
# and how many blocks it has compressed; its update takes bytes one at a
# time, and compresses when a block is full. Because update is a fold over
# the bytes, feeding a ++ b is feeding a and then b, from every state
# (LAWS.bend: md_streaming), whatever the compression function; each hash's
# split law (streaming in any pieces equals the one-shot digest) follows.
#
# Each algorithm's file supplies its chaining value, compression function,
# and final step (the padding, and the digest from the chaining value):
#   md4.bend (RFC 1320), md5.bend (RFC 1321), sha1.bend (FIPS 180-4),
#   ripemd160.bend (Dobbertin, Bosselaers, Preneel), sm3.bend (GB/T 32905),
#   streebog.bend (RFC 6986), michael.bend (IEEE 802.11i's MIC).
# The block size is a parameter (~last: the block size less one, a power of
# two less one for HsMd.md_pad), so 64-byte blocks (all the hashes) and the
# 4-byte words of Michael run through the same engine.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W

# The package's errors: a key of a length the algorithm does not take
type HsError is Data:
  HsBadKeyLength{got: Nat}

# The engine's state (opaque): the chaining value, the bytes of the
# unfinished block (last first), how many there are, and the number of
# blocks compressed
type HsMdState<-C: Data> is Data:
  HsMdState{cv: C, buf: List<&2, U32>, cnt: U32, nb: W.W64}

# Chaining values of two, four, five and eight 32-bit words (open types)
type HsW2 is Data:
  HsW2{a: U32, b: U32}

type HsW4 is Data:
  HsW4{a: U32, b: U32, c: U32, d: U32}

type HsW5 is Data:
  HsW5{a: U32, b: U32, c: U32, d: U32, e: U32}

type HsW8 is Data:
  HsW8{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

# The sixteen words of a 64-byte block (internal to the package)
type HsW16 is Data:
  HsW16{x0: U32, x1: U32, x2: U32, x3: U32, x4: U32, x5: U32, x6: U32, x7: U32, x8: U32, x9: U32, x10: U32, x11: U32, x12: U32, x13: U32, x14: U32, x15: U32}

# Words, natively (bulk data: bytes' field readers are for headers)

# x rotated left by n (1 to 31)
def hs.rotl(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shln(x, n), U32.shrn(x, Nat.sub(32n, n)))

# the word with bytes a (least significant), b, c, d
def hs.le(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))

# the word with bytes a (most significant), b, c, d
def hs.be(a: U32, b: U32, c: U32, d: U32) -> U32:
  hs.le(d, c, b, a)

# A block's sixteen words, little-endian (MD4, MD5, RIPEMD-160) or
# big-endian (SHA-1, SM3); a block of another length gives zeros (the engine
# passes only whole blocks)
def hs.block.le(blk: List<&2, U32>) -> HsW16:
  match blk:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, Con{b8, Con{b9, Con{b10, Con{b11, Con{b12, Con{b13, Con{b14, Con{b15, Con{b16, Con{b17, Con{b18, Con{b19, Con{b20, Con{b21, Con{b22, Con{b23, Con{b24, Con{b25, Con{b26, Con{b27, Con{b28, Con{b29, Con{b30, Con{b31, Con{b32, Con{b33, Con{b34, Con{b35, Con{b36, Con{b37, Con{b38, Con{b39, Con{b40, Con{b41, Con{b42, Con{b43, Con{b44, Con{b45, Con{b46, Con{b47, Con{b48, Con{b49, Con{b50, Con{b51, Con{b52, Con{b53, Con{b54, Con{b55, Con{b56, Con{b57, Con{b58, Con{b59, Con{b60, Con{b61, Con{b62, Con{b63, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      HsW16{hs.le(b0, b1, b2, b3), hs.le(b4, b5, b6, b7), hs.le(b8, b9, b10, b11), hs.le(b12, b13, b14, b15), hs.le(b16, b17, b18, b19), hs.le(b20, b21, b22, b23), hs.le(b24, b25, b26, b27), hs.le(b28, b29, b30, b31), hs.le(b32, b33, b34, b35), hs.le(b36, b37, b38, b39), hs.le(b40, b41, b42, b43), hs.le(b44, b45, b46, b47), hs.le(b48, b49, b50, b51), hs.le(b52, b53, b54, b55), hs.le(b56, b57, b58, b59), hs.le(b60, b61, b62, b63)}
    case _:
      HsW16{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

def hs.block.be(blk: List<&2, U32>) -> HsW16:
  match blk:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, Con{b8, Con{b9, Con{b10, Con{b11, Con{b12, Con{b13, Con{b14, Con{b15, Con{b16, Con{b17, Con{b18, Con{b19, Con{b20, Con{b21, Con{b22, Con{b23, Con{b24, Con{b25, Con{b26, Con{b27, Con{b28, Con{b29, Con{b30, Con{b31, Con{b32, Con{b33, Con{b34, Con{b35, Con{b36, Con{b37, Con{b38, Con{b39, Con{b40, Con{b41, Con{b42, Con{b43, Con{b44, Con{b45, Con{b46, Con{b47, Con{b48, Con{b49, Con{b50, Con{b51, Con{b52, Con{b53, Con{b54, Con{b55, Con{b56, Con{b57, Con{b58, Con{b59, Con{b60, Con{b61, Con{b62, Con{b63, Nil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      HsW16{hs.be(b0, b1, b2, b3), hs.be(b4, b5, b6, b7), hs.be(b8, b9, b10, b11), hs.be(b12, b13, b14, b15), hs.be(b16, b17, b18, b19), hs.be(b20, b21, b22, b23), hs.be(b24, b25, b26, b27), hs.be(b28, b29, b30, b31), hs.be(b32, b33, b34, b35), hs.be(b36, b37, b38, b39), hs.be(b40, b41, b42, b43), hs.be(b44, b45, b46, b47), hs.be(b48, b49, b50, b51), hs.be(b52, b53, b54, b55), hs.be(b56, b57, b58, b59), hs.be(b60, b61, b62, b63)}
    case _:
      HsW16{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

# The digest bytes of a chaining value: each word little-endian (MD4, MD5,
# RIPEMD-160, Michael) or big-endian (SHA-1, SM3), in order

def HsW2.le(x: HsW2) -> B.Octets:
  match x:
    case HsW2{a, b}:
      B.Octets.of_list(B.append(B.le32(a), B.le32(b)))

def HsW4.le(x: HsW4) -> B.Octets:
  match x:
    case HsW4{a, b, c, d}:
      B.Octets.of_list(B.append(B.le32(a), B.append(B.le32(b), B.append(B.le32(c), B.le32(d)))))

def HsW5.le(x: HsW5) -> B.Octets:
  match x:
    case HsW5{a, b, c, d, e}:
      B.Octets.of_list(B.append(B.le32(a), B.append(B.le32(b), B.append(B.le32(c), B.append(B.le32(d), B.le32(e))))))

def HsW5.be(x: HsW5) -> B.Octets:
  match x:
    case HsW5{a, b, c, d, e}:
      B.Octets.of_list(B.append(B.be32(a), B.append(B.be32(b), B.append(B.be32(c), B.append(B.be32(d), B.be32(e))))))

def HsW8.be(x: HsW8) -> B.Octets:
  match x:
    case HsW8{a, b, c, d, e, f, g, h}:
      B.Octets.of_list(B.append(B.be32(a), B.append(B.be32(b), B.append(B.be32(c), B.append(B.be32(d), B.append(B.be32(e), B.append(B.be32(f), B.append(B.be32(g), B.be32(h)))))))))

# The engine

# the state before any byte, from the initial chaining value
def HsMd.start(~C: Data, cv: C) -> HsMdState<C>:
  HsMdState{cv, Nil{}, 0, W.W64.zero()}

def hs.md.push(~C: Data, ~compress: C -> List<&2, U32> -> C, full: Bool, cv: C, buf: List<&2, U32>, cnt: U32, nb: W.W64) -> HsMdState<C>:
  match full:
    case True{}:
      HsMdState{compress(cv, B.rev(buf)), Nil{}, 0, W.W64.add(nb, W.W64.one())}
    case False{}:
      HsMdState{cv, buf, U32.add(cnt, 1), nb}

# one byte in: a block of last + 1 bytes is compressed when it is full
def hs.md.step(~C: Data, ~compress: C -> List<&2, U32> -> C, ~last: U32, s: HsMdState<C>, b: U32) -> HsMdState<C>:
  match s:
    case HsMdState{cv, buf, +cnt, nb}:
      hs.md.push(~C, ~compress, U32.is_eq(cnt, last), cv, Con{b, buf}, cnt, nb)

def hs.md.feed(~C: Data, ~compress: C -> List<&2, U32> -> C, ~last: U32, xs: List<&2, U32>, s: HsMdState<C>) -> HsMdState<C>:
  match xs:
    case Nil{}:
      s
    case Con{x, t}:
      hs.md.feed(~C, ~compress, ~last, t, hs.md.step(~C, ~compress, ~last, s, x))

# the state after more bytes
def HsMd.update(~C: Data, ~compress: C -> List<&2, U32> -> C, ~last: U32, s: HsMdState<C>, o: B.Octets) -> HsMdState<C>:
  hs.md.feed(~C, ~compress, ~last, B.Octets.to_list(o), s)

# the same, for bytes as a list (each element is taken as it is: callers
# pass bytes)
def HsMd.update_list(~C: Data, ~compress: C -> List<&2, U32> -> C, ~last: U32, s: HsMdState<C>, xs: List<&2, U32>) -> HsMdState<C>:
  hs.md.feed(~C, ~compress, ~last, xs, s)

# The state's parts: the chaining value, the bytes of the unfinished block
# (first first), how many there are, and the number of blocks compressed
def HsMd.cv(~C: Data, s: HsMdState<C>) -> C:
  match s:
    case HsMdState{cv, buf, cnt, nb}:
      cv

def HsMd.pending(~C: Data, s: HsMdState<C>) -> List<&2, U32>:
  match s:
    case HsMdState{cv, buf, cnt, nb}:
      B.rev(buf)

def HsMd.count(~C: Data, s: HsMdState<C>) -> U32:
  match s:
    case HsMdState{cv, buf, cnt, nb}:
      cnt

def HsMd.blocks(~C: Data, s: HsMdState<C>) -> W.W64:
  match s:
    case HsMdState{cv, buf, cnt, nb}:
      nb

# The length so far in bits, modulo 2^64 (blocks of last + 1 bytes)
def HsMd.bits(~C: Data, ~last: U32, +s: HsMdState<C>) -> W.W64:
  W.W64.add(W.W64.mul(HsMd.blocks(~C, s), W.W64.from_u32(U32.shln(U32.add(last, 1), 3n))), W.W64.from_u32(U32.shln(HsMd.count(~C, s), 3n)))

# The length field: eight bytes, little-endian (MD4, MD5, RIPEMD-160) or
# big-endian (SHA-1, SM3)
def hs.len.le(v: W.W64) -> List<&2, U32>:
  B.le64(v)

def hs.len.be(v: W.W64) -> List<&2, U32>:
  B.be64(v)

# The Merkle-Damgard padding after cnt bytes of an unfinished block: the
# byte 0x80, zeros, then the length field, so that the whole is a number of
# blocks (the block size last + 1 a power of two)
def HsMd.md_pad(~last: U32, +cnt: U32, +field: List<&2, U32>) -> List<&2, U32>:
  +k = U32.and(U32.sub(U32.sub(last, U32.from_nat(B.len(field))), cnt), last)
  Con{128, B.append(B.zeros(U32.to_nat(k)), field)}

# The final step of a Merkle-Damgard hash: the padding with the length in
# bits (~field writes it: eight bytes, little- or big-endian), through the
# engine, then the digest of the chaining value (~out)
def HsMd.final_md(~C: Data, ~compress: C -> List<&2, U32> -> C, ~last: U32, ~field: W.W64 -> List<&2, U32>, ~out: C -> B.Octets, +s: HsMdState<C>) -> B.Octets:
  out(HsMd.cv(~C, hs.md.feed(~C, ~compress, ~last, HsMd.md_pad(~last, HsMd.count(~C, s), field(HsMd.bits(~C, ~last, s))), s)))
