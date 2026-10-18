# bend-osdev-gf, GF(2^128): the field of GCM's GHASH (NIST SP 800-38D) and
# of the tweak arithmetic in XTS (IEEE Std 1619), LRW and CMAC (NIST SP
# 800-38B), all modulo x^128 + x^7 + x^2 + x + 1, in the three bit orders
# they use.
#
# A Gf128 is a 16-byte block as four big-endian 32-bit words: byte 0 is the
# top byte of w0, byte 15 the bottom byte of w3. The bit orders:
#
#  * GCM (SP 800-38D, 6.3): bit 0 of the block, the most significant bit
#    of byte 0, is the coefficient of x^0; bit 127, the least significant
#    bit of byte 15, that of x^127. Multiplying by x shifts the block right
#    one bit, and a bit falling off the end adds R = 0xE1 || 0^120.
#  * big-endian (CMAC's doubling, SP 800-38B 6.1; LRW): the block is a
#    128-bit big-endian number whose bit i is the coefficient of x^i.
#    Multiplying by x shifts it left one bit, and a carry adds 0x87.
#  * little-endian (XTS, IEEE 1619 5.2): the block is a 128-bit
#    little-endian number (byte 0 least significant); multiplying by x
#    shifts it left one bit, and a carry adds 0x87 to byte 0.
import Base
import ../bytes/bytes.bend as B

type Gf128 is Data:
  Gf128{w0: U32, w1: U32, w2: U32, w3: U32}

type Gf128Error is Data:
  Gf128BadLength{got: Nat}

def Gf128.zero() -> Gf128:
  Gf128{0, 0, 0, 0}

def Gf128.of_words(w0: U32, w1: U32, w2: U32, w3: U32) -> Gf128:
  Gf128{w0, w1, w2, w3}

def Gf128.words(x: Gf128) -> List<&2, U32>:
  match x:
    case Gf128{w0, w1, w2, w3}:
      [w0, w1, w2, w3]

def Gf128.xor(a: Gf128, b: Gf128) -> Gf128:
  match a b:
    case Gf128{a0, a1, a2, a3} Gf128{b0, b1, b2, b3}:
      Gf128{U32.xor(a0, b0), U32.xor(a1, b1), U32.xor(a2, b2), U32.xor(a3, b3)}

def Gf128.is_eq(a: Gf128, b: Gf128) -> Bool:
  match a b:
    case Gf128{a0, a1, a2, a3} Gf128{b0, b1, b2, b3}:
      Bool.and(U32.is_eq(a0, b0), Bool.and(U32.is_eq(a1, b1), Bool.and(U32.is_eq(a2, b2), U32.is_eq(a3, b3))))

# Bytes

def gf128.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32.or(U32.shln(U32.and(255, a), 24n), U32.or(U32.shln(U32.and(255, b), 16n), U32.or(U32.shln(U32.and(255, c), 8n), U32.and(255, d))))

def gf128.of_list.go(xs: List<&2, U32>) -> Gf128:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, t}}}}}}}}}}}}}}}}:
      Gf128{gf128.word(a0, a1, a2, a3), gf128.word(a4, a5, a6, a7), gf128.word(a8, a9, a10, a11), gf128.word(a12, a13, a14, a15)}
    case o:
      Gf128.zero()

def gf128.of_list.pick(ok: Bool, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, Gf128Error, Gf128>:
  match ok:
    case True{}:
      Done{gf128.of_list.go(xs)}
    case False{}:
      Fail{Gf128BadLength{n}}

# the block of 16 bytes (any other length is refused)
def Gf128.of_octets(+o: B.Octets) -> Result<&2, &2, Gf128Error, Gf128>:
  +n = B.Octets.len(o)
  gf128.of_list.pick(Nat.is_eq(n, 16n), n, B.Octets.to_list(o))

def Gf128.to_octets(x: Gf128) -> B.Octets:
  match x:
    case Gf128{w0, w1, w2, w3}:
      B.Octets.concat([B.Octets.be32(w0), B.Octets.be32(w1), B.Octets.be32(w2), B.Octets.be32(w3)])

def Gf128.hex(x: Gf128) -> String:
  B.Octets.hex(Gf128.to_octets(x))

# all ones if the low bit of b is set, else 0
def gf128.mask(b: U32) -> U32:
  U32.sub(0, U32.and(b, 1))

def Gf128.and_mask(a: Gf128, +m: U32) -> Gf128:
  match a:
    case Gf128{w0, w1, w2, w3}:
      Gf128{U32.and(w0, m), U32.and(w1, m), U32.and(w2, m), U32.and(w3, m)}

# Multiplication by x

# GCM's order: shift right one bit; bit 127 falling off adds 0xE1 to byte 0
def Gf128.mul_x_gcm(v: Gf128) -> Gf128:
  match v:
    case Gf128{+w0, +w1, +w2, +w3}:
      Gf128{U32.xor(U32.shr(w0), U32.and(3774873600, gf128.mask(w3))), U32.or(U32.shr(w1), U32.shln(w0, 31n)), U32.or(U32.shr(w2), U32.shln(w1, 31n)), U32.or(U32.shr(w3), U32.shln(w2, 31n))}

# big-endian (CMAC's doubling, LRW): shift left one bit; a carry adds 0x87
# to byte 15
def Gf128.double_be(v: Gf128) -> Gf128:
  match v:
    case Gf128{+w0, +w1, +w2, +w3}:
      Gf128{U32.or(U32.shl(w0), U32.shrn(w1, 31n)), U32.or(U32.shl(w1), U32.shrn(w2, 31n)), U32.or(U32.shl(w2), U32.shrn(w3, 31n)), U32.xor(U32.shl(w3), U32.and(135, gf128.mask(U32.shrn(w0, 31n))))}

# little-endian (XTS): every byte shifts left one bit, taking the top bit of
# the byte before it; the top bit of byte 15 adds 0x87 to byte 0

# each byte of w shifted left, with the carries between w's own bytes
def gf128.le.shift(+w: U32) -> U32:
  U32.or(U32.and(4278124286, U32.shl(w)), U32.and(65793, U32.shrn(w, 15n)))

# the carry out of w's last byte, into the first byte of the next word
def gf128.le.carry(w: U32) -> U32:
  U32.shln(U32.and(128, w), 17n)

def Gf128.double_le(v: Gf128) -> Gf128:
  match v:
    case Gf128{+w0, +w1, +w2, +w3}:
      Gf128{U32.xor(gf128.le.shift(w0), U32.and(2264924160, gf128.mask(U32.shrn(w3, 7n)))), U32.or(gf128.le.shift(w1), gf128.le.carry(w0)), U32.or(gf128.le.shift(w2), gf128.le.carry(w1)), U32.or(gf128.le.shift(w3), gf128.le.carry(w2))}

# GCM's multiplication (SP 800-38D, Algorithm 1): Z = 0, V = Y; for each
# bit X_i of X, from bit 0: if X_i, Z = Z + V; then V = V * x

def gf128.gcm.bit(+x: U32, zv: Gf128 & Gf128) -> Gf128 & Gf128:
  (z, +v) = zv
  (Gf128.xor(z, Gf128.and_mask(v, gf128.mask(U32.shrn(x, 31n)))), Gf128.mul_x_gcm(v))

# the 32 bits of the word x, from its top bit
def gf128.gcm.word(n: Nat, +x: U32, zv: Gf128 & Gf128) -> Gf128 & Gf128:
  match n:
    case 0n:
      zv
    case 1n+k:
      gf128.gcm.word(k, U32.shl(x), gf128.gcm.bit(x, zv))

def gf128.fst(p: Gf128 & Gf128) -> Gf128:
  (a, b) = p
  a

def Gf128.mul_gcm(x: Gf128, y: Gf128) -> Gf128:
  match x:
    case Gf128{w0, w1, w2, w3}:
      gf128.fst(gf128.gcm.word(32n, w3, gf128.gcm.word(32n, w2, gf128.gcm.word(32n, w1, gf128.gcm.word(32n, w0, (Gf128.zero(), y))))))

# GHASH (SP 800-38D, 6.4): Y = (Y + X_i) * H for each block X_i
def Gf128.ghash_update(+h: Gf128, y: Gf128, x: Gf128) -> Gf128:
  Gf128.mul_gcm(Gf128.xor(y, x), h)

def Gf128.ghash.go(xs: List<&2, Gf128>, +h: Gf128, y: Gf128) -> Gf128:
  match xs:
    case Nil{}:
      y
    case Con{x, rest}:
      Gf128.ghash.go(rest, h, Gf128.ghash_update(h, y, x))

def Gf128.ghash(+h: Gf128, xs: List<&2, Gf128>) -> Gf128:
  Gf128.ghash.go(xs, h, Gf128.zero())

# The big-endian multiplication (LRW): Horner's rule over the bits of b,
# from the top: z = z * x + bit * a

def gf128.be.word(n: Nat, +x: U32, +a: Gf128, z: Gf128) -> Gf128:
  match n:
    case 0n:
      z
    case 1n+k:
      gf128.be.word(k, U32.shl(x), a, Gf128.xor(Gf128.double_be(z), Gf128.and_mask(a, gf128.mask(U32.shrn(x, 31n)))))

def Gf128.mul_be(+a: Gf128, b: Gf128) -> Gf128:
  match b:
    case Gf128{w0, w1, w2, w3}:
      gf128.be.word(32n, w3, a, gf128.be.word(32n, w2, a, gf128.be.word(32n, w1, a, gf128.be.word(32n, w0, a, Gf128.zero()))))
