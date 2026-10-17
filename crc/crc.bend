# bend-osdev-crc: cyclic redundancy checks, in the Rocksoft parameter model
# (Ross Williams, "A Painless Guide to CRC Error Detection Algorithms", 1993;
# the catalogue of parameters at reveng.sourceforge.io).
#
# A CRC is fixed by its width, polynomial (in normal, most-significant-first
# form), initial register value, bit order, and final XOR. Crc32Spec covers
# widths 8 to 32 on U32; Crc64Spec covers width 64 on W64. Every CRC here
# reads its input bytes in the same order it writes its result (refin =
# refout), as all the CRCs below do.
#
# The kernel's CRCs as named variants: crc32c (iSCSI, ext4, btrfs), crc16 (the
# ARC variant: ext4's group descriptors), crc_t10dif (SCSI data integrity),
# crc64_ecma, crc64_xz and crc64_nvme. crc32 (ISO-HDLC) is here as a
# cross-check against implementations outside this repository.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

type Crc32Spec is Data:
  Crc32Spec{width: Nat, poly: U32, init: U32, reflected: Bool, xorout: U32}

type Crc64Spec is Data:
  Crc64Spec{poly: W.W64, init: W.W64, reflected: Bool, xorout: W.W64}

# Reflection: the low n bits of a word in reverse order

def reflect32.go(n: Nat, +x: U32, r: U32) -> U32:
  match n:
    case 0n:
      r
    case 1n+p:
      reflect32.go(p, U32.shr(x), U32.or(U32.shl(r), U32.and(x, 1)))

def reflect32(x: U32, n: Nat) -> U32:
  reflect32.go(n, x, 0)

def reflect64.go(n: Nat, +x: W.W64, r: W.W64) -> W.W64:
  match n:
    case 0n:
      r
    case 1n+p:
      reflect64.go(p, W.W64.shr(x, 1n), W.W64.or(W.W64.shl(r, 1n), W.W64.and(x, W.W64.one())))

def reflect64(x: W.W64) -> W.W64:
  reflect64.go(64n, x, W.W64.zero())

# The 32-bit engine, least significant bit first (reflected)

def r32.pick(odd: Bool, +poly: U32, c: U32) -> U32:
  match odd:
    case True{}:
      U32.xor(U32.shr(c), poly)
    case False{}:
      U32.shr(c)

def r32.bits(n: Nat, +poly: U32, +c: U32) -> U32:
  match n:
    case 0n:
      c
    case 1n+p:
      r32.bits(p, poly, r32.pick(U32.is_eq(U32.and(c, 1), 1), poly, c))

# the register after the bytes xs, from register c (poly reflected)
def r32.raw(xs: List<&2, U32>, +poly: U32, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{h, t}:
      r32.raw(t, poly, r32.bits(8n, poly, U32.xor(c, U32.and(h, 255))))

# The 32-bit engine, most significant bit first

def n32.pick(top: Bool, +poly: U32, +mask: U32, c: U32) -> U32:
  match top:
    case True{}:
      U32.and(U32.xor(U32.shl(c), poly), mask)
    case False{}:
      U32.and(U32.shl(c), mask)

def n32.bits(n: Nat, +poly: U32, +topbit: U32, +mask: U32, +c: U32) -> U32:
  match n:
    case 0n:
      c
    case 1n+p:
      n32.bits(p, poly, topbit, mask, n32.pick(Bool.not(U32.is_eq(U32.and(c, topbit), 0)), poly, mask, c))

# the register after the bytes xs, from register c; shift is width - 8
def n32.raw(xs: List<&2, U32>, +poly: U32, +shift: Nat, +topbit: U32, +mask: U32, c: U32) -> U32:
  match xs:
    case Nil{}:
      c
    case Con{h, t}:
      n32.raw(t, poly, shift, topbit, mask, n32.bits(8n, poly, topbit, mask, U32.xor(c, U32.shln(U32.and(h, 255), shift))))

# The 64-bit engines

def r64.pick(odd: Bool, +poly: W.W64, c: W.W64) -> W.W64:
  match odd:
    case True{}:
      W.W64.xor(W.W64.shr(c, 1n), poly)
    case False{}:
      W.W64.shr(c, 1n)

def r64.bits(n: Nat, +poly: W.W64, +c: W.W64) -> W.W64:
  match n:
    case 0n:
      c
    case 1n+p:
      r64.bits(p, poly, r64.pick(U32.is_eq(U32.and(W.W64.lo(c), 1), 1), poly, c))

def r64.raw(xs: List<&2, U32>, +poly: W.W64, c: W.W64) -> W.W64:
  match xs:
    case Nil{}:
      c
    case Con{h, t}:
      r64.raw(t, poly, r64.bits(8n, poly, W.W64.xor(c, W.W64.from_u32(U32.and(h, 255)))))

def n64.pick(top: Bool, +poly: W.W64, c: W.W64) -> W.W64:
  match top:
    case True{}:
      W.W64.xor(W.W64.shl(c, 1n), poly)
    case False{}:
      W.W64.shl(c, 1n)

def n64.bits(n: Nat, +poly: W.W64, +c: W.W64) -> W.W64:
  match n:
    case 0n:
      c
    case 1n+p:
      n64.bits(p, poly, n64.pick(Bool.not(U32.is_eq(U32.and(W.W64.hi(c), 2147483648), 0)), poly, c))

def n64.raw(xs: List<&2, U32>, +poly: W.W64, c: W.W64) -> W.W64:
  match xs:
    case Nil{}:
      c
    case Con{h, t}:
      n64.raw(t, poly, n64.bits(8n, poly, W.W64.xor(c, W.W64.from_parts(U32.shln(U32.and(h, 255), 24n), 0))))

# The generic CRCs

# the register after the bytes xs, from register c, without the final XOR:
# what a caller that computes a CRC in pieces passes from one piece to the next
def Crc32Spec.update.go(reflected: Bool, +width: Nat, poly: U32, c: U32, xs: List<&2, U32>) -> U32:
  match reflected:
    case True{}:
      r32.raw(xs, reflect32(poly, width), c)
    case False{}:
      +shift = Nat.sub(width, 8n)
      n32.raw(xs, poly, shift, U32.shln(1, Nat.sub(width, 1n)), U32.sub(U32.shln(1, width), 1), c)

def Crc32Spec.update(spec: Crc32Spec, c: U32, o: B.Octets) -> U32:
  match spec:
    case Crc32Spec{+width, poly, init, reflected, xorout}:
      Crc32Spec.update.go(reflected, width, poly, c, B.Octets.to_list(o))

# the register a CRC starts from
def Crc32Spec.start.go(reflected: Bool, init: U32, width: Nat) -> U32:
  match reflected:
    case True{}:
      reflect32(init, width)
    case False{}:
      init

def Crc32Spec.start(spec: Crc32Spec) -> U32:
  match spec:
    case Crc32Spec{+width, poly, init, reflected, xorout}:
      Crc32Spec.start.go(reflected, init, width)

def Crc32Spec.finish(spec: Crc32Spec, c: U32) -> U32:
  match spec:
    case Crc32Spec{width, poly, init, reflected, xorout}:
      U32.xor(c, xorout)

def Crc32Spec.compute(+spec: Crc32Spec, xs: B.Octets) -> U32:
  Crc32Spec.finish(spec, Crc32Spec.update(spec, Crc32Spec.start(spec), xs))

def Crc64Spec.update.go(reflected: Bool, poly: W.W64, c: W.W64, xs: List<&2, U32>) -> W.W64:
  match reflected:
    case True{}:
      r64.raw(xs, reflect64(poly), c)
    case False{}:
      n64.raw(xs, poly, c)

def Crc64Spec.update(spec: Crc64Spec, c: W.W64, o: B.Octets) -> W.W64:
  match spec:
    case Crc64Spec{poly, init, reflected, xorout}:
      Crc64Spec.update.go(reflected, poly, c, B.Octets.to_list(o))

def Crc64Spec.start.go(reflected: Bool, init: W.W64) -> W.W64:
  match reflected:
    case True{}:
      reflect64(init)
    case False{}:
      init

def Crc64Spec.start(spec: Crc64Spec) -> W.W64:
  match spec:
    case Crc64Spec{poly, init, reflected, xorout}:
      Crc64Spec.start.go(reflected, init)

def Crc64Spec.finish(spec: Crc64Spec, c: W.W64) -> W.W64:
  match spec:
    case Crc64Spec{poly, init, reflected, xorout}:
      W.W64.xor(c, xorout)

def Crc64Spec.compute(+spec: Crc64Spec, xs: B.Octets) -> W.W64:
  Crc64Spec.finish(spec, Crc64Spec.update(spec, Crc64Spec.start(spec), xs))

# The named CRCs (parameters from the reveng catalogue)

# CRC-32C (Castagnoli): poly 0x1EDC6F41
def crc32c.spec() -> Crc32Spec:
  Crc32Spec{32n, 517762881, 4294967295, True{}, 4294967295}

# CRC-32 (ISO-HDLC, as zlib and Ethernet): poly 0x04C11DB7
def crc32.spec() -> Crc32Spec:
  Crc32Spec{32n, 79764919, 4294967295, True{}, 4294967295}

# CRC-16/ARC (the kernel's crc16): poly 0x8005
def crc16.spec() -> Crc32Spec:
  Crc32Spec{16n, 32773, 0, True{}, 0}

# CRC-16/T10-DIF: poly 0x8BB7
def crc_t10dif.spec() -> Crc32Spec:
  Crc32Spec{16n, 35767, 0, False{}, 0}

# CRC-64/ECMA-182: poly 0x42F0E1EBA9EA3693, most significant bit first
def crc64_ecma.spec() -> Crc64Spec:
  Crc64Spec{W.W64.from_parts(1123082731, 2850698899), W.W64.zero(), False{}, W.W64.zero()}

# CRC-64/XZ: the same polynomial, reflected, as the XZ format's check
def crc64_xz.spec() -> Crc64Spec:
  Crc64Spec{W.W64.from_parts(1123082731, 2850698899), W.W64.max(), True{}, W.W64.max()}

# CRC-64/NVME: poly 0xAD93D23594C93659
def crc64_nvme.spec() -> Crc64Spec:
  Crc64Spec{W.W64.from_parts(2912145973, 2496214617), W.W64.max(), True{}, W.W64.max()}

def crc32c(xs: B.Octets) -> U32:
  Crc32Spec.compute(crc32c.spec(), xs)

def crc32(xs: B.Octets) -> U32:
  Crc32Spec.compute(crc32.spec(), xs)

def crc16(xs: B.Octets) -> U32:
  Crc32Spec.compute(crc16.spec(), xs)

def crc_t10dif(xs: B.Octets) -> U32:
  Crc32Spec.compute(crc_t10dif.spec(), xs)

def crc64_ecma(xs: B.Octets) -> W.W64:
  Crc64Spec.compute(crc64_ecma.spec(), xs)

def crc64_xz(xs: B.Octets) -> W.W64:
  Crc64Spec.compute(crc64_xz.spec(), xs)

def crc64_nvme(xs: B.Octets) -> W.W64:
  Crc64Spec.compute(crc64_nvme.spec(), xs)
