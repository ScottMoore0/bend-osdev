# VMAC over any block cipher of at least 128 bits (the block-cipher
# interface, block.bend), as T. Krovetz and W. Dai, "VMAC: Message
# Authentication Code using Universal Hashing" (draft-krovetz-vmac-01, 2007)
# specifies it with AES: a 64- or 128-bit tag (VMAC-64, VMAC-128) of a
# message under a key and a nonce of 1 to 15 bytes.
#
#   KDF(K, index, n): the first n bytes of E(K, index || 0), E(K, index || 1),
#     .. (the index a byte, the counter the block's other bytes, big-endian)
#   VHASH, one 64-bit word per 64 bits of tag (iter = 0, 1):
#     L1: NH over each 128-byte piece of the message (zero-padded to 16
#       bytes): the sum of (m_i + k_i)(m_(i+1) + k_(i+1)) mod 2^126 over the
#       piece's 64-bit words m (little-endian) and the NH key's k
#       (big-endian; KDF index 128, offset by 16 bytes per iter)
#     L2: y = 1, then y = y k + a mod 2^127 - 1 for each NH value a (the
#       poly key k from KDF index 192 with each 32-bit field's top 3 bits
#       cleared; y = k for an empty message), then plus (the message's bit
#       length mod 1024) 2^64
#     L3: ((m1 + k1)(m2 + k2)) mod 2^64 - 257, m1 and m2 y's quotient and
#       remainder by 2^64 - 2^32, k1 and k2 the iter-th pair of 64-bit words
#       of KDF index 224 both below 2^64 - 257
#   PDF: E(K, the nonce left-padded with zeros to a block) (for a 64-bit
#     tag, with the nonce's last bit cleared, and the half that bit picks)
#   the tag: each 64-bit word of the PDF plus the VHASH word, mod 2^64
#
# As a MAC (mac.bend), with the nonce as the message's first nlen bytes
# (CrVmac.mac): ~CrVmacKey<K>, ~CrVmac.key(..), ~CrVmac.mac(..),
# ~CrVmac.verify(..); verify is the interface's named default, so the MAC
# laws hold for VMAC over every cipher (LAWS.bend: vmac_accepts).
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./crypto.bend as Cr
import ./mac.bend as Mc
import ./octets.bend as O

# 128-bit numbers (internal)
type CrU128 is Data:
  CrU128{hi: W.W64, lo: W.W64}

def cr.vm.carry(c: Bool) -> W.W64:
  match c:
    case True{}:
      W.W64.one()
    case False{}:
      W.W64.zero()

def cr.vm.u(+lo: W.W64) -> CrU128:
  CrU128{W.W64.zero(), lo}

# a + b mod 2^128
def cr.vm.add(a: CrU128, b: CrU128) -> CrU128:
  match a b:
    case CrU128{ah, +al} CrU128{bh, bl}:
      +lo = W.W64.add(al, bl)
      CrU128{W.W64.add(W.W64.add(ah, bh), cr.vm.carry(W.W64.is_lt(lo, al))), lo}

def cr.vm.w(+a: U32) -> W.W64:
  W.W64.from_u32(a)

# the 128-bit product of two 64-bit words
def cr.vm.mul(+a: W.W64, +b: W.W64) -> CrU128:
  +al = W.W64.lo(a)
  +ah = W.W64.hi(a)
  +bl = W.W64.lo(b)
  +bh = W.W64.hi(b)
  +p0 = W.W64.mul(cr.vm.w(al), cr.vm.w(bl))
  +p1 = W.W64.mul(cr.vm.w(al), cr.vm.w(bh))
  +p2 = W.W64.mul(cr.vm.w(ah), cr.vm.w(bl))
  +p3 = W.W64.mul(cr.vm.w(ah), cr.vm.w(bh))
  +mid = W.W64.add(p1, p2)
  +lo = W.W64.add(p0, W.W64.shl(mid, 32n))
  CrU128{W.W64.add(W.W64.add(p3, W.W64.shr(mid, 32n)), W.W64.add(W.W64.shl(cr.vm.carry(W.W64.is_lt(mid, p1)), 32n), cr.vm.carry(W.W64.is_lt(lo, p0)))), lo}

# Words of bytes

def cr.vm.at.go(xs: List<&2, U32>, i: Nat) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          cr.vm.at.go(t, p)

def cr.vm.at(+xs: List<&2, U32>, +i: Nat) -> U32:
  B.byte(cr.vm.at.go(xs, i))

def cr.vm.u32be(+xs: List<&2, U32>, +i: Nat) -> U32:
  U32.or(U32.or(U32.shln(cr.vm.at(xs, i), 24n), U32.shln(cr.vm.at(xs, Nat.add(i, 1n)), 16n)), U32.or(U32.shln(cr.vm.at(xs, Nat.add(i, 2n)), 8n), cr.vm.at(xs, Nat.add(i, 3n))))

def cr.vm.u32le(+xs: List<&2, U32>, +i: Nat) -> U32:
  U32.or(U32.or(U32.shln(cr.vm.at(xs, Nat.add(i, 3n)), 24n), U32.shln(cr.vm.at(xs, Nat.add(i, 2n)), 16n)), U32.or(U32.shln(cr.vm.at(xs, Nat.add(i, 1n)), 8n), cr.vm.at(xs, i)))

# the big-endian and the little-endian 64-bit word at byte i
def cr.vm.w64be(+xs: List<&2, U32>, +i: Nat) -> W.W64:
  W.W64.from_parts(cr.vm.u32be(xs, i), cr.vm.u32be(xs, Nat.add(i, 4n)))

def cr.vm.w64le(+xs: List<&2, U32>, +i: Nat) -> W.W64:
  W.W64.from_parts(cr.vm.u32le(xs, Nat.add(i, 4n)), cr.vm.u32le(xs, i))

def cr.vm.word(be: Bool, +xs: List<&2, U32>, +i: Nat) -> W.W64:
  match be:
    case True{}:
      cr.vm.w64be(xs, i)
    case False{}:
      cr.vm.w64le(xs, i)

# n big-endian (be True) or little-endian 64-bit words of xs from byte i
def cr.vm.words(n: Nat, +be: Bool, +xs: List<&2, U32>, +i: Nat) -> List<&2, W.W64>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{cr.vm.word(be, xs, i), cr.vm.words(p, be, xs, Nat.add(i, 8n))}

def cr.vm.bytes64(+w: W.W64) -> List<&2, U32>:
  B.append(B.be32(W.W64.hi(w)), B.be32(W.W64.lo(w)))

# The KDF: the bytes of E(K, index || counter), counter = 0, 1, ..

def cr.vm.encb(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, x: Maybe<&2, Blk>, +o: B.Octets) -> List<&2, U32>:
  match x:
    case None{}:
      B.Octets.to_list(o)
    case Some{b}:
      B.Octets.to_list(blk_to(enc(k, b)))

def cr.vm.e(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +o: B.Octets) -> List<&2, U32>:
  cr.vm.encb(~K, ~Blk, ~enc, ~blk_to, k, blk_of(o), o)

def cr.vm.kdf.go(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, blocks: Nat, +k: K, +index: U32, +c: U32) -> List<&2, U32>:
  match blocks:
    case 0n:
      Nil{}
    case 1n+p:
      +o = B.Octets.of_list(Con{index, B.append(B.zeros(Nat.sub(bsize, 5n)), B.be32(c))})
      B.append(cr.vm.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o), cr.vm.kdf.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, p, k, index, U32.add(c, 1)))

# the first n bytes of the KDF for index
def cr.vm.kdf(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +index: U32, +n: Nat) -> List<&2, U32>:
  B.take(n, cr.vm.kdf.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, Nat.add(Nat.div(n, bsize), 1n), k, index, 0))

# L1: NH, mod 2^126

def cr.vm.nh.go(ms: List<&2, W.W64>, ks: List<&2, W.W64>, y: CrU128) -> CrU128:
  match ms:
    case Con{m0, Con{m1, mt}}:
      match ks:
        case Con{k0, Con{k1, kt}}:
          cr.vm.nh.go(mt, kt, cr.vm.add(y, cr.vm.mul(W.W64.add(m0, k0), W.W64.add(m1, k1))))
        case _:
          y
    case _:
      y

def cr.vm.mod126(x: CrU128) -> CrU128:
  match x:
    case CrU128{h, l}:
      CrU128{W.W64.and(h, W.W64.from_parts(1073741823, 4294967295)), l}

# the NH value of a piece of 1 to 128 bytes (zero-padded to 16 bytes)
def cr.vm.nh(+ks: List<&2, W.W64>, +p: List<&2, U32>) -> CrU128:
  cr.vm.mod126(cr.vm.nh.go(cr.vm.words(Nat.mul(2n, Nat.div(Nat.add(B.len(p), 15n), 16n)), False{}, p, 0n), ks, cr.vm.u(W.W64.zero())))

# L2: arithmetic mod p127 = 2^127 - 1

def cr.vm.m63() -> W.W64:
  W.W64.from_parts(2147483647, 4294967295)

def cr.vm.fold.pick(top: Bool, +h: W.W64, +l: W.W64) -> CrU128:
  match top:
    case True{}:
      cr.vm.add(CrU128{W.W64.and(h, cr.vm.m63()), l}, cr.vm.u(W.W64.one()))
    case False{}:
      CrU128{h, l}

# x below 2^128 to a value congruent mod p127 below 2^127 + 1
def cr.vm.fold(x: CrU128) -> CrU128:
  match x:
    case CrU128{+h, +l}:
      cr.vm.fold.pick(W.W64.is_eq(W.W64.shr(h, 63n), W.W64.one()), h, l)

def cr.vm.norm.pick(p: Bool, +x: CrU128) -> CrU128:
  match p:
    case True{}:
      cr.vm.u(W.W64.zero())
    case False{}:
      x

# x (below 2^127 + 1) fully reduced mod p127
def cr.vm.norm(+x: CrU128) -> CrU128:
  match x:
    case CrU128{h, l}:
      cr.vm.norm.pick(Bool.and(W.W64.is_eq(h, cr.vm.m63()), W.W64.is_eq(l, W.W64.max())), x)

def cr.vm.reduce(+x: CrU128) -> CrU128:
  cr.vm.norm(cr.vm.fold(cr.vm.fold(x)))

def cr.vm.lt(a: CrU128, b: CrU128) -> Bool:
  match a b:
    case CrU128{+ah, al} CrU128{+bh, bl}:
      Bool.or(W.W64.is_lt(ah, bh), Bool.and(W.W64.is_eq(ah, bh), W.W64.is_lt(al, bl)))

# the 256-bit number with 64-bit words x3, x2, x1, x0 reduced mod p127:
# (x >> 127) + (x mod 2^127)
def cr.vm.mm3(+x3: W.W64, +x2: W.W64, +x1: W.W64, +x0: W.W64) -> CrU128:
  cr.vm.reduce(cr.vm.fold(cr.vm.add(CrU128{W.W64.or(W.W64.shl(x3, 1n), W.W64.shr(x2, 63n)), W.W64.or(W.W64.shl(x2, 1n), W.W64.shr(x1, 63n))}, CrU128{W.W64.and(x1, cr.vm.m63()), x0})))

def cr.vm.mm2(b: CrU128, +x1: W.W64, +x0: W.W64) -> CrU128:
  match b:
    case CrU128{x3, x2}:
      cr.vm.mm3(x3, x2, x1, x0)

def cr.vm.mm1(a: CrU128, +x0: W.W64, +mh: W.W64, midc: Bool, +p3: CrU128) -> CrU128:
  match a:
    case CrU128{ac, x1}:
      cr.vm.mm2(cr.vm.add(cr.vm.add(p3, CrU128{cr.vm.carry(midc), mh}), cr.vm.u(ac)), x1, x0)

def cr.vm.mm0(p0: CrU128, mid: CrU128, midc: Bool, +p3: CrU128) -> CrU128:
  match p0 mid:
    case CrU128{q0h, q0l} CrU128{mh, ml}:
      cr.vm.mm1(cr.vm.add(cr.vm.u(q0h), cr.vm.u(ml)), q0l, mh, midc, p3)

# the 256-bit p3 2^128 + (p1 + p2) 2^64 + p0, reduced mod p127
def cr.vm.mulmod.go(p0: CrU128, +p1: CrU128, p2: CrU128, +p3: CrU128) -> CrU128:
  +mid = cr.vm.add(p1, p2)
  cr.vm.mm0(p0, mid, cr.vm.lt(mid, p1), p3)

# a * b mod p127, for a, b below 2^127
def cr.vm.mulmod(a: CrU128, b: CrU128) -> CrU128:
  match a b:
    case CrU128{+ah, +al} CrU128{+bh, +bl}:
      cr.vm.mulmod.go(cr.vm.mul(al, bl), cr.vm.mul(al, bh), cr.vm.mul(ah, bl), cr.vm.mul(ah, bh))

# L2 over the NH values of the pieces ps, from y; an empty message is the
# poly key itself
def cr.vm.poly.go(+nk: List<&2, W.W64>, +k: CrU128, ps: List<&2, List<&2, U32>>, +y: CrU128) -> CrU128:
  match ps:
    case Nil{}:
      y
    case Con{p, t}:
      cr.vm.poly.go(nk, k, t, cr.vm.reduce(cr.vm.add(cr.vm.mulmod(y, k), cr.vm.nh(nk, p))))

def cr.vm.poly(+nk: List<&2, W.W64>, +k: CrU128, ps: List<&2, List<&2, U32>>) -> CrU128:
  match ps:
    case Nil{}:
      k
    case Con{p, t}:
      cr.vm.poly.go(nk, k, Con{p, t}, cr.vm.u(W.W64.one()))

# L3: the 64-bit words of y's quotient and remainder by 2^64 - 2^32, then
# ((m1 + k1)(m2 + k2)) mod p64 = 2^64 - 257

def cr.vm.p64() -> W.W64:
  W.W64.from_parts(4294967295, 4294967039)

# x below 2^128, folded: hi 2^64 + lo = hi 257 + lo (mod p64)
def cr.vm.f64(x: CrU128) -> CrU128:
  match x:
    case CrU128{h, +l}:
      cr.vm.add(cr.vm.mul(h, cr.vm.w(257)), cr.vm.u(l))

def cr.vm.sub64.pick(ge: Bool, +x: W.W64) -> W.W64:
  match ge:
    case True{}:
      W.W64.sub(x, cr.vm.p64())
    case False{}:
      x

def cr.vm.last64(x: CrU128) -> W.W64:
  match x:
    case CrU128{h, +l}:
      +y = W.W64.add(l, W.W64.mul(h, cr.vm.w(257)))
      cr.vm.sub64.pick(W.W64.is_ge(y, cr.vm.p64()), y)

# x below 2^130 (as hi, lo) mod p64
def cr.vm.mod64(+x: CrU128) -> W.W64:
  cr.vm.last64(cr.vm.f64(cr.vm.f64(x)))

def cr.vm.digit(+r: W.W64, +d: U32) -> W.W64:
  W.W64.from_parts(W.W64.lo(r), d)

# q (the quotient's two low base-2^32 digits) and r, for (x2, x1, x0)
# divided by 2^32 - 1, one digit at a time
type CrVmQr is Data:
  CrVmQr{q1: U32, q0: U32, r: U32}

def cr.vm.qr(+x2: U32, +x1: U32, +x0: U32) -> CrVmQr:
  +d = cr.vm.w(4294967295)
  +r2 = W.W64.mod(cr.vm.w(x2), d)
  +c1 = cr.vm.digit(r2, x1)
  +r1 = W.W64.mod(c1, d)
  +c0 = cr.vm.digit(r1, x0)
  CrVmQr{W.W64.lo(W.W64.div(c1, d)), W.W64.lo(W.W64.div(c0, d)), W.W64.lo(W.W64.mod(c0, d))}

def cr.vm.l3.go(qr: CrVmQr, +lo: U32, +k1: W.W64, +k2: W.W64) -> W.W64:
  match qr:
    case CrVmQr{q1, q0, r}:
      cr.vm.mod64(cr.vm.mul(cr.vm.mod64(cr.vm.add(cr.vm.u(W.W64.from_parts(q1, q0)), cr.vm.u(k1))), cr.vm.mod64(cr.vm.add(cr.vm.u(W.W64.from_parts(r, lo)), cr.vm.u(k2)))))

# L3 of y (below p127) under k1, k2
def cr.vm.l3(y: CrU128, +k1: W.W64, +k2: W.W64) -> W.W64:
  match y:
    case CrU128{+h, +l}:
      cr.vm.l3.go(cr.vm.qr(W.W64.hi(h), W.W64.lo(h), W.W64.hi(l)), W.W64.lo(l), k1, k2)

# The key

# one VHASH word's keys: the NH key words, the poly key, the L3 pair
type CrVmIter is Data:
  CrVmIter{nh: List<&2, W.W64>, poly: CrU128, k1: W.W64, k2: W.W64}

def cr.vm.l3keys.pick(ok: Bool, +a: W.W64, +b: W.W64, rest: List<&2, CrU128>) -> List<&2, CrU128>:
  match ok:
    case True{}:
      Con{CrU128{a, b}, rest}
    case False{}:
      rest

# the L3 pairs of 64-bit words of the KDF bytes xs both below p64, in order
def cr.vm.l3keys(xs: List<&2, W.W64>) -> List<&2, CrU128>:
  match xs:
    case Con{+a, Con{+b, t}}:
      cr.vm.l3keys.pick(Bool.and(W.W64.is_lt(a, cr.vm.p64()), W.W64.is_lt(b, cr.vm.p64())), a, b, cr.vm.l3keys(t))
    case _:
      Nil{}

def cr.vm.nth.pair(ps: List<&2, CrU128>, i: Nat) -> CrU128:
  match ps:
    case Nil{}:
      CrU128{W.W64.zero(), W.W64.zero()}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+j:
          cr.vm.nth.pair(t, j)

def cr.vm.u128.of(+xs: List<&2, U32>) -> CrU128:
  CrU128{cr.vm.w64be(xs, 0n), cr.vm.w64be(xs, 8n)}

# the poly key mask: each 32-bit field's top 3 bits cleared
def cr.vm.pmask(x: CrU128) -> CrU128:
  match x:
    case CrU128{h, l}:
      +m = W.W64.from_parts(536870911, 536870911)
      CrU128{W.W64.and(h, m), W.W64.and(l, m)}

def cr.vm.iter.of(+nh: List<&2, W.W64>, +poly: CrU128, kp: CrU128) -> CrVmIter:
  match kp:
    case CrU128{k1, k2}:
      CrVmIter{nh, poly, k1, k2}

# A VMAC key: the cipher's key schedule and each VHASH word's keys (one for
# a 64-bit tag, two for a 128-bit tag; opaque)
type CrVmacKey<-K: Data> is Data:
  CrVmacKey{k: K, iters: List<&2, CrVmIter>}

def cr.vm.iters(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, n: Nat, +k: K, +i: Nat, +l3: List<&2, CrU128>) -> List<&2, CrVmIter>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +nh = cr.vm.words(16n, True{}, B.drop(Nat.mul(16n, i), cr.vm.kdf(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k, 128, Nat.add(128n, Nat.mul(16n, i)))), 0n)
      +poly = cr.vm.pmask(cr.vm.u128.of(B.drop(Nat.mul(16n, i), cr.vm.kdf(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k, 192, Nat.mul(16n, Nat.add(i, 1n))))))
      Con{cr.vm.iter.of(nh, poly, cr.vm.nth.pair(l3, i)), cr.vm.iters(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, p, k, Nat.add(i, 1n), l3)}

def cr.vm.key.of(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +words: Nat, +k: K) -> CrVmacKey<K>:
  +l3 = cr.vm.l3keys(cr.vm.words(32n, True{}, cr.vm.kdf(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k, 224, 256n), 0n))
  CrVmacKey{k, cr.vm.iters(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, words, k, 0n, l3)}

# The key for tags of words 64-bit words (1: VMAC-64, 2: VMAC-128) from a raw
# key the cipher takes (KDF index 224's first 16 pairs give the L3 keys)
def CrVmac.key(~K: Data, ~Blk: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~words: Nat, o: B.Octets) -> Result<&2, &2, Cr.CrError, CrVmacKey<K>>:
  Result.map(&2, &2, Cr.CrError, K, CrVmacKey<K>, k => cr.vm.key.of(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, words, k), key(o))

# VHASH: one word per iter
def cr.vm.vhash(its: List<&2, CrVmIter>, +ps: List<&2, List<&2, U32>>, +lenterm: W.W64) -> List<&2, W.W64>:
  match its:
    case Nil{}:
      Nil{}
    case Con{it, rest}:
      match it:
        case CrVmIter{nh, poly, k1, k2}:
          Con{cr.vm.l3(cr.vm.reduce(cr.vm.add(cr.vm.poly(nh, poly, ps), CrU128{lenterm, W.W64.zero()})), k1, k2), cr.vm.vhash(rest, ps, lenterm)}

# the tag words: pad word + hash word, mod 2^64
def cr.vm.sum(ps: List<&2, W.W64>, hs: List<&2, W.W64>) -> List<&2, U32>:
  match ps hs:
    case Con{p, pt} Con{h, ht}:
      B.append(cr.vm.bytes64(W.W64.add(p, h)), cr.vm.sum(pt, ht))
    case _ _:
      Nil{}

def cr.vm.len(its: List<&2, CrVmIter>) -> Nat:
  match its:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+cr.vm.len(t)

def cr.vm.pdf.last(one: Bool, +b: U32) -> U32:
  match one:
    case True{}:
      U32.and(254, b)
    case False{}:
      b

def cr.vm.pdf.pick(one: Bool, odd: Bool, +t: List<&2, U32>, +words: Nat) -> List<&2, W.W64>:
  match one:
    case True{}:
      match odd:
        case True{}:
          [cr.vm.w64be(t, 8n)]
        case False{}:
          [cr.vm.w64be(t, 0n)]
    case False{}:
      cr.vm.words(words, True{}, t, 0n)

# the PDF's words for a nonce of 1 to 15 bytes
def cr.vm.pdf(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +words: Nat, +nonce: List<&2, U32>) -> List<&2, W.W64>:
  +n = B.len(nonce)
  +last = cr.vm.at(nonce, Nat.sub(n, 1n))
  +bit = U32.and(1, last)
  +cleared = B.append(B.take(Nat.sub(n, 1n), nonce), [cr.vm.pdf.last(Nat.is_eq(words, 1n), last)])
  +t = cr.vm.e(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, B.Octets.of_list(B.append(B.zeros(Nat.sub(bsize, n)), cleared)))
  cr.vm.pdf.pick(Nat.is_eq(words, 1n), U32.is_eq(bit, 1), t, words)

def cr.vm.tag.go(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrVmacKey<K>, +nonce: List<&2, U32>, +m: List<&2, U32>) -> B.Octets:
  match kk:
    case CrVmacKey{+k, +its}:
      +lenterm = W.W64.from_u32(U32.mul(U32.from_nat(Nat.mod(B.len.fast(m), 128n)), 8))
      B.Octets.of_list(cr.vm.sum(cr.vm.pdf(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, k, cr.vm.len(its), nonce), cr.vm.vhash(its, O.CrOct.pieces(128n, m), lenterm)))

def cr.vm.tag.pick(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ok: Bool, kk: CrVmacKey<K>, +nonce: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match ok:
    case True{}:
      Done{cr.vm.tag.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, B.Octets.to_list(nonce), B.Octets.to_list(m))}
    case False{}:
      Fail{Cr.CrBadNonceLength{B.Octets.len(nonce)}}

# The tag of m under a nonce of 1 to bsize - 1 bytes (CrBadNonceLength
# otherwise): 8 bytes for a VMAC-64 key, 16 for a VMAC-128 key
def CrVmac.tag(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, kk: CrVmacKey<K>, +nonce: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  +n = B.Octets.len(nonce)
  cr.vm.tag.pick(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, Bool.and(Nat.is_lt(0n, n), Nat.is_lt(n, bsize)), kk, nonce, m)

def cr.vm.or_empty(r: Result<&2, &2, Cr.CrError, B.Octets>) -> B.Octets:
  match r:
    case Fail{e}:
      B.Octets.empty()
    case Done{t}:
      t

# As a MAC: the nonce is the message's first nlen bytes (1 to bsize - 1),
# the data the rest; a message too short for its nonce has the empty tag
def cr.vm.mac(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~nlen: Nat, kk: CrVmacKey<K>, +m: B.Octets) -> B.Octets:
  cr.vm.or_empty(CrVmac.tag(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, B.Octets.take(nlen, m), B.Octets.drop(nlen, m)))

def CrVmac.mac(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~nlen: Nat, kk: CrVmacKey<K>, m: B.Octets) -> B.Octets:
  cr.vm.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen, kk, m)

# whether t is m's tag (every byte compared; the MAC interface's default)
def CrVmac.verify(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~nlen: Nat, kk: CrVmacKey<K>, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~CrVmacKey<K>, ~CrVmac.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen), kk, m, t)
