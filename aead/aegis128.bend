# AEGIS-128 (H. Wu, B. Preneel, "AEGIS: A Fast Authenticated Encryption
# Algorithm (v1.1)", CAESAR final portfolio, 2016, section 2.3): a 128-bit
# key, a 128-bit nonce, a 128-bit tag, and an 80-byte state of five 16-byte
# blocks S0 .. S4 updated by the AES round function (aesround.bend):
#   StateUpdate128(S, m) = (AESRound(S4, S0 xor m), AESRound(S0, S1),
#                           AESRound(S1, S2), AESRound(S2, S3),
#                           AESRound(S3, S4))
#   initialization: S = (K xor IV, const1, const0, K xor const0,
#     K xor const1), then ten updates with K, K xor IV, K, K xor IV, ..
#   associated data: an update with each 16-byte block (the last zero-padded)
#   encryption: C_i = P_i xor S1 xor S4 xor (S2 and S3), then an update with
#     P_i (a short last block: only its bytes encrypted, the zero-padded
#     block used for the update)
#   finalization: tmp = S3 xor (adlen || msglen), the bit lengths as 64-bit
#     little-endian numbers; seven updates with tmp; the tag is
#     S0 xor S1 xor S2 xor S3 xor S4
# As an AEAD (crypto's aead.bend): ~AdAegisKey, ~AdAegis128.key,
# ~AdAegis128.seal, ~AdAegis128.open; the ciphertext is C followed by the
# 16-byte tag.
#
# The message is processed a byte at a time: each byte is XORed with the
# next keystream byte and joins the block that updates the state when it is
# whole. Decryption recovers each plaintext byte the same way and so runs
# through the same states, which is why open accepts what seal produced
# (LAWS.bend: aegis128_round_trip, for every key, nonce, associated data and
# message).
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crypto/crypto.bend as Cr
import ../crypto/octets.bend as O
import ./aead.bend as Ad
import ./aesround.bend as R

# The state (internal)
type AdAegisSt is Data:
  AdAegisSt{s0: R.AdBlk, s1: R.AdBlk, s2: R.AdBlk, s3: R.AdBlk, s4: R.AdBlk}

def ad.ae.update(+sb: R.AdSbox, st: AdAegisSt, +m: R.AdBlk) -> AdAegisSt:
  match st:
    case AdAegisSt{+a0, +a1, +a2, +a3, +a4}:
      AdAegisSt{R.AdAes.round(sb, a4, R.AdBlk.xor(a0, m)), R.AdAes.round(sb, a0, a1), R.AdAes.round(sb, a1, a2), R.AdAes.round(sb, a2, a3), R.AdAes.round(sb, a3, a4)}

# the keystream block S1 xor S4 xor (S2 and S3)
def ad.ae.z(st: AdAegisSt) -> R.AdBlk:
  match st:
    case AdAegisSt{a0, a1, a2, a3, a4}:
      R.AdBlk.xor(R.AdBlk.xor(a1, a4), R.AdBlk.and(a2, a3))

# const0 and const1 (the Fibonacci sequence mod 256)
def ad.ae.c0() -> R.AdBlk:
  R.AdBlk{65794, 50661389, 354563929, 2431220066}

def ad.ae.c1() -> R.AdBlk:
  R.AdBlk{3678214229, 1841442801, 537997634, 1941252317}

def ad.ae.init.go(n: Nat, +sb: R.AdSbox, +k: R.AdBlk, +kiv: R.AdBlk, st: AdAegisSt) -> AdAegisSt:
  match n:
    case 0n:
      st
    case 1n+p:
      ad.ae.init.go(p, sb, k, kiv, ad.ae.update(sb, ad.ae.update(sb, st, k), kiv))

def ad.ae.init(+sb: R.AdSbox, +k: R.AdBlk, +iv: R.AdBlk) -> AdAegisSt:
  +kiv = R.AdBlk.xor(k, iv)
  ad.ae.init.go(5n, sb, k, kiv, AdAegisSt{kiv, ad.ae.c1(), ad.ae.c0(), R.AdBlk.xor(k, ad.ae.c0()), R.AdBlk.xor(k, ad.ae.c1())})

# the state after the associated data's 16-byte pieces (the last
# zero-padded)
def ad.ae.absorb(+sb: R.AdSbox, ps: List<&2, List<&2, U32>>, st: AdAegisSt) -> AdAegisSt:
  match ps:
    case Nil{}:
      st
    case Con{p, t}:
      ad.ae.absorb(sb, t, ad.ae.update(sb, st, R.AdBlk.of_list(p)))

# The message, a byte at a time (internal): the state, the keystream bytes
# left of the current block, the current block's plaintext bytes so far
# (last first) and how many
type AdAegisRun is Data:
  AdAegisRun{st: AdAegisSt, zs: List<&2, U32>, buf: List<&2, U32>, n: Nat}

def ad.ae.run0(+st: AdAegisSt) -> AdAegisRun:
  AdAegisRun{st, R.AdBlk.to_list(ad.ae.z(st)), Nil{}, 0n}

def ad.ae.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      ad.ae.rev(t, Con{h, acc})

def ad.ae.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def ad.ae.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

def ad.ae.step.pick(full: Bool, +sb: R.AdSbox, st: AdAegisSt, zs: List<&2, U32>, +buf: List<&2, U32>, +n: Nat) -> AdAegisRun:
  match full:
    case True{}:
      ad.ae.run0(ad.ae.update(sb, st, R.AdBlk.of_list(ad.ae.rev(buf, Nil{}))))
    case False{}:
      AdAegisRun{st, ad.ae.tail(zs), buf, 1n+n}

# the run after the plaintext byte x
def ad.ae.step(+sb: R.AdSbox, r: AdAegisRun, x: U32) -> AdAegisRun:
  match r:
    case AdAegisRun{st, zs, buf, +n}:
      ad.ae.step.pick(Nat.is_eq(n, 15n), sb, st, zs, Con{x, buf}, n)

# the next keystream byte
def ad.ae.zhead(r: AdAegisRun) -> U32:
  match r:
    case AdAegisRun{st, zs, buf, n}:
      ad.ae.head(zs)

def ad.ae.flush.pick(empty: Bool, +sb: R.AdSbox, st: AdAegisSt, buf: List<&2, U32>) -> AdAegisSt:
  match empty:
    case True{}:
      st
    case False{}:
      ad.ae.update(sb, st, R.AdBlk.of_list(ad.ae.rev(buf, Nil{})))

# the state after the last, short block (zero-padded)
def ad.ae.flush(+sb: R.AdSbox, r: AdAegisRun) -> AdAegisSt:
  match r:
    case AdAegisRun{st, zs, buf, n}:
      ad.ae.flush.pick(Nat.is_eq(n, 0n), sb, st, buf)

# Encryption and decryption, structurally (the proofs' reference): the
# output bytes, and the run after them

def ad.ae.eout(xs: List<&2, U32>, +sb: R.AdSbox, +r: AdAegisRun) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{B.byte(U32.xor(x, ad.ae.zhead(r))), ad.ae.eout(t, sb, ad.ae.step(sb, r, B.byte(x)))}

def ad.ae.eafter(xs: List<&2, U32>, +sb: R.AdSbox, +r: AdAegisRun) -> AdAegisRun:
  match xs:
    case Nil{}:
      r
    case Con{+x, t}:
      ad.ae.eafter(t, sb, ad.ae.step(sb, r, B.byte(x)))

def ad.ae.dout(ys: List<&2, U32>, +sb: R.AdSbox, +r: AdAegisRun) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, t}:
      Con{B.byte(U32.xor(y, ad.ae.zhead(r))), ad.ae.dout(t, sb, ad.ae.step(sb, r, B.byte(U32.xor(y, ad.ae.zhead(r)))))}

def ad.ae.dafter(ys: List<&2, U32>, +sb: R.AdSbox, +r: AdAegisRun) -> AdAegisRun:
  match ys:
    case Nil{}:
      r
    case Con{+y, t}:
      ad.ae.dafter(t, sb, ad.ae.step(sb, r, B.byte(U32.xor(y, ad.ae.zhead(r)))))

# The loops that run (tail calls): the run after the bytes, and the output
type AdAegisOut is Data:
  AdAegisOut{r: AdAegisRun, out: List<&2, U32>}

def ad.ae.ego(xs: List<&2, U32>, +sb: R.AdSbox, +r: AdAegisRun, acc: List<&2, U32>) -> AdAegisOut:
  match xs:
    case Nil{}:
      AdAegisOut{r, ad.ae.rev(acc, Nil{})}
    case Con{+x, t}:
      ad.ae.ego(t, sb, ad.ae.step(sb, r, B.byte(x)), Con{B.byte(U32.xor(x, ad.ae.zhead(r))), acc})

def ad.ae.dgo(ys: List<&2, U32>, +sb: R.AdSbox, +r: AdAegisRun, acc: List<&2, U32>) -> AdAegisOut:
  match ys:
    case Nil{}:
      AdAegisOut{r, ad.ae.rev(acc, Nil{})}
    case Con{+y, t}:
      +p = B.byte(U32.xor(y, ad.ae.zhead(r)))
      ad.ae.dgo(t, sb, ad.ae.step(sb, r, p), Con{p, acc})

# Finalization: the tag from the state after the message, and the lengths
def ad.ae.fin.go(n: Nat, +sb: R.AdSbox, +tmp: R.AdBlk, st: AdAegisSt) -> AdAegisSt:
  match n:
    case 0n:
      st
    case 1n+p:
      ad.ae.fin.go(p, sb, tmp, ad.ae.update(sb, st, tmp))

def ad.ae.tag(st: AdAegisSt) -> B.Octets:
  match st:
    case AdAegisSt{a0, a1, a2, a3, a4}:
      R.AdBlk.to_octets(R.AdBlk.xor(R.AdBlk.xor(R.AdBlk.xor(a0, a1), R.AdBlk.xor(a2, a3)), a4))

# n as a 64-bit word, counted up (W64.from_nat divides by 2^32, a literal
# the checker would expand when a proof meets it)
def ad.ae.w64(n: Nat, acc: W.W64) -> W.W64:
  match n:
    case 0n:
      acc
    case 1n+p:
      ad.ae.w64(p, W.W64.add(acc, W.W64.one()))

# the bit length of n bytes as 8 little-endian bytes
def ad.ae.bits(n: Nat) -> List<&2, U32>:
  B.le64(W.W64.shl(ad.ae.w64(n, W.W64.zero()), 3n))

def ad.ae.s3(st: AdAegisSt) -> R.AdBlk:
  match st:
    case AdAegisSt{a0, a1, a2, a3, a4}:
      a3

def ad.ae.final(+sb: R.AdSbox, +st: AdAegisSt, +alen: Nat, +mlen: Nat) -> B.Octets:
  ad.ae.tag(ad.ae.fin.go(7n, sb, R.AdBlk.xor(ad.ae.s3(st), R.AdBlk.of_list(B.append(ad.ae.bits(alen), ad.ae.bits(mlen)))), st))

# An AEGIS-128 key: the key block and the AES S-box (opaque)
type AdAegisKey is Data:
  AdAegisKey{k: R.AdBlk, sb: R.AdSbox}

def ad.ae.key.pick(ok: Bool, +o: B.Octets) -> Result<&2, &2, Cr.CrError, AdAegisKey>:
  match ok:
    case True{}:
      Done{AdAegisKey{R.AdBlk.of_octets(o), R.AdAes.sbox()}}
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(o)}}

def ad.ae.key(+o: B.Octets) -> Result<&2, &2, Cr.CrError, AdAegisKey>:
  ad.ae.key.pick(Nat.is_eq(B.Octets.len(o), 16n), o)

# a 16-byte key
def AdAegis128.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, AdAegisKey>:
  ad.ae.key(o)

# the run before the message: the state after the key, nonce and associated
# data
def ad.ae.start(+sb: R.AdSbox, +k: R.AdBlk, +nonce: B.Octets, +aad: B.Octets) -> AdAegisRun:
  ad.ae.run0(ad.ae.absorb(sb, O.CrOct.pieces(16n, B.Octets.to_list(aad)), ad.ae.init(sb, k, R.AdBlk.of_octets(nonce))))

def ad.ae.sealed(+sb: R.AdSbox, +aad: B.Octets, +p: B.Octets, o: AdAegisOut) -> B.Octets:
  match o:
    case AdAegisOut{r, out}:
      Ad.AdTag.join(B.Octets.of_list(out), ad.ae.final(sb, ad.ae.flush(sb, r), B.Octets.len(aad), B.Octets.len(p)))

def ad.ae.seal.go(kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, +p: B.Octets) -> B.Octets:
  match kk:
    case AdAegisKey{+k, +sb}:
      ad.ae.sealed(sb, aad, p, ad.ae.ego(B.Octets.to_list(p), sb, ad.ae.start(sb, k, nonce, aad), Nil{}))

def ad.ae.nonce(+nonce: B.Octets) -> Result<&2, &2, Cr.CrError, Unit>:
  Cr.CrError.check(Nat.is_eq(B.Octets.len(nonce), 16n), Cr.CrBadNonceLength{B.Octets.len(nonce)})

def ad.ae.seal(+kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, +p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => ad.ae.seal.go(kk, nonce, aad, p), ad.ae.nonce(nonce))

# p sealed under a 16-byte nonce: the ciphertext and the 16-byte tag
def AdAegis128.seal(kk: AdAegisKey, nonce: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.ae.seal(kk, nonce, aad, p)

def ad.ae.tag_of.of(+sb: R.AdSbox, +aad: B.Octets, +c: B.Octets, o: AdAegisOut) -> B.Octets:
  match o:
    case AdAegisOut{r, out}:
      ad.ae.final(sb, ad.ae.flush(sb, r), B.Octets.len(aad), B.Octets.len(c))

def ad.ae.tag_of.go(kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, +c: B.Octets) -> B.Octets:
  match kk:
    case AdAegisKey{+k, +sb}:
      ad.ae.tag_of.of(sb, aad, c, ad.ae.dgo(B.Octets.to_list(c), sb, ad.ae.start(sb, k, nonce, aad), Nil{}))

# The tag open expects for the ciphertext c (without its tag)
def AdAegis128.tag_of(kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, +c: B.Octets) -> B.Octets:
  ad.ae.tag_of.go(kk, nonce, aad, c)

def ad.ae.plain.of(o: AdAegisOut) -> B.Octets:
  match o:
    case AdAegisOut{r, out}:
      B.Octets.of_list(out)

def ad.ae.plain(kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, +c: B.Octets) -> B.Octets:
  match kk:
    case AdAegisKey{+k, +sb}:
      ad.ae.plain.of(ad.ae.dgo(B.Octets.to_list(c), sb, ad.ae.start(sb, k, nonce, aad), Nil{}))

def ad.ae.check(ok: Bool, +p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match ok:
    case True{}:
      Done{p}
    case False{}:
      Fail{Cr.CrTagMismatch{}}

def ad.ae.open.go(+kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, s: Ad.AdSplit) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match s:
    case Ad.AdSplit{+c, t}:
      ad.ae.check(Ad.AdTag.is_eq(AdAegis128.tag_of(kk, nonce, aad, c), t), ad.ae.plain(kk, nonce, aad, c))

def ad.ae.open(+kk: AdAegisKey, +nonce: B.Octets, +aad: B.Octets, +c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, Unit, B.Octets, ad.ae.nonce(nonce), u => Result.bind(&2, &2, Cr.CrError, Ad.AdSplit, B.Octets, Ad.AdTag.split(16n, c), s => ad.ae.open.go(kk, nonce, aad, s)))

# c (the ciphertext with its tag) opened: the plaintext, or CrTagMismatch
# (no plaintext released)
def AdAegis128.open(kk: AdAegisKey, nonce: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.ae.open(kk, nonce, aad, c)
