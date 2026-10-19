# Encrypt-then-MAC: an AEAD from any cipher with an IV and any MAC, as the
# Linux kernel's "authenc(mac, cipher)" composes them (for example
# authenc(hmac(sha256), cbc(aes)) for IPsec) and as D. McGrew, J. Foley, K.
# Paterson, "Authenticated Encryption with AES-CBC and HMAC-SHA"
# (draft-mcgrew-aead-aes-cbc-hmac-sha2-05, 2014) specifies it:
#   C = Enc(K_E, IV, P),  T = the first tlen bytes of MAC(K_M, input),
#   the AEAD's ciphertext C || T
# Opening checks T before decrypting anything, and releases nothing when it
# differs. What the MAC covers is a parameter (~input, from the associated
# data A, the IV and C), with two named defaults:
#   AdAuthenc.input_kernel   A || C (the kernel's authenc: an IV to be
#                            authenticated is part of A, as ESP does)
#   AdAuthenc.input_mcgrew   A || IV || C || AL, AL the bit length of A as a
#                            64-bit big-endian number (the draft's section
#                            2.1, with S = IV || C)
# A MAC shorter than tlen is zero-padded, so every tag has tlen bytes.
#
# The cipher (template arguments ~KE, ~ekey, ~enc, ~dec) takes a key
# schedule, an IV and bytes; ivcipher.bend makes one of any block cipher in
# CBC, with or without PKCS #7 padding. The MAC is the crypto package's MAC
# interface (~KM, ~mkey, ~mac). The key is the two keys (AdAuthencKey); a raw
# key is the MAC key then the cipher key, as both the kernel (after its
# length header) and the draft lay it out.
#
# Laws (LAWS.bend): open accepts what seal produced, wherever the cipher's
# decryption undoes its encryption (authenc_round_trip_if); and any tag but
# the one the MAC computes is refused (authenc_tamper).
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../crypto/crypto.bend as Cr
import ./aead.bend as Ad

# The two keys
type AdAuthencKey<-KE: Data, -KM: Data> is Data:
  AdAuthencKey{ke: KE, km: KM}

# The named MAC inputs

def AdAuthenc.input_kernel(aad: B.Octets, iv: B.Octets, c: B.Octets) -> B.Octets:
  B.Octets.append(aad, c)

def ad.au.mcgrew(+aad: B.Octets, iv: B.Octets, c: B.Octets) -> B.Octets:
  B.Octets.append(aad, B.Octets.append(iv, B.Octets.append(c, B.Octets.of_list(B.be64(W.W64.shl(W.W64.from_nat(B.Octets.len(aad)), 3n))))))

def AdAuthenc.input_mcgrew(aad: B.Octets, iv: B.Octets, c: B.Octets) -> B.Octets:
  ad.au.mcgrew(aad, iv, c)

# the first n bytes of xs, zero-padded to n
def ad.au.fit(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Con{0, ad.au.fit(m, Nil{})}
        case Con{h, t}:
          Con{h, ad.au.fit(m, t)}

# The tag of the ciphertext c: the MAC's first tlen bytes (zero-padded)
def AdAuthenc.tag(~KE: Data, ~KM: Data, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, k: AdAuthencKey<KE, KM>, aad: B.Octets, iv: B.Octets, c: B.Octets) -> B.Octets:
  match k:
    case AdAuthencKey{ke, km}:
      B.Octets.of_list(ad.au.fit(tlen, B.Octets.to_list(mac(km, input(aad, iv, c)))))

def ad.au.sealed(~KE: Data, ~KM: Data, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, +k: AdAuthencKey<KE, KM>, +aad: B.Octets, +iv: B.Octets, +c: B.Octets) -> B.Octets:
  Ad.AdTag.join(c, AdAuthenc.tag(~KE, ~KM, ~mac, ~input, ~tlen, k, aad, iv, c))

def ad.au.ke(~KE: Data, ~KM: Data, k: AdAuthencKey<KE, KM>) -> KE:
  match k:
    case AdAuthencKey{ke, km}:
      ke

def ad.au.seal(~KE: Data, ~KM: Data, ~enc: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, +k: AdAuthencKey<KE, KM>, +iv: B.Octets, +aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => ad.au.sealed(~KE, ~KM, ~mac, ~input, ~tlen, k, aad, iv, c), enc(ad.au.ke(~KE, ~KM, k), iv, p))

# p sealed under the IV: C || T
def AdAuthenc.seal(~KE: Data, ~KM: Data, ~enc: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, k: AdAuthencKey<KE, KM>, iv: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.au.seal(~KE, ~KM, ~enc, ~mac, ~input, ~tlen, k, iv, aad, p)

def ad.au.check(ok: Bool) -> Result<&2, &2, Cr.CrError, Unit>:
  Cr.CrError.check(ok, Cr.CrTagMismatch{})

def ad.au.open.go(~KE: Data, ~KM: Data, ~dec: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, +k: AdAuthencKey<KE, KM>, +iv: B.Octets, +aad: B.Octets, s: Ad.AdSplit) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match s:
    case Ad.AdSplit{+c, t}:
      Result.bind(&2, &2, Cr.CrError, Unit, B.Octets, ad.au.check(Ad.AdTag.is_eq(AdAuthenc.tag(~KE, ~KM, ~mac, ~input, ~tlen, k, aad, iv, c), t)), u => dec(ad.au.ke(~KE, ~KM, k), iv, c))

def ad.au.open(~KE: Data, ~KM: Data, ~dec: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, +k: AdAuthencKey<KE, KM>, +iv: B.Octets, +aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, Ad.AdSplit, B.Octets, Ad.AdTag.split(tlen, c), s => ad.au.open.go(~KE, ~KM, ~dec, ~mac, ~input, ~tlen, k, iv, aad, s))

# C || T opened: P, or CrTagMismatch (the cipher is not run), CrTooShort
def AdAuthenc.open(~KE: Data, ~KM: Data, ~dec: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~mac: KM -> B.Octets -> B.Octets, ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets, ~tlen: Nat, k: AdAuthencKey<KE, KM>, iv: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.au.open(~KE, ~KM, ~dec, ~mac, ~input, ~tlen, k, iv, aad, c)

# The key from the two raw keys
def AdAuthenc.key_of(~KE: Data, ~KM: Data, ~ekey: B.Octets -> Result<&2, &2, Cr.CrError, KE>, ~mkey: B.Octets -> Result<&2, &2, Cr.CrError, KM>, eo: B.Octets, mo: B.Octets) -> Result<&2, &2, Cr.CrError, AdAuthencKey<KE, KM>>:
  do Result<&2, &2, Cr.CrError, AdAuthencKey<KE, KM>>:
    ke : KE <- ekey(eo)
    km : KM <- mkey(mo)
    return AdAuthencKey{ke, km}

def ad.au.key(~KE: Data, ~KM: Data, ~ekey: B.Octets -> Result<&2, &2, Cr.CrError, KE>, ~mkey: B.Octets -> Result<&2, &2, Cr.CrError, KM>, +elen: Nat, +o: B.Octets) -> Result<&2, &2, Cr.CrError, AdAuthencKey<KE, KM>>:
  +n = B.Octets.len(o)
  +m = Nat.sub(n, elen)
  Result.bind(&2, &2, Cr.CrError, Unit, AdAuthencKey<KE, KM>, Cr.CrError.check(Nat.is_le(elen, n), Cr.CrBadKeyLength{n}), u => AdAuthenc.key_of(~KE, ~KM, ~ekey, ~mkey, B.Octets.drop(m, o), B.Octets.take(m, o)))

# The key from one raw key: the MAC key, then the cipher key of elen bytes
# (CrBadKeyLength for fewer than elen bytes, or a key either refuses)
def AdAuthenc.key(~KE: Data, ~KM: Data, ~ekey: B.Octets -> Result<&2, &2, Cr.CrError, KE>, ~mkey: B.Octets -> Result<&2, &2, Cr.CrError, KM>, ~elen: Nat, o: B.Octets) -> Result<&2, &2, Cr.CrError, AdAuthencKey<KE, KM>>:
  ad.au.key(~KE, ~KM, ~ekey, ~mkey, elen, o)
