# echainiv, "encrypted chain IV": an AEAD whose nonce is a sequence number
# encrypted under a block cipher, sent in front of the ciphertext (the Linux
# kernel's "echainiv(aead)", for IPsec with CBC-based AEADs, where an IV
# must be unpredictable as well as unique). The IV is generated as NIST SP
# 800-38A, Appendix C, recommends for CBC ("apply the forward cipher
# function, under the same key that is used for the encryption of the
# plaintext, to a nonce", here a nonce made from the sequence number and a
# secret salt, as in seqiv.bend):
#   IV = E(Kc, salt xor (0 .. 0 || seq)),  sealed: IV || AEAD.seal(K, IV, A || IV, P)
#   opened: the first ivlen bytes are the IV, AEAD.open(K, IV, A || IV, the rest)
# The IV is part of the AEAD's associated data, so it is authenticated even
# under an AEAD that does not bind its nonce (as seqiv.bend).
# Kc is the key schedule of a block cipher of the crypto package's
# interface (for authenc(hmac(..), cbc(aes)), AES under the AEAD's cipher
# key), and the salt one block. The kernel's echainiv draws its salt at
# random and chains through earlier IVs, so its IVs differ from these, but a
# receiver reads the IV from the packet, and the two interoperate.
#
# Over any AEAD with an ivlen-byte nonce. Laws (LAWS.bend): open accepts what
# seal produced wherever the AEAD's does, at the generated IV
# (echainiv_round_trip_if).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/octets.bend as O

# The key: the AEAD's key, the IV cipher's key schedule, and the salt
type AdEchainivKey<-KA: Data, -KC: Data> is Data:
  AdEchainivKey{ka: KA, kc: KC, salt: B.Octets}

def ad.ec.ka(~KA: Data, ~KC: Data, k: AdEchainivKey<KA, KC>) -> KA:
  match k:
    case AdEchainivKey{ka, kc, salt}:
      ka

def ad.ec.e(~KC: Data, ~Blk: Data, ~enc: KC -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +kc: KC, x: Maybe<&2, Blk>, +o: B.Octets) -> B.Octets:
  match x:
    case None{}:
      o
    case Some{b}:
      blk_to(enc(kc, b))

# The IV of sequence number seq: E(Kc, salt xor seq right-aligned)
def AdEchainiv.iv(~KA: Data, ~KC: Data, ~Blk: Data, ~enc: KC -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: AdEchainivKey<KA, KC>, +seq: B.Octets) -> B.Octets:
  match k:
    case AdEchainivKey{ka, +kc, +salt}:
      +x = O.CrOct.xor(salt, B.Octets.append(B.Octets.zeros(Nat.sub(B.Octets.len(salt), B.Octets.len(seq))), seq))
      ad.ec.e(~KC, ~Blk, ~enc, ~blk_to, kc, blk_of(x), x)

# The key from the AEAD's raw key, the IV cipher's raw key and the salt
def AdEchainiv.key(~KA: Data, ~KC: Data, ~akey: B.Octets -> Result<&2, &2, Cr.CrError, KA>, ~ckey: B.Octets -> Result<&2, &2, Cr.CrError, KC>, ao: B.Octets, co: B.Octets, salt: B.Octets) -> Result<&2, &2, Cr.CrError, AdEchainivKey<KA, KC>>:
  do Result<&2, &2, Cr.CrError, AdEchainivKey<KA, KC>>:
    ka : KA <- akey(ao)
    kc : KC <- ckey(co)
    return AdEchainivKey{ka, kc, salt}

def ad.ec.seal(~KA: Data, ~KC: Data, ~Blk: Data, ~enc: KC -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~seal: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdEchainivKey<KA, KC>, +seq: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  +iv = AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, k, seq)
  Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => B.Octets.append(iv, c), seal(ad.ec.ka(~KA, ~KC, k), iv, B.Octets.append(aad, iv), p))

# p sealed under the sequence number seq: IV || the AEAD's ciphertext
def AdEchainiv.seal(~KA: Data, ~KC: Data, ~Blk: Data, ~enc: KC -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~seal: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, k: AdEchainivKey<KA, KC>, seq: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.ec.seal(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, ~seal, k, seq, aad, p)

def ad.ec.open.go(~KA: Data, ~KC: Data, ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdEchainivKey<KA, KC>, aad: B.Octets, +n: Nat, s: Maybe<&2, B.OctetsSplit>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match s:
    case None{}:
      Fail{Cr.CrTooShort{n}}
    case Some{B.OctetsSplit{+iv, c}}:
      open(ad.ec.ka(~KA, ~KC, k), iv, B.Octets.append(aad, iv), c)

def ad.ec.open(~KA: Data, ~KC: Data, ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~ivlen: Nat, +k: AdEchainivKey<KA, KC>, seq: B.Octets, aad: B.Octets, +c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.ec.open.go(~KA, ~KC, ~open, k, aad, B.Octets.len(c), B.Octets.split_at(ivlen, c))

# IV || C opened: the AEAD's open of C under the first ivlen bytes and
# A || IV, or CrTooShort
def AdEchainiv.open(~KA: Data, ~KC: Data, ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~ivlen: Nat, k: AdEchainivKey<KA, KC>, seq: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.ec.open(~KA, ~KC, ~open, ~ivlen, k, seq, aad, c)
