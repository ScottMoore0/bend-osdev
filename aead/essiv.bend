# ESSIV, "encrypted salt-sector initialization vector" (C. Fruhwirth, "New
# Methods in Hard Disk Encryption", 2005, section 4.2; the Linux kernel's
# "essiv(cipher, hash)", as dm-crypt and fscrypt use it): the IV of a sector
# is the sector's number encrypted under a key derived from the data key,
#   salt = H(K),  IV' = E(salt, IV)
# where H is any hash of the crypto package's hash interface (~digest) and E
# any block cipher of its block-cipher interface (the "salt cipher", whose
# key is the digest: SHA-256 and AES-256 in dm-crypt's aes-cbc-essiv:sha256).
#
# Two forms, both taking the data key K whole:
#   * over a cipher with an IV (ivcipher.bend: CBC): AdEssiv.encrypt and
#     AdEssiv.decrypt run it under IV';
#   * over an AEAD (crypto's AEAD interface, the kernel's essiv(authenc(..)))
#     AdEssiv.seal and AdEssiv.open run it under the nonce IV'.
# Laws (LAWS.bend): each undoes itself wherever what it wraps does, at the
# derived IV (essiv_round_trip_if, essiv_aead_round_trip_if).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr

# The key: the wrapped algorithm's key, and the salt cipher's key schedule
type AdEssivKey<-KD: Data, -KS: Data> is Data:
  AdEssivKey{kd: KD, ks: KS}

def ad.es.e(~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +ks: KS, x: Maybe<&2, Blk>, +iv: B.Octets) -> B.Octets:
  match x:
    case None{}:
      iv
    case Some{b}:
      blk_to(enc(ks, b))

def ad.es.iv(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: AdEssivKey<KD, KS>, +iv: B.Octets) -> B.Octets:
  match k:
    case AdEssivKey{kd, +ks}:
      ad.es.e(~KS, ~Blk, ~enc, ~blk_to, ks, blk_of(iv), iv)

# IV' = E(salt, IV) (an IV the salt cipher's format refuses is used as it is)
def AdEssiv.iv(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: AdEssivKey<KD, KS>, +iv: B.Octets) -> B.Octets:
  ad.es.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, k, iv)

def ad.es.kd(~KD: Data, ~KS: Data, k: AdEssivKey<KD, KS>) -> KD:
  match k:
    case AdEssivKey{kd, ks}:
      kd

def ad.es.key(~KD: Data, ~KS: Data, ~dkey: B.Octets -> Result<&2, &2, Cr.CrError, KD>, ~skey: B.Octets -> Result<&2, &2, Cr.CrError, KS>, ~digest: B.Octets -> B.Octets, +o: B.Octets) -> Result<&2, &2, Cr.CrError, AdEssivKey<KD, KS>>:
  do Result<&2, &2, Cr.CrError, AdEssivKey<KD, KS>>:
    kd : KD <- dkey(o)
    ks : KS <- skey(digest(o))
    return AdEssivKey{kd, ks}

# The key from the data key K: the wrapped algorithm's key of K, and the
# salt cipher's key of H(K)
def AdEssiv.key(~KD: Data, ~KS: Data, ~dkey: B.Octets -> Result<&2, &2, Cr.CrError, KD>, ~skey: B.Octets -> Result<&2, &2, Cr.CrError, KS>, ~digest: B.Octets -> B.Octets, o: B.Octets) -> Result<&2, &2, Cr.CrError, AdEssivKey<KD, KS>>:
  ad.es.key(~KD, ~KS, ~dkey, ~skey, ~digest, o)

# Over a cipher with an IV (~cenc, ~cdec: key schedule, IV, bytes)

def ad.es.encrypt(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~cenc: KD -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdEssivKey<KD, KS>, +iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cenc(ad.es.kd(~KD, ~KS, k), AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, k, iv), m)

def AdEssiv.encrypt(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~cenc: KD -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, k: AdEssivKey<KD, KS>, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.es.encrypt(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~cenc, k, iv, m)

def ad.es.decrypt(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~cdec: KD -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdEssivKey<KD, KS>, +iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cdec(ad.es.kd(~KD, ~KS, k), AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, k, iv), c)

def AdEssiv.decrypt(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~cdec: KD -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, k: AdEssivKey<KD, KS>, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.es.decrypt(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~cdec, k, iv, c)

# Over an AEAD (~seal, ~open: key, nonce, associated data, bytes)

def ad.es.seal(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~seal: KD -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdEssivKey<KD, KS>, +iv: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  seal(ad.es.kd(~KD, ~KS, k), AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, k, iv), aad, p)

def AdEssiv.seal(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~seal: KD -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, k: AdEssivKey<KD, KS>, iv: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.es.seal(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~seal, k, iv, aad, p)

def ad.es.open(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~open: KD -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdEssivKey<KD, KS>, +iv: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  open(ad.es.kd(~KD, ~KS, k), AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, k, iv), aad, c)

def AdEssiv.open(~KD: Data, ~KS: Data, ~Blk: Data, ~enc: KS -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ~open: KD -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, k: AdEssivKey<KD, KS>, iv: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.es.open(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~open, k, iv, aad, c)
