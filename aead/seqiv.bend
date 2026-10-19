# seqiv: an AEAD whose nonce is made from a sequence number, sent in front
# of the ciphertext (the Linux kernel's "seqiv(aead)", as IPsec ESP uses
# it with GCM and CCM). The sender keeps a counter (the packet's sequence
# number); the nonce is the counter, right-aligned in the nonce's length and
# XORed with a secret salt from the key material, as RFC 8446 (TLS 1.3),
# section 5.3, forms its per-record nonce, and as RFC 5116, section 3.2,
# recommends (a counter, so that no nonce repeats under one key). The nonce
# travels with the ciphertext, as ESP's explicit IV does, so the receiver
# needs no counter:
#   IV = salt xor (0 .. 0 || seq),  sealed: IV || AEAD.seal(K, IV, A || IV, P)
#   opened: the first ivlen bytes are the IV, AEAD.open(K, IV, A || IV, the rest)
# The IV is part of the AEAD's associated data, so it is authenticated even
# under an AEAD that does not bind its nonce (Encrypt-then-MAC over A || C,
# authenc.bend's kernel layout), as ESP authenticates its IV (RFC 4303,
# section 3.3.2.1, with the IV part of the payload the ICV covers).
# The salt is the last ivlen bytes of the raw key (as RFC 4106's GCM in ESP
# takes its salt from the end of the key material); the kernel's seqiv draws
# its salt at random, so its IVs differ from these, but a receiver reads the
# IV from the packet, and the two interoperate.
#
# Over any AEAD of the crypto package's AEAD interface (~KA, ~akey, ~seal,
# ~open) with an ivlen-byte nonce. Laws (LAWS.bend): open accepts what seal
# produced wherever the AEAD's open accepts what its seal produced, at the
# generated IV (seqiv_round_trip_if).
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/octets.bend as O

# The key: the AEAD's key and the salt
type AdSeqivKey<-KA: Data> is Data:
  AdSeqivKey{ka: KA, salt: B.Octets}

def ad.sq.ka(~KA: Data, k: AdSeqivKey<KA>) -> KA:
  match k:
    case AdSeqivKey{ka, salt}:
      ka

# The IV of sequence number seq (big-endian bytes, at most as long as the
# salt): the salt XOR seq, right-aligned
def AdSeqiv.iv(~KA: Data, k: AdSeqivKey<KA>, +seq: B.Octets) -> B.Octets:
  match k:
    case AdSeqivKey{ka, +salt}:
      O.CrOct.xor(salt, B.Octets.append(B.Octets.zeros(Nat.sub(B.Octets.len(salt), B.Octets.len(seq))), seq))

def ad.sq.key(~KA: Data, ~akey: B.Octets -> Result<&2, &2, Cr.CrError, KA>, +ivlen: Nat, +o: B.Octets) -> Result<&2, &2, Cr.CrError, AdSeqivKey<KA>>:
  +n = B.Octets.len(o)
  +m = Nat.sub(n, ivlen)
  do Result<&2, &2, Cr.CrError, AdSeqivKey<KA>>:
    Cr.CrError.check(Nat.is_le(ivlen, n), Cr.CrBadKeyLength{n})
    ka : KA <- akey(B.Octets.take(m, o))
    return AdSeqivKey{ka, B.Octets.drop(m, o)}

# The key from raw key material: the AEAD's key, then an ivlen-byte salt
def AdSeqiv.key(~KA: Data, ~akey: B.Octets -> Result<&2, &2, Cr.CrError, KA>, ~ivlen: Nat, o: B.Octets) -> Result<&2, &2, Cr.CrError, AdSeqivKey<KA>>:
  ad.sq.key(~KA, ~akey, ivlen, o)

def ad.sq.seal(~KA: Data, ~seal: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdSeqivKey<KA>, +seq: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  +iv = AdSeqiv.iv(~KA, k, seq)
  Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => B.Octets.append(iv, c), seal(ad.sq.ka(~KA, k), iv, B.Octets.append(aad, iv), p))

# p sealed under the sequence number seq: IV || the AEAD's ciphertext
def AdSeqiv.seal(~KA: Data, ~seal: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, k: AdSeqivKey<KA>, seq: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.sq.seal(~KA, ~seal, k, seq, aad, p)

def ad.sq.open.go(~KA: Data, ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, +k: AdSeqivKey<KA>, aad: B.Octets, +n: Nat, s: Maybe<&2, B.OctetsSplit>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match s:
    case None{}:
      Fail{Cr.CrTooShort{n}}
    case Some{B.OctetsSplit{+iv, c}}:
      open(ad.sq.ka(~KA, k), iv, B.Octets.append(aad, iv), c)

# IV || C opened (the IV the first ivlen bytes; the sequence number is not
# needed): the AEAD's open of C under that IV and A || IV, or CrTooShort
def ad.sq.open(~KA: Data, ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~ivlen: Nat, +k: AdSeqivKey<KA>, seq: B.Octets, aad: B.Octets, +c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.sq.open.go(~KA, ~open, k, aad, B.Octets.len(c), B.Octets.split_at(ivlen, c))

def AdSeqiv.open(~KA: Data, ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>, ~ivlen: Nat, k: AdSeqivKey<KA>, seq: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.sq.open(~KA, ~open, ~ivlen, k, seq, aad, c)
