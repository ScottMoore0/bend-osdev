# bend-osdev-pubkey: the public-key algorithms of bend-osdev as instances
# of bend-osdev-crypto's signature and key-agreement interfaces
# (crypto/sign.bend, crypto/kex.bend):
#
#   rsa.bend     RSASSA-PKCS1-v1_5 and RSASSA-PSS (the rsa package)
#   dh.bend      finite-field Diffie-Hellman (the dh package)
#   ecc.bend     ECDH and ECDSA (the ecc package)
#   sm2.bend     SM2 signatures (the sm2 package)
#   ecrdsa.bend  GOST R 34.10-2012 signatures (the ecrdsa package)
#
# This file holds what they share: HMAC from a raw key, the MAC that RFC
# 6979's deterministic per-message secret is built on.
import Base
import ../bytes/bytes.bend as B
import ../crypto/hmac.bend as Hm

# HMAC over a hash of block size bsize, from the raw key (RFC 2104)
def PkHmac.raw(~bsize: Nat, ~digest: B.Octets -> B.Octets, k: B.Octets, m: B.Octets) -> B.Octets:
  Hm.CrHmac.mac(~digest, Hm.CrHmac.key(~bsize, ~digest, k), m)
