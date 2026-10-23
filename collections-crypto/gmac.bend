# GMAC (NIST SP 800-38D: GCM with no data to encrypt, so the tag
# authenticates the associated data alone) over AES-128 and AES-256 as a
# MAC: bend-collections' AES-GCM sealing an empty plaintext, which leaves
# only the 16-byte tag.
#
# The MAC interface has no nonce, so, as crypto's VMAC (vmac.bend) does, the
# message's first 12 bytes are the nonce (96 bits, the length
# bend-collections' GCM takes) and the rest is the data authenticated. A
# message shorter than its nonce has the empty tag. A nonce must never be
# used twice under one key.
#
# The instances:
#   ~CcGmacKey, ~CcGmac.key128, ~CcGmac.mac, ~CcGmac.verify
#   ~CcGmacKey, ~CcGmac.key256, ~CcGmac.mac, ~CcGmac.verify
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/mac.bend as Mc
import ./collections-crypto.bend as C
import bend-collections-laws-crypto@1.0.0.0/src/crypto/aead.bend as A

# A GMAC key (opaque): the AES-GCM algorithm and the raw key
type CcGmacKey is Data:
  CcGmacKey{alg: A.Alg, key: List<&2, U32>}

def cc.gmac.key(ok: Bool, +alg: A.Alg, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcGmacKey>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(o)}}
    case True{}:
      Done{CcGmacKey{alg, B.Octets.to_list(o)}}

def cc.gmac.key_of(+alg: A.Alg, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcGmacKey>:
  cc.gmac.key(Nat.is_eq(B.Octets.len(o), A.key_size(alg)), alg, o)

# GMAC-AES-128: a 16-byte key
def CcGmac.key128(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcGmacKey>:
  cc.gmac.key_of(A.AES_128_GCM{}, o)

# GMAC-AES-256: a 32-byte key
def CcGmac.key256(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcGmacKey>:
  cc.gmac.key_of(A.AES_256_GCM{}, o)

def cc.gmac.tag(+alg: A.Alg, +key: List<&2, U32>, +m: List<&2, U32>) -> B.Octets:
  C.CcRes.or_empty(A.encrypt(alg, key, List.take(&2, U32, m, 12n), List.drop(&2, U32, m, 12n), Nil{}))

# the 16-byte tag of m's data under m's nonce (its first 12 bytes)
def CcGmac.mac(k: CcGmacKey, m: B.Octets) -> B.Octets:
  match k:
    case CcGmacKey{alg, key}:
      cc.gmac.tag(alg, key, B.Octets.to_list(m))

# whether t is m's tag (every byte compared)
def CcGmac.verify(k: CcGmacKey, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~CcGmacKey, ~CcGmac.mac, k, m, t)
