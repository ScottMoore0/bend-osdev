# Ed25519 (RFC 8032 section 5.1) as a signature scheme: bend-collections'
# signatures (sign.bend), which its laws prove to be RFC 8032's key
# generation, signing and verification for every key and message.
# Verification is the cofactorless check [S]B = R + [k]A' that section 5.1.7
# allows, with S < L required; it refuses a public key or R that does not
# decode (section 5.1.3).
#
# A secret key is the 32-byte seed (section 5.1.5), a public key the 32-byte
# encoding of A, a signature 64 bytes (R || S). Signing is deterministic, as
# RFC 8032 defines it.
#
# The instance:
#   ~CcEdSk, ~CcEdPk, ~CcEd25519.secret, ~CcEd25519.public,
#   ~CcEd25519.pk_of, ~CcEd25519.pk_to, ~CcEd25519.sign, ~CcEd25519.verify
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ./collections-crypto.bend as C
import bend-collections-laws-crypto@1.0.0.0/src/crypto/sign.bend as SG

# A secret key (opaque): the 32-byte seed
type CcEdSk is Data:
  CcEdSk{seed: List<&2, U32>}

# A public key (opaque): 32 bytes
type CcEdPk is Data:
  CcEdPk{key: B.Octets}

def cc.ed.secret(ok: Bool, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcEdSk>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(o)}}
    case True{}:
      Done{CcEdSk{B.Octets.to_list(o)}}

def cc.ed.secret_of(+o: B.Octets) -> Result<&2, &2, Cr.CrError, CcEdSk>:
  cc.ed.secret(Nat.is_eq(B.Octets.len(o), 32n), o)

# The secret key of a 32-byte seed (CrBadKeyLength otherwise)
def CcEd25519.secret(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcEdSk>:
  cc.ed.secret_of(o)

def cc.ed.public(m: Maybe<&2, SG.Keypair>) -> CcEdPk:
  match m:
    case None{}:
      CcEdPk{B.Octets.empty()}
    case Some{kp}:
      match kp:
        case SG.Keypair{s, p}:
          CcEdPk{B.Octets.of_list(p)}

# Its public key, the encoding of [s]B (section 5.1.5)
def CcEd25519.public(k: CcEdSk) -> CcEdPk:
  match k:
    case CcEdSk{seed}:
      cc.ed.public(SG.generate_keypair(seed))

def cc.ed.pk(ok: Bool, +o: B.Octets) -> Result<&2, &2, Cr.CrError, CcEdPk>:
  match ok:
    case False{}:
      Fail{Cr.CrBadPublicKey{}}
    case True{}:
      Done{CcEdPk{o}}

def cc.ed.pk_of(+o: B.Octets) -> Result<&2, &2, Cr.CrError, CcEdPk>:
  cc.ed.pk(Nat.is_eq(B.Octets.len(o), 32n), o)

# A public key of 32 bytes (CrBadPublicKey otherwise; whether it decodes to
# a point is verification's question, as section 5.1.7 asks it)
def CcEd25519.pk_of(o: B.Octets) -> Result<&2, &2, Cr.CrError, CcEdPk>:
  cc.ed.pk_of(o)

# a public key's bytes
def CcEd25519.pk_to(p: CcEdPk) -> B.Octets:
  match p:
    case CcEdPk{o}:
      o

# The 64-byte signature of a message (section 5.1.6)
def CcEd25519.sign(k: CcEdSk, m: B.Octets) -> B.Octets:
  match k:
    case CcEdSk{seed}:
      C.CcRes.or_empty(SG.sign(seed, B.Octets.to_list(m)))

# Whether a signature is valid for a message (section 5.1.7)
def CcEd25519.verify(p: CcEdPk, m: B.Octets, s: B.Octets) -> Bool:
  match p:
    case CcEdPk{o}:
      SG.verify(B.Octets.to_list(o), B.Octets.to_list(m), B.Octets.to_list(s))
