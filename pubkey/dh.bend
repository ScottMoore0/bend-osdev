# Finite-field Diffie-Hellman (the dh package, NIST SP 800-56A) as an
# instance of the key-agreement interface (crypto's kex.bend), over any group
# (~grp: a DhGroup, such as DhGroups.ffdhe2048() of dh/groups.bend):
#   ~N.BnNat, ~N.BnNat, ~PkDh.secret(~grp), ~PkDh.public(~grp),
#   ~PkDh.pk_of(~grp), ~PkDh.pk_to(~grp), ~PkDh.shared(~grp)
# A private key's bytes are the big-endian x in [1, q - 1]; a public key's
# are y as big-endian bytes of p's length; the peer's key is validated in
# full (by the Legendre symbol, for the safe-prime groups the instance is
# meant for: SP 800-56A 5.6.2.3.1, footnote 22) before the primitive, and
# the shared secret Z has p's length. Any group with q = (p - 1) / 2 plugs
# in; for another group, use dh's Dh.agree (y^q mod p = 1) instead.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../dh/dh.bend as D
import ../crypto/crypto.bend as Cr

# dh's errors onto CrError
def PkDh.err(e: D.DhError) -> Cr.CrError:
  match e:
    case D.DhBadPrivateKey{}:
      Cr.CrBadKey{}
    case D.DhBadPublicKey{}:
      Cr.CrBadPublicKey{}
    case D.DhBadSharedSecret{}:
      Cr.CrBadPublicKey{}
    case D.DhBadLength{}:
      Cr.CrBadPublicKey{}

def PkDh.secret(~grp: D.DhGroup, o: B.Octets) -> Result<&2, &2, Cr.CrError, N.BnNat>:
  Cr.CrError.lift(~D.DhError, ~N.BnNat, ~PkDh.err, D.Dh.private_of(grp, o))

def PkDh.public(~grp: D.DhGroup, x: N.BnNat) -> N.BnNat:
  D.Dh.public(grp, x)

# a public key from its bytes (dh's Dh.public_of)
def PkDh.public_of(~grp: D.DhGroup, o: B.Octets) -> Result<&2, &2, D.DhError, N.BnNat>:
  D.Dh.public_of(grp, o)

def PkDh.pk_of(~grp: D.DhGroup, o: B.Octets) -> Result<&2, &2, Cr.CrError, N.BnNat>:
  Cr.CrError.lift(~D.DhError, ~N.BnNat, ~PkDh.err, PkDh.public_of(~grp, o))

def PkDh.pk_to(~grp: D.DhGroup, y: N.BnNat) -> B.Octets:
  D.Dh.public_to(grp, y)

def PkDh.shared(~grp: D.DhGroup, x: N.BnNat, y: N.BnNat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Cr.CrError.lift(~D.DhError, ~B.Octets, ~PkDh.err, D.Dh.agree_safe(grp, x, y))
