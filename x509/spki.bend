# bend-osdev-x509, SubjectPublicKeyInfo (RFC 5280 4.1.2.7): the key's
# algorithm and the key itself as a BIT STRING, whose format is the
# algorithm's (RSAPublicKey for rsaEncryption, an EC point for
# id-ecPublicKey, the raw key for Ed25519). The exact octets of the whole
# structure are kept: some identifiers (subjectKeyIdentifier's method 1,
# 4.2.1.2) and some key formats are computed over them.
import Base
import ../bytes/bytes.bend as B
import ../asn1/node.bend as AN
import ../asn1/bits.bend as ABi
import ../asn1/schema.bend as ASc
import ./error.bend as XE
import ./rules.bend as XR
import ./alg.bend as XA

type X509Spki is Data:
  X509Spki{alg: XA.X509AlgId, key: ABi.Asn1Bits, raw: B.Octets}

def X509Spki.alg(s: X509Spki) -> XA.X509AlgId:
  match s:
    case X509Spki{a, k, r}:
      a

def X509Spki.key(s: X509Spki) -> ABi.Asn1Bits:
  match s:
    case X509Spki{a, k, r}:
      k

def X509Spki.raw(s: X509Spki) -> B.Octets:
  match s:
    case X509Spki{a, k, r}:
      r

def x5.whole_octets(+b: ABi.Asn1Bits) -> Maybe<&2, B.Octets>:
  Bool.pick(Maybe<&2, B.Octets>, Nat.is_eq(ABi.Asn1Bits.unused(b), 0n), Some{ABi.Asn1Bits.octets(b)}, None{})

# the key's octets (None when the BIT STRING is not whole octets)
def X509Spki.key_octets(s: X509Spki) -> Maybe<&2, B.Octets>:
  x5.whole_octets(X509Spki.key(s))

def x5.spki.mk(a: Result<&2, &2, XE.X509Error, XA.X509AlgId>, k: Result<&2, &2, XE.X509Error, ABi.Asn1Bits>, raw: B.Octets) -> Result<&2, &2, XE.X509Error, X509Spki>:
  match a k:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{y}:
      Done{X509Spki{x, y, raw}}

def x5.bits.of(+r: XR.X509Rules, m: Maybe<&2, AN.Asn1Node>, e: XE.X509Error) -> Result<&2, &2, XE.X509Error, ABi.Asn1Bits>:
  match m:
    case None{}:
      Fail{e}
    case Some{n}:
      XE.x5.or(ABi.Asn1Bits, ABi.Asn1.get_bits(XR.X509Rules.asn1(r), n), e)

# a SubjectPublicKeyInfo matched against x5.s.spki()
def x5.spki.of(+r: XR.X509Rules, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Spki>:
  x5.spki.mk(XA.x5.alg.of(ASc.Asn1Match.at(m, 0n)), x5.bits.of(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), XE.X509BadKey{}), ASc.Asn1Match.raw(m))
