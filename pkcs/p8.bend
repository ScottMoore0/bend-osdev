# bend-osdev-pkcs, PKCS #8 private keys, unencrypted: RFC 5208's
# PrivateKeyInfo (version 0) and RFC 5958's OneAsymmetricKey (version 0,
# v1, or 1, v2, which may carry the public key):
#
#   OneAsymmetricKey ::= SEQUENCE { version Version,
#     privateKeyAlgorithm PrivateKeyAlgorithmIdentifier,
#     privateKey PrivateKey (OCTET STRING),
#     attributes [0] Attributes OPTIONAL,
#     publicKey [1] PublicKey (BIT STRING) OPTIONAL }
#
# The privateKey octets are the algorithm's format: RSAPrivateKey for
# rsaEncryption, ECPrivateKey for id-ecPublicKey, and for the curves of
# RFC 8410 (Ed25519, Ed448, X25519, X448) an OCTET STRING holding the raw
# key (RFC 8410 section 7, CurvePrivateKey), which Pkcs8.curve_private_key
# reads.
import Base
import ../bytes/bytes.bend as B
import ../asn1/node.bend as AN
import ../asn1/asn1.bend as A
import ../asn1/prim.bend as AP
import ../asn1/bits.bend as ABi
import ../asn1/tag.bend as AT
import ../asn1/schema.bend as ASc
import ../x509/alg.bend as XA
import ./error.bend as PE
import ./rules.bend as PR
import ./schema.bend as PS
import ./attr.bend as PA
import ./signer.bend as PG

type Pkcs8Key is Data:
  Pkcs8Key{version: Nat, alg: XA.X509AlgId, private_key: B.Octets, attributes: List<&2, PA.CmsAttr>, public_key: Maybe<&2, ABi.Asn1Bits>, raw: B.Octets}

# 0 (v1) or 1 (v2)
def Pkcs8Key.version(k: Pkcs8Key) -> Nat:
  match k:
    case Pkcs8Key{v, a, p, x, u, r}:
      v

def Pkcs8Key.alg(k: Pkcs8Key) -> XA.X509AlgId:
  match k:
    case Pkcs8Key{v, a, p, x, u, r}:
      a

# the privateKey OCTET STRING's contents
def Pkcs8Key.private_key(k: Pkcs8Key) -> B.Octets:
  match k:
    case Pkcs8Key{v, a, p, x, u, r}:
      p

def Pkcs8Key.attributes(k: Pkcs8Key) -> List<&2, PA.CmsAttr>:
  match k:
    case Pkcs8Key{v, a, p, x, u, r}:
      x

def Pkcs8Key.public_key(k: Pkcs8Key) -> Maybe<&2, ABi.Asn1Bits>:
  match k:
    case Pkcs8Key{v, a, p, x, u, r}:
      u

def Pkcs8Key.raw(k: Pkcs8Key) -> B.Octets:
  match k:
    case Pkcs8Key{v, a, p, x, u, r}:
      r

# Reading

def pk.p8.pub(+r: PR.PkcsRules, m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, PE.PkcsError, Maybe<&2, ABi.Asn1Bits>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{n}:
      Result.map(&2, &2, PE.PkcsError, ABi.Asn1Bits, Maybe<&2, ABi.Asn1Bits>, b => Some{b}, PE.pk.or(ABi.Asn1Bits, ABi.Asn1.get_bits_as(PR.PkcsRules.asn1(r), AT.Asn1Tag.context(1n), n), PE.PkcsBadKey{}))

def pk.p8.of(+r: PR.PkcsRules, +m: ASc.Asn1Match) -> Result<&2, &2, PE.PkcsError, Pkcs8Key>:
  +v = PG.pk.nat(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), PE.PkcsBadVersion{})
  +a = PE.pk.x509(XA.X509AlgId, XA.X509AlgId.of_match(ASc.Asn1Match.at(m, 1n)))
  +p = PG.pk.octets(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 2n)), PE.PkcsBadKey{})
  +x = PA.pk.attrs.of(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 3n)))
  +u = pk.p8.pub(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 4n)))
  +raw = ASc.Asn1Match.raw(m)
  PE.pk.then(Nat, Pkcs8Key, v, v1 => PE.pk.then(XA.X509AlgId, Pkcs8Key, a, a1 => PE.pk.then(B.Octets, Pkcs8Key, p, p1 => PE.pk.then(List<&2, PA.CmsAttr>, Pkcs8Key, x, x1 => PE.pk.then(Maybe<&2, ABi.Asn1Bits>, Pkcs8Key, u, u1 => Done{Pkcs8Key{v1, a1, p1, x1, u1, raw}})))))

# RFC 5958 section 2: v1 or v2, v2 when the public key is present
def pk.p8.conform(+r: PR.PkcsRules, +k: Pkcs8Key) -> Result<&2, &2, PE.PkcsError, Unit>:
  +v = Pkcs8Key.version(k)
  PE.pk.gate(PR.PkcsRules.versions(r), PE.pk.check(Bool.and(Nat.is_le(v, 1n), Bool.or(Bool.not(Maybe.is_some(&2, ABi.Asn1Bits, Pkcs8Key.public_key(k))), Nat.is_eq(v, 1n))), PE.PkcsBadVersion{}))

# whether a key passes every check its rules ask for
def Pkcs8Key.conforms(+r: PR.PkcsRules, k: Pkcs8Key) -> Bool:
  Result.is_done(&2, &2, PE.PkcsError, Unit, pk.p8.conform(r, k))

def pk.p8.fin(q: Result<&2, &2, PE.PkcsError, Unit>, k: Pkcs8Key) -> Result<&2, &2, PE.PkcsError, Pkcs8Key>:
  match q:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{k}

def pk.p8.finish(+r: PR.PkcsRules, res: Result<&2, &2, PE.PkcsError, Pkcs8Key>) -> Result<&2, &2, PE.PkcsError, Pkcs8Key>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{+k}:
      pk.p8.fin(pk.p8.conform(r, k), k)

def pk.p8.parse0(+r: PR.PkcsRules, b: B.Octets) -> Result<&2, &2, PE.PkcsError, Pkcs8Key>:
  PE.pk.then(ASc.Asn1Match, Pkcs8Key, PE.pk.lift(ASc.Asn1Match, ASc.Asn1.match(PR.PkcsRules.asn1(r), PS.pk.s.key(), b)), m => pk.p8.of(r, m))

# the key whose PrivateKeyInfo or OneAsymmetricKey octets b are
def Pkcs8.parse(+r: PR.PkcsRules, b: B.Octets) -> Result<&2, &2, PE.PkcsError, Pkcs8Key>:
  pk.p8.finish(r, pk.p8.parse0(r, b))

# an RFC 8410 curve's raw private key: the privateKey octets read as an
# OCTET STRING (CurvePrivateKey)
def Pkcs8.curve_private_key(+r: PR.PkcsRules, k: Pkcs8Key) -> Result<&2, &2, PE.PkcsError, B.Octets>:
  PE.pk.then(AN.Asn1Node, B.Octets, PE.pk.or(AN.Asn1Node, A.Asn1.decode(PR.PkcsRules.asn1(r), Pkcs8Key.private_key(k)), PE.PkcsBadKey{}), n => PE.pk.or(B.Octets, AP.Asn1.get_octets(PR.PkcsRules.asn1(r), n), PE.PkcsBadKey{}))
