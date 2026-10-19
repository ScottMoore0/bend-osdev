# bend-osdev-x509, AlgorithmIdentifier (RFC 5280 4.1.1.2): an algorithm's
# object identifier, its parameters if any (left as an element: their type
# is the algorithm's), and the exact octets read, which RFC 5280 4.1.1.2
# compares between the certificate's two signature algorithm fields.
import Base
import ../bytes/bytes.bend as B
import ../asn1/node.bend as AN
import ../asn1/asn1.bend as A
import ../asn1/schema.bend as ASc
import ../oid/oid.bend as O
import ./error.bend as XE

type X509AlgId is Data:
  X509AlgId{oid: O.Oid, params: Maybe<&2, AN.Asn1Node>, raw: B.Octets}

def X509AlgId.oid(a: X509AlgId) -> O.Oid:
  match a:
    case X509AlgId{o, p, r}:
      o

def X509AlgId.params(a: X509AlgId) -> Maybe<&2, AN.Asn1Node>:
  match a:
    case X509AlgId{o, p, r}:
      p

def X509AlgId.raw(a: X509AlgId) -> B.Octets:
  match a:
    case X509AlgId{o, p, r}:
      r

# whether two identifiers are the same octets
def X509AlgId.is_eq(a: X509AlgId, b: X509AlgId) -> Bool:
  B.Octets.is_eq(X509AlgId.raw(a), X509AlgId.raw(b))

def x5.alg.mk(r: Result<&2, &2, XE.X509Error, O.Oid>, p: Maybe<&2, AN.Asn1Node>, raw: B.Octets) -> Result<&2, &2, XE.X509Error, X509AlgId>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      Done{X509AlgId{o, p, raw}}

def x5.alg.oid(m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, O.Oid>:
  match m:
    case None{}:
      Fail{XE.X509BadAlgorithm{}}
    case Some{n}:
      XE.x5.oid_or(O.Oid.of_node(n), XE.X509BadAlgorithm{})

# an AlgorithmIdentifier matched against x5.s.alg()
def x5.alg.of(+m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509AlgId>:
  x5.alg.mk(x5.alg.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))), ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), ASc.Asn1Match.raw(m))

# an AlgorithmIdentifier matched against X509.schema_alg()
def X509AlgId.of_match(+m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509AlgId>:
  x5.alg.of(m)
