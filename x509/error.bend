# bend-osdev-x509, why a certificate was refused.
import Base
import ../asn1/error.bend as AE
import ../oid/oid.bend as O
import ../oid/text.bend as OT

type X509Error is Data:
  X509Asn1{error: AE.Asn1Error}
  X509BadVersion{}
  X509BadSerial{}
  X509BadAlgorithm{}
  X509AlgMismatch{}
  X509BadName{}
  X509EmptyIssuer{}
  X509BadTime{}
  X509BadKey{}
  X509BadUniqueId{}
  X509EmptyExtensions{}
  X509BadExtension{id: O.Oid}
  X509DuplicateExtension{id: O.Oid}
  X509UnknownCritical{id: O.Oid}

def X509Error.name(e: X509Error) -> String:
  match e:
    case X509Asn1{x}:
      "X509Asn1 " ++ AE.Asn1Error.name(x)
    case X509BadVersion{}:
      "X509BadVersion"
    case X509BadSerial{}:
      "X509BadSerial"
    case X509BadAlgorithm{}:
      "X509BadAlgorithm"
    case X509AlgMismatch{}:
      "X509AlgMismatch"
    case X509BadName{}:
      "X509BadName"
    case X509EmptyIssuer{}:
      "X509EmptyIssuer"
    case X509BadTime{}:
      "X509BadTime"
    case X509BadKey{}:
      "X509BadKey"
    case X509BadUniqueId{}:
      "X509BadUniqueId"
    case X509EmptyExtensions{}:
      "X509EmptyExtensions"
    case X509BadExtension{o}:
      "X509BadExtension " ++ OT.Oid.to_text(o)
    case X509DuplicateExtension{o}:
      "X509DuplicateExtension " ++ OT.Oid.to_text(o)
    case X509UnknownCritical{o}:
      "X509UnknownCritical " ++ OT.Oid.to_text(o)

# Results of asn1's readers as x509's

# r, its failure named e
def x5.or(-A: Data, r: Result<&2, &2, AE.Asn1Error, A>, e: X509Error) -> Result<&2, &2, X509Error, A>:
  match r:
    case Fail{x}:
      Fail{e}
    case Done{v}:
      Done{v}

# r, its failure kept as asn1's
def x5.lift(-A: Data, r: Result<&2, &2, AE.Asn1Error, A>) -> Result<&2, &2, X509Error, A>:
  match r:
    case Fail{x}:
      Fail{X509Asn1{x}}
    case Done{v}:
      Done{v}

# m, its absence named e
def x5.some(-A: Data, m: Maybe<&2, A>, e: X509Error) -> Result<&2, &2, X509Error, A>:
  match m:
    case None{}:
      Fail{e}
    case Some{v}:
      Done{v}

# e unless ok
def x5.check(ok: Bool, e: X509Error) -> Result<&2, &2, X509Error, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# a list of results as a result
def x5.cons(-A: Data, a: Result<&2, &2, X509Error, A>, r: Result<&2, &2, X509Error, List<&2, A>>) -> Result<&2, &2, X509Error, List<&2, A>>:
  match a r:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{xs}:
      Done{Con{x, xs}}

# an Oid read, its failure named e
def x5.oid_or(r: Result<&2, &2, O.OidError, O.Oid>, e: X509Error) -> Result<&2, &2, X509Error, O.Oid>:
  match r:
    case Fail{x}:
      Fail{e}
    case Done{o}:
      Done{o}

# r, its failure renamed e
def x5.or_x(-A: Data, r: Result<&2, &2, X509Error, A>, e: X509Error) -> Result<&2, &2, X509Error, A>:
  match r:
    case Fail{x}:
      Fail{e}
    case Done{v}:
      Done{v}

# r, then f of its value
def x5.then(-A: Data, -C: Data, r: Result<&2, &2, X509Error, A>, f: A -> Result<&2, &2, X509Error, C>) -> Result<&2, &2, X509Error, C>:
  Result.bind(&2, &2, X509Error, A, C, r, f)
