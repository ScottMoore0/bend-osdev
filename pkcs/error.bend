# bend-osdev-pkcs, why a message or key was refused.
import Base
import ../asn1/error.bend as AE
import ../oid/oid.bend as O
import ../oid/text.bend as OT
import ../x509/error.bend as XE

type PkcsError is Data:
  PkcsAsn1{error: AE.Asn1Error}
  PkcsX509{error: XE.X509Error}
  PkcsNotSignedData{}
  PkcsBadVersion{}
  PkcsBadSigner{}
  PkcsBadContent{}
  PkcsBadAttribute{id: O.Oid}
  PkcsAttrsNotDer{}
  PkcsMissingAttrs{}
  PkcsContentTypeMismatch{}
  PkcsDigestNotListed{}
  PkcsBadKey{}

def PkcsError.name(e: PkcsError) -> String:
  match e:
    case PkcsAsn1{x}:
      "PkcsAsn1 " ++ AE.Asn1Error.name(x)
    case PkcsX509{x}:
      "PkcsX509 " ++ XE.X509Error.name(x)
    case PkcsNotSignedData{}:
      "PkcsNotSignedData"
    case PkcsBadVersion{}:
      "PkcsBadVersion"
    case PkcsBadSigner{}:
      "PkcsBadSigner"
    case PkcsBadContent{}:
      "PkcsBadContent"
    case PkcsBadAttribute{o}:
      "PkcsBadAttribute " ++ OT.Oid.to_text(o)
    case PkcsAttrsNotDer{}:
      "PkcsAttrsNotDer"
    case PkcsMissingAttrs{}:
      "PkcsMissingAttrs"
    case PkcsContentTypeMismatch{}:
      "PkcsContentTypeMismatch"
    case PkcsDigestNotListed{}:
      "PkcsDigestNotListed"
    case PkcsBadKey{}:
      "PkcsBadKey"

# Results of other packages' readers as pkcs's

def pk.or(-A: Data, r: Result<&2, &2, AE.Asn1Error, A>, e: PkcsError) -> Result<&2, &2, PkcsError, A>:
  match r:
    case Fail{x}:
      Fail{e}
    case Done{v}:
      Done{v}

def pk.lift(-A: Data, r: Result<&2, &2, AE.Asn1Error, A>) -> Result<&2, &2, PkcsError, A>:
  match r:
    case Fail{x}:
      Fail{PkcsAsn1{x}}
    case Done{v}:
      Done{v}

def pk.x509(-A: Data, r: Result<&2, &2, XE.X509Error, A>) -> Result<&2, &2, PkcsError, A>:
  match r:
    case Fail{x}:
      Fail{PkcsX509{x}}
    case Done{v}:
      Done{v}

def pk.oid_or(r: Result<&2, &2, O.OidError, O.Oid>, e: PkcsError) -> Result<&2, &2, PkcsError, O.Oid>:
  match r:
    case Fail{x}:
      Fail{e}
    case Done{o}:
      Done{o}

def pk.some(-A: Data, m: Maybe<&2, A>, e: PkcsError) -> Result<&2, &2, PkcsError, A>:
  match m:
    case None{}:
      Fail{e}
    case Some{v}:
      Done{v}

def pk.check(ok: Bool, e: PkcsError) -> Result<&2, &2, PkcsError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def pk.cons(-A: Data, a: Result<&2, &2, PkcsError, A>, r: Result<&2, &2, PkcsError, List<&2, A>>) -> Result<&2, &2, PkcsError, List<&2, A>>:
  match a r:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{xs}:
      Done{Con{x, xs}}

def pk.then(-A: Data, -C: Data, r: Result<&2, &2, PkcsError, A>, f: A -> Result<&2, &2, PkcsError, C>) -> Result<&2, &2, PkcsError, C>:
  Result.bind(&2, &2, PkcsError, A, C, r, f)

def pk.first(rs: List<&2, Result<&2, &2, PkcsError, Unit>>) -> Result<&2, &2, PkcsError, Unit>:
  match rs:
    case Nil{}:
      Done{Unit{}}
    case Con{Fail{e}, t}:
      Fail{e}
    case Con{Done{u}, t}:
      pk.first(t)

def pk.gate(on: Bool, c: Result<&2, &2, PkcsError, Unit>) -> Result<&2, &2, PkcsError, Unit>:
  match on:
    case True{}:
      c
    case False{}:
      Done{Unit{}}
