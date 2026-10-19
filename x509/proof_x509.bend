# Proofs for bend-osdev-x509: a parse answers only certificates its checks
# passed (the checks are its last step), and X509.find_ext answers only
# extensions with the identifier asked for.
import Base
import ../bytes/bytes.bend as B
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./ext.bend as XX
import ./x509.bend as X

def xp.disc(r: Result<&2, &2, XE.X509Error, X.X509Cert>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def xp.fd(-x: XE.X509Error, -y: X.X509Cert, e: {Fail{x} == Done{y} : Result<&2, &2, XE.X509Error, X.X509Cert>}) -> Empty:
  %e : xp.disc(_)
  Unit{}

def xp.mdisc(m: Maybe<&2, XX.X509Ext>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      Empty

def xp.nd(-y: XX.X509Ext, e: {None{} == Some{y} : Maybe<&2, XX.X509Ext>}) -> Empty:
  %e : xp.mdisc(_)
  Unit{}

def xp.fin(q: Result<&2, &2, XE.X509Error, Unit>, +r: XR.X509Rules, +c0: X.X509Cert, -c: X.X509Cert, +hq: {X.x5.conform(r, c0) == q : Result<&2, &2, XE.X509Error, Unit>}, +e: {X.x5.fin(q, c0) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}) -> {X.X509Cert.conforms(r, c) == True{} : Bool}:
  match q:
    case Fail{x}:
      Empty.absurd({X.X509Cert.conforms(r, c) == True{} : Bool}, xp.fd(x, c, e))
    case Done{u}:
      +ec : {c0 == c : X.X509Cert} = Equal.cong(Result<&2, &2, XE.X509Error, X.X509Cert>, X.X509Cert, z => Result.default(&2, &2, XE.X509Error, X.X509Cert, z, c0), Done{c0}, Done{c}, e)
      %ec : {X.X509Cert.conforms(r, _) == True{} : Bool}
      %Equal.sym(Result<&2, &2, XE.X509Error, Unit>, X.x5.conform(r, c0), Done{u}, hq) : {Result.is_done(&2, &2, XE.X509Error, Unit, _) == True{} : Bool}
      {==}

def xp.finish(res: Result<&2, &2, XE.X509Error, X.X509Cert>, +r: XR.X509Rules, -c: X.X509Cert, +e: {X.x5.finish(r, res) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}) -> {X.X509Cert.conforms(r, c) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({X.X509Cert.conforms(r, c) == True{} : Bool}, xp.fd(x, c, e))
    case Done{+c0}:
      xp.fin(X.x5.conform(r, c0), r, c0, c, {==}, e)

def xp.find.pick(hit: Bool, +y: XX.X509Ext, -rest: Maybe<&2, XX.X509Ext>, +id: O.Oid, -x: XX.X509Ext, +hh: {O.Oid.is_eq(XX.X509Ext.id(y), id) == hit : Bool}, +h: {XX.x5.find.pick(hit, y, rest) == Some{x} : Maybe<&2, XX.X509Ext>}, ih: @h2: {rest == Some{x} : Maybe<&2, XX.X509Ext>} -> {O.Oid.is_eq(XX.X509Ext.id(x), id) == True{} : Bool}) -> {O.Oid.is_eq(XX.X509Ext.id(x), id) == True{} : Bool}:
  match hit:
    case True{}:
      +ey : {y == x : XX.X509Ext} = Equal.cong(Maybe<&2, XX.X509Ext>, XX.X509Ext, z => Maybe.default(&2, XX.X509Ext, z, y), Some{y}, Some{x}, h)
      %ey : {O.Oid.is_eq(XX.X509Ext.id(_), id) == True{} : Bool}
      hh
    case False{}:
      ih(h)

def xp.find(es: List<&2, XX.X509Ext>, +id: O.Oid, -x: XX.X509Ext, +h: {XX.X509.find_ext(es, id) == Some{x} : Maybe<&2, XX.X509Ext>}) -> {O.Oid.is_eq(XX.X509Ext.id(x), id) == True{} : Bool}:
  match es:
    case Nil{}:
      Empty.absurd({O.Oid.is_eq(XX.X509Ext.id(x), id) == True{} : Bool}, xp.nd(x, h))
    case Con{+y, +t}:
      xp.find.pick(O.Oid.is_eq(XX.X509Ext.id(y), id), y, XX.X509.find_ext(t, id), id, x, {==}, h, h2 => xp.find(t, id, x, h2))
