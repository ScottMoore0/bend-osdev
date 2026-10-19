# Proofs for bend-osdev-pkcs: a parse answers only messages and keys its
# checks passed (the checks are its last step), and Cms.find_attr answers
# only attributes of the type asked for.
import Base
import ../bytes/bytes.bend as B
import ../oid/oid.bend as O
import ./error.bend as PE
import ./rules.bend as PR
import ./attr.bend as PA
import ./pkcs.bend as P
import ./p8.bend as P8

def pp.disc(r: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pp.fd(-x: PE.PkcsError, -y: P.CmsSignedData, e: {Fail{x} == Done{y} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}) -> Empty:
  %e : pp.disc(_)
  Unit{}

def pp.kdisc(r: Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pp.kfd(-x: PE.PkcsError, -y: P8.Pkcs8Key, e: {Fail{x} == Done{y} : Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>}) -> Empty:
  %e : pp.kdisc(_)
  Unit{}

def pp.mdisc(m: Maybe<&2, PA.CmsAttr>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      Empty

def pp.nd(-y: PA.CmsAttr, e: {None{} == Some{y} : Maybe<&2, PA.CmsAttr>}) -> Empty:
  %e : pp.mdisc(_)
  Unit{}

# SignedData

def pp.fin(q: Result<&2, &2, PE.PkcsError, Unit>, +r: PR.PkcsRules, +s0: P.CmsSignedData, -s: P.CmsSignedData, +hq: {P.pk.conform(r, s0) == q : Result<&2, &2, PE.PkcsError, Unit>}, +e: {P.pk.fin(q, s0) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}) -> {P.CmsSignedData.conforms(r, s) == True{} : Bool}:
  match q:
    case Fail{x}:
      Empty.absurd({P.CmsSignedData.conforms(r, s) == True{} : Bool}, pp.fd(x, s, e))
    case Done{u}:
      +es : {s0 == s : P.CmsSignedData} = Equal.cong(Result<&2, &2, PE.PkcsError, P.CmsSignedData>, P.CmsSignedData, z => Result.default(&2, &2, PE.PkcsError, P.CmsSignedData, z, s0), Done{s0}, Done{s}, e)
      %es : {P.CmsSignedData.conforms(r, _) == True{} : Bool}
      %Equal.sym(Result<&2, &2, PE.PkcsError, Unit>, P.pk.conform(r, s0), Done{u}, hq) : {Result.is_done(&2, &2, PE.PkcsError, Unit, _) == True{} : Bool}
      {==}

def pp.finish(res: Result<&2, &2, PE.PkcsError, P.CmsSignedData>, +r: PR.PkcsRules, -s: P.CmsSignedData, +e: {P.pk.finish(r, res) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}) -> {P.CmsSignedData.conforms(r, s) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({P.CmsSignedData.conforms(r, s) == True{} : Bool}, pp.fd(x, s, e))
    case Done{+s0}:
      pp.fin(P.pk.conform(r, s0), r, s0, s, {==}, e)

# PKCS #8

def pp.kfin(q: Result<&2, &2, PE.PkcsError, Unit>, +r: PR.PkcsRules, +k0: P8.Pkcs8Key, -k: P8.Pkcs8Key, +hq: {P8.pk.p8.conform(r, k0) == q : Result<&2, &2, PE.PkcsError, Unit>}, +e: {P8.pk.p8.fin(q, k0) == Done{k} : Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>}) -> {P8.Pkcs8Key.conforms(r, k) == True{} : Bool}:
  match q:
    case Fail{x}:
      Empty.absurd({P8.Pkcs8Key.conforms(r, k) == True{} : Bool}, pp.kfd(x, k, e))
    case Done{u}:
      +ek : {k0 == k : P8.Pkcs8Key} = Equal.cong(Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>, P8.Pkcs8Key, z => Result.default(&2, &2, PE.PkcsError, P8.Pkcs8Key, z, k0), Done{k0}, Done{k}, e)
      %ek : {P8.Pkcs8Key.conforms(r, _) == True{} : Bool}
      %Equal.sym(Result<&2, &2, PE.PkcsError, Unit>, P8.pk.p8.conform(r, k0), Done{u}, hq) : {Result.is_done(&2, &2, PE.PkcsError, Unit, _) == True{} : Bool}
      {==}

def pp.kfinish(res: Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>, +r: PR.PkcsRules, -k: P8.Pkcs8Key, +e: {P8.pk.p8.finish(r, res) == Done{k} : Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>}) -> {P8.Pkcs8Key.conforms(r, k) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({P8.Pkcs8Key.conforms(r, k) == True{} : Bool}, pp.kfd(x, k, e))
    case Done{+k0}:
      pp.kfin(P8.pk.p8.conform(r, k0), r, k0, k, {==}, e)

# Finding attributes

def pp.find.pick(hit: Bool, +y: PA.CmsAttr, -rest: Maybe<&2, PA.CmsAttr>, +id: O.Oid, -x: PA.CmsAttr, +hh: {O.Oid.is_eq(PA.CmsAttr.attr_type(y), id) == hit : Bool}, +h: {PA.pk.find.pick(hit, y, rest) == Some{x} : Maybe<&2, PA.CmsAttr>}, ih: @h2: {rest == Some{x} : Maybe<&2, PA.CmsAttr>} -> {O.Oid.is_eq(PA.CmsAttr.attr_type(x), id) == True{} : Bool}) -> {O.Oid.is_eq(PA.CmsAttr.attr_type(x), id) == True{} : Bool}:
  match hit:
    case True{}:
      +ey : {y == x : PA.CmsAttr} = Equal.cong(Maybe<&2, PA.CmsAttr>, PA.CmsAttr, z => Maybe.default(&2, PA.CmsAttr, z, y), Some{y}, Some{x}, h)
      %ey : {O.Oid.is_eq(PA.CmsAttr.attr_type(_), id) == True{} : Bool}
      hh
    case False{}:
      ih(h)

def pp.find(xs: List<&2, PA.CmsAttr>, +id: O.Oid, -x: PA.CmsAttr, +h: {PA.Cms.find_attr(xs, id) == Some{x} : Maybe<&2, PA.CmsAttr>}) -> {O.Oid.is_eq(PA.CmsAttr.attr_type(x), id) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({O.Oid.is_eq(PA.CmsAttr.attr_type(x), id) == True{} : Bool}, pp.nd(x, h))
    case Con{+y, +t}:
      pp.find.pick(O.Oid.is_eq(PA.CmsAttr.attr_type(y), id), y, PA.Cms.find_attr(t, id), id, x, {==}, h, h2 => pp.find(t, id, x, h2))
