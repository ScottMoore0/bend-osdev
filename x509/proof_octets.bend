# Proofs for bend-osdev-x509: the octets a parse keeps. X509.parse matches
# the input against the certificate's schema (bend-osdev-asn1) and reads
# each field from a field's match; the octets it keeps for the certificate,
# the tbsCertificate, the names, the algorithm identifiers, the key and each
# extension are the octets of those matches (xq.tbs, xq.cert, xq.parsed, by
# following each step of the readers' Result chains, xq.then), so asn1's
# match laws (match_split, match_whole, match_within, match_input) make
# them slices of the input, one inside another as the certificate's ASN.1
# nests them.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/schema.bend as ASc
import ../asn1/bits.bend as ABi
import ../asn1/LAWS.bend as AL
import ../asn1/PROOF.bend as AP
import ../oid/oid.bend as O
import ./error.bend as XE
import ./rules.bend as XR
import ./schema.bend as XS
import ./alg.bend as XA
import ./name.bend as XN
import ./validity.bend as XV
import ./spki.bend as XK
import ./ext.bend as XX
import ./x509.bend as X

# a step of a Result chain: whatever follows a value read holds of the chain
def xq.then(-A: Data, -C: Data, a: Result<&2, &2, XE.X509Error, A>, k: A -> Result<&2, &2, XE.X509Error, C>, -Q: Result<&2, &2, XE.X509Error, C> -> Type, hf: @x: XE.X509Error -> Q(Fail{x}), hk: @v: A -> @ev: {a == Done{v} : Result<&2, &2, XE.X509Error, A>} -> Q(k(v))) -> Q(XE.x5.then(A, C, a, k)):
  match a:
    case Fail{x}:
      hf(x)
    case Done{+v}:
      hk(v, {==})

def xq.rdisc(-A: Data, z: Result<&2, &2, XE.X509Error, A>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def xq.rfd(-A: Data, -x: XE.X509Error, -y: A, e: {Fail{x} == Done{y} : Result<&2, &2, XE.X509Error, A>}) -> Empty:
  %e : xq.rdisc(A, _)
  Unit{}

# Each field's kept octets: its match's

def xq.nraw(z: Result<&2, &2, XE.X509Error, XN.X509Name>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{n}:
      XN.X509Name.raw(n)

def xq.name_mk(rs: Result<&2, &2, XE.X509Error, List<&2, List<&2, XN.X509Atv>>>, +raw: B.Octets, +n: XN.X509Name, +e: {XN.x5.name.mk(rs, raw) == Done{n} : Result<&2, &2, XE.X509Error, XN.X509Name>}) -> {XN.X509Name.raw(n) == raw : B.Octets}:
  match rs:
    case Fail{x}:
      Empty.absurd({XN.X509Name.raw(n) == raw : B.Octets}, xq.rfd(XN.X509Name, x, n, e))
    case Done{+l}:
      Equal.sym(B.Octets, raw, XN.X509Name.raw(n), Equal.cong(Result<&2, &2, XE.X509Error, XN.X509Name>, B.Octets, z => xq.nraw(z), Done{XN.X509Name{l, raw}}, Done{n}, e))

def xq.name_raw(+m: ASc.Asn1Match, +n: XN.X509Name, +e: {XN.x5.name.of(m) == Done{n} : Result<&2, &2, XE.X509Error, XN.X509Name>}) -> {XN.X509Name.raw(n) == ASc.Asn1Match.raw(m) : B.Octets}:
  xq.name_mk(XN.x5.rdns(ASc.Asn1Match.items(m)), ASc.Asn1Match.raw(m), n, e)

def xq.araw(z: Result<&2, &2, XE.X509Error, XA.X509AlgId>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{a}:
      XA.X509AlgId.raw(a)

def xq.alg_mk(r0: Result<&2, &2, XE.X509Error, O.Oid>, +p: Maybe<&2, AN.Asn1Node>, +raw: B.Octets, +a: XA.X509AlgId, +e: {XA.x5.alg.mk(r0, p, raw) == Done{a} : Result<&2, &2, XE.X509Error, XA.X509AlgId>}) -> {XA.X509AlgId.raw(a) == raw : B.Octets}:
  match r0:
    case Fail{x}:
      Empty.absurd({XA.X509AlgId.raw(a) == raw : B.Octets}, xq.rfd(XA.X509AlgId, x, a, e))
    case Done{+o}:
      Equal.sym(B.Octets, raw, XA.X509AlgId.raw(a), Equal.cong(Result<&2, &2, XE.X509Error, XA.X509AlgId>, B.Octets, z => xq.araw(z), Done{XA.X509AlgId{o, p, raw}}, Done{a}, e))

def xq.alg_raw(+m: ASc.Asn1Match, +a: XA.X509AlgId, +e: {XA.x5.alg.of(m) == Done{a} : Result<&2, &2, XE.X509Error, XA.X509AlgId>}) -> {XA.X509AlgId.raw(a) == ASc.Asn1Match.raw(m) : B.Octets}:
  xq.alg_mk(XA.x5.alg.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))), ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), ASc.Asn1Match.raw(m), a, e)

def xq.kraw(z: Result<&2, &2, XE.X509Error, XK.X509Spki>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{k}:
      XK.X509Spki.raw(k)

def xq.spki_mk(a0: Result<&2, &2, XE.X509Error, XA.X509AlgId>, k0: Result<&2, &2, XE.X509Error, ABi.Asn1Bits>, +raw: B.Octets, +k: XK.X509Spki, +e: {XK.x5.spki.mk(a0, k0, raw) == Done{k} : Result<&2, &2, XE.X509Error, XK.X509Spki>}) -> {XK.X509Spki.raw(k) == raw : B.Octets}:
  match a0 k0:
    case Fail{x} _:
      Empty.absurd({XK.X509Spki.raw(k) == raw : B.Octets}, xq.rfd(XK.X509Spki, x, k, e))
    case Done{y} Fail{x}:
      Empty.absurd({XK.X509Spki.raw(k) == raw : B.Octets}, xq.rfd(XK.X509Spki, x, k, e))
    case Done{+y} Done{+z}:
      Equal.sym(B.Octets, raw, XK.X509Spki.raw(k), Equal.cong(Result<&2, &2, XE.X509Error, XK.X509Spki>, B.Octets, q => xq.kraw(q), Done{XK.X509Spki{y, z, raw}}, Done{k}, e))

def xq.spki_raw(+r: XR.X509Rules, +m: ASc.Asn1Match, +k: XK.X509Spki, +e: {XK.x5.spki.of(r, m) == Done{k} : Result<&2, &2, XE.X509Error, XK.X509Spki>}) -> {XK.X509Spki.raw(k) == ASc.Asn1Match.raw(m) : B.Octets}:
  xq.spki_mk(XA.x5.alg.of(ASc.Asn1Match.at(m, 0n)), XK.x5.bits.of(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), XE.X509BadKey{}), ASc.Asn1Match.raw(m), k, e)

def xq.xraw(z: Result<&2, &2, XE.X509Error, XX.X509Ext>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{y}:
      XX.X509Ext.raw(y)

def xq.ext_mk(+id: O.Oid, c0: Result<&2, &2, XE.X509Error, Bool>, v0: Result<&2, &2, XE.X509Error, B.Octets>, +raw: B.Octets, +x: XX.X509Ext, +e: {XX.x5.ext.mk(id, c0, v0, raw) == Done{x} : Result<&2, &2, XE.X509Error, XX.X509Ext>}) -> {XX.X509Ext.raw(x) == raw : B.Octets}:
  match c0 v0:
    case Fail{y} _:
      Empty.absurd({XX.X509Ext.raw(x) == raw : B.Octets}, xq.rfd(XX.X509Ext, y, x, e))
    case Done{c} Fail{y}:
      Empty.absurd({XX.X509Ext.raw(x) == raw : B.Octets}, xq.rfd(XX.X509Ext, y, x, e))
    case Done{+c} Done{+w}:
      Equal.sym(B.Octets, raw, XX.X509Ext.raw(x), Equal.cong(Result<&2, &2, XE.X509Error, XX.X509Ext>, B.Octets, q => xq.xraw(q), Done{XX.X509Ext{id, c, w, raw}}, Done{x}, e))

def xq.ext_with(+r: XR.X509Rules, +m: ASc.Asn1Match, i0: Result<&2, &2, XE.X509Error, O.Oid>, +x: XX.X509Ext, +e: {XX.x5.ext.with(r, m, i0) == Done{x} : Result<&2, &2, XE.X509Error, XX.X509Ext>}) -> {XX.X509Ext.raw(x) == ASc.Asn1Match.raw(m) : B.Octets}:
  match i0:
    case Fail{y}:
      Empty.absurd({XX.X509Ext.raw(x) == ASc.Asn1Match.raw(m) : B.Octets}, xq.rfd(XX.X509Ext, y, x, e))
    case Done{+id}:
      xq.ext_mk(id, XX.x5.ext.bool(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)), id), XX.x5.ext.octets(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 2n)), id), ASc.Asn1Match.raw(m), x, e)

def xq.ext_raw(+r: XR.X509Rules, +m: ASc.Asn1Match, +x: XX.X509Ext, +e: {XX.x5.ext.of(r, m) == Done{x} : Result<&2, &2, XE.X509Error, XX.X509Ext>}) -> {XX.X509Ext.raw(x) == ASc.Asn1Match.raw(m) : B.Octets}:
  xq.ext_with(r, m, XX.x5.ext.id(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))), x, e)

# Extensions: each one's octets are its match's, in order

def xq.eall(ms: List<&2, ASc.Asn1Match>, es: List<&2, XX.X509Ext>) -> Type:
  match ms es:
    case Nil{} Nil{}:
      Unit
    case Con{m, t} Con{x, u}:
      {XX.X509Ext.raw(x) == ASc.Asn1Match.raw(m) : B.Octets} & xq.eall(t, u)
    case Nil{} Con{x, u}:
      Empty
    case Con{m, t} Nil{}:
      Empty

def xq.ep(ms: List<&2, ASc.Asn1Match>, z: Result<&2, &2, XE.X509Error, List<&2, XX.X509Ext>>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{es}:
      xq.eall(ms, es)

def xq.econs(+r: XR.X509Rules, +m0: ASc.Asn1Match, +t: List<&2, ASc.Asn1Match>, a: Result<&2, &2, XE.X509Error, XX.X509Ext>, b: Result<&2, &2, XE.X509Error, List<&2, XX.X509Ext>>, +ha: {XX.x5.ext.of(r, m0) == a : Result<&2, &2, XE.X509Error, XX.X509Ext>}, hb: xq.ep(t, b)) -> xq.ep(Con{m0, t}, XE.x5.cons(XX.X509Ext, a, b)):
  match a b:
    case Fail{y} _:
      Unit{}
    case Done{x} Fail{y}:
      Unit{}
    case Done{+x} Done{es}:
      (xq.ext_raw(r, m0, x, ha), hb)

def xq.exts_ok(+r: XR.X509Rules, ms: List<&2, ASc.Asn1Match>) -> xq.ep(ms, XX.x5.exts.of(r, ms)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{+m0, +t}:
      xq.econs(r, m0, t, XX.x5.ext.of(r, m0), XX.x5.exts.of(r, t), {==}, xq.exts_ok(r, t))

def xq.split_ty(ms: List<&2, ASc.Asn1Match>, +x: XX.X509Ext) -> Type:
  Sigma<&1, &1, List<&2, ASc.Asn1Match>, mpre => Sigma<&1, &1, ASc.Asn1Match, mx => Sigma<&1, &1, List<&2, ASc.Asn1Match>, mpost => {ms == List.append(&2, ASc.Asn1Match, mpre, Con{mx, mpost}) : List<&2, ASc.Asn1Match>} & {XX.X509Ext.raw(x) == ASc.Asn1Match.raw(mx) : B.Octets}>>>

def xq.es_step(+m0: ASc.Asn1Match, +t: List<&2, ASc.Asn1Match>, +x: XX.X509Ext, ih: xq.split_ty(t, x)) -> xq.split_ty(Con{m0, t}, x):
  (+mpre, (+mx, (+mpost, (+e1, +e2)))) = ih
  (Con{m0, mpre}, (mx, (mpost, (Equal.cong(List<&2, ASc.Asn1Match>, List<&2, ASc.Asn1Match>, z => Con{m0, z}, t, List.append(&2, ASc.Asn1Match, mpre, Con{mx, mpost}), e1), e2))))

def xq.eall_split(ms: List<&2, ASc.Asn1Match>, pre: List<&2, XX.X509Ext>, +x: XX.X509Ext, +post: List<&2, XX.X509Ext>, h: xq.eall(ms, List.append(&2, XX.X509Ext, pre, Con{x, post}))) -> xq.split_ty(ms, x):
  match ms pre:
    case Nil{} Nil{}:
      Empty.absurd(xq.split_ty(Nil{}, x), h)
    case Nil{} Con{p, u}:
      Empty.absurd(xq.split_ty(Nil{}, x), h)
    case Con{+m0, +t} Nil{}:
      (hx, ht) = h
      (Nil{}, (m0, (t, ({==}, hx))))
    case Con{+m0, +t} Con{p, +u}:
      (hp, ht) = h
      xq.es_step(m0, t, x, xq.eall_split(t, u, x, post, ht))

def xq.ecast(+ms: List<&2, ASc.Asn1Match>, +es: List<&2, XX.X509Ext>, +es2: List<&2, XX.X509Ext>, +h: {es == es2 : List<&2, XX.X509Ext>}, he: xq.eall(ms, es)) -> xq.eall(ms, es2):
  %h : xq.eall(ms, _)
  he

def xq.epcast(+ms: List<&2, ASc.Asn1Match>, z: Result<&2, &2, XE.X509Error, List<&2, XX.X509Ext>>, +es: List<&2, XX.X509Ext>, +h: {z == Done{es} : Result<&2, &2, XE.X509Error, List<&2, XX.X509Ext>>}, hz: xq.ep(ms, z)) -> xq.eall(ms, es):
  %h : xq.ep(ms, _)
  hz

# The tbsCertificate's kept octets and its fields'

def xq.tp(+r: XR.X509Rules, +m: ASc.Asn1Match, z: Result<&2, &2, XE.X509Error, X.X509Tbs>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{t}:
      {X.X509Tbs.raw(t) == ASc.Asn1Match.raw(m) : B.Octets} & ({XN.X509Name.raw(X.X509Tbs.issuer(t)) == ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 3n)) : B.Octets} & ({XN.X509Name.raw(X.X509Tbs.subject(t)) == ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 5n)) : B.Octets} & ({XK.X509Spki.raw(X.X509Tbs.spki(t)) == ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 6n)) : B.Octets} & ({XA.X509AlgId.raw(X.X509Tbs.signature(t)) == ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 2n)) : B.Octets} & {XX.x5.exts.of(r, ASc.Asn1Match.items(ASc.Asn1Match.inner(ASc.Asn1Match.at(m, 9n)))) == Done{X.X509Tbs.extensions(t)} : Result<&2, &2, XE.X509Error, List<&2, XX.X509Ext>>}))))

# the parse keeps, of a tbsCertificate matched as m, m's octets and the
# octets of its fields' matches (generated by the expression in x5.tbs.of)
def xq.tbs(+r: XR.X509Rules, +m: ASc.Asn1Match) -> xq.tp(r, m, X.x5.tbs.of(r, m)):
  +v = X.x5.version(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)))
  +s = X.x5.serial(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n)))
  +a = XA.x5.alg.of(ASc.Asn1Match.at(m, 2n))
  +i = XN.x5.name.of(ASc.Asn1Match.at(m, 3n))
  +va = XV.x5.validity.of(r, ASc.Asn1Match.at(m, 4n))
  +su = XN.x5.name.of(ASc.Asn1Match.at(m, 5n))
  +k = XK.x5.spki.of(r, ASc.Asn1Match.at(m, 6n))
  +iu = X.x5.uid(r, 1n, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 7n)))
  +su2 = X.x5.uid(r, 2n, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 8n)))
  +xm = ASc.Asn1Match.at(m, 9n)
  +x = XX.x5.exts.of(r, ASc.Asn1Match.items(ASc.Asn1Match.inner(xm)))
  +xp = ASc.Asn1Match.present(xm)
  +raw = ASc.Asn1Match.raw(m)
  xq.then(Nat, X.X509Tbs, v, v1 => XE.x5.then(B.Octets, X.X509Tbs, s, s1 => XE.x5.then(XA.X509AlgId, X.X509Tbs, a, a1 => XE.x5.then(XN.X509Name, X.X509Tbs, i, i1 => XE.x5.then(XV.X509Validity, X.X509Tbs, va, va1 => XE.x5.then(XN.X509Name, X.X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}))))))))), z => xq.tp(r, m, z), x0 => Unit{}, +v1 => +ev => xq.then(B.Octets, X.X509Tbs, s, s1 => XE.x5.then(XA.X509AlgId, X.X509Tbs, a, a1 => XE.x5.then(XN.X509Name, X.X509Tbs, i, i1 => XE.x5.then(XV.X509Validity, X.X509Tbs, va, va1 => XE.x5.then(XN.X509Name, X.X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}})))))))), z => xq.tp(r, m, z), x0 => Unit{}, +s1 => +es => xq.then(XA.X509AlgId, X.X509Tbs, a, a1 => XE.x5.then(XN.X509Name, X.X509Tbs, i, i1 => XE.x5.then(XV.X509Validity, X.X509Tbs, va, va1 => XE.x5.then(XN.X509Name, X.X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}))))))), z => xq.tp(r, m, z), x0 => Unit{}, +a1 => +ea => xq.then(XN.X509Name, X.X509Tbs, i, i1 => XE.x5.then(XV.X509Validity, X.X509Tbs, va, va1 => XE.x5.then(XN.X509Name, X.X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}})))))), z => xq.tp(r, m, z), x0 => Unit{}, +i1 => +ei => xq.then(XV.X509Validity, X.X509Tbs, va, va1 => XE.x5.then(XN.X509Name, X.X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}))))), z => xq.tp(r, m, z), x0 => Unit{}, +va1 => +eva => xq.then(XN.X509Name, X.X509Tbs, su, su1 => XE.x5.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}})))), z => xq.tp(r, m, z), x0 => Unit{}, +su1 => +esu => xq.then(XK.X509Spki, X.X509Tbs, k, k1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}))), z => xq.tp(r, m, z), x0 => Unit{}, +k1 => +ek => xq.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, iu, iu1 => XE.x5.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}})), z => xq.tp(r, m, z), x0 => Unit{}, +iu1 => +eiu => xq.then(Maybe<&2, ABi.Asn1Bits>, X.X509Tbs, su2, su21 => XE.x5.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}), z => xq.tp(r, m, z), x0 => Unit{}, +su21 => +esu2 => xq.then(List<&2, XX.X509Ext>, X.X509Tbs, x, x1 => Done{X.X509Tbs{v1, s1, a1, i1, va1, su1, k1, iu1, su21, x1, xp, raw}}, z => xq.tp(r, m, z), x0 => Unit{}, +x1 => +ex => ({==}, (xq.name_raw(ASc.Asn1Match.at(m, 3n), i1, ei), (xq.name_raw(ASc.Asn1Match.at(m, 5n), su1, esu), (xq.spki_raw(r, ASc.Asn1Match.at(m, 6n), k1, ek), (xq.alg_raw(ASc.Asn1Match.at(m, 2n), a1, ea), ex)))))))))))))))

# The certificate's kept octets and its outer algorithm's

def xq.cp(+r: XR.X509Rules, +m: ASc.Asn1Match, z: Result<&2, &2, XE.X509Error, X.X509Cert>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{c}:
      {X.X509Cert.raw(c) == ASc.Asn1Match.raw(m) : B.Octets} & ({XA.X509AlgId.raw(X.X509Cert.sig_alg(c)) == ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 1n)) : B.Octets} & xq.tp(r, ASc.Asn1Match.at(m, 0n), Done{X.X509Cert.tbs(c)}))

def xq.cmk(+r: XR.X509Rules, +m: ASc.Asn1Match, t0: Result<&2, &2, XE.X509Error, X.X509Tbs>, a0: Result<&2, &2, XE.X509Error, XA.X509AlgId>, s0: Result<&2, &2, XE.X509Error, ABi.Asn1Bits>, ht: xq.tp(r, ASc.Asn1Match.at(m, 0n), t0), +ea: {XA.x5.alg.of(ASc.Asn1Match.at(m, 1n)) == a0 : Result<&2, &2, XE.X509Error, XA.X509AlgId>}) -> xq.cp(r, m, X.x5.cert.mk(t0, a0, s0, ASc.Asn1Match.raw(m))):
  match t0 a0 s0:
    case Done{x} Done{+y} Done{z}:
      ({==}, (xq.alg_raw(ASc.Asn1Match.at(m, 1n), y, ea), ht))
    case Fail{e} _ _:
      Unit{}
    case Done{x} Fail{e} _:
      Unit{}
    case Done{x} Done{y} Fail{e}:
      Unit{}

def xq.cert(+r: XR.X509Rules, +m: ASc.Asn1Match) -> xq.cp(r, m, X.x5.cert.of(r, m)):
  xq.cmk(r, m, X.x5.tbs.of(r, ASc.Asn1Match.at(m, 0n)), XA.x5.alg.of(ASc.Asn1Match.at(m, 1n)), XK.x5.bits.of(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 2n)), XE.X509Asn1{AE.Asn1BadBits{}}), xq.tbs(r, ASc.Asn1Match.at(m, 0n)), {==})

# A parse: the certificate's match, and the octets kept are its matches'

def xq.qp(+r: XR.X509Rules, +b: B.Octets, z: Result<&2, &2, XE.X509Error, X.X509Cert>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{c}:
      Sigma<&1, &1, ASc.Asn1Match, m => {ASc.Asn1.match(XR.X509Rules.asn1(r), XS.x5.s.cert(), b) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>} & xq.cp(r, m, Done{c})>

def xq.mval(z: Result<&2, &2, XE.X509Error, ASc.Asn1Match>) -> ASc.Asn1Match:
  match z:
    case Fail{x}:
      ASc.Asn1MAbsent{}
    case Done{v}:
      v

def xq.lift(x: Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>, +m: ASc.Asn1Match, +e: {XE.x5.lift(ASc.Asn1Match, x) == Done{m} : Result<&2, &2, XE.X509Error, ASc.Asn1Match>}) -> {x == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}:
  match x:
    case Fail{y}:
      Empty.absurd({Fail{y} == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, xq.rfd(ASc.Asn1Match, XE.X509Asn1{y}, m, e))
    case Done{+v}:
      +ev = Equal.cong(Result<&2, &2, XE.X509Error, ASc.Asn1Match>, ASc.Asn1Match, z => xq.mval(z), Done{v}, Done{m}, e)
      Equal.cong(ASc.Asn1Match, Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>, z => Done{z}, v, m, ev)

def xq.p1(+r: XR.X509Rules, +b: B.Octets, +m: ASc.Asn1Match, z0: Result<&2, &2, XE.X509Error, X.X509Cert>, +em: {ASc.Asn1.match(XR.X509Rules.asn1(r), XS.x5.s.cert(), b) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, hc: xq.cp(r, m, z0)) -> xq.qp(r, b, z0):
  match z0:
    case Fail{x}:
      Unit{}
    case Done{c}:
      (m, (em, hc))

def xq.p0(+r: XR.X509Rules, +b: B.Octets) -> xq.qp(r, b, X.x5.parse0(r, b)):
  +mr = ASc.Asn1.match(XR.X509Rules.asn1(r), XS.x5.s.cert(), b)
  xq.then(ASc.Asn1Match, X.X509Cert, XE.x5.lift(ASc.Asn1Match, mr), m => X.x5.cert.of(r, m), z => xq.qp(r, b, z), x0 => Unit{}, +m => +em => xq.p1(r, b, m, X.x5.cert.of(r, m), xq.lift(mr, m, em), xq.cert(r, m)))

def xq.cval(z: Result<&2, &2, XE.X509Error, X.X509Cert>, +d: X.X509Cert) -> X.X509Cert:
  match z:
    case Fail{x}:
      d
    case Done{v}:
      v

def xq.fin2(q: Result<&2, &2, XE.X509Error, Unit>, +c0: X.X509Cert, +c: X.X509Cert, +e: {X.x5.fin(q, c0) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}) -> {Done{c0} == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}:
  match q:
    case Fail{x}:
      Empty.absurd({Done{c0} == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}, xq.rfd(X.X509Cert, x, c, e))
    case Done{u}:
      e

def xq.fin(+r: XR.X509Rules, res: Result<&2, &2, XE.X509Error, X.X509Cert>, +c: X.X509Cert, +e: {X.x5.finish(r, res) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}) -> {res == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}:
  match res:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}, xq.rfd(X.X509Cert, x, c, e))
    case Done{+c0}:
      xq.fin2(X.x5.conform(r, c0), c0, c, e)

def xq.qcast(+r: XR.X509Rules, +b: B.Octets, z: Result<&2, &2, XE.X509Error, X.X509Cert>, +c: X.X509Cert, +h: {z == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}, q: xq.qp(r, b, z)) -> xq.qp(r, b, Done{c}):
  %h : xq.qp(r, b, _)
  q

# a certificate parsed from b: the match of b it was read from
def xq.parsed(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, +e: {X.X509.parse(r, b) == Done{c} : Result<&2, &2, XE.X509Error, X.X509Cert>}) -> xq.qp(r, b, Done{c}):
  xq.qcast(r, b, X.x5.parse0(r, b), c, xq.fin(r, X.x5.parse0(r, b), c, e), xq.p0(r, b))

# Steps from the certificate's match

def xq.f1(+m: ASc.Asn1Match, +i: Nat) -> {ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}]) == ASc.Asn1Match.at(m, i) : ASc.Asn1Match}:
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}]), ASc.Asn1Match.follow(ASc.Asn1Match.at(m, i), Nil{}), ASc.Asn1Match.at(m, i), AL.follow_at(m, i, Nil{}), AL.follow_nil(ASc.Asn1Match.at(m, i)))

def xq.f2(+m: ASc.Asn1Match, +i: Nat, +j: Nat) -> {ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}, ASc.Asn1StepAt{j}]) == ASc.Asn1Match.at(ASc.Asn1Match.at(m, i), j) : ASc.Asn1Match}:
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}, ASc.Asn1StepAt{j}]), ASc.Asn1Match.follow(ASc.Asn1Match.at(m, i), [ASc.Asn1StepAt{j}]), ASc.Asn1Match.at(ASc.Asn1Match.at(m, i), j), AL.follow_at(m, i, [ASc.Asn1StepAt{j}]), xq.f1(ASc.Asn1Match.at(m, i), j))

# extension k: the k-th of the extensions field's matches
def xq.fx(+m: ASc.Asn1Match, +k: Nat) -> {ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{9n}, ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}]) == ASc.Asn1Match.at(ASc.Asn1Match.inner(ASc.Asn1Match.at(m, 9n)), k) : ASc.Asn1Match}:
  +m9 = ASc.Asn1Match.at(m, 9n)
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{9n}, ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}]), ASc.Asn1Match.follow(m9, [ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}]), ASc.Asn1Match.at(ASc.Asn1Match.inner(m9), k), AL.follow_at(m, 9n, [ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}]), Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m9, [ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}]), ASc.Asn1Match.follow(ASc.Asn1Match.inner(m9), [ASc.Asn1StepAt{k}]), ASc.Asn1Match.at(ASc.Asn1Match.inner(m9), k), AL.follow_inner(m9, [ASc.Asn1StepAt{k}]), xq.f1(ASc.Asn1Match.inner(m9), k)))

# The laws

def xq.sl(o: B.Octets, c: B.Octets) -> Type:
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {c == B.Octets.append(u, B.Octets.append(o, v)) : B.Octets}>>

def xq.ar(+r: XR.X509Rules) -> AR.Asn1Rules:
  XR.X509Rules.asn1(r)

# law cert_split
def xq.split(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> Sigma<&1, &1, B.Octets, rest => {B.Octets.append(X.X509Cert.raw(c), rest) == b : B.Octets}>:
  (+m, (+em, hc)) = hp
  (hraw, rest) = hc
  %Equal.sym(B.Octets, X.X509Cert.raw(c), ASc.Asn1Match.raw(m), hraw) : Sigma<&1, &1, B.Octets, rest => {B.Octets.append(_, rest) == b : B.Octets}>
  AL.match_split(xq.ar(r), XS.x5.s.cert(), b, m, em)

# law cert_whole
def xq.whole(+r: XR.X509Rules, +ht: {AR.Asn1Rules.trailing(XR.X509Rules.asn1(r)) == False{} : Bool}, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> {X.X509Cert.raw(c) == b : B.Octets}:
  (+m, (+em, hc)) = hp
  (hraw, rest) = hc
  Equal.trans(B.Octets, X.X509Cert.raw(c), ASc.Asn1Match.raw(m), b, hraw, AL.match_whole(xq.ar(r), ht, XS.x5.s.cert(), b, m, em))

# law tbs_slice
def xq.tbs_slice(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(X.X509Cert.tbs_raw(c), b):
  (+m, (+em, hc)) = hp
  (hraw, (hsa, ht)) = hc
  (+htr, hrest) = ht
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(_, b)
  %xq.f1(m, 0n) : xq.sl(ASc.Asn1Match.raw(_), b)
  AL.match_input(xq.ar(r), XS.x5.s.cert(), b, m, [ASc.Asn1StepAt{0n}], em)

# laws tbs_within, sig_alg_within: field i of the certificate in its octets
def xq.in_cert(+r: XR.X509Rules, +b: B.Octets, +m: ASc.Asn1Match, +i: Nat, +em: {ASc.Asn1.match(xq.ar(r), XS.x5.s.cert(), b) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}) -> xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(m, i)), ASc.Asn1Match.raw(m)):
  %xq.f1(m, i) : xq.sl(ASc.Asn1Match.raw(_), ASc.Asn1Match.raw(m))
  %AL.follow_nil(m) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}])), ASc.Asn1Match.raw(_))
  AL.match_within(xq.ar(r), XS.x5.s.cert(), b, m, Nil{}, [ASc.Asn1StepAt{i}], em)

def xq.tbs_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(X.X509Cert.tbs_raw(c), X.X509Cert.raw(c)):
  (+m, (+em, hc)) = hp
  (+hraw, (hsa, ht)) = hc
  (+htr, hrest) = ht
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(_, X.X509Cert.raw(c))
  %Equal.sym(B.Octets, X.X509Cert.raw(c), ASc.Asn1Match.raw(m), hraw) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), _)
  xq.in_cert(r, b, m, 0n, em)

def xq.sig_alg_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(XA.X509AlgId.raw(X.X509Cert.sig_alg(c)), X.X509Cert.raw(c)):
  (+m, (+em, hc)) = hp
  (+hraw, (+hsa, ht)) = hc
  %Equal.sym(B.Octets, XA.X509AlgId.raw(X.X509Cert.sig_alg(c)), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 1n)), hsa) : xq.sl(_, X.X509Cert.raw(c))
  %Equal.sym(B.Octets, X.X509Cert.raw(c), ASc.Asn1Match.raw(m), hraw) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 1n)), _)
  xq.in_cert(r, b, m, 1n, em)

# field j of the tbsCertificate in the tbsCertificate's octets
def xq.in_tbs(+r: XR.X509Rules, +b: B.Octets, +m: ASc.Asn1Match, +j: Nat, +em: {ASc.Asn1.match(xq.ar(r), XS.x5.s.cert(), b) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}) -> xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), j)), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n))):
  %xq.f2(m, 0n, j) : xq.sl(ASc.Asn1Match.raw(_), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)))
  %xq.f1(m, 0n) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{0n}, ASc.Asn1StepAt{j}])), ASc.Asn1Match.raw(_))
  AL.match_within(xq.ar(r), XS.x5.s.cert(), b, m, [ASc.Asn1StepAt{0n}], [ASc.Asn1StepAt{j}], em)

def xq.issuer_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(XN.X509Name.raw(X.X509Cert.issuer(c)), X.X509Cert.tbs_raw(c)):
  (+m, (+em, hc)) = hp
  (hraw, (hsa, ht)) = hc
  (+htr, (+hi, hrest)) = ht
  %Equal.sym(B.Octets, XN.X509Name.raw(X.X509Cert.issuer(c)), ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 3n)), hi) : xq.sl(_, X.X509Cert.tbs_raw(c))
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 3n)), _)
  xq.in_tbs(r, b, m, 3n, em)

def xq.subject_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(XN.X509Name.raw(X.X509Cert.subject(c)), X.X509Cert.tbs_raw(c)):
  (+m, (+em, hc)) = hp
  (hraw, (hsa, ht)) = hc
  (+htr, (hi, (+hs, hrest))) = ht
  %Equal.sym(B.Octets, XN.X509Name.raw(X.X509Cert.subject(c)), ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 5n)), hs) : xq.sl(_, X.X509Cert.tbs_raw(c))
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 5n)), _)
  xq.in_tbs(r, b, m, 5n, em)

def xq.spki_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(XK.X509Spki.raw(X.X509Cert.spki(c)), X.X509Cert.tbs_raw(c)):
  (+m, (+em, hc)) = hp
  (hraw, (hsa, ht)) = hc
  (+htr, (hi, (hs, (+hk, hrest)))) = ht
  %Equal.sym(B.Octets, XK.X509Spki.raw(X.X509Cert.spki(c)), ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 6n)), hk) : xq.sl(_, X.X509Cert.tbs_raw(c))
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 6n)), _)
  xq.in_tbs(r, b, m, 6n, em)

def xq.tbs_alg_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, hp: xq.qp(r, b, Done{c})) -> xq.sl(XA.X509AlgId.raw(X.X509Tbs.signature(X.X509Cert.tbs(c))), X.X509Cert.tbs_raw(c)):
  (+m, (+em, hc)) = hp
  (hraw, (hsa, ht)) = hc
  (+htr, (hi, (hs, (hk, (+ha, hx))))) = ht
  %Equal.sym(B.Octets, XA.X509AlgId.raw(X.X509Tbs.signature(X.X509Cert.tbs(c))), ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 2n)), ha) : xq.sl(_, X.X509Cert.tbs_raw(c))
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 2n)), _)
  xq.in_tbs(r, b, m, 2n, em)

# law ext_within: an extension's octets are the k-th extension match's
def xq.ext_in2(+r: XR.X509Rules, +b: B.Octets, +m: ASc.Asn1Match, +x: XX.X509Ext, +em: {ASc.Asn1.match(xq.ar(r), XS.x5.s.cert(), b) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, sp: xq.split_ty(ASc.Asn1Match.items(ASc.Asn1Match.inner(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 9n))), x)) -> xq.sl(XX.X509Ext.raw(x), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n))):
  (+mpre, (+mx, (+mpost, (+e1, +e2)))) = sp
  +t0 = ASc.Asn1Match.at(m, 0n)
  +k = List.length(&2, ASc.Asn1Match, mpre)
  +hat = AL.at_items(ASc.Asn1Match.inner(ASc.Asn1Match.at(t0, 9n)), mpre, mx, mpost, e1)
  %Equal.sym(B.Octets, XX.X509Ext.raw(x), ASc.Asn1Match.raw(mx), e2) : xq.sl(_, ASc.Asn1Match.raw(t0))
  %hat : xq.sl(ASc.Asn1Match.raw(_), ASc.Asn1Match.raw(t0))
  %xq.fx(t0, k) : xq.sl(ASc.Asn1Match.raw(_), ASc.Asn1Match.raw(t0))
  %AL.follow_at(m, 0n, [ASc.Asn1StepAt{9n}, ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}]) : xq.sl(ASc.Asn1Match.raw(_), ASc.Asn1Match.raw(t0))
  %xq.f1(m, 0n) : xq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{0n}, ASc.Asn1StepAt{9n}, ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}])), ASc.Asn1Match.raw(_))
  AL.match_within(xq.ar(r), XS.x5.s.cert(), b, m, [ASc.Asn1StepAt{0n}], [ASc.Asn1StepAt{9n}, ASc.Asn1StepInner{}, ASc.Asn1StepAt{k}], em)

def xq.ext_within(+r: XR.X509Rules, +b: B.Octets, +c: X.X509Cert, +pre: List<&2, XX.X509Ext>, +x: XX.X509Ext, +post: List<&2, XX.X509Ext>, +h: {X.X509Cert.extensions(c) == List.append(&2, XX.X509Ext, pre, Con{x, post}) : List<&2, XX.X509Ext>}, hp: xq.qp(r, b, Done{c})) -> xq.sl(XX.X509Ext.raw(x), X.X509Cert.tbs_raw(c)):
  (+m, (+em, hc)) = hp
  (hraw, (hsa, ht)) = hc
  (+htr, (hi, (hs, (hk, (ha, hx))))) = ht
  +ms = ASc.Asn1Match.items(ASc.Asn1Match.inner(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 0n), 9n)))
  +es = X.X509Cert.extensions(c)
  he = xq.ecast(ms, es, List.append(&2, XX.X509Ext, pre, Con{x, post}), h, xq.epcast(ms, XX.x5.exts.of(r, ms), es, hx, xq.exts_ok(r, ms)))
  %Equal.sym(B.Octets, X.X509Cert.tbs_raw(c), ASc.Asn1Match.raw(ASc.Asn1Match.at(m, 0n)), htr) : xq.sl(XX.X509Ext.raw(x), _)
  xq.ext_in2(r, b, m, x, em, xq.eall_split(ms, pre, x, post, he))
