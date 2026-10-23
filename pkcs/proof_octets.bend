# Proofs for bend-osdev-pkcs: the octets a parse keeps. Cms.parse matches
# the input against ContentInfo's schema, then the content's octets against
# SignedData's (bend-osdev-asn1 schemas), and reads each field from a
# field's match; the SignedData's octets and each signer's signed
# attributes' octets are the octets of those matches (pq.sd, pq.signer, by
# following each step of the readers' Result chains, pq.then), so asn1's
# match laws make them slices of the input. Under the attrs_der rule the
# parse has matched those octets again under DER, so asn1's match_der,
# match_of_node and encode_retag make Cms.signed_message the DER of a SET
# OF the attributes' elements. The Octets algebra here (equal bytes,
# associativity, slices of slices) is from bytes' interface laws, as
# bytes states none of it yet.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/encode.bend as AEn
import ../asn1/schema.bend as ASc
import ../asn1/LAWS.bend as AL
import ../asn1/PROOF.bend as AP
import ../oid/oid.bend as O
import ../x509/alg.bend as XA
import ./error.bend as PE
import ./rules.bend as PR
import ./schema.bend as PSc
import ./attr.bend as PA
import ./signer.bend as PG
import ./pkcs.bend as P
import ./signed.bend as PS
import ./proof_pkcs.bend as PP

# Octets: equal bytes, joins, slices

def pq.ext(+a: B.Octets, +b: B.Octets, +h: {B.Octets.to_list(a) == B.Octets.to_list(b) : List<&2, U32>}) -> {a == b : B.Octets}:
  %BL.octets_of_to(a) : {_ == b : B.Octets}
  %BL.octets_of_to(b) : {B.Octets.of_list(B.Octets.to_list(a)) == _ : B.Octets}
  Equal.cong(List<&2, U32>, B.Octets, z => B.Octets.of_list(z), B.Octets.to_list(a), B.Octets.to_list(b), h)

def pq.lassoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pq.lassoc(t, ys, zs) : {Con{h, List.append(&2, U32, List.append(&2, U32, t, ys), zs)} == Con{h, _} : List<&2, U32>}
      {==}

def pq.assoc.l(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.to_list(B.Octets.append(B.Octets.append(a, b), c)) == B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c))) : List<&2, U32>}:
  +la = B.Octets.to_list(a)
  +lb = B.Octets.to_list(b)
  +lc = B.Octets.to_list(c)
  +rhs = B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c)))
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.append(a, b), c)), B.append(B.Octets.to_list(B.Octets.append(a, b)), lc), BL.octets_append_list(B.Octets.append(a, b), c)) : {_ == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(la, lb), BL.octets_append_list(a, b)) : {B.append(_, lc) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, rhs, B.append(la, B.Octets.to_list(B.Octets.append(b, c))), BL.octets_append_list(a, B.Octets.append(b, c))) : {B.append(B.append(la, lb), lc) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(b, c)), B.append(lb, lc), BL.octets_append_list(b, c)) : {B.append(B.append(la, lb), lc) == B.append(la, _) : List<&2, U32>}
  pq.lassoc(la, lb, lc)

def pq.assoc(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.append(B.Octets.append(a, b), c) == B.Octets.append(a, B.Octets.append(b, c)) : B.Octets}:
  pq.ext(B.Octets.append(B.Octets.append(a, b), c), B.Octets.append(a, B.Octets.append(b, c)), pq.assoc.l(a, b, c))

def pq.sl(o: B.Octets, c: B.Octets) -> Type:
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {c == B.Octets.append(u, B.Octets.append(o, v)) : B.Octets}>>

def pq.sl_trans.e(+o: B.Octets, +m: B.Octets, +c: B.Octets, +u1: B.Octets, +v1: B.Octets, +u2: B.Octets, +v2: B.Octets, +e1: {m == B.Octets.append(u1, B.Octets.append(o, v1)) : B.Octets}, +e2: {c == B.Octets.append(u2, B.Octets.append(m, v2)) : B.Octets}) -> {c == B.Octets.append(B.Octets.append(u2, u1), B.Octets.append(o, B.Octets.append(v1, v2))) : B.Octets}:
  +y = B.Octets.append(o, v1)
  +x = B.Octets.append(o, B.Octets.append(v1, v2))
  +rhs = B.Octets.append(B.Octets.append(u2, u1), x)
  %Equal.sym(B.Octets, c, B.Octets.append(u2, B.Octets.append(m, v2)), e2) : {_ == rhs : B.Octets}
  %Equal.sym(B.Octets, m, B.Octets.append(u1, y), e1) : {B.Octets.append(u2, B.Octets.append(_, v2)) == rhs : B.Octets}
  %Equal.sym(B.Octets, rhs, B.Octets.append(u2, B.Octets.append(u1, x)), pq.assoc(u2, u1, x)) : {B.Octets.append(u2, B.Octets.append(B.Octets.append(u1, y), v2)) == _ : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(u1, y), v2), B.Octets.append(u1, B.Octets.append(y, v2)), pq.assoc(u1, y, v2)) : {B.Octets.append(u2, _) == B.Octets.append(u2, B.Octets.append(u1, x)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(y, v2), x, pq.assoc(o, v1, v2)) : {B.Octets.append(u2, B.Octets.append(u1, _)) == B.Octets.append(u2, B.Octets.append(u1, x)) : B.Octets}
  {==}

def pq.sl_trans(+o: B.Octets, +m: B.Octets, +c: B.Octets, h1: pq.sl(o, m), h2: pq.sl(m, c)) -> pq.sl(o, c):
  (+u1, (+v1, +e1)) = h1
  (+u2, (+v2, +e2)) = h2
  (B.Octets.append(u2, u1), (B.Octets.append(v1, v2), pq.sl_trans.e(o, m, c, u1, v1, u2, v2, e1, e2)))

# signed attributes retagged: the first octet becomes SET's (RFC 5652 5.4)
def pq.mask_to(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.mask(B.Octets.to_list(o)), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o))), Equal.cong(B.Octets, List<&2, U32>, z => B.Octets.to_list(z), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)))

def pq.retag.l(+l: B.Octets) -> {B.Octets.to_list(PS.Cms.set_tagged(B.Octets.append(B.Octets.of_list([160]), l))) == B.Octets.to_list(B.Octets.append(B.Octets.of_list([49]), l)) : List<&2, U32>}:
  +ll = B.Octets.to_list(l)
  +rhs = B.Octets.to_list(B.Octets.append(B.Octets.of_list([49]), l))
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list([160]), l)), B.append(B.Octets.to_list(B.Octets.of_list([160])), ll), BL.octets_append_list(B.Octets.of_list([160]), l)) : {B.Octets.to_list(B.Octets.of_list(PS.pk.retag.l(_))) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([160])), B.mask([160]), BL.octets_to_of([160])) : {B.Octets.to_list(B.Octets.of_list(PS.pk.retag.l(B.append(_, ll)))) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{49, ll})), B.mask(Con{49, ll}), BL.octets_to_of(Con{49, ll})) : {_ == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, rhs, B.append(B.Octets.to_list(B.Octets.of_list([49])), ll), BL.octets_append_list(B.Octets.of_list([49]), l)) : {B.mask(Con{49, ll}) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([49])), B.mask([49]), BL.octets_to_of([49])) : {B.mask(Con{49, ll}) == B.append(_, ll) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(ll), ll, pq.mask_to(l)) : {Con{B.byte(49), _} == B.append(B.mask([49]), ll) : List<&2, U32>}
  {==}

def pq.retag(+l: B.Octets) -> {PS.Cms.set_tagged(B.Octets.append(B.Octets.of_list([160]), l)) == B.Octets.append(B.Octets.of_list([49]), l) : B.Octets}:
  pq.ext(PS.Cms.set_tagged(B.Octets.append(B.Octets.of_list([160]), l)), B.Octets.append(B.Octets.of_list([49]), l), pq.retag.l(l))

# A step of a Result chain: whatever follows a value read holds of the chain

def pq.then(-A: Data, -C: Data, a: Result<&2, &2, PE.PkcsError, A>, k: A -> Result<&2, &2, PE.PkcsError, C>, -Q: Result<&2, &2, PE.PkcsError, C> -> Type, hf: @x: PE.PkcsError -> Q(Fail{x}), hk: @v: A -> @ev: {a == Done{v} : Result<&2, &2, PE.PkcsError, A>} -> Q(k(v))) -> Q(PE.pk.then(A, C, a, k)):
  match a:
    case Fail{x}:
      hf(x)
    case Done{+v}:
      hk(v, {==})

def pq.rdisc(-A: Data, z: Result<&2, &2, PE.PkcsError, A>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pq.rfd(-A: Data, -x: PE.PkcsError, -y: A, e: {Fail{x} == Done{y} : Result<&2, &2, PE.PkcsError, A>}) -> Empty:
  %e : pq.rdisc(A, _)
  Unit{}

def pq.aval(z: Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>) -> Maybe<&2, PG.CmsAttrs>:
  match z:
    case Fail{x}:
      None{}
    case Done{v}:
      v

# Signed attributes: their octets, a field's match's

def pq.ap(m3: ASc.Asn1Match, ma: Maybe<&2, PG.CmsAttrs>) -> Type:
  match ma:
    case None{}:
      Unit
    case Some{a}:
      {PG.CmsAttrs.raw(a) == ASc.Asn1Match.raw(m3) : B.Octets}

def pq.sa3(z: Result<&2, &2, PE.PkcsError, List<&2, PA.CmsAttr>>, +m3: ASc.Asn1Match, +a1: Maybe<&2, PG.CmsAttrs>, +ea: {Result.map(&2, &2, PE.PkcsError, List<&2, PA.CmsAttr>, Maybe<&2, PG.CmsAttrs>, xs => Some{PG.CmsAttrs{xs, ASc.Asn1Match.raw(m3)}}, z) == Done{a1} : Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>}) -> pq.ap(m3, a1):
  match z:
    case Fail{x}:
      Empty.absurd(pq.ap(m3, a1), pq.rfd(Maybe<&2, PG.CmsAttrs>, x, a1, ea))
    case Done{+xs}:
      +e2 = Equal.cong(Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>, Maybe<&2, PG.CmsAttrs>, q => pq.aval(q), Done{Some{PG.CmsAttrs{xs, ASc.Asn1Match.raw(m3)}}}, Done{a1}, ea)
      %e2 : pq.ap(m3, _)
      {==}

def pq.sa2(p: Bool, +m3: ASc.Asn1Match, +a1: Maybe<&2, PG.CmsAttrs>, +ea: {Bool.pick(Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>, p, Result.map(&2, &2, PE.PkcsError, List<&2, PA.CmsAttr>, Maybe<&2, PG.CmsAttrs>, xs => Some{PG.CmsAttrs{xs, ASc.Asn1Match.raw(m3)}}, PA.pk.attrs.of(ASc.Asn1Match.items(m3))), Done{None{}}) == Done{a1} : Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>}) -> pq.ap(m3, a1):
  match p:
    case True{}:
      pq.sa3(PA.pk.attrs.of(ASc.Asn1Match.items(m3)), m3, a1, ea)
    case False{}:
      +e2 = Equal.cong(Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>, Maybe<&2, PG.CmsAttrs>, q => pq.aval(q), Done{None{}}, Done{a1}, ea)
      %e2 : pq.ap(m3, _)
      Unit{}

def pq.sa(+m3: ASc.Asn1Match, +a1: Maybe<&2, PG.CmsAttrs>, +ea: {PG.pk.signed.of(m3) == Done{a1} : Result<&2, &2, PE.PkcsError, Maybe<&2, PG.CmsAttrs>>}) -> pq.ap(m3, a1):
  pq.sa2(ASc.Asn1Match.present(m3), m3, a1, ea)

def pq.gp(m: ASc.Asn1Match, z: Result<&2, &2, PE.PkcsError, PG.CmsSigner>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{g}:
      pq.ap(ASc.Asn1Match.at(m, 3n), PG.CmsSigner.signed_attrs(g))

# a signer read from a SignerInfo's match m: its signed attributes' octets
# are those of m's field 3 (generated from the expression in pk.signer.of)
def pq.signer(+r: PR.PkcsRules, +m: ASc.Asn1Match) -> pq.gp(m, PG.pk.signer.of(r, m)):
  +v = PG.pk.nat(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), PE.PkcsBadVersion{})
  +i = PG.pk.sid.of(ASc.Asn1Match.at(m, 1n))
  +d = PE.pk.x509(XA.X509AlgId, XA.X509AlgId.of_match(ASc.Asn1Match.at(m, 2n)))
  +a = PG.pk.signed.of(ASc.Asn1Match.at(m, 3n))
  +g = PE.pk.x509(XA.X509AlgId, XA.X509AlgId.of_match(ASc.Asn1Match.at(m, 4n)))
  +x = PG.pk.octets(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 5n)), PE.PkcsBadSigner{})
  +u = PA.pk.attrs.of(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 6n)))
  pq.then(Nat, PG.CmsSigner, v, v1 => PE.pk.then(PG.CmsSid, PG.CmsSigner, i, i1 => PE.pk.then(XA.X509AlgId, PG.CmsSigner, d, d1 => PE.pk.then(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner, a, a1 => PE.pk.then(XA.X509AlgId, PG.CmsSigner, g, g1 => PE.pk.then(B.Octets, PG.CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}})))))), z => pq.gp(m, z), x0 => Unit{}, +v1 => +ev => pq.then(PG.CmsSid, PG.CmsSigner, i, i1 => PE.pk.then(XA.X509AlgId, PG.CmsSigner, d, d1 => PE.pk.then(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner, a, a1 => PE.pk.then(XA.X509AlgId, PG.CmsSigner, g, g1 => PE.pk.then(B.Octets, PG.CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}}))))), z => pq.gp(m, z), x0 => Unit{}, +i1 => +ei => pq.then(XA.X509AlgId, PG.CmsSigner, d, d1 => PE.pk.then(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner, a, a1 => PE.pk.then(XA.X509AlgId, PG.CmsSigner, g, g1 => PE.pk.then(B.Octets, PG.CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}})))), z => pq.gp(m, z), x0 => Unit{}, +d1 => +ed => pq.then(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner, a, a1 => PE.pk.then(XA.X509AlgId, PG.CmsSigner, g, g1 => PE.pk.then(B.Octets, PG.CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}}))), z => pq.gp(m, z), x0 => Unit{}, +a1 => +ea => pq.then(XA.X509AlgId, PG.CmsSigner, g, g1 => PE.pk.then(B.Octets, PG.CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}})), z => pq.gp(m, z), x0 => Unit{}, +g1 => +eg => pq.then(B.Octets, PG.CmsSigner, x, x1 => PE.pk.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}}), z => pq.gp(m, z), x0 => Unit{}, +x1 => +ex => pq.then(List<&2, PA.CmsAttr>, PG.CmsSigner, u, u1 => Done{PG.CmsSigner{v1, i1, d1, a1, g1, x1, u1}}, z => pq.gp(m, z), x0 => Unit{}, +u1 => +eu => pq.sa(ASc.Asn1Match.at(m, 3n), a1, ea))))))))

# Signers: each one's signed attributes, its match's field 3, in order

def pq.gall(ms: List<&2, ASc.Asn1Match>, gs: List<&2, PG.CmsSigner>) -> Type:
  match ms gs:
    case Nil{} Nil{}:
      Unit
    case Con{m, t} Con{g, u}:
      pq.ap(ASc.Asn1Match.at(m, 3n), PG.CmsSigner.signed_attrs(g)) & pq.gall(t, u)
    case Nil{} Con{g, u}:
      Empty
    case Con{m, t} Nil{}:
      Empty

def pq.gl(ms: List<&2, ASc.Asn1Match>, z: Result<&2, &2, PE.PkcsError, List<&2, PG.CmsSigner>>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{gs}:
      pq.gall(ms, gs)

def pq.gcons(+m0: ASc.Asn1Match, +t: List<&2, ASc.Asn1Match>, a: Result<&2, &2, PE.PkcsError, PG.CmsSigner>, b: Result<&2, &2, PE.PkcsError, List<&2, PG.CmsSigner>>, ha: pq.gp(m0, a), hb: pq.gl(t, b)) -> pq.gl(Con{m0, t}, PE.pk.cons(PG.CmsSigner, a, b)):
  match a b:
    case Fail{y} _:
      Unit{}
    case Done{x} Fail{y}:
      Unit{}
    case Done{x} Done{gs}:
      (ha, hb)

def pq.signers_ok(+r: PR.PkcsRules, ms: List<&2, ASc.Asn1Match>) -> pq.gl(ms, PG.pk.signers.of(r, ms)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{+m0, +t}:
      pq.gcons(m0, t, PG.pk.signer.of(r, m0), PG.pk.signers.of(r, t), pq.signer(r, m0), pq.signers_ok(r, t))

def pq.split_ty(ms: List<&2, ASc.Asn1Match>, +g: PG.CmsSigner) -> Type:
  Sigma<&1, &1, List<&2, ASc.Asn1Match>, mpre => Sigma<&1, &1, ASc.Asn1Match, mg => Sigma<&1, &1, List<&2, ASc.Asn1Match>, mpost => {ms == List.append(&2, ASc.Asn1Match, mpre, Con{mg, mpost}) : List<&2, ASc.Asn1Match>} & pq.ap(ASc.Asn1Match.at(mg, 3n), PG.CmsSigner.signed_attrs(g))>>>

def pq.gs_step(+m0: ASc.Asn1Match, +t: List<&2, ASc.Asn1Match>, +g: PG.CmsSigner, ih: pq.split_ty(t, g)) -> pq.split_ty(Con{m0, t}, g):
  (+mpre, (+mg, (+mpost, (+e1, e2)))) = ih
  (Con{m0, mpre}, (mg, (mpost, (Equal.cong(List<&2, ASc.Asn1Match>, List<&2, ASc.Asn1Match>, z => Con{m0, z}, t, List.append(&2, ASc.Asn1Match, mpre, Con{mg, mpost}), e1), e2))))

def pq.gall_split(ms: List<&2, ASc.Asn1Match>, pre: List<&2, PG.CmsSigner>, +g: PG.CmsSigner, +post: List<&2, PG.CmsSigner>, h: pq.gall(ms, List.append(&2, PG.CmsSigner, pre, Con{g, post}))) -> pq.split_ty(ms, g):
  match ms pre:
    case Nil{} Nil{}:
      Empty.absurd(pq.split_ty(Nil{}, g), h)
    case Nil{} Con{p, u}:
      Empty.absurd(pq.split_ty(Nil{}, g), h)
    case Con{+m0, +t} Nil{}:
      (hg, ht) = h
      (Nil{}, (m0, (t, ({==}, hg))))
    case Con{+m0, +t} Con{p, +u}:
      (hp, ht) = h
      pq.gs_step(m0, t, g, pq.gall_split(t, u, g, post, ht))

def pq.gcast(+ms: List<&2, ASc.Asn1Match>, +gs: List<&2, PG.CmsSigner>, +gs2: List<&2, PG.CmsSigner>, +h: {gs == gs2 : List<&2, PG.CmsSigner>}, hg: pq.gall(ms, gs)) -> pq.gall(ms, gs2):
  %h : pq.gall(ms, _)
  hg

def pq.glcast(+ms: List<&2, ASc.Asn1Match>, z: Result<&2, &2, PE.PkcsError, List<&2, PG.CmsSigner>>, +gs: List<&2, PG.CmsSigner>, +h: {z == Done{gs} : Result<&2, &2, PE.PkcsError, List<&2, PG.CmsSigner>>}, hz: pq.gl(ms, z)) -> pq.gall(ms, gs):
  %h : pq.gl(ms, _)
  hz

def pq.apcast(+m3: ASc.Asn1Match, +ma: Maybe<&2, PG.CmsAttrs>, +a: PG.CmsAttrs, +h: {ma == Some{a} : Maybe<&2, PG.CmsAttrs>}, hp: pq.ap(m3, ma)) -> {PG.CmsAttrs.raw(a) == ASc.Asn1Match.raw(m3) : B.Octets}:
  %h : pq.ap(m3, _)
  hp

# The SignedData's kept octets, and its signers' match

def pq.sp(+r: PR.PkcsRules, +m: ASc.Asn1Match, z: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{s}:
      {P.CmsSignedData.raw(s) == ASc.Asn1Match.raw(m) : B.Octets} & ({PG.pk.signers.of(r, ASc.Asn1Match.items(ASc.Asn1Match.at(m, 5n))) == Done{P.CmsSignedData.signers(s)} : Result<&2, &2, PE.PkcsError, List<&2, PG.CmsSigner>>} & {P.CmsSignedData.certificates(s) == P.pk.raws(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 3n))) : List<&2, B.Octets>})


# a SignedData read from its match m: its octets are m's, its signers read
# from m's field 5, its certificates the octets of m's field 3's elements
# (generated from the expression in pk.sd.of)
def pq.sd(+r: PR.PkcsRules, +m: ASc.Asn1Match) -> pq.sp(r, m, P.pk.sd.of(r, m)):
  +v = PG.pk.nat(ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n)), PE.PkcsBadVersion{})
  +d = P.pk.algs(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 1n)))
  +em = ASc.Asn1Match.at(m, 2n)
  +t = P.pk.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(em, 0n)), PE.PkcsBadContent{})
  +c = P.pk.econtent(r, ASc.Asn1Match.node(ASc.Asn1Match.inner(ASc.Asn1Match.at(em, 1n))))
  +x = P.pk.raws(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 3n)))
  +l = P.pk.raws(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 4n)))
  +g = PG.pk.signers.of(r, ASc.Asn1Match.items(ASc.Asn1Match.at(m, 5n)))
  +raw = ASc.Asn1Match.raw(m)
  pq.then(Nat, P.CmsSignedData, v, v1 => PE.pk.then(List<&2, XA.X509AlgId>, P.CmsSignedData, d, d1 => PE.pk.then(O.Oid, P.CmsSignedData, t, t1 => PE.pk.then(Maybe<&2, B.Octets>, P.CmsSignedData, c, c1 => PE.pk.then(List<&2, PG.CmsSigner>, P.CmsSignedData, g, g1 => Done{P.CmsSignedData{v1, d1, t1, c1, x, l, g1, raw}})))), z => pq.sp(r, m, z), x0 => Unit{}, +v1 => +ev => pq.then(List<&2, XA.X509AlgId>, P.CmsSignedData, d, d1 => PE.pk.then(O.Oid, P.CmsSignedData, t, t1 => PE.pk.then(Maybe<&2, B.Octets>, P.CmsSignedData, c, c1 => PE.pk.then(List<&2, PG.CmsSigner>, P.CmsSignedData, g, g1 => Done{P.CmsSignedData{v1, d1, t1, c1, x, l, g1, raw}}))), z => pq.sp(r, m, z), x0 => Unit{}, +d1 => +ed => pq.then(O.Oid, P.CmsSignedData, t, t1 => PE.pk.then(Maybe<&2, B.Octets>, P.CmsSignedData, c, c1 => PE.pk.then(List<&2, PG.CmsSigner>, P.CmsSignedData, g, g1 => Done{P.CmsSignedData{v1, d1, t1, c1, x, l, g1, raw}})), z => pq.sp(r, m, z), x0 => Unit{}, +t1 => +et => pq.then(Maybe<&2, B.Octets>, P.CmsSignedData, c, c1 => PE.pk.then(List<&2, PG.CmsSigner>, P.CmsSignedData, g, g1 => Done{P.CmsSignedData{v1, d1, t1, c1, x, l, g1, raw}}), z => pq.sp(r, m, z), x0 => Unit{}, +c1 => +ec => pq.then(List<&2, PG.CmsSigner>, P.CmsSignedData, g, g1 => Done{P.CmsSignedData{v1, d1, t1, c1, x, l, g1, raw}}, z => pq.sp(r, m, z), x0 => Unit{}, +g1 => +eg => ({==}, (eg, {==})))))))

# ContentInfo: its content's octets matched as a SignedData

def pq.sdr(+r: PR.PkcsRules, +ci: ASc.Asn1Match) -> B.Octets:
  ASc.Asn1Match.raw(ASc.Asn1Match.inner(ASc.Asn1Match.at(ci, 1n)))

def pq.qci(+r: PR.PkcsRules, +ci: ASc.Asn1Match, z: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{s}:
      Sigma<&1, &1, ASc.Asn1Match, m => {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), pq.sdr(r, ci)) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>} & pq.sp(r, m, Done{s})>

def pq.mval(z: Result<&2, &2, PE.PkcsError, ASc.Asn1Match>) -> ASc.Asn1Match:
  match z:
    case Fail{x}:
      ASc.Asn1MAbsent{}
    case Done{v}:
      v

def pq.lift(x: Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>, +m: ASc.Asn1Match, +e: {PE.pk.lift(ASc.Asn1Match, x) == Done{m} : Result<&2, &2, PE.PkcsError, ASc.Asn1Match>}) -> {x == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}:
  match x:
    case Fail{y}:
      Empty.absurd({Fail{y} == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, pq.rfd(ASc.Asn1Match, PE.PkcsAsn1{y}, m, e))
    case Done{+v}:
      +ev = Equal.cong(Result<&2, &2, PE.PkcsError, ASc.Asn1Match>, ASc.Asn1Match, z => pq.mval(z), Done{v}, Done{m}, e)
      Equal.cong(ASc.Asn1Match, Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>, z => Done{z}, v, m, ev)

def pq.qci1(+r: PR.PkcsRules, +ci: ASc.Asn1Match, +m: ASc.Asn1Match, z0: Result<&2, &2, PE.PkcsError, P.CmsSignedData>, +em: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), pq.sdr(r, ci)) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, h: pq.sp(r, m, z0)) -> pq.qci(r, ci, z0):
  match z0:
    case Fail{x}:
      Unit{}
    case Done{s}:
      (m, (em, h))

def pq.inner(+r: PR.PkcsRules, ok: Bool, +ci: ASc.Asn1Match) -> pq.qci(r, ci, P.pk.sd.inner(r, ok, ci)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      +mr = ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), ASc.Asn1Match.raw(ASc.Asn1Match.inner(ASc.Asn1Match.at(ci, 1n))))
      pq.then(ASc.Asn1Match, P.CmsSignedData, PE.pk.lift(ASc.Asn1Match, mr), m => P.pk.sd.of(r, m), z => pq.qci(r, ci, z), x0 => Unit{}, +m => +em => pq.qci1(r, ci, m, P.pk.sd.of(r, m), pq.lift(mr, m, em), pq.sd(r, m)))

def pq.ci(+r: PR.PkcsRules, +ci: ASc.Asn1Match) -> pq.qci(r, ci, P.pk.ci.of(r, ci)):
  pq.then(O.Oid, P.CmsSignedData, P.pk.oid(ASc.Asn1Match.node(ASc.Asn1Match.at(ci, 0n)), PE.PkcsNotSignedData{}), +t => P.pk.sd.inner(r, O.Oid.is_eq(t, P.Cms.id_signed_data()), ci), z => pq.qci(r, ci, z), x0 => Unit{}, +t => +et => pq.inner(r, O.Oid.is_eq(t, P.Cms.id_signed_data()), ci))

# A parse: the ContentInfo's match, and in it the SignedData's

def pq.qp(+r: PR.PkcsRules, +b: B.Octets, z: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{s}:
      Sigma<&1, &1, ASc.Asn1Match, ci => {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b) == Done{ci} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>} & pq.qci(r, ci, Done{s})>

def pq.p1(+r: PR.PkcsRules, +b: B.Octets, +ci: ASc.Asn1Match, z0: Result<&2, &2, PE.PkcsError, P.CmsSignedData>, +eci: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b) == Done{ci} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, h: pq.qci(r, ci, z0)) -> pq.qp(r, b, z0):
  match z0:
    case Fail{x}:
      Unit{}
    case Done{s}:
      (ci, (eci, h))

def pq.p0(+r: PR.PkcsRules, +b: B.Octets) -> pq.qp(r, b, P.pk.parse0(r, b)):
  +mr = ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b)
  pq.then(ASc.Asn1Match, P.CmsSignedData, PE.pk.lift(ASc.Asn1Match, mr), m => P.pk.ci.of(r, m), z => pq.qp(r, b, z), x0 => Unit{}, +ci => +eci => pq.p1(r, b, ci, P.pk.ci.of(r, ci), pq.lift(mr, ci, eci), pq.ci(r, ci)))

def pq.fin2(q: Result<&2, &2, PE.PkcsError, Unit>, +s0: P.CmsSignedData, +s: P.CmsSignedData, +e: {P.pk.fin(q, s0) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}) -> {Done{s0} == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}:
  match q:
    case Fail{x}:
      Empty.absurd({Done{s0} == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}, pq.rfd(P.CmsSignedData, x, s, e))
    case Done{u}:
      e

def pq.fin(+r: PR.PkcsRules, res: Result<&2, &2, PE.PkcsError, P.CmsSignedData>, +s: P.CmsSignedData, +e: {P.pk.finish(r, res) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}) -> {res == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}:
  match res:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}, pq.rfd(P.CmsSignedData, x, s, e))
    case Done{+s0}:
      pq.fin2(P.pk.conform(r, s0), s0, s, e)

def pq.qcast(+r: PR.PkcsRules, +b: B.Octets, z: Result<&2, &2, PE.PkcsError, P.CmsSignedData>, +s: P.CmsSignedData, +h: {z == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}, q: pq.qp(r, b, z)) -> pq.qp(r, b, Done{s}):
  %h : pq.qp(r, b, _)
  q

# a SignedData parsed from b: the matches it was read from
def pq.parsed(+r: PR.PkcsRules, +b: B.Octets, +s: P.CmsSignedData, +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}) -> pq.qp(r, b, Done{s}):
  pq.qcast(r, b, P.pk.parse0(r, b), s, pq.fin(r, P.pk.parse0(r, b), s, e), pq.p0(r, b))

# Steps

def pq.f1(+m: ASc.Asn1Match, +i: Nat) -> {ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}]) == ASc.Asn1Match.at(m, i) : ASc.Asn1Match}:
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{i}]), ASc.Asn1Match.follow(ASc.Asn1Match.at(m, i), Nil{}), ASc.Asn1Match.at(m, i), AL.follow_at(m, i, Nil{}), AL.follow_nil(ASc.Asn1Match.at(m, i)))

# the content: field 1 of the ContentInfo, inside its EXPLICIT tag
def pq.fc(+ci: ASc.Asn1Match) -> {ASc.Asn1Match.follow(ci, [ASc.Asn1StepAt{1n}, ASc.Asn1StepInner{}]) == ASc.Asn1Match.inner(ASc.Asn1Match.at(ci, 1n)) : ASc.Asn1Match}:
  +c1 = ASc.Asn1Match.at(ci, 1n)
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(ci, [ASc.Asn1StepAt{1n}, ASc.Asn1StepInner{}]), ASc.Asn1Match.follow(c1, [ASc.Asn1StepInner{}]), ASc.Asn1Match.inner(c1), AL.follow_at(ci, 1n, [ASc.Asn1StepInner{}]), Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(c1, [ASc.Asn1StepInner{}]), ASc.Asn1Match.follow(ASc.Asn1Match.inner(c1), Nil{}), ASc.Asn1Match.inner(c1), AL.follow_inner(c1, Nil{}), AL.follow_nil(ASc.Asn1Match.inner(c1))))

# signer k's signed attributes: field 3 of element k of field 5
def pq.fs(+m: ASc.Asn1Match, +k: Nat) -> {ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{5n}, ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}]) == ASc.Asn1Match.at(ASc.Asn1Match.at(ASc.Asn1Match.at(m, 5n), k), 3n) : ASc.Asn1Match}:
  +m5 = ASc.Asn1Match.at(m, 5n)
  +mk = ASc.Asn1Match.at(m5, k)
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{5n}, ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}]), ASc.Asn1Match.follow(m5, [ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}]), ASc.Asn1Match.at(mk, 3n), AL.follow_at(m, 5n, [ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}]), Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m5, [ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}]), ASc.Asn1Match.follow(mk, [ASc.Asn1StepAt{3n}]), ASc.Asn1Match.at(mk, 3n), AL.follow_at(m5, k, [ASc.Asn1StepAt{3n}]), pq.f1(mk, 3n)))

# The content's octets are a slice of the input
def pq.sd_in(+r: PR.PkcsRules, +b: B.Octets, +ci: ASc.Asn1Match, +eci: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b) == Done{ci} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}) -> pq.sl(pq.sdr(r, ci), b):
  %pq.fc(ci) : pq.sl(ASc.Asn1Match.raw(_), b)
  AL.match_input(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b, ci, [ASc.Asn1StepAt{1n}, ASc.Asn1StepInner{}], eci)

# law signed_data_slice
def pq.sd_slice(+r: PR.PkcsRules, +b: B.Octets, +s: P.CmsSignedData, hp: pq.qp(r, b, Done{s})) -> pq.sl(P.CmsSignedData.raw(s), b):
  (+ci, (+eci, hq)) = hp
  (+m, (+em, hs)) = hq
  (+hraw, hrest) = hs
  +c = pq.sdr(r, ci)
  %Equal.sym(B.Octets, P.CmsSignedData.raw(s), ASc.Asn1Match.raw(m), hraw) : pq.sl(_, b)
  %AL.follow_nil(m) : pq.sl(ASc.Asn1Match.raw(_), b)
  pq.sl_trans(ASc.Asn1Match.raw(ASc.Asn1Match.follow(m, Nil{})), c, b, AL.match_input(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), c, m, Nil{}, em), pq.sd_in(r, b, ci, eci))

# law signed_attrs_slice
def pq.sa_in(+r: PR.PkcsRules, +b: B.Octets, +ci: ASc.Asn1Match, +eci: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b) == Done{ci} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, +m: ASc.Asn1Match, +em: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), pq.sdr(r, ci)) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, +a: PG.CmsAttrs, +g: PG.CmsSigner, +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}, sp: pq.split_ty(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 5n)), g)) -> pq.sl(PG.CmsAttrs.raw(a), b):
  (+mpre, (+mg, (+mpost, (+e1, e2)))) = sp
  +k = List.length(&2, ASc.Asn1Match, mpre)
  +c = pq.sdr(r, ci)
  +hat = AL.at_items(ASc.Asn1Match.at(m, 5n), mpre, mg, mpost, e1)
  +hr = pq.apcast(ASc.Asn1Match.at(mg, 3n), PG.CmsSigner.signed_attrs(g), a, ha, e2)
  %Equal.sym(B.Octets, PG.CmsAttrs.raw(a), ASc.Asn1Match.raw(ASc.Asn1Match.at(mg, 3n)), hr) : pq.sl(_, b)
  %hat : pq.sl(ASc.Asn1Match.raw(ASc.Asn1Match.at(_, 3n)), b)
  %pq.fs(m, k) : pq.sl(ASc.Asn1Match.raw(_), b)
  pq.sl_trans(ASc.Asn1Match.raw(ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{5n}, ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}])), c, b, AL.match_input(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), c, m, [ASc.Asn1StepAt{5n}, ASc.Asn1StepAt{k}, ASc.Asn1StepAt{3n}], em), pq.sd_in(r, b, ci, eci))

def pq.sa_slice(+r: PR.PkcsRules, +b: B.Octets, +s: P.CmsSignedData, +pre: List<&2, PG.CmsSigner>, +g: PG.CmsSigner, +post: List<&2, PG.CmsSigner>, +a: PG.CmsAttrs, +hg: {P.CmsSignedData.signers(s) == List.append(&2, PG.CmsSigner, pre, Con{g, post}) : List<&2, PG.CmsSigner>}, +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}, hp: pq.qp(r, b, Done{s})) -> pq.sl(PG.CmsAttrs.raw(a), b):
  (+ci, (+eci, hq)) = hp
  (+m, (+em, hs)) = hq
  (hraw, (+hsig, hcert)) = hs
  +ms = ASc.Asn1Match.items(ASc.Asn1Match.at(m, 5n))
  +gs = P.CmsSignedData.signers(s)
  pq.sa_in(r, b, ci, eci, m, em, a, g, ha, pq.gall_split(ms, pre, g, post, pq.gcast(ms, gs, List.append(&2, PG.CmsSigner, pre, Con{g, post}), hg, pq.glcast(ms, PG.pk.signers.of(r, ms), gs, hsig, pq.signers_ok(r, ms)))))

# Certificates: each one's octets, the octets of an element of field 3

def pq.odisc(l: List<&2, B.Octets>) -> Type:
  match l:
    case Nil{}:
      Unit
    case Con{x, t}:
      Empty

def pq.ofd(-x: B.Octets, -t: List<&2, B.Octets>, e: {Nil{} == Con{x, t} : List<&2, B.Octets>}) -> Empty:
  %e : pq.odisc(_)
  Unit{}

def pq.ohead(l: List<&2, B.Octets>) -> B.Octets:
  match l:
    case Nil{}:
      B.Octets.empty()
    case Con{x, t}:
      x

def pq.otail(l: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def pq.csplit_ty(ms: List<&2, ASc.Asn1Match>, +o: B.Octets) -> Type:
  Sigma<&1, &1, List<&2, ASc.Asn1Match>, mpre => Sigma<&1, &1, ASc.Asn1Match, mo => Sigma<&1, &1, List<&2, ASc.Asn1Match>, mpost => {ms == List.append(&2, ASc.Asn1Match, mpre, Con{mo, mpost}) : List<&2, ASc.Asn1Match>} & {o == ASc.Asn1Match.raw(mo) : B.Octets}>>>

def pq.cs_step(+m0: ASc.Asn1Match, +t: List<&2, ASc.Asn1Match>, +o: B.Octets, ih: pq.csplit_ty(t, o)) -> pq.csplit_ty(Con{m0, t}, o):
  (+mpre, (+mo, (+mpost, (+e1, +e2)))) = ih
  (Con{m0, mpre}, (mo, (mpost, (Equal.cong(List<&2, ASc.Asn1Match>, List<&2, ASc.Asn1Match>, z => Con{m0, z}, t, List.append(&2, ASc.Asn1Match, mpre, Con{mo, mpost}), e1), e2))))

def pq.raws_split(ms: List<&2, ASc.Asn1Match>, pre: List<&2, B.Octets>, +o: B.Octets, +post: List<&2, B.Octets>, +h: {P.pk.raws(ms) == List.append(&2, B.Octets, pre, Con{o, post}) : List<&2, B.Octets>}) -> pq.csplit_ty(ms, o):
  match ms pre:
    case Nil{} Nil{}:
      Empty.absurd(pq.csplit_ty(Nil{}, o), pq.ofd(o, post, h))
    case Nil{} Con{+p, +u}:
      Empty.absurd(pq.csplit_ty(Nil{}, o), pq.ofd(p, List.append(&2, B.Octets, u, Con{o, post}), h))
    case Con{+m0, +t} Nil{}:
      +eh = Equal.cong(List<&2, B.Octets>, B.Octets, z => pq.ohead(z), Con{ASc.Asn1Match.raw(m0), P.pk.raws(t)}, Con{o, post}, h)
      (Nil{}, (m0, (t, ({==}, Equal.sym(B.Octets, ASc.Asn1Match.raw(m0), o, eh)))))
    case Con{+m0, +t} Con{+p, +u}:
      +et = Equal.cong(List<&2, B.Octets>, List<&2, B.Octets>, z => pq.otail(z), Con{ASc.Asn1Match.raw(m0), P.pk.raws(t)}, Con{p, List.append(&2, B.Octets, u, Con{o, post})}, h)
      pq.cs_step(m0, t, o, pq.raws_split(t, u, o, post, et))

# element k of field 3: a certificate
def pq.fcert(+m: ASc.Asn1Match, +k: Nat) -> {ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{3n}, ASc.Asn1StepAt{k}]) == ASc.Asn1Match.at(ASc.Asn1Match.at(m, 3n), k) : ASc.Asn1Match}:
  Equal.trans(ASc.Asn1Match, ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{3n}, ASc.Asn1StepAt{k}]), ASc.Asn1Match.follow(ASc.Asn1Match.at(m, 3n), [ASc.Asn1StepAt{k}]), ASc.Asn1Match.at(ASc.Asn1Match.at(m, 3n), k), AL.follow_at(m, 3n, [ASc.Asn1StepAt{k}]), pq.f1(ASc.Asn1Match.at(m, 3n), k))

def pq.cert_in(+r: PR.PkcsRules, +b: B.Octets, +ci: ASc.Asn1Match, +eci: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.content_info(), b) == Done{ci} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, +m: ASc.Asn1Match, +em: {ASc.Asn1.match(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), pq.sdr(r, ci)) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}, +o: B.Octets, sp: pq.csplit_ty(ASc.Asn1Match.items(ASc.Asn1Match.at(m, 3n)), o)) -> pq.sl(o, b):
  (+mpre, (+mo, (+mpost, (+e1, +e2)))) = sp
  +k = List.length(&2, ASc.Asn1Match, mpre)
  +c = pq.sdr(r, ci)
  +hat = AL.at_items(ASc.Asn1Match.at(m, 3n), mpre, mo, mpost, e1)
  %Equal.sym(B.Octets, o, ASc.Asn1Match.raw(mo), e2) : pq.sl(_, b)
  %hat : pq.sl(ASc.Asn1Match.raw(_), b)
  %pq.fcert(m, k) : pq.sl(ASc.Asn1Match.raw(_), b)
  pq.sl_trans(ASc.Asn1Match.raw(ASc.Asn1Match.follow(m, [ASc.Asn1StepAt{3n}, ASc.Asn1StepAt{k}])), c, b, AL.match_input(PR.PkcsRules.asn1(r), PSc.pk.s.signed_data(), c, m, [ASc.Asn1StepAt{3n}, ASc.Asn1StepAt{k}], em), pq.sd_in(r, b, ci, eci))

# law certificate_slice
def pq.cert_slice(+r: PR.PkcsRules, +b: B.Octets, +s: P.CmsSignedData, +pre: List<&2, B.Octets>, +o: B.Octets, +post: List<&2, B.Octets>, +hc: {P.CmsSignedData.certificates(s) == List.append(&2, B.Octets, pre, Con{o, post}) : List<&2, B.Octets>}, hp: pq.qp(r, b, Done{s})) -> pq.sl(o, b):
  (+ci, (+eci, hq)) = hp
  (+m, (+em, hs)) = hq
  (hraw, (hsig, hcert)) = hs
  +ms = ASc.Asn1Match.items(ASc.Asn1Match.at(m, 3n))
  pq.cert_in(r, b, ci, eci, m, em, o, pq.raws_split(ms, pre, o, post, Equal.trans(List<&2, B.Octets>, P.pk.raws(ms), P.CmsSignedData.certificates(s), List.append(&2, B.Octets, pre, Con{o, post}), Equal.sym(List<&2, B.Octets>, P.CmsSignedData.certificates(s), P.pk.raws(ms), hcert), hc)))

# Under attrs_der: the checks the parse passed

def pq.bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def pq.bft(+e: {False{} == True{} : Bool}) -> Empty:
  %e : pq.bdisc(_)
  Unit{}

def pq.first_hd(a: Result<&2, &2, PE.PkcsError, Unit>, +t: List<&2, Result<&2, &2, PE.PkcsError, Unit>>, +h: {Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.first(Con{a, t})) == True{} : Bool}) -> {Result.is_done(&2, &2, PE.PkcsError, Unit, a) == True{} : Bool}:
  match a:
    case Fail{x}:
      Empty.absurd({False{} == True{} : Bool}, pq.bft(h))
    case Done{u}:
      {==}

def pq.first_tl(a: Result<&2, &2, PE.PkcsError, Unit>, +t: List<&2, Result<&2, &2, PE.PkcsError, Unit>>, +h: {Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.first(Con{a, t})) == True{} : Bool}) -> {Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.first(t)) == True{} : Bool}:
  match a:
    case Fail{x}:
      Empty.absurd({Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.first(t)) == True{} : Bool}, pq.bft(h))
    case Done{u}:
      h

def pq.first1(a: Result<&2, &2, PE.PkcsError, Unit>, +h: {Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.first([a])) == True{} : Bool}) -> {Result.is_done(&2, &2, PE.PkcsError, Unit, a) == True{} : Bool}:
  pq.first_hd(a, Nil{}, h)

# a signer of a list that passes the signers' checks passes its own
def pq.sok(+r: PR.PkcsRules, +s: P.CmsSignedData, pre: List<&2, PG.CmsSigner>, +g: PG.CmsSigner, +post: List<&2, PG.CmsSigner>, +h: {Result.is_done(&2, &2, PE.PkcsError, Unit, P.pk.signers_ok(r, s, List.append(&2, PG.CmsSigner, pre, Con{g, post}))) == True{} : Bool}) -> {Result.is_done(&2, &2, PE.PkcsError, Unit, P.pk.signer_ok(r, s, g)) == True{} : Bool}:
  match pre:
    case Nil{}:
      pq.first_hd(P.pk.signer_ok(r, s, g), [P.pk.signers_ok(r, s, post)], h)
    case Con{+p, +u}:
      pq.sok(r, s, u, g, post, pq.first1(P.pk.signers_ok(r, s, List.append(&2, PG.CmsSigner, u, Con{g, post})), pq.first_tl(P.pk.signer_ok(r, s, p), [P.pk.signers_ok(r, s, List.append(&2, PG.CmsSigner, u, Con{g, post}))], h)))

def pq.check_ok(ok: Bool, +e: PE.PkcsError, +h: {Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.check(ok, e)) == True{} : Bool}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, pq.bft(h))

def pq.gate_t(on: Bool, c: Result<&2, &2, PE.PkcsError, Unit>, +hon: {on == True{} : Bool}, +h: {Result.is_done(&2, &2, PE.PkcsError, Unit, PE.pk.gate(on, c)) == True{} : Bool}) -> {Result.is_done(&2, &2, PE.PkcsError, Unit, c) == True{} : Bool}:
  match on:
    case True{}:
      h
    case False{}:
      Empty.absurd({Result.is_done(&2, &2, PE.PkcsError, Unit, c) == True{} : Bool}, pq.bft(hon))

def pq.mdone(z: Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>, +h: {Result.is_done(&2, &2, AE.Asn1Error, ASc.Asn1Match, z) == True{} : Bool}) -> Sigma<&1, &1, ASc.Asn1Match, m => {z == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}>:
  match z:
    case Fail{x}:
      Empty.absurd(Sigma<&1, &1, ASc.Asn1Match, m => {Fail{x} == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}>, pq.bft(h))
    case Done{+m}:
      (m, {==})

# the signed attributes' octets match their schema under DER
def pq.der_match(+r: PR.PkcsRules, +b: B.Octets, +s: P.CmsSignedData, +pre: List<&2, PG.CmsSigner>, +g: PG.CmsSigner, +post: List<&2, PG.CmsSigner>, +a: PG.CmsAttrs, +e: {P.Cms.parse(r, b) == Done{s} : Result<&2, &2, PE.PkcsError, P.CmsSignedData>}, +hg: {P.CmsSignedData.signers(s) == List.append(&2, PG.CmsSigner, pre, Con{g, post}) : List<&2, PG.CmsSigner>}, +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}, +hd: {PR.PkcsRules.attrs_der(r) == True{} : Bool}) -> Sigma<&1, &1, ASc.Asn1Match, m => {ASc.Asn1.match(AR.Asn1Rules.der(), PSc.pk.s.attrs(0n), PG.CmsAttrs.raw(a)) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}>:
  +hc = PP.pp.finish(P.pk.parse0(r, b), r, s, e)
  +hcs = pq.first_tl(PE.pk.gate(PR.PkcsRules.versions(r), PE.pk.check(Nat.is_eq(P.CmsSignedData.version(s), P.Cms.expected_version(s)), PE.PkcsBadVersion{})), [P.pk.signers_ok(r, s, P.CmsSignedData.signers(s))], hc)
  +hcs1 = pq.first1(P.pk.signers_ok(r, s, P.CmsSignedData.signers(s)), hcs)
  +hcs2 = Equal.trans(Bool, Result.is_done(&2, &2, PE.PkcsError, Unit, P.pk.signers_ok(r, s, List.append(&2, PG.CmsSigner, pre, Con{g, post}))), Result.is_done(&2, &2, PE.PkcsError, Unit, P.pk.signers_ok(r, s, P.CmsSignedData.signers(s))), True{}, Equal.cong(List<&2, PG.CmsSigner>, Bool, z => Result.is_done(&2, &2, PE.PkcsError, Unit, P.pk.signers_ok(r, s, z)), List.append(&2, PG.CmsSigner, pre, Con{g, post}), P.CmsSignedData.signers(s), Equal.sym(List<&2, PG.CmsSigner>, P.CmsSignedData.signers(s), List.append(&2, PG.CmsSigner, pre, Con{g, post}), hg)), hcs1)
  +hso = pq.sok(r, s, pre, g, post, hcs2)
  +c1 = PE.pk.gate(PR.PkcsRules.versions(r), PE.pk.check(P.pk.signer_version(g), PE.PkcsBadVersion{}))
  +c2 = PE.pk.gate(PR.PkcsRules.attrs_der(r), PE.pk.check(P.pk.attrs_der(PG.CmsSigner.signed_attrs(g)), PE.PkcsAttrsNotDer{}))
  +c3 = PE.pk.gate(PR.PkcsRules.attrs_required(r), P.pk.required.attrs(P.CmsSignedData.content_type(s), PG.CmsSigner.signed_attrs(g)))
  +c4 = PE.pk.gate(PR.PkcsRules.digests_listed(r), PE.pk.check(P.pk.listed(P.CmsSignedData.digest_algs(s), PG.CmsSigner.digest_alg(g)), PE.PkcsDigestNotListed{}))
  +h2 = pq.first_hd(c2, [c3, c4], pq.first_tl(c1, [c2, c3, c4], hso))
  +h3 = pq.check_ok(P.pk.attrs_der(PG.CmsSigner.signed_attrs(g)), PE.PkcsAttrsNotDer{}, pq.gate_t(PR.PkcsRules.attrs_der(r), PE.pk.check(P.pk.attrs_der(PG.CmsSigner.signed_attrs(g)), PE.PkcsAttrsNotDer{}), hd, h2))
  +h4 = Equal.trans(Bool, P.pk.attrs_der(Some{a}), P.pk.attrs_der(PG.CmsSigner.signed_attrs(g)), True{}, Equal.cong(Maybe<&2, PG.CmsAttrs>, Bool, z => P.pk.attrs_der(z), Some{a}, PG.CmsSigner.signed_attrs(g), Equal.sym(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner.signed_attrs(g), Some{a}, ha)), h3)
  pq.mdone(ASc.Asn1.match(AR.Asn1Rules.der(), PSc.pk.s.attrs(0n), PG.CmsAttrs.raw(a)), h4)

def pq.nval(z: Maybe<&2, AN.Asn1Node>) -> AN.Asn1Node:
  match z:
    case None{}:
      AN.Asn1Prim{AT.Asn1Tag.null(), B.Octets.empty()}
    case Some{v}:
      v

def pq.ofst(p: B.Octets & B.Octets) -> B.Octets:
  (x, y) = p
  x

def pq.osnd(p: B.Octets & B.Octets) -> B.Octets:
  (x, y) = p
  y

# re-tagged: the DER of a SET of the same elements
def pq.der3(+g: PG.CmsSigner, +c: B.Octets, +a: PG.CmsAttrs, +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}, +ns: List<&2, AN.Asn1Node>, rt: Sigma<&1, &1, B.Octets, l => {PG.CmsAttrs.raw(a) == B.Octets.append(AEn.Asn1.identifier(AT.Asn1Tag.context(0n), True{}), l) : B.Octets} & {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), ns}) == Done{B.Octets.append(AEn.Asn1.identifier(AT.Asn1Tag.set(), True{}), l)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>) -> Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{PS.Cms.signed_message(g, c)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>:
  (+l, (+e1, +e2)) = rt
  +hv = AL.vec_identifier()
  +h0 = Equal.cong(B.Octets & B.Octets, B.Octets, z => pq.ofst(z), (AEn.Asn1.identifier(AT.Asn1Tag.context(0n), True{}), AEn.Asn1.identifier(AT.Asn1Tag.set(), True{})), (B.Octets.of_list([160]), B.Octets.of_list([49])), hv)
  +h1 = Equal.cong(B.Octets & B.Octets, B.Octets, z => pq.osnd(z), (AEn.Asn1.identifier(AT.Asn1Tag.context(0n), True{}), AEn.Asn1.identifier(AT.Asn1Tag.set(), True{})), (B.Octets.of_list([160]), B.Octets.of_list([49])), hv)
  %Equal.sym(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner.signed_attrs(g), Some{a}, ha) : Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{PS.pk.signed.msg(_, c)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>
  %Equal.sym(B.Octets, PG.CmsAttrs.raw(a), B.Octets.append(AEn.Asn1.identifier(AT.Asn1Tag.context(0n), True{}), l), e1) : Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{PS.Cms.set_tagged(_)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>
  %Equal.sym(B.Octets, AEn.Asn1.identifier(AT.Asn1Tag.context(0n), True{}), B.Octets.of_list([160]), h0) : Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{PS.Cms.set_tagged(B.Octets.append(_, l))} : Result<&2, &2, AE.Asn1Error, B.Octets>}>
  %Equal.sym(B.Octets, PS.Cms.set_tagged(B.Octets.append(B.Octets.of_list([160]), l)), B.Octets.append(B.Octets.of_list([49]), l), pq.retag(l)) : Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{_} : Result<&2, &2, AE.Asn1Error, B.Octets>}>
  %h1 : Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{B.Octets.append(_, l)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>
  (ns, e2)

def pq.der2(+g: PG.CmsSigner, +c: B.Octets, +a: PG.CmsAttrs, +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}, +ma: ASc.Asn1Match, +hw: {ASc.Asn1Match.raw(ma) == PG.CmsAttrs.raw(a) : B.Octets}, hn: Sigma<&1, &1, AN.Asn1Node, n => {ASc.Asn1Match.node(ma) == Some{n} : Maybe<&2, AN.Asn1Node>} & {AEn.Asn1.encode(n) == Done{ASc.Asn1Match.raw(ma)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>, ho: Sigma<&1, &1, List<&2, AN.Asn1Node>, ns => {ASc.Asn1Match.node(ma) == Some{AN.Asn1Cons{AT.Asn1Tag.context(0n), ns}} : Maybe<&2, AN.Asn1Node>}>) -> Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{PS.Cms.signed_message(g, c)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>:
  (+n, (+hn1, +hn2)) = hn
  (+ns, +ho1) = ho
  +hnn = Equal.cong(Maybe<&2, AN.Asn1Node>, AN.Asn1Node, z => pq.nval(z), Some{n}, Some{AN.Asn1Cons{AT.Asn1Tag.context(0n), ns}}, Equal.trans(Maybe<&2, AN.Asn1Node>, Some{n}, ASc.Asn1Match.node(ma), Some{AN.Asn1Cons{AT.Asn1Tag.context(0n), ns}}, Equal.sym(Maybe<&2, AN.Asn1Node>, ASc.Asn1Match.node(ma), Some{n}, hn1), ho1))
  +he = Equal.trans(Result<&2, &2, AE.Asn1Error, B.Octets>, AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.context(0n), ns}), AEn.Asn1.encode(n), Done{PG.CmsAttrs.raw(a)}, Equal.cong(AN.Asn1Node, Result<&2, &2, AE.Asn1Error, B.Octets>, z => AEn.Asn1.encode(z), AN.Asn1Cons{AT.Asn1Tag.context(0n), ns}, n, Equal.sym(AN.Asn1Node, n, AN.Asn1Cons{AT.Asn1Tag.context(0n), ns}, hnn)), Equal.trans(Result<&2, &2, AE.Asn1Error, B.Octets>, AEn.Asn1.encode(n), Done{ASc.Asn1Match.raw(ma)}, Done{PG.CmsAttrs.raw(a)}, hn2, Equal.cong(B.Octets, Result<&2, &2, AE.Asn1Error, B.Octets>, z => Done{z}, ASc.Asn1Match.raw(ma), PG.CmsAttrs.raw(a), hw)))
  pq.der3(g, c, a, ha, ns, AL.encode_retag(AT.Asn1Tag.context(0n), AT.Asn1Tag.set(), ns, PG.CmsAttrs.raw(a), {==}, {==}, he))

def pq.der1(+g: PG.CmsSigner, +c: B.Octets, +a: PG.CmsAttrs, +ha: {PG.CmsSigner.signed_attrs(g) == Some{a} : Maybe<&2, PG.CmsAttrs>}, dm: Sigma<&1, &1, ASc.Asn1Match, m => {ASc.Asn1.match(AR.Asn1Rules.der(), PSc.pk.s.attrs(0n), PG.CmsAttrs.raw(a)) == Done{m} : Result<&2, &2, AE.Asn1Error, ASc.Asn1Match>}>) -> Sigma<&1, &1, List<&2, AN.Asn1Node>, xs => {AEn.Asn1.encode(AN.Asn1Cons{AT.Asn1Tag.set(), xs}) == Done{PS.Cms.signed_message(g, c)} : Result<&2, &2, AE.Asn1Error, B.Octets>}>:
  (+ma, +em) = dm
  +o = PG.CmsAttrs.raw(a)
  +der = AR.Asn1Rules.der()
  pq.der2(g, c, a, ha, ma, AL.match_whole(der, {==}, PSc.pk.s.attrs(0n), o, ma, em), AL.match_der(der, {==}, {==}, PSc.pk.s.attrs(0n), o, ma, em), AL.match_of_node(der, AT.Asn1Tag.context(0n), PSc.pk.s.attr(), True{}, o, ma, em))
