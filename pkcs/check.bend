import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/node.bend as AN
import ../asn1/string.bend as AS
import ../asn1/rules.bend as AR
import ../asn1/bits.bend as ABi
import ../oid/oid.bend as O
import ../oid/text.bend as OT
import ../x509/rules.bend as XR
import ../x509/alg.bend as XA
import ../x509/name.bend as XN
import ../x509/namecmp.bend as XC
import ../x509/x509.bend as X
import ./error.bend as PE
import ./rules.bend as PR
import ./attr.bend as PA
import ./signer.bend as PG
import ./pkcs.bend as P
import ./signed.bend as PS
import ./p8.bend as P8

def hexd(+c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(U32, U32.is_lt(x, 58), U32.sub(x, 48), U32.sub(x, 87))

def unhex(s: String) -> List<&2, U32>:
  match s:
    case SCon{a, SCon{b, t}}:
      Con{U32.add(U32.mul(hexd(a), 16), hexd(b)), unhex(t)}
    case _:
      Nil{}

def hx(s: String) -> B.Octets:
  B.Octets.of_list(unhex(s))

def join(sep: String, xs: List<&2, String>) -> String:
  XN.x5.join(sep, xs)

def val(r: Result<&2, &2, AE.Asn1Error, AS.Asn1Str>) -> String:
  match r:
    case Fail{e}:
      "?"
    case Done{s}:
      AS.Asn1Str.text(s)

def atv(a: XN.X509Atv) -> String:
  match a:
    case XN.X509Atv{t, v}:
      OT.Oid.to_text(t) ++ "=" ++ val(AS.Asn1.get_string(AR.Asn1Rules.ber(), v))

def atvs(xs: List<&2, XN.X509Atv>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{atv(a), atvs(t)}

def rdns(rs: List<&2, List<&2, XN.X509Atv>>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{join(" + ", atvs(r)), rdns(t)}

def nm(n: XN.X509Name) -> String:
  join(", ", rdns(XN.X509Name.rdns(n)))

def algs(xs: List<&2, XA.X509AlgId>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{OT.Oid.to_text(XA.X509AlgId.oid(a)), algs(t)}

def hexes(xs: List<&2, B.Octets>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{B.Octets.hex(a), hexes(t)}

def mhex(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case None{}:
      "-"
    case Some{o}:
      B.Octets.hex(o)

def sid(s: PG.CmsSid) -> String:
  match s:
    case PG.CmsSidIssuer{i, n}:
      "iss:" ++ nm(i) ++ "/" ++ B.Octets.hex(n)
    case PG.CmsSidKeyId{k}:
      "ski:" ++ B.Octets.hex(k)

def attr1(+a: PA.CmsAttr) -> String:
  OT.Oid.to_text(PA.CmsAttr.attr_type(a)) ++ "=" ++ Nat.show(List.length(&2, AN.Asn1Node, PA.CmsAttr.values(a)))

def attrl(xs: List<&2, PA.CmsAttr>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{attr1(a), attrl(t)}

def attrs(m: Maybe<&2, PG.CmsAttrs>) -> String:
  match m:
    case None{}:
      "-"
    case Some{x}:
      join(",", attrl(PG.CmsAttrs.attrs(x)))

def certmatch(m: Maybe<&2, X.X509Cert>) -> String:
  match m:
    case None{}:
      "-"
    case Some{c}:
      B.Octets.hex(X.X509Cert.serial(c))

def signer(+s: P.CmsSignedData, +content: B.Octets, +g: PG.CmsSigner) -> String:
  join(" ", ["v" ++ Nat.show(PG.CmsSigner.version(g)), "sid=" ++ sid(PG.CmsSigner.sid(g)), "dig=" ++ OT.Oid.to_text(XA.X509AlgId.oid(PG.CmsSigner.digest_alg(g))), "attrs=" ++ attrs(PG.CmsSigner.signed_attrs(g)), "md=" ++ mhex(PS.Cms.message_digest(g)), "sigalg=" ++ OT.Oid.to_text(XA.X509AlgId.oid(PG.CmsSigner.sig_alg(g))), "sig=" ++ B.Octets.hex(PG.CmsSigner.signature(g)), "signed=" ++ B.Octets.hex(PS.Cms.signed_message(g, content)), "unsigned=" ++ Nat.show(List.length(&2, PA.CmsAttr, PG.CmsSigner.unsigned_attrs(g))), "cert=" ++ certmatch(PS.Cms.signer_certificate(XR.X509.rules_lenient(), XC.X509.name_rules(), s, g))])

def signers(+s: P.CmsSignedData, +content: B.Octets, gs: List<&2, PG.CmsSigner>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      Con{signer(s, content, g), signers(s, content, t)}

def show(+s: P.CmsSignedData, +content: B.Octets) -> String:
  join(" | ", ["v" ++ Nat.show(P.CmsSignedData.version(s)), "digests=" ++ join(",", algs(P.CmsSignedData.digest_algs(s))), "type=" ++ OT.Oid.to_text(P.CmsSignedData.content_type(s)), "content=" ++ mhex(P.CmsSignedData.content(s)), "certs=" ++ join(";", hexes(P.CmsSignedData.certificates(s))), "crls=" ++ Nat.show(List.length(&2, B.Octets, P.CmsSignedData.crls(s))), "signers=" ++ join(" || ", signers(s, content, P.CmsSignedData.signers(s)))])

def res(+content: B.Octets, x: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> String:
  match x:
    case Fail{e}:
      "ERR"
    case Done{+s}:
      show(s, Maybe.default(&2, B.Octets, P.CmsSignedData.content(s), content))

def ok(x: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> String:
  match x:
    case Fail{e}:
      PE.PkcsError.name(e)
    case Done{s}:
      "ok"

# a SignedData, with external content for a detached signature
def cms(+r: PR.PkcsRules, b: B.Octets, +content: B.Octets) -> String:
  res(content, P.Cms.parse(r, b))

def cms_ok(+r: PR.PkcsRules, b: B.Octets) -> String:
  ok(P.Cms.parse(r, b))

def mbits(m: Maybe<&2, ABi.Asn1Bits>) -> String:
  match m:
    case None{}:
      "-"
    case Some{b}:
      B.Octets.hex(ABi.Asn1Bits.octets(b))

def rhex(r: Result<&2, &2, PE.PkcsError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "-"
    case Done{o}:
      B.Octets.hex(o)

def mparams(m: Maybe<&2, AN.Asn1Node>) -> String:
  match m:
    case None{}:
      "-"
    case Some{n}:
      "p"

def key(+r: PR.PkcsRules, +k: P8.Pkcs8Key) -> String:
  +a = P8.Pkcs8Key.alg(k)
  join(" ", ["v" ++ Nat.show(P8.Pkcs8Key.version(k)), "alg=" ++ OT.Oid.to_text(XA.X509AlgId.oid(a)), "params=" ++ mparams(XA.X509AlgId.params(a)), "key=" ++ B.Octets.hex(P8.Pkcs8Key.private_key(k)), "curve=" ++ rhex(P8.Pkcs8.curve_private_key(r, k)), "pub=" ++ mbits(P8.Pkcs8Key.public_key(k)), "attrs=" ++ Nat.show(List.length(&2, PA.CmsAttr, P8.Pkcs8Key.attributes(k)))])

def kres(+r: PR.PkcsRules, x: Result<&2, &2, PE.PkcsError, P8.Pkcs8Key>) -> String:
  match x:
    case Fail{e}:
      "ERR"
    case Done{k}:
      key(r, k)

def p8(+r: PR.PkcsRules, b: B.Octets) -> String:
  kres(r, P8.Pkcs8.parse(r, b))


def msg_a() -> B.Octets:
  hx("308202cf06092a864886f70d010702a08202c0308202bc020101310d300b0609608648016503040201301806092a864886f70d010701a00b040968656c6c6f20636d73a082018c308201883082012fa00302010202020a0b300a06082a8648ce3d0403023023310f300d06035504030c065369676e65723110300e060355040a0c074578616d706c65301e170d3236313031393039313233345a170d3336313031363039313233345a3023310f300d06035504030c065369676e65723110300e060355040a0c074578616d706c653059301306072a8648ce3d020106082a8648ce3d0301070342000401a3b6c6dc42fb2afdafe73234ae60c021fbb1b2be47e7b67336abb2927060328deac34c1737ef76af5615dbb1b34fc9268b96f1143885f6d06620af51a99f92a3533051301d0603551d0e041604142d1d3720afadd7e6a30d02953d0b271b2b591e10301f0603551d230418301680142d1d3720afadd7e6a30d02953d0b271b2b591e10300f0603551d130101ff040530030101ff300a06082a8648ce3d0403020347003044022038715d6d47c5935ba52b601402b7654b2db4d985b89e14499317bfa158752d520220728ae6764c43ac319be646c6e380f973d82f65ef3ad921b7aaaac389631bf7b03181fd3081fa02010130293023310f300d06035504030c065369676e65723110300e060355040a0c074578616d706c6502020a0b300b0609608648016503040201a069301806092a864886f70d010903310b06092a864886f70d010701301c06092a864886f70d010905310f170d3236313031393039313233345a302f06092a864886f70d0109043122042058308a9b5212fd352cb20917d92960ef193e873541354d705407a85ce4bf6126300a06082a8648ce3d0403020446304402201ff19cdb91c22d88bc7566f94cf39f3548bcd38764e79d356f7f23a1e3f7f7ff022045d2a899fe92e56024aafc73306296dbd321f13ef57e664c27ab24e2c3ba0817")

def msg_b() -> B.Octets:
  hx("3081ae06092a864886f70d010702a081a030819d020103310d300b0609608648016503040201300b06092a864886f70d010701317c307a02010380142d1d3720afadd7e6a30d02953d0b271b2b591e10300b0609608648016503040201300a06082a8648ce3d0403020446304402202a4588d6d74e0941a426135ca6e2b4f7d7dff0b807592c4705032bf44696ecf102205cb5c8a2d2ab5da072f42e578a1292489418e7a2244921bd0328b4cff2d5f81f")

def key_e() -> B.Octets:
  hx("302e020100300506032b65700422042067faecaa15abdb3b8928165f67107f2b455c506dc2f084a588968f0a4084ca47")

def content() -> B.Octets:
  B.Octets.of_string("hello cms")

def trail(o: B.Octets) -> B.Octets:
  B.Octets.append(o, hx("00"))

def sha_stub(o: B.Octets) -> B.Octets:
  o

def mdsig(+c: B.Octets, gs: List<&2, PG.CmsSigner>) -> String:
  match gs:
    case Con{+g, t}:
      Bool.show(PS.Cms.digest_matches(~(o => sha_stub(o)), g, c)) ++ " " ++ Bool.show(PS.Cms.verify_with(~B.Octets, ~(o => Done{o}), ~(p => m => z => Nat.is_eq(B.Octets.len(m), 9n)), B.Octets.empty(), g, c))
    case Nil{}:
      "no signers"

# the message digest against a stand-in digest (the content itself), and
# the signature check with a stand-in scheme (valid when the signed octets
# are 9 long: the content's, signed without attributes)
def mdcheck(+c: B.Octets, x: Result<&2, &2, PE.PkcsError, P.CmsSignedData>) -> String:
  match x:
    case Fail{e}:
      PE.PkcsError.name(e)
    case Done{s}:
      mdsig(c, P.CmsSignedData.signers(s))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("SignedData")
    IO.print(cms(PR.Pkcs.rules(), msg_a(), content()))
    IO.print(cms(PR.Pkcs.rules(), msg_b(), content()))
    IO.print(cms_ok(PR.Pkcs.rules_strict(), msg_a()) ++ " " ++ cms_ok(PR.Pkcs.rules_strict(), msg_b()))
    IO.print(mdcheck(content(), P.Cms.parse(PR.Pkcs.rules(), msg_a())))
    IO.print(mdcheck(content(), P.Cms.parse(PR.Pkcs.rules(), msg_b())))
    IO.print("Refused")
    IO.print(cms_ok(PR.Pkcs.rules(), trail(msg_a())))
    IO.print(cms_ok(PR.Pkcs.rules(), B.Octets.take(100n, msg_a())))
    IO.print(cms_ok(PR.Pkcs.rules(), key_e()))
    IO.print(cms_ok(PR.Pkcs.rules(), hx("300b06092a864886f70d010701")))
    IO.print("PKCS 8")
    IO.print(p8(PR.Pkcs.rules(), key_e()))
    IO.print(p8(PR.Pkcs.rules(), B.Octets.take(20n, key_e())))
    IO.print(p8(PR.Pkcs.rules(), msg_b()))

#|SignedData
#|v1 | digests=2.16.840.1.101.3.4.2.1 | type=1.2.840.113549.1.7.1 | content=68656c6c6f20636d73 | certs=308201883082012fa00302010202020a0b300a06082a8648ce3d0403023023310f300d06035504030c065369676e65723110300e060355040a0c074578616d706c65301e170d3236313031393039313233345a170d3336313031363039313233345a3023310f300d06035504030c065369676e65723110300e060355040a0c074578616d706c653059301306072a8648ce3d020106082a8648ce3d0301070342000401a3b6c6dc42fb2afdafe73234ae60c021fbb1b2be47e7b67336abb2927060328deac34c1737ef76af5615dbb1b34fc9268b96f1143885f6d06620af51a99f92a3533051301d0603551d0e041604142d1d3720afadd7e6a30d02953d0b271b2b591e10301f0603551d230418301680142d1d3720afadd7e6a30d02953d0b271b2b591e10300f0603551d130101ff040530030101ff300a06082a8648ce3d0403020347003044022038715d6d47c5935ba52b601402b7654b2db4d985b89e14499317bfa158752d520220728ae6764c43ac319be646c6e380f973d82f65ef3ad921b7aaaac389631bf7b0 | crls=0 | signers=v1 sid=iss:2.5.4.3=Signer, 2.5.4.10=Example/0a0b dig=2.16.840.1.101.3.4.2.1 attrs=1.2.840.113549.1.9.3=1,1.2.840.113549.1.9.5=1,1.2.840.113549.1.9.4=1 md=58308a9b5212fd352cb20917d92960ef193e873541354d705407a85ce4bf6126 sigalg=1.2.840.10045.4.3.2 sig=304402201ff19cdb91c22d88bc7566f94cf39f3548bcd38764e79d356f7f23a1e3f7f7ff022045d2a899fe92e56024aafc73306296dbd321f13ef57e664c27ab24e2c3ba0817 signed=3169301806092a864886f70d010903310b06092a864886f70d010701301c06092a864886f70d010905310f170d3236313031393039313233345a302f06092a864886f70d0109043122042058308a9b5212fd352cb20917d92960ef193e873541354d705407a85ce4bf6126 unsigned=0 cert=0a0b
#|v3 | digests=2.16.840.1.101.3.4.2.1 | type=1.2.840.113549.1.7.1 | content=- | certs= | crls=0 | signers=v3 sid=ski:2d1d3720afadd7e6a30d02953d0b271b2b591e10 dig=2.16.840.1.101.3.4.2.1 attrs=- md=- sigalg=1.2.840.10045.4.3.2 sig=304402202a4588d6d74e0941a426135ca6e2b4f7d7dff0b807592c4705032bf44696ecf102205cb5c8a2d2ab5da072f42e578a1292489418e7a2244921bd0328b4cff2d5f81f signed=68656c6c6f20636d73 unsigned=0 cert=-
#|ok ok
#|False False
#|False True
#|Refused
#|PkcsAsn1 Asn1Trailing
#|PkcsAsn1 Asn1Truncated
#|PkcsAsn1 Asn1SchemaMismatch
#|PkcsNotSignedData
#|PKCS 8
#|v0 alg=1.3.101.112 params=- key=042067faecaa15abdb3b8928165f67107f2b455c506dc2f084a588968f0a4084ca47 curve=67faecaa15abdb3b8928165f67107f2b455c506dc2f084a588968f0a4084ca47 pub=- attrs=0
#|ERR
#|ERR
