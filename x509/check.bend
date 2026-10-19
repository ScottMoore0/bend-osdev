import Base
import ../bytes/bytes.bend as B
import ../asn1/node.bend as AN
import ../asn1/tag.bend as AT
import ../crypto/crypto.bend as Cr
import ../asn1/bits.bend as ABi
import ../asn1/time.bend as ATi
import ../oid/oid.bend as O
import ../oid/text.bend as OT
import ./error.bend as XE
import ./rules.bend as XR
import ./alg.bend as XA
import ./name.bend as XN
import ./namecmp.bend as XC
import ./validity.bend as XV
import ./spki.bend as XK
import ./ext.bend as XX
import ./extval.bend as XEV
import ./gname.bend as XG
import ./x509.bend as X
import ./verify.bend as XVf

# Hex input

def hexd(+c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(U32, U32.is_lt(x, 58), U32.sub(x, 48), Bool.pick(U32, U32.is_lt(x, 71), U32.sub(x, 55), U32.sub(x, 87)))

def unhex(s: String) -> List<&2, U32>:
  match s:
    case SCon{a, SCon{b, t}}:
      Con{U32.add(U32.mul(hexd(a), 16), hexd(b)), unhex(t)}
    case _:
      Nil{}

def hx(s: String) -> B.Octets:
  B.Octets.of_list(unhex(s))

# Showing

def join(sep: String, xs: List<&2, String>) -> String:
  XN.x5.join(sep, xs)

def nats(xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{Nat.show(a), nats(t)}

def mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-"
    case Some{n}:
      Nat.show(n)

def mhex(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case None{}:
      "-"
    case Some{o}:
      B.Octets.hex(o)

def gns(gs: List<&2, XG.X509GeneralName>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      Con{XG.X509GeneralName.show(g), gns(t)}

def oids(os: List<&2, O.Oid>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{OT.Oid.to_text(o), oids(t)}

def err(e: XE.X509Error) -> String:
  XE.X509Error.name(e)

def r_bc(r: Result<&2, &2, XE.X509Error, XEV.X509BasicConstraints>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{+b}:
      "ca=" ++ Bool.show(XEV.X509BasicConstraints.ca(b)) ++ " pathlen=" ++ mnat(XEV.X509BasicConstraints.path_len(b))

def r_ku(r: Result<&2, &2, XE.X509Error, ABi.Asn1Bits>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{b}:
      join(",", nats(XEV.X509.key_usage_bits(b)))

def r_oct(r: Result<&2, &2, XE.X509Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.hex(o)

def mgns(m: Maybe<&2, List<&2, XG.X509GeneralName>>) -> String:
  match m:
    case None{}:
      "-"
    case Some{gs}:
      join(";", gns(gs))

def r_aki(r: Result<&2, &2, XE.X509Error, XEV.X509Aki>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{+a}:
      "keyid=" ++ mhex(XEV.X509Aki.key_id(a)) ++ " serial=" ++ mhex(XEV.X509Aki.serial(a)) ++ " issuer=" ++ mgns(XEV.X509Aki.issuer(a))

def r_gns(r: Result<&2, &2, XE.X509Error, List<&2, XG.X509GeneralName>>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{gs}:
      join(",", gns(gs))

def r_oids(r: Result<&2, &2, XE.X509Error, List<&2, O.Oid>>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{os}:
      join(",", oids(os))

def extv(k: Nat, +r: XR.X509Rules, +e: XX.X509Ext) -> String:
  match k:
    case 1n:
      r_bc(XEV.X509.basic_constraints_of(r, e))
    case 2n:
      r_ku(XEV.X509.key_usage_of(r, e))
    case 3n:
      r_oct(XEV.X509.subject_key_id_of(r, e))
    case 4n:
      r_aki(XEV.X509.authority_key_id_of(r, e))
    case 5n:
      r_gns(XEV.X509.subject_alt_name_of(r, e))
    case 6n:
      r_oids(XEV.X509.ext_key_usage_of(r, e))
    case _:
      B.Octets.hex(XX.X509Ext.value(e))

def ext1(+r: XR.X509Rules, +e: XX.X509Ext) -> String:
  +id = XX.X509Ext.id(e)
  +head = OT.Oid.to_text(id) ++ Bool.pick(String, XX.X509Ext.critical(e), "!", "") ++ " "
  head ++ extv(XEV.x5.kind(id), r, e)

def exts(+r: XR.X509Rules, es: List<&2, XX.X509Ext>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{ext1(r, e), exts(r, t)}

def mparams(m: Maybe<&2, AN.Asn1Node>) -> String:
  match m:
    case None{}:
      ""
    case Some{p}:
      "(params)"

def alg(+a: XA.X509AlgId) -> String:
  OT.Oid.to_text(XA.X509AlgId.oid(a)) ++ mparams(XA.X509AlgId.params(a))

def show(+r: XR.X509Rules, +c: X.X509Cert) -> String:
  +t = X.X509Cert.tbs(c)
  +v = X.X509Tbs.validity(t)
  join(" | ", ["v" ++ Nat.show(X.X509Tbs.version(t)), "serial=" ++ B.Octets.hex(X.X509Tbs.serial(t)), "sig=" ++ alg(X.X509Tbs.signature(t)), "issuer=" ++ XN.X509Name.show(X.X509Tbs.issuer(t)), "from=" ++ ATi.Asn1Time.show(XV.X509Validity.not_before(v)), "to=" ++ ATi.Asn1Time.show(XV.X509Validity.not_after(v)), "subject=" ++ XN.X509Name.show(X.X509Tbs.subject(t)), "key=" ++ alg(XK.X509Spki.alg(X.X509Tbs.spki(t))) ++ ":" ++ mhex(XK.X509Spki.key_octets(X.X509Tbs.spki(t))), "exts=" ++ join("; ", exts(r, X.X509Tbs.extensions(t))), "outer=" ++ alg(X.X509Cert.sig_alg(c)), "tbs=" ++ Nat.show(B.Octets.len(X.X509Cert.tbs_raw(c))), "siglen=" ++ Nat.show(B.Octets.len(X.X509Cert.signature_octets(c)))])

def res(+r: XR.X509Rules, x: Result<&2, &2, XE.X509Error, X.X509Cert>) -> String:
  match x:
    case Fail{e}:
      err(e)
    case Done{c}:
      show(r, c)

def parse(+r: XR.X509Rules, b: B.Octets) -> String:
  res(r, X.X509.parse(r, b))

def ca() -> B.Octets:
  hx("308201c230820174a00302010202021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a73081a430120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_dup() -> B.Octets:
  hx("308201e130820193a00302010202021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381c63081c330120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_unkcrit() -> B.Octets:
  hx("308201dc3082018ea00302010202021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381c13081be30120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b060105050703023018060a2b0601040183b24301010101ff04070c0568656c6c6f300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_v1ext() -> B.Octets:
  hx("308201bd3082016f02021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a73081a430120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_noissuer() -> B.Octets:
  hx("3082018d3082013fa00302010202021234300506032b65703000301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a73081a430120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_gentime() -> B.Octets:
  hx("308201c430820176a00302010202021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c07546573742043413020180f32303236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a73081a430120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_badbc() -> B.Octets:
  hx("308201bc3082016ea00302010202021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a130819e300c0603551d130101ff04020500300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_algmix() -> B.Octets:
  hx("308201c230820174a00302010202021234300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a73081a430120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6571034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def c_negserial() -> B.Octets:
  hx("308201c230820174a0030201020202ff01300506032b65703035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341301e170d3236313031393038333230335a170d3236313131383038333230335a3035310b300906035504061302555331143012060355040a0c0b4578616d706c65204f72673110300e06035504030c0754657374204341302a300506032b65700321001b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487da381a73081a430120603551d130101ff040830060101ff020102300e0603551d0f0101ff040403020186301d0603551d0e041604145df4d0eec300a73462cc8cf7010ab51a6e4e289c30400603551d1104393037820b6578616d706c652e636f6d810d61406578616d706c652e636f6d8704c00002018613687474703a2f2f6578616d706c652e636f6d2f301d0603551d250416301406082b0601050507030106082b06010505070302300506032b6570034100311f69bd62b774a49da5353a5f51528ca50b56b1b399ba98bb47e25102390ce05b4ae5745ca64db1951b74e7a6aca65f69937db74e30cfb5b6d3a1ff51cea605")

def ok(x: Result<&2, &2, XE.X509Error, X.X509Cert>) -> String:
  match x:
    case Fail{e}:
      err(e)
    case Done{c}:
      "ok"

def try3(+b: B.Octets) -> String:
  ok(X.X509.parse(XR.X509.rules(), b)) ++ " / " ++ ok(X.X509.parse(XR.X509.rules_strict(), b)) ++ " / " ++ ok(X.X509.parse(XR.X509.rules_lenient(), b))

def cut(+n: Nat, b: B.Octets) -> B.Octets:
  B.Octets.take(n, b)

def plus(b: B.Octets) -> B.Octets:
  B.Octets.append(b, hx("00"))

def names(x: Result<&2, &2, XE.X509Error, X.X509Cert>) -> String:
  match x:
    case Fail{e}:
      err(e)
    case Done{+c}:
      Bool.show(XVf.X509.self_issued(XC.X509.name_rules(), c)) ++ " " ++ Bool.show(XVf.X509.names_chain(XC.X509.name_rules_binary(), [c, c, c]))

def toy_pk(o: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Done{o}

# a stand-in scheme: valid when the message is 376 octets and the signature 64
def toy_verify(pk: B.Octets, m: B.Octets, s: B.Octets) -> Bool:
  Bool.and(Nat.is_eq(B.Octets.len(m), 376n), Nat.is_eq(B.Octets.len(s), 64n))

def verified(x: Result<&2, &2, XE.X509Error, X.X509Cert>) -> String:
  match x:
    case Fail{e}:
      err(e)
    case Done{+c}:
      Bool.show(XVf.X509.verify_by(~B.Octets, ~(o => toy_pk(o)), ~(p => m => s => toy_verify(p, m, s)), c, c))

def cn(+t: Nat, +s: String) -> XN.X509Name:
  XN.X509Name{[[XN.X509Atv{O.Oid{[2n, 5n, 4n, 3n]}, AN.Asn1Prim{AT.Asn1Tag.universal(t), B.Octets.of_string(s)}}]], B.Octets.of_string(s)}

def cmp(+a: XN.X509Name, +b: XN.X509Name) -> String:
  Bool.show(XC.X509Name.matches(XC.X509.name_rules(), a, b)) ++ " " ++ Bool.show(XC.X509Name.matches(XC.X509NameRules{True{}, False{}, False{}}, a, b)) ++ " " ++ Bool.show(XC.X509Name.matches(XC.X509.name_rules_binary(), a, b))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("Certificate")
    IO.print(parse(XR.X509.rules(), ca()))
    IO.print(try3(ca()))
    IO.print(names(X.X509.parse(XR.X509.rules(), ca())))
    IO.print(verified(X.X509.parse(XR.X509.rules(), ca())))
    IO.print("Refused")
    IO.print(try3(plus(ca())))
    IO.print(try3(cut(300n, ca())))
    IO.print("dup " ++ try3(c_dup()))
    IO.print("unkcrit " ++ try3(c_unkcrit()))
    IO.print("v1ext " ++ try3(c_v1ext()))
    IO.print("noissuer " ++ try3(c_noissuer()))
    IO.print("gentime " ++ try3(c_gentime()))
    IO.print("badbc " ++ try3(c_badbc()))
    IO.print("algmix " ++ try3(c_algmix()))
    IO.print("negserial " ++ try3(c_negserial()))
    IO.print("Serial numbers")
    IO.print(join(" ", [Bool.show(X.X509.serial_ok(hx("01"))), Bool.show(X.X509.serial_ok(hx("00"))), Bool.show(X.X509.serial_ok(hx("ff"))), Bool.show(X.X509.serial_ok(hx("0080"))), Bool.show(X.X509.serial_ok(hx("7f0102030405060708090a0b0c0d0e0f10111213"))), Bool.show(X.X509.serial_ok(hx("7f0102030405060708090a0b0c0d0e0f1011121314")))]))
    IO.print("Names")
    IO.print(cmp(cn(19n, "Example  Org"), cn(12n, "example org")))
    IO.print(cmp(cn(12n, " Example Org "), cn(12n, "Example Org")))
    IO.print(cmp(cn(12n, "Example"), cn(12n, "Example")))
    IO.print(cmp(cn(12n, "   "), cn(12n, "")))
    IO.print(cmp(cn(12n, "Example"), cn(12n, "Exemple")))

#|Certificate
#|v2 | serial=1234 | sig=1.3.101.112 | issuer=id-at-countryName=US, id-at-organizationName=Example Org, id-at-commonName=Test CA | from=2026-10-19T08:32:03Z | to=2026-11-18T08:32:03Z | subject=id-at-countryName=US, id-at-organizationName=Example Org, id-at-commonName=Test CA | key=1.3.101.112:1b09bcc17504b5a3db3c4d4b80b7fd7f63894eceb20db2743f93afc9fe42487d | exts=2.5.29.19! ca=True pathlen=2; 2.5.29.15! 0,5,6; 2.5.29.14 5df4d0eec300a73462cc8cf7010ab51a6e4e289c; 2.5.29.17 DNS:example.com,email:a@example.com,IP:c0000201,URI:http://example.com/; 2.5.29.37 1.3.6.1.5.5.7.3.1,1.3.6.1.5.5.7.3.2 | outer=1.3.101.112 | tbs=376 | siglen=64
#|ok / ok / ok
#|True True
#|True
#|Refused
#|X509Asn1 Asn1Trailing / X509Asn1 Asn1Trailing / X509Asn1 Asn1Trailing
#|X509Asn1 Asn1Truncated / X509Asn1 Asn1Truncated / X509Asn1 Asn1Truncated
#|dup X509DuplicateExtension 2.5.29.14 / X509DuplicateExtension 2.5.29.14 / ok
#|unkcrit ok / X509UnknownCritical 1.3.6.1.4.1.55619.1.1 / ok
#|v1ext X509BadVersion / X509BadVersion / ok
#|noissuer X509EmptyIssuer / X509EmptyIssuer / ok
#|gentime X509BadTime / X509BadTime / ok
#|badbc X509BadExtension 2.5.29.19 / X509BadExtension 2.5.29.19 / ok
#|algmix X509AlgMismatch / X509AlgMismatch / ok
#|negserial ok / X509BadSerial / ok
#|Serial numbers
#|True False False True True False
#|Names
#|True False False
#|True False False
#|True True True
#|True False False
#|False False False
