import Base
import ../bytes/bytes.bend as B
import ./oid.bend as O
import ./text.bend as T
import ./registry.bend as R
import ./show.bend as S

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

def rb(r: Result<&2, &2, O.OidError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      O.OidError.name(e)
    case Done{b}:
      B.Octets.hex(b)

def ro(r: Result<&2, &2, O.OidError, O.Oid>) -> String:
  match r:
    case Fail{e}:
      O.OidError.name(e)
    case Done{o}:
      T.Oid.to_text(o)

def rn(r: Result<&2, &2, O.OidError, O.Oid>) -> String:
  match r:
    case Fail{e}:
      O.OidError.name(e)
    case Done{o}:
      S.Oid.show(o)

def mo(m: Maybe<&2, O.Oid>) -> String:
  match m:
    case None{}:
      "-"
    case Some{o}:
      T.Oid.to_text(o)

def ms(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "-"
    case Some{s}:
      s

def strict() -> T.OidTextRules:
  T.Oid.text_rules()

def lenient() -> T.OidTextRules:
  T.Oid.text_rules_lenient()

# text to DER
def td(s: String) -> String:
  rb(Result.bind(&2, &2, O.OidError, O.Oid, B.Octets, T.Oid.of_text(strict(), s), o => O.Oid.to_der(o)))

# DER to text
def dt(h: String) -> String:
  ro(O.Oid.of_der(hx(h)))

def sp(a: String, b: String) -> String:
  a ++ " " ++ b

# The registry: every entry valid, its DER read back as it, its name and
# arcs found again, and no name or arcs twice

def reg.same(r: Result<&2, &2, O.OidError, O.Oid>, +o: O.Oid) -> Bool:
  match r:
    case Done{x}:
      O.Oid.is_eq(x, o)
    case Fail{x}:
      False{}

def reg.msame(m: Maybe<&2, O.Oid>, +o: O.Oid) -> Bool:
  match m:
    case Some{x}:
      O.Oid.is_eq(x, o)
    case None{}:
      False{}

def reg.ok1(+e: R.OidEntry) -> Bool:
  +o : O.Oid = O.Oid{R.OidEntry.arcs(e)}
  +same = reg.same(Result.bind(&2, &2, O.OidError, B.Octets, O.Oid, O.Oid.to_der(o), b => O.Oid.of_der(b)), o)
  +named = reg.msame(R.Oid.named(R.OidEntry.name(e)), o)
  +name = String.eq(ms(R.Oid.name(o)), R.OidEntry.name(e))
  Bool.and(O.Oid.valid(o), Bool.and(same, Bool.and(named, name)))

def reg.all(es: List<&2, R.OidEntry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(reg.ok1(e), reg.all(t))

def reg.clash(+e: R.OidEntry, es: List<&2, R.OidEntry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{+f, t}:
      Bool.or(Bool.or(String.eq(R.OidEntry.name(e), R.OidEntry.name(f)), O.oid.eq(R.OidEntry.arcs(e), R.OidEntry.arcs(f))), reg.clash(e, t))

def reg.unique(es: List<&2, R.OidEntry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{+e, +t}:
      Bool.and(Bool.not(reg.clash(e, t)), reg.unique(t))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("DER")
    IO.print(sp(td("2.5.4.3"), td("1.2.840.113549.1.1.11")))
    IO.print(sp(td("2.16.840.1.101.3.4.2.1"), td("0.9.2342.19200300.100.1.25")))
    IO.print(sp(td("2.999.3"), td("1.39.4294967296")))
    IO.print(sp(dt("0603550403"), dt("06092a864886f70d01010b")))
    IO.print(sp(dt("060388370300"), dt("0604550403")))
    IO.print(sp(dt("060480550403"), dt("0603558003")))
    IO.print(sp(dt("068103550403"), dt("0403550403")))
    IO.print(sp(dt("2603550403"), dt("0600")))
    IO.print(sp(dt("06025504"), dt("060155")))
    IO.print(rb(O.Oid.to_der(O.Oid{[3n, 1n]})))
    IO.print(rb(O.Oid.to_der(O.Oid{[1n, 40n]})))
    IO.print(rb(O.Oid.to_der(O.Oid{[2n]})))
    IO.print(ro(O.Oid.of_arcs([2n, 5n, 4n, 3n])))
    IO.print("Text")
    IO.print(sp(ro(T.Oid.of_text(strict(), "1.2.840.113549")), ro(T.Oid.of_text(strict(), "0.0"))))
    IO.print(sp(ro(T.Oid.of_text(strict(), "1.02.3")), ro(T.Oid.of_text(lenient(), "1.02.3"))))
    IO.print(sp(ro(T.Oid.of_text(strict(), "")), ro(T.Oid.of_text(strict(), "1"))))
    IO.print(sp(ro(T.Oid.of_text(strict(), "1.2.")), ro(T.Oid.of_text(strict(), ".1.2"))))
    IO.print(sp(ro(T.Oid.of_text(strict(), "1.2a")), ro(T.Oid.of_text(strict(), "3.1"))))
    IO.print(sp(ro(T.Oid.of_text(strict(), "2.99999999999999")), ro(T.Oid.of_text(strict(), "2.999999999999999"))))
    IO.print(sp(ro(T.Oid.of_text(strict(), "1.2.-3")), ro(T.Oid.of_text(strict(), "1. 2"))))
    IO.print("Registry")
    IO.print(sp(rn(O.Oid.of_der(hx("06092a864886f70d01010b"))), rn(O.Oid.of_der(hx("06032a0304")))))
    IO.print(sp(mo(R.Oid.named("id-sha256")), mo(R.Oid.named("id-ecPublicKey"))))
    IO.print(sp(mo(R.Oid.named("secp256r1")), mo(R.Oid.named("no-such-name"))))
    IO.print(sp(ms(R.Oid.name(O.Oid{[2n, 5n, 29n, 19n]})), ms(R.Oid.name(O.Oid{[1n, 2n, 840n, 113549n, 1n, 9n, 4n]}))))
    IO.print(Bool.show(R.Oid.is_named(O.Oid{[2n, 5n, 4n, 3n]}, "id-at-commonName")))
    IO.print(Nat.show(List.length(&2, R.OidEntry, R.Oid.registry())))
    IO.print(sp(Bool.show(reg.all(R.Oid.registry())), Bool.show(reg.unique(R.Oid.registry()))))

#|DER
#|0603550403 06092a864886f70d01010b
#|0609608648016503040201 060a0992268993f22c640119
#|0603883703 06064f9080808000
#|2.5.4.3 1.2.840.113549.1.1.11
#|OidAsn1 Asn1Trailing OidAsn1 Asn1Truncated
#|OidAsn1 Asn1BadOid OidAsn1 Asn1BadOid
#|OidAsn1 Asn1NonMinimalLength OidAsn1 Asn1Unexpected
#|OidAsn1 Asn1Truncated OidAsn1 Asn1BadOid
#|2.5.4 2.5
#|OidBadArcs
#|OidBadArcs
#|OidBadArcs
#|2.5.4.3
#|Text
#|1.2.840.113549 0.0
#|OidBadText 1.2.3
#|OidBadText OidBadArcs
#|OidBadText OidBadText
#|OidBadText OidBadArcs
#|OidBadArcs OidBadText
#|OidBadText OidBadText
#|Registry
#|sha256WithRSAEncryption 1.2.3.4
#|2.16.840.1.101.3.4.2.1 1.2.840.10045.2.1
#|1.2.840.10045.3.1.7 -
#|id-ce-basicConstraints id-messageDigest
#|True
#|127
#|True True
