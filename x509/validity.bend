# bend-osdev-x509, Validity (RFC 5280 4.1.2.5): the times a certificate is
# valid from and to, each a UTCTime or a GeneralizedTime (Time ::= CHOICE
# { utcTime UTCTime, generalTime GeneralizedTime }). Each time keeps which
# it was, for the profile's check (rules.bend, time_profile): UTCTime for
# years through 2049 and GeneralizedTime from 2050 (4.1.2.5), Zulu time
# with seconds (4.1.2.5.1, 4.1.2.5.2; asn1 checks the seconds and the Z
# under DER), no fractions of a second (4.1.2.5.2).
import Base
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/time.bend as ATi
import ../asn1/schema.bend as ASc
import ./error.bend as XE
import ./rules.bend as XR

type X509Time is Data:
  X509Time{time: ATi.Asn1Time, utc: Bool}

type X509Validity is Data:
  X509Validity{not_before: X509Time, not_after: X509Time}

def X509Time.time(t: X509Time) -> ATi.Asn1Time:
  match t:
    case X509Time{x, u}:
      x

def X509Time.utc(t: X509Time) -> Bool:
  match t:
    case X509Time{x, u}:
      u

def X509Validity.not_before(v: X509Validity) -> ATi.Asn1Time:
  match v:
    case X509Validity{a, b}:
      X509Time.time(a)

def X509Validity.not_after(v: X509Validity) -> ATi.Asn1Time:
  match v:
    case X509Validity{a, b}:
      X509Time.time(b)

# whether t is within the validity period, both ends included (4.1.2.5)
def X509Validity.contains(+v: X509Validity, +t: ATi.Asn1Time) -> Bool:
  Bool.and(Bool.not(Cmp.is_gt(ATi.Asn1Time.cmp(X509Validity.not_before(v), t))), Bool.not(Cmp.is_gt(ATi.Asn1Time.cmp(t, X509Validity.not_after(v)))))

# The profile's check

def x5.zulu(z: ATi.Asn1Zone) -> Bool:
  match z:
    case ATi.Asn1Zulu{}:
      True{}
    case _:
      False{}

def x5.whole(fs: List<&2, Nat>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, t}:
      False{}

def X509Time.profile_ok(t: X509Time) -> Bool:
  match t:
    case X509Time{ATi.Asn1Time{y, mo, d, h, mi, s, fs, z}, u}:
      Bool.and(Bool.not(Bool.xor(u, Nat.is_lt(y, 2050n))), Bool.and(x5.zulu(z), x5.whole(fs)))

def X509Validity.profile_ok(v: X509Validity) -> Bool:
  match v:
    case X509Validity{a, b}:
      Bool.and(X509Time.profile_ok(a), X509Time.profile_ok(b))

# Reading

def x5.time.mk(r: Result<&2, &2, AE.Asn1Error, ATi.Asn1Time>, utc: Bool) -> Result<&2, &2, XE.X509Error, X509Time>:
  match r:
    case Fail{e}:
      Fail{XE.X509BadTime{}}
    case Done{t}:
      Done{X509Time{t, utc}}

def x5.time.of(+r: XR.X509Rules, m: Maybe<&2, AN.Asn1Node>) -> Result<&2, &2, XE.X509Error, X509Time>:
  match m:
    case None{}:
      Fail{XE.X509BadTime{}}
    case Some{+n}:
      x5.time.mk(ATi.Asn1.get_time(XR.X509Rules.asn1(r), XR.X509Rules.pivot(r), n), AT.Asn1Tag.is_eq(AN.Asn1Node.tag(n), AT.Asn1Tag.utc_time()))

def x5.validity.mk(a: Result<&2, &2, XE.X509Error, X509Time>, b: Result<&2, &2, XE.X509Error, X509Time>) -> Result<&2, &2, XE.X509Error, X509Validity>:
  match a b:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{y}:
      Done{X509Validity{x, y}}

# a Validity matched against x5.s.validity()
def x5.validity.of(+r: XR.X509Rules, +m: ASc.Asn1Match) -> Result<&2, &2, XE.X509Error, X509Validity>:
  x5.validity.mk(x5.time.of(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 0n))), x5.time.of(r, ASc.Asn1Match.node(ASc.Asn1Match.at(m, 1n))))
