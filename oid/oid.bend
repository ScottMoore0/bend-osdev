# bend-osdev-oid: object identifiers, the entry file. An object identifier
# is its arcs, a list of natural numbers (ITU-T X.680 (02/2021) clause 32);
# its DER form is the OBJECT IDENTIFIER element (X.690 (02/2021) 8.19), read
# and written through bend-osdev-asn1; its text form is the arcs in decimal
# joined by full stops (text.bend); the registry of names is registry.bend.
#
# An Oid is valid when it has both forms here: at least two arcs, the first
# 0, 1 or 2 and the second below 40 under 0 and 1 (X.690 8.19.4), every
# subidentifier within asn1's bound (below 2^42), and every arc of at most
# fourteen decimal digits. Every constructor (Oid.of_arcs, Oid.of_der,
# Oid.of_text) answers only valid Oids.
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/encode.bend as AEn
import ../asn1/asn1.bend as A
import ../asn1/oidval.bend as AO

type Oid is Data:
  Oid{arcs: List<&2, Nat>}

type OidError is Data:
  OidBadArcs{}
  OidBadText{}
  OidAsn1{error: AE.Asn1Error}

def Oid.arcs(o: Oid) -> List<&2, Nat>:
  match o:
    case Oid{xs}:
      xs

# Decimal digits (base 10), most significant first

def oid.dg.go(fuel: Nat, lt: Bool, +n: Nat) -> List<&2, Nat>:
  match fuel lt:
    case _ True{}:
      [n]
    case 0n False{}:
      [n]
    case 1n+f False{}:
      +q = Nat.div(n, 10n)
      List.append(&2, Nat, oid.dg.go(f, Nat.is_lt(q, 10n), q), [Nat.mod(n, 10n)])

def oid.digits(+n: Nat) -> List<&2, Nat>:
  oid.dg.go(n, Nat.is_lt(n, 10n), n)

# the most decimal digits an arc may have (Bend's run-time natural numbers
# are below 2^48, and 10^14 is below that)
def oid.max_digits() -> Nat:
  14n

def oid.text_ok(arcs: List<&2, Nat>) -> Bool:
  match arcs:
    case Nil{}:
      True{}
    case Con{+a, t}:
      Bool.and(Nat.is_le(List.length(&2, Nat, oid.digits(a)), oid.max_digits()), oid.text_ok(t))

# The DER form of arcs: the OBJECT IDENTIFIER element's octets

def oid.der.of(r: Result<&2, &2, AE.Asn1Error, B.Octets>) -> Result<&2, &2, AE.Asn1Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      AEn.Asn1.encode(AN.Asn1Prim{AT.Asn1Tag.oid(), c})

def oid.der(+arcs: List<&2, Nat>) -> Result<&2, &2, AE.Asn1Error, B.Octets>:
  oid.der.of(AO.Asn1.oid_content(arcs))

def oid.done(r: Result<&2, &2, AE.Asn1Error, B.Octets>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      True{}

# whether arcs name an object identifier with both forms here
def Oid.valid_arcs(+arcs: List<&2, Nat>) -> Bool:
  Bool.and(oid.text_ok(arcs), oid.done(oid.der(arcs)))

def Oid.valid(o: Oid) -> Bool:
  Oid.valid_arcs(Oid.arcs(o))

def oid.mk(ok: Bool, arcs: List<&2, Nat>) -> Result<&2, &2, OidError, Oid>:
  match ok:
    case True{}:
      Done{Oid{arcs}}
    case False{}:
      Fail{OidBadArcs{}}

# the Oid of arcs (OidBadArcs unless they are valid)
def Oid.of_arcs(+arcs: List<&2, Nat>) -> Result<&2, &2, OidError, Oid>:
  oid.mk(Oid.valid_arcs(arcs), arcs)

def oid.eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, s} Con{b, t}:
      Bool.and(Nat.is_eq(a, b), oid.eq(s, t))
    case _ _:
      False{}

def Oid.is_eq(a: Oid, b: Oid) -> Bool:
  oid.eq(Oid.arcs(a), Oid.arcs(b))

# whether o's arcs are arcs
def Oid.is(o: Oid, arcs: List<&2, Nat>) -> Bool:
  oid.eq(Oid.arcs(o), arcs)

# DER

def oid.wrap(r: Result<&2, &2, AE.Asn1Error, B.Octets>) -> Result<&2, &2, OidError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{OidAsn1{e}}
    case Done{b}:
      Done{b}

def oid.to_der.pick(ok: Bool, +arcs: List<&2, Nat>) -> Result<&2, &2, OidError, B.Octets>:
  match ok:
    case True{}:
      oid.wrap(oid.der(arcs))
    case False{}:
      Fail{OidBadArcs{}}

# the DER octets of o: 06, the length, the contents (OidBadArcs for an
# invalid Oid)
def Oid.to_der(o: Oid) -> Result<&2, &2, OidError, B.Octets>:
  match o:
    case Oid{+arcs}:
      oid.to_der.pick(Oid.valid_arcs(arcs), arcs)

def oid.of_arcs_r(r: Result<&2, &2, AE.Asn1Error, List<&2, Nat>>) -> Result<&2, &2, OidError, Oid>:
  match r:
    case Fail{e}:
      Fail{OidAsn1{e}}
    case Done{+arcs}:
      Oid.of_arcs(arcs)

# the Oid of an OBJECT IDENTIFIER element
def Oid.of_node(n: AN.Asn1Node) -> Result<&2, &2, OidError, Oid>:
  oid.of_arcs_r(AO.Asn1.get_oid(n))

def oid.of_der.r(r: Result<&2, &2, AE.Asn1Error, AN.Asn1Node>) -> Result<&2, &2, OidError, Oid>:
  match r:
    case Fail{e}:
      Fail{OidAsn1{e}}
    case Done{n}:
      Oid.of_node(n)

# the Oid whose DER octets b are (decoded under DER rules)
def Oid.of_der(b: B.Octets) -> Result<&2, &2, OidError, Oid>:
  oid.of_der.r(A.Asn1.decode(AR.Asn1Rules.der(), b))

def oid.node.of(r: Result<&2, &2, AE.Asn1Error, B.Octets>) -> Result<&2, &2, OidError, AN.Asn1Node>:
  match r:
    case Fail{e}:
      Fail{OidAsn1{e}}
    case Done{c}:
      Done{AN.Asn1Prim{AT.Asn1Tag.oid(), c}}

# o as an OBJECT IDENTIFIER element
def Oid.node(o: Oid) -> Result<&2, &2, OidError, AN.Asn1Node>:
  oid.node.of(AO.Asn1.oid_content(Oid.arcs(o)))

def OidError.name(e: OidError) -> String:
  match e:
    case OidBadArcs{}:
      "OidBadArcs"
    case OidBadText{}:
      "OidBadText"
    case OidAsn1{x}:
      "OidAsn1 " ++ AE.Asn1Error.name(x)
