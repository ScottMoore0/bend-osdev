# bend-osdev-asn1, tags (ITU-T X.680 (02/2021) clause 8: a class and a
# number; Table 1 assigns the universal ones) and their identifier octets
# (ITU-T X.690 (02/2021) 8.1.2): bits 8 and 7 the class (Table 1), bit 6
# primitive (0) or constructed (1), bits 5 to 1 the number when it is 0 to 30
# (8.1.2.2), else 11111 and the number in base-128 subsequent octets, bit 8
# set on all but the last, the first not 80 hex (8.1.2.4).
import Base
import ../bytes/bytes.bend as B
import ./number.bend as Nu

type Asn1Class is Data:
  Asn1Universal{}
  Asn1Application{}
  Asn1Context{}
  Asn1Private{}

type Asn1Tag is Data:
  Asn1Tag{cls: Asn1Class, num: Nat}

type A1Id1 is Data:
  A1Id1{cls: Asn1Class, cons: Bool, low: Nat}

def Asn1Tag.cls(t: Asn1Tag) -> Asn1Class:
  match t:
    case Asn1Tag{c, n}:
      c

def Asn1Tag.num(t: Asn1Tag) -> Nat:
  match t:
    case Asn1Tag{c, n}:
      n

def Asn1Tag.universal(n: Nat) -> Asn1Tag:
  Asn1Tag{Asn1Universal{}, n}

def Asn1Tag.context(n: Nat) -> Asn1Tag:
  Asn1Tag{Asn1Context{}, n}

# The universal tags of X.680 Table 1 that the typed readers use
def Asn1Tag.boolean() -> Asn1Tag:
  Asn1Tag.universal(1n)

def Asn1Tag.integer() -> Asn1Tag:
  Asn1Tag.universal(2n)

def Asn1Tag.bit_string() -> Asn1Tag:
  Asn1Tag.universal(3n)

def Asn1Tag.octet_string() -> Asn1Tag:
  Asn1Tag.universal(4n)

def Asn1Tag.null() -> Asn1Tag:
  Asn1Tag.universal(5n)

def Asn1Tag.oid() -> Asn1Tag:
  Asn1Tag.universal(6n)

def Asn1Tag.enumerated() -> Asn1Tag:
  Asn1Tag.universal(10n)

def Asn1Tag.utf8_string() -> Asn1Tag:
  Asn1Tag.universal(12n)

def Asn1Tag.sequence() -> Asn1Tag:
  Asn1Tag.universal(16n)

def Asn1Tag.set() -> Asn1Tag:
  Asn1Tag.universal(17n)

def Asn1Tag.printable_string() -> Asn1Tag:
  Asn1Tag.universal(19n)

def Asn1Tag.t61_string() -> Asn1Tag:
  Asn1Tag.universal(20n)

def Asn1Tag.ia5_string() -> Asn1Tag:
  Asn1Tag.universal(22n)

def Asn1Tag.utc_time() -> Asn1Tag:
  Asn1Tag.universal(23n)

def Asn1Tag.generalized_time() -> Asn1Tag:
  Asn1Tag.universal(24n)

def Asn1Tag.universal_string() -> Asn1Tag:
  Asn1Tag.universal(28n)

def Asn1Tag.bmp_string() -> Asn1Tag:
  Asn1Tag.universal(30n)

# the class's rank in X.680 8.6's canonical order, and its bits 8 and 7
def Asn1Class.rank(c: Asn1Class) -> Nat:
  match c:
    case Asn1Universal{}:
      0n
    case Asn1Application{}:
      1n
    case Asn1Context{}:
      2n
    case Asn1Private{}:
      3n

def Asn1Class.is_eq(a: Asn1Class, b: Asn1Class) -> Bool:
  Nat.is_eq(Asn1Class.rank(a), Asn1Class.rank(b))

def Asn1Tag.is_eq(a: Asn1Tag, b: Asn1Tag) -> Bool:
  match a b:
    case Asn1Tag{c, n} Asn1Tag{d, m}:
      Bool.and(Asn1Class.is_eq(c, d), Nat.is_eq(n, m))

def a1.tag_lt.go(c: Cmp, +n: Nat, +m: Nat) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      Nat.is_lt(n, m)
    case GT{}:
      False{}

# a before b in X.680 8.6's canonical order of tags
def Asn1Tag.is_lt(a: Asn1Tag, b: Asn1Tag) -> Bool:
  match a b:
    case Asn1Tag{c, +n} Asn1Tag{d, +m}:
      a1.tag_lt.go(Nat.cmp(Asn1Class.rank(c), Asn1Class.rank(d)), n, m)

def a1.cls_base(c: Asn1Class) -> Nat:
  match c:
    case Asn1Universal{}:
      0n
    case Asn1Application{}:
      64n
    case Asn1Context{}:
      128n
    case Asn1Private{}:
      192n

# the leading identifier octet's value: class bits, the P/C bit, and bits 5
# to 1 (low: the number, or 31 for the high-tag form)
def a1.id_octet(c: Asn1Class, cons: Bool, low: Nat) -> Nat:
  Nat.add(a1.cls_base(c), Nat.add(Bool.pick(Nat, cons, 32n, 0n), low))

def a1.id_pick(lt: Bool, c: Asn1Class, cons: Bool, +n: Nat) -> List<&2, U32>:
  match lt:
    case True{}:
      [Nu.a1.b(a1.id_octet(c, cons, n))]
    case False{}:
      Con{Nu.a1.b(a1.id_octet(c, cons, 31n)), Nu.a1.b128(n)}

# whether a tag number has identifier octets here: a low number, or a high
# one in at most six base-128 octets (number.bend's bound)
def a1.id_ok(+n: Nat) -> Bool:
  Bool.or(Nat.is_lt(n, 31n), Nat.is_le(List.length(&2, U32, Nu.a1.b128(n)), Nu.a1.max_octets()))

# the identifier octets of a tag, primitive or constructed (8.1.2)
def a1.id_bytes(c: Asn1Class, cons: Bool, +n: Nat) -> List<&2, U32>:
  a1.id_pick(Nat.is_lt(n, 31n), c, cons, n)

# The leading identifier octet, read: class, P/C bit, bits 5 to 1

def a1.id1.pc(ge: Bool, c: Asn1Class, +k: Nat) -> A1Id1:
  match ge:
    case True{}:
      A1Id1{c, True{}, Nat.sub(k, 32n)}
    case False{}:
      A1Id1{c, False{}, k}

def a1.id1.cls(c: Asn1Class, +k: Nat) -> A1Id1:
  a1.id1.pc(Nat.is_le(32n, k), c, k)

def a1.id1.a(ge: Bool, +k: Nat) -> A1Id1:
  match ge:
    case True{}:
      a1.id1.cls(Asn1Application{}, Nat.sub(k, 64n))
    case False{}:
      a1.id1.cls(Asn1Universal{}, k)

def a1.id1.c(ge: Bool, +k: Nat) -> A1Id1:
  match ge:
    case True{}:
      a1.id1.cls(Asn1Context{}, Nat.sub(k, 128n))
    case False{}:
      a1.id1.a(Nat.is_le(64n, k), k)

def a1.id1.p(ge: Bool, +k: Nat) -> A1Id1:
  match ge:
    case True{}:
      a1.id1.cls(Asn1Private{}, Nat.sub(k, 192n))
    case False{}:
      a1.id1.c(Nat.is_le(128n, k), k)

# the parts of a leading identifier octet of value k (below 256)
def a1.id1(+k: Nat) -> A1Id1:
  a1.id1.p(Nat.is_le(192n, k), k)
