# bend-osdev-acpi, aml_ns.bend: the ACPI namespace (ACPI 6.5, section 5.3):
# named objects by absolute path, the predefined root scopes (5.3.1), and
# the search rules for names (5.3: a name of one NameSeg with no prefix is
# looked up in the current scope and then in each enclosing scope up to the
# root; any other name is taken as it stands).
#
# Paths are strings: "\" for the root, "\_SB_.PCI0" below it, every
# segment four characters.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./aml_name.bend as N
import ./aml_value.bend as V

type AmlObject is Data:
  # Name(): a data object
  AmlOData{v: V.AmlValue}
  # Method(): its argument count, its flags byte and its body (AML bytes)
  AmlOMethod{nargs: Nat, flags: U32, body: B.Octets}
  # Scope, Device, Processor, PowerResource, ThermalZone: the ObjectType
  # code (0 for a plain scope)
  AmlOScope{kind: U32}
  # OperationRegion(): address space, offset, length; parent: the scope
  # that holds it (its device's _ADR gives a PCI region its function)
  AmlORegion{space: U32, offset: W.W64, length: W.W64, parent: String}
  # a field unit of a region: bit offset and width, the field's flags
  # (access type, lock rule, update rule) and access attribute
  AmlOField{region: String, bit_off: Nat, bits: Nat, flags: U32}
  # a field unit reached through an index register and a data register
  AmlOIndexField{index: String, data: String, bit_off: Nat, bits: Nat, flags: U32}
  # a field of a buffer (CreateBitField and the others): the buffer's
  # location, bit offset and width
  AmlOBufField{buf: V.AmlLoc, bit_off: Nat, bits: Nat}
  AmlOMutex{sync: U32}
  AmlOEvent{}
  AmlOAlias{target: String}
  # an object the interpreter provides: 1 is \_OSI
  AmlOBuiltin{id: U32}
  # declared by External, not defined in the tables read
  AmlOExternal{kind: U32}

type AmlNs is Data:
  AmlNs{objs: Map<&2, AmlObject>}

def AmlObject.type(o: AmlObject) -> U32:
  match o:
    case AmlOData{v}:
      V.AmlValue.type(v)
    case AmlOMethod{n, f, b}:
      8
    case AmlOScope{k}:
      k
    case AmlORegion{s, off, l, p}:
      10
    case AmlOField{r, o2, n, f}:
      5
    case AmlOIndexField{i, d, o2, n, f}:
      5
    case AmlOBufField{b, o2, n}:
      14
    case AmlOMutex{s}:
      9
    case AmlOEvent{}:
      7
    case AmlOAlias{t}:
      0
    case AmlOBuiltin{i}:
      8
    case AmlOExternal{k}:
      k

# Paths

def AmlPath.root() -> String:
  "\\"

def AmlPath.is_root(+p: String) -> Bool:
  String.eq(p, "\\")

def ns.child.pick(root: Bool, scope: String, seg: String) -> String:
  match root:
    case True{}:
      "\\" ++ seg
    case False{}:
      scope ++ "." ++ seg

def ns.parent.pick(top: Bool, +p: String) -> String:
  match top:
    case True{}:
      "\\"
    case False{}:
      String.take(p, Nat.sub(String.length(p), 5n))

# the last segment of a path ("" for the root)

# the enclosing scope (the root's is the root)

# a segment (4 characters) below a scope
def AmlPath.child(+scope: String, seg: String) -> String:
  ns.child.pick(AmlPath.is_root(scope), scope, seg)

def AmlPath.parent(+p: String) -> String:
  ns.parent.pick(Nat.is_le(String.length(p), 5n), p)

def AmlPath.last(+p: String) -> String:
  String.drop(p, Nat.sub(String.length(p), 4n))

def ns.ups(n: Nat, +p: String) -> String:
  match n:
    case 0n:
      p
    case 1n+k:
      ns.ups(k, AmlPath.parent(p))

def ns.segs(ss: List<&2, B.Octets>, +p: String) -> String:
  match ss:
    case Nil{}:
      p
    case Con{s, t}:
      ns.segs(t, AmlPath.child(p, B.Octets.to_string(s)))

def ns.of_name.pick(root: Bool, u: Nat, +scope: String, ss: List<&2, B.Octets>) -> String:
  match root:
    case True{}:
      ns.segs(ss, "\\")
    case False{}:
      ns.segs(ss, ns.ups(u, scope))

# Objects


# a name taken as it stands, from a scope (no search): where Name, Method
# and the other definitions create their object
def AmlPath.of_name(+scope: String, n: N.AmlName) -> String:
  match n:
    case N.AmlName{r, u, ss}:
      ns.of_name.pick(r, u, scope, ss)

def AmlNs.empty() -> AmlNs:
  AmlNs{Map.new(&2, AmlObject)}

def ns.snd.bool(r: Map<&2, AmlObject> & Bool) -> Bool:
  (m, b) = r
  b


def ns.snd.obj(r: Map<&2, AmlObject> & AmlObject) -> AmlObject:
  (m, o) = r
  o


def ns.got(has: Bool, +m: Map<&2, AmlObject>, +p: String) -> Maybe<&2, AmlObject>:
  match has:
    case True{}:
      Some{ns.snd.obj(Map.get(AmlObject, AmlOEvent{}, m, p))}
    case False{}:
      None{}

# the object at a path

def AmlNs.has(ns: AmlNs, +p: String) -> Bool:
  match ns:
    case AmlNs{m}:
      ns.snd.bool(Map.has(&2, AmlObject, m, p))

# the object at a path
def AmlNs.get(ns: AmlNs, +p: String) -> Maybe<&2, AmlObject>:
  match ns:
    case AmlNs{+m}:
      ns.got(ns.snd.bool(Map.has(&2, AmlObject, m, p)), m, p)

def AmlNs.set(ns: AmlNs, p: String, o: AmlObject) -> AmlNs:
  match ns:
    case AmlNs{m}:
      AmlNs{Map.set(&2, AmlObject, m, p, o)}

def AmlNs.remove(ns: AmlNs, p: String) -> AmlNs:
  match ns:
    case AmlNs{m}:
      AmlNs{Map.del(&2, AmlObject, m, p)}

# every path, sorted
def AmlNs.paths(ns: AmlNs) -> List<&2, String>:
  match ns:
    case AmlNs{m}:
      List.sort(~String, ~String.is_le, Map.keys(&2, AmlObject, m))

# the search for a NameSeg from a scope outward; hit: it is in this scope;
# top: this scope is the root
def ns.search.go(n: Nat, hit: Bool, top: Bool, +ns: AmlNs, +scope: String, +seg: String) -> Maybe<&2, String>:
  match n:
    case 0n:
      None{}
    case 1n+k:
      match hit:
        case True{}:
          Some{AmlPath.child(scope, seg)}
        case False{}:
          match top:
            case True{}:
              None{}
            case False{}:
              +up = AmlPath.parent(scope)
              ns.search.go(k, AmlNs.has(ns, AmlPath.child(up, seg)), AmlPath.is_root(up), ns, up, seg)

def ns.single(ss: List<&2, B.Octets>) -> String:
  match ss:
    case Con{s, t}:
      B.Octets.to_string(s)
    case Nil{}:
      ""


def ns.exists(hit: Bool, p: String) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      None{}

# The namespace OSPM starts with (5.3.1, 5.7): the root scopes _GPE, _PR_,
# _SB_, _SI_ and _TZ_, _OS_ (the operating system's name), _REV and the
# _OSI method

def ns.resolve.pick(single: Bool, +ns: AmlNs, +scope: String, +n: N.AmlName) -> Maybe<&2, String>:
  match single:
    case True{}:
      +seg = ns.single(N.AmlName.segs(n))
      ns.search.go(String.length(scope), AmlNs.has(ns, AmlPath.child(scope, seg)), AmlPath.is_root(scope), ns, scope, seg)
    case False{}:
      +p = AmlPath.of_name(scope, n)
      ns.exists(AmlNs.has(ns, p), p)


# the object a name refers to, from a scope: a single NameSeg is searched
# for outward (5.3); None if it is not defined
def AmlNs.resolve(+ns: AmlNs, +scope: String, +n: N.AmlName) -> Maybe<&2, String>:
  match n:
    case N.AmlName{r, u, +ss}:
      ns.resolve.pick(Bool.and(Bool.not(r), Bool.and(Nat.is_eq(u, 0n), Nat.is_eq(List.length(&2, B.Octets, ss), 1n))), ns, scope, N.AmlName{r, u, ss})

def AmlNs.initial(os: String, rev: U32) -> AmlNs:
  +a = AmlNs.set(AmlNs.empty(), "\\", AmlOScope{0})
  +b = AmlNs.set(AmlNs.set(AmlNs.set(a, "\\_GPE", AmlOScope{0}), "\\_PR_", AmlOScope{0}), "\\_SB_", AmlOScope{6})
  +c = AmlNs.set(AmlNs.set(b, "\\_SI_", AmlOScope{0}), "\\_TZ_", AmlOScope{0})
  AmlNs.set(AmlNs.set(AmlNs.set(c, "\\_OS_", AmlOData{V.AmlStr{B.Octets.of_string(os)}}), "\\_REV", AmlOData{V.AmlInt{W.W64.from_u32(rev)}}), "\\_OSI", AmlOBuiltin{1})
