# bend-osdev-acpi, aml_value.bend: the values AML computes with (ACPI 6.5,
# section 19.3.5, ASL Data Types, and 19.3.5.7, Data Type Conversion
# Rules): integers (64 bits, or 32 in a definition block of revision
# below 2), strings, buffers, packages, and object references.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E

# Where a value lives, for Store, RefOf and Index
type AmlLoc is Data:
  # a named object, by its absolute path ("\_SB_.PCI0.FOO_")
  AmlLName{path: String}
  AmlLLocal{i: Nat}
  AmlLArg{i: Nat}
  # element i of the buffer, string or package at a location
  AmlLIndex{base: AmlLoc, i: Nat}
  # element i of a value that has no location (Index of a temporary)
  AmlLElem{v: AmlValue, i: Nat}
  AmlLDebug{}
  # the NullName target: results stored there are dropped
  AmlLNone{}

type AmlValue is Data:
  AmlUninit{}
  AmlInt{v: W.W64}
  # a String (without its NUL)
  AmlStr{s: B.Octets}
  AmlBuf{b: B.Octets}
  AmlPkg{xs: List<&2, AmlValue>}
  # an object reference: RefOf, Index, or a name inside a package
  AmlRef{loc: AmlLoc}
  # a named object that holds no data (a device, a method, a region, ...)
  # used as an operand: its path and ObjectType code
  AmlObj{path: String, kind: U32}

# ObjectType codes (chapter 19, ObjectType): 0 uninitialized, 1 integer,
# 2 string, 3 buffer, 4 package, 5 field unit, 6 device, 7 event, 8 method,
# 9 mutex, 10 operation region, 11 power resource, 12 processor, 13 thermal
# zone, 14 buffer field, 16 debug object
def AmlValue.type(v: AmlValue) -> U32:
  match v:
    case AmlUninit{}:
      0
    case AmlInt{x}:
      1
    case AmlStr{s}:
      2
    case AmlBuf{b}:
      3
    case AmlPkg{xs}:
      4
    case AmlRef{l}:
      0
    case AmlObj{p, k}:
      k

# Integers of the definition block's width

# the low 32 bits only, when the block is 32-bit
def AmlInt.fit(wide: Bool, +v: W.W64) -> W.W64:
  match wide:
    case True{}:
      v
    case False{}:
      W.W64.from_u32(W.W64.lo(v))

def AmlInt.ones(wide: Bool) -> W.W64:
  AmlInt.fit(wide, W.W64.max())

# AML's True is Ones, False is Zero
def AmlInt.of_bool(+wide: Bool, b: Bool) -> W.W64:
  match b:
    case True{}:
      AmlInt.ones(wide)
    case False{}:
      W.W64.zero()

def AmlInt.width_bytes(wide: Bool) -> Nat:
  match wide:
    case True{}:
      8n
    case False{}:
      4n

# Conversions (19.3.5.7)

# up to n bytes, little-endian
def val.le.go(n: Nat, xs: List<&2, U32>, +sh: Nat, acc: W.W64) -> W.W64:
  match n:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case Con{h, t}:
          val.le.go(p, t, Nat.add(sh, 8n), W.W64.or(acc, W.W64.shl(W.W64.from_u32(U32.and(h, 255)), sh)))

def val.hexdig.pick(d: Bool, u: Bool, l: Bool, +c: U32) -> Maybe<&2, U32>:
  match d:
    case True{}:
      Some{U32.sub(c, 48)}
    case False{}:
      match u:
        case True{}:
          Some{U32.sub(c, 55)}
        case False{}:
          match l:
            case True{}:
              Some{U32.sub(c, 87)}
            case False{}:
              None{}

def val.hexdig(+c: U32) -> Maybe<&2, U32>:
  val.hexdig.pick(Bool.and(U32.is_le(48, c), U32.is_le(c, 57)), Bool.and(U32.is_le(65, c), U32.is_le(c, 70)), Bool.and(U32.is_le(97, c), U32.is_le(c, 102)), c)

def val.decdig(+c: U32) -> Maybe<&2, U32>:
  val.hexdig.pick(Bool.and(U32.is_le(48, c), U32.is_le(c, 57)), False{}, False{}, c)

def val.dig.head(hex: Bool, xs: List<&2, U32>) -> Maybe<&2, U32>:
  match hex xs:
    case _ Nil{}:
      None{}
    case True{} Con{+h, t}:
      val.hexdig(h)
    case False{} Con{+h, t}:
      val.decdig(h)

def val.base(hex: Bool) -> W.W64:
  match hex:
    case True{}:
      W.W64.from_u32(16)
    case False{}:
      W.W64.from_u32(10)


# digits from the front of a string, up to the first other character or
# n digits; m: the first character's digit value
def val.digits(n: Nat, xs: List<&2, U32>, m: Maybe<&2, U32>, acc: W.W64, +hex: Bool) -> W.W64:
  match n:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case Con{h, +t}:
          match m:
            case None{}:
              acc
            case Some{d}:
              val.digits(p, t, val.dig.head(hex, t), W.W64.add(W.W64.mul(acc, val.base(hex)), W.W64.from_u32(d)), hex)

def val.hex.parse(+wide: Bool, +xs: List<&2, U32>) -> W.W64:
  val.digits(Nat.mul(2n, AmlInt.width_bytes(wide)), xs, val.dig.head(True{}, xs), W.W64.zero(), True{})

def val.has0x(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{a, Con{+b, t}}:
      Bool.and(U32.is_eq(a, 48), Bool.or(U32.is_eq(b, 120), U32.is_eq(b, 88)))
    case _:
      False{}

def val.parse_int.pick(hex: Bool, +wide: Bool, +xs: List<&2, U32>) -> W.W64:
  match hex:
    case True{}:
      AmlInt.fit(wide, val.hex.parse(wide, B.drop(2n, xs)))
    case False{}:
      AmlInt.fit(wide, val.digits(20n, xs, val.dig.head(False{}, xs), W.W64.zero(), False{}))

# the implicit conversion to Integer: a buffer's first 8 (or 4) bytes,
# little-endian; a string's leading hexadecimal digits

# a String as an Integer, as ToInteger reads it: hexadecimal after 0x,
# decimal otherwise
def AmlValue.parse_int(+wide: Bool, +xs: List<&2, U32>) -> W.W64:
  val.parse_int.pick(val.has0x(xs), wide, xs)

def AmlValue.to_int(+wide: Bool, v: AmlValue) -> Result<&2, &2, E.AcpiError, W.W64>:
  match v:
    case AmlInt{x}:
      Done{AmlInt.fit(wide, x)}
    case AmlBuf{b}:
      Done{val.le.go(AmlInt.width_bytes(wide), B.Octets.to_list(b), 0n, W.W64.zero())}
    case AmlStr{s}:
      Done{val.hex.parse(wide, B.Octets.to_list(s))}
    case AmlUninit{}:
      Fail{E.AcpiAmlBadType{"uninitialized value used as an integer"}}
    case AmlPkg{xs}:
      Fail{E.AcpiAmlBadType{"package used as an integer"}}
    case AmlRef{l}:
      Fail{E.AcpiAmlBadType{"reference used as an integer"}}
    case AmlObj{p, k}:
      Fail{E.AcpiAmlBadType{"object used as an integer"}}

def val.int.bytes(wide: Bool, +x: W.W64) -> B.Octets:
  match wide:
    case True{}:
      B.Octets.le64(x)
    case False{}:
      B.Octets.le32(W.W64.lo(x))

# the implicit conversion to Buffer: an integer's 8 (or 4) bytes,
# little-endian; a string's bytes and its NUL
def AmlValue.to_buf(+wide: Bool, v: AmlValue) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match v:
    case AmlInt{x}:
      Done{val.int.bytes(wide, x)}
    case AmlBuf{b}:
      Done{b}
    case AmlStr{s}:
      Done{B.Octets.append(s, B.Octets.of_list([0]))}
    case _:
      Fail{E.AcpiAmlBadType{"cannot convert to a buffer"}}

def val.hex.digit.pick(lt: Bool, +d: U32) -> U32:
  match lt:
    case True{}:
      U32.add(48, d)
    case False{}:
      U32.add(55, d)

# n hex digits of x, most significant first, upper case

def val.hex.digit(+d: U32) -> U32:
  val.hex.digit.pick(U32.is_lt(d, 10), d)

def val.hex.text(n: Nat, +x: W.W64, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      val.hex.text(p, W.W64.shr(x, 4n), Con{val.hex.digit(U32.and(W.W64.lo(x), 15)), acc})

def val.buf.text(xs: List<&2, U32>, first: Bool) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      match first:
        case True{}:
          Con{val.hex.digit(U32.shrn(h, 4n)), Con{val.hex.digit(U32.and(h, 15)), val.buf.text(t, False{})}}
        case False{}:
          Con{32, Con{val.hex.digit(U32.shrn(h, 4n)), Con{val.hex.digit(U32.and(h, 15)), val.buf.text(t, False{})}}}

# the implicit conversion to String: an integer as 16 (or 8) hex digits; a
# buffer as two hex digits per byte, separated by spaces
def AmlValue.to_str(+wide: Bool, v: AmlValue) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match v:
    case AmlInt{x}:
      Done{B.Octets.of_list(val.hex.text(Nat.mul(2n, AmlInt.width_bytes(wide)), x, Nil{}))}
    case AmlStr{s}:
      Done{s}
    case AmlBuf{b}:
      Done{B.Octets.of_list(val.buf.text(B.Octets.to_list(b), True{}))}
    case _:
      Fail{E.AcpiAmlBadType{"cannot convert to a string"}}

# Comparison (chapter 19, LEqual, LGreater, LLess): integers as
# unsigned numbers; strings and buffers byte by byte, a prefix first

def val.cmp.then(prev: Cmp, c: Cmp) -> Cmp:
  match prev:
    case EQ{}:
      c
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def val.cmp.go(xs: List<&2, U32>, ys: List<&2, U32>, prev: Cmp) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      prev
    case Nil{} Con{y, t}:
      val.cmp.then(prev, LT{})
    case Con{x, t} Nil{}:
      val.cmp.then(prev, GT{})
    case Con{+x, xt} Con{+y, yt}:
      val.cmp.go(xt, yt, val.cmp.then(prev, U32.cmp(x, y)))

def val.bytes.cmp(xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  val.cmp.go(xs, ys, EQ{})

# the comparison of a with b, b converted to a's type
def AmlValue.compare(+wide: Bool, a: AmlValue, +b: AmlValue) -> Result<&2, &2, E.AcpiError, Cmp>:
  match a:
    case AmlInt{x}:
      Result.map(&2, &2, E.AcpiError, W.W64, Cmp, y => W.W64.cmp(AmlInt.fit(wide, x), y), AmlValue.to_int(wide, b))
    case AmlStr{s}:
      Result.map(&2, &2, E.AcpiError, B.Octets, Cmp, t => val.bytes.cmp(B.Octets.to_list(s), B.Octets.to_list(t)), AmlValue.to_str(wide, b))
    case AmlBuf{s}:
      Result.map(&2, &2, E.AcpiError, B.Octets, Cmp, t => val.bytes.cmp(B.Octets.to_list(s), B.Octets.to_list(t)), AmlValue.to_buf(wide, b))
    case _:
      Fail{E.AcpiAmlBadType{"cannot compare"}}

# Text, for tests and debugging: integers in hex ("0x1f"), strings quoted,
# buffers as "buf[01 ab]", packages as "{a, b}", references as "ref"

def val.lz.z(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, +t}:
      Bool.and(U32.is_eq(h, 48), Bool.not(List.is_empty(&2, U32, t)))

# leading zeros dropped (one kept); z: the head is a zero with more after it
def val.lz(xs: List<&2, U32>, still: Bool, z: Bool) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, +t}:
      match still:
        case True{}:
          match z:
            case True{}:
              val.lz(t, True{}, val.lz.z(t))
            case False{}:
              Con{h, val.lz(t, False{}, False{})}
        case False{}:
          Con{h, val.lz(t, False{}, False{})}

def val.lower.pick(up: Bool, +h: U32) -> U32:
  match up:
    case True{}:
      U32.add(h, 32)
    case False{}:
      h

def val.lower(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{val.lower.pick(U32.is_le(65, h), h), val.lower(t)}

def AmlValue.show_int(+x: W.W64) -> String:
  +ds = val.hex.text(16n, x, Nil{})
  "0x" ++ B.to_string(val.lower(val.lz(ds, True{}, val.lz.z(ds))))

def val.sep(first: Bool) -> String:
  match first:
    case True{}:
      ""
    case False{}:
      ", "

def val.ref.show(l: AmlLoc) -> String:
  match l:
    case AmlLName{p}:
      "ref " ++ p
    case AmlLLocal{i}:
      "ref Local" ++ Nat.show(i)
    case AmlLArg{i}:
      "ref Arg" ++ Nat.show(i)
    case AmlLIndex{b, i}:
      "ref index " ++ Nat.show(i)
    case AmlLElem{v, i}:
      "ref element " ++ Nat.show(i)
    case AmlLDebug{}:
      "ref Debug"
    case AmlLNone{}:
      "ref none"

def val.show.list(vs: List<&2, AmlValue>, +first: Bool) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{v, rest}:
      match v:
        case AmlPkg{xs}:
          val.sep(first) ++ "{" ++ val.show.list(xs, True{}) ++ "}" ++ val.show.list(rest, False{})
        case AmlUninit{}:
          val.sep(first) ++ "uninit" ++ val.show.list(rest, False{})
        case AmlInt{x}:
          val.sep(first) ++ AmlValue.show_int(x) ++ val.show.list(rest, False{})
        case AmlStr{t}:
          val.sep(first) ++ "\"" ++ B.Octets.to_string(t) ++ "\"" ++ val.show.list(rest, False{})
        case AmlBuf{b}:
          val.sep(first) ++ "buf[" ++ B.to_string(val.lower(val.buf.text(B.Octets.to_list(b), True{}))) ++ "]" ++ val.show.list(rest, False{})
        case AmlRef{l}:
          val.sep(first) ++ val.ref.show(l) ++ val.show.list(rest, False{})
        case AmlObj{p, k}:
          val.sep(first) ++ "object " ++ p ++ val.show.list(rest, False{})

def AmlValue.show(v: AmlValue) -> String:
  val.show.list([v], True{})
