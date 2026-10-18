# bend-osdev-acpi, aml_term.bend: building AML (ACPI 6.5, chapter 20, AML
# Specification): terms and their encoding, with a constructor for each
# ASL operator this package uses (chapter 19 names them), so that a
# definition block can be written in Bend:
#
#   AmlT.scope("\\_SB", [AmlT.device("PCI0", [
#     AmlT.name("_HID", AmlT.eisaid("PNP0A03")),
#     AmlT.method("_STA", 0n, False{}, [AmlT.ret(AmlT.int32(15))])])])
#
# A term is a number, a string, raw bytes, an opcode with operands, or a
# package (an opcode, then a PkgLength covering a head and a body), which
# is enough for every encoding in chapter 20: the constructors below fill
# them in. Operands are lists, so that encoding is one structural
# recursion.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./aml_pkglength.bend as K
import ./aml_name.bend as N

type AmlTerm is Data:
  # an integer, in its shortest encoding: ZeroOp, OneOp, OnesOp (all 64
  # bits set), or the Byte, Word, DWord or QWord prefix
  AmlTInt{v: W.W64}
  # a String (AsciiCharList, then the NUL the encoder adds)
  AmlTStr{s: B.Octets}
  # bytes as they are: a NameString, Local0, Debug, ...
  AmlTRaw{bytes: B.Octets}
  # an opcode (or a NameString, for a method call) followed by operands
  AmlTOp{code: B.Octets, args: List<&2, AmlTerm>}
  # an opcode, then a PkgLength covering head and body
  AmlTPkg{code: B.Octets, head: B.Octets, body: List<&2, AmlTerm>}

# Field elements (20.2.5.2, FieldList)
type AmlFieldElem is Data:
  # NamedField: a NameSeg and its width in bits
  AmlFNamed{seg: B.Octets, bits: U32}
  # ReservedField (ASL Offset): bits skipped
  AmlFReserved{bits: U32}
  # AccessField: access type and attribute from here on
  AmlFAccess{access_type: U32, attrib: U32}

# Encoding

def tm.b(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(xs)

def tm.int.pick(z: Bool, o: Bool, m: Bool, b8: Bool, b16: Bool, b32: Bool, +v: W.W64) -> B.Octets:
  match z:
    case True{}:
      tm.b([0])
    case False{}:
      match o:
        case True{}:
          tm.b([1])
        case False{}:
          match m:
            case True{}:
              tm.b([255])
            case False{}:
              match b8:
                case True{}:
                  tm.b([10, W.W64.lo(v)])
                case False{}:
                  match b16:
                    case True{}:
                      B.Octets.append(tm.b([11]), B.Octets.le16(W.W64.lo(v)))
                    case False{}:
                      match b32:
                        case True{}:
                          B.Octets.append(tm.b([12]), B.Octets.le32(W.W64.lo(v)))
                        case False{}:
                          B.Octets.append(tm.b([14]), B.Octets.le64(v))

def tm.int(+v: W.W64) -> B.Octets:
  +lo = W.W64.lo(v)
  +small = U32.is_eq(W.W64.hi(v), 0)
  tm.int.pick(W.W64.is_zero(v), W.W64.is_eq(v, W.W64.one()), W.W64.is_eq(v, W.W64.max()), Bool.and(small, U32.is_lt(lo, 256)), Bool.and(small, U32.is_lt(lo, 65536)), small, v)

def tm.str(+s: B.Octets) -> B.Octets:
  B.Octets.concat([tm.b([13]), s, tm.b([0])])

# a term list; every term's operands and body are sublists, so this is one
# structural recursion
def AmlT.encode(ts: List<&2, AmlTerm>) -> B.Octets:
  match ts:
    case Nil{}:
      B.Octets.empty()
    case Con{t, rest}:
      match t:
        case AmlTInt{v}:
          B.Octets.append(tm.int(v), AmlT.encode(rest))
        case AmlTStr{s}:
          B.Octets.append(tm.str(s), AmlT.encode(rest))
        case AmlTRaw{bs}:
          B.Octets.append(bs, AmlT.encode(rest))
        case AmlTOp{c, args}:
          B.Octets.concat([c, AmlT.encode(args), AmlT.encode(rest)])
        case AmlTPkg{c, h, body}:
          B.Octets.concat([c, K.AmlPkgLength.wrap(B.Octets.append(h, AmlT.encode(body))), AmlT.encode(rest)])

def AmlT.encode1(t: AmlTerm) -> B.Octets:
  AmlT.encode([t])

def tm.field.enc(es: List<&2, AmlFieldElem>) -> B.Octets:
  match es:
    case Nil{}:
      B.Octets.empty()
    case Con{AmlFNamed{s, n}, t}:
      B.Octets.concat([s, K.AmlPkgLength.encode(n), tm.field.enc(t)])
    case Con{AmlFReserved{n}, t}:
      B.Octets.concat([tm.b([0]), K.AmlPkgLength.encode(n), tm.field.enc(t)])
    case Con{AmlFAccess{a, b}, t}:
      B.Octets.append(tm.b([1, a, b]), tm.field.enc(t))

# Data objects (20.2.3)

def AmlT.int(v: W.W64) -> AmlTerm:
  AmlTInt{v}

def AmlT.int32(v: U32) -> AmlTerm:
  AmlTInt{W.W64.from_u32(v)}

def AmlT.zero() -> AmlTerm:
  AmlTInt{W.W64.zero()}

def AmlT.one() -> AmlTerm:
  AmlTInt{W.W64.one()}

def AmlT.ones() -> AmlTerm:
  AmlTRaw{tm.b([255])}

def AmlT.str(s: String) -> AmlTerm:
  AmlTStr{B.Octets.of_string(s)}

def AmlT.revision() -> AmlTerm:
  AmlTRaw{tm.b([91, 48])}

# a Buffer of size bytes (a term), initialised from bytes
def AmlT.buffer(size: AmlTerm, bytes: B.Octets) -> AmlTerm:
  AmlTPkg{tm.b([17]), B.Octets.empty(), [size, AmlTRaw{bytes}]}

# a Buffer holding exactly these bytes
def AmlT.buf(+bytes: B.Octets) -> AmlTerm:
  AmlT.buffer(AmlT.int(W.W64.from_nat(B.Octets.len(bytes))), bytes)

def AmlT.package(+elems: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([18]), tm.b([U32.from_nat(List.length(&2, AmlTerm, elems))]), elems}

def AmlT.var_package(count: AmlTerm, elems: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([19]), B.Octets.empty(), Con{count, elems}}

# EISAID("PNP0A03") (chapter 19, EISAID): three letters of five bits each and four hex
# digits, stored most significant byte first, as a DWord
def tm.hex.pick(digit: Bool, upper: Bool, +c: U32) -> U32:
  match digit:
    case True{}:
      U32.sub(c, 48)
    case False{}:
      match upper:
        case True{}:
          U32.and(U32.sub(c, 55), 15)
        case False{}:
          U32.and(U32.sub(c, 87), 15)

def tm.hex(+c: U32) -> U32:
  tm.hex.pick(U32.is_le(c, 57), U32.is_le(65, c), c)

def tm.eisa(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{a, Con{b, Con{c, Con{d0, Con{d1, Con{d2, Con{d3, t}}}}}}}:
      +hi = U32.or(U32.shln(U32.and(U32.sub(a, 64), 31), 10n), U32.or(U32.shln(U32.and(U32.sub(b, 64), 31), 5n), U32.and(U32.sub(c, 64), 31)))
      +lo = U32.or(U32.shln(tm.hex(d0), 12n), U32.or(U32.shln(tm.hex(d1), 8n), U32.or(U32.shln(tm.hex(d2), 4n), tm.hex(d3))))
      U32.or(U32.or(U32.shrn(hi, 8n), U32.shln(U32.and(hi, 255), 8n)), U32.or(U32.shln(U32.shrn(lo, 8n), 16n), U32.shln(U32.and(lo, 255), 24n)))
    case _:
      0

def AmlT.eisaid_value(s: String) -> U32:
  tm.eisa(B.of_string(s))

def AmlT.eisaid(s: String) -> AmlTerm:
  AmlT.int32(AmlT.eisaid_value(s))

# Names (20.2.2): a name as an operand, a method call, Local and Arg

def tm.name(s: String) -> B.Octets:
  N.AmlName.encode(N.AmlName.of_text(s))

# a name as a term (its value, a reference to it in a package, or a call
# of a method that takes no arguments)
def AmlT.nm(s: String) -> AmlTerm:
  AmlTRaw{tm.name(s)}

def AmlT.call(s: String, args: List<&2, AmlTerm>) -> AmlTerm:
  AmlTOp{tm.name(s), args}

def AmlT.local(i: U32) -> AmlTerm:
  AmlTRaw{tm.b([U32.add(96, U32.and(i, 7))])}

def AmlT.arg(i: U32) -> AmlTerm:
  AmlTRaw{tm.b([U32.add(104, U32.min(i, 6))])}

def AmlT.debug() -> AmlTerm:
  AmlTRaw{tm.b([91, 49])}

# NullName, the Target that discards a result
def AmlT.none() -> AmlTerm:
  AmlTRaw{tm.b([0])}

# Named objects and scopes (20.2.5.1 to 20.2.5.2)

def AmlT.name(s: String, v: AmlTerm) -> AmlTerm:
  AmlTOp{B.Octets.append(tm.b([8]), tm.name(s)), [v]}

def AmlT.scope(s: String, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([16]), tm.name(s), body}

def AmlT.device(s: String, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([91, 130]), tm.name(s), body}

def tm.bit(b: Bool, v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

# a method of nargs arguments (0 to 7), serialized or not, sync level 0
def AmlT.method(s: String, nargs: Nat, ser: Bool, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([20]), B.Octets.append(tm.name(s), tm.b([U32.or(U32.and(U32.from_nat(nargs), 7), tm.bit(ser, 8))])), body}

def AmlT.processor(s: String, id: U32, pblk: U32, plen: U32, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([91, 131]), B.Octets.concat([tm.name(s), tm.b([id]), B.Octets.le32(pblk), tm.b([plen])]), body}

def AmlT.power_resource(s: String, level: U32, order: U32, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([91, 132]), B.Octets.concat([tm.name(s), tm.b([level]), B.Octets.le16(order)]), body}

def AmlT.thermal_zone(s: String, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([91, 133]), tm.name(s), body}

# OperationRegion(name, space, offset, length): space 0 SystemMemory,
# 1 SystemIO, 2 PCI_Config, 3 EmbeddedControl, ...
def AmlT.region(s: String, space: U32, off: AmlTerm, len: AmlTerm) -> AmlTerm:
  AmlTOp{B.Octets.concat([tm.b([91, 128]), tm.name(s), tm.b([space])]), [off, len]}

# FieldFlags (20.2.5.2): access type 0 AnyAcc, 1 ByteAcc, 2 WordAcc,
# 3 DWordAcc, 4 QWordAcc, 5 BufferAcc; lock; update rule 0 Preserve,
# 1 WriteAsOnes, 2 WriteAsZeros
def AmlT.field_flags(access: U32, lock: Bool, update: U32) -> U32:
  U32.or(U32.and(access, 15), U32.or(tm.bit(lock, 16), U32.shln(U32.and(update, 3), 5n)))

def AmlT.field(region: String, flags: U32, es: List<&2, AmlFieldElem>) -> AmlTerm:
  AmlTPkg{tm.b([91, 129]), B.Octets.append(tm.name(region), tm.b([flags])), [AmlTRaw{tm.field.enc(es)}]}

def AmlT.index_field(index: String, data: String, flags: U32, es: List<&2, AmlFieldElem>) -> AmlTerm:
  AmlTPkg{tm.b([91, 134]), B.Octets.concat([tm.name(index), tm.name(data), tm.b([flags])]), [AmlTRaw{tm.field.enc(es)}]}

def AmlT.fnamed(s: String, bits: U32) -> AmlFieldElem:
  AmlFNamed{N.AmlName.seg(s), bits}

def AmlT.mutex(s: String, sync: U32) -> AmlTerm:
  AmlTRaw{B.Octets.concat([tm.b([91, 1]), tm.name(s), tm.b([sync])])}

def AmlT.event(s: String) -> AmlTerm:
  AmlTRaw{B.Octets.append(tm.b([91, 2]), tm.name(s))}

def AmlT.alias(src: String, dst: String) -> AmlTerm:
  AmlTRaw{B.Octets.concat([tm.b([6]), tm.name(src), tm.name(dst)])}

def AmlT.external(s: String, kind: U32, nargs: U32) -> AmlTerm:
  AmlTRaw{B.Octets.concat([tm.b([21]), tm.name(s), tm.b([kind, nargs])])}

# CreateBitField, CreateByteField, CreateWordField, CreateDWordField,
# CreateQWordField (op 141, 140, 139, 138, 143): a field of a buffer
def AmlT.create_field(op: U32, src: AmlTerm, index: AmlTerm, s: String) -> AmlTerm:
  AmlTOp{tm.b([op]), [src, index, AmlTRaw{tm.name(s)}]}

def AmlT.create_dword_field(src: AmlTerm, index: AmlTerm, s: String) -> AmlTerm:
  AmlT.create_field(138, src, index, s)

# Statements (20.2.5.3)

def AmlT.if_(pred: AmlTerm, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([160]), B.Octets.empty(), Con{pred, body}}

def AmlT.if_else(pred: AmlTerm, body: List<&2, AmlTerm>, els: List<&2, AmlTerm>) -> AmlTerm:
  AmlTOp{B.Octets.empty(), [AmlT.if_(pred, body), AmlTPkg{tm.b([161]), B.Octets.empty(), els}]}

def AmlT.while_(pred: AmlTerm, body: List<&2, AmlTerm>) -> AmlTerm:
  AmlTPkg{tm.b([162]), B.Octets.empty(), Con{pred, body}}

def AmlT.ret(v: AmlTerm) -> AmlTerm:
  AmlTOp{tm.b([164]), [v]}

def AmlT.brk() -> AmlTerm:
  AmlTRaw{tm.b([165])}

def AmlT.cont() -> AmlTerm:
  AmlTRaw{tm.b([159])}

def AmlT.noop() -> AmlTerm:
  AmlTRaw{tm.b([163])}

def AmlT.notify(obj: AmlTerm, v: AmlTerm) -> AmlTerm:
  AmlTOp{tm.b([134]), [obj, v]}

def AmlT.sleep(ms: AmlTerm) -> AmlTerm:
  AmlTOp{tm.b([91, 34]), [ms]}

def AmlT.stall(us: AmlTerm) -> AmlTerm:
  AmlTOp{tm.b([91, 33]), [us]}

def AmlT.acquire(m: AmlTerm, timeout: U32) -> AmlTerm:
  AmlTOp{tm.b([91, 35]), [m, AmlTRaw{B.Octets.le16(timeout)}]}

def AmlT.release(m: AmlTerm) -> AmlTerm:
  AmlTOp{tm.b([91, 39]), [m]}

# Expressions (20.2.5.4): opcode, operands, then the Target (a name, a
# Local, Debug, or AmlT.none())

def AmlT.op(op: U32, args: List<&2, AmlTerm>) -> AmlTerm:
  AmlTOp{tm.b([op]), args}

def AmlT.store(v: AmlTerm, target: AmlTerm) -> AmlTerm:
  AmlT.op(112, [v, target])

def AmlT.copy_object(v: AmlTerm, target: AmlTerm) -> AmlTerm:
  AmlT.op(157, [v, target])

def AmlT.add(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(114, [a, b, t])

def AmlT.subtract(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(116, [a, b, t])

def AmlT.multiply(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(119, [a, b, t])

# Divide(dividend, divisor, remainder target, quotient target)
def AmlT.divide(a: AmlTerm, b: AmlTerm, rem: AmlTerm, quo: AmlTerm) -> AmlTerm:
  AmlT.op(120, [a, b, rem, quo])

def AmlT.mod(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(133, [a, b, t])

def AmlT.shift_left(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(121, [a, b, t])

def AmlT.shift_right(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(122, [a, b, t])

def AmlT.and(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(123, [a, b, t])

def AmlT.nand(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(124, [a, b, t])

def AmlT.or(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(125, [a, b, t])

def AmlT.nor(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(126, [a, b, t])

def AmlT.xor(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(127, [a, b, t])

def AmlT.not(a: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(128, [a, t])

def AmlT.find_set_left_bit(a: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(129, [a, t])

def AmlT.find_set_right_bit(a: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(130, [a, t])

def AmlT.increment(t: AmlTerm) -> AmlTerm:
  AmlT.op(117, [t])

def AmlT.decrement(t: AmlTerm) -> AmlTerm:
  AmlT.op(118, [t])

def AmlT.concat(a: AmlTerm, b: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(115, [a, b, t])

def AmlT.land(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.op(144, [a, b])

def AmlT.lor(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.op(145, [a, b])

def AmlT.lnot(a: AmlTerm) -> AmlTerm:
  AmlT.op(146, [a])

def AmlT.lequal(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.op(147, [a, b])

def AmlT.lgreater(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.op(148, [a, b])

def AmlT.lless(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.op(149, [a, b])

# LNotEqual, LLessEqual, LGreaterEqual: LNot of LEqual, LGreater, LLess
def AmlT.lnot_equal(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.lnot(AmlT.lequal(a, b))

def AmlT.lless_equal(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.lnot(AmlT.lgreater(a, b))

def AmlT.lgreater_equal(a: AmlTerm, b: AmlTerm) -> AmlTerm:
  AmlT.lnot(AmlT.lless(a, b))

# References

def AmlT.ref_of(a: AmlTerm) -> AmlTerm:
  AmlT.op(113, [a])

def AmlT.deref_of(a: AmlTerm) -> AmlTerm:
  AmlT.op(131, [a])

def AmlT.index(a: AmlTerm, i: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(136, [a, i, t])

def AmlT.cond_ref_of(a: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlTOp{tm.b([91, 18]), [a, t]}

def AmlT.size_of(a: AmlTerm) -> AmlTerm:
  AmlT.op(135, [a])

def AmlT.object_type(a: AmlTerm) -> AmlTerm:
  AmlT.op(142, [a])

# Conversions

def AmlT.to_integer(a: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(153, [a, t])

def AmlT.to_buffer(a: AmlTerm, t: AmlTerm) -> AmlTerm:
  AmlT.op(150, [a, t])
