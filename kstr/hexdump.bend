# bend-osdev-kstr, hex dump lines in the layout of the kernel's
# hex_dump_to_buffer and print_hex_dump, as their documentation describes:
# up to rowsize bytes (16 or 32) a line, as groups of groupsize bytes (1, 2,
# 4 or 8; 1 when the line's length is not a multiple of it) in lower-case
# hex, separated by spaces, each group printed as one number (little-endian
# by default, as on the machines the kernel documents); then, if asked, the
# bytes as text (printable ASCII as itself, anything else as a dot) starting
# at column rowsize * 2 + rowsize / groupsize + 1, so that the text lines up
# on a short last line. print_hex_dump puts an offset "%.8x: " before each
# line. The documentation's example (16 bytes, groups of 1, with text):
#   40 41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f  @ABCDEFGHIJKLMNO
import Base
import ../bytes/bytes.bend as B
import ./format.bend as F

type KDump is Data:
  KDump{rowsize: Nat, groupsize: Nat, ascii: Bool, little: Bool}

type KDumpPrefix is Data:
  KDumpNone{}
  KDumpOffset{}

# 16 bytes a line, single bytes, with the text
def KDump.default() -> KDump:
  KDump{16n, 1n, True{}, True{}}

def kdump.hex2(+b: U32) -> List<&2, U32>:
  [F.KStr.hex_digit(U32.and(15, U32.shrn(b, 4n))), F.KStr.hex_digit(U32.and(15, b))]

def kdump.hexes(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      B.append(kdump.hex2(h), kdump.hexes(t))

def kdump.group.pick(little: Bool, +xs: List<&2, U32>) -> List<&2, U32>:
  match little:
    case True{}:
      kdump.hexes(B.rev(xs))
    case False{}:
      kdump.hexes(xs)

def kdump.sep(first: Bool, rest: List<&2, U32>) -> List<&2, U32>:
  match first:
    case True{}:
      rest
    case False{}:
      Con{32, rest}

# the groups of g bytes, each in hex, separated by spaces
def kdump.groups(n: Nat, +xs: List<&2, U32>, +g: Nat, +little: Bool, first: Bool) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          kdump.sep(first, B.append(kdump.group.pick(little, B.take(g, Con{h, t})), kdump.groups(k, B.drop(g, Con{h, t}), g, little, False{})))

def kdump.printable.pick(ok: Bool, c: U32) -> U32:
  match ok:
    case True{}:
      c
    case False{}:
      46

def kdump.printable(+c: U32) -> U32:
  kdump.printable.pick(Bool.and(U32.is_le(32, c), U32.is_le(c, 126)), c)

def kdump.text(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{kdump.printable(h), kdump.text(t)}

def kdump.spaces(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+k:
      kdump.spaces(k, Con{32, acc})

def kdump.group.ok(+g: Nat, +len: Nat) -> Bool:
  Bool.and(Bool.or(Bool.or(Nat.is_eq(g, 1n), Nat.is_eq(g, 2n)), Bool.or(Nat.is_eq(g, 4n), Nat.is_eq(g, 8n))), Nat.is_eq(Nat.mod(len, g), 0n))

def kdump.pick.nat(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def kdump.with_text(ascii: Bool, +col: Nat, +hex: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match ascii:
    case True{}:
      B.append(hex, kdump.spaces(Nat.sub(col, B.len(hex)), kdump.text(xs)))
    case False{}:
      hex

def kdump.line(f: KDump, +xs: List<&2, U32>) -> List<&2, U32>:
  match f:
    case KDump{rs, +gs, ascii, +little}:
      +row = kdump.pick.nat(Nat.is_eq(rs, 32n), 32n, 16n)
      +ys = B.take(row, xs)
      +len = B.len(ys)
      +g = kdump.pick.nat(kdump.group.ok(gs, len), gs, 1n)
      kdump.with_text(ascii, Nat.add(Nat.add(Nat.mul(row, 2n), Nat.div(row, g)), 1n), kdump.groups(len, ys, g, little, True{}), ys)

def kdump.line.pick(empty: Bool, f: KDump, +xs: List<&2, U32>) -> List<&2, U32>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      kdump.line(f, xs)

def kdump.line.start(f: KDump, +xs: List<&2, U32>) -> List<&2, U32>:
  kdump.line.pick(B.list_eq(xs, Nil{}), f, xs)

# one line for the first rowsize bytes of o (hex_dump_to_buffer); an empty
# o gives an empty line
def KStr.hex_dump_line(f: KDump, o: B.Octets) -> B.Octets:
  B.Octets.of_list(kdump.line.start(f, B.Octets.to_list(o)))

def kdump.prefix(p: KDumpPrefix, +off: Nat) -> List<&2, U32>:
  match p:
    case KDumpNone{}:
      Nil{}
    case KDumpOffset{}:
      B.append(B.Octets.to_list(F.KStr.hex32(U32.from_nat(off))), [58, 32])

def kdump.rowsize(f: KDump) -> Nat:
  match f:
    case KDump{rs, gs, ascii, little}:
      kdump.pick.nat(Nat.is_eq(rs, 32n), 32n, 16n)

def kdump.lines(n: Nat, +f: KDump, +p: KDumpPrefix, +row: Nat, +xs: List<&2, U32>, +off: Nat) -> List<&2, B.Octets>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{B.Octets.of_list(B.append(kdump.prefix(p, off), kdump.line(f, Con{h, t}))), kdump.lines(k, f, p, row, B.drop(row, Con{h, t}), Nat.add(off, row))}

# every line of o, each with the prefix (print_hex_dump)
def KStr.hex_dump(+f: KDump, +p: KDumpPrefix, o: B.Octets) -> List<&2, B.Octets>:
  +xs = B.Octets.to_list(o)
  kdump.lines(B.len(xs), f, p, kdump.rowsize(f), xs, 0n)
