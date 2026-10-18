# bend-osdev-acpi, aml_resource.bend: resource data types (ACPI 6.5,
# section 6.4), what _CRS, _PRS and _SRS buffers hold. A resource template
# is a run of descriptors ending with an End Tag:
#
#   small (bit 7 clear): a byte holding the type (bits 6-3) and the length
#     (bits 2-0), then that many bytes. Read here: IRQ (type 4, 6.4.2.1),
#     DMA (5, 6.4.2.2), I/O port (8, 6.4.2.5), fixed I/O (9, 6.4.2.6),
#     End Tag (15)
#   large (bit 7 set): the type in bits 6-0, a 2-byte length, then that
#     many bytes. Read here: 32-bit memory range (5, 6.4.3.3), 32-bit fixed
#     memory range (6, 6.4.3.4), DWord, Word and QWord address space (7, 8,
#     10: 6.4.3.5.1-3), extended interrupt (9, 6.4.3.6)
#
# Every other descriptor is kept as AmlROther with its tag and bytes.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./fields.bend as F

type AmlResource is Data:
  # IRQ: the mask of IRQs 0-15, and the flags byte (0x01 if absent: edge,
  # active high)
  AmlRIrq{mask: U32, flags: U32}
  AmlRDma{mask: U32, flags: U32}
  # I/O port: decode (1: 16-bit), minimum and maximum base, alignment,
  # length
  AmlRIo{decode: U32, min: U32, max: U32, align: U32, len: U32}
  AmlRFixedIo{base: U32, len: U32}
  # 32-bit memory: write status (1: writable), minimum and maximum base,
  # alignment, length
  AmlRMem32{writable: U32, min: U32, max: U32, align: U32, len: U32}
  AmlRMem32Fixed{writable: U32, base: U32, len: U32}
  # an address space descriptor (DWord, Word or QWord: width 32, 16, 64):
  # resource type (0 memory, 1 I/O, 2 bus number), general flags, type
  # specific flags, then granularity, minimum, maximum, translation offset
  # and length, in an address-range record
  AmlRAddr{width: U32, kind: U32, flags: U32, tflags: U32, range: AmlRange}
  # extended interrupt: flags (bit 0 consumer, 1 edge, 2 active low,
  # 3 shared, 4 wake capable) and the interrupt numbers
  AmlRExtIrq{flags: U32, irqs: List<&2, U32>}
  AmlROther{tag: U32, data: B.Octets}

type AmlRange is Data:
  AmlRange{gran: W.W64, min: W.W64, max: W.W64, tra: W.W64, len: W.W64}

# Reading one descriptor; d: its bytes after the tag (and, for a large
# one, after its length)

def res.u.go(+w: Nat, +d: B.Octets, +i: Nat) -> W.W64:
  match w:
    case 2n:
      W.W64.from_u32(F.AcpiF.u16(d, i))
    case 4n:
      W.W64.from_u32(F.AcpiF.u32(d, i))
    case _:
      F.AcpiF.u64(d, i)

def res.u(+d: B.Octets, +i: Nat, +w: Nat) -> W.W64:
  res.u.go(w, d, i)

# an address space descriptor whose fields are w bytes wide
def res.addr(+bits: U32, +w: Nat, +d: B.Octets) -> AmlResource:
  AmlRAddr{bits, F.AcpiF.u8(d, 0n), F.AcpiF.u8(d, 1n), F.AcpiF.u8(d, 2n), AmlRange{res.u(d, 3n, w), res.u(d, Nat.add(3n, w), w), res.u(d, Nat.add(3n, Nat.mul(2n, w)), w), res.u(d, Nat.add(3n, Nat.mul(3n, w)), w), res.u(d, Nat.add(3n, Nat.mul(4n, w)), w)}}

def res.irqs(n: Nat, +d: B.Octets, +i: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{F.AcpiF.u32(d, i), res.irqs(p, d, Nat.add(i, 4n))}

def res.irq.flags.pick(has: Bool, +d: B.Octets) -> U32:
  match has:
    case True{}:
      F.AcpiF.u8(d, 2n)
    case False{}:
      1

def res.irq.flags(+d: B.Octets) -> U32:
  res.irq.flags.pick(Nat.is_le(3n, B.Octets.len(d)), d)

def res.small(+t: Nat, +d: B.Octets) -> AmlResource:
  match t:
    case 4n:
      AmlRIrq{F.AcpiF.u16(d, 0n), res.irq.flags(d)}
    case 5n:
      AmlRDma{F.AcpiF.u8(d, 0n), F.AcpiF.u8(d, 1n)}
    case 8n:
      AmlRIo{F.AcpiF.u8(d, 0n), F.AcpiF.u16(d, 1n), F.AcpiF.u16(d, 3n), F.AcpiF.u8(d, 5n), F.AcpiF.u8(d, 6n)}
    case 9n:
      AmlRFixedIo{F.AcpiF.u16(d, 0n), F.AcpiF.u8(d, 2n)}
    case _:
      AmlROther{U32.shln(U32.from_nat(t), 3n), d}

# the minimum lengths of the descriptors read
def res.min.small(+t: Nat) -> Nat:
  match t:
    case 4n:
      2n
    case 5n:
      2n
    case 8n:
      7n
    case 9n:
      3n
    case _:
      0n

def res.min.large(+t: Nat) -> Nat:
  match t:
    case 5n:
      17n
    case 6n:
      9n
    case 7n:
      23n
    case 8n:
      13n
    case 10n:
      43n
    case 9n:
      2n
    case _:
      0n

# The walk: one descriptor per step

type AmlResNext is Data:
  AmlResMore{res: AmlResource, rest: B.Octets}
  AmlResEnd{}

def res.small.end(end: Bool, +t: Nat, +n: Nat, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  match end:
    case True{}:
      Done{AmlResEnd{}}
    case False{}:
      Done{AmlResMore{res.small(t, B.Octets.take(n, o)), B.Octets.drop(n, o)}}

def res.small.fit(ok: Bool, +t: Nat, +n: Nat, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  match ok:
    case False{}:
      Fail{E.AcpiBadEntry{0n, U32.from_nat(t)}}
    case True{}:
      res.small.end(Nat.is_eq(t, 15n), t, n, o)

def res.small.go(+t: Nat, +n: Nat, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  res.small.fit(Bool.and(Nat.is_le(n, B.Octets.len(o)), Nat.is_le(res.min.small(t), n)), t, n, o)

# Text

def res.show.irqs(xs: List<&2, U32>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.show(x), res.show.irqs(t)}

def AmlResource.show(r: AmlResource) -> String:
  match r:
    case AmlRIrq{m, f}:
      "irq mask " ++ U32.show(m) ++ " flags " ++ U32.show(f)
    case AmlRDma{m, f}:
      "dma mask " ++ U32.show(m) ++ " flags " ++ U32.show(f)
    case AmlRIo{dc, mn, mx, al, l}:
      "io " ++ U32.show(mn) ++ "-" ++ U32.show(mx) ++ " align " ++ U32.show(al) ++ " len " ++ U32.show(l)
    case AmlRFixedIo{b, l}:
      "fixed io " ++ U32.show(b) ++ " len " ++ U32.show(l)
    case AmlRMem32{wr, mn, mx, al, l}:
      "mem32 " ++ U32.show(mn) ++ "-" ++ U32.show(mx) ++ " len " ++ U32.show(l)
    case AmlRMem32Fixed{wr, b, l}:
      "mem32 fixed " ++ U32.show(b) ++ " len " ++ U32.show(l)
    case AmlRAddr{bits, k, f, tf, AmlRange{g, mn, mx, t, l}}:
      "addr" ++ U32.show(bits) ++ " type " ++ U32.show(k) ++ " " ++ W.W64.show_hex(mn) ++ "-" ++ W.W64.show_hex(mx) ++ " len " ++ W.W64.show_hex(l)
    case AmlRExtIrq{f, irqs}:
      "extirq flags " ++ U32.show(f) ++ " " ++ String.join(res.show.irqs(irqs), ",")
    case AmlROther{t, d}:
      "other " ++ U32.show(t) ++ " " ++ B.Octets.hex(d)

# Writing: each descriptor as bytes, and a template (descriptors, then an
# End Tag whose checksum byte is 0, which section 6.4.2 accepts)

def res.b(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(xs)

def res.w.go(+n: Nat, +v: W.W64) -> B.Octets:
  match n:
    case 16n:
      B.Octets.le16(W.W64.lo(v))
    case 32n:
      B.Octets.le32(W.W64.lo(v))
    case _:
      B.Octets.le64(v)

def res.w(+width: U32, +v: W.W64) -> B.Octets:
  res.w.go(U32.to_nat(width), v)

def res.lenc(+t: U32, +d: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.append(res.b([t]), B.Octets.le16(U32.from_nat(B.Octets.len(d)))), d)

def res.large(+t: Nat, +d: B.Octets) -> AmlResource:
  match t:
    case 5n:
      AmlRMem32{F.AcpiF.u8(d, 0n), F.AcpiF.u32(d, 1n), F.AcpiF.u32(d, 5n), F.AcpiF.u32(d, 9n), F.AcpiF.u32(d, 13n)}
    case 6n:
      AmlRMem32Fixed{F.AcpiF.u8(d, 0n), F.AcpiF.u32(d, 1n), F.AcpiF.u32(d, 5n)}
    case 7n:
      res.addr(32, 4n, d)
    case 8n:
      res.addr(16, 2n, d)
    case 10n:
      res.addr(64, 8n, d)
    case 9n:
      AmlRExtIrq{F.AcpiF.u8(d, 0n), res.irqs(U32.to_nat(F.AcpiF.u8(d, 1n)), d, 2n)}
    case _:
      AmlROther{U32.add(128, U32.from_nat(t)), d}

def res.large.fit(ok: Bool, +t: Nat, +n: Nat, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  match ok:
    case False{}:
      Fail{E.AcpiBadEntry{0n, U32.add(128, U32.from_nat(t))}}
    case True{}:
      Done{AmlResMore{res.large(t, B.Octets.take(n, o)), B.Octets.drop(n, o)}}

def res.large.go(+t: Nat, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  +n = U32.to_nat(F.AcpiF.u16(o, 0n))
  res.large.fit(Bool.and(Nat.is_le(Nat.add(2n, n), B.Octets.len(o)), Nat.is_le(res.min.large(t), n)), t, n, B.Octets.drop(2n, o))

def res.tag.pick(small: Bool, +b: U32, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  match small:
    case True{}:
      res.small.go(U32.to_nat(U32.and(U32.shrn(b, 3n), 15)), U32.to_nat(U32.and(b, 7)), o)
    case False{}:
      res.large.go(U32.to_nat(U32.and(b, 127)), o)

def res.tag(+b: U32, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  res.tag.pick(U32.is_eq(U32.and(b, 128), 0), b, o)

def res.step.pick(m: Maybe<&2, U32>, +o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  match m:
    case None{}:
      Done{AmlResEnd{}}
    case Some{+b}:
      res.tag(b, B.Octets.drop(1n, o))

def res.step(+o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlResNext>:
  res.step.pick(B.Octets.at(o, 0n), o)

def res.loop(fuel: Nat, r: Result<&2, &2, E.AcpiError, AmlResNext>, acc: List<&2, AmlResource>) -> Result<&2, &2, E.AcpiError, List<&2, AmlResource>>:
  match fuel:
    case 0n:
      Done{List.reverse(&2, AmlResource, acc)}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{AmlResEnd{}}:
          Done{List.reverse(&2, AmlResource, acc)}
        case Done{AmlResMore{x, +rest}}:
          res.loop(p, res.step(rest), Con{x, acc})

# the descriptors of a resource template, up to its End Tag (or its end);
# AcpiBadEntry for a descriptor shorter than its type needs or that runs
# past the buffer
def AmlResource.parse(+o: B.Octets) -> Result<&2, &2, E.AcpiError, List<&2, AmlResource>>:
  res.loop(Nat.add(B.Octets.len(o), 1n), res.step(o), Nil{})

def res.addr.tag.go(+n: Nat) -> U32:
  match n:
    case 16n:
      136
    case 32n:
      135
    case _:
      138

def res.addr.tag(+width: U32) -> U32:
  res.addr.tag.go(U32.to_nat(width))

def res.irqs.enc(xs: List<&2, U32>) -> B.Octets:
  match xs:
    case Nil{}:
      B.Octets.empty()
    case Con{x, t}:
      B.Octets.append(B.Octets.le32(x), res.irqs.enc(t))

def res.other(small: Bool, +t: U32, +d: B.Octets) -> B.Octets:
  match small:
    case True{}:
      B.Octets.append(res.b([U32.or(t, U32.from_nat(B.Octets.len(d)))]), d)
    case False{}:
      res.lenc(t, d)

def AmlResource.encode(r: AmlResource) -> B.Octets:
  match r:
    case AmlRIrq{m, f}:
      B.Octets.append(res.b([35]), B.Octets.append(B.Octets.le16(m), res.b([f])))
    case AmlRDma{m, f}:
      res.b([42, m, f])
    case AmlRIo{dc, mn, mx, al, l}:
      B.Octets.concat([res.b([71, dc]), B.Octets.le16(mn), B.Octets.le16(mx), res.b([al, l])])
    case AmlRFixedIo{b, l}:
      B.Octets.concat([res.b([75]), B.Octets.le16(b), res.b([l])])
    case AmlRMem32{wr, mn, mx, al, l}:
      res.lenc(133, B.Octets.concat([res.b([wr]), B.Octets.le32(mn), B.Octets.le32(mx), B.Octets.le32(al), B.Octets.le32(l)]))
    case AmlRMem32Fixed{wr, b, l}:
      res.lenc(134, B.Octets.concat([res.b([wr]), B.Octets.le32(b), B.Octets.le32(l)]))
    case AmlRAddr{+bits, k, f, tf, AmlRange{g, mn, mx, t, l}}:
      res.lenc(res.addr.tag(bits), B.Octets.concat([res.b([k, f, tf]), res.w(bits, g), res.w(bits, mn), res.w(bits, mx), res.w(bits, t), res.w(bits, l)]))
    case AmlRExtIrq{f, +irqs}:
      res.lenc(137, B.Octets.concat([res.b([f, U32.from_nat(List.length(&2, U32, irqs))]), res.irqs.enc(irqs)]))
    case AmlROther{+t, +d}:
      res.other(U32.is_lt(t, 128), t, d)

def res.enc.all(rs: List<&2, AmlResource>) -> B.Octets:
  match rs:
    case Nil{}:
      res.b([121, 0])
    case Con{r, t}:
      B.Octets.append(AmlResource.encode(r), res.enc.all(t))

# a resource template: the descriptors, then the End Tag
def AmlResource.template(rs: List<&2, AmlResource>) -> B.Octets:
  res.enc.all(rs)
