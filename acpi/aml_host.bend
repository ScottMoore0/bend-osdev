# bend-osdev-acpi, aml_host.bend: how AML reaches hardware. Operation
# regions (ACPI 6.5, chapter 19, OperationRegion; 5.5.2.4, Access to
# Operation Regions) are read and written through a host, a template
# argument of the interpreter:
#
#   ~H: Data, ~io: H -> AmlHostOp -> Result<&2, &2, AcpiError, AmlHostAns<H>>
#
# io(h, AmlHRead{a}) answers the value read and the host after the read
# (a read may have effects); io(h, AmlHWrite{a, v}) answers the host after
# the write (and v). An access names its address space (0 SystemMemory,
# 1 SystemIO, 2 PCI_Config, 3 EmbeddedControl, 4 SMBus, 5 SystemCMOS,
# 6 PciBarTarget, 7 IPMI, 8 GeneralPurposeIO, 9 GenericSerialBus, 10 PCC,
# 0x80 and up OEM), its address and its width in bits (8, 16, 32 or 64).
#
# A PCI_Config address is laid out as in a Generic Address Structure
# (5.2.3.2: offset in bits 0-15, function in 16-31, device in 32-47), with
# the bus in bits 48-55 and the low byte of the segment in bits 56-63
# (AmlPci.address); the interpreter takes the device and function from the
# region's device's _ADR, the bus from _BBN and the segment from _SEG of the
# nearest enclosing device that has them (6.1.1, 6.5.5, 6.5.6).
#
# AmlMemHost, the default, is pure memory: one byte map per address space,
# zero where nothing was written, and a log of every access.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E

type AmlAccess is Data:
  AmlAccess{space: U32, address: W.W64, width: Nat}

type AmlHostOp is Data:
  AmlHRead{a: AmlAccess}
  AmlHWrite{a: AmlAccess, v: W.W64}

type AmlHostAns<-H: Data> is Data:
  AmlHostAns{host: H, value: W.W64}

def AmlPci.address(seg: U32, bus: U32, dev: U32, fun: U32, off: U32) -> W.W64:
  W.W64.from_parts(U32.or(U32.shln(U32.and(seg, 255), 24n), U32.or(U32.shln(U32.and(bus, 255), 16n), U32.and(dev, 65535))), U32.or(U32.shln(U32.and(fun, 65535), 16n), U32.and(off, 65535)))

# The in-memory host

type AmlMemHost is Data:
  AmlMemHost{bytes: Map<&2, U32>, log: List<&2, AmlHostOp>}

def AmlMemHost.new() -> AmlMemHost:
  AmlMemHost{Map.new(&2, U32), Nil{}}

def hst.key(+space: U32, +a: W.W64) -> String:
  U32.show(space) ++ ":" ++ W.W64.show_hex(a)

def hst.snd(r: Map<&2, U32> & U32) -> U32:
  (m, v) = r
  v

def hst.byte(+m: Map<&2, U32>, +space: U32, +a: W.W64) -> U32:
  hst.snd(Map.get(U32, 0, m, hst.key(space, a)))

# n bytes from address a, little-endian, into acc from bit sh
def hst.rd(n: Nat, +m: Map<&2, U32>, +space: U32, +a: W.W64, +sh: Nat, acc: W.W64) -> W.W64:
  match n:
    case 0n:
      acc
    case 1n+p:
      hst.rd(p, m, space, W.W64.add(a, W.W64.one()), Nat.add(sh, 8n), W.W64.or(acc, W.W64.shl(W.W64.from_u32(hst.byte(m, space, a)), sh)))

def hst.wr(n: Nat, m: Map<&2, U32>, +space: U32, +a: W.W64, +v: W.W64) -> Map<&2, U32>:
  match n:
    case 0n:
      m
    case 1n+p:
      hst.wr(p, Map.set(&2, U32, m, hst.key(space, a), U32.and(W.W64.lo(v), 255)), space, W.W64.add(a, W.W64.one()), W.W64.shr(v, 8n))

def hst.go(h: AmlMemHost, op: AmlHostOp) -> Result<&2, &2, E.AcpiError, AmlHostAns<AmlMemHost>>:
  match h op:
    case AmlMemHost{+m, log} AmlHRead{AmlAccess{+s, +a, +w}}:
      Done{AmlHostAns{AmlMemHost{m, Con{AmlHRead{AmlAccess{s, a, w}}, log}}, hst.rd(Nat.div(w, 8n), m, s, a, 0n, W.W64.zero())}}
    case AmlMemHost{m, log} AmlHWrite{AmlAccess{+s, +a, +w}, +v}:
      Done{AmlHostAns{AmlMemHost{hst.wr(Nat.div(w, 8n), m, s, a, v), Con{AmlHWrite{AmlAccess{s, a, w}, v}, log}}, v}}

# the host interface for AmlMemHost (plain parameters, so that it fits the
# template type ~io)
def AmlMemHost.io(h: AmlMemHost, op: AmlHostOp) -> Result<&2, &2, E.AcpiError, AmlHostAns<AmlMemHost>>:
  hst.go(h, op)

def hst.load(xs: List<&2, U32>, m: Map<&2, U32>, +space: U32, +a: W.W64) -> Map<&2, U32>:
  match xs:
    case Nil{}:
      m
    case Con{x, t}:
      hst.load(t, Map.set(&2, U32, m, hst.key(space, a), x), space, W.W64.add(a, W.W64.one()))

# the host with bytes o at address a of a space (no access logged)
def AmlMemHost.poke(h: AmlMemHost, +space: U32, +a: W.W64, o: B.Octets) -> AmlMemHost:
  match h:
    case AmlMemHost{m, log}:
      AmlMemHost{hst.load(B.Octets.to_list(o), m, space, a), log}

# the byte at an address of a space
def AmlMemHost.peek(h: AmlMemHost, +space: U32, +a: W.W64) -> U32:
  match h:
    case AmlMemHost{+m, log}:
      hst.byte(m, space, a)

def hst.rev(xs: List<&2, AmlHostOp>, acc: List<&2, AmlHostOp>) -> List<&2, AmlHostOp>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      hst.rev(t, Con{x, acc})

# every access so far, oldest first
def AmlMemHost.log(h: AmlMemHost) -> List<&2, AmlHostOp>:
  match h:
    case AmlMemHost{m, log}:
      hst.rev(log, Nil{})

def AmlHostOp.show(op: AmlHostOp) -> String:
  match op:
    case AmlHRead{AmlAccess{s, a, w}}:
      "read " ++ U32.show(s) ++ ":" ++ W.W64.show_hex(a) ++ "/" ++ Nat.show(w)
    case AmlHWrite{AmlAccess{s, a, w}, v}:
      "write " ++ U32.show(s) ++ ":" ++ W.W64.show_hex(a) ++ "/" ++ Nat.show(w) ++ " " ++ W.W64.show_hex(v)

def hst.show(xs: List<&2, AmlHostOp>, first: Bool) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match first:
        case True{}:
          AmlHostOp.show(x) ++ hst.show(t, False{})
        case False{}:
          "; " ++ AmlHostOp.show(x) ++ hst.show(t, False{})

# the log as text, oldest first, "; " between accesses
def AmlMemHost.show_log(h: AmlMemHost) -> String:
  hst.show(AmlMemHost.log(h), True{})
