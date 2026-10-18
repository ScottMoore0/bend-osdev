# bend-osdev-acpi, aml_field.bend: reading and writing field units (ACPI
# 6.5, chapter 19, Field; and section 5.5.2.4, Access to Operation
# Regions) and buffer fields (chapter 19, CreateBitField and the others).
#
# A field unit is bits [bit_off, bit_off + bits) of its region, read and
# written in units of its access width (FieldFlags bits 0-3: ByteAcc 1
# byte, WordAcc 2, DWordAcc 4, QWordAcc 8; AnyAcc and BufferAcc are read a
# byte at a time). A unit the field covers only in part is written by its
# update rule (bits 5-6: Preserve reads the unit first, WriteAsOnes and
# WriteAsZeros fill the other bits). A unit outside the region is refused
# (AcpiAmlRange). Fields up to 64 bits are Integers; wider fields, and wider
# buffer fields, are Buffers.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./aml_host.bend as Hs

# a field unit, with its region resolved
type AmlFieldDesc is Data:
  AmlFieldDesc{space: U32, base: W.W64, rlen: W.W64, bit_off: Nat, bits: Nat, flags: U32}

def fld.width.go(a: Nat) -> Nat:
  match a:
    case 2n:
      2n
    case 3n:
      4n
    case 4n:
      8n
    case _:
      1n

# the access width in bytes, from the field flags
def AmlField.unit(+flags: U32) -> Nat:
  fld.width.go(U32.to_nat(U32.and(flags, 15)))

def AmlField.update_rule(+flags: U32) -> U32:
  U32.and(U32.shrn(flags, 5n), 3)

def fld.mask.pick(all: Bool, +n: Nat) -> W.W64:
  match all:
    case True{}:
      W.W64.max()
    case False{}:
      W.W64.sub(W.W64.shl(W.W64.one(), n), W.W64.one())

# n low bits set
def fld.mask(+n: Nat) -> W.W64:
  fld.mask.pick(Nat.is_le(64n, n), n)

def fld.min(+a: Nat, +b: Nat) -> Nat:
  Nat.min(a, b)

def fld.max(+a: Nat, +b: Nat) -> Nat:
  Nat.max(a, b)

# one unit: its address, and the part of the field it holds
type AmlUnit is Data:
  # addr: the unit's address; s: the field's first bit in it; n: how many
  # field bits it holds; d: where they go in the field's value
  AmlUnit{addr: W.W64, s: Nat, n: Nat, d: Nat, fits: Bool}

def fld.unit(+f: AmlFieldDesc, +k: Nat) -> AmlUnit:
  match f:
    case AmlFieldDesc{sp, +base, +rlen, +off, +bits, +flags}:
      +w = AmlField.unit(flags)
      +ubits = Nat.mul(w, 8n)
      +start = Nat.mul(k, ubits)
      +lo = fld.max(off, start)
      +hi = fld.min(Nat.add(off, bits), Nat.add(start, ubits))
      AmlUnit{W.W64.add(base, W.W64.from_nat(Nat.mul(k, w))), Nat.sub(lo, start), Nat.sub(hi, lo), Nat.sub(lo, off), W.W64.is_le(W.W64.from_nat(Nat.mul(Nat.add(k, 1n), w)), rlen)}

def fld.first(+f: AmlFieldDesc) -> Nat:
  match f:
    case AmlFieldDesc{sp, base, rlen, +off, bits, +flags}:
      Nat.div(off, Nat.mul(AmlField.unit(flags), 8n))

def fld.count(+f: AmlFieldDesc) -> Nat:
  match f:
    case AmlFieldDesc{sp, base, rlen, +off, +bits, +flags}:
      +ub = Nat.mul(AmlField.unit(flags), 8n)
      Nat.sub(Nat.add(Nat.div(Nat.sub(Nat.add(off, bits), 1n), ub), 1n), Nat.div(off, ub))

def fld.space(f: AmlFieldDesc) -> U32:
  match f:
    case AmlFieldDesc{sp, base, rlen, off, bits, flags}:
      sp

def fld.flags(f: AmlFieldDesc) -> U32:
  match f:
    case AmlFieldDesc{sp, base, rlen, off, bits, flags}:
      flags

def fld.bits(f: AmlFieldDesc) -> Nat:
  match f:
    case AmlFieldDesc{sp, base, rlen, off, bits, flags}:
      bits

def fld.access(+f: AmlFieldDesc, +addr: W.W64) -> Hs.AmlAccess:
  Hs.AmlAccess{fld.space(f), addr, Nat.mul(AmlField.unit(fld.flags(f)), 8n)}

def AmlUnit.addr(u: AmlUnit) -> W.W64:
  match u:
    case AmlUnit{a, s, n, d, ok}:
      a

def AmlUnit.fits(u: AmlUnit) -> Bool:
  match u:
    case AmlUnit{a, s, n, d, ok}:
      ok

# the unit's own bits that belong to the field
def AmlUnit.hole(u: AmlUnit) -> W.W64:
  match u:
    case AmlUnit{a, +s, +n, d, ok}:
      W.W64.shl(fld.mask(n), s)

# the field bits a unit holds, from the unit's value v, in place in the
# field's value
def AmlUnit.take(u: AmlUnit, +v: W.W64) -> W.W64:
  match u:
    case AmlUnit{a, +s, +n, +d, ok}:
      W.W64.shl(W.W64.and(W.W64.shr(v, s), fld.mask(n)), d)

# the unit's share of the field's value x, in place in the unit
def AmlUnit.put(u: AmlUnit, +x: W.W64) -> W.W64:
  match u:
    case AmlUnit{a, +s, +n, +d, ok}:
      W.W64.shl(W.W64.and(W.W64.shr(x, d), fld.mask(n)), s)

# the unit is the field's alone (no other bits to keep)
def AmlUnit.whole(u: AmlUnit, +w: Nat) -> Bool:
  match u:
    case AmlUnit{a, s, +n, d, ok}:
      Nat.is_eq(n, Nat.mul(w, 8n))

def fld.rd.unit(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, fits: Bool, h: H, +a: Hs.AmlAccess) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match fits:
    case True{}:
      io(h, Hs.AmlHRead{a})
    case False{}:
      Fail{E.AcpiAmlRange{}}

def fld.rd.next(-H: Data, +u: AmlUnit, +acc: W.W64, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Hs.AmlHostAns{h2, +v}}:
      Done{Hs.AmlHostAns{h2, W.W64.or(acc, AmlUnit.take(u, v))}}

# units k .. k + n - 1, read and joined into the value in r
def fld.rd(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +f: AmlFieldDesc, +k: Nat, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, acc}}:
          +u = fld.unit(f, k)
          fld.rd(~H, ~io, p, f, 1n+k, fld.rd.next(H, u, acc, fld.rd.unit(~H, ~io, AmlUnit.fits(u), h, fld.access(f, AmlUnit.addr(u)))))

# the value of a field unit of at most 64 bits
def AmlField.read_int(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +f: AmlFieldDesc, h: H) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  fld.rd(~H, ~io, fld.count(f), f, fld.first(f), Done{Hs.AmlHostAns{h, W.W64.zero()}})

# Writing

# the unit's bits that are not the field's, by the update rule: read
# (Preserve), all ones, all zeros
def fld.keep(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, whole: Bool, rule: Nat, h: H, +a: Hs.AmlAccess) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match whole:
    case True{}:
      Done{Hs.AmlHostAns{h, W.W64.zero()}}
    case False{}:
      match rule:
        case 1n:
          Done{Hs.AmlHostAns{h, W.W64.max()}}
        case 2n:
          Done{Hs.AmlHostAns{h, W.W64.zero()}}
        case _:
          io(h, Hs.AmlHRead{a})

def fld.wr.unit(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +u: AmlUnit, +a: Hs.AmlAccess, +x: W.W64) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Hs.AmlHostAns{h, +old}}:
      io(h, Hs.AmlHWrite{a, W.W64.or(W.W64.and(old, W.W64.not(AmlUnit.hole(u))), AmlUnit.put(u, x))})

def fld.wr.fits(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, fits: Bool, h: H, +f: AmlFieldDesc, +u: AmlUnit, +x: W.W64) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match fits:
    case False{}:
      Fail{E.AcpiAmlRange{}}
    case True{}:
      +a = fld.access(f, AmlUnit.addr(u))
      +flags = fld.flags(f)
      fld.wr.unit(~H, ~io, fld.keep(~H, ~io, AmlUnit.whole(u, AmlField.unit(flags)), U32.to_nat(AmlField.update_rule(flags)), h, a), u, a, x)

# units k .. k + n - 1 written with their share of x
def fld.wr(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +f: AmlFieldDesc, +k: Nat, +x: W.W64, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, v}}:
          +u = fld.unit(f, k)
          fld.wr(~H, ~io, p, f, 1n+k, x, fld.wr.fits(~H, ~io, AmlUnit.fits(u), h, f, u, x))

# a field unit of at most 64 bits set to x (its low bits)
def AmlField.write_int(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +f: AmlFieldDesc, h: H, +x: W.W64) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  fld.wr(~H, ~io, fld.count(f), f, fld.first(f), x, Done{Hs.AmlHostAns{h, W.W64.zero()}})

# Wider fields: a byte at a time, as a Buffer

def fld.byte(+f: AmlFieldDesc, +j: Nat) -> AmlFieldDesc:
  match f:
    case AmlFieldDesc{sp, base, rlen, +off, +bits, flags}:
      AmlFieldDesc{sp, base, rlen, Nat.add(off, Nat.mul(j, 8n)), Nat.min(8n, Nat.sub(bits, Nat.mul(j, 8n))), flags}

type AmlFieldBuf<-H: Data> is Data:
  AmlFieldBuf{host: H, value: B.Octets}

def fld.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      fld.rev(t, Con{x, acc})

# bytes j .. j + n of the field; r: the read of byte j - 1
def fld.bytes.rd(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +f: AmlFieldDesc, +j: Nat, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, acc: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlFieldBuf<H>>:
  match n:
    case 0n:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, v}}:
          Done{AmlFieldBuf{h, B.Octets.of_list(fld.rev(Con{W.W64.lo(v), acc}, Nil{}))}}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, v}}:
          fld.bytes.rd(~H, ~io, p, f, 1n+j, AmlField.read_int(~H, ~io, fld.byte(f, j), h), Con{W.W64.lo(v), acc})

def fld.nbytes(+f: AmlFieldDesc) -> Nat:
  Nat.div(Nat.add(fld.bits(f), 7n), 8n)

# a field unit of any width, as a Buffer of its bytes
def AmlField.read_buf(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +f: AmlFieldDesc, h: H) -> Result<&2, &2, E.AcpiError, AmlFieldBuf<H>>:
  fld.bytes.rd(~H, ~io, Nat.sub(fld.nbytes(f), 1n), f, 1n, AmlField.read_int(~H, ~io, fld.byte(f, 0n), h), Nil{})

def fld.bytes.wr(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +f: AmlFieldDesc, +j: Nat, +o: B.Octets, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, v}}:
          fld.bytes.wr(~H, ~io, p, f, 1n+j, o, AmlField.write_int(~H, ~io, fld.byte(f, j), h, W.W64.from_u32(Maybe.default(&2, U32, B.Octets.at(o, j), 0))))

# a field unit of any width set from the bytes of o (zeros past its end)
def AmlField.write_buf(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +f: AmlFieldDesc, h: H, +o: B.Octets) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  fld.bytes.wr(~H, ~io, fld.nbytes(f), f, 0n, o, Done{Hs.AmlHostAns{h, W.W64.zero()}})

# Buffer fields: bits of a buffer

def fld.bit(+o: B.Octets, +i: Nat) -> W.W64:
  W.W64.and(W.W64.shr(W.W64.from_u32(Maybe.default(&2, U32, B.Octets.at(o, Nat.div(i, 8n)), 0)), Nat.mod(i, 8n)), W.W64.one())

def fld.bits.get(n: Nat, +o: B.Octets, +i: Nat, +k: Nat, acc: W.W64) -> W.W64:
  match n:
    case 0n:
      acc
    case 1n+p:
      fld.bits.get(p, o, Nat.add(i, 1n), Nat.add(k, 1n), W.W64.or(acc, W.W64.shl(fld.bit(o, i), k)))

def fld.bits.pick(ok: Bool, r: Result<&2, &2, E.AcpiError, W.W64>) -> Result<&2, &2, E.AcpiError, W.W64>:
  match ok:
    case True{}:
      r
    case False{}:
      Fail{E.AcpiAmlRange{}}

# bits [off, off + n) of o (n at most 64), as an integer; AcpiAmlRange if
# they run past o
def AmlBits.get(+o: B.Octets, +off: Nat, +n: Nat) -> Result<&2, &2, E.AcpiError, W.W64>:
  fld.bits.pick(Nat.is_le(Nat.add(off, n), Nat.mul(B.Octets.len(o), 8n)), Done{fld.bits.get(n, o, off, 0n, W.W64.zero())})

def fld.bits.one(on: Bool, +old: U32, +bit: U32) -> U32:
  match on:
    case True{}:
      U32.or(old, bit)
    case False{}:
      U32.and(old, U32.not(bit))

def fld.bits.set(n: Nat, xs: List<&2, U32>, +i: Nat, +k: Nat, +v: W.W64) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      +ys = xs
      +j = Nat.div(i, 8n)
      +bit = U32.shln(1, Nat.mod(i, 8n))
      +old = Maybe.default(&2, U32, B.at(ys, j), 0)
      +on = W.W64.is_eq(W.W64.and(W.W64.shr(v, k), W.W64.one()), W.W64.one())
      fld.bits.set(p, List.set(&2, U32, ys, j, fld.bits.one(on, old, bit)), Nat.add(i, 1n), Nat.add(k, 1n), v)

def fld.bufs.pick(ok: Bool, +o: B.Octets, +off: Nat, n: Nat, +v: W.W64) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match ok:
    case True{}:
      Done{B.Octets.of_list(fld.bits.set(n, B.Octets.to_list(o), off, 0n, v))}
    case False{}:
      Fail{E.AcpiAmlRange{}}

# o with bits [off, off + n) set from the low n bits of v (n at most 64)
def AmlBits.set(+o: B.Octets, +off: Nat, +n: Nat, +v: W.W64) -> Result<&2, &2, E.AcpiError, B.Octets>:
  fld.bufs.pick(Nat.is_le(Nat.add(off, n), Nat.mul(B.Octets.len(o), 8n)), o, off, n, v)

def fld.bitsb.get(n: Nat, +o: B.Octets, +i: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      fld.rev(acc, Nil{})
    case 1n+p:
      fld.bitsb.get(p, o, Nat.add(i, 8n), Con{W.W64.lo(fld.bits.get(8n, o, i, 0n, W.W64.zero())), acc})

# bits [off, off + n) of o as a Buffer of ceil(n / 8) bytes (the last byte's
# high bits are the bits that follow the field; callers mask them)
def AmlBits.get_buf(+o: B.Octets, +off: Nat, +n: Nat) -> B.Octets:
  B.Octets.of_list(fld.bitsb.get(Nat.div(Nat.add(n, 7n), 8n), o, off, Nil{}))

# IndexField (chapter 19): the field's bits are reached a unit at a time by
# writing the unit's byte offset to the index field, then reading or
# writing the data field. f: the field (base 0; rlen its reach). A write
# puts the field's share of each unit in the data field; the other bits of
# the unit are written as zeros (the update rule is not applied through
# the data register).

def fld.ix.rd.k(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +dat: AmlFieldDesc, +u: AmlUnit, +acc: W.W64, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Hs.AmlHostAns{h, v}}:
      fld.rd.next(H, u, acc, AmlField.read_int(~H, ~io, dat, h))

def fld.ix.rd(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +idx: AmlFieldDesc, +dat: AmlFieldDesc, +f: AmlFieldDesc, +k: Nat, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, acc}}:
          +u = fld.unit(f, k)
          fld.ix.rd(~H, ~io, p, idx, dat, f, 1n+k, fld.ix.rd.k(~H, ~io, dat, u, acc, AmlField.write_int(~H, ~io, idx, h, AmlUnit.addr(u))))

def AmlField.read_indexed(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +idx: AmlFieldDesc, +dat: AmlFieldDesc, +f: AmlFieldDesc, h: H) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  fld.ix.rd(~H, ~io, fld.count(f), idx, dat, f, fld.first(f), Done{Hs.AmlHostAns{h, W.W64.zero()}})

def fld.ix.data(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +dat: AmlFieldDesc, +u: AmlUnit, +x: W.W64, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Hs.AmlHostAns{h, v}}:
      AmlField.write_int(~H, ~io, dat, h, AmlUnit.put(u, x))

def fld.ix.wr(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, n: Nat, +idx: AmlFieldDesc, +dat: AmlFieldDesc, +f: AmlFieldDesc, +k: Nat, +x: W.W64, r: Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  match n:
    case 0n:
      r
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{Hs.AmlHostAns{h, v}}:
          +u = fld.unit(f, k)
          fld.ix.wr(~H, ~io, p, idx, dat, f, 1n+k, x, fld.ix.data(~H, ~io, dat, u, x, AmlField.write_int(~H, ~io, idx, h, AmlUnit.addr(u))))

def AmlField.write_indexed(~H: Data, ~io: H -> Hs.AmlHostOp -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>, +idx: AmlFieldDesc, +dat: AmlFieldDesc, +f: AmlFieldDesc, h: H, +x: W.W64) -> Result<&2, &2, E.AcpiError, Hs.AmlHostAns<H>>:
  fld.ix.wr(~H, ~io, fld.count(f), idx, dat, f, fld.first(f), x, Done{Hs.AmlHostAns{h, W.W64.zero()}})
