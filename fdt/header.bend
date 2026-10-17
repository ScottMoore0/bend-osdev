# bend-osdev-fdt, header.bend: the 40-byte header of a devicetree blob
# (Devicetree Specification v0.4, section 5.2), big-endian:
#
#   magic (0xd00dfeed), totalsize, off_dt_struct, off_dt_strings,
#   off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys,
#   size_dt_strings, size_dt_struct
#
# FdtHeader.decode reads the ten fields as they are; FdtHeader.check
# validates them against the blob's length, with one error for each way a
# header can be wrong. size_dt_struct exists from version 17; for version 16
# it is ignored and the structure block runs to totalsize.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./layout.bend as L

type FdtHeader is Data:
  FdtHeader{magic: U32, totalsize: U32, off_dt_struct: U32, off_dt_strings: U32, off_mem_rsvmap: U32, version: U32, last_comp_version: U32, boot_cpuid_phys: U32, size_dt_strings: U32, size_dt_struct: U32}

# The versions a reader accepts
type FdtVersions is Data:
  # versions 16 and 17 (the default)
  FdtV16V17{}
  # version 17 only
  FdtV17Only{}
  # any version from 16 on whose last_comp_version is at most 17, as the
  # specification allows a later version to declare itself readable
  FdtVCompatible{}

def FdtVersions.default() -> FdtVersions:
  FdtV16V17{}

# 0xd00dfeed
def FdtHeader.magic_value() -> U32:
  3490578157

# the header's size in bytes
def FdtHeader.size() -> Nat:
  40n

# Writing

def hdr.list(h: FdtHeader) -> List<&2, U32>:
  match h:
    case FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings, off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys, size_dt_strings, size_dt_struct}:
      B.append(B.be32(magic), B.append(B.be32(totalsize), B.append(B.be32(off_dt_struct), B.append(B.be32(off_dt_strings), B.append(B.be32(off_mem_rsvmap), B.append(B.be32(version), B.append(B.be32(last_comp_version), B.append(B.be32(boot_cpuid_phys), B.append(B.be32(size_dt_strings), B.be32(size_dt_struct))))))))))

# the header's 40 bytes
def FdtHeader.encode(h: FdtHeader) -> B.Octets:
  B.Octets.of_list(hdr.list(h))

# Reading

def hdr.mk(m0: Maybe<&2, U32>, m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>, m4: Maybe<&2, U32>, m5: Maybe<&2, U32>, m6: Maybe<&2, U32>, m7: Maybe<&2, U32>, m8: Maybe<&2, U32>, m9: Maybe<&2, U32>) -> Maybe<&2, FdtHeader>:
  match m0 m1 m2 m3 m4 m5 m6 m7 m8 m9:
    case Some{a} Some{b} Some{c} Some{d} Some{e} Some{f} Some{g} Some{i} Some{j} Some{k}:
      Some{FdtHeader{a, b, c, d, e, f, g, i, j, k}}
    case _ _ _ _ _ _ _ _ _ _:
      None{}

# the header in the first 40 bytes; None if there are fewer
def hdr.decode(+xs: List<&2, U32>) -> Maybe<&2, FdtHeader>:
  hdr.mk(B.be32_at(xs, 0n), B.be32_at(xs, 4n), B.be32_at(xs, 8n), B.be32_at(xs, 12n), B.be32_at(xs, 16n), B.be32_at(xs, 20n), B.be32_at(xs, 24n), B.be32_at(xs, 28n), B.be32_at(xs, 32n), B.be32_at(xs, 36n))

def hdr.decode.pub(m: Maybe<&2, FdtHeader>) -> Result<&2, &2, E.FdtError, FdtHeader>:
  match m:
    case Some{h}:
      Done{h}
    case None{}:
      Fail{E.FdtTooShort{}}

# the ten fields of the first 40 bytes, unchecked
def FdtHeader.decode(o: B.Octets) -> Result<&2, &2, E.FdtError, FdtHeader>:
  hdr.decode.pub(hdr.decode(B.Octets.to_list(o)))

# Checking

def hdr.vers_more(vs: FdtVersions, +v: U32) -> Bool:
  match vs:
    case FdtV16V17{}:
      U32.is_eq(v, 16)
    case FdtV17Only{}:
      False{}
    case FdtVCompatible{}:
      U32.is_lt(15, v)

# version 17 is always accepted
def hdr.version_ok(vs: FdtVersions, +v: U32) -> Bool:
  Bool.or(U32.is_eq(v, 17), hdr.vers_more(vs, v))

def hdr.lastcomp_ok(v: U32, +lc: U32) -> Bool:
  Bool.and(U32.is_le(lc, 17), U32.is_le(lc, v))

# the end of the structure block: size_dt_struct exists from version 17
def hdr.struct_end(has_size: Bool, +off: Nat, size: Nat) -> Nat:
  match has_size:
    case True{}:
      Nat.add(off, size)
    case False{}:
      off

def hdr.c7(ok: Bool) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{E.FdtBadStrings{}}

def hdr.c6(ok: Bool, +ts: Nat, +ostr: Nat, sstr: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      hdr.c7(Bool.and(L.fdt.le(40n, ostr), L.fdt.le(Nat.add(ostr, sstr), ts)))
    case False{}:
      Fail{E.FdtBadStruct{}}

def hdr.c5(ok: Bool, +v: U32, +ts: Nat, +os: Nat, ostr: Nat, sstr: Nat, sst: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      hdr.c6(Bool.and(L.fdt.al4(os), Bool.and(L.fdt.le(40n, os), L.fdt.le(hdr.struct_end(U32.is_lt(16, v), os, sst), ts))), ts, ostr, sstr)
    case False{}:
      Fail{E.FdtBadRsvmap{}}

def hdr.c4(ok: Bool, +v: U32, +ts: Nat, os: Nat, ostr: Nat, +orsv: Nat, sstr: Nat, sst: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      hdr.c5(Bool.and(L.fdt.al8(orsv), Bool.and(L.fdt.le(40n, orsv), L.fdt.le(orsv, ts))), v, ts, os, ostr, sstr, sst)
    case False{}:
      Fail{E.FdtBadTotalSize{}}

def hdr.c3(ok: Bool, v: U32, +ts: Nat, os: Nat, ostr: Nat, orsv: Nat, sstr: Nat, sst: Nat, len: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      hdr.c4(Bool.and(L.fdt.le(40n, ts), L.fdt.le(ts, len)), v, ts, os, ostr, orsv, sstr, sst)
    case False{}:
      Fail{E.FdtBadLastComp{}}

def hdr.c2(ok: Bool, +v: U32, lc: U32, ts: Nat, os: Nat, ostr: Nat, orsv: Nat, sstr: Nat, sst: Nat, len: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      hdr.c3(hdr.lastcomp_ok(v, lc), v, ts, os, ostr, orsv, sstr, sst, len)
    case False{}:
      Fail{E.FdtBadVersion{}}

def hdr.c1(ok: Bool, vs: FdtVersions, +v: U32, lc: U32, ts: Nat, os: Nat, ostr: Nat, orsv: Nat, sstr: Nat, sst: Nat, len: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match ok:
    case True{}:
      hdr.c2(hdr.version_ok(vs, v), v, lc, ts, os, ostr, orsv, sstr, sst, len)
    case False{}:
      Fail{E.FdtBadMagic{}}

# a header fit for a blob of len bytes: the magic; a version vs accepts; a
# last_comp_version this reader understands; totalsize from 40 bytes to len;
# the reservation block 8-aligned, after the header, within totalsize; the
# structure block 4-aligned, after the header, within totalsize; the strings
# block after the header, within totalsize. Checked in that order.
def FdtHeader.check(vs: FdtVersions, h: FdtHeader, len: Nat) -> Result<&2, &2, E.FdtError, Unit>:
  match h:
    case FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings, off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys, size_dt_strings, size_dt_struct}:
      hdr.c1(U32.is_eq(magic, FdtHeader.magic_value()), vs, version, last_comp_version, U32.to_nat(totalsize), U32.to_nat(off_dt_struct), U32.to_nat(off_dt_strings), U32.to_nat(off_mem_rsvmap), U32.to_nat(size_dt_strings), U32.to_nat(size_dt_struct), len)
