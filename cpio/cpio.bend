# bend-osdev-cpio: the "new ASCII" (newc, magic 070701) and "crc" (070702)
# cpio formats, as the Linux initramfs uses them. Written from the cpio(5)
# manual page (libarchive / FreeBSD) and the kernel's documentation of the
# initramfs buffer format.
#
# An archive is a run of entries, each a 110-byte header, the name, and the
# data, and ends with an entry named "TRAILER!!!". The header is the six-byte
# magic and thirteen fields, each eight ASCII hex digits (hexfield.bend):
# ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor,
# rdevminor, namesize and check. The name (namesize bytes, its NUL included)
# is padded with NULs so that header and name together are a multiple of four
# bytes long; the data (filesize bytes) is padded to a multiple of four too.
# In the crc format, check is the sum of the data bytes, modulo 2^32; in newc
# it is zero, and readers ignore it.
#
# A CpioEntry holds what an entry carries; filesize, namesize and check follow
# from its name and data, so Cpio.build computes them and Cpio.parse checks
# them. The public interface is listed in README.md; the list-level defs are
# internal.
import Base
import ../bytes/bytes.bend as B
import ./hexfield.bend as H

type CpioFormat is Data:
  CpioNewc{}
  CpioCrc{}

type CpioHeader is Data:
  CpioHeader{format: CpioFormat, ino: U32, mode: U32, uid: U32, gid: U32, nlink: U32, mtime: U32, filesize: U32, devmajor: U32, devminor: U32, rdevmajor: U32, rdevminor: U32, namesize: U32, check: U32}

# name: the path's bytes, without the NUL; data: the file's contents
type CpioEntry is Data:
  CpioEntry{ino: U32, mode: U32, uid: U32, gid: U32, nlink: U32, mtime: U32, devmajor: U32, devminor: U32, rdevmajor: U32, rdevminor: U32, name: B.Octets, data: B.Octets}

# a header and the bytes after it
type CpioHeaderAt is Data:
  CpioHeaderAt{header: CpioHeader, rest: B.Octets}

# why an archive was refused
type CpioError is Data:
  CpioTruncated{}
  CpioBadMagic{}
  CpioBadHex{}
  CpioBadNameSize{}
  CpioNoNul{}
  CpioBadChecksum{}
  CpioNoTrailer{}

# Internal types

type CpioHdrRest is Data:
  CpioHdrRest{header: CpioHeader, rest: List<&2, U32>}

type CpioCut is Data:
  CpioCut{head: List<&2, U32>, rest: List<&2, U32>}

type CpioFields is Data:
  CpioFields{values: List<&2, U32>, rest: List<&2, U32>}

type CpioStep is Data:
  CpioStepEnd{}
  CpioStepBad{error: CpioError}
  CpioStepEntry{entry: CpioEntry, rest: List<&2, U32>}

# The usual format: the initramfs is newc
def CpioFormat.default() -> CpioFormat:
  CpioNewc{}

# Header fields

# the fields vs, then the bytes rest
def fields.encode_onto(vs: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match vs:
    case Nil{}:
      rest
    case Con{v, t}:
      B.append(H.field.encode(v), fields.encode_onto(t, rest))

def fields.cons(m: Maybe<&2, U32>, r: Result<&2, &2, CpioError, CpioFields>) -> Result<&2, &2, CpioError, CpioFields>:
  match m r:
    case None{} _:
      Fail{CpioBadHex{}}
    case Some{v} Fail{e}:
      Fail{e}
    case Some{v} Done{CpioFields{vs, rest}}:
      Done{CpioFields{Con{v, vs}, rest}}

# n fields from the head of xs, and the bytes after them
def fields.take(n: Nat, xs: List<&2, U32>) -> Result<&2, &2, CpioError, CpioFields>:
  match n:
    case 0n:
      Done{CpioFields{Nil{}, xs}}
    case 1n+p:
      match xs:
        case Con{c7, Con{c6, Con{c5, Con{c4, Con{c3, Con{c2, Con{c1, Con{c0, t}}}}}}}}:
          fields.cons(H.field.join(H.nibble.decode(c7), H.nibble.decode(c6), H.nibble.decode(c5), H.nibble.decode(c4), H.nibble.decode(c3), H.nibble.decode(c2), H.nibble.decode(c1), H.nibble.decode(c0)), fields.take(p, t))
        case _:
          Fail{CpioTruncated{}}

# Headers

# the last digit of the magic: 070701 (newc) or 070702 (crc)
def magic.last(fmt: CpioFormat) -> U32:
  match fmt:
    case CpioNewc{}:
      49
    case CpioCrc{}:
      50

def magic(fmt: CpioFormat) -> List<&2, U32>:
  [48, 55, 48, 55, 48, magic.last(fmt)]

def magic.prefix(a: U32, b: U32, c: U32, d: U32, e: U32) -> Bool:
  Bool.and(U32.is_eq(U32.and(a, 255), 48), Bool.and(U32.is_eq(U32.and(b, 255), 55), Bool.and(U32.is_eq(U32.and(c, 255), 48), Bool.and(U32.is_eq(U32.and(d, 255), 55), U32.is_eq(U32.and(e, 255), 48)))))

def magic.kind.crc(hit: Bool) -> Maybe<&2, CpioFormat>:
  match hit:
    case True{}:
      Some{CpioCrc{}}
    case False{}:
      None{}

def magic.kind.newc(hit: Bool, +c: U32) -> Maybe<&2, CpioFormat>:
  match hit:
    case True{}:
      Some{CpioNewc{}}
    case False{}:
      magic.kind.crc(U32.is_eq(c, 50))

# the format a magic's last byte names
def magic.kind(x: U32) -> Maybe<&2, CpioFormat>:
  +c = U32.and(x, 255)
  magic.kind.newc(U32.is_eq(c, 49), c)

# the thirteen fields, in storage order
def hdr.values(h: CpioHeader) -> List<&2, U32>:
  match h:
    case CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}:
      [ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check]

def hdr.format(h: CpioHeader) -> CpioFormat:
  match h:
    case CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}:
      fmt

# the header's 110 bytes
def hdr.encode(+h: CpioHeader) -> List<&2, U32>:
  B.append(magic(hdr.format(h)), fields.encode_onto(hdr.values(h), Nil{}))

def hdr.of(fmt: CpioFormat, vs: List<&2, U32>, rest: List<&2, U32>) -> Result<&2, &2, CpioError, CpioHdrRest>:
  match vs:
    case Con{ino, Con{mode, Con{uid, Con{gid, Con{nlink, Con{mtime, Con{filesize, Con{devmajor, Con{devminor, Con{rdevmajor, Con{rdevminor, Con{namesize, Con{check, Nil{}}}}}}}}}}}}}}:
      Done{CpioHdrRest{CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}, rest}}
    case _:
      Fail{CpioTruncated{}}

def hdr.decode.go(ok: Bool, k: Maybe<&2, CpioFormat>, m: Result<&2, &2, CpioError, CpioFields>) -> Result<&2, &2, CpioError, CpioHdrRest>:
  match ok k m:
    case True{} Some{fmt} Done{CpioFields{vs, rest}}:
      hdr.of(fmt, vs, rest)
    case True{} Some{fmt} Fail{e}:
      Fail{e}
    case _ _ _:
      Fail{CpioBadMagic{}}

# the header at the head of xs, and the bytes after it
def hdr.decode(xs: List<&2, U32>) -> Result<&2, &2, CpioError, CpioHdrRest>:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, t}}}}}}:
      hdr.decode.go(magic.prefix(a, b, c, d, e), magic.kind(f), fields.take(13n, t))
    case _:
      Fail{CpioTruncated{}}

# Sizes: a length as a 32-bit field

def nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+nat.half(q)

def nat.odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          nat.odd(q)

# the low k bits of n
def nat.bits(k: Nat, +n: Nat) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{nat.odd(n), nat.bits(p, nat.half(n))}

# n with its low k bits dropped: n / 2^k
def nat.high(k: Nat, n: Nat) -> Nat:
  match k:
    case 0n:
      n
    case 1n+p:
      nat.high(p, nat.half(n))

# n modulo 2^32
def size32(n: Nat) -> U32:
  U32{nat.bits(32n, n)}

# n / 2^32: zero exactly when n fits in a 32-bit field
def size.over(n: Nat) -> Nat:
  nat.high(32n, n)

# Byte lists

def split.cons(h: U32, m: Maybe<&2, CpioCut>) -> Maybe<&2, CpioCut>:
  match m:
    case None{}:
      None{}
    case Some{CpioCut{a, b}}:
      Some{CpioCut{Con{h, a}, b}}

# the first n bytes and the rest; None if there are fewer than n
def split(n: Nat, xs: List<&2, U32>) -> Maybe<&2, CpioCut>:
  match n:
    case 0n:
      Some{CpioCut{Nil{}, xs}}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{h, t}:
          split.cons(h, split(p, t))

# all but the first n bytes; None if there are fewer than n
def skip(n: Nat, xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      Some{xs}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{h, t}:
          skip(p, t)

# the padding that takes a length of n bytes to a multiple of four
def pad4(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+a:
      match a:
        case 0n:
          3n
        case 1n+b:
          match b:
            case 0n:
              2n
            case 1n+c:
              match c:
                case 0n:
                  1n
                case 1n+d:
                  pad4(d)

def checksum.go(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      checksum.go(t, U32.add(acc, U32.and(h, 255)))

def checksum(xs: List<&2, U32>) -> U32:
  checksum.go(xs, 0)

# equal bytes, comparing the low 8 bits of each element of xs
def same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      List.is_empty(&2, U32, ys)
    case Con{a, t}:
      match ys:
        case Nil{}:
          False{}
        case Con{b, u}:
          Bool.and(U32.is_eq(U32.and(a, 255), b), same(t, u))

# "TRAILER!!!"
def trailer.name() -> List<&2, U32>:
  [84, 82, 65, 73, 76, 69, 82, 33, 33, 33]

def trailer.is(name: List<&2, U32>) -> Bool:
  same(name, trailer.name())

# Reading an entry

def hdr.namesize(h: CpioHeader) -> U32:
  match h:
    case CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}:
      namesize

def hdr.filesize(h: CpioHeader) -> U32:
  match h:
    case CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}:
      filesize

def hdr.check_ok.go(fmt: CpioFormat, check: U32, data: List<&2, U32>) -> Bool:
  match fmt:
    case CpioNewc{}:
      True{}
    case CpioCrc{}:
      U32.is_eq(check, checksum(data))

# the crc format's check matches the data (the newc format has none)
def hdr.check_ok(h: CpioHeader, data: List<&2, U32>) -> Bool:
  match h:
    case CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}:
      hdr.check_ok.go(fmt, check, data)

def entry.of(h: CpioHeader, name: List<&2, U32>, data: List<&2, U32>) -> CpioEntry:
  match h:
    case CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, filesize, devmajor, devminor, rdevmajor, rdevminor, namesize, check}:
      CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(name), B.Octets.of_list(data)}

def entry.r10(ok: Bool, e: CpioEntry, r: List<&2, U32>) -> CpioStep:
  match ok:
    case True{}:
      CpioStepEntry{e, r}
    case False{}:
      CpioStepBad{CpioBadChecksum{}}

# after the data's padding
def entry.r9(m: Maybe<&2, List<&2, U32>>, name: List<&2, U32>, +data: List<&2, U32>, +h: CpioHeader) -> CpioStep:
  match m:
    case None{}:
      CpioStepBad{CpioTruncated{}}
    case Some{r}:
      entry.r10(hdr.check_ok(h, data), entry.of(h, name, data), r)

# after the data
def entry.r8(m: Maybe<&2, CpioCut>, name: List<&2, U32>, h: CpioHeader) -> CpioStep:
  match m:
    case None{}:
      CpioStepBad{CpioTruncated{}}
    case Some{CpioCut{+data, r}}:
      entry.r9(skip(pad4(B.len(data)), r), name, data, h)

# after the name's padding
def entry.r7(m: Maybe<&2, List<&2, U32>>, name: List<&2, U32>, +h: CpioHeader) -> CpioStep:
  match m:
    case None{}:
      CpioStepBad{CpioTruncated{}}
    case Some{r}:
      entry.r8(split(U32.to_nat(hdr.filesize(h)), r), name, h)

# after the name's NUL: the trailer ends the archive
def entry.r6(t: Bool, name: List<&2, U32>, p: Nat, h: CpioHeader, r: List<&2, U32>) -> CpioStep:
  match t:
    case True{}:
      CpioStepEnd{}
    case False{}:
      entry.r7(skip(pad4(Nat.add(111n, p)), r), name, h)

def entry.r5(ok: Bool, +name: List<&2, U32>, p: Nat, h: CpioHeader, r: List<&2, U32>) -> CpioStep:
  match ok:
    case True{}:
      entry.r6(trailer.is(name), name, p, h, r)
    case False{}:
      CpioStepBad{CpioNoNul{}}

# after the name: its NUL
def entry.r4(r: List<&2, U32>, name: List<&2, U32>, p: Nat, h: CpioHeader) -> CpioStep:
  match r:
    case Nil{}:
      CpioStepBad{CpioTruncated{}}
    case Con{z, t}:
      entry.r5(U32.is_eq(U32.and(z, 255), 0), name, p, h, t)

def entry.r3(m: Maybe<&2, CpioCut>, p: Nat, h: CpioHeader) -> CpioStep:
  match m:
    case None{}:
      CpioStepBad{CpioTruncated{}}
    case Some{CpioCut{name, r}}:
      entry.r4(r, name, p, h)

# after the header: the name, namesize - 1 bytes and a NUL
def entry.r2(+n: Nat, h: CpioHeader, r: List<&2, U32>) -> CpioStep:
  match n:
    case 0n:
      CpioStepBad{CpioBadNameSize{}}
    case 1n+p:
      entry.r3(split(p, r), p, h)

def entry.r1(m: Result<&2, &2, CpioError, CpioHdrRest>) -> CpioStep:
  match m:
    case Fail{e}:
      CpioStepBad{e}
    case Done{CpioHdrRest{+h, r}}:
      entry.r2(U32.to_nat(hdr.namesize(h)), h, r)

# the entry at the head of xs, and the bytes after it
def entry.read(xs: List<&2, U32>) -> CpioStep:
  match xs:
    case Nil{}:
      CpioStepBad{CpioNoTrailer{}}
    case Con{h, t}:
      entry.r1(hdr.decode(Con{h, t}))

def parse.cons(e: CpioEntry, m: Result<&2, &2, CpioError, List<&2, CpioEntry>>) -> Result<&2, &2, CpioError, List<&2, CpioEntry>>:
  match m:
    case Fail{x}:
      Fail{x}
    case Done{l}:
      Done{Con{e, l}}

# fuel bounds the number of entries
def parse.go(fuel: Nat, s: CpioStep) -> Result<&2, &2, CpioError, List<&2, CpioEntry>>:
  match fuel s:
    case _ CpioStepEnd{}:
      Done{Nil{}}
    case _ CpioStepBad{x}:
      Fail{x}
    case 0n CpioStepEntry{e, r}:
      Fail{CpioTruncated{}}
    case 1n+f CpioStepEntry{e, r}:
      parse.cons(e, parse.go(f, entry.read(r)))

# Public interface

def CpioHeader.encode(h: CpioHeader) -> B.Octets:
  B.Octets.of_list(hdr.encode(h))

def CpioHeader.decode.pub(m: Result<&2, &2, CpioError, CpioHdrRest>) -> Result<&2, &2, CpioError, CpioHeaderAt>:
  match m:
    case Fail{e}:
      Fail{e}
    case Done{CpioHdrRest{h, r}}:
      Done{CpioHeaderAt{h, B.Octets.of_list(r)}}

# the header at the head of o, and the bytes after it
def CpioHeader.decode(o: B.Octets) -> Result<&2, &2, CpioError, CpioHeaderAt>:
  CpioHeader.decode.pub(hdr.decode(B.Octets.to_list(o)))

# the crc format's check: the sum of the bytes, modulo 2^32
def Cpio.checksum(o: B.Octets) -> U32:
  checksum(B.Octets.to_list(o))

# the name of the archive's last entry
def Cpio.trailer_name() -> B.Octets:
  B.Octets.of_list(trailer.name())

def Cpio.is_trailer_name(name: B.Octets) -> Bool:
  trailer.is(B.Octets.to_list(name))

# a file entry with the usual defaults: inode 0, one link, owner 0, time 0
def CpioEntry.file(name: String, mode: U32, data: B.Octets) -> CpioEntry:
  CpioEntry{0, mode, 0, 0, 1, 0, 0, 0, 0, 0, B.Octets.of_string(name), data}

def CpioEntry.name_string(e: CpioEntry) -> String:
  match e:
    case CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}:
      B.Octets.to_string(name)

def trailer.entry() -> CpioEntry:
  CpioEntry{0, 0, 0, 0, 1, 0, 0, 0, 0, 0, Cpio.trailer_name(), B.Octets.empty()}

def entry.check(fmt: CpioFormat, data: B.Octets) -> U32:
  match fmt:
    case CpioNewc{}:
      0
    case CpioCrc{}:
      Cpio.checksum(data)

# the header an entry is written with
def CpioEntry.header(+fmt: CpioFormat, e: CpioEntry) -> CpioHeader:
  match e:
    case CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, +data}:
      CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, size32(1n+B.len(B.Octets.to_list(name))), entry.check(fmt, data)}

# one entry's bytes (header, name, NUL, padding, data, padding), then rest
def entry.onto(+fmt: CpioFormat, e: CpioEntry, rest: B.Octets) -> B.Octets:
  match e:
    case CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      B.Octets.append(CpioHeader.encode(CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, size32(1n+B.len(B.Octets.to_list(name))), entry.check(fmt, data)}), B.Octets.append(name, B.Octets.append(B.Octets.cons(0, B.Octets.zeros(pad4(Nat.add(111n, B.len(B.Octets.to_list(name)))))), B.Octets.append(data, B.Octets.append(B.Octets.zeros(pad4(B.len(B.Octets.to_list(data)))), rest)))))

# an archive in format fmt: the entries, then the trailer
def Cpio.build(+fmt: CpioFormat, es: List<&2, CpioEntry>) -> B.Octets:
  match es:
    case Nil{}:
      entry.onto(fmt, trailer.entry(), B.Octets.empty())
    case Con{e, t}:
      entry.onto(fmt, e, Cpio.build(fmt, t))

# the entries of an archive in either format, up to its trailer; bytes after
# the trailer's name are ignored (an initramfs may pad the archive)
def Cpio.parse(+o: B.Octets) -> Result<&2, &2, CpioError, List<&2, CpioEntry>>:
  parse.go(B.len(B.Octets.to_list(o)), entry.read(B.Octets.to_list(o)))

# The entries Cpio.build can hold, so that Cpio.parse gives them back: the
# data, and the name with its NUL, fit in a 32-bit size field; the name is
# not the trailer's.
def CpioEntry.valid(e: CpioEntry) -> Type:
  match e:
    case CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      {size.over(B.len(B.Octets.to_list(data))) == 0n : Nat} & {size.over(1n+B.len(B.Octets.to_list(name))) == 0n : Nat} & {Cpio.is_trailer_name(name) == False{} : Bool}

def CpioEntry.valid_all(es: List<&2, CpioEntry>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{e, t}:
      CpioEntry.valid(e) & CpioEntry.valid_all(t)
