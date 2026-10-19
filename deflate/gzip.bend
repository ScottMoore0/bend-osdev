# bend-osdev-deflate: the gzip format (RFC 1952): members, each a header, a
# raw DEFLATE stream, the CRC-32 of the data and its size modulo 2^32.
#
# RFC 1952, 2.2: "The members simply appear one after another in the file".
# 2.3.1: ID1 = 31, ID2 = 139; CM = 8; FLG's bits FTEXT, FHCRC, FEXTRA,
# FNAME, FCOMMENT ("Reserved FLG bits must be zero"); MTIME, XFL ("XFL = 2 -
# compressor used maximum compression, slowest algorithm"; "XFL = 4 -
# compressor used fastest algorithm"), OS ("255 - unknown"); the optional
# fields in that order: XLEN and the extra field, the zero-terminated name and
# comment, and a CRC16 ("the two least significant bytes of the CRC32 for all
# bytes of the gzip header up to and not including the CRC16"); then CRC32
# and ISIZE ("the size of the original (uncompressed) input data modulo
# 2^32"), least significant byte first (2.1). 2.3.1.2: a decompressor must
# check ID1, ID2 and CM and "give an error indication if any reserved bit is
# non-zero".
#
# CRC-32 is bend-osdev-crc's (the ISO-HDLC parameters, table-driven).
#
# What the RFC leaves open, decided as the gzip tool (gzip 1.12, as a black
# box) decides it: the header's CRC16 is checked when FHCRC is set; after a
# member, nothing, or nothing but zero bytes, ends the file; one more byte
# alone is a truncated member; ID1 ID2 start another member; anything else
# is trailing garbage, ignored (or refused with InflateOptions' ignore
# False); an empty file is truncated.
import Base
import ../bytes/bytes.bend as B
import ../crc/crc.bend as CR
import ../crc/table.bend as CT
import ./error.bend as E
import ./eq.bend as Q
import ./window.bend as W
import ./inflate.bend as I
import ./deflate.bend as D

# the CRC-32 gzip stores (2.3.1, CRC32: "computed according to CRC-32
# algorithm used in the ISO 3309 standard and in section 8.1.1.6.2 of ITU-T
# recommendation V.42"; bend-osdev-crc's crc32 parameters, table-driven)

def gzip_crc32(o: B.Octets) -> U32:
  CT.Crc32Spec.compute_fast(CR.crc32.spec(), o)

def gz.crc32(o: B.Octets) -> U32:
  gzip_crc32(o)

# The header

# text: FTEXT; mtime: MTIME; xfl: XFL; os: OS; extra, name, comment: the
# optional fields (a name or comment stops at its first zero byte); hcrc:
# whether to write the header's CRC16
type GzipHeader is Data:
  GzipHeader{text: Bool, mtime: U32, xfl: U32, os: U32, extra: Maybe<&2, B.Octets>, name: Maybe<&2, B.Octets>, comment: Maybe<&2, B.Octets>, hcrc: Bool}

# no time stamp, XFL 0, OS 255 (unknown), no optional fields
def GzipHeader.default() -> GzipHeader:
  GzipHeader{False{}, 0, 0, 255, None{}, None{}, None{}, False{}}

type GzipOptions is Data:
  GzipOptions{deflate: D.DeflateOptions, header: GzipHeader}

def gz.xfl.at(max: Bool, fast: Bool) -> U32:
  match max:
    case True{}:
      2
    case False{}:
      match fast:
        case True{}:
          4
        case False{}:
          0

# level l (0 to 9): XFL 2 at level 9, 4 at level 1, else 0 (as the gzip
# tool writes)
def GzipOptions.level(+l: U32) -> GzipOptions:
  GzipOptions{D.DeflateOptions.level(l), GzipHeader{False{}, 0, gz.xfl.at(U32.is_eq(l, 9), U32.is_eq(l, 1)), 255, None{}, None{}, None{}, False{}}}

def GzipOptions.default() -> GzipOptions:
  GzipOptions{D.DeflateOptions.default(), GzipHeader.default()}

def gz.bit(b: Bool, +v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

def gz.has(m: Maybe<&2, B.Octets>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def gz.push_if(ok: Bool, +h: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      Con{h, acc}
    case False{}:
      acc

# the bytes up to the first zero byte (live: none seen yet)
def gz.cstr(xs: List<&2, U32>, live: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      B.rev(acc)
    case Con{+h, t}:
      match live:
        case True{}:
          +nz = U32.is_ne(B.byte(h), 0)
          gz.cstr(t, nz, gz.push_if(nz, B.byte(h), acc))
        case False{}:
          B.rev(acc)

def gz.opt.extra(m: Maybe<&2, B.Octets>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      +xs = B.take.fast(65535n, B.Octets.to_list(x))
      B.append.fast(B.le16(U32.from_nat(B.len.fast(xs))), xs)

def gz.opt.str(m: Maybe<&2, B.Octets>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      B.append.fast(gz.cstr(B.Octets.to_list(x), True{}, Nil{}), [0])

def gz.hcrc(on: Bool, +xs: List<&2, U32>) -> List<&2, U32>:
  match on:
    case True{}:
      B.append.fast(xs, B.le16(gz.crc32(B.Octets.of_list(xs))))
    case False{}:
      xs

# a member's header bytes (2.3.1)
def gzip_header_bytes(h: GzipHeader) -> List<&2, U32>:
  match h:
    case GzipHeader{text, mtime, xfl, os, +extra, +name, +comment, +hcrc}:
      +flg = U32.or(U32.or(gz.bit(text, 1), gz.bit(hcrc, 2)), U32.or(U32.or(gz.bit(gz.has(extra), 4), gz.bit(gz.has(name), 8)), gz.bit(gz.has(comment), 16)))
      +fixed = B.append.fast([31, 139, 8, flg], B.append.fast(B.le32(mtime), [B.byte(xfl), B.byte(os)]))
      gz.hcrc(hcrc, B.append.fast(fixed, B.append.fast(gz.opt.extra(extra), B.append.fast(gz.opt.str(name), gz.opt.str(comment)))))

# The writer

# o as one gzip member
def gzip_compress_with(go: GzipOptions, +o: B.Octets) -> B.Octets:
  match go:
    case GzipOptions{dopts, h}:
      B.Octets.append(B.Octets.of_list(gzip_header_bytes(h)), B.Octets.append(D.deflate_with(dopts, o), B.Octets.append(B.Octets.le32(gz.crc32(o)), B.Octets.le32(U32.from_nat(B.Octets.len(o))))))

def gzip_compress(+o: B.Octets) -> B.Octets:
  gzip_compress_with(GzipOptions.default(), o)

# The reader: a member's header

# how many bytes up to and including the first zero (live: none seen yet)
def gz.zlen(xs: List<&2, U32>, live: Bool, n: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      match live:
        case True{}:
          None{}
        case False{}:
          Some{n}
    case Con{h, t}:
      match live:
        case True{}:
          gz.zlen(t, U32.is_ne(B.byte(h), 0), 1n+n)
        case False{}:
          Some{n}

# a header parsed so far: n bytes of it, and the rest of the input
type DflGzHead is Data:
  DflGzHead{n: Nat, rest: List<&2, U32>}

def gz.skip.n(ok: Bool, +k: Nat, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match ok:
    case True{}:
      Done{DflGzHead{Nat.add(n, k), B.drop(k, xs)}}
    case False{}:
      Fail{E.DeflateTruncated{}}

def gz.skip(m: Maybe<&2, Nat>, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match m:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{+k}:
      gz.skip.n(Nat.is_le(k, B.len.fast(xs)), k, n, xs)

def gz.xlen(m: Maybe<&2, U32>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      Some{4294967295n}
    case Some{v}:
      Some{Nat.add(2n, U32.to_nat(v))}

def gz.field(on: Bool, r: Result<&2, &2, E.DeflateError, DflGzHead>, zero: Bool) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match on:
    case False{}:
      r
    case True{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{DflGzHead{+n, +xs}}:
          match zero:
            case True{}:
              gz.skip(gz.zlen(xs, True{}, 0n), n, xs)
            case False{}:
              gz.skip(gz.xlen(B.le16_at(xs, 0n)), n, xs)

def gz.crc16.ok(ok: Bool, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match ok:
    case True{}:
      Done{DflGzHead{Nat.add(n, 2n), B.drop(2n, xs)}}
    case False{}:
      Fail{E.DeflateGzipBadHeaderCrc{}}

def gz.crc16.at(m: Maybe<&2, U32>, +c: U32, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match m:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{v}:
      gz.crc16.ok(Q.eq.u32(v, B.low16(c)), n, xs)

def gz.crc16(on: Bool, +all: List<&2, U32>, r: Result<&2, &2, E.DeflateError, DflGzHead>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match on:
    case False{}:
      r
    case True{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{DflGzHead{+n, +xs}}:
          gz.crc16.at(B.le16_at(xs, 0n), gz.crc32(B.Octets.of_list(B.take.fast(n, all))), n, xs)

def gz.flag(+flg: U32, +m: U32) -> Bool:
  U32.is_eq(U32.and(flg, m), m)

# the optional fields, after the 10 fixed bytes
def gz.opts(+flg: U32, +all: List<&2, U32>, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  gz.crc16(gz.flag(flg, 2), all, gz.field(gz.flag(flg, 16), gz.field(gz.flag(flg, 8), gz.field(gz.flag(flg, 4), Done{DflGzHead{10n, xs}}, False{}), True{}), True{}))

def gz.head.flg(ok: Bool, +flg: U32, +all: List<&2, U32>, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match ok:
    case True{}:
      gz.opts(flg, all, xs)
    case False{}:
      Fail{E.DeflateGzipReservedFlags{}}

def gz.head.cm(ok: Bool, +flg: U32, +all: List<&2, U32>, +xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match ok:
    case True{}:
      gz.head.flg(U32.is_eq(U32.and(flg, 224), 0), flg, all, xs)
    case False{}:
      Fail{E.DeflateGzipBadMethod{}}

def gz.head.magic(ok: Bool, +all: List<&2, U32>, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match ok:
    case False{}:
      Fail{E.DeflateGzipBadMagic{}}
    case True{}:
      match xs:
        case Con{a, Con{b, Con{+cm, Con{+flg, Con{t0, Con{t1, Con{t2, Con{t3, Con{x, Con{o, rest}}}}}}}}}}:
          gz.head.cm(U32.is_eq(cm, 8), flg, all, rest)
        case _:
          Fail{E.DeflateTruncated{}}

def gz.head.of(+all: List<&2, U32>, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  match xs:
    case Con{+a, Con{+b, t}}:
      gz.head.magic(Bool.and(U32.is_eq(a, 31), U32.is_eq(b, 139)), all, all)
    case _:
      Fail{E.DeflateTruncated{}}

# a member's header at the start of xs: its length and what follows
def gz.head(+xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflGzHead>:
  gz.head.of(xs, xs)

# The reader: a member's data and trailer

# a member's output, and the input after it
type DflGzMember is Data:
  DflGzMember{out: B.Octets, rest: List<&2, U32>}

def gz.size.ok(ok: Bool, +out: B.Octets, +rest: B.Octets) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match ok:
    case True{}:
      Done{DflGzMember{out, B.Octets.to_list(rest)}}
    case False{}:
      Fail{E.DeflateGzipBadSize{}}

def gz.size.at(m: Maybe<&2, U32>, +out: B.Octets, +rest: B.Octets) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match m:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{v}:
      gz.size.ok(Q.eq.u32(v, U32.from_nat(B.Octets.len(out))), out, rest)

def gz.size(s: Maybe<&2, B.OctetsSplit>, +out: B.Octets) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match s:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{B.OctetsSplit{f, rest}}:
      gz.size.at(B.Octets.le32_at(f, 0n), out, rest)

def gz.crc.ok(ok: Bool, +out: B.Octets, +rest: B.Octets) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match ok:
    case True{}:
      gz.size(B.Octets.split_at(4n, rest), out)
    case False{}:
      Fail{E.DeflateGzipBadCrc{}}

def gz.crc.at(m: Maybe<&2, U32>, +out: B.Octets, +rest: B.Octets) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match m:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{v}:
      gz.crc.ok(Q.eq.u32(v, gz.crc32(out)), out, rest)

# CRC32 and ISIZE, after the data, four bytes each
def gz.trailer(s: Maybe<&2, B.OctetsSplit>, +out: B.Octets) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match s:
    case None{}:
      Fail{E.DeflateTruncated{}}
    case Some{B.OctetsSplit{f, rest}}:
      gz.crc.at(B.Octets.le32_at(f, 0n), out, rest)

def gz.body(r: Result<&2, &2, E.DeflateError, I.DflOutRest>) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{I.DflOutRest{+out, rest}}:
      gz.trailer(B.Octets.split_at(4n, B.Octets.of_list(rest)), out)

def gz.member.of(h: Result<&2, &2, E.DeflateError, DflGzHead>, +room: Nat) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  match h:
    case Fail{e}:
      Fail{e}
    case Done{DflGzHead{n, rest}}:
      gz.body(I.inf.run.out(W.win.empty(), room, rest))

# one member at the start of xs, its output at most room bytes
def gz.member(+xs: List<&2, U32>, +room: Nat) -> Result<&2, &2, E.DeflateError, DflGzMember>:
  gz.member.of(gz.head(xs), room)

# The reader: the members one after another

def gz.zeros(xs: List<&2, U32>, all: Bool) -> Bool:
  match xs:
    case Nil{}:
      all
    case Con{h, t}:
      gz.zeros(t, Bool.and(all, U32.is_eq(h, 0)))

def gz.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# what follows a member (2.2, and the gzip tool): 0 the end, 1 another
# member, 2 a truncated member, 3 trailing garbage
def gz.next(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{+a, t}:
      match t:
        case Nil{}:
          gz.sel(U32.is_eq(a, 0), 0, 2)
        case Con{+b, +u}:
          gz.sel(Bool.and(U32.is_eq(a, 31), U32.is_eq(b, 139)), 1, gz.sel(gz.zeros(Con{a, Con{b, u}}, True{}), 0, 3))

# the loop's state: the input left, the room left, the output so far
type DflGz is Data:
  DflGzGo{xs: List<&2, U32>, room: Nat, out: B.Octets}
  DflGzEnd{r: Result<&2, &2, E.DeflateError, B.Octets>}

def gz.after.pick(end: Bool, more: Bool, cut: Bool, ignore: Bool, +rest: List<&2, U32>, +room: Nat, +out: B.Octets) -> DflGz:
  match end:
    case True{}:
      DflGzEnd{Done{out}}
    case False{}:
      match more:
        case True{}:
          DflGzGo{rest, room, out}
        case False{}:
          match cut:
            case True{}:
              DflGzEnd{Fail{E.DeflateTruncated{}}}
            case False{}:
              match ignore:
                case True{}:
                  DflGzEnd{Done{out}}
                case False{}:
                  DflGzEnd{Fail{E.DeflateTrailingData{}}}

def gz.after.at(+k: U32, +ignore: Bool, +rest: List<&2, U32>, +room: Nat, +out: B.Octets) -> DflGz:
  gz.after.pick(U32.is_eq(k, 0), U32.is_eq(k, 1), U32.is_eq(k, 2), ignore, rest, room, out)

def gz.step.of(r: Result<&2, &2, E.DeflateError, DflGzMember>, +ignore: Bool, +room: Nat, +out: B.Octets) -> DflGz:
  match r:
    case Fail{e}:
      DflGzEnd{Fail{e}}
    case Done{DflGzMember{+o, +rest}}:
      gz.after.at(gz.next(rest), ignore, rest, Nat.sub(room, B.Octets.len(o)), B.Octets.append(out, o))

def gz.step(s: DflGz, +ignore: Bool) -> DflGz:
  match s:
    case DflGzGo{+xs, +room, out}:
      gz.step.of(gz.member(xs, room), ignore, room, out)
    case DflGzEnd{r}:
      DflGzEnd{r}

def gz.loop(fuel: Nat, s: DflGz, +ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match fuel:
    case 0n:
      match s:
        case DflGzGo{xs, room, out}:
          Done{out}
        case DflGzEnd{r}:
          r
    case 1n+f:
      match s:
        case DflGzGo{xs, room, out}:
          gz.loop(f, gz.step(DflGzGo{xs, room, out}, ignore), ignore)
        case DflGzEnd{r}:
          r

def gz.guard.ok(ok: Bool, +o: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match ok:
    case True{}:
      Done{o}
    case False{}:
      Fail{E.DeflateOutputTooLarge{}}

def gz.guard(r: Result<&2, &2, E.DeflateError, B.Octets>, +max: U32) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+o}:
      gz.guard.ok(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)

def gz.run(+xs: List<&2, U32>, +max: U32, +ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  gz.guard(gz.loop(Nat.add(2n, B.len.fast(xs)), DflGzGo{xs, U32.to_nat(max), B.Octets.empty()}, ignore), max)

# the data of every member of the gzip file src, joined
def gzip_decompress_with(opts: I.InflateOptions, src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match opts:
    case I.InflateOptions{max, dict, ignore}:
      gz.run(B.Octets.to_list(src), max, ignore)

def gzip_decompress(src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  gzip_decompress_with(I.InflateOptions.default(), src)

# The streaming writer: the header with the first bytes; CRC32 and ISIZE,
# kept as the data comes in, at the end

def gz.spec() -> CR.Crc32Spec:
  CR.crc32.spec()

type GzipWriter is Data:
  GzipWriter{d: D.Deflater, crc: U32, size: U32, head: List<&2, U32>}

type DflGzipWritten is Data:
  DflGzipWritten{writer: GzipWriter, bytes: B.Octets}

def gzip_start(go: GzipOptions) -> GzipWriter:
  match go:
    case GzipOptions{dopts, h}:
      GzipWriter{D.deflate_start(dopts), CR.Crc32Spec.start(gz.spec()), 0, gzip_header_bytes(h)}

def gz.fed(r: D.DflDeflated, +crc: U32, +size: U32, head: List<&2, U32>) -> DflGzipWritten:
  match r:
    case D.DflDeflated{d, bytes}:
      DflGzipWritten{GzipWriter{d, crc, size, Nil{}}, B.Octets.append(B.Octets.of_list(head), bytes)}

# more data: answers the bytes it completes
def gzip_feed(w: GzipWriter, +o: B.Octets) -> DflGzipWritten:
  match w:
    case GzipWriter{d, crc, size, head}:
      gz.fed(D.deflate_feed(d, o), CT.Crc32Spec.update_fast(gz.spec(), crc, o), U32.add(size, U32.from_nat(B.Octets.len(o))), head)

# the end of the data: the rest of the member
def gzip_finish(w: GzipWriter) -> B.Octets:
  match w:
    case GzipWriter{d, crc, size, head}:
      B.Octets.append(B.Octets.of_list(head), B.Octets.append(D.deflate_finish(d), B.Octets.append(B.Octets.le32(CR.Crc32Spec.finish(gz.spec(), crc)), B.Octets.le32(size))))

# The streaming reader: each member's header (held until it is whole), its
# data through an inflater, its trailer (held until its 8 bytes are in);
# between members, the bytes that follow one, until they show what they are

# max, ignore: as InflateOptions'
type DflGzCfg is Data:
  DflGzCfg{max: U32, ignore: Bool}

type GzipInflater is Data:
  # before a member's header: the bytes so far; room: the output still
  # allowed; first: no member yet
  GzipInHead{buf: List<&2, U32>, room: Nat, first: Bool, cfg: DflGzCfg}
  # a member's data: its CRC-32 register and size so far
  GzipInBody{inf: I.Inflater, crc: U32, size: U32, cfg: DflGzCfg}
  # a member's trailer: the bytes after its data so far
  GzipInTrail{buf: List<&2, U32>, room: Nat, crc: U32, size: U32, cfg: DflGzCfg}
  # after a member: the bytes after it so far
  GzipInAfter{buf: List<&2, U32>, room: Nat, cfg: DflGzCfg}
  # the file has ended (what follows is ignored)
  GzipInDone{}
  GzipInBad{e: E.DeflateError}

type DflGzipFed is Data:
  DflGzipFed{inflater: GzipInflater, out: B.Octets}

def gzip_inflate_start(opts: I.InflateOptions) -> GzipInflater:
  match opts:
    case I.InflateOptions{+max, dict, ignore}:
      GzipInHead{Nil{}, U32.to_nat(max), True{}, DflGzCfg{max, ignore}}

# A step: from one state to the next, with the output it gives (moved: it
# did something; when not, more input is needed)
type DflGzStep is Data:
  DflGzStep{st: GzipInflater, out: List<&2, B.Octets>, moved: Bool}

def gz.s.body(r: I.DflFed, +crc: U32, +size: U32, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match r:
    case I.DflFed{i, +o}:
      DflGzStep{GzipInBody{i, CT.Crc32Spec.update_fast(gz.spec(), crc, o), U32.add(size, U32.from_nat(B.Octets.len(o))), cfg}, Con{o, out}, True{}}

def gz.s.wait(e: E.DeflateError, +st: GzipInflater, out: List<&2, B.Octets>) -> DflGzStep:
  match e:
    case E.DeflateTruncated{}:
      DflGzStep{st, out, False{}}
    case _:
      DflGzStep{GzipInBad{e}, out, True{}}

def gz.s.head(r: Result<&2, &2, E.DeflateError, DflGzHead>, +buf: List<&2, U32>, +room: Nat, +first: Bool, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match r:
    case Fail{e}:
      gz.s.wait(e, GzipInHead{buf, room, first, cfg}, out)
    case Done{DflGzHead{n, rest}}:
      match cfg:
        case DflGzCfg{+max, ignore}:
          gz.s.body(I.inflate_feed(I.inf.start(W.win.empty(), room, max, ignore), B.Octets.of_list(rest)), CR.Crc32Spec.start(gz.spec()), 0, DflGzCfg{max, ignore}, out)

def gz.s.ended(done: Bool, +i: I.Inflater, +crc: U32, +size: U32, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match done:
    case True{}:
      DflGzStep{GzipInTrail{I.inflate_rest(i), I.inflate_room(i), crc, size, cfg}, out, True{}}
    case False{}:
      DflGzStep{GzipInBody{i, crc, size, cfg}, out, False{}}

def gz.s.size(ok: Bool, +rest: List<&2, U32>, +room: Nat, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match ok:
    case True{}:
      DflGzStep{GzipInAfter{rest, room, cfg}, out, True{}}
    case False{}:
      DflGzStep{GzipInBad{E.DeflateGzipBadSize{}}, out, True{}}

def gz.s.crc(ok: Bool, +buf: List<&2, U32>, +room: Nat, +size: U32, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match ok:
    case True{}:
      gz.s.size(Q.eq.u32(Maybe.default(&2, U32, B.le32_at(buf, 4n), 0), size), B.drop(8n, buf), room, cfg, out)
    case False{}:
      DflGzStep{GzipInBad{E.DeflateGzipBadCrc{}}, out, True{}}

def gz.s.trail(whole: Bool, +buf: List<&2, U32>, +room: Nat, +crc: U32, +size: U32, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match whole:
    case True{}:
      gz.s.crc(Q.eq.u32(Maybe.default(&2, U32, B.le32_at(buf, 0n), 0), CR.Crc32Spec.finish(gz.spec(), crc)), buf, room, size, cfg, out)
    case False{}:
      DflGzStep{GzipInTrail{buf, room, crc, size, cfg}, out, False{}}

def gz.s.after.at(more: Bool, garbage: Bool, +buf: List<&2, U32>, +room: Nat, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  match more:
    case True{}:
      DflGzStep{GzipInHead{buf, room, False{}, cfg}, out, True{}}
    case False{}:
      match garbage:
        case True{}:
          match cfg:
            case DflGzCfg{max, ignore}:
              match ignore:
                case True{}:
                  DflGzStep{GzipInDone{}, out, True{}}
                case False{}:
                  DflGzStep{GzipInBad{E.DeflateTrailingData{}}, out, True{}}
        case False{}:
          DflGzStep{GzipInAfter{buf, room, cfg}, out, False{}}

# after a member: another member, the end so far (zeros, or nothing yet),
# one byte (wait), or garbage
def gz.s.after(+k: U32, +buf: List<&2, U32>, +room: Nat, +cfg: DflGzCfg, out: List<&2, B.Octets>) -> DflGzStep:
  gz.s.after.at(U32.is_eq(k, 1), U32.is_eq(k, 3), buf, room, cfg, out)

def gz.step.in(st: GzipInflater, out: List<&2, B.Octets>) -> DflGzStep:
  match st:
    case GzipInHead{+buf, +room, +first, +cfg}:
      gz.s.head(gz.head(buf), buf, room, first, cfg, out)
    case GzipInBody{+i, +crc, +size, +cfg}:
      gz.s.ended(I.inflate_done(i), i, crc, size, cfg, out)
    case GzipInTrail{+buf, +room, +crc, +size, +cfg}:
      gz.s.trail(Nat.is_le(8n, B.len.fast(buf)), buf, room, crc, size, cfg, out)
    case GzipInAfter{+buf, +room, +cfg}:
      gz.s.after(gz.next(buf), buf, room, cfg, out)
    case GzipInDone{}:
      DflGzStep{GzipInDone{}, out, False{}}
    case GzipInBad{e}:
      DflGzStep{GzipInBad{e}, out, False{}}

# steps while they move on
def gz.advance(fuel: Nat, s: DflGzStep) -> DflGzStep:
  match fuel:
    case 0n:
      s
    case 1n+f:
      match s:
        case DflGzStep{st, out, moved}:
          match moved:
            case True{}:
              gz.advance(f, gz.step.in(st, out))
            case False{}:
              DflGzStep{st, out, False{}}

# the new bytes go where the state is
def gz.add(st: GzipInflater, o: B.Octets) -> DflGzStep:
  match st:
    case GzipInHead{buf, room, first, cfg}:
      DflGzStep{GzipInHead{B.append.fast(buf, B.Octets.to_list(o)), room, first, cfg}, Nil{}, True{}}
    case GzipInBody{i, crc, size, cfg}:
      gz.s.body(I.inflate_feed(i, o), crc, size, cfg, Nil{})
    case GzipInTrail{buf, room, crc, size, cfg}:
      DflGzStep{GzipInTrail{B.append.fast(buf, B.Octets.to_list(o)), room, crc, size, cfg}, Nil{}, True{}}
    case GzipInAfter{buf, room, cfg}:
      DflGzStep{GzipInAfter{B.append.fast(buf, B.Octets.to_list(o)), room, cfg}, Nil{}, True{}}
    case GzipInDone{}:
      DflGzStep{GzipInDone{}, Nil{}, False{}}
    case GzipInBad{e}:
      DflGzStep{GzipInBad{e}, Nil{}, False{}}

def gz.fed.of(s: DflGzStep) -> DflGzipFed:
  match s:
    case DflGzStep{st, out, moved}:
      DflGzipFed{st, B.Octets.concat(List.reverse(&2, B.Octets, out))}

# more of the file: answers the data it completes
def gzip_inflate_feed(z: GzipInflater, +o: B.Octets) -> DflGzipFed:
  gz.fed.of(gz.advance(Nat.add(4n, Nat.mul(3n, B.Octets.len(o))), gz.add(z, o)))

def gz.fin.head(r: Result<&2, &2, E.DeflateError, DflGzHead>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{h}:
      Fail{E.DeflateTruncated{}}

def gz.fin.after.at(end: Bool, garbage: Bool, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match end:
    case True{}:
      Done{B.Octets.empty()}
    case False{}:
      match garbage:
        case True{}:
          match ignore:
            case True{}:
              Done{B.Octets.empty()}
            case False{}:
              Fail{E.DeflateTrailingData{}}
        case False{}:
          Fail{E.DeflateTruncated{}}

def gz.fin.after(+k: U32, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  gz.fin.after.at(U32.is_eq(k, 0), U32.is_eq(k, 3), ignore)

def gz.fin.body(r: Result<&2, &2, E.DeflateError, I.DflInflated>) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Fail{E.DeflateTruncated{}}

def gz.cfg.ignore(c: DflGzCfg) -> Bool:
  match c:
    case DflGzCfg{max, ignore}:
      ignore

# the end of the file: what is left of the data (all of it has been handed
# out by the feeds), or the failure
def gzip_inflate_finish(z: GzipInflater) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match z:
    case GzipInHead{buf, room, first, cfg}:
      gz.fin.head(gz.head(buf))
    case GzipInBody{i, crc, size, cfg}:
      gz.fin.body(I.inflate_finish(i))
    case GzipInTrail{buf, room, crc, size, cfg}:
      Fail{E.DeflateTruncated{}}
    case GzipInAfter{+buf, room, cfg}:
      gz.fin.after(gz.next(buf), gz.cfg.ignore(cfg))
    case GzipInDone{}:
      Done{B.Octets.empty()}
    case GzipInBad{e}:
      Fail{e}
