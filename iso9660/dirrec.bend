# bend-osdev-iso9660, dirrec.bend: directory records (ECMA-119, 4th edition,
# 9.1). A record is:
#   0       length of the record (LEN_DR)
#   1       extended attribute record length
#   2..9    location of the extent (both-endian 32)
#   10..17  data length (both-endian 32)
#   18..24  recording date and time (7 bytes)
#   25      file flags (bit 0 hidden, 1 directory, 2 associated file,
#           3 record format, 4 protection, 7 multi-extent)
#   26      file unit size (interleave)
#   27      interleave gap size
#   28..31  volume sequence number (both-endian 16)
#   32      length of the file identifier (LEN_FI)
#   33..    the file identifier, a zero byte if LEN_FI is even, then the
#           system use area up to LEN_DR
# A directory's first two records are its own ("\0") and its parent's
# ("\1"). Records never cross a logical sector boundary.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./fields.bend as F

type IsoDirRec is Data:
  IsoDirRec{ext_attr: U32, extent: U32, size: U32, date: F.IsoDirDate, flags: U32, unit_size: U32, gap: U32, vol_seq: U32, ident: B.Octets, system_use: B.Octets}

# the identifier and system use area of a record
type IsoDirRecTail is Data:
  IsoDirRecTail{ident: B.Octets, system_use: B.Octets}

# Lengths

# the padding byte after an identifier of n bytes: one if n is even
def iso.pad(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n:
      0n
    case 2n+p:
      iso.pad(p)

# the bytes before the system use area, for an identifier of n bytes
def iso.fixed(+n: Nat) -> Nat:
  Nat.add(33n, Nat.add(n, iso.pad(n)))

def iso.olen(o: B.Octets) -> Nat:
  B.len(B.Octets.to_list(o))

# the record's length, LEN_DR
def IsoDirRec.length(r: IsoDirRec) -> Nat:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      Nat.add(iso.fixed(iso.olen(id)), iso.olen(su))

# the records this package writes and reads back: a non-empty identifier,
# and a length that fits LEN_DR's byte
def IsoDirRec.fits(+r: IsoDirRec) -> Bool:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      Bool.and(Nat.is_le(1n, iso.olen(id)), Nat.is_lt(IsoDirRec.length(r), 256n))

# the record as stored: bytes to 8 bits, the sequence number to 16
def IsoDirRec.norm(r: IsoDirRec) -> IsoDirRec:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      IsoDirRec{B.byte(ea), ex, sz, F.IsoDirDate.norm(dt), B.byte(fl), B.byte(us), B.byte(gp), B.low16(vs), id, su}

# Writing a record

def iso.dirrec.header(r: IsoDirRec, t: Nat, n: Nat) -> List<&2, U32>:
  match r:
    case IsoDirRec{ea, +ex, +sz, dt, fl, us, gp, +vs, id, su}:
      Con{U32.from_nat(t), Con{ea, B.append(B.le32(ex), B.append(B.be32(ex), B.append(B.le32(sz), B.append(B.be32(sz), B.append(F.IsoDirDate.bytes(dt), Con{fl, Con{us, Con{gp, B.append(B.le16(vs), B.append(B.be16(vs), [U32.from_nat(n)]))}}})))))}}

def iso.dirrec.body(id: B.Octets, +n: Nat, su: B.Octets) -> List<&2, U32>:
  B.append(B.Octets.to_list(id), B.append(B.zeros(iso.pad(n)), B.Octets.to_list(su)))

# the record's bytes; LEN_DR and LEN_FI are taken modulo 256
def IsoDirRec.encode(+r: IsoDirRec) -> B.Octets:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, +id, +su}:
      +n = iso.olen(id)
      B.Octets.of_list(B.append(iso.dirrec.header(r, IsoDirRec.length(r), n), iso.dirrec.body(id, n, su)))

# Reading a record

# the element at offset i, as it is (the list holds bytes already)
def iso.at.head(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{h, t}:
      Some{h}
    case Nil{}:
      None{}

def iso.at(xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  iso.at.head(B.drop(i, xs))

def iso.dirrec.su(ok: Bool, id: List<&2, U32>, su: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRecTail>:
  match ok:
    case True{}:
      Done{IsoDirRecTail{B.Octets.of_list(id), B.Octets.of_list(su)}}
    case False{}:
      Fail{F.IsoTruncated{}}

def iso.dirrec.ident(ok: Bool, +id: List<&2, U32>, +sulen: Nat, after: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRecTail>:
  match ok:
    case True{}:
      +su = B.take(sulen, after)
      iso.dirrec.su(Nat.is_eq(B.len(su), sulen), id, su)
    case False{}:
      Fail{F.IsoTruncated{}}

def iso.dirrec.room(ok: Bool, +len_dr: Nat, +n: Nat, +body: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRecTail>:
  match ok:
    case True{}:
      +id = B.take(n, body)
      iso.dirrec.ident(Nat.is_eq(B.len(id), n), id, Nat.sub(len_dr, iso.fixed(n)), B.drop(iso.pad(n), B.drop(n, body)))
    case False{}:
      Fail{F.IsoBadRecordLength{len_dr}}

def iso.dirrec.named(ok: Bool, +len_dr: Nat, +n: Nat, body: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRecTail>:
  match ok:
    case True{}:
      iso.dirrec.room(Nat.is_le(iso.fixed(n), len_dr), len_dr, n, body)
    case False{}:
      Fail{F.IsoBadIdentifierLength{n}}

# the identifier and system use area of a record of length len_dr whose
# identifier has n bytes, from the bytes after its 33-byte header
def iso.dirrec.tail(+len_dr: Nat, +n: Nat, body: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRecTail>:
  iso.dirrec.named(Nat.is_le(1n, n), len_dr, n, body)

def IsoDirRec.of_tail(a: U32, e: U32, s: U32, d: F.IsoDirDate, f: U32, u: U32, g: U32, v: U32, tl: IsoDirRecTail) -> IsoDirRec:
  match tl:
    case IsoDirRecTail{id, su}:
      IsoDirRec{a, e, s, d, f, u, g, v, id, su}

def iso.dirrec.tail.m(len_dr: Maybe<&2, U32>, n: Maybe<&2, U32>, body: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRecTail>:
  match len_dr n:
    case Some{l} Some{k}:
      iso.dirrec.tail(U32.to_nat(l), U32.to_nat(k), body)
    case _ _:
      Fail{F.IsoTruncated{}}

def iso.dirrec.build(ea: Maybe<&2, U32>, ex: Result<&2, &2, F.IsoError, U32>, sz: Result<&2, &2, F.IsoError, U32>, dt: Result<&2, &2, F.IsoError, F.IsoDirDate>, fl: Maybe<&2, U32>, us: Maybe<&2, U32>, gp: Maybe<&2, U32>, vs: Result<&2, &2, F.IsoError, U32>, tl: Result<&2, &2, F.IsoError, IsoDirRecTail>) -> Result<&2, &2, F.IsoError, IsoDirRec>:
  match ea fl us gp:
    case Some{a} Some{f} Some{u} Some{g}:
      do Result<&2, &2, F.IsoError, IsoDirRec>:
        e : U32 <- ex
        s : U32 <- sz
        d : F.IsoDirDate <- dt
        v : U32 <- vs
        t : IsoDirRecTail <- tl
        return IsoDirRec.of_tail(a, e, s, d, f, u, g, v, t)
    case _ _ _ _:
      Fail{F.IsoTruncated{}}

# a record at the head of xs (the bytes of a sector from the record on)
def iso.dirrec.list(mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoDirRec>:
  +m = mode
  iso.dirrec.build(iso.at(xs, 1n), F.iso.both32.list(m, B.drop(2n, xs), 2n), F.iso.both32.list(m, B.drop(10n, xs), 10n), F.iso.dirdate.list(B.drop(18n, xs)), iso.at(xs, 25n), iso.at(xs, 26n), iso.at(xs, 27n), F.iso.both16.list(m, B.drop(28n, xs), 28n), iso.dirrec.tail.m(iso.at(xs, 0n), iso.at(xs, 32n), B.drop(33n, xs)))

# the record at the start of o (any bytes may follow it)
def IsoDirRec.decode(mode: F.IsoEndian, o: B.Octets) -> Result<&2, &2, F.IsoError, IsoDirRec>:
  iso.dirrec.list(mode, B.Octets.to_list(o))

# Flags and identifiers

def iso.bit(+flags: U32, mask: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(mask, flags), 0))

def IsoDirRec.flags_of(r: IsoDirRec) -> U32:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      fl

def IsoDirRec.is_hidden(r: IsoDirRec) -> Bool:
  iso.bit(IsoDirRec.flags_of(r), 1)

def IsoDirRec.is_dir(r: IsoDirRec) -> Bool:
  iso.bit(IsoDirRec.flags_of(r), 2)

def IsoDirRec.is_associated(r: IsoDirRec) -> Bool:
  iso.bit(IsoDirRec.flags_of(r), 4)

# more records of the same file follow (multi-extent)
def IsoDirRec.is_multi_extent(r: IsoDirRec) -> Bool:
  iso.bit(IsoDirRec.flags_of(r), 128)

def IsoDirRec.extent_of(r: IsoDirRec) -> U32:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      ex

def IsoDirRec.size_of(r: IsoDirRec) -> U32:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      sz

def IsoDirRec.ident_of(r: IsoDirRec) -> B.Octets:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      id

def IsoDirRec.system_use_of(r: IsoDirRec) -> B.Octets:
  match r:
    case IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      su

def iso.ident.is(xs: List<&2, U32>, v: U32) -> Bool:
  match xs:
    case Con{h, Nil{}}:
      U32.is_eq(h, v)
    case _:
      False{}

# the record of the directory itself ("\0") or of its parent ("\1")
def IsoDirRec.is_self(r: IsoDirRec) -> Bool:
  iso.ident.is(B.Octets.to_list(IsoDirRec.ident_of(r)), 0)

def IsoDirRec.is_parent(r: IsoDirRec) -> Bool:
  iso.ident.is(B.Octets.to_list(IsoDirRec.ident_of(r)), 1)

# the logical blocks an extent of size bytes takes
def iso.blocks.up(part: Bool, n: Nat) -> Nat:
  match part:
    case True{}:
      1n+n
    case False{}:
      n

def Iso.blocks(+size: U32) -> Nat:
  iso.blocks.up(Bool.not(U32.is_eq(U32.and(2047, size), 0)), U32.to_nat(U32.shrn(size, 11n)))
