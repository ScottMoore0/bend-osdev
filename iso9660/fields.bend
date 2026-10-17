# bend-osdev-iso9660, fields.bend: what every part of an ISO 9660 volume
# shares. The error type; both-endian numbers (ECMA-119, 4th edition, 7.2.3
# and 7.3.3: a number stored twice, least significant byte first and then
# most significant byte first); the two date formats (9.1.5: the 7-byte date
# of a directory record; 8.4.26.1: the 17-byte date of a volume descriptor);
# and identifiers (7.4: a- and d-characters, padded with spaces).
#
# The readers work on bytes as a list (B.Octets.to_list), so that reading at
# an offset walks the list once; the public defs take and answer Octets.
# Readers never re-mask an element: the list comes from Octets.to_list, whose
# elements are bytes already.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD

# Why a volume, a structure or a lookup was refused
type IsoError is Data:
  # the device refused a read
  IsoDev{error: BD.DevError}
  # the device's blocks are not 2048 bytes
  IsoBadBlockSize{size: Nat}
  # a volume descriptor without the standard identifier "CD001"
  IsoNotIso{sector: Nat}
  # a volume descriptor whose version is not 1 (2 for an enhanced one)
  IsoBadDescriptorVersion{sector: Nat}
  # the descriptor set ended without a primary volume descriptor
  IsoNoPrimary{}
  # more volume descriptors than IsoOptions.max_descriptors, with no terminator
  IsoNoTerminator{}
  # a logical block size other than 2048
  IsoBadLogicalBlockSize{size: U32}
  # the two halves of a both-endian field disagree (offset in its structure)
  IsoBothEndianMismatch{offset: Nat}
  # fewer bytes than a structure needs
  IsoTruncated{}
  # a 17-byte date with a byte that is not a digit
  IsoBadDate{}
  # a directory record whose length cannot hold its identifier
  IsoBadRecordLength{length: Nat}
  # a directory record whose identifier length is 0
  IsoBadIdentifierLength{length: Nat}
  # an extent past the end of the volume
  IsoExtentOutOfRange{block: U32}
  # a System Use entry shorter than 4 bytes or running past its area
  IsoBadSusp{}
  # a CE entry of the wrong length, or a continuation area outside its block
  IsoBadContinuation{}
  # more continuation areas than IsoOptions.max_continuations
  IsoContinuationLimit{}
  # a Rock Ridge entry too short for its fields (its signature)
  IsoBadRrip{sig: String}
  # a Joliet identifier of an odd number of bytes
  IsoBadJolietName{}
  # no entry of this name
  IsoNotFound{name: String}
  # a path component that is not a directory
  IsoNotDirectory{name: String}
  # a directory where a file was expected
  IsoIsDirectory{name: String}
  # a path deeper than IsoOptions.max_depth, or a relocation loop
  IsoDepthLimit{}
  # an interleaved file (file unit size not 0), which this reader does not read
  IsoInterleaved{}
  # an El Torito boot catalog whose validation entry is malformed
  IsoBadBootCatalog{}
  # Joliet naming was asked for, and the volume has no Joliet descriptor
  IsoNoJoliet{}
  # Rock Ridge naming was asked for, and the root has no SUSP/RRIP entries
  IsoNoRockRidge{}

def IsoError.show(e: IsoError) -> String:
  match e:
    case IsoDev{BD.DevOutOfRange{n}}:
      "device: block " ++ Nat.show(n) ++ " out of range"
    case IsoDev{BD.DevBadLength{a, b}}:
      "device: bad length"
    case IsoDev{BD.DevFailed{c}}:
      "device: failed " ++ U32.show(c)
    case IsoBadBlockSize{n}:
      "block size " ++ Nat.show(n) ++ " is not 2048"
    case IsoNotIso{n}:
      "no CD001 at sector " ++ Nat.show(n)
    case IsoBadDescriptorVersion{n}:
      "bad descriptor version at sector " ++ Nat.show(n)
    case IsoNoPrimary{}:
      "no primary volume descriptor"
    case IsoNoTerminator{}:
      "no descriptor set terminator"
    case IsoBadLogicalBlockSize{n}:
      "logical block size " ++ U32.show(n)
    case IsoBothEndianMismatch{n}:
      "both-endian halves differ at " ++ Nat.show(n)
    case IsoTruncated{}:
      "truncated"
    case IsoBadDate{}:
      "bad date"
    case IsoBadRecordLength{n}:
      "bad record length " ++ Nat.show(n)
    case IsoBadIdentifierLength{n}:
      "bad identifier length " ++ Nat.show(n)
    case IsoExtentOutOfRange{b}:
      "extent " ++ U32.show(b) ++ " out of range"
    case IsoBadSusp{}:
      "bad system use entry"
    case IsoBadContinuation{}:
      "bad continuation area"
    case IsoContinuationLimit{}:
      "too many continuation areas"
    case IsoBadRrip{s}:
      "bad rock ridge " ++ s
    case IsoBadJolietName{}:
      "bad joliet name"
    case IsoNotFound{s}:
      "not found: " ++ s
    case IsoNotDirectory{s}:
      "not a directory: " ++ s
    case IsoIsDirectory{s}:
      "is a directory: " ++ s
    case IsoDepthLimit{}:
      "too deep"
    case IsoInterleaved{}:
      "interleaved file"
    case IsoBadBootCatalog{}:
      "bad boot catalog"
    case IsoNoJoliet{}:
      "no joliet"
    case IsoNoRockRidge{}:
      "no rock ridge"

# Both-endian numbers: which half to believe

type IsoEndian is Data:
  # read both halves and refuse the field when they differ
  IsoEndianCheck{}
  # trust the least significant byte first half
  IsoEndianLittle{}
  # trust the most significant byte first half
  IsoEndianBig{}

def IsoEndian.default() -> IsoEndian:
  IsoEndianCheck{}

def iso.both.agree(eq: Bool, lo: U32, off: Nat) -> Result<&2, &2, IsoError, U32>:
  match eq:
    case True{}:
      Done{lo}
    case False{}:
      Fail{IsoBothEndianMismatch{off}}

def iso.both.pick(mode: IsoEndian, +lo: U32, +hi: U32, off: Nat) -> Result<&2, &2, IsoError, U32>:
  match mode:
    case IsoEndianCheck{}:
      iso.both.agree(U32.is_eq(lo, hi), lo, off)
    case IsoEndianLittle{}:
      Done{lo}
    case IsoEndianBig{}:
      Done{hi}

def iso.both.go(mode: IsoEndian, lo: Maybe<&2, U32>, hi: Maybe<&2, U32>, off: Nat) -> Result<&2, &2, IsoError, U32>:
  match lo hi:
    case Some{l} Some{h}:
      iso.both.pick(mode, l, h, off)
    case _ _:
      Fail{IsoTruncated{}}

# a both-endian 32-bit field at the head of xs (8 bytes); off names it in errors
def iso.both32.list(mode: IsoEndian, +xs: List<&2, U32>, off: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.both.go(mode, B.le32.head(xs), B.be32.head(B.drop(4n, xs)), off)

# a both-endian 16-bit field at the head of xs (4 bytes)
def iso.both16.list(mode: IsoEndian, +xs: List<&2, U32>, off: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.both.go(mode, B.le16.head(xs), B.be16.head(B.drop(2n, xs)), off)

def Iso.both32_encode_pair(lo: U32, hi: U32) -> B.Octets:
  B.Octets.of_list(B.append(B.le32(lo), B.be32(hi)))

def Iso.both32_encode(+v: U32) -> B.Octets:
  Iso.both32_encode_pair(v, v)

def Iso.both16_encode_pair(lo: U32, hi: U32) -> B.Octets:
  B.Octets.of_list(B.append(B.le16(lo), B.be16(hi)))

def Iso.both16_encode(+v: U32) -> B.Octets:
  Iso.both16_encode_pair(v, v)

# the both-endian 32-bit field at byte offset at of o
def Iso.both32_decode(mode: IsoEndian, o: B.Octets, +at: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.both32.list(mode, B.drop(at, B.Octets.to_list(o)), at)

def Iso.both16_decode(mode: IsoEndian, o: B.Octets, +at: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.both16.list(mode, B.drop(at, B.Octets.to_list(o)), at)

# Single-byte and single-endian fields at an offset of a list

def iso.need(-A: Data, m: Maybe<&2, A>) -> Result<&2, &2, IsoError, A>:
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{IsoTruncated{}}

def iso.u8(xs: List<&2, U32>, i: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.need(U32, B.at(xs, i))

def iso.le32(xs: List<&2, U32>, i: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.need(U32, B.le32_at(xs, i))

def iso.be32(xs: List<&2, U32>, i: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.need(U32, B.be32_at(xs, i))

def iso.le16(xs: List<&2, U32>, i: Nat) -> Result<&2, &2, IsoError, U32>:
  iso.need(U32, B.le16_at(xs, i))

# n bytes at offset i, as Octets (fewer if the list ends)
def iso.slice(+i: Nat, n: Nat, xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(B.take(n, B.drop(i, xs)))

# The 7-byte date of a directory record (9.1.5): years since 1900, month,
# day, hour, minute, second, and the offset from Greenwich in 15-minute
# intervals (a signed byte, -48 to 52, kept as its unsigned value 0 to 255)

type IsoDirDate is Data:
  IsoDirDate{year: U32, month: U32, day: U32, hour: U32, minute: U32, second: U32, offset: U32}

# the date as stored: every field to 8 bits
def IsoDirDate.norm(d: IsoDirDate) -> IsoDirDate:
  match d:
    case IsoDirDate{y, mo, dd, h, mi, s, o}:
      IsoDirDate{B.byte(y), B.byte(mo), B.byte(dd), B.byte(h), B.byte(mi), B.byte(s), B.byte(o)}

def IsoDirDate.bytes(d: IsoDirDate) -> List<&2, U32>:
  match d:
    case IsoDirDate{y, mo, dd, h, mi, s, o}:
      [y, mo, dd, h, mi, s, o]

def IsoDirDate.encode(d: IsoDirDate) -> B.Octets:
  B.Octets.of_list(IsoDirDate.bytes(d))

def iso.dirdate.list(xs: List<&2, U32>) -> Result<&2, &2, IsoError, IsoDirDate>:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, t}}}}}}}:
      Done{IsoDirDate{a0, a1, a2, a3, a4, a5, a6}}
    case _:
      Fail{IsoTruncated{}}

# the date in the first 7 bytes of o
def IsoDirDate.decode(o: B.Octets) -> Result<&2, &2, IsoError, IsoDirDate>:
  iso.dirdate.list(B.Octets.to_list(o))

# Decimal digits, for the 17-byte date. A number is kept as a fixed count of
# digits, least significant first; counting up (inc) carries as on paper and
# wraps at the top.

type IsoDigit is Data:
  IsoDig0{}
  IsoDig1{}
  IsoDig2{}
  IsoDig3{}
  IsoDig4{}
  IsoDig5{}
  IsoDig6{}
  IsoDig7{}
  IsoDig8{}
  IsoDig9{}

# the digit's character ('0' is 48)
def IsoDigit.byte(d: IsoDigit) -> U32:
  match d:
    case IsoDig0{}:
      48
    case IsoDig1{}:
      49
    case IsoDig2{}:
      50
    case IsoDig3{}:
      51
    case IsoDig4{}:
      52
    case IsoDig5{}:
      53
    case IsoDig6{}:
      54
    case IsoDig7{}:
      55
    case IsoDig8{}:
      56
    case IsoDig9{}:
      57

def IsoDigit.value(d: IsoDigit) -> Nat:
  match d:
    case IsoDig0{}:
      0n
    case IsoDig1{}:
      1n
    case IsoDig2{}:
      2n
    case IsoDig3{}:
      3n
    case IsoDig4{}:
      4n
    case IsoDig5{}:
      5n
    case IsoDig6{}:
      6n
    case IsoDig7{}:
      7n
    case IsoDig8{}:
      8n
    case IsoDig9{}:
      9n

def iso.digit.of(k: Nat) -> Maybe<&2, IsoDigit>:
  match k:
    case 0n:
      Some{IsoDig0{}}
    case 1n:
      Some{IsoDig1{}}
    case 2n:
      Some{IsoDig2{}}
    case 3n:
      Some{IsoDig3{}}
    case 4n:
      Some{IsoDig4{}}
    case 5n:
      Some{IsoDig5{}}
    case 6n:
      Some{IsoDig6{}}
    case 7n:
      Some{IsoDig7{}}
    case 8n:
      Some{IsoDig8{}}
    case 9n:
      Some{IsoDig9{}}
    case _:
      None{}

def iso.digit.pick(low: Bool, +n: Nat) -> Maybe<&2, IsoDigit>:
  match low:
    case True{}:
      None{}
    case False{}:
      iso.digit.of(Nat.sub(n, 48n))

# the digit whose character is b, if it is one
def IsoDigit.of_byte(b: U32) -> Maybe<&2, IsoDigit>:
  +n = U32.to_nat(b)
  iso.digit.pick(Nat.is_lt(n, 48n), n)

# the next number, least significant digit first (all nines wrap to zeros)
def iso.digits.inc(ds: List<&2, IsoDigit>) -> List<&2, IsoDigit>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case IsoDig0{}:
          Con{IsoDig1{}, t}
        case IsoDig1{}:
          Con{IsoDig2{}, t}
        case IsoDig2{}:
          Con{IsoDig3{}, t}
        case IsoDig3{}:
          Con{IsoDig4{}, t}
        case IsoDig4{}:
          Con{IsoDig5{}, t}
        case IsoDig5{}:
          Con{IsoDig6{}, t}
        case IsoDig6{}:
          Con{IsoDig7{}, t}
        case IsoDig7{}:
          Con{IsoDig8{}, t}
        case IsoDig8{}:
          Con{IsoDig9{}, t}
        case IsoDig9{}:
          Con{IsoDig0{}, iso.digits.inc(t)}

def iso.digits.zero(k: Nat) -> List<&2, IsoDigit>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{IsoDig0{}, iso.digits.zero(p)}

# the k digits of n (n modulo 10^k), least significant first
def iso.digits.of(+k: Nat, n: Nat) -> List<&2, IsoDigit>:
  match n:
    case 0n:
      iso.digits.zero(k)
    case 1n+p:
      iso.digits.inc(iso.digits.of(k, p))

# the number with these digits, least significant first
def iso.digits.value(ds: List<&2, IsoDigit>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(IsoDigit.value(d), Nat.mul(iso.digits.value(t), 10n))

# the digits' characters, most significant first, in front of rest
def iso.digits.bytes(ds: List<&2, IsoDigit>, rest: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      rest
    case Con{d, t}:
      iso.digits.bytes(t, Con{IsoDigit.byte(d), rest})

# digits read, and the bytes after them
type IsoDigitsRest is Data:
  IsoDigitsRest{digits: List<&2, IsoDigit>, rest: List<&2, U32>}

def iso.digits.push(m: Maybe<&2, IsoDigit>, acc: Maybe<&2, List<&2, IsoDigit>>) -> Maybe<&2, List<&2, IsoDigit>>:
  match m acc:
    case Some{d} Some{ds}:
      Some{Con{d, ds}}
    case _ _:
      None{}

def iso.digits.done(acc: Maybe<&2, List<&2, IsoDigit>>, xs: List<&2, U32>) -> Maybe<&2, IsoDigitsRest>:
  match acc:
    case Some{ds}:
      Some{IsoDigitsRest{ds, xs}}
    case None{}:
      None{}

# k digit characters from the head of xs, most significant first: the digits
# (least significant first, in front of those in acc) and the rest of xs;
# None if xs is shorter or a byte is not a digit
def iso.digits.read(k: Nat, xs: List<&2, U32>, acc: Maybe<&2, List<&2, IsoDigit>>) -> Maybe<&2, IsoDigitsRest>:
  match k:
    case 0n:
      iso.digits.done(acc, xs)
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{h, t}:
          iso.digits.read(p, t, iso.digits.push(IsoDigit.of_byte(h), acc))

# The 17-byte date of a volume descriptor (8.4.26.1): year (4 digits),
# month, day, hour, minute, second and hundredths of a second (2 digits
# each), then the offset from Greenwich in 15-minute intervals (a signed
# byte, kept as its unsigned value). All digits zero and offset zero means
# "not specified".

type IsoVolDate is Data:
  IsoVolDate{year: Nat, month: Nat, day: Nat, hour: Nat, minute: Nat, second: Nat, hundredths: Nat, offset: U32}

# whether every field fits its digits (year below 10000, the others below 100)
def IsoVolDate.fits(d: IsoVolDate) -> Bool:
  match d:
    case IsoVolDate{y, mo, dd, h, mi, s, c, o}:
      Bool.and(Nat.is_lt(y, 10000n), Bool.and(Nat.is_lt(mo, 100n), Bool.and(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(h, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)))))))

# the date as stored: the offset to 8 bits
def IsoVolDate.norm(d: IsoVolDate) -> IsoVolDate:
  match d:
    case IsoVolDate{y, mo, dd, h, mi, s, c, o}:
      IsoVolDate{y, mo, dd, h, mi, s, c, B.byte(o)}

def IsoVolDate.unspecified() -> IsoVolDate:
  IsoVolDate{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0}

def IsoVolDate.bytes(d: IsoVolDate) -> List<&2, U32>:
  match d:
    case IsoVolDate{y, mo, dd, h, mi, s, c, o}:
      iso.digits.bytes(iso.digits.of(4n, y), iso.digits.bytes(iso.digits.of(2n, mo), iso.digits.bytes(iso.digits.of(2n, dd), iso.digits.bytes(iso.digits.of(2n, h), iso.digits.bytes(iso.digits.of(2n, mi), iso.digits.bytes(iso.digits.of(2n, s), iso.digits.bytes(iso.digits.of(2n, c), [o])))))))

# the 17 bytes of a date (each field modulo its digits)
def IsoVolDate.encode(d: IsoVolDate) -> B.Octets:
  B.Octets.of_list(IsoVolDate.bytes(d))

def iso.voldate.got(m: Maybe<&2, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoDigitsRest>:
  match m:
    case Some{r}:
      Done{r}
    case None{}:
      Fail{IsoBadDate{}}

def iso.voldate.field(k: Nat, xs: List<&2, U32>) -> Result<&2, &2, IsoError, IsoDigitsRest>:
  iso.voldate.got(iso.digits.read(k, xs, Some{Nil{}}))

def iso.voldate.last(xs: List<&2, U32>) -> Result<&2, &2, IsoError, U32>:
  match xs:
    case Con{o, t}:
      Done{o}
    case Nil{}:
      Fail{IsoBadDate{}}

def iso.voldate.d7(y: Nat, mo: Nat, dd: Nat, h: Nat, mi: Nat, s: Nat, r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{cs, t}}:
      Result.map(&2, &2, IsoError, U32, IsoVolDate, o => IsoVolDate{y, mo, dd, h, mi, s, iso.digits.value(cs), o}, iso.voldate.last(t))
    case Fail{e}:
      Fail{e}

def iso.voldate.d6(y: Nat, mo: Nat, dd: Nat, h: Nat, mi: Nat, r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{ss, t}}:
      iso.voldate.d7(y, mo, dd, h, mi, iso.digits.value(ss), iso.voldate.field(2n, t))
    case Fail{e}:
      Fail{e}

def iso.voldate.d5(y: Nat, mo: Nat, dd: Nat, h: Nat, r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{ms, t}}:
      iso.voldate.d6(y, mo, dd, h, iso.digits.value(ms), iso.voldate.field(2n, t))
    case Fail{e}:
      Fail{e}

def iso.voldate.d4(y: Nat, mo: Nat, dd: Nat, r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{hs, t}}:
      iso.voldate.d5(y, mo, dd, iso.digits.value(hs), iso.voldate.field(2n, t))
    case Fail{e}:
      Fail{e}

def iso.voldate.d3(y: Nat, mo: Nat, r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{ds, t}}:
      iso.voldate.d4(y, mo, iso.digits.value(ds), iso.voldate.field(2n, t))
    case Fail{e}:
      Fail{e}

def iso.voldate.d2(y: Nat, r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{ms, t}}:
      iso.voldate.d3(y, iso.digits.value(ms), iso.voldate.field(2n, t))
    case Fail{e}:
      Fail{e}

def iso.voldate.d1(r: Result<&2, &2, IsoError, IsoDigitsRest>) -> Result<&2, &2, IsoError, IsoVolDate>:
  match r:
    case Done{IsoDigitsRest{ys, t}}:
      iso.voldate.d2(iso.digits.value(ys), iso.voldate.field(2n, t))
    case Fail{e}:
      Fail{e}

def iso.voldate.list(xs: List<&2, U32>) -> Result<&2, &2, IsoError, IsoVolDate>:
  iso.voldate.d1(iso.voldate.field(4n, xs))

# the date in the first 17 bytes of o: IsoBadDate if a digit is not one
def IsoVolDate.decode(o: B.Octets) -> Result<&2, &2, IsoError, IsoVolDate>:
  iso.voldate.list(B.Octets.to_list(o))

def IsoVolDate.is_unspecified(+d: IsoVolDate) -> Bool:
  match d:
    case IsoVolDate{y, mo, dd, h, mi, s, c, o}:
      Bool.and(Nat.is_eq(Nat.add(y, Nat.add(mo, Nat.add(dd, Nat.add(h, Nat.add(mi, Nat.add(s, c)))))), 0n), U32.is_eq(o, 0))

def iso.pad2.pick(small: Bool, n: Nat) -> String:
  match small:
    case True{}:
      "0" ++ Nat.show(n)
    case False{}:
      Nat.show(n)

def iso.pad2(+n: Nat) -> String:
  iso.pad2.pick(Nat.is_lt(n, 10n), n)

def IsoVolDate.show(d: IsoVolDate) -> String:
  match d:
    case IsoVolDate{y, mo, dd, h, mi, s, c, o}:
      Nat.show(y) ++ "-" ++ iso.pad2(mo) ++ "-" ++ iso.pad2(dd) ++ " " ++ iso.pad2(h) ++ ":" ++ iso.pad2(mi) ++ ":" ++ iso.pad2(s) ++ "." ++ iso.pad2(c) ++ " " ++ U32.show(o)

def IsoDirDate.show(d: IsoDirDate) -> String:
  match d:
    case IsoDirDate{y, mo, dd, h, mi, s, o}:
      Nat.show(Nat.add(1900n, U32.to_nat(y))) ++ "-" ++ iso.pad2(U32.to_nat(mo)) ++ "-" ++ iso.pad2(U32.to_nat(dd)) ++ " " ++ iso.pad2(U32.to_nat(h)) ++ ":" ++ iso.pad2(U32.to_nat(mi)) ++ ":" ++ iso.pad2(U32.to_nat(s)) ++ " " ++ U32.show(o)

# Identifiers (7.4): a- and d-character strings padded with spaces

def iso.text.list(xs: List<&2, U32>) -> String:
  String.trim_end(B.to_string(xs))

# an identifier field as text: one character per byte, trailing spaces dropped
def Iso.text(o: B.Octets) -> String:
  iso.text.list(B.Octets.to_list(o))

# Reading the device: a 2048-byte logical sector is one device block

def iso.dev(r: Result<&2, &2, BD.DevError, B.Octets>) -> Result<&2, &2, IsoError, B.Octets>:
  match r:
    case Done{o}:
      Done{o}
    case Fail{e}:
      Fail{IsoDev{e}}

def iso.read_sector(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, n: Nat) -> Result<&2, &2, IsoError, B.Octets>:
  iso.dev(read_block(d, n))
