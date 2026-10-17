# bend-osdev-xz: the .xz container's fields ("The .xz File Format", version
# 1.2.x, Lasse Collin and Igor Pavlov, public domain): variable-length
# integers, the stream header and footer, block headers with their filter
# flags, and the index.
#
# The parsers read the front of a byte list and answer the value and the
# bytes after it. XzTruncated always means the list ended too soon, and
# nothing else, so a streaming decoder can treat it as "wait for more input".
# The public defs (XzStream.header and the others) take Octets.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ../crc/crc.bend as C

# A value parsed from the front of a byte list, and the bytes after it
type XzGot<-A: Data> is Data:
  XzGot{value: A, rest: List<&2, U32>}

def XzGot.value(-A: Data, g: XzGot<A>) -> A:
  match g:
    case XzGot{v, r}:
      v

def XzGot.rest(-A: Data, g: XzGot<A>) -> List<&2, U32>:
  match g:
    case XzGot{v, r}:
      r

# A filter in a block's chain: its ID and its properties
type XzFilter is Data:
  XzFilter{id: Nat, props: B.Octets}

# A block header: its size in bytes (8 to 1024), the compressed and
# uncompressed sizes if it gives them, and the filter chain, in the order the
# encoder applied them (so LZMA2 is last)
type XzBlockHeader is Data:
  XzBlockHeader{size: Nat, csize: Maybe<&2, Nat>, usize: Maybe<&2, Nat>, filters: List<&2, XzFilter>}

# An index record: a block's unpadded size (header, compressed data and check,
# without the padding) and its uncompressed size
type XzRecord is Data:
  XzRecord{unpadded: Nat, uncompressed: Nat}

# The index: its records, and its size in bytes (indicator to CRC32)
type XzIndex is Data:
  XzIndex{records: List<&2, XzRecord>, size: Nat}

# A stream footer: the index size it records (backward size), and the check ID
# of its stream flags
type XzFooter is Data:
  XzFooter{backward: Nat, check: U32}

# Helpers

def XzC.require(ok: Bool, +e: E.XzError) -> Result<&2, &2, E.XzError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# a parse inside a slice of known size: running out is malformation e, not
# truncation
def XzC.inside(-A: Data, r: Result<&2, &2, E.XzError, A>, +e: E.XzError) -> Result<&2, &2, E.XzError, A>:
  match r:
    case Fail{E.XzTruncated{}}:
      Fail{e}
    case Fail{x}:
      Fail{x}
    case Done{v}:
      Done{v}

# exactly n bytes, or XzTruncated
def XzC.take.go(ok: Bool, +n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<List<&2, U32>>>:
  match ok:
    case True{}:
      Done{XzGot{B.take(n, xs), B.drop(n, xs)}}
    case False{}:
      Fail{E.XzTruncated{}}

def XzC.has(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match xs:
        case Nil{}:
          False{}
        case Con{h, t}:
          XzC.has(p, t)

def XzC.take(+n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<List<&2, U32>>>:
  XzC.take.go(XzC.has(n, xs), n, xs)

def XzC.all_zero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(U32.is_eq(h, 0), XzC.all_zero(t))

def XzC.crc32(xs: List<&2, U32>) -> U32:
  C.crc32(B.Octets.of_list(xs))

# the little-endian 32-bit field at the front (the list has at least 4 bytes)
def XzC.le32(xs: List<&2, U32>) -> U32:
  Maybe.default(&2, U32, B.le32_at(xs, 0n), 0)

# Variable-length integers (1.2): up to nine bytes, seven bits each, least
# significant first, the top bit set on every byte but the last; the last
# byte may be 0 only if it is the only one. more: another byte follows;
# zero: the byte that ended it was a superfluous 0.
def XzC.vli.go(n: Nat, more: Bool, zero: Bool, xs: List<&2, U32>, +acc: Nat, +mul: Nat, +bad: E.XzError) -> Result<&2, &2, E.XzError, XzGot<Nat>>:
  match n more:
    case _ False{}:
      match zero:
        case True{}:
          Fail{bad}
        case False{}:
          Done{XzGot{acc, xs}}
    case 0n True{}:
      Fail{bad}
    case 1n+p True{}:
      match xs:
        case Nil{}:
          Fail{E.XzTruncated{}}
        case Con{+h, t}:
          XzC.vli.go(p, U32.is_ge(h, 128), Bool.and(U32.is_eq(h, 0), Nat.is_gt(mul, 1n)), t, Nat.add(acc, Nat.mul(U32.to_nat(U32.and(h, 127)), mul)), Nat.mul(mul, 128n), bad)

def XzC.vli(xs: List<&2, U32>, +bad: E.XzError) -> Result<&2, &2, E.XzError, XzGot<Nat>>:
  XzC.vli.go(9n, True{}, False{}, xs, 0n, 1n, bad)

# The stream header and footer (2.1)

# the magic bytes, compared as far as the input goes
def XzC.magic.go(expect: List<&2, U32>, same: Bool, xs: List<&2, U32>, +bad: E.XzError) -> Result<&2, &2, E.XzError, List<&2, U32>>:
  match expect:
    case Nil{}:
      match same:
        case True{}:
          Done{xs}
        case False{}:
          Fail{bad}
    case Con{+e, et}:
      match same:
        case False{}:
          Fail{bad}
        case True{}:
          match xs:
            case Nil{}:
              Fail{E.XzTruncated{}}
            case Con{+h, t}:
              XzC.magic.go(et, U32.is_eq(h, e), t, bad)

# the header magic: FD 37 7A 58 5A 00
def XzC.header_magic() -> List<&2, U32>:
  [253, 55, 122, 88, 90, 0]

# the stream flags: a null byte, then the check ID in the low four bits
def XzC.flags(+f0: U32, +f1: U32) -> Result<&2, &2, E.XzError, U32>:
  do Result<&2, &2, E.XzError, U32>:
    XzC.require(Bool.and(U32.is_eq(f0, 0), U32.is_lt(f1, 16)), E.XzBadStreamFlags{})
    return f1

def XzC.header.check(h: List<&2, U32>, +rest: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<U32>>:
  match h:
    case Con{+f0, Con{+f1, Con{c0, Con{c1, Con{c2, Con{c3, t}}}}}}:
      do Result<&2, &2, E.XzError, XzGot<U32>>:
        XzC.require(U32.is_eq(XzC.crc32([f0, f1]), XzC.le32([c0, c1, c2, c3])), E.XzBadHeaderCrc{})
        +check : U32 <- XzC.flags(f0, f1)
        return XzGot{check, rest}
    case _:
      Fail{E.XzTruncated{}}

def XzC.header.fields(+g: XzGot<List<&2, U32>>) -> Result<&2, &2, E.XzError, XzGot<U32>>:
  XzC.header.check(XzGot.value(List<&2, U32>, g), XzGot.rest(List<&2, U32>, g))

def XzC.header.got(r: Result<&2, &2, E.XzError, XzGot<List<&2, U32>>>) -> Result<&2, &2, E.XzError, XzGot<U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      XzC.header.fields(g)

def XzC.header.after(r: Result<&2, &2, E.XzError, List<&2, U32>>) -> Result<&2, &2, E.XzError, XzGot<U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rest}:
      XzC.header.got(XzC.take(6n, rest))

# A stream header at the front of xs: its check ID
def XzC.header(xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<U32>>:
  XzC.header.after(XzC.magic.go(XzC.header_magic(), True{}, xs, E.XzBadMagic{}))

def XzC.footer.check(f: List<&2, U32>, +rest: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzFooter>>:
  match f:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{+b0, Con{+b1, Con{+b2, Con{+b3, Con{+f0, Con{+f1, Con{+y, Con{+z, t}}}}}}}}}}}}:
      do Result<&2, &2, E.XzError, XzGot<XzFooter>>:
        XzC.require(Bool.and(U32.is_eq(y, 89), U32.is_eq(z, 90)), E.XzBadFooterMagic{})
        XzC.require(U32.is_eq(XzC.crc32([b0, b1, b2, b3, f0, f1]), XzC.le32([c0, c1, c2, c3])), E.XzBadFooterCrc{})
        +check : U32 <- XzC.flags(f0, f1)
        return XzGot{XzFooter{Nat.mul(Nat.add(U32.to_nat(XzC.le32([b0, b1, b2, b3])), 1n), 4n), check}, rest}
    case _:
      Fail{E.XzTruncated{}}

def XzC.footer.fields(+g: XzGot<List<&2, U32>>) -> Result<&2, &2, E.XzError, XzGot<XzFooter>>:
  XzC.footer.check(XzGot.value(List<&2, U32>, g), XzGot.rest(List<&2, U32>, g))

# A stream footer at the front of xs
def XzC.footer(+xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzFooter>>:
  do Result<&2, &2, E.XzError, XzGot<XzFooter>>:
    +g : XzGot<List<&2, U32>> <- XzC.take(12n, xs)
    XzC.footer.fields(g)

# Block headers (3.1)

def XzC.bytes(+n: Nat, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<B.Octets>>:
  do Result<&2, &2, E.XzError, XzGot<B.Octets>>:
    +g : XzGot<List<&2, U32>> <- XzC.take(n, xs)
    return XzGot{B.Octets.of_list(XzGot.value(List<&2, U32>, g)), XzGot.rest(List<&2, U32>, g)}

# one filter's flags: its ID, the size of its properties, and the properties
def XzC.filter(xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzFilter>>:
  do Result<&2, &2, E.XzError, XzGot<XzFilter>>:
    +id : XzGot<Nat> <- XzC.vli(xs, E.XzBadBlockHeader{})
    +ps : XzGot<Nat> <- XzC.vli(XzGot.rest(Nat, id), E.XzBadBlockHeader{})
    +pr : XzGot<B.Octets> <- XzC.bytes(XzGot.value(Nat, ps), XzGot.rest(Nat, ps))
    return XzGot{XzFilter{XzGot.value(Nat, id), XzGot.value(B.Octets, pr)}, XzGot.rest(B.Octets, pr)}


# n + 1 filters; r is the one just parsed
def XzC.filters.go(n: Nat, r: Result<&2, &2, E.XzError, XzGot<XzFilter>>, acc: List<&2, XzFilter>) -> Result<&2, &2, E.XzError, XzGot<List<&2, XzFilter>>>:
  match n:
    case 0n:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{XzGot{f, rest}}:
          Done{XzGot{List.reverse(&2, XzFilter, Con{f, acc}), rest}}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{XzGot{f, rest}}:
          XzC.filters.go(p, XzC.filter(rest), Con{f, acc})

def XzC.filters(n: Nat, xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<List<&2, XzFilter>>>:
  match n:
    case 0n:
      Done{XzGot{Nil{}, xs}}
    case 1n+p:
      XzC.filters.go(p, XzC.filter(xs), Nil{})

# an optional size field
def XzC.opt.some(r: Result<&2, &2, E.XzError, XzGot<Nat>>) -> Result<&2, &2, E.XzError, XzGot<Maybe<&2, Nat>>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzGot{v, rest}}:
      Done{XzGot{Some{v}, rest}}

def XzC.opt(present: Bool, xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<Maybe<&2, Nat>>>:
  match present:
    case True{}:
      XzC.opt.some(XzC.vli(xs, E.XzBadBlockHeader{}))
    case False{}:
      Done{XzGot{None{}, xs}}

# the fields after the size byte: the flags (bits 0-1 the number of filters
# less one, bits 2-5 reserved, bit 6 a compressed size follows, bit 7 an
# uncompressed size follows), the sizes, the filter flags, and null padding
def XzC.block.parse(+size: Nat, xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzBlockHeader>:
  match xs:
    case Nil{}:
      Fail{E.XzBadBlockHeader{}}
    case Con{+f, t}:
      do Result<&2, &2, E.XzError, XzBlockHeader>:
        XzC.require(U32.is_eq(U32.and(f, 60), 0), E.XzBadBlockHeader{})
        +cs : XzGot<Maybe<&2, Nat>> <- XzC.opt(Bool.not(U32.is_eq(U32.and(f, 64), 0)), t)
        +us : XzGot<Maybe<&2, Nat>> <- XzC.opt(Bool.not(U32.is_eq(U32.and(f, 128), 0)), XzGot.rest(Maybe<&2, Nat>, cs))
        +fl : XzGot<List<&2, XzFilter>> <- XzC.filters(U32.to_nat(U32.add(U32.and(f, 3), 1)), XzGot.rest(Maybe<&2, Nat>, us))
        XzC.require(XzC.all_zero(XzGot.rest(List<&2, XzFilter>, fl)), E.XzBadBlockHeader{})
        return XzBlockHeader{size, XzGot.value(Maybe<&2, Nat>, cs), XzGot.value(Maybe<&2, Nat>, us), XzGot.value(List<&2, XzFilter>, fl)}

def XzC.block.fields(+size: Nat, +h: List<&2, U32>, +rest: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzBlockHeader>>:
  +n = Nat.sub(size, 4n)
  do Result<&2, &2, E.XzError, XzGot<XzBlockHeader>>:
    XzC.require(U32.is_eq(XzC.crc32(B.take(n, h)), XzC.le32(B.drop(n, h))), E.XzBadBlockHeaderCrc{})
    +hdr : XzBlockHeader <- XzC.inside(XzBlockHeader, XzC.block.parse(size, B.drop(1n, B.take(n, h))), E.XzBadBlockHeader{})
    return XzGot{hdr, rest}

def XzC.block.sized(+size: Nat, +g: XzGot<List<&2, U32>>) -> Result<&2, &2, E.XzError, XzGot<XzBlockHeader>>:
  XzC.block.fields(size, XzGot.value(List<&2, U32>, g), XzGot.rest(List<&2, U32>, g))

# A block header at the front of xs, whose first byte b0 is not 0: it is
# (b0 + 1) * 4 bytes long, and ends with the CRC32 of the rest
def XzC.block(+b0: U32, +xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzBlockHeader>>:
  +size = Nat.mul(Nat.add(U32.to_nat(U32.and(b0, 255)), 1n), 4n)
  do Result<&2, &2, E.XzError, XzGot<XzBlockHeader>>:
    +g : XzGot<List<&2, U32>> <- XzC.take(size, xs)
    XzC.block.sized(size, g)

# The index (4)

def XzC.record(xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzRecord>>:
  do Result<&2, &2, E.XzError, XzGot<XzRecord>>:
    +u : XzGot<Nat> <- XzC.vli(xs, E.XzBadIndex{})
    +c : XzGot<Nat> <- XzC.vli(XzGot.rest(Nat, u), E.XzBadIndex{})
    return XzGot{XzRecord{XzGot.value(Nat, u), XzGot.value(Nat, c)}, XzGot.rest(Nat, c)}

def XzC.records.go(n: Nat, r: Result<&2, &2, E.XzError, XzGot<XzRecord>>, acc: List<&2, XzRecord>) -> Result<&2, &2, E.XzError, XzGot<List<&2, XzRecord>>>:
  match n:
    case 0n:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{XzGot{x, rest}}:
          Done{XzGot{List.reverse(&2, XzRecord, Con{x, acc}), rest}}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{XzGot{x, rest}}:
          XzC.records.go(p, XzC.record(rest), Con{x, acc})

def XzC.records(n: Nat, xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<List<&2, XzRecord>>>:
  match n:
    case 0n:
      Done{XzGot{Nil{}, xs}}
    case 1n+p:
      XzC.records.go(p, XzC.record(xs), Nil{})

# after the records: null padding to a multiple of four bytes, and the CRC32
# of everything from the indicator on
def XzC.index.end(+xs: List<&2, U32>, recs: List<&2, XzRecord>, +rest: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzIndex>>:
  +used = Nat.sub(B.len(xs), B.len(rest))
  +pad = Nat.mod(Nat.sub(4n, Nat.mod(used, 4n)), 4n)
  do Result<&2, &2, E.XzError, XzGot<XzIndex>>:
    +p : XzGot<List<&2, U32>> <- XzC.take(pad, rest)
    XzC.require(XzC.all_zero(XzGot.value(List<&2, U32>, p)), E.XzBadPadding{})
    +c : XzGot<List<&2, U32>> <- XzC.take(4n, XzGot.rest(List<&2, U32>, p))
    XzC.require(U32.is_eq(XzC.crc32(B.take(Nat.add(used, pad), xs)), XzC.le32(XzGot.value(List<&2, U32>, c))), E.XzBadIndexCrc{})
    return XzGot{XzIndex{recs, Nat.add(Nat.add(used, pad), 4n)}, XzGot.rest(List<&2, U32>, c)}

def XzC.index.recs(+xs: List<&2, U32>, +g: XzGot<List<&2, XzRecord>>) -> Result<&2, &2, E.XzError, XzGot<XzIndex>>:
  XzC.index.end(xs, XzGot.value(List<&2, XzRecord>, g), XzGot.rest(List<&2, XzRecord>, g))

# An index at the front of xs: the indicator 0, the number of records, the
# records, padding, and the CRC32
def XzC.index(+xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzGot<XzIndex>>:
  match xs:
    case Nil{}:
      Fail{E.XzTruncated{}}
    case Con{+ind, t}:
      do Result<&2, &2, E.XzError, XzGot<XzIndex>>:
        XzC.require(U32.is_eq(ind, 0), E.XzBadIndex{})
        +n : XzGot<Nat> <- XzC.vli(t, E.XzBadIndex{})
        +g : XzGot<List<&2, XzRecord>> <- XzC.records(XzGot.value(Nat, n), XzGot.rest(Nat, n))
        XzC.index.recs(Con{ind, t}, g)

# The public parsers, on Octets (each reads its structure at the front of o
# and ignores what follows)

def XzC.value(-A: Data, r: Result<&2, &2, E.XzError, XzGot<A>>) -> Result<&2, &2, E.XzError, A>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{XzGot{v, rest}}:
      Done{v}

# a stream header: its check ID
def XzStream.header(o: B.Octets) -> Result<&2, &2, E.XzError, U32>:
  XzC.value(U32, XzC.header(B.Octets.to_list(o)))

def XzStream.footer(o: B.Octets) -> Result<&2, &2, E.XzError, XzFooter>:
  XzC.value(XzFooter, XzC.footer(B.Octets.to_list(o)))

def XzStream.block_header.go(xs: List<&2, U32>) -> Result<&2, &2, E.XzError, XzBlockHeader>:
  match xs:
    case Nil{}:
      Fail{E.XzTruncated{}}
    case Con{+b0, t}:
      XzC.value(XzBlockHeader, XzC.block(b0, Con{b0, t}))

# a block header (not an index: its first byte is not 0)
def XzStream.block_header(o: B.Octets) -> Result<&2, &2, E.XzError, XzBlockHeader>:
  XzStream.block_header.go(B.Octets.to_list(o))

def XzStream.index(o: B.Octets) -> Result<&2, &2, E.XzError, XzIndex>:
  XzC.value(XzIndex, XzC.index(B.Octets.to_list(o)))

def XzStream.vli(o: B.Octets) -> Result<&2, &2, E.XzError, Nat>:
  XzC.value(Nat, XzC.vli(B.Octets.to_list(o), E.XzBadBlockHeader{}))
