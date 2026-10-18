# bend-osdev-c842, the format: the templates, the codes, and the parser and
# serialiser of the bit stream.
#
# Sources (README.md): Blaner et al., "IBM POWER7+ processor on-chip
# accelerators for cryptography and active memory expansion", IBM J. Res. &
# Dev. 57(6), 2013, paper 3 (the paper); US 2006/0106870 A1, Figure 3 (the
# patent); and black-box observations of Linux's 842 (ref/OBSERVATIONS.md).
#
# A stream is a sequence of 5-bit codes, each followed by its fields, written
# most significant bit first and packed from each byte's top bit down (E1):
#
#   0 to 25   an 8-byte chunk, as the template's sub-phrases (the patent's
#             Figure 3 numbering, which Linux uses: E2). Each sub-phrase is
#             LL, two raw bytes (16 bits); P2, an 8-bit index of a 2-byte
#             phrase; P4, a 9-bit index of a 4-byte phrase; or P8, an 8-bit
#             index of an 8-byte phrase (the paper)
#   27        RPT: a 6-bit field f, then f + 1 copies of the previous 8
#             bytes (the paper's RPT; the field's offset of one: E1)
#   28        Z8: 8 zero bytes (the paper)
#   29        short data: a 3-bit count n (1 to 7), then n bytes (E1, E2)
#   30        the end: a 32-bit CRC of the uncompressed bytes (E1; crc.bend)
#   26, 31    invalid (E2)
#
# After the CRC, zero bits fill the stream to a whole number of 8-byte words
# (E1); a reader ignores whatever follows the CRC (E2).
#
# The parser is a state machine taking one bit at a time and announcing each
# field as it completes (C842Event), so a decoder can act on a field before
# the next is read, as Linux's does (E7). c842.tokens reads a whole stream
# into tokens with it; c842.serialise writes tokens back.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as Bi

# Sub-phrases

type C842Kind is Data:
  C842LL{}
  C842P2{}
  C842P4{}
  C842P8{}

# a sub-phrase's bits in the stream
def C842Kind.width(k: C842Kind) -> Nat:
  match k:
    case C842LL{}:
      16n
    case C842P2{}:
      8n
    case C842P4{}:
      9n
    case C842P8{}:
      8n

# the bytes a sub-phrase stands for
def C842Kind.size(k: C842Kind) -> U32:
  match k:
    case C842LL{}:
      2
    case C842P2{}:
      2
    case C842P4{}:
      4
    case C842P8{}:
      8

# the history a pointer's index counts in: 512 bytes for P2, 2048 for P4
# and P8 (the paper); 0 for a literal
def C842Kind.history(k: C842Kind) -> U32:
  match k:
    case C842LL{}:
      0
    case C842P2{}:
      512
    case C842P4{}:
      2048
    case C842P8{}:
      2048

# The 26 templates, by code (the patent's Figure 3, states 0 to 25)
def c842.templates() -> List<&2, List<&2, C842Kind>>:
  [
    [C842LL{}, C842LL{}, C842LL{}, C842LL{}],
    [C842LL{}, C842LL{}, C842LL{}, C842P2{}],
    [C842LL{}, C842LL{}, C842P2{}, C842LL{}],
    [C842LL{}, C842LL{}, C842P2{}, C842P2{}],
    [C842LL{}, C842LL{}, C842P4{}],
    [C842LL{}, C842P2{}, C842LL{}, C842LL{}],
    [C842LL{}, C842P2{}, C842LL{}, C842P2{}],
    [C842LL{}, C842P2{}, C842P2{}, C842LL{}],
    [C842LL{}, C842P2{}, C842P2{}, C842P2{}],
    [C842LL{}, C842P2{}, C842P4{}],
    [C842P2{}, C842LL{}, C842LL{}, C842LL{}],
    [C842P2{}, C842LL{}, C842LL{}, C842P2{}],
    [C842P2{}, C842LL{}, C842P2{}, C842LL{}],
    [C842P2{}, C842LL{}, C842P2{}, C842P2{}],
    [C842P2{}, C842LL{}, C842P4{}],
    [C842P2{}, C842P2{}, C842LL{}, C842LL{}],
    [C842P2{}, C842P2{}, C842LL{}, C842P2{}],
    [C842P2{}, C842P2{}, C842P2{}, C842LL{}],
    [C842P2{}, C842P2{}, C842P2{}, C842P2{}],
    [C842P2{}, C842P2{}, C842P4{}],
    [C842P4{}, C842LL{}, C842LL{}],
    [C842P4{}, C842LL{}, C842P2{}],
    [C842P4{}, C842P2{}, C842LL{}],
    [C842P4{}, C842P2{}, C842P2{}],
    [C842P4{}, C842P4{}],
    [C842P8{}]
  ]

def c842.nth(xs: List<&2, List<&2, C842Kind>>, n: Nat) -> Maybe<&2, List<&2, C842Kind>>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, t}:
      match n:
        case 0n:
          Some{h}
        case 1n+p:
          c842.nth(t, p)

def c842.template.at(lt: Bool, t: U32) -> Maybe<&2, List<&2, C842Kind>>:
  match lt:
    case True{}:
      c842.nth(c842.templates(), U32.to_nat(t))
    case False{}:
      None{}

# the sub-phrases of template t (codes 0 to 25)
def c842.template(+t: U32) -> Maybe<&2, List<&2, C842Kind>>:
  c842.template.at(U32.is_lt(t, 26), t)

# The special codes

def c842.code.repeat() -> U32:
  27

def c842.code.zero() -> U32:
  28

def c842.code.short() -> U32:
  29

def c842.code.end() -> U32:
  30

# Tokens: a stream as values

# a sub-phrase's field: a literal's two bytes, or a pointer's index
type C842Field is Data:
  C842Lit{hi: U32, lo: U32}
  C842Ptr{index: U32}

# a chunk by template t (its fields in the template's order); RPT with field
# n (n + 1 copies); Z8; short data; the end with its CRC
type C842Token is Data:
  C842Chunk{t: U32, fields: List<&2, C842Field>}
  C842Repeat{n: U32}
  C842Zero{}
  C842Short{bytes: List<&2, U32>}
  C842End{crc: U32}

# Bit lists

def c842.fmt.cat(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      b
    case Con{h, t}:
      Con{h, c842.fmt.cat(t, b)}

def c842.fmt.zeros(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{False{}, c842.fmt.zeros(p)}

# the low n bits of v, most significant first
def c842.bits.u(+n: Nat, +v: U32) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{U32.is_eq(U32.and(U32.shrn(v, p), 1), 1), c842.bits.u(p, v)}

def c842.fmt.b01(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# the value of bits read in reverse (the last bit read, least significant,
# first)
def c842.fmt.value(bs: List<&2, Bool>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, t}:
      U32.or(U32.shl(c842.fmt.value(t)), c842.fmt.b01(b))

# The serialiser

# a field as the template's kind k reads it (a field of the other sort is
# written as zero bits: tokens are expected to match their templates)
def c842.fmt.field(k: C842Kind, f: C842Field) -> List<&2, Bool>:
  match k:
    case C842LL{}:
      match f:
        case C842Lit{hi, +lo}:
          c842.fmt.cat(Bi.c842.bits.byte(hi), Bi.c842.bits.byte(lo))
        case C842Ptr{i}:
          c842.fmt.zeros(16n)
    case C842P2{}:
      match f:
        case C842Ptr{i}:
          c842.bits.u(8n, i)
        case C842Lit{hi, lo}:
          c842.fmt.zeros(8n)
    case C842P4{}:
      match f:
        case C842Ptr{i}:
          c842.bits.u(9n, i)
        case C842Lit{hi, lo}:
          c842.fmt.zeros(9n)
    case C842P8{}:
      match f:
        case C842Ptr{i}:
          c842.bits.u(8n, i)
        case C842Lit{hi, lo}:
          c842.fmt.zeros(8n)

# the fields of a template's kinds (a missing field is written as zeros)
def c842.fmt.fields(ks: List<&2, C842Kind>, fs: List<&2, C842Field>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, kt}:
      match fs:
        case Nil{}:
          c842.fmt.cat(c842.fmt.zeros(C842Kind.width(k)), c842.fmt.fields(kt, Nil{}))
        case Con{f, ft}:
          c842.fmt.cat(c842.fmt.field(k, f), c842.fmt.fields(kt, ft))

def c842.fmt.kinds(m: Maybe<&2, List<&2, C842Kind>>) -> List<&2, C842Kind>:
  match m:
    case None{}:
      Nil{}
    case Some{ks}:
      ks

def c842.fmt.bytes(bs: List<&2, U32>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      c842.fmt.cat(Bi.c842.bits.byte(b), c842.fmt.bytes(t))

def c842.fmt.count(bs: List<&2, U32>) -> U32:
  U32.from_nat(List.length(&2, U32, bs))

# one token's bits
def c842.fmt.token(t: C842Token) -> List<&2, Bool>:
  match t:
    case C842Chunk{+code, fs}:
      c842.fmt.cat(c842.bits.u(5n, code), c842.fmt.fields(c842.fmt.kinds(c842.template(code)), fs))
    case C842Repeat{n}:
      c842.fmt.cat(c842.bits.u(5n, 27), c842.bits.u(6n, n))
    case C842Zero{}:
      c842.bits.u(5n, 28)
    case C842Short{+bs}:
      c842.fmt.cat(c842.bits.u(5n, 29), c842.fmt.cat(c842.bits.u(3n, c842.fmt.count(bs)), c842.fmt.bytes(bs)))
    case C842End{c}:
      c842.fmt.cat(c842.bits.u(5n, 30), Bi.c842.bits.word(c))

# a stream's bits, before padding
def c842.serialise(ts: List<&2, C842Token>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      c842.fmt.cat(c842.fmt.token(t), c842.serialise(rest))

# Packing: bits to bytes, zero-filled to whole 8-byte words

# the bits, then zeros to the end of the current 64-bit word (w: the bits
# left in it; 0: no word open)
def c842.fmt.pad(bs: List<&2, Bool>, w: Nat) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      c842.fmt.zeros(w)
    case Con{b, t}:
      match w:
        case 0n:
          Con{b, c842.fmt.pad(t, 63n)}
        case 1n+q:
          Con{b, c842.fmt.pad(t, q)}

# the byte of a list's first 8 bits, most significant first
def c842.fmt.last(bs: List<&2, Bool>) -> U32:
  match bs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, rest}}}}}}}}:
      Bi.c842.byte.of(c7, c6, c5, c4, c3, c2, c1, c0)
    case _:
      0

# bytes of 8 bits each, most significant first (a last group of fewer than 8
# bits is zero-filled)
def c842.fmt.group(bs: List<&2, Bool>) -> List<&2, U32>:
  match bs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, rest}}}}}}}}:
      Con{Bi.c842.byte.of(c7, c6, c5, c4, c3, c2, c1, c0), c842.fmt.group(rest)}
    case Nil{}:
      Nil{}
    case _:
      [c842.fmt.last(c842.fmt.cat(bs, c842.fmt.zeros(7n)))]

# a stream's bytes: its bits, zero-filled to a whole number of 8-byte words
def c842.pack(bs: List<&2, Bool>) -> B.Octets:
  B.Octets.of_list(c842.fmt.group(c842.fmt.pad(bs, 0n)))

# the zero bits pad adds after bs (w: as pad's)
def c842.pack.fill.go(bs: List<&2, Bool>, w: Nat) -> Nat:
  match bs:
    case Nil{}:
      w
    case Con{b, t}:
      match w:
        case 0n:
          c842.pack.fill.go(t, 63n)
        case 1n+q:
          c842.pack.fill.go(t, q)

# the zero bits group adds to complete its last byte (none when the bits are
# a whole number of bytes, as pad's always are)
def c842.fmt.gfill(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, rest}}}}}}}}:
      c842.fmt.gfill(rest)
    case Nil{}:
      0n
    case _:
      Nat.sub(8n, List.length(&2, Bool, bs))

# the zero bits pack adds after bs
def c842.pack.fill(+bs: List<&2, Bool>) -> Nat:
  Nat.add(c842.pack.fill.go(bs, 0n), c842.fmt.gfill(c842.fmt.pad(bs, 0n)))

# a byte list's bits, most significant first
def c842.unpack.list(xs: List<&2, U32>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      c842.fmt.cat(Bi.c842.bits.byte(x), c842.unpack.list(t))

# a stream's bits
def c842.unpack(o: B.Octets) -> List<&2, Bool>:
  c842.unpack.list(B.Octets.to_list(o))

# The parser: one bit at a time

# what the parser reads next: a code; a field of the current template (then
# the rest of its kinds); RPT's field; short data's count; a short data
# byte (n left, counting this one); the CRC; nothing (after the CRC)
type C842Want is Data:
  C842WCode{}
  C842WField{k: C842Kind, more: List<&2, C842Kind>}
  C842WRepeat{}
  C842WCount{}
  C842WShort{n: Nat}
  C842WCrc{}
  C842WEnd{}

# what is being read, its bits so far (in reverse), and how many are left
type C842Parser is Data:
  C842Parser{want: C842Want, got: List<&2, Bool>, left: Nat}

# what a bit completes: nothing yet; the start of a chunk; a literal's two
# bytes; a pointer; RPT; Z8; the start of short data (n bytes); a short data
# byte; the end and its CRC; a failure
type C842Event is Data:
  C842ENone{}
  C842ETemplate{t: U32}
  C842ELit{hi: U32, lo: U32}
  C842EPtr{k: C842Kind, index: U32}
  C842ERepeat{n: U32}
  C842EZero{}
  C842EShortStart{n: Nat}
  C842EShort{b: U32}
  C842EEnd{crc: U32}
  C842EBad{e: E.C842Error}

type C842Step is Data:
  C842Step{p: C842Parser, ev: C842Event}

def c842.parse.want(w: C842Want, n: Nat) -> C842Parser:
  C842Parser{w, Nil{}, n}

# the parser at the start of a stream
def C842Parser.start() -> C842Parser:
  c842.parse.want(C842WCode{}, 5n)

def c842.parse.code_next() -> C842Parser:
  c842.parse.want(C842WCode{}, 5n)

# after a field: the template's next field, or the next code
def c842.parse.next_field(more: List<&2, C842Kind>) -> C842Parser:
  match more:
    case Nil{}:
      c842.parse.code_next()
    case Con{+k, t}:
      c842.parse.want(C842WField{k, t}, C842Kind.width(k))

# a template code: its first field next
def c842.parse.chunk(m: Maybe<&2, List<&2, C842Kind>>, t: U32) -> C842Step:
  match m:
    case None{}:
      C842Step{c842.parse.code_next(), C842EBad{E.C842BadTemplate{}}}
    case Some{ks}:
      C842Step{c842.parse.next_field(ks), C842ETemplate{t}}

def c842.parse.c30(hit: Bool) -> C842Step:
  match hit:
    case True{}:
      C842Step{c842.parse.want(C842WCrc{}, 32n), C842ENone{}}
    case False{}:
      C842Step{c842.parse.code_next(), C842EBad{E.C842BadTemplate{}}}

def c842.parse.c29(hit: Bool, +t: U32) -> C842Step:
  match hit:
    case True{}:
      C842Step{c842.parse.want(C842WCount{}, 3n), C842ENone{}}
    case False{}:
      c842.parse.c30(U32.is_eq(t, 30))

def c842.parse.c28(hit: Bool, +t: U32) -> C842Step:
  match hit:
    case True{}:
      C842Step{c842.parse.code_next(), C842EZero{}}
    case False{}:
      c842.parse.c29(U32.is_eq(t, 29), t)

def c842.parse.c27(hit: Bool, +t: U32) -> C842Step:
  match hit:
    case True{}:
      C842Step{c842.parse.want(C842WRepeat{}, 6n), C842ENone{}}
    case False{}:
      c842.parse.c28(U32.is_eq(t, 28), t)

def c842.parse.code.at(lt: Bool, +t: U32) -> C842Step:
  match lt:
    case True{}:
      c842.parse.chunk(c842.template(t), t)
    case False{}:
      c842.parse.c27(U32.is_eq(t, 27), t)

def c842.parse.code(+t: U32) -> C842Step:
  c842.parse.code.at(U32.is_lt(t, 26), t)

# a literal's 16 bits, read in reverse: the second byte's, then the first's
def c842.parse.lit(bs: List<&2, Bool>) -> C842Event:
  match bs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, Con{c5, Con{c6, Con{c7, Con{c8, Con{c9, Con{c10, Con{c11, Con{c12, Con{c13, Con{c14, Con{c15, rest}}}}}}}}}}}}}}}}:
      C842ELit{Bi.c842.byte.of(c8, c9, c10, c11, c12, c13, c14, c15), Bi.c842.byte.of(c0, c1, c2, c3, c4, c5, c6, c7)}
    case _:
      C842ELit{0, 0}

def c842.parse.field(k: C842Kind, bs: List<&2, Bool>) -> C842Event:
  match k:
    case C842LL{}:
      c842.parse.lit(bs)
    case C842P2{}:
      C842EPtr{C842P2{}, c842.fmt.value(bs)}
    case C842P4{}:
      C842EPtr{C842P4{}, c842.fmt.value(bs)}
    case C842P8{}:
      C842EPtr{C842P8{}, c842.fmt.value(bs)}

def c842.parse.count(zero: Bool, +n: Nat) -> C842Step:
  match zero:
    case True{}:
      C842Step{c842.parse.code_next(), C842EBad{E.C842BadShort{}}}
    case False{}:
      C842Step{c842.parse.want(C842WShort{n}, 8n), C842EShortStart{n}}

# after a short data byte, n of them left counting it
def c842.parse.short_next(n: Nat) -> C842Parser:
  match n:
    case 0n:
      c842.parse.code_next()
    case 1n+m:
      match m:
        case 0n:
          c842.parse.code_next()
        case 1n+r:
          c842.parse.want(C842WShort{1n+r}, 8n)

# a unit's last bit has come: what it was
def c842.parse.finish(w: C842Want, bs: List<&2, Bool>) -> C842Step:
  match w:
    case C842WCode{}:
      c842.parse.code(c842.fmt.value(bs))
    case C842WField{k, more}:
      C842Step{c842.parse.next_field(more), c842.parse.field(k, bs)}
    case C842WRepeat{}:
      C842Step{c842.parse.code_next(), C842ERepeat{c842.fmt.value(bs)}}
    case C842WCount{}:
      +v = c842.fmt.value(bs)
      c842.parse.count(U32.is_eq(v, 0), U32.to_nat(v))
    case C842WShort{n}:
      C842Step{c842.parse.short_next(n), C842EShort{Bi.c842.byte.of_rev(bs)}}
    case C842WCrc{}:
      C842Step{c842.parse.want(C842WEnd{}, 1n), C842EEnd{Bi.c842.word.of(bs)}}
    case C842WEnd{}:
      C842Step{c842.parse.want(C842WEnd{}, 1n), C842ENone{}}

def c842.parse.at(left: Nat, w: C842Want, bs: List<&2, Bool>) -> C842Step:
  match left:
    case 0n:
      c842.parse.finish(w, bs)
    case 1n+r:
      match r:
        case 0n:
          c842.parse.finish(w, bs)
        case 1n+s:
          C842Step{C842Parser{w, bs, 1n+s}, C842ENone{}}

# one bit
def C842Parser.step(p: C842Parser, b: Bool) -> C842Step:
  match p:
    case C842Parser{w, got, left}:
      c842.parse.at(left, w, Con{b, got})

# A whole stream as tokens

# the tokens so far (reversed), the chunk being read (its code and fields,
# reversed) or the short data being read (its bytes, reversed)
type C842Open is Data:
  C842ONone{}
  C842OChunk{t: U32, fs: List<&2, C842Field>}
  C842OShort{bs: List<&2, U32>}

type C842Toks is Data:
  C842TGoing{p: C842Parser, ts: List<&2, C842Token>, open: C842Open}
  C842TDone{ts: List<&2, C842Token>}
  C842TBad{e: E.C842Error}

def c842.tok.close(o: C842Open, ts: List<&2, C842Token>) -> List<&2, C842Token>:
  match o:
    case C842ONone{}:
      ts
    case C842OChunk{t, fs}:
      Con{C842Chunk{t, List.reverse(&2, C842Field, fs)}, ts}
    case C842OShort{bs}:
      Con{C842Short{List.reverse(&2, U32, bs)}, ts}

def c842.tok.add_field(o: C842Open, f: C842Field) -> C842Open:
  match o:
    case C842OChunk{t, fs}:
      C842OChunk{t, Con{f, fs}}
    case _:
      o

def c842.tok.add_byte(o: C842Open, b: U32) -> C842Open:
  match o:
    case C842OShort{bs}:
      C842OShort{Con{b, bs}}
    case _:
      o

def c842.tok.event(p: C842Parser, ev: C842Event, ts: List<&2, C842Token>, o: C842Open) -> C842Toks:
  match ev:
    case C842ENone{}:
      C842TGoing{p, ts, o}
    case C842ETemplate{t}:
      C842TGoing{p, c842.tok.close(o, ts), C842OChunk{t, Nil{}}}
    case C842ELit{hi, lo}:
      C842TGoing{p, ts, c842.tok.add_field(o, C842Lit{hi, lo})}
    case C842EPtr{k, i}:
      C842TGoing{p, ts, c842.tok.add_field(o, C842Ptr{i})}
    case C842ERepeat{n}:
      C842TGoing{p, Con{C842Repeat{n}, c842.tok.close(o, ts)}, C842ONone{}}
    case C842EZero{}:
      C842TGoing{p, Con{C842Zero{}, c842.tok.close(o, ts)}, C842ONone{}}
    case C842EShortStart{n}:
      C842TGoing{p, c842.tok.close(o, ts), C842OShort{Nil{}}}
    case C842EShort{b}:
      C842TGoing{p, ts, c842.tok.add_byte(o, b)}
    case C842EEnd{c}:
      C842TDone{List.reverse(&2, C842Token, Con{C842End{c}, c842.tok.close(o, ts)})}
    case C842EBad{e}:
      C842TBad{e}

def c842.tok.apply(s: C842Step, ts: List<&2, C842Token>, o: C842Open) -> C842Toks:
  match s:
    case C842Step{p, ev}:
      c842.tok.event(p, ev, ts, o)

def c842.tok.go(bs: List<&2, Bool>, st: C842Toks) -> C842Toks:
  match bs:
    case Nil{}:
      st
    case Con{b, t}:
      match st:
        case C842TGoing{p, ts, o}:
          c842.tok.go(t, c842.tok.apply(C842Parser.step(p, b), ts, o))
        case _:
          st

# a stream's tokens, up to and including the end (what follows is ignored);
# this reads the format only: pointers, repeats and the CRC are not checked
# (decode.bend does that)
def c842.tok.result(st: C842Toks) -> Result<&2, &2, E.C842Error, List<&2, C842Token>>:
  match st:
    case C842TGoing{p, ts, op}:
      Fail{E.C842Truncated{}}
    case C842TDone{ts}:
      Done{ts}
    case C842TBad{e}:
      Fail{e}

def c842.tokens(o: B.Octets) -> Result<&2, &2, E.C842Error, List<&2, C842Token>>:
  c842.tok.result(c842.tok.go(c842.unpack(o), C842TGoing{C842Parser.start(), Nil{}, C842ONone{}}))

# The worst case

# the most bits a stream of n bytes needs before padding: 69 bits for each
# 8-byte chunk (the paper's maximum: a 5-bit template and four 16-bit
# literals), 5 + 3 + 8k bits for a tail of k bytes as short data, and 37
# bits for the end and its CRC
def c842.worst_bits(n: Nat) -> Nat:
  match n:
    case 0n:
      37n
    case 1n+a:
      match a:
        case 0n:
          53n
        case 1n+b:
          match b:
            case 0n:
              61n
            case 1n+c:
              match c:
                case 0n:
                  69n
                case 1n+d:
                  match d:
                    case 0n:
                      77n
                    case 1n+e:
                      match e:
                        case 0n:
                          85n
                        case 1n+f:
                          match f:
                            case 0n:
                              93n
                            case 1n+g:
                              match g:
                                case 0n:
                                  101n
                                case 1n+h:
                                  Nat.add(69n, c842.worst_bits(h))

def c842.words.at(qr: Nat & Nat) -> Nat:
  (q, r) = qr
  match r:
    case 0n:
      q
    case 1n+s:
      1n+q

# the most bytes a stream of n bytes needs: worst_bits(n), padded to whole
# 8-byte words
def c842.worst_bytes(n: Nat) -> Nat:
  Nat.mul(8n, c842.words.at(Nat.divmod(c842.worst_bits(n), 64n)))
