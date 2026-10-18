# bend-osdev-c842, the decoder: a stream's bits in, its bytes out.
#
# The parser (format.bend) announces each field as its last bit arrives,
# and the decoder acts on it at once, so that every failure is found where
# Linux finds it (ref/OBSERVATIONS.md, E7):
#
#   a literal       its two bytes
#   a pointer       s bytes (s = 2, 4, 8) from the position p below: the
#                   latest p congruent to index * s modulo the history
#                   (512 bytes for P2, 2048 for P4 and P8, as the paper's
#                   ring histories) with p below the output's length rounded
#                   down to 8 (E3, E6). No such p: C842BadPointer
#   RPT, field f    f + 1 copies of the last 8 bytes (E1). Fewer than 8
#                   bytes of output: C842BadRepeat (Linux refuses an empty
#                   output and reads before its buffer otherwise: E7, E8)
#   Z8              8 zero bytes
#   short data      its bytes (count 0: C842BadShort, from the parser)
#   the end         the CRC must be the output's (crc.bend): C842BadCrc
#
# A byte past the maximum output is C842OutputTooLarge; input that ends
# before the end and its CRC is C842Truncated; whatever follows the CRC is
# ignored (E2). Every byte is written through c842.dec.push, the only place
# the output grows.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./format.bend as F
import ./window.bend as W
import ./crc.bend as K

# the output so far (reversed), its length, the window over it, and the room
# left; or the output, after the end; or a failure
type C842Run is Data:
  C842Going{acc: List<&2, U32>, n: U32, win: W.C842Win, room: Nat}
  C842Finished{out: B.Octets}
  C842Failed{e: E.C842Error}

type C842Dec is Data:
  C842Dec{p: F.C842Parser, run: C842Run}

# a decoder that may write max bytes
def c842.dec.start(max: Nat) -> C842Dec:
  C842Dec{F.C842Parser.start(), C842Going{Nil{}, 0, W.c842.win.empty(), max}}

# one more byte of output
def c842.dec.push(r: C842Run, +b: U32) -> C842Run:
  match r:
    case C842Going{acc, +n, win, room}:
      match room:
        case 0n:
          C842Failed{E.C842OutputTooLarge{}}
        case 1n+q:
          C842Going{Con{b, acc}, U32.add(n, 1), W.c842.win.put(win, n, b), q}
    case _:
      r

def c842.dec.pushes(xs: List<&2, U32>, r: C842Run) -> C842Run:
  match xs:
    case Nil{}:
      r
    case Con{x, t}:
      c842.dec.pushes(t, c842.dec.push(r, x))

# Pointers

def c842.dec.pos.wrap(lt: Bool, +p0: U32, h: U32) -> Maybe<&2, U32>:
  match lt:
    case True{}:
      None{}
    case False{}:
      Some{U32.sub(p0, h)}

def c842.dec.pos.at(below: Bool, +p0: U32, +h: U32) -> Maybe<&2, U32>:
  match below:
    case True{}:
      Some{p0}
    case False{}:
      c842.dec.pos.wrap(U32.is_lt(p0, h), p0, h)

# the position a pointer reads: base + index * size, where base is the
# output's length rounded down to 8 (t8) and then to the history h; less h if
# that is t8 or more; none if that would be below 0
def c842.dec.pos(+n: U32, idx: U32, size: U32, +h: U32) -> Maybe<&2, U32>:
  +t8 = U32.and(n, 4294967288)
  +p0 = U32.add(U32.and(t8, U32.sub(0, h)), U32.mul(idx, size))
  c842.dec.pos.at(U32.is_lt(p0, t8), p0, h)

def c842.dec.byte_at(r: C842Run, p: U32) -> U32:
  match r:
    case C842Going{acc, n, win, room}:
      W.c842.win.get(win, p)
    case _:
      0

# k bytes from position p on
def c842.dec.copy(k: Nat, +p: U32, +r: C842Run) -> C842Run:
  match k:
    case 0n:
      r
    case 1n+j:
      c842.dec.copy(j, U32.add(p, 1), c842.dec.push(r, c842.dec.byte_at(r, p)))

def c842.dec.ptr.at(m: Maybe<&2, U32>, +k: F.C842Kind, +r: C842Run) -> C842Run:
  match m:
    case None{}:
      C842Failed{E.C842BadPointer{}}
    case Some{p}:
      c842.dec.copy(U32.to_nat(F.C842Kind.size(k)), p, r)

def c842.dec.ptr(+k: F.C842Kind, idx: U32, +r: C842Run) -> C842Run:
  match r:
    case C842Going{acc, +n, win, room}:
      c842.dec.ptr.at(c842.dec.pos(n, idx, F.C842Kind.size(k), F.C842Kind.history(k)), k, C842Going{acc, n, win, room})
    case _:
      r

# RPT

# the last 8 bytes, in order, if there are 8
def c842.dec.last8(acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match acc:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, rest}}}}}}}}:
      Some{[a7, a6, a5, a4, a3, a2, a1, a0]}
    case _:
      None{}

def c842.dec.reps(k: Nat, +xs: List<&2, U32>, r: C842Run) -> C842Run:
  match k:
    case 0n:
      r
    case 1n+j:
      c842.dec.reps(j, xs, c842.dec.pushes(xs, r))

def c842.dec.rpt.at(m: Maybe<&2, List<&2, U32>>, k: Nat, r: C842Run) -> C842Run:
  match m:
    case None{}:
      C842Failed{E.C842BadRepeat{}}
    case Some{xs}:
      c842.dec.reps(k, xs, r)

def c842.dec.rpt(f: U32, r: C842Run) -> C842Run:
  match r:
    case C842Going{+acc, n, win, room}:
      c842.dec.rpt.at(c842.dec.last8(acc), 1n+U32.to_nat(f), C842Going{acc, n, win, room})
    case _:
      r

# The end: the CRC

def c842.dec.weq(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          Bool.and(Bool.not(Bool.xor(x, y)), c842.dec.weq(p, s, t))

def c842.u32_same(a: U32, b: U32) -> Bool:
  match a b:
    case U32{x} U32{y}:
      c842.dec.weq(32n, x, y)

def c842.dec.end.at(ok: Bool, out: B.Octets) -> C842Run:
  match ok:
    case True{}:
      C842Finished{out}
    case False{}:
      C842Failed{E.C842BadCrc{}}

def c842.dec.end.out(c: U32, +out: B.Octets) -> C842Run:
  c842.dec.end.at(c842.u32_same(c, K.c842.crc(out)), out)

def c842.dec.end(c: U32, r: C842Run) -> C842Run:
  match r:
    case C842Going{acc, n, win, room}:
      c842.dec.end.out(c, B.Octets.of_list(B.rev(acc)))
    case _:
      r

# Events and bits

def c842.dec.event(ev: F.C842Event, r: C842Run) -> C842Run:
  match ev:
    case F.C842ENone{}:
      r
    case F.C842ETemplate{t}:
      r
    case F.C842ELit{hi, lo}:
      c842.dec.push(c842.dec.push(r, hi), lo)
    case F.C842EPtr{k, i}:
      c842.dec.ptr(k, i, r)
    case F.C842ERepeat{f}:
      c842.dec.rpt(f, r)
    case F.C842EZero{}:
      c842.dec.pushes([0, 0, 0, 0, 0, 0, 0, 0], r)
    case F.C842EShortStart{k}:
      r
    case F.C842EShort{b}:
      c842.dec.push(r, b)
    case F.C842EEnd{c}:
      c842.dec.end(c, r)
    case F.C842EBad{e}:
      C842Failed{e}

def c842.dec.step(s: F.C842Step, r: C842Run) -> C842Dec:
  match s:
    case F.C842Step{p, ev}:
      C842Dec{p, c842.dec.event(ev, r)}

# one bit: a finished or failed decoder takes no more
def c842.dec.bit(d: C842Dec, b: Bool) -> C842Dec:
  match d:
    case C842Dec{p, r}:
      match r:
        case C842Going{acc, n, win, room}:
          c842.dec.step(F.C842Parser.step(p, b), C842Going{acc, n, win, room})
        case _:
          C842Dec{p, r}

def c842.dec.go(bs: List<&2, Bool>, d: C842Dec) -> C842Dec:
  match bs:
    case Nil{}:
      d
    case Con{b, t}:
      c842.dec.go(t, c842.dec.bit(d, b))

def c842.dec.result(d: C842Dec) -> Result<&2, &2, E.C842Error, B.Octets>:
  match d:
    case C842Dec{p, r}:
      match r:
        case C842Going{acc, n, win, room}:
          Fail{E.C842Truncated{}}
        case C842Finished{o}:
          Done{o}
        case C842Failed{e}:
          Fail{e}

# The stream src's bytes, at most max of them
def c842.decompress(src: B.Octets, max: Nat) -> Result<&2, &2, E.C842Error, B.Octets>:
  c842.dec.result(c842.dec.go(F.c842.unpack(src), c842.dec.start(max)))

# Streaming: feed a stream in pieces, then finish

def c842.reader_start(max: Nat) -> C842Dec:
  c842.dec.start(max)

def c842.reader_feed(d: C842Dec, piece: B.Octets) -> C842Dec:
  c842.dec.go(F.c842.unpack(piece), d)

def c842.reader_finish(d: C842Dec) -> Result<&2, &2, E.C842Error, B.Octets>:
  c842.dec.result(d)

def c842.reader.go(ps: List<&2, B.Octets>, d: C842Dec) -> C842Dec:
  match ps:
    case Nil{}:
      d
    case Con{p, t}:
      c842.reader.go(t, c842.reader_feed(d, p))

# a stream fed to a reader in these pieces
def c842.reader_decompress(max: Nat, ps: List<&2, B.Octets>) -> Result<&2, &2, E.C842Error, B.Octets>:
  c842.reader_finish(c842.reader.go(ps, c842.reader_start(max)))
