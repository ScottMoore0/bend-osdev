# A TCP segment as a connection sees it, and its wire form.
#
# A connection works on TcpSeg: sequence and acknowledgment numbers, the
# control bits, the window, the MSS option (RFC 9293 section 3.7.1) and the
# data. Ports and addresses belong to the demultiplexer, which turns a
# TcpSeg into a header (bend-osdev-netheaders' TcpHeader) and back.
import Base
import ../bytes/bytes.bend as B
import ../netheaders/tcp.bend as NT

# flags: the control bits, as in NT.TcpHeader's flags field (FIN 1, SYN 2,
# RST 4, PSH 8, ACK 16, URG 32); mss: the MSS option, on a SYN
type TcpSeg is Data:
  TcpSeg{seq: U32, ack: U32, flags: U32, wnd: U32, mss: Maybe<&2, U32>, data: B.Octets}

# whether the control bit mask is set in flags
def TcpSeg.has(+flags: U32, mask: U32) -> Bool:
  U32.is_ne(U32.and(flags, mask), 0)

def TcpSeg.flags(s: TcpSeg) -> U32:
  match s:
    case TcpSeg{q, a, f, w, m, d}:
      f

def TcpSeg.seq(s: TcpSeg) -> U32:
  match s:
    case TcpSeg{q, a, f, w, m, d}:
      q

def TcpSeg.ack(s: TcpSeg) -> U32:
  match s:
    case TcpSeg{q, a, f, w, m, d}:
      a

def TcpSeg.data(s: TcpSeg) -> B.Octets:
  match s:
    case TcpSeg{q, a, f, w, m, d}:
      d

def TcpSeg.syn(+s: TcpSeg) -> Bool:
  TcpSeg.has(TcpSeg.flags(s), NT.TcpHeader.SYN())

def TcpSeg.fin(+s: TcpSeg) -> Bool:
  TcpSeg.has(TcpSeg.flags(s), NT.TcpHeader.FIN())

def TcpSeg.rst(+s: TcpSeg) -> Bool:
  TcpSeg.has(TcpSeg.flags(s), NT.TcpHeader.RST())

def TcpSeg.is_ack(+s: TcpSeg) -> Bool:
  TcpSeg.has(TcpSeg.flags(s), NT.TcpHeader.ACK())

# The sequence space a segment occupies: its data, and one each for SYN and
# FIN (RFC 9293 section 3.4)
def TcpSeg.len(+s: TcpSeg) -> U32:
  U32.add(U32.from_nat(B.Octets.len(TcpSeg.data(s))), U32.add(Bool.to_u32(TcpSeg.syn(s)), Bool.to_u32(TcpSeg.fin(s))))

# The MSS option (kind 2, length 4, a 16-bit value)

def TcpSeg.mss_option(m: Maybe<&2, U32>) -> B.Octets:
  match m:
    case None{}:
      B.Octets.empty()
    case Some{v}:
      B.Octets.append(B.Octets.of_list([2, 4]), B.Octets.be16(v))

# The options are walked one at a time; each step first classifies the
# option at the head: 0 the end (or no bytes), 1 no operation, 2 MSS, 3 any
# other (skipped by its length byte; a length below 2 ends the walk)

def TcpSeg.opt.class.of(end: Bool, nop: Bool, mss: Bool) -> Nat:
  match end nop mss:
    case True{} _ _:
      0n
    case False{} True{} _:
      1n
    case False{} False{} True{}:
      2n
    case False{} False{} False{}:
      3n

def TcpSeg.opt.class(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+k, t}:
      TcpSeg.opt.class.of(U32.is_eq(k, 0), U32.is_eq(k, 1), U32.is_eq(k, 2))

# an option of length l: at least 2 bytes, else the walk stops
def TcpSeg.opt.skip(ok: Bool, +l: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      B.drop(l, xs)
    case False{}:
      Nil{}

def TcpSeg.opt.length(xs: List<&2, U32>) -> Nat:
  match xs:
    case Con{k, Con{l, t}}:
      U32.to_nat(l)
    case _:
      0n

def TcpSeg.opt.after(+xs: List<&2, U32>) -> List<&2, U32>:
  +l = TcpSeg.opt.length(xs)
  TcpSeg.opt.skip(Nat.is_ge(l, 2n), l, xs)

def TcpSeg.opt.mss(xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{k, Con{l, Con{a, Con{b, t}}}}:
      B.be16_at([a, b], 0n)
    case _:
      None{}

# the MSS option among the option bytes xs; c is TcpSeg.opt.class(xs), and
# fuel bounds the walk (40 bytes of options at most)
def TcpSeg.find_mss(fuel: Nat, +xs: List<&2, U32>, c: Nat) -> Maybe<&2, U32>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match c:
        case 0n:
          None{}
        case 1n:
          +t = B.drop(1n, xs)
          TcpSeg.find_mss(f, t, TcpSeg.opt.class(t))
        case 2n:
          TcpSeg.opt.mss(xs)
        case _:
          +t = TcpSeg.opt.after(xs)
          TcpSeg.find_mss(f, t, TcpSeg.opt.class(t))

def TcpSeg.parse_mss(o: B.Octets) -> Maybe<&2, U32>:
  +xs = B.Octets.to_list(o)
  TcpSeg.find_mss(41n, xs, TcpSeg.opt.class(xs))

# Wire form

# the segment of a parsed header and its payload
def TcpSeg.of_header(h: NT.TcpHeader, payload: B.Octets) -> TcpSeg:
  match h:
    case NT.TcpHeader{sp, dp, sq, ak, off, rs, fl, win, ck, ur, o}:
      TcpSeg{sq, ak, fl, win, TcpSeg.parse_mss(o), payload}

# the header (ports given, checksum zero: build_ipv4 computes it) of a
# segment; an MSS option makes the header 24 bytes
def TcpSeg.header(sport: U32, dport: U32, s: TcpSeg) -> NT.TcpHeader:
  match s:
    case TcpSeg{q, a, f, w, +m, d}:
      NT.TcpHeader{sport, dport, q, a, U32.add(5, U32.mul(Bool.to_u32(Maybe.is_some(&2, U32, m)), 1)), 0, f, w, 0, 0, TcpSeg.mss_option(m)}
