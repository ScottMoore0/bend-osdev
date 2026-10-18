# bend-osdev-lzo, LZO1X decompression, written from the Linux kernel's
# documentation file Documentation/staging/lzo.rst ("LZO stream format as
# understood by Linux's LZO decompressor"), a prose description of the
# bitstream; no LZO source code was read (see README.md).
#
# A stream is a run of instructions. Each instruction's first byte holds an
# opcode and operands; more bytes may follow (length bytes, a distance, the
# literals). The first byte of a stream is read differently (18 to 255 open
# with a run of literals), and the meaning of an instruction byte below 16
# depends on how many literals the instruction before it copied: the
# "state" the documentation describes, kept here as an LzoCls.
#
#   first byte 18..255   copy (byte - 17) literals
#   0000LLLL (state 0)   copy 3 + L literals (L = 0: 18 + length bytes)
#   0000DDSS (1 to 3)    M1: copy 2 bytes, distance (H << 2) + D + 1
#   0000DDSS (4 or more) M1: copy 3 bytes, distance (H << 2) + D + 2049
#   0001HLLL             M4: copy 2 + L bytes (L = 0: 9 + length bytes),
#                        distance 16384 + (H << 14) + D (two more bytes, LE16
#                        DDDDDDDD:DDDDDDSS); distance 16384 is the end marker
#   001LLLLL             M3: copy 2 + L bytes (L = 0: 33 + length bytes),
#                        distance D + 1 (two more bytes, as M4)
#   01LDDDSS             M2: copy 3 + L bytes, distance (H << 3) + D + 1
#   1LLDDDSS             M2: copy 5 + L bytes, distance (H << 3) + D + 1
#
# H is the byte after the opcode (M1, M2). Length bytes: each zero byte adds
# 255 and goes on; the first non-zero byte adds itself and ends. After a
# match, S (0 to 3) literals follow, and S is the next instruction's state.
#
# The decoder takes the stream and a maximum output size and answers
# Fail{e} for every malformed stream: a match before the start of the output
# (LzoBadDistance), a stream cut short (LzoTruncated: the input ends before
# the end marker), an output past the maximum (LzoOutputTooLarge), bytes
# after the end marker (LzoTrailing). It reads the input one byte at a time,
# never past its end, and never writes more than the maximum.
#
# Each byte is read in two parts: dec.trans says what it does (pure parsing,
# no output), and dec.apply does it (the only place the output grows).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./window.bend as W

# How many literals the last instruction copied (the documentation's state):
# none yet, at the first byte; none; 1 to 3; 4 or more
type LzoCls is Data:
  LzoFirst{}
  LzoZero{}
  LzoFew{}
  LzoMany{}

# the instructions with a two-byte distance: M3, and M4 with its H bit
type LzoFar is Data:
  LzoM3{}
  LzoM4{far: Bool}

# What the next byte is: an instruction (after a class); a length byte of a
# literal run (n so far); a literal (n left, then an instruction after class
# c); the distance byte of M1 or M2 (length, D bits, S, base, shift); a
# length byte of M3 or M4; the first or second distance byte of M3 or M4;
# past the end marker; or nothing, after a failure
type LzoSt is Data:
  LzoIns{c: LzoCls}
  LzoLitExt{n: Nat}
  LzoLit{n: Nat, c: LzoCls}
  LzoNear{len: Nat, d: U32, s: U32, base: U32, sh: Nat}
  LzoMatExt{n: Nat, k: LzoFar}
  LzoDist{len: Nat, k: LzoFar}
  LzoDist2{len: Nat, k: LzoFar, lo: U32}
  LzoEnd{}
  LzoBad{e: E.LzoError}

# st: what the next byte is; acc: the output so far, reversed; win: the
# window over the same bytes; room: how many more bytes the output may take
type LzoDec is Data:
  LzoDec{st: LzoSt, acc: List<&2, U32>, win: W.LzoWin, room: Nat}

# a stream's output, reversed, and the room left
type LzoOut is Data:
  LzoOut{acc: List<&2, U32>, room: Nat}

# a length byte: zero (255, and more follow) or the last one, with its value
type LzoExt is Data:
  LzoExtZero{}
  LzoExtLast{v: Nat}

# What one byte does: move to a state; write a literal, then move to a
# state; copy a match (len bytes o + 1 back, then s literals)
type LzoAct is Data:
  LzoGo{st: LzoSt}
  LzoPush{h: U32, st: LzoSt}
  LzoCopy{o: Nat, len: Nat, s: Nat}

def dec.ext.pick(zero: Bool, b: U32) -> LzoExt:
  match zero:
    case True{}:
      LzoExtZero{}
    case False{}:
      LzoExtLast{U32.to_nat(b)}

def dec.ext(+h: U32) -> LzoExt:
  dec.ext.pick(U32.is_eq(h, 0), h)

# Matches: their distance and length fields

# M1 and M2: the distance byte H; distance - 1 = base + (H << sh) + D
def dec.near(len: Nat, d: U32, s: U32, base: U32, sh: Nat, h: U32) -> LzoAct:
  LzoCopy{U32.to_nat(U32.add(base, U32.or(U32.shln(h, sh), d))), len, U32.to_nat(s)}

# M3 and M4: the 14 D bits of the LE16 distance field, and its 2 S bits
def dec.d14(lo: U32, hi: U32) -> U32:
  U32.shrn(U32.or(lo, U32.shln(hi, 8n)), 2n)

def dec.s2(lo: U32) -> Nat:
  U32.to_nat(U32.and(lo, 3))

# M4 with H = 0: distance 16384 (D = 0) is the end marker
def dec.m4.end(eos: Bool, len: Nat, +lo: U32, hi: U32) -> LzoAct:
  match eos:
    case True{}:
      LzoGo{LzoEnd{}}
    case False{}:
      LzoCopy{U32.to_nat(U32.add(16383, dec.d14(lo, hi))), len, dec.s2(lo)}

def dec.m4(far: Bool, len: Nat, +lo: U32, +hi: U32) -> LzoAct:
  match far:
    case True{}:
      LzoCopy{U32.to_nat(U32.add(32767, dec.d14(lo, hi))), len, dec.s2(lo)}
    case False{}:
      dec.m4.end(Bool.and(U32.is_lt(lo, 4), U32.is_eq(hi, 0)), len, lo, hi)

# the second distance byte of M3 or M4
def dec.dist2(k: LzoFar, len: Nat, +lo: U32, hi: U32) -> LzoAct:
  match k:
    case LzoM3{}:
      LzoCopy{U32.to_nat(dec.d14(lo, hi)), len, dec.s2(lo)}
    case LzoM4{far}:
      dec.m4(far, len, lo, hi)

# Instructions

# a length field of M3 or M4: 0 means length bytes follow
def dec.mlen(zero: Bool, base: Nat, len: Nat, k: LzoFar) -> LzoAct:
  match zero:
    case True{}:
      LzoGo{LzoMatExt{base, k}}
    case False{}:
      LzoGo{LzoDist{len, k}}

# 0001HLLL (16 to 31): M4
def dec.m4i(+h: U32) -> LzoAct:
  +l = U32.and(h, 7)
  dec.mlen(U32.is_eq(l, 0), 9n, Nat.add(2n, U32.to_nat(l)), LzoM4{U32.is_eq(U32.and(h, 8), 8)})

# 001LLLLL (32 to 63): M3
def dec.m3i(+h: U32) -> LzoAct:
  +l = U32.and(h, 31)
  dec.mlen(U32.is_eq(l, 0), 33n, Nat.add(2n, U32.to_nat(l)), LzoM3{})

# 01LDDDSS and 1LLDDDSS (64 to 255): M2, of 1 + (byte >> 5) bytes
def dec.m2i(+h: U32) -> LzoAct:
  LzoGo{LzoNear{Nat.add(1n, U32.to_nat(U32.shrn(h, 5n))), U32.and(U32.shrn(h, 2n), 7), U32.and(h, 3), 0, 3n}}

# 0000LLLL after no literals: a run of 4 literals or more
def dec.run.pick(zero: Bool, h: U32) -> LzoAct:
  match zero:
    case True{}:
      LzoGo{LzoLitExt{18n}}
    case False{}:
      LzoGo{LzoLit{Nat.add(3n, U32.to_nat(h)), LzoMany{}}}

def dec.run(+h: U32) -> LzoAct:
  dec.run.pick(U32.is_eq(h, 0), h)

# 0 to 15: what it means depends on the literals before it
def dec.low(c: LzoCls, +h: U32) -> LzoAct:
  match c:
    case LzoFirst{}:
      dec.run(h)
    case LzoZero{}:
      dec.run(h)
    case LzoFew{}:
      LzoGo{LzoNear{2n, U32.shrn(h, 2n), U32.and(h, 3), 0, 2n}}
    case LzoMany{}:
      LzoGo{LzoNear{3n, U32.shrn(h, 2n), U32.and(h, 3), 2048, 2n}}

def dec.first.cls(few: Bool) -> LzoCls:
  match few:
    case True{}:
      LzoFew{}
    case False{}:
      LzoMany{}

# the first byte, 18 to 255: byte - 17 literals
def dec.first(h: U32) -> LzoAct:
  +n = Nat.sub(U32.to_nat(h), 17n)
  LzoGo{LzoLit{n, dec.first.cls(Nat.is_lt(n, 4n))}}

# 18 to 255, not the first byte
def dec.high(lt32: Bool, lt64: Bool, +h: U32) -> LzoAct:
  match lt32 lt64:
    case True{} _:
      dec.m4i(h)
    case False{} True{}:
      dec.m3i(h)
    case False{} False{}:
      dec.m2i(h)

# 16 and up: 16 and 17 are M4 everywhere; 18 and up open a stream with
# literals
def dec.top(lt18: Bool, c: LzoCls, +h: U32) -> LzoAct:
  match lt18:
    case True{}:
      dec.m4i(h)
    case False{}:
      match c:
        case LzoFirst{}:
          dec.first(h)
        case _:
          dec.high(U32.is_lt(h, 32), U32.is_lt(h, 64), h)

def dec.ins.pick(lt16: Bool, c: LzoCls, +h: U32) -> LzoAct:
  match lt16:
    case True{}:
      dec.low(c, h)
    case False{}:
      dec.top(U32.is_lt(h, 18), c, h)

# an instruction byte, after literals of class c
def dec.ins(c: LzoCls, +h: U32) -> LzoAct:
  dec.ins.pick(U32.is_lt(h, 16), c, h)

# Literals and length bytes

# n literals left: copy this one; none left: this byte is an instruction
def dec.lit(n: Nat, c: LzoCls, +h: U32) -> LzoAct:
  match n:
    case 0n:
      dec.ins(c, h)
    case 1n+p:
      LzoPush{h, LzoLit{p, c}}

def dec.litext(e: LzoExt, n: Nat) -> LzoAct:
  match e:
    case LzoExtZero{}:
      LzoGo{LzoLitExt{Nat.add(255n, n)}}
    case LzoExtLast{v}:
      LzoGo{LzoLit{Nat.add(v, n), LzoMany{}}}

def dec.matext(e: LzoExt, n: Nat, k: LzoFar) -> LzoAct:
  match e:
    case LzoExtZero{}:
      LzoGo{LzoMatExt{Nat.add(255n, n), k}}
    case LzoExtLast{v}:
      LzoGo{LzoDist{Nat.add(v, n), k}}

# what the byte h does in state st (reading only: nothing is written here)
def dec.trans(st: LzoSt, +h: U32) -> LzoAct:
  match st:
    case LzoIns{c}:
      dec.ins(c, h)
    case LzoLitExt{n}:
      dec.litext(dec.ext(h), n)
    case LzoLit{n, c}:
      dec.lit(n, c, h)
    case LzoNear{len, dd, s, base, sh}:
      dec.near(len, dd, s, base, sh, h)
    case LzoMatExt{n, k}:
      dec.matext(dec.ext(h), n, k)
    case LzoDist{len, k}:
      LzoGo{LzoDist2{len, k, h}}
    case LzoDist2{len, k, lo}:
      dec.dist2(k, len, lo, h)
    case LzoEnd{}:
      LzoGo{LzoBad{E.LzoTrailing{}}}
    case LzoBad{e}:
      LzoGo{LzoBad{e}}

# Writing: the output and the window grow only here

# what follows a match: S literals, then an instruction after their class
def dec.after(s: Nat) -> LzoSt:
  match s:
    case 0n:
      LzoIns{LzoZero{}}
    case 1n+p:
      LzoLit{1n+p, LzoFew{}}

# n bytes, each the one o + 1 back; the copy may overlap what it writes
def dec.copy.go(n: Nat, room: Nat, +o: Nat, s: Nat, acc: List<&2, U32>, +win: W.LzoWin) -> LzoDec:
  match n:
    case 0n:
      LzoDec{dec.after(s), acc, win, room}
    case 1n+p:
      match room:
        case 0n:
          LzoDec{LzoBad{E.LzoOutputTooLarge{}}, acc, win, 0n}
        case 1n+r:
          +v = W.win.get(win, o)
          dec.copy.go(p, r, o, s, Con{v, acc}, W.win.put(win, v))

def dec.copy.check(ok: Bool, len: Nat, o: Nat, s: Nat, acc: List<&2, U32>, win: W.LzoWin, room: Nat) -> LzoDec:
  match ok:
    case True{}:
      dec.copy.go(len, room, o, s, acc, win)
    case False{}:
      LzoDec{LzoBad{E.LzoBadDistance{}}, acc, win, room}

# a match o + 1 back, after count bytes of output: refused when it reaches
# before the start (so with no output, at every distance); the byte at the
# distance exists, and the copy only adds bytes, so every later byte it reads
# exists too
def dec.copy.at(count: Nat, +o: Nat, len: Nat, s: Nat, acc: List<&2, U32>, win: W.LzoWin, room: Nat) -> LzoDec:
  match count:
    case 0n:
      LzoDec{LzoBad{E.LzoBadDistance{}}, acc, win, room}
    case 1n+c:
      dec.copy.check(Nat.is_lt(o, 1n+c), len, o, s, acc, win, room)

def dec.apply(a: LzoAct, acc: List<&2, U32>, +win: W.LzoWin, room: Nat) -> LzoDec:
  match a:
    case LzoGo{st}:
      LzoDec{st, acc, win, room}
    case LzoPush{+h, st}:
      match room:
        case 0n:
          LzoDec{LzoBad{E.LzoOutputTooLarge{}}, acc, win, 0n}
        case 1n+r:
          LzoDec{st, Con{h, acc}, W.win.put(win, h), r}
    case LzoCopy{o, len, s}:
      dec.copy.at(W.win.count(win), o, len, s, acc, win, room)

# The decoder: one byte at a time

def dec.step(d: LzoDec, +h: U32) -> LzoDec:
  match d:
    case LzoDec{st, acc, win, room}:
      dec.apply(dec.trans(st, h), acc, win, room)

def dec.go(xs: List<&2, U32>, d: LzoDec) -> LzoDec:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      dec.go(t, dec.step(d, h))

# the end of the input: right after the end marker, or the stream is cut
def dec.end(d: LzoDec) -> Result<&2, &2, E.LzoError, LzoOut>:
  match d:
    case LzoDec{st, acc, win, room}:
      match st:
        case LzoEnd{}:
          Done{LzoOut{acc, room}}
        case LzoBad{e}:
          Fail{e}
        case _:
          Fail{E.LzoTruncated{}}

# the decoder before the first byte, with room bytes
def dec.start(room: Nat) -> LzoDec:
  LzoDec{LzoIns{LzoFirst{}}, Nil{}, W.win.empty(), room}

def dec.run_list(src: List<&2, U32>, room: Nat) -> Result<&2, &2, E.LzoError, LzoOut>:
  dec.end(dec.go(src, dec.start(room)))

def dec.out(r: Result<&2, &2, E.LzoError, LzoOut>) -> Result<&2, &2, E.LzoError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{LzoOut{acc, room}}:
      Done{B.Octets.of_list(B.rev(acc))}

# The public interface: one-shot

# the bytes of the LZO1X stream src, at most max of them
def lzo1x_decompress(src: B.Octets, max: Nat) -> Result<&2, &2, E.LzoError, B.Octets>:
  dec.out(dec.run_list(B.Octets.to_list(src), max))

# The public interface: streaming. Feed the stream in pieces; each piece
# answers the bytes it completes; finish checks the stream ended at its end
# marker. The reader keeps the window, not the output.

type LzoReader is Data:
  LzoReader{d: LzoDec}

type LzoRead is Data:
  LzoRead{reader: LzoReader, bytes: B.Octets}

def reader_start(max: Nat) -> LzoReader:
  LzoReader{dec.start(max)}

def rd.err(st: LzoSt) -> Maybe<&2, E.LzoError>:
  match st:
    case LzoBad{e}:
      Some{e}
    case _:
      None{}

def rd.fed.pick(m: Maybe<&2, E.LzoError>, st: LzoSt, acc: List<&2, U32>, win: W.LzoWin, room: Nat) -> Result<&2, &2, E.LzoError, LzoRead>:
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{LzoRead{LzoReader{LzoDec{st, Nil{}, win, room}}, B.Octets.of_list(B.rev(acc))}}

def rd.fed(d: LzoDec) -> Result<&2, &2, E.LzoError, LzoRead>:
  match d:
    case LzoDec{+st, acc, win, room}:
      rd.fed.pick(rd.err(st), st, acc, win, room)

# the next piece of the stream: the bytes it completes, or the failure
def reader_feed(r: LzoReader, src: B.Octets) -> Result<&2, &2, E.LzoError, LzoRead>:
  match r:
    case LzoReader{d}:
      rd.fed(dec.go(B.Octets.to_list(src), d))

def rd.fin(r: Result<&2, &2, E.LzoError, LzoOut>) -> Result<&2, &2, E.LzoError, Nat>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{LzoOut{acc, room}}:
      Done{room}

# the end of the input: Done{n} when the stream ended at its end marker (n:
# the room left), else the failure
def reader_finish(r: LzoReader) -> Result<&2, &2, E.LzoError, Nat>:
  match r:
    case LzoReader{d}:
      rd.fin(dec.end(d))

def rd.fin.all(r: Result<&2, &2, E.LzoError, Nat>, out: B.Octets) -> Result<&2, &2, E.LzoError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{n}:
      Done{out}

# feed the pieces ps, after the reader's answer r, joining the bytes out
def rd.all(ps: List<&2, B.Octets>, r: Result<&2, &2, E.LzoError, LzoRead>, out: B.Octets) -> Result<&2, &2, E.LzoError, B.Octets>:
  match ps:
    case Nil{}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{LzoRead{rd, bytes}}:
          rd.fin.all(reader_finish(rd), B.Octets.append(out, bytes))
    case Con{p, t}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{LzoRead{rd, bytes}}:
          rd.all(t, reader_feed(rd, p), B.Octets.append(out, bytes))

# the stream fed to a reader in the pieces ps, then finished: the bytes of
# every piece, joined (LAWS.bend: the same as decoding the pieces joined)
def reader_decompress(max: Nat, ps: List<&2, B.Octets>) -> Result<&2, &2, E.LzoError, B.Octets>:
  rd.all(ps, rd.fed(dec.start(max)), B.Octets.empty())
