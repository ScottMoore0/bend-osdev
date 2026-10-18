# bend-osdev-c842, the encoder: bytes in, a stream out.
#
# c842.literals writes the simplest stream: every 8-byte chunk as template 0
# (four literals), a tail of 1 to 7 bytes as short data, the end and its CRC.
# That is the documented worst case: 69 bits a chunk (the paper), plus the
# tail and 37 bits (format.bend's c842.worst_bits).
#
# The encoder (c842.enc.tokens) takes the input a chunk at a time:
#   * a chunk equal to the one before is part of a run, written as RPT (field
#     f for f + 1 chunks; 64 at most, so a longer run takes several);
#   * otherwise, eight zero bytes are Z8;
#   * otherwise the matcher (match.bend) looks for the chunk's seven phrases
#     (one of 8 bytes, two of 4, four of 2), and the chunk is written with
#     the template of fewest bits whose pointers were all found (on a tie,
#     the lowest code); template 0 always qualifies;
#   * the tail is short data, then the end and the CRC.
#
# c842.compress_bits checks its stream: it decodes it, and answers the
# literal stream instead should the stream not give the input back or be
# longer than the literal stream (c842.worst_bits). So, for every input, what it writes
# decodes to the input, and is no longer than the worst case (LAWS.bend).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./format.bend as F
import ./window.bend as W
import ./match.bend as M
import ./crc.bend as K
import ./decode.bend as D

# The literal-only stream

# the tokens: each chunk as template 0, the tail as short data, the end with
# CRC c
def c842.enc.lits(xs: List<&2, U32>, c: U32) -> List<&2, F.C842Token>:
  match xs:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, rest}}}}}}}}:
      Con{F.C842Chunk{0, [F.C842Lit{b0, b1}, F.C842Lit{b2, b3}, F.C842Lit{b4, b5}, F.C842Lit{b6, b7}]}, c842.enc.lits(rest, c)}
    case Nil{}:
      [F.C842End{c}]
    case _:
      [F.C842Short{xs}, F.C842End{c}]

# the literal stream's bits, before padding
def c842.literal_bits(+o: B.Octets) -> List<&2, Bool>:
  F.c842.serialise(c842.enc.lits(B.Octets.to_list(o), K.c842.crc(o)))

# the literal stream
def c842.literals(o: B.Octets) -> B.Octets:
  F.c842.pack(c842.literal_bits(o))

# The encoder

type C842CompressOptions is Data:
  C842CompressOptions{strategy: M.C842Strategy}

def C842CompressOptions.default() -> C842CompressOptions:
  C842CompressOptions{M.C842Strategy.default()}

# what the matcher found for a chunk's phrases: the 8-byte one, the two
# 4-byte ones, the four 2-byte ones (in order)
type C842Finds is Data:
  C842Finds{f8: Maybe<&2, U32>, f4a: Maybe<&2, U32>, f4b: Maybe<&2, U32>, f2a: Maybe<&2, U32>, f2b: Maybe<&2, U32>, f2c: Maybe<&2, U32>, f2d: Maybe<&2, U32>}

# the pointer for a sub-phrase of kind k at byte offset off of the chunk
def c842.enc.at4(off: Nat, a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match off:
    case 0n:
      a
    case 1n+p:
      b

def c842.enc.at2(off: Nat, a: Maybe<&2, U32>, b: Maybe<&2, U32>, c: Maybe<&2, U32>, d: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match off:
    case 0n:
      a
    case 1n+p:
      match p:
        case 0n:
          b
        case 1n+q:
          match q:
            case 0n:
              b
            case 1n+r:
              match r:
                case 0n:
                  c
                case 1n+s:
                  match s:
                    case 0n:
                      c
                    case 1n+t:
                      d

def c842.enc.lookup(k: F.C842Kind, off: Nat, fs: C842Finds) -> Maybe<&2, U32>:
  match k:
    case F.C842P8{}:
      match fs:
        case C842Finds{f8, f4a, f4b, f2a, f2b, f2c, f2d}:
          f8
    case F.C842P4{}:
      match fs:
        case C842Finds{f8, f4a, f4b, f2a, f2b, f2c, f2d}:
          c842.enc.at4(off, f4a, f4b)
    case F.C842P2{}:
      match fs:
        case C842Finds{f8, f4a, f4b, f2a, f2b, f2c, f2d}:
          c842.enc.at2(off, f2a, f2b, f2c, f2d)
    case F.C842LL{}:
      None{}

def c842.enc.drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          c842.enc.drop(p, t)

def c842.enc.lit(xs: List<&2, U32>) -> F.C842Field:
  match xs:
    case Con{a, Con{b, t}}:
      F.C842Lit{a, b}
    case _:
      F.C842Lit{0, 0}

# a template tried on a chunk: its bits and fields (reversed so far)
type C842Try is Data:
  C842Try{bits: Nat, fields: List<&2, F.C842Field>}

def c842.enc.try.ptr(m: Maybe<&2, U32>, rest: Maybe<&2, C842Try>) -> Maybe<&2, C842Try>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      match rest:
        case None{}:
          None{}
        case Some{C842Try{n, fs}}:
          Some{C842Try{n, Con{F.C842Ptr{i}, fs}}}

def c842.enc.try.cost(+k: F.C842Kind, r: Maybe<&2, C842Try>) -> Maybe<&2, C842Try>:
  match r:
    case None{}:
      None{}
    case Some{C842Try{n, fs}}:
      Some{C842Try{Nat.add(F.C842Kind.width(k), n), fs}}

def c842.enc.try.lit(f: F.C842Field, rest: Maybe<&2, C842Try>) -> Maybe<&2, C842Try>:
  match rest:
    case None{}:
      None{}
    case Some{C842Try{n, fs}}:
      Some{C842Try{n, Con{f, fs}}}

def c842.enc.try.one(+k: F.C842Kind, off: Nat, xs: List<&2, U32>, fs: C842Finds, rest: Maybe<&2, C842Try>) -> Maybe<&2, C842Try>:
  match k:
    case F.C842LL{}:
      c842.enc.try.cost(F.C842LL{}, c842.enc.try.lit(c842.enc.lit(xs), rest))
    case F.C842P2{}:
      c842.enc.try.cost(F.C842P2{}, c842.enc.try.ptr(c842.enc.lookup(F.C842P2{}, off, fs), rest))
    case F.C842P4{}:
      c842.enc.try.cost(F.C842P4{}, c842.enc.try.ptr(c842.enc.lookup(F.C842P4{}, off, fs), rest))
    case F.C842P8{}:
      c842.enc.try.cost(F.C842P8{}, c842.enc.try.ptr(c842.enc.lookup(F.C842P8{}, off, fs), rest))

# the template's kinds ks from byte offset off of the chunk (whose bytes from
# off on are xs): its bits and fields, or none if a pointer was not found
def c842.enc.try(ks: List<&2, F.C842Kind>, +off: Nat, +xs: List<&2, U32>, +fs: C842Finds) -> Maybe<&2, C842Try>:
  match ks:
    case Nil{}:
      Some{C842Try{0n, Nil{}}}
    case Con{+k, t}:
      +sz = U32.to_nat(F.C842Kind.size(k))
      c842.enc.try.one(k, off, xs, fs, c842.enc.try(t, Nat.add(off, sz), c842.enc.drop(sz, xs), fs))

# the best template so far: its code, bits and fields
type C842Pick is Data:
  C842Pick{code: U32, bits: Nat, fields: List<&2, F.C842Field>}

def c842.enc.better.at(lt: Bool, a: C842Pick, b: C842Pick) -> C842Pick:
  match lt:
    case True{}:
      a
    case False{}:
      b

def c842.enc.better(r: Maybe<&2, C842Try>, +code: U32, best: C842Pick) -> C842Pick:
  match r:
    case None{}:
      best
    case Some{C842Try{+n, fs}}:
      match best:
        case C842Pick{bc, +bn, bfs}:
          c842.enc.better.at(Nat.is_lt(n, bn), C842Pick{code, n, fs}, C842Pick{bc, bn, bfs})

def c842.enc.best(ts: List<&2, List<&2, F.C842Kind>>, +code: U32, +xs: List<&2, U32>, +fs: C842Finds, best: C842Pick) -> C842Pick:
  match ts:
    case Nil{}:
      best
    case Con{ks, t}:
      c842.enc.best(t, U32.add(code, 1), xs, fs, c842.enc.better(c842.enc.try(ks, 0n, xs, fs), code, best))

# the chunk xs as its best template
def c842.enc.chunk_of(p: C842Pick) -> F.C842Token:
  match p:
    case C842Pick{code, n, fs}:
      F.C842Chunk{code, fs}

def c842.enc.template(+xs: List<&2, U32>, +fs: C842Finds) -> F.C842Token:
  c842.enc.chunk_of(c842.enc.best(F.c842.templates(), 0, xs, fs, C842Pick{0, 1000n, Nil{}}))

# The matcher's finds for a chunk

# the matcher and what it found last
type C842Seek is Type:
  C842Seek{m: M.C842Matcher, f: Maybe<&2, U32>}

def c842.enc.seek(r: M.C842Found) -> C842Seek:
  match r:
    case M.C842Found{m, f}:
      C842Seek{m, f}

type C842Finding is Type:
  C842Finding{m: M.C842Matcher, fs: C842Finds}

def c842.enc.f2d(s: C842Seek, f8: Maybe<&2, U32>, f4a: Maybe<&2, U32>, f4b: Maybe<&2, U32>, f2a: Maybe<&2, U32>, f2b: Maybe<&2, U32>, f2c: Maybe<&2, U32>) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      C842Finding{m, C842Finds{f8, f4a, f4b, f2a, f2b, f2c, f}}

def c842.enc.f2c(s: C842Seek, +i: U32, +b6: U32, +b7: U32, w: W.C842Win, f8: Maybe<&2, U32>, f4a: Maybe<&2, U32>, f4b: Maybe<&2, U32>, f2a: Maybe<&2, U32>, f2b: Maybe<&2, U32>) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      c842.enc.f2d(c842.enc.seek(M.c842.match.find(m, F.C842P2{}, i, [b6, b7], w)), f8, f4a, f4b, f2a, f2b, f)

def c842.enc.f2b(s: C842Seek, +i: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, +w: W.C842Win, f8: Maybe<&2, U32>, f4a: Maybe<&2, U32>, f4b: Maybe<&2, U32>, f2a: Maybe<&2, U32>) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      c842.enc.f2c(c842.enc.seek(M.c842.match.find(m, F.C842P2{}, i, [b4, b5], w)), i, b6, b7, w, f8, f4a, f4b, f2a, f)

def c842.enc.f2a(s: C842Seek, +i: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, +w: W.C842Win, f8: Maybe<&2, U32>, f4a: Maybe<&2, U32>, f4b: Maybe<&2, U32>) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      c842.enc.f2b(c842.enc.seek(M.c842.match.find(m, F.C842P2{}, i, [b2, b3], w)), i, b4, b5, b6, b7, w, f8, f4a, f4b, f)

def c842.enc.f4b(s: C842Seek, +i: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, +w: W.C842Win, f8: Maybe<&2, U32>, f4a: Maybe<&2, U32>) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      c842.enc.f2a(c842.enc.seek(M.c842.match.find(m, F.C842P2{}, i, [b0, b1], w)), i, b2, b3, b4, b5, b6, b7, w, f8, f4a, f)

def c842.enc.f4a(s: C842Seek, +i: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, +w: W.C842Win, f8: Maybe<&2, U32>) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      c842.enc.f4b(c842.enc.seek(M.c842.match.find(m, F.C842P4{}, i, [b4, b5, b6, b7], w)), i, b0, b1, b2, b3, b4, b5, b6, b7, w, f8, f)

def c842.enc.f8(s: C842Seek, +i: U32, +b0: U32, +b1: U32, +b2: U32, +b3: U32, +b4: U32, +b5: U32, +b6: U32, +b7: U32, +w: W.C842Win) -> C842Finding:
  match s:
    case C842Seek{m, f}:
      c842.enc.f4a(c842.enc.seek(M.c842.match.find(m, F.C842P4{}, i, [b0, b1, b2, b3], w)), i, b0, b1, b2, b3, b4, b5, b6, b7, w, f)

# the seven phrases of the chunk at i (its 8 bytes in xs)
def c842.enc.finds(m: M.C842Matcher, +i: U32, xs: List<&2, U32>, +w: W.C842Win) -> C842Finding:
  match xs:
    case Con{+b0, Con{+b1, Con{+b2, Con{+b3, Con{+b4, Con{+b5, Con{+b6, Con{+b7, rest}}}}}}}}:
      c842.enc.f8(c842.enc.seek(M.c842.match.find(m, F.C842P8{}, i, [b0, b1, b2, b3, b4, b5, b6, b7], w)), i, b0, b1, b2, b3, b4, b5, b6, b7, w)
    case _:
      C842Finding{m, C842Finds{None{}, None{}, None{}, None{}, None{}, None{}, None{}}}

# the matcher with the chunk at i seen
def c842.enc.see(m: M.C842Matcher, +i: U32, xs: List<&2, U32>) -> M.C842Matcher:
  match xs:
    case Con{+b0, Con{+b1, Con{+b2, Con{+b3, Con{+b4, Con{+b5, Con{+b6, Con{+b7, rest}}}}}}}}:
      m8 = M.c842.match.add(m, F.C842P8{}, i, [b0, b1, b2, b3, b4, b5, b6, b7])
      m4 = M.c842.match.add(M.c842.match.add(m8, F.C842P4{}, i, [b0, b1, b2, b3]), F.C842P4{}, U32.add(i, 4), [b4, b5, b6, b7])
      M.c842.match.add(M.c842.match.add(M.c842.match.add(M.c842.match.add(m4, F.C842P2{}, i, [b0, b1]), F.C842P2{}, U32.add(i, 2), [b2, b3]), F.C842P2{}, U32.add(i, 4), [b4, b5]), F.C842P2{}, U32.add(i, 6), [b6, b7])
    case _:
      m

# the window with the bytes xs from position i on
def c842.enc.put(xs: List<&2, U32>, w: W.C842Win, +i: U32) -> W.C842Win:
  match xs:
    case Nil{}:
      w
    case Con{x, t}:
      c842.enc.put(t, W.c842.win.put(w, i, x), U32.add(i, 1))

# The chunk loop

def c842.enc.same.go(xs: List<&2, U32>, ys: List<&2, U32>, ok: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      ok
    case Con{a, s} Con{b, t}:
      c842.enc.same.go(s, t, Bool.and(ok, D.c842.u32_same(a, b)))
    case _ _:
      False{}

def c842.enc.zero(xs: List<&2, U32>, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{x, t}:
      c842.enc.zero(t, Bool.and(ok, U32.is_eq(x, 0)))

# a run of k repeated chunks, as RPT
def c842.enc.flush(k: Nat, ts: List<&2, F.C842Token>) -> List<&2, F.C842Token>:
  match k:
    case 0n:
      ts
    case 1n+r:
      Con{F.C842Repeat{U32.from_nat(r)}, ts}

# the matcher, the window over the input so far, the next chunk's position,
# the chunk before it, the run of repeats of it so far, the tokens (reversed)
type C842Enc is Type:
  C842Enc{m: M.C842Matcher, w: W.C842Win, i: U32, prev: List<&2, U32>, run: Nat, ts: List<&2, F.C842Token>}

def c842.enc.next(m: M.C842Matcher, +w: W.C842Win, +i: U32, +xs: List<&2, U32>, run: Nat, ts: List<&2, F.C842Token>) -> C842Enc:
  C842Enc{c842.enc.see(m, i, xs), c842.enc.put(xs, w, i), U32.add(i, 8), xs, run, ts}

def c842.enc.coded(f: C842Finding, +w: W.C842Win, +i: U32, +xs: List<&2, U32>, ts: List<&2, F.C842Token>) -> C842Enc:
  match f:
    case C842Finding{m, fs}:
      c842.enc.next(m, w, i, xs, 0n, Con{c842.enc.template(xs, fs), ts})

def c842.enc.fresh(zero: Bool, m: M.C842Matcher, +w: W.C842Win, +i: U32, +xs: List<&2, U32>, ts: List<&2, F.C842Token>) -> C842Enc:
  match zero:
    case True{}:
      c842.enc.next(m, w, i, xs, 0n, Con{F.C842Zero{}, ts})
    case False{}:
      c842.enc.coded(c842.enc.finds(m, i, xs, w), w, i, xs, ts)

def c842.enc.again(full: Bool, m: M.C842Matcher, +w: W.C842Win, +i: U32, +xs: List<&2, U32>, +run: Nat, ts: List<&2, F.C842Token>) -> C842Enc:
  match full:
    case True{}:
      c842.enc.next(m, w, i, xs, 0n, Con{F.C842Repeat{63}, ts})
    case False{}:
      c842.enc.next(m, w, i, xs, run, ts)

def c842.enc.chunk.at(same: Bool, m: M.C842Matcher, +w: W.C842Win, +i: U32, +xs: List<&2, U32>, +run: Nat, ts: List<&2, F.C842Token>) -> C842Enc:
  match same:
    case True{}:
      c842.enc.again(Nat.is_eq(run, 63n), m, w, i, xs, 1n+run, ts)
    case False{}:
      c842.enc.fresh(c842.enc.zero(xs, True{}), m, w, i, xs, c842.enc.flush(run, ts))

def c842.enc.chunk(+xs: List<&2, U32>, st: C842Enc) -> C842Enc:
  match st:
    case C842Enc{m, w, +i, prev, +run, ts}:
      c842.enc.chunk.at(c842.enc.same.go(prev, xs, True{}), m, w, i, xs, run, ts)

def c842.enc.end(st: C842Enc, xs: List<&2, U32>, c: U32) -> List<&2, F.C842Token>:
  match st:
    case C842Enc{m, w, i, prev, run, ts}:
      match xs:
        case Nil{}:
          List.reverse(&2, F.C842Token, Con{F.C842End{c}, c842.enc.flush(run, ts)})
        case _:
          List.reverse(&2, F.C842Token, Con{F.C842End{c}, Con{F.C842Short{xs}, c842.enc.flush(run, ts)}})

def c842.enc.go(xs: List<&2, U32>, st: C842Enc, c: U32) -> List<&2, F.C842Token>:
  match xs:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, rest}}}}}}}}:
      c842.enc.go(rest, c842.enc.chunk([b0, b1, b2, b3, b4, b5, b6, b7], st), c)
    case _:
      c842.enc.end(st, xs, c)

# the encoder's tokens for o, with this strategy
def c842.enc.tokens(s: M.C842Strategy, +o: B.Octets) -> List<&2, F.C842Token>:
  c842.enc.go(B.Octets.to_list(o), C842Enc{M.c842.match.new(s), W.c842.win.empty(), 0, Nil{}, 0n, Nil{}}, K.c842.crc(o))

# the encoder's stream's bits, unchecked
def c842.compress_bits_unchecked(opts: C842CompressOptions, +o: B.Octets) -> List<&2, Bool>:
  match opts:
    case C842CompressOptions{s}:
      F.c842.serialise(c842.enc.tokens(s, o))

# the encoder's stream, unchecked
def c842.compress_unchecked(opts: C842CompressOptions, +o: B.Octets) -> B.Octets:
  F.c842.pack(c842.compress_bits_unchecked(opts, o))

# Checking: decode the stream and compare

def c842.enc.ok(r: Result<&2, &2, E.C842Error, B.Octets>, +o: B.Octets) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      c842.enc.same.go(B.Octets.to_list(x), B.Octets.to_list(o), True{})

def c842.enc.pick(ok: Bool, +m: List<&2, Bool>, +o: B.Octets) -> List<&2, Bool>:
  match ok:
    case True{}:
      m
    case False{}:
      c842.literal_bits(o)

# the encoder's bits m if they are no longer than the worst case (the literal
# stream's length: LAWS.bend, literal_bits_worst) and decode back to o; else
# the literal stream's
def c842.enc.check(+m: List<&2, Bool>, +o: B.Octets) -> List<&2, Bool>:
  c842.enc.pick(Bool.and(Nat.is_le(List.length(&2, Bool, m), F.c842.worst_bits(B.Octets.len(o))), c842.enc.ok(D.c842.decompress(F.c842.pack(m), B.Octets.len(o)), o)), m, o)

# the stream's bits for o: the encoder's, checked (else the literal stream's)
def c842.compress_bits(opts: C842CompressOptions, +o: B.Octets) -> List<&2, Bool>:
  c842.enc.check(c842.compress_bits_unchecked(opts, o), o)

# a stream for o
def c842.compress_with(opts: C842CompressOptions, +o: B.Octets) -> B.Octets:
  F.c842.pack(c842.compress_bits(opts, o))

def c842.compress(+o: B.Octets) -> B.Octets:
  c842.compress_with(C842CompressOptions.default(), o)
