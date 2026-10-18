# bend-osdev-bzip2: the first run-length stage, RLE1 (Tsai, "BZip2 Format
# Specification", section 4.1).
#
# Before the Burrows-Wheeler transform, bzip2 replaces every run of 4 to 255
# equal bytes by the first 4 of them and a count byte, the number of further
# copies (0 to 251). A longer run is cut into runs of 255 and a remainder.
# After a count byte the decoder starts afresh, so the next byte may equal
# the run's byte without continuing it. Runs of 1 to 3 bytes stay as they are.
#
# rle1_encode and rle1_decode work on whole byte strings; the block coder
# (stream.bend, compress.bend) uses the same steps a block at a time.
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L

# The encoder: the run in progress (k copies of h; k = 0 before the first
# byte), and what a byte emits

type Bzip2Rle1Run is Data:
  Bzip2Rle1Run{h: U32, k: Nat}

type Bzip2Rle1Emit is Data:
  Bzip2Rle1Emit{out: List<&2, U32>, run: Bzip2Rle1Run}

# a run of k copies of h, encoded
def rle1.emit(k: Nat, +h: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      match k1:
        case 0n:
          [h]
        case 1n+k2:
          match k2:
            case 0n:
              [h, h]
            case 1n+k3:
              match k3:
                case 0n:
                  [h, h, h]
                case 1n+m:
                  [h, h, h, h, U32.from_nat(m)]

def rle1.emit.run(r: Bzip2Rle1Run) -> List<&2, U32>:
  match r:
    case Bzip2Rle1Run{h, k}:
      rle1.emit(k, h)

def rle1.enc.pick(same: Bool, +b: U32, +h: U32, +k: Nat) -> Bzip2Rle1Emit:
  match same:
    case True{}:
      Bzip2Rle1Emit{Nil{}, Bzip2Rle1Run{h, 1n+k}}
    case False{}:
      Bzip2Rle1Emit{rle1.emit(k, h), Bzip2Rle1Run{b, 1n}}

def rle1.enc.step.b(+b: U32, +h: U32, +k: Nat) -> Bzip2Rle1Emit:
  rle1.enc.pick(Bool.and(U32.is_eq(b, h), Nat.is_lt(k, 255n)), b, h, k)

# the next byte: it continues the run (the same byte, and fewer than 255 so
# far), or the run is emitted and a new one starts
def rle1.enc.step(y: U32, r: Bzip2Rle1Run) -> Bzip2Rle1Emit:
  match r:
    case Bzip2Rle1Run{+h, +k}:
      rle1.enc.step.b(B.byte(y), h, k)

def rle1.emit.out(e: Bzip2Rle1Emit) -> List<&2, U32>:
  match e:
    case Bzip2Rle1Emit{out, run}:
      out

def rle1.emit.next(e: Bzip2Rle1Emit) -> Bzip2Rle1Run:
  match e:
    case Bzip2Rle1Emit{out, run}:
      run

# the encoding, structurally (the reference the proofs follow)
def rle1.enc(xs: List<&2, U32>, r: Bzip2Rle1Run) -> List<&2, U32>:
  match xs:
    case Nil{}:
      rle1.emit.run(r)
    case Con{y, t}:
      +e = rle1.enc.step(y, r)
      L.bz.app(rle1.emit.out(e), rle1.enc(t, rle1.emit.next(e)))

# the same, tail-recursively: acc holds the output so far, reversed
def rle1.enc.fast(xs: List<&2, U32>, r: Bzip2Rle1Run, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      L.bz.rev(L.bz.push(rle1.emit.run(r), acc))
    case Con{y, t}:
      +e = rle1.enc.step(y, r)
      rle1.enc.fast(t, rle1.emit.next(e), L.bz.push(rle1.emit.out(e), acc))

def rle1.enc.start() -> Bzip2Rle1Run:
  Bzip2Rle1Run{0, 0n}

# The decoder: the last byte, and how many times in a row it has been seen
# (0 after a count byte, and at the start)

type Bzip2Rle1Dec is Data:
  Bzip2Rle1Dec{last: U32, n: Nat}

type Bzip2Rle1Out is Data:
  Bzip2Rle1Out{out: List<&2, U32>, st: Bzip2Rle1Dec}

# a byte that is not a count: the run goes on (to m in a row) if it is the
# same byte, or a new one starts
def rle1.dec.lit(same: Bool, +b: U32, last: U32, m: Nat) -> Bzip2Rle1Out:
  match same:
    case True{}:
      Bzip2Rle1Out{[b], Bzip2Rle1Dec{b, m}}
    case False{}:
      Bzip2Rle1Out{[b], Bzip2Rle1Dec{b, 1n}}

def rle1.dec.step.b(+b: U32, s: Bzip2Rle1Dec) -> Bzip2Rle1Out:
  match s:
    case Bzip2Rle1Dec{+last, n}:
      match n:
        case 0n:
          Bzip2Rle1Out{[b], Bzip2Rle1Dec{b, 1n}}
        case 1n+n1:
          match n1:
            case 0n:
              rle1.dec.lit(U32.is_eq(b, last), b, last, 2n)
            case 1n+n2:
              match n2:
                case 0n:
                  rle1.dec.lit(U32.is_eq(b, last), b, last, 3n)
                case 1n+n3:
                  match n3:
                    case 0n:
                      rle1.dec.lit(U32.is_eq(b, last), b, last, 4n)
                    case 1n+n4:
                      Bzip2Rle1Out{L.bz.rep(U32.to_nat(b), last), Bzip2Rle1Dec{last, 0n}}

def rle1.dec.step(y: U32, s: Bzip2Rle1Dec) -> Bzip2Rle1Out:
  rle1.dec.step.b(B.byte(y), s)

def rle1.out.out(o: Bzip2Rle1Out) -> List<&2, U32>:
  match o:
    case Bzip2Rle1Out{out, st}:
      out

def rle1.out.next(o: Bzip2Rle1Out) -> Bzip2Rle1Dec:
  match o:
    case Bzip2Rle1Out{out, st}:
      st

# the decoding, structurally
def rle1.dec(ys: List<&2, U32>, s: Bzip2Rle1Dec) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      +o = rle1.dec.step(y, s)
      L.bz.app(rle1.out.out(o), rle1.dec(t, rle1.out.next(o)))

# the same, tail-recursively
def rle1.dec.fast(ys: List<&2, U32>, s: Bzip2Rle1Dec, acc: List<&2, U32>) -> List<&2, U32>:
  match ys:
    case Nil{}:
      L.bz.rev(acc)
    case Con{y, t}:
      +o = rle1.dec.step(y, s)
      rle1.dec.fast(t, rle1.out.next(o), L.bz.push(rle1.out.out(o), acc))

def rle1.dec.start() -> Bzip2Rle1Dec:
  Bzip2Rle1Dec{0, 0n}

# The decoder with a limit: room is how many more bytes may come out; None
# if the output would pass it. acc holds the output, reversed.

type Bzip2Rle1Lim is Data:
  Bzip2Rle1More{ys: List<&2, U32>, room: Nat, acc: List<&2, U32>}
  Bzip2Rle1Full{}

def rle1.lim.pick(fits: Bool, +k: Nat, ys: List<&2, U32>, out: List<&2, U32>, room: Nat, acc: List<&2, U32>) -> Bzip2Rle1Lim:
  match fits:
    case True{}:
      Bzip2Rle1More{ys, Nat.sub(room, k), L.bz.push(out, acc)}
    case False{}:
      Bzip2Rle1Full{}

def rle1.dec.lim(fuel: Nat, s: Bzip2Rle1Dec, st: Bzip2Rle1Lim) -> Maybe<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match st:
        case Bzip2Rle1Full{}:
          None{}
        case Bzip2Rle1More{ys, +room, acc}:
          match ys:
            case Nil{}:
              Some{acc}
            case Con{y, t}:
              +o = rle1.dec.step(y, s)
              +out = rle1.out.out(o)
              +k = L.bz.len(out)
              rle1.dec.lim(f, rle1.out.next(o), rle1.lim.pick(Nat.is_le(k, room), k, t, out, room, acc))

# the bytes ys decode to (reversed), if there are at most room of them
def rle1_decode_list(+ys: List<&2, U32>, room: Nat) -> Maybe<&2, List<&2, U32>>:
  rle1.dec.lim(1n+L.bz.len(ys), rle1.dec.start(), Bzip2Rle1More{ys, room, Nil{}})

# The public interface

# the RLE1 encoding of o
def rle1_encode(o: B.Octets) -> B.Octets:
  B.Octets.of_list(rle1.enc.fast(B.Octets.to_list(o), rle1.enc.start(), Nil{}))

# the RLE1 decoding of o (every byte string decodes: a count byte may be 0 to
# 255)
def rle1_decode(o: B.Octets) -> B.Octets:
  B.Octets.of_list(rle1.dec.fast(B.Octets.to_list(o), rle1.dec.start(), Nil{}))
