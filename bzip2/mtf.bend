# bend-osdev-bzip2: the move-to-front stage and the second run-length stage,
# RLE2 (Tsai, "BZip2 Format Specification", sections 4.3 and 4.4).
#
# Move-to-front replaces each byte by its position in a list of the bytes
# (the alphabet), then moves it to the front. bzip2's alphabet is the bytes a
# block uses, in increasing order (the symbol map: symbol_map below). Runs of
# position 0 are then written in bijective base 2, least significant digit
# first, with two symbols: RUNA (0) for the digit 1 and RUNB (1) for the digit
# 2, so a run of n zeros is the digits of n; any other position p is the
# symbol p + 1. The block coder adds the end-of-block symbol after these.
#
# mtf_encode and mtf_decode are this stage alone, usable without the rest of
# bzip2: the symbols are U32 (0 to 256), the alphabet and the data Octets.
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L
import ./error.bend as E

# The digits of a run of zeros (least significant first)

type Bzip2Digit is Data:
  Bzip2RunA{}
  Bzip2RunB{}

# one more zero: the digits of n + 1 from those of n
def mtf.inc(ds: List<&2, Bzip2Digit>) -> List<&2, Bzip2Digit>:
  match ds:
    case Nil{}:
      [Bzip2RunA{}]
    case Con{d, t}:
      match d:
        case Bzip2RunA{}:
          Con{Bzip2RunB{}, t}
        case Bzip2RunB{}:
          Con{Bzip2RunA{}, mtf.inc(t)}

# the digits as symbols
def mtf.syms(ds: List<&2, Bzip2Digit>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      match d:
        case Bzip2RunA{}:
          Con{0, mtf.syms(t)}
        case Bzip2RunB{}:
          Con{1, mtf.syms(t)}

# the digits as symbols, pushed onto acc
def mtf.syms.push(ds: List<&2, Bzip2Digit>, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      match d:
        case Bzip2RunA{}:
          mtf.syms.push(t, Con{0, acc})
        case Bzip2RunB{}:
          mtf.syms.push(t, Con{1, acc})

# Finding a byte in the alphabet, and taking the byte at a position out of it

type Bzip2MtfLook is Data:
  Bzip2MtfLook{i: Nat}
  Bzip2MtfHit{i: Nat}

def mtf.idx.step(eq: Bool, i: Nat) -> Bzip2MtfLook:
  match eq:
    case True{}:
      Bzip2MtfHit{i}
    case False{}:
      Bzip2MtfLook{1n+i}

def mtf.idx.end(st: Bzip2MtfLook) -> Maybe<&2, Nat>:
  match st:
    case Bzip2MtfLook{i}:
      None{}
    case Bzip2MtfHit{i}:
      Some{i}

def mtf.idx.go(alpha: List<&2, U32>, st: Bzip2MtfLook, +x: U32) -> Maybe<&2, Nat>:
  match alpha:
    case Nil{}:
      mtf.idx.end(st)
    case Con{h, t}:
      match st:
        case Bzip2MtfHit{i}:
          Some{i}
        case Bzip2MtfLook{i}:
          mtf.idx.go(t, mtf.idx.step(U32.is_eq(h, x), i), x)

# the position of x in alpha (its first occurrence)
def mtf.idx(alpha: List<&2, U32>, +x: U32) -> Maybe<&2, Nat>:
  mtf.idx.go(alpha, Bzip2MtfLook{0n}, x)

# the byte at a position, and the rest of the alphabet: the alphabet with
# the byte moved to the front is Con{x, rest}
type Bzip2MtfTake is Data:
  Bzip2MtfTake{x: U32, rest: List<&2, U32>}

# walk to position j (i: where the walk is; here: whether i is j; pre: the
# bytes passed, reversed)
def mtf.take.go(alpha: List<&2, U32>, here: Bool, +i: Nat, pre: List<&2, U32>, +j: Nat) -> Maybe<&2, Bzip2MtfTake>:
  match alpha:
    case Nil{}:
      None{}
    case Con{+h, t}:
      match here:
        case True{}:
          Some{Bzip2MtfTake{h, L.bz.push(pre, t)}}
        case False{}:
          mtf.take.go(t, Nat.is_eq(1n+i, j), 1n+i, Con{h, pre}, j)

# the byte at position j of alpha, and alpha with it moved to the front
def mtf.take(alpha: List<&2, U32>, +j: Nat) -> Maybe<&2, Bzip2MtfTake>:
  mtf.take.go(alpha, Nat.is_eq(0n, j), 0n, Nil{}, j)

# The encoder: what one byte emits, the alphabet after it, and the digits of
# the run of zeros in progress

type Bzip2MtfEnc is Data:
  Bzip2MtfEnc{out: List<&2, U32>, alpha: List<&2, U32>, ds: List<&2, Bzip2Digit>}

def mtf.enc.moved(m: Maybe<&2, Bzip2MtfTake>, ds: List<&2, Bzip2Digit>, +sym: U32, alpha: List<&2, U32>) -> Bzip2MtfEnc:
  match m:
    case Some{r}:
      match r:
        case Bzip2MtfTake{x, rest}:
          Bzip2MtfEnc{L.bz.app(mtf.syms(ds), [sym]), Con{x, rest}, Nil{}}
    case None{}:
      Bzip2MtfEnc{Nil{}, alpha, ds}

# a byte at position p: position 0 lengthens the run; any other emits the
# run's digits and the symbol p + 1. A byte not in the alphabet is dropped.
def mtf.enc.at(m: Maybe<&2, Nat>, +alpha: List<&2, U32>, ds: List<&2, Bzip2Digit>) -> Bzip2MtfEnc:
  match m:
    case None{}:
      Bzip2MtfEnc{Nil{}, alpha, ds}
    case Some{p}:
      match p:
        case 0n:
          Bzip2MtfEnc{Nil{}, alpha, mtf.inc(ds)}
        case 1n+(+q):
          mtf.enc.moved(mtf.take(alpha, 1n+q), ds, U32.from_nat(1n+1n+q), alpha)

def mtf.enc.step(y: U32, +alpha: List<&2, U32>, ds: List<&2, Bzip2Digit>) -> Bzip2MtfEnc:
  mtf.enc.at(mtf.idx(alpha, B.byte(y)), alpha, ds)

def mtf.enc.out(e: Bzip2MtfEnc) -> List<&2, U32>:
  match e:
    case Bzip2MtfEnc{out, alpha, ds}:
      out

def mtf.enc.alpha(e: Bzip2MtfEnc) -> List<&2, U32>:
  match e:
    case Bzip2MtfEnc{out, alpha, ds}:
      alpha

def mtf.enc.ds(e: Bzip2MtfEnc) -> List<&2, Bzip2Digit>:
  match e:
    case Bzip2MtfEnc{out, alpha, ds}:
      ds

# the encoding, structurally (the reference the proofs follow)
def mtf.enc(xs: List<&2, U32>, alpha: List<&2, U32>, ds: List<&2, Bzip2Digit>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      mtf.syms(ds)
    case Con{y, t}:
      +e = mtf.enc.step(y, alpha, ds)
      L.bz.app(mtf.enc.out(e), mtf.enc(t, mtf.enc.alpha(e), mtf.enc.ds(e)))

# the same, tail-recursively
def mtf.enc.fast(xs: List<&2, U32>, alpha: List<&2, U32>, ds: List<&2, Bzip2Digit>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      L.bz.rev(mtf.syms.push(ds, acc))
    case Con{y, t}:
      +e = mtf.enc.step(y, alpha, ds)
      mtf.enc.fast(t, mtf.enc.alpha(e), mtf.enc.ds(e), L.bz.push(mtf.enc.out(e), acc))

# The decoder: the alphabet, the zeros of the run so far (cnt) and the
# weight of its next digit (w), and how many more bytes may come out

type Bzip2MtfDec is Data:
  Bzip2MtfDec{alpha: List<&2, U32>, cnt: Nat, w: Nat, room: Nat}
  Bzip2MtfBad{e: E.Bzip2Error}

type Bzip2MtfOut is Data:
  Bzip2MtfOut{out: List<&2, U32>, st: Bzip2MtfDec}

def mtf.flush.pick(fits: Bool, +h: U32, t: List<&2, U32>, +cnt: Nat, +room: Nat) -> Bzip2MtfOut:
  match fits:
    case True{}:
      Bzip2MtfOut{L.bz.rep(cnt, h), Bzip2MtfDec{Con{h, t}, 0n, 1n, Nat.sub(room, cnt)}}
    case False{}:
      Bzip2MtfOut{Nil{}, Bzip2MtfBad{E.Bzip2OutputTooLarge{}}}

# the run of cnt zeros: cnt copies of the front byte
def mtf.flush(cnt: Nat, alpha: List<&2, U32>, +room: Nat) -> Bzip2MtfOut:
  match cnt:
    case 0n:
      Bzip2MtfOut{Nil{}, Bzip2MtfDec{alpha, 0n, 1n, room}}
    case 1n+(+c):
      match alpha:
        case Nil{}:
          Bzip2MtfOut{Nil{}, Bzip2MtfBad{E.Bzip2BadSymbol{}}}
        case Con{h, t}:
          mtf.flush.pick(Nat.is_le(1n+c, room), h, t, 1n+c, room)

def mtf.dec.put(m: Maybe<&2, Bzip2MtfTake>, out: List<&2, U32>, room: Nat) -> Bzip2MtfOut:
  match m:
    case None{}:
      Bzip2MtfOut{Nil{}, Bzip2MtfBad{E.Bzip2BadSymbol{}}}
    case Some{r}:
      match r:
        case Bzip2MtfTake{+x, rest}:
          match room:
            case 0n:
              Bzip2MtfOut{Nil{}, Bzip2MtfBad{E.Bzip2OutputTooLarge{}}}
            case 1n+k:
              Bzip2MtfOut{L.bz.app(out, [x]), Bzip2MtfDec{Con{x, rest}, 0n, 1n, k}}

# the symbol for position p: the run before it, then the byte at p
def mtf.dec.index(f: Bzip2MtfOut, +p: Nat) -> Bzip2MtfOut:
  match f:
    case Bzip2MtfOut{out, st}:
      match st:
        case Bzip2MtfDec{alpha, cnt, w, room}:
          mtf.dec.put(mtf.take(alpha, p), out, room)
        case Bzip2MtfBad{e}:
          Bzip2MtfOut{Nil{}, Bzip2MtfBad{e}}

# RUNA adds w zeros, RUNB 2w; the next digit weighs 2w
def mtf.dec.sym(n: Nat, alpha: List<&2, U32>, cnt: Nat, +w: Nat, room: Nat) -> Bzip2MtfOut:
  match n:
    case 0n:
      Bzip2MtfOut{Nil{}, Bzip2MtfDec{alpha, Nat.add(cnt, w), Nat.add(w, w), room}}
    case 1n+n1:
      match n1:
        case 0n:
          Bzip2MtfOut{Nil{}, Bzip2MtfDec{alpha, Nat.add(cnt, Nat.add(w, w)), Nat.add(w, w), room}}
        case 1n+p:
          mtf.dec.index(mtf.flush(cnt, alpha, room), 1n+p)

def mtf.dec.step(s: U32, st: Bzip2MtfDec) -> Bzip2MtfOut:
  match st:
    case Bzip2MtfDec{alpha, cnt, w, room}:
      mtf.dec.sym(U32.to_nat(s), alpha, cnt, w, room)
    case Bzip2MtfBad{e}:
      Bzip2MtfOut{Nil{}, Bzip2MtfBad{e}}

def mtf.out.out(o: Bzip2MtfOut) -> List<&2, U32>:
  match o:
    case Bzip2MtfOut{out, st}:
      out

def mtf.out.next(o: Bzip2MtfOut) -> Bzip2MtfDec:
  match o:
    case Bzip2MtfOut{out, st}:
      st

def mtf.end.out(o: Bzip2MtfOut) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match o:
    case Bzip2MtfOut{out, st}:
      match st:
        case Bzip2MtfDec{alpha, cnt, w, room}:
          Done{out}
        case Bzip2MtfBad{e}:
          Fail{e}

# the end of the symbols: the last run
def mtf.dec.end(st: Bzip2MtfDec) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match st:
    case Bzip2MtfDec{alpha, cnt, w, room}:
      mtf.end.out(mtf.flush(cnt, alpha, room))
    case Bzip2MtfBad{e}:
      Fail{e}

def mtf.res.app(xs: List<&2, U32>, r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ys}:
      Done{L.bz.app(xs, ys)}

def mtf.res.push(acc: List<&2, U32>, r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ys}:
      Done{L.bz.push(acc, ys)}

# the decoding, structurally
def mtf.dec(syms: List<&2, U32>, st: Bzip2MtfDec) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match syms:
    case Nil{}:
      mtf.dec.end(st)
    case Con{s, t}:
      +o = mtf.dec.step(s, st)
      mtf.res.app(mtf.out.out(o), mtf.dec(t, mtf.out.next(o)))

# the same, tail-recursively, stopping at the first failure
def mtf.dec.fast(syms: List<&2, U32>, st: Bzip2MtfDec, acc: List<&2, U32>) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match syms:
    case Nil{}:
      mtf.res.push(acc, mtf.dec.end(st))
    case Con{s, t}:
      match st:
        case Bzip2MtfBad{e}:
          Fail{e}
        case Bzip2MtfDec{alpha, cnt, w, room}:
          +o = mtf.dec.step(s, Bzip2MtfDec{alpha, cnt, w, room})
          mtf.dec.fast(t, mtf.out.next(o), L.bz.push(mtf.out.out(o), acc))

# the decoding of syms from the alphabet alpha, at most room bytes
def mtf_decode_list(syms: List<&2, U32>, alpha: List<&2, U32>, room: Nat) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  mtf.dec.fast(syms, Bzip2MtfDec{alpha, 0n, 1n, room}, Nil{})

# The symbol map: the bytes a block uses, in increasing order

def mtf.mark(xs: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{h, t}:
      mtf.mark(t, Array.set(U32, a, B.byte(h), 1))

def mtf.used.pick(on: Bool, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match on:
    case True{}:
      Con{i, acc}
    case False{}:
      acc

def mtf.used.go(n: Nat, r: Array<U32> & U32, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, v) = r
      +j = U32.sub(i, 1)
      mtf.used.go(p, Array.get(U32, a, j), j, mtf.used.pick(U32.is_eq(v, 1), i, acc))

# the bytes of xs, each once, in increasing order
def mtf.used(xs: List<&2, U32>) -> List<&2, U32>:
  mtf.used.go(256n, Array.get(U32, mtf.mark(xs, [0 : U32*256n]), 255), 255, Nil{})

def mtf.covers.has(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{i}:
      True{}

# whether every byte of xs is in alpha
def mtf.covers(xs: List<&2, U32>, +alpha: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(mtf.covers.has(mtf.idx(alpha, B.byte(y))), mtf.covers(t, alpha))

def mtf.res.octets(r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ys}:
      Done{B.Octets.of_list(ys)}

# The public interface

# the bytes o uses, in increasing order: bzip2's alphabet for o
def symbol_map(o: B.Octets) -> B.Octets:
  B.Octets.of_list(mtf.used(B.Octets.to_list(o)))

# whether every byte of o is in alpha (so that mtf_encode keeps them all)
def mtf_covers(alpha: B.Octets, o: B.Octets) -> Bool:
  mtf.covers(B.Octets.to_list(o), B.Octets.to_list(alpha))

# the move-to-front and RLE2 symbols of o, starting from the alphabet alpha
# (bytes of o not in alpha are dropped: see mtf_covers)
def mtf_encode(alpha: B.Octets, o: B.Octets) -> List<&2, U32>:
  mtf.enc.fast(B.Octets.to_list(o), B.Octets.to_list(alpha), Nil{}, Nil{})

# the bytes the symbols syms stand for, starting from the alphabet alpha: a
# failure for a position past the alphabet (Bzip2BadSymbol) or more than max
# bytes (Bzip2OutputTooLarge)
def mtf_decode(alpha: B.Octets, syms: List<&2, U32>, max: Nat) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  mtf.res.octets(mtf_decode_list(syms, B.Octets.to_list(alpha), max))
