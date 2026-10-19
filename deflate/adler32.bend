# bend-osdev-deflate: Adler-32, the zlib format's check value (RFC 1950,
# section 2.2, ADLER32, and section 9's sample code).
#
# "s1 is the sum of all bytes, s2 is the sum of all s1 values. Both sums
# are done modulo 65521. s1 is initialized to 1, s2 to zero. The Adler-32
# checksum is stored as s2*65536 + s1". Each sum stays below 65521, so one
# subtraction after each addition keeps it there (a byte is at most 255, a
# sum at most 65520).
#
# Streaming: Adler32.start, Adler32.update (any number of times, on pieces
# in order), Adler32.finish; adler32(o) is the one-shot form.
import Base
import ../bytes/bytes.bend as B

type Adler32 is Data:
  Adler32{s1: U32, s2: U32}

def adl.base() -> U32:
  65521

def adl.red(big: Bool, +x: U32) -> U32:
  match big:
    case True{}:
      U32.sub(x, adl.base())
    case False{}:
      x

# x modulo 65521, for x below 2 * 65521
def adl.mod(+x: U32) -> U32:
  adl.red(U32.is_le(adl.base(), x), x)

def adl.step(a: Adler32, h: U32) -> Adler32:
  match a:
    case Adler32{s1, s2}:
      +n1 = adl.mod(U32.add(s1, B.byte(h)))
      Adler32{n1, adl.mod(U32.add(s2, n1))}

def adl.go(xs: List<&2, U32>, a: Adler32) -> Adler32:
  match xs:
    case Nil{}:
      a
    case Con{h, t}:
      adl.go(t, adl.step(a, h))

def Adler32.start() -> Adler32:
  Adler32{1, 0}

def Adler32.update(a: Adler32, o: B.Octets) -> Adler32:
  adl.go(B.Octets.to_list(o), a)

def Adler32.finish(a: Adler32) -> U32:
  match a:
    case Adler32{s1, s2}:
      U32.or(U32.shln(s2, 16n), s1)

# the Adler-32 of o
def adler32(o: B.Octets) -> U32:
  Adler32.finish(Adler32.update(Adler32.start(), o))
