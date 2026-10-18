# bend-osdev-lzo, Adler-32 (RFC 1950, section 8.2): the checksum the lzop
# container uses by default. Two sums modulo 65521: a, one plus the bytes;
# b, the sum of each step's a. The checksum is b * 65536 + a.
#
# Streaming: Adler32.start, then Adler32.update with each piece, then
# Adler32.finish; adler32 is the three in a row. LAWS.bend proves that
# pieces give the checksum of the whole.
import Base
import ../bytes/bytes.bend as B

# the two sums
type Adler32 is Data:
  Adler32{a: U32, b: U32}

# x, less 65521 if it is 65521 or more (x below 2 * 65521)
def adl.pick(lt: Bool, +x: U32) -> U32:
  match lt:
    case True{}:
      x
    case False{}:
      U32.sub(x, 65521)

def adl.mod(+x: U32) -> U32:
  adl.pick(U32.is_lt(x, 65521), x)

def adl.go(xs: List<&2, U32>, s: Adler32) -> Adler32:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      match s:
        case Adler32{a, b}:
          +a2 = adl.mod(U32.add(a, h))
          adl.go(t, Adler32{a2, adl.mod(U32.add(b, a2))})

def Adler32.start() -> Adler32:
  Adler32{1, 0}

def Adler32.update(s: Adler32, o: B.Octets) -> Adler32:
  adl.go(B.Octets.to_list(o), s)

def Adler32.finish(s: Adler32) -> U32:
  match s:
    case Adler32{a, b}:
      U32.or(U32.shln(b, 16n), a)

def adler32(o: B.Octets) -> U32:
  Adler32.finish(Adler32.update(Adler32.start(), o))
