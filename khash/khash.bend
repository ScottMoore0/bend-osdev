# bend-osdev-khash: non-cryptographic hashes. This file: Bob Jenkins'
# lookup3 (public domain; "Hash functions for hash table lookup", 2006,
# burtleburtle.net/bob/hash/doobs.html and its lookup3 description), in the
# forms the kernel calls jhash (a byte string, as Jenkins' hashlittle),
# jhash2 (32-bit words, as hashword) and jhash_1word to jhash_3words.
#
# The state is three words a, b, c, all set to 0xdeadbeef + length in bytes
# + initval. Each full block of twelve bytes (three words) is added in and
# mixed; the last block, of one to twelve bytes (one to three words), is
# added in and finished; an empty input skips the finish. The answer is c.
# Bytes go into words little-endian.
#
# golden.bend holds the multiplicative hashes (hash_32, hash_64).
import Base
import ../bytes/bytes.bend as B

def jhash.initval() -> U32:
  3735928559

def jhash.rot(+x: U32, +k: Nat) -> U32:
  U32.or(U32.shln(x, k), U32.shrn(x, Nat.sub(32n, k)))

type JhashState is Data:
  JhashState{a: U32, b: U32, c: U32}

# mix(a, b, c): six rounds of subtract, rotate-xor, add
def jhash.mix(s: JhashState) -> JhashState:
  match s:
    case JhashState{+a, +b, +c}:
      +a1 = U32.xor(U32.sub(a, c), jhash.rot(c, 4n))
      +c1 = U32.add(c, b)
      +b1 = U32.xor(U32.sub(b, a1), jhash.rot(a1, 6n))
      +a2 = U32.add(a1, c1)
      +c2 = U32.xor(U32.sub(c1, b1), jhash.rot(b1, 8n))
      +b2 = U32.add(b1, a2)
      +a3 = U32.xor(U32.sub(a2, c2), jhash.rot(c2, 16n))
      +c3 = U32.add(c2, b2)
      +b3 = U32.xor(U32.sub(b2, a3), jhash.rot(a3, 19n))
      +a4 = U32.add(a3, c3)
      +c4 = U32.xor(U32.sub(c3, b3), jhash.rot(b3, 4n))
      +b4 = U32.add(b3, a4)
      JhashState{a4, b4, c4}

# final(a, b, c): seven rounds of xor and subtract-rotate
def jhash.final(s: JhashState) -> JhashState:
  match s:
    case JhashState{+a, +b, +c}:
      +c1 = U32.sub(U32.xor(c, b), jhash.rot(b, 14n))
      +a1 = U32.sub(U32.xor(a, c1), jhash.rot(c1, 11n))
      +b1 = U32.sub(U32.xor(b, a1), jhash.rot(a1, 25n))
      +c2 = U32.sub(U32.xor(c1, b1), jhash.rot(b1, 16n))
      +a2 = U32.sub(U32.xor(a1, c2), jhash.rot(c2, 4n))
      +b2 = U32.sub(U32.xor(b1, a2), jhash.rot(a2, 14n))
      +c3 = U32.sub(U32.xor(c2, b2), jhash.rot(b2, 24n))
      JhashState{a2, b2, c3}

def jhash.add(s: JhashState, x: U32, y: U32, z: U32) -> JhashState:
  match s:
    case JhashState{a, b, c}:
      JhashState{U32.add(a, x), U32.add(b, y), U32.add(c, z)}

def jhash.c(s: JhashState) -> U32:
  match s:
    case JhashState{a, b, c}:
      c

def jhash.start(+v: U32) -> JhashState:
  JhashState{v, v, v}

# Words (jhash2): blocks of three words while more than three remain

def jhash2.go(ws: List<&2, U32>, s: JhashState) -> U32:
  match ws:
    case Nil{}:
      jhash.c(s)
    case Con{x, Nil{}}:
      jhash.c(jhash.final(jhash.add(s, x, 0, 0)))
    case Con{x, Con{y, Nil{}}}:
      jhash.c(jhash.final(jhash.add(s, x, y, 0)))
    case Con{x, Con{y, Con{z, Nil{}}}}:
      jhash.c(jhash.final(jhash.add(s, x, y, z)))
    case Con{x, Con{y, Con{z, rest}}}:
      jhash2.go(rest, jhash.mix(jhash.add(s, x, y, z)))

def jhash.len.go(xs: List<&2, U32>, n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      jhash.len.go(t, U32.add(n, 1))

# the hash of the words ws, from initval
def Jhash.jhash2(+ws: List<&2, U32>, initval: U32) -> U32:
  jhash2.go(ws, jhash.start(U32.add(U32.add(jhash.initval(), U32.shln(jhash.len.go(ws, 0), 2n)), initval)))

# The three-word forms: jhash2 of [a, b, c], [a, b] and [a]

def Jhash.jhash_3words(a: U32, b: U32, c: U32, initval: U32) -> U32:
  jhash.c(jhash.final(jhash.add(jhash.start(U32.add(U32.add(jhash.initval(), 12), initval)), a, b, c)))

def Jhash.jhash_2words(a: U32, b: U32, initval: U32) -> U32:
  jhash.c(jhash.final(jhash.add(jhash.start(U32.add(U32.add(jhash.initval(), 8), initval)), a, b, 0)))

def Jhash.jhash_1word(a: U32, initval: U32) -> U32:
  jhash.c(jhash.final(jhash.add(jhash.start(U32.add(U32.add(jhash.initval(), 4), initval)), a, 0, 0)))

# Bytes (jhash): blocks of twelve bytes while more than twelve remain; the
# last block's missing bytes count as zero

# up to four bytes, little-endian, from the front of xs (missing ones 0)
def jhash.word(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{b0, Con{b1, Con{b2, Con{b3, t}}}}:
      U32.or(U32.and(255, b0), U32.or(U32.shln(U32.and(255, b1), 8n), U32.or(U32.shln(U32.and(255, b2), 16n), U32.shln(U32.and(255, b3), 24n))))
    case Con{b0, Con{b1, Con{b2, Nil{}}}}:
      U32.or(U32.and(255, b0), U32.or(U32.shln(U32.and(255, b1), 8n), U32.shln(U32.and(255, b2), 16n)))
    case Con{b0, Con{b1, Nil{}}}:
      U32.or(U32.and(255, b0), U32.shln(U32.and(255, b1), 8n))
    case Con{b0, Nil{}}:
      U32.and(255, b0)
    case Nil{}:
      0

# the bytes as words, padding the last with zero bytes
def jhash.words(n: Nat, +xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      B.rev(acc)
    case 1n+k:
      match xs:
        case Nil{}:
          B.rev(acc)
        case Con{h, t}:
          jhash.words(k, B.drop(3n, t), Con{jhash.word(Con{h, t}), acc})

# the hash of the bytes o, from initval; the same as jhash2 of the bytes
# read as little-endian words (the last padded with zero bytes), with the
# length counted in bytes
def Jhash.jhash(o: B.Octets, initval: U32) -> U32:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  jhash2.go(jhash.words(n, xs, Nil{}), jhash.start(U32.add(U32.add(jhash.initval(), U32.from_nat(n)), initval)))
