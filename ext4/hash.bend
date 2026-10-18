# bend-osdev-ext4: the directory hashes of hashed (htree) directories.
#
# The ext4 disk-layout documentation ("Hash Tree Directories") names the
# hash versions a dx_root records: 0 legacy, 1 half MD4, 2 TEA, and 3, 4, 5
# the same three reading names as unsigned chars (the superblock's
# s_flags say which a filesystem uses; s_hash_seed seeds MD4 and TEA). It
# does not define the functions. The definitions below are the package's,
# checked as black boxes against debugfs's dx_hash command and against the
# hashes e2fsck writes into the index of the directories it builds (see
# README.md, "Specification"): MD4's round functions and constants are
# those of RFC 1320, applied to 8 words at a time over 3 rounds of 8 steps;
# TEA is Wheeler and Needham's cipher, 16 cycles, used as a compression
# function on 4 words at a time; legacy is a multiplicative hash of the
# bytes. Names are packed into words big end first, each word starting from
# a padding word made of the name's remaining length.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E

type Ext4HashBuf is Data:
  Ext4HashBuf{a: U32, b: U32, c: U32, d: U32}

# a directory hash: the major hash orders the index; the minor is kept for
# readdir cookies and is not used by lookups
type Ext4DxHash is Data:
  Ext4DxHash{major: U32, minor: U32}

def Ext4DxHash.major(h: Ext4DxHash) -> U32:
  match h:
    case Ext4DxHash{a, b}:
      a

def Ext4DxHash.minor(h: Ext4DxHash) -> U32:
  match h:
    case Ext4DxHash{a, b}:
      b

def Ext4Hash.rol(+x: U32, s: Nat) -> U32:
  +k = s
  U32.or(U32.shln(x, k), U32.shrn(x, Nat.sub(32n, k)))

# a name byte as the hash reads it: sign-extended when chars are signed
def Ext4Hash.char.pick(neg: Bool, +c: U32) -> U32:
  match neg:
    case True{}:
      U32.or(c, 4294967040)
    case False{}:
      c

def Ext4Hash.char.go(signed: Bool, +b: U32) -> U32:
  match signed:
    case True{}:
      Ext4Hash.char.pick(U32.is_le(128, b), b)
    case False{}:
      b

def Ext4Hash.char(signed: Bool, c: U32) -> U32:
  Ext4Hash.char.go(signed, U32.and(c, 255))

# Legacy: a multiplicative hash over the bytes

def Ext4Hash.legacy.fix(top: Bool, +h: U32) -> U32:
  match top:
    case True{}:
      U32.sub(h, 2147483647)
    case False{}:
      h

def Ext4Hash.legacy.go(xs: List<&2, U32>, +signed: Bool, +h0: U32, h1: U32) -> U32:
  match xs:
    case Nil{}:
      U32.shl(h0)
    case Con{c, t}:
      +h = U32.add(h1, U32.xor(h0, U32.mul(Ext4Hash.char(signed, c), 7152373)))
      Ext4Hash.legacy.go(t, signed, Ext4Hash.legacy.fix(Bool.not(U32.is_eq(U32.and(h, 2147483648), 0)), h), h0)

def Ext4Hash.legacy(signed: Bool, xs: List<&2, U32>) -> U32:
  Ext4Hash.legacy.go(xs, signed, 312737325, 934013177)

# Packing a name into num words (str2hashbuf): each group of four bytes is
# shifted into a word that starts as the padding word; a final partial group
# is shifted into the padding word too; padding words fill what is left

# the words of the full groups, and the word the last (partial) group left
def Ext4Hash.groups(xs: List<&2, U32>, +signed: Bool, +pad: U32, val: U32, k: Nat, acc: List<&2, U32>) -> List<&2, U32> & U32:
  match xs k:
    case Nil{} _:
      (List.reverse(&2, U32, acc), val)
    case Con{c, t} 3n:
      Ext4Hash.groups(t, signed, pad, pad, 0n, Con{U32.add(Ext4Hash.char(signed, c), U32.shln(val, 8n)), acc})
    case Con{c, t} j:
      Ext4Hash.groups(t, signed, pad, U32.add(Ext4Hash.char(signed, c), U32.shln(val, 8n)), Nat.add(j, 1n), acc)

def Ext4Hash.pack.fin(+num: Nat, +pad: U32, r: List<&2, U32> & U32) -> List<&2, U32>:
  (fulls, val) = r
  List.take(&2, U32, List.append(&2, U32, fulls, Con{val, List.replicate(U32, num, pad)}), num)

# num words from a name whose remaining length (from xs on) is len
def Ext4Hash.pack(xs: List<&2, U32>, +len: Nat, +num: Nat, +signed: Bool) -> List<&2, U32>:
  +l = U32.from_nat(len)
  +p1 = U32.or(l, U32.shln(l, 8n))
  +pad = U32.or(p1, U32.shln(p1, 16n))
  Ext4Hash.pack.fin(num, pad, Ext4Hash.groups(B.take(Nat.mul(4n, num), xs), signed, pad, pad, 0n, Nil{}))

# Half MD4: MD4's three rounds over 8 words (RFC 1320's functions and
# constants, 8 steps a round)

def Ext4Hash.f(+x: U32, +y: U32, +z: U32) -> U32:
  U32.xor(z, U32.and(x, U32.xor(y, z)))

def Ext4Hash.g(+x: U32, +y: U32, +z: U32) -> U32:
  U32.add(U32.and(x, y), U32.and(U32.xor(x, y), z))

def Ext4Hash.h(x: U32, y: U32, z: U32) -> U32:
  U32.xor(x, U32.xor(y, z))

def Ext4Hash.r1(a: U32, +b: U32, +c: U32, +d: U32, x: U32, s: Nat) -> U32:
  Ext4Hash.rol(U32.add(U32.add(a, Ext4Hash.f(b, c, d)), x), s)

def Ext4Hash.r2(a: U32, +b: U32, +c: U32, +d: U32, x: U32, s: Nat) -> U32:
  Ext4Hash.rol(U32.add(U32.add(a, Ext4Hash.g(b, c, d)), U32.add(x, 1518500249)), s)

def Ext4Hash.r3(a: U32, +b: U32, +c: U32, +d: U32, x: U32, s: Nat) -> U32:
  Ext4Hash.rol(U32.add(U32.add(a, Ext4Hash.h(b, c, d)), U32.add(x, 1859775393)), s)

def Ext4Hash.md4.go(+a: U32, +b: U32, +c: U32, +d: U32, +i0: U32, +i1: U32, +i2: U32, +i3: U32, +i4: U32, +i5: U32, +i6: U32, +i7: U32) -> Ext4HashBuf:
  +a1 = Ext4Hash.r1(a, b, c, d, i0, 3n)
  +d1 = Ext4Hash.r1(d, a1, b, c, i1, 7n)
  +c1 = Ext4Hash.r1(c, d1, a1, b, i2, 11n)
  +b1 = Ext4Hash.r1(b, c1, d1, a1, i3, 19n)
  +a2 = Ext4Hash.r1(a1, b1, c1, d1, i4, 3n)
  +d2 = Ext4Hash.r1(d1, a2, b1, c1, i5, 7n)
  +c2 = Ext4Hash.r1(c1, d2, a2, b1, i6, 11n)
  +b2 = Ext4Hash.r1(b1, c2, d2, a2, i7, 19n)
  +a3 = Ext4Hash.r2(a2, b2, c2, d2, i1, 3n)
  +d3 = Ext4Hash.r2(d2, a3, b2, c2, i3, 5n)
  +c3 = Ext4Hash.r2(c2, d3, a3, b2, i5, 9n)
  +b3 = Ext4Hash.r2(b2, c3, d3, a3, i7, 13n)
  +a4 = Ext4Hash.r2(a3, b3, c3, d3, i0, 3n)
  +d4 = Ext4Hash.r2(d3, a4, b3, c3, i2, 5n)
  +c4 = Ext4Hash.r2(c3, d4, a4, b3, i4, 9n)
  +b4 = Ext4Hash.r2(b3, c4, d4, a4, i6, 13n)
  +a5 = Ext4Hash.r3(a4, b4, c4, d4, i3, 3n)
  +d5 = Ext4Hash.r3(d4, a5, b4, c4, i7, 9n)
  +c5 = Ext4Hash.r3(c4, d5, a5, b4, i2, 11n)
  +b5 = Ext4Hash.r3(b4, c5, d5, a5, i6, 15n)
  +a6 = Ext4Hash.r3(a5, b5, c5, d5, i1, 3n)
  +d6 = Ext4Hash.r3(d5, a6, b5, c5, i5, 9n)
  +c6 = Ext4Hash.r3(c5, d6, a6, b5, i0, 11n)
  +b6 = Ext4Hash.r3(b5, c6, d6, a6, i4, 15n)
  Ext4HashBuf{U32.add(a, a6), U32.add(b, b6), U32.add(c, c6), U32.add(d, d6)}

# one half-MD4 step: the buffer after 8 words
def Ext4Hash.md4(buf: Ext4HashBuf, ws: List<&2, U32>) -> Ext4HashBuf:
  match buf ws:
    case Ext4HashBuf{a, b, c, d} Con{i0, Con{i1, Con{i2, Con{i3, Con{i4, Con{i5, Con{i6, Con{i7, t}}}}}}}}:
      Ext4Hash.md4.go(a, b, c, d, i0, i1, i2, i3, i4, i5, i6, i7)
    case _ _:
      buf

# TEA: 16 cycles of Wheeler and Needham's cipher on the buffer's first two
# words, keyed by 4 words, added back into the buffer

def Ext4Hash.tea.go(n: Nat, +sum: U32, +b0: U32, +b1: U32, +a: U32, +b: U32, +c: U32, +d: U32) -> U32 & U32:
  match n:
    case 0n:
      (b0, b1)
    case 1n+p:
      +s = U32.add(sum, 2654435769)
      +x0 = U32.add(b0, U32.xor(U32.xor(U32.add(U32.shln(b1, 4n), a), U32.add(b1, s)), U32.add(U32.shrn(b1, 5n), b)))
      +x1 = U32.add(b1, U32.xor(U32.xor(U32.add(U32.shln(x0, 4n), c), U32.add(x0, s)), U32.add(U32.shrn(x0, 5n), d)))
      Ext4Hash.tea.go(p, s, x0, x1, a, b, c, d)

def Ext4Hash.tea.fin(+b0: U32, +b1: U32, c: U32, d: U32, r: U32 & U32) -> Ext4HashBuf:
  (x0, x1) = r
  Ext4HashBuf{U32.add(b0, x0), U32.add(b1, x1), c, d}

# one TEA step: the buffer after 4 words
def Ext4Hash.tea(buf: Ext4HashBuf, ws: List<&2, U32>) -> Ext4HashBuf:
  match buf ws:
    case Ext4HashBuf{+b0, +b1, c, d} Con{i0, Con{i1, Con{i2, Con{i3, t}}}}:
      Ext4Hash.tea.fin(b0, b1, c, d, Ext4Hash.tea.go(16n, 0, b0, b1, i0, i1, i2, i3))
    case _ _:
      buf

# The chunked hashes: md4 over 32 bytes at a time, tea over 16

def Ext4Hash.md4.chunks(fuel: Nat, xs: List<&2, U32>, +len: Nat, +signed: Bool, buf: Ext4HashBuf) -> Ext4HashBuf:
  match fuel:
    case 0n:
      buf
    case 1n+f:
      +ys = xs
      Ext4Hash.md4.chunks(f, B.drop(32n, ys), Nat.sub(len, 32n), signed, Ext4Hash.md4(buf, Ext4Hash.pack(ys, len, 8n, signed)))

def Ext4Hash.tea.chunks(fuel: Nat, xs: List<&2, U32>, +len: Nat, +signed: Bool, buf: Ext4HashBuf) -> Ext4HashBuf:
  match fuel:
    case 0n:
      buf
    case 1n+f:
      +ys = xs
      Ext4Hash.tea.chunks(f, B.drop(16n, ys), Nat.sub(len, 16n), signed, Ext4Hash.tea(buf, Ext4Hash.pack(ys, len, 4n, signed)))

# the starting buffer: the seed, unless it is all zeros (or missing), when
# MD4's initial words are used
def Ext4Hash.start.pick(zero: Bool, seed: List<&2, U32>) -> Ext4HashBuf:
  match zero seed:
    case False{} Con{a, Con{b, Con{c, Con{d, t}}}}:
      Ext4HashBuf{a, b, c, d}
    case _ _:
      Ext4HashBuf{1732584193, 4023233417, 2562383102, 271733878}

def Ext4Hash.all_zero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(U32.is_eq(h, 0), Ext4Hash.all_zero(t))

def Ext4Hash.start(+seed: List<&2, U32>) -> Ext4HashBuf:
  Ext4Hash.start.pick(Ext4Hash.all_zero(seed), seed)

def Ext4HashBuf.a(x: Ext4HashBuf) -> U32:
  match x:
    case Ext4HashBuf{a, b, c, d}:
      a

def Ext4HashBuf.b(x: Ext4HashBuf) -> U32:
  match x:
    case Ext4HashBuf{a, b, c, d}:
      b

def Ext4HashBuf.c(x: Ext4HashBuf) -> U32:
  match x:
    case Ext4HashBuf{a, b, c, d}:
      c

def Ext4Hash.md4_of(+signed: Bool, seed: List<&2, U32>, +xs: List<&2, U32>) -> Ext4DxHash:
  +n = B.len(xs)
  +buf = Ext4Hash.md4.chunks(Nat.div(Nat.add(n, 31n), 32n), xs, n, signed, Ext4Hash.start(seed))
  Ext4DxHash{Ext4HashBuf.b(buf), Ext4HashBuf.c(buf)}

def Ext4Hash.tea_of(+signed: Bool, seed: List<&2, U32>, +xs: List<&2, U32>) -> Ext4DxHash:
  +n = B.len(xs)
  +buf = Ext4Hash.tea.chunks(Nat.div(Nat.add(n, 15n), 16n), xs, n, signed, Ext4Hash.start(seed))
  Ext4DxHash{Ext4HashBuf.a(buf), Ext4HashBuf.b(buf)}

# the major hash as stored: bit 0 cleared (it marks a collision in the
# index), and the end-of-directory value 0xFFFFFFFE avoided
def Ext4Hash.finish.pick(eof: Bool, +h: U32) -> U32:
  match eof:
    case True{}:
      4294967292
    case False{}:
      h

def Ext4Hash.finish(h: Ext4DxHash) -> Ext4DxHash:
  match h:
    case Ext4DxHash{a, b}:
      +m = U32.and(a, 4294967294)
      Ext4DxHash{Ext4Hash.finish.pick(U32.is_eq(m, 4294967294), m), b}

# The hash versions

# the version a lookup uses: the root's (0 to 2), moved to its unsigned
# twin (3 to 5) when the filesystem hashes unsigned chars
def Ext4Hash.version.pick(low: Bool, +v: U32) -> U32:
  match low:
    case True{}:
      U32.add(v, 3)
    case False{}:
      v

def Ext4Hash.version(+root: U32, signed: Bool) -> U32:
  match signed:
    case True{}:
      root
    case False{}:
      Ext4Hash.version.pick(U32.is_le(root, 2), root)

def Ext4Hash.of.go(v: Nat, seed: List<&2, U32>, +xs: List<&2, U32>, +ver: U32) -> Result<&2, &2, E.Ext4Error, Ext4DxHash>:
  match v:
    case 0n:
      Done{Ext4DxHash{Ext4Hash.legacy(True{}, xs), 0}}
    case 1n:
      Done{Ext4Hash.md4_of(True{}, seed, xs)}
    case 2n:
      Done{Ext4Hash.tea_of(True{}, seed, xs)}
    case 3n:
      Done{Ext4DxHash{Ext4Hash.legacy(False{}, xs), 0}}
    case 4n:
      Done{Ext4Hash.md4_of(False{}, seed, xs)}
    case 5n:
      Done{Ext4Hash.tea_of(False{}, seed, xs)}
    case _:
      Fail{E.Ext4BadHashVersion{ver}}

# the hash of a name under hash version v (0 to 5) and a 4-word seed;
# Ext4BadHashVersion for any other version (6, SipHash, is for casefolded
# encrypted directories, which are not read)
def Ext4Hash.name(+v: U32, seed: List<&2, U32>, name: B.Octets) -> Result<&2, &2, E.Ext4Error, Ext4DxHash>:
  do Result<&2, &2, E.Ext4Error, Ext4DxHash>:
    h : Ext4DxHash <- Ext4Hash.of.go(U32.to_nat(v), seed, B.Octets.to_list(name), v)
    return Ext4Hash.finish(h)
