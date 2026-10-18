# DES (FIPS 46-3, Data Encryption Standard, 1999) as a 64-bit block cipher.
#
# The cipher is IP, sixteen Feistel rounds (L, R) -> (R, L xor f(K_i, R)),
# the swap of the two halves, and IP^-1. Decryption here undoes each step in
# reverse order: IP, the swap, the rounds undone last to first
# ((L', R') -> (R' xor f(K_i, L'), L')), IP^-1. That is the same function as
# FIPS 46-3's "the same algorithm with the key schedule reversed", written so
# that decrypt(encrypt(b)) == b is provable for every key and every block
# (LAWS.bend): a Feistel round is undone whatever its round function.
#
# IP and IP^-1 move bits as lists of Bools, so a proof computes through them.
# The round function f and the key schedule use native word operations: f
# looks up eight tables that combine each S-box with the permutation P (SP),
# built from FIPS 46-3's S-boxes and P once per key (Bend 2.0.37 does not keep
# a computed table between calls, so the key holds it).
import Base
import ../bytes/bytes.bend as B
import ./legacy-ciphers.bend as L

# The tables of FIPS 46-3 (bit 1 is the most significant)

# IP
def des.ip.table() -> List<&2, Nat>:
  [58n, 50n, 42n, 34n, 26n, 18n, 10n, 2n, 60n, 52n, 44n, 36n, 28n, 20n, 12n, 4n,
    62n, 54n, 46n, 38n, 30n, 22n, 14n, 6n, 64n, 56n, 48n, 40n, 32n, 24n, 16n, 8n,
    57n, 49n, 41n, 33n, 25n, 17n, 9n, 1n, 59n, 51n, 43n, 35n, 27n, 19n, 11n, 3n,
    61n, 53n, 45n, 37n, 29n, 21n, 13n, 5n, 63n, 55n, 47n, 39n, 31n, 23n, 15n, 7n]

# IP^-1
def des.fp.table() -> List<&2, Nat>:
  [40n, 8n, 48n, 16n, 56n, 24n, 64n, 32n, 39n, 7n, 47n, 15n, 55n, 23n, 63n, 31n,
    38n, 6n, 46n, 14n, 54n, 22n, 62n, 30n, 37n, 5n, 45n, 13n, 53n, 21n, 61n, 29n,
    36n, 4n, 44n, 12n, 52n, 20n, 60n, 28n, 35n, 3n, 43n, 11n, 51n, 19n, 59n, 27n,
    34n, 2n, 42n, 10n, 50n, 18n, 58n, 26n, 33n, 1n, 41n, 9n, 49n, 17n, 57n, 25n]

# P
def des.p.table() -> List<&2, Nat>:
  [16n, 7n, 20n, 21n, 29n, 12n, 28n, 17n, 1n, 15n, 23n, 26n, 5n, 18n, 31n, 10n,
    2n, 8n, 24n, 14n, 32n, 27n, 3n, 9n, 19n, 13n, 30n, 6n, 22n, 11n, 4n, 25n]

# PC-1, the bits of C_0
def des.pc1c.table() -> List<&2, Nat>:
  [57n, 49n, 41n, 33n, 25n, 17n, 9n, 1n, 58n, 50n, 42n, 34n, 26n, 18n, 10n, 2n,
    59n, 51n, 43n, 35n, 27n, 19n, 11n, 3n, 60n, 52n, 44n, 36n]

# PC-1, the bits of D_0
def des.pc1d.table() -> List<&2, Nat>:
  [63n, 55n, 47n, 39n, 31n, 23n, 15n, 7n, 62n, 54n, 46n, 38n, 30n, 22n, 14n, 6n,
    61n, 53n, 45n, 37n, 29n, 21n, 13n, 5n, 28n, 20n, 12n, 4n]

# PC-2, its first 24 entries
def des.pc2a.table() -> List<&2, Nat>:
  [14n, 17n, 11n, 24n, 1n, 5n, 3n, 28n, 15n, 6n, 21n, 10n, 23n, 19n, 12n, 4n,
    26n, 8n, 16n, 7n, 27n, 20n, 13n, 2n]

# PC-2, its last 24 entries
def des.pc2b.table() -> List<&2, Nat>:
  [41n, 52n, 31n, 37n, 47n, 55n, 30n, 40n, 51n, 45n, 33n, 48n, 44n, 49n, 39n, 56n,
    34n, 53n, 46n, 42n, 50n, 36n, 29n, 32n]

# the left shifts of the key schedule
def des.shifts() -> List<&2, Nat>:
  [1n, 1n, 2n, 2n, 2n, 2n, 2n, 2n, 1n, 2n, 2n, 2n, 2n, 2n, 2n, 1n]

# S1: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s1() -> List<&2, U32>:
  [14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7,
    0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8,
    4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0,
    15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13]

# S2: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s2() -> List<&2, U32>:
  [15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10,
    3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5,
    0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15,
    13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9]

# S3: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s3() -> List<&2, U32>:
  [10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8,
    13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1,
    13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7,
    1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12]

# S4: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s4() -> List<&2, U32>:
  [7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15,
    13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9,
    10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4,
    3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14]

# S5: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s5() -> List<&2, U32>:
  [2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9,
    14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6,
    4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14,
    11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3]

# S6: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s6() -> List<&2, U32>:
  [12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11,
    10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8,
    9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6,
    4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13]

# S7: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s7() -> List<&2, U32>:
  [4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1,
    13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6,
    1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2,
    6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12]

# S8: row r (0 to 3), column c (0 to 15) is entry 16r + c
def des.s8() -> List<&2, U32>:
  [13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7,
    1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2,
    7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8,
    2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11]

# IP and IP^-1, on bits

# the bits of a block, bit 1 (the top bit of hi) first
def des.bits(b: L.LcBlock64) -> List<&2, Bool>:
  match b:
    case L.LcBlock64{hi, lo}:
      L.lc.msb(hi, L.lc.msb(lo, Nil{}))

# the bits a table picks: entry t is bit t of bs
def des.pick(tab: List<&2, Nat>, +bs: List<&2, Bool>) -> List<&2, Bool>:
  match tab:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      Con{L.lc.nth(bs, Nat.sub(t, 1n)), des.pick(rest, bs)}

# The two halves of the Feistel network (internal)
type LcDesHalves is Data:
  LcDesHalves{l: U32, r: U32}

# 64 bits as halves: the first 32 (most significant first) are l
def des.halves(bs: List<&2, Bool>) -> LcDesHalves:
  +rv = L.lc.rev_bits(bs, Nil{})
  LcDesHalves{U32{L.lc.word_lsb(32n, L.lc.drop_bits(32n, rv))}, U32{L.lc.word_lsb(32n, rv)}}

def des.block(bs: List<&2, Bool>) -> L.LcBlock64:
  +rv = L.lc.rev_bits(bs, Nil{})
  L.LcBlock64{U32{L.lc.word_lsb(32n, L.lc.drop_bits(32n, rv))}, U32{L.lc.word_lsb(32n, rv)}}

def des.hbits(h: LcDesHalves) -> List<&2, Bool>:
  match h:
    case LcDesHalves{l, r}:
      L.lc.msb(l, L.lc.msb(r, Nil{}))

def des.ip(b: L.LcBlock64) -> LcDesHalves:
  des.halves(des.pick(des.ip.table(), des.bits(b)))

def des.fp(h: LcDesHalves) -> L.LcBlock64:
  des.block(des.pick(des.fp.table(), des.hbits(h)))

def des.swap(h: LcDesHalves) -> LcDesHalves:
  match h:
    case LcDesHalves{l, r}:
      LcDesHalves{r, l}

# The round function f(K, R) = P(S(E(R) xor K))


# a permutation of a 32-bit word (P): entry t is bit t of x
def des.perm32(tab: List<&2, Nat>, +x: U32, acc: U32) -> U32:
  match tab:
    case Nil{}:
      acc
    case Con{t, rest}:
      des.perm32(rest, x, U32.or(U32.shl(acc), L.lc.bit(x, Nat.sub(32n, t))))

# the S-box entry for 6 bits b1 .. b6: row b1 b6, column b2 b3 b4 b5
def des.sbox(s: List<&2, U32>, +x: U32) -> U32:
  +row = U32.or(U32.and(2, U32.shrn(x, 4n)), U32.and(1, x))
  +col = U32.and(15, U32.shr(x))
  L.lc.at(s, U32.to_nat(U32.add(U32.mul(row, 16), col)))

# the SP table of S-box s, its output placed sh bits up (28 for S1 .. 0 for
# S8): entry x is P of S(x) in place
def des.sp.go(n: Nat, +s: List<&2, U32>, +sh: Nat, +x: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{des.perm32(des.p.table(), U32.shln(des.sbox(s, x), sh), 0), des.sp.go(p, s, sh, U32.add(x, 1))}

def des.sp(s: List<&2, U32>, sh: Nat) -> L.LcTab:
  L.lc.tab(6n, des.sp.go(64n, s, sh, 0))

def des.sp1() -> L.LcTab:
  des.sp(des.s1(), 28n)

def des.sp2() -> L.LcTab:
  des.sp(des.s2(), 24n)

def des.sp3() -> L.LcTab:
  des.sp(des.s3(), 20n)

def des.sp4() -> L.LcTab:
  des.sp(des.s4(), 16n)

def des.sp5() -> L.LcTab:
  des.sp(des.s5(), 12n)

def des.sp6() -> L.LcTab:
  des.sp(des.s6(), 8n)

def des.sp7() -> L.LcTab:
  des.sp(des.s7(), 4n)

def des.sp8() -> L.LcTab:
  des.sp(des.s8(), 0n)

# the eight SP tables, built once per key (internal)
type LcDesSp is Data:
  LcDesSp{t1: L.LcTab, t2: L.LcTab, t3: L.LcTab, t4: L.LcTab, t5: L.LcTab, t6: L.LcTab, t7: L.LcTab, t8: L.LcTab}

def des.tables() -> LcDesSp:
  LcDesSp{des.sp1(), des.sp2(), des.sp3(), des.sp4(), des.sp5(), des.sp6(), des.sp7(), des.sp8()}

# a round key: a 48-bit subkey as its eight 6-bit groups, K's bits 1 to 6
# first, and the SP tables (internal)
type LcDesRk is Data:
  LcDesRk{sp: LcDesSp, k0: U32, k1: U32, k2: U32, k3: U32, k4: U32, k5: U32, k6: U32, k7: U32}

# group i of E(R): bits 4i .. 4i + 5 of R (bit 0 is bit 32), the top six bits
# of R rotated left by n = 4i - 1 (mod 32)
def des.e(+r: U32, +n: Nat) -> U32:
  U32.and(63, U32.shrn(L.lc.rotl(r, n), 26n))

def des.f(k: LcDesRk, +r: U32) -> U32:
  match k:
    case LcDesRk{LcDesSp{t1, t2, t3, t4, t5, t6, t7, t8}, k0, k1, k2, k3, k4, k5, k6, k7}:
      +a = U32.xor(L.lc.tab.get(6n, t1, U32.xor(des.e(r, 31n), k0)), L.lc.tab.get(6n, t2, U32.xor(des.e(r, 3n), k1)))
      +b = U32.xor(L.lc.tab.get(6n, t3, U32.xor(des.e(r, 7n), k2)), L.lc.tab.get(6n, t4, U32.xor(des.e(r, 11n), k3)))
      +c = U32.xor(L.lc.tab.get(6n, t5, U32.xor(des.e(r, 15n), k4)), L.lc.tab.get(6n, t6, U32.xor(des.e(r, 19n), k5)))
      +d = U32.xor(L.lc.tab.get(6n, t7, U32.xor(des.e(r, 23n), k6)), L.lc.tab.get(6n, t8, U32.xor(des.e(r, 27n), k7)))
      U32.xor(U32.xor(a, b), U32.xor(c, d))

# The Feistel network

def des.step(k: LcDesRk, h: LcDesHalves) -> LcDesHalves:
  match h:
    case LcDesHalves{l, +r}:
      LcDesHalves{r, U32.xor(l, des.f(k, r))}

# the round undone
def des.unstep(k: LcDesRk, h: LcDesHalves) -> LcDesHalves:
  match h:
    case LcDesHalves{+a, b}:
      LcDesHalves{U32.xor(b, des.f(k, a)), a}

# the rounds of ks, first to last
def des.rounds(ks: List<&2, LcDesRk>, h: LcDesHalves) -> LcDesHalves:
  match ks:
    case Nil{}:
      h
    case Con{k, t}:
      des.rounds(t, des.step(k, h))

# the rounds of ks undone, last to first
def des.unrounds(ks: List<&2, LcDesRk>, h: LcDesHalves) -> LcDesHalves:
  match ks:
    case Nil{}:
      h
    case Con{k, t}:
      des.unstep(k, des.unrounds(t, h))

# The key schedule

def des.kbit.pick(low: Bool, +hi: U32, +lo: U32, +t: Nat) -> U32:
  match low:
    case True{}:
      L.lc.bit(lo, Nat.sub(64n, t))
    case False{}:
      L.lc.bit(hi, Nat.sub(32n, t))

# the bits that tab picks from the 64-bit key hi:lo, appended to acc
def des.picks64(tab: List<&2, Nat>, +hi: U32, +lo: U32, acc: U32) -> U32:
  match tab:
    case Nil{}:
      acc
    case Con{+t, rest}:
      des.picks64(rest, hi, lo, U32.or(U32.shl(acc), des.kbit.pick(Nat.is_lt(32n, t), hi, lo, t)))

def des.cdbit.pick(low: Bool, +c: U32, +d: U32, +t: Nat) -> U32:
  match low:
    case True{}:
      L.lc.bit(d, Nat.sub(56n, t))
    case False{}:
      L.lc.bit(c, Nat.sub(28n, t))

# the bits that tab picks from the 56 bits C:D (28 each), appended to acc
def des.picks56(tab: List<&2, Nat>, +c: U32, +d: U32, acc: U32) -> U32:
  match tab:
    case Nil{}:
      acc
    case Con{+t, rest}:
      des.picks56(rest, c, d, U32.or(U32.shl(acc), des.cdbit.pick(Nat.is_lt(28n, t), c, d, t)))

def des.rot28(+x: U32, +s: Nat) -> U32:
  U32.and(268435455, U32.or(U32.shln(x, s), U32.shrn(x, Nat.sub(28n, s))))

def des.group(+x: U32, n: Nat) -> U32:
  U32.and(63, U32.shrn(x, n))

# K_i = PC-2(C_i D_i), as its eight groups
def des.subkey(sp: LcDesSp, +c: U32, +d: U32) -> LcDesRk:
  +a = des.picks56(des.pc2a.table(), c, d, 0)
  +b = des.picks56(des.pc2b.table(), c, d, 0)
  LcDesRk{sp, des.group(a, 18n), des.group(a, 12n), des.group(a, 6n), des.group(a, 0n), des.group(b, 18n), des.group(b, 12n), des.group(b, 6n), des.group(b, 0n)}

# K_1 .. K_16 from C_0, D_0
def des.schedule(shifts: List<&2, Nat>, +sp: LcDesSp, +c: U32, +d: U32) -> List<&2, LcDesRk>:
  match shifts:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      +c2 = des.rot28(c, s)
      +d2 = des.rot28(d, s)
      Con{des.subkey(sp, c2, d2), des.schedule(t, sp, c2, d2)}

# A DES key: its sixteen round keys (opaque; built by LcDes.key)
type LcDesKey is Data:
  LcDesKey{ks: List<&2, LcDesRk>}

# the key whose 64 bits (parity bits included, and ignored) are hi:lo
def des.key_of(+hi: U32, +lo: U32) -> LcDesKey:
  LcDesKey{des.schedule(des.shifts(), des.tables(), des.picks64(des.pc1c.table(), hi, lo, 0), des.picks64(des.pc1d.table(), hi, lo, 0))}

def des.key.pick(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcDesKey>:
  match ok:
    case True{}:
      Done{des.key_of(L.lc.be(L.lc.at(xs, 0n), L.lc.at(xs, 1n), L.lc.at(xs, 2n), L.lc.at(xs, 3n)), L.lc.be(L.lc.at(xs, 4n), L.lc.at(xs, 5n), L.lc.at(xs, 6n), L.lc.at(xs, 7n)))}
    case False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# an 8-byte key (the parity bits, the low bit of each byte, are not checked)
def LcDes.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcDesKey>:
  +xs = B.Octets.to_list(o)
  des.key.pick(Nat.is_eq(B.len(xs), 8n), xs)

def LcDes.encrypt(k: LcDesKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcDesKey{ks}:
      des.fp(des.swap(des.rounds(ks, des.ip(b))))

def LcDes.decrypt(k: LcDesKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcDesKey{ks}:
      des.fp(des.unrounds(ks, des.swap(des.ip(b))))
