# Serpent (R. Anderson, E. Biham, L. Knudsen, "Serpent: A Proposal for the
# Advanced Encryption Standard", AES submission, 1998), in its bitslice
# description: a 128-bit block cipher with keys of up to 256 bits, as a
# cipher for cipher-modes' modes (~LcSerpentKey, ~LcSerpent.encrypt,
# ~LcSerpent.decrypt).
#
# Serpent reads the block as four little-endian words X0..X3 (byte 0 is the
# low byte of X0, as in the NESSIE vectors and the kernel); a CmBlock holds
# big-endian words, so the cipher swaps each word's bytes on the way in and
# out. The key schedule turns the key into a list of steps, each one
# invertible: the byte swap, the 33 round-key XORs, the 32 S-box layers and
# the 31 linear transformations. Encryption runs the steps first to last;
# decryption undoes them last to first (the inverse S-boxes and the inverse
# linear transformation), as the paper's decryption does, and
# decrypt(encrypt(b)) == b is provable for every key and block.
#
# The S-box layer works on bits: bit j of X0..X3 is a 4-bit value (X0 its low
# bit) that the S-box maps, so a proof can undo it one bit position at a time.
# The rotations of the linear transformation are computed on bits too; the
# key schedule's arithmetic is native.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-core/cipher-core.bend as L

# The eight S-boxes (section 2, "the S-boxes"): entry v is S_i(v)

type LcSpBox is Data:
  LcSp0{}
  LcSp1{}
  LcSp2{}
  LcSp3{}
  LcSp4{}
  LcSp5{}
  LcSp6{}
  LcSp7{}

def sp.table(b: LcSpBox) -> List<&2, U32>:
  match b:
    case LcSp0{}:
      [3, 8, 15, 1, 10, 6, 5, 11, 14, 13, 4, 2, 7, 0, 9, 12]
    case LcSp1{}:
      [15, 12, 2, 7, 9, 0, 5, 10, 1, 11, 14, 8, 6, 13, 3, 4]
    case LcSp2{}:
      [8, 6, 7, 9, 3, 12, 10, 15, 13, 1, 14, 4, 0, 11, 5, 2]
    case LcSp3{}:
      [0, 15, 11, 8, 12, 9, 6, 3, 13, 1, 2, 4, 10, 7, 5, 14]
    case LcSp4{}:
      [1, 15, 8, 3, 12, 0, 11, 6, 2, 5, 4, 10, 9, 14, 7, 13]
    case LcSp5{}:
      [15, 5, 2, 11, 4, 10, 9, 12, 0, 3, 14, 8, 13, 6, 7, 1]
    case LcSp6{}:
      [7, 2, 12, 5, 8, 4, 6, 11, 14, 9, 1, 15, 13, 3, 10, 0]
    case LcSp7{}:
      [1, 13, 15, 0, 14, 8, 2, 11, 7, 4, 12, 10, 9, 3, 5, 6]

# the inverse S-boxes
def sp.itable(b: LcSpBox) -> List<&2, U32>:
  match b:
    case LcSp0{}:
      [13, 3, 11, 0, 10, 6, 5, 12, 1, 14, 4, 7, 15, 9, 8, 2]
    case LcSp1{}:
      [5, 8, 2, 14, 15, 6, 12, 3, 11, 4, 7, 9, 1, 13, 10, 0]
    case LcSp2{}:
      [12, 9, 15, 4, 11, 14, 1, 2, 0, 3, 6, 13, 5, 8, 10, 7]
    case LcSp3{}:
      [0, 9, 10, 7, 11, 14, 6, 13, 3, 5, 12, 2, 4, 8, 15, 1]
    case LcSp4{}:
      [5, 0, 8, 3, 10, 9, 7, 14, 2, 12, 11, 6, 4, 15, 13, 1]
    case LcSp5{}:
      [8, 15, 2, 9, 4, 1, 13, 14, 11, 6, 5, 3, 7, 12, 10, 0]
    case LcSp6{}:
      [15, 10, 1, 13, 5, 3, 6, 0, 4, 9, 14, 7, 2, 12, 8, 11]
    case LcSp7{}:
      [3, 0, 6, 13, 9, 14, 15, 8, 5, 12, 11, 7, 10, 1, 4, 2]

def sp.pick(inv: Bool, b: LcSpBox) -> List<&2, U32>:
  match inv:
    case True{}:
      sp.itable(b)
    case False{}:
      sp.table(b)

# the S-box (inv False) or its inverse (inv True) at v
def sp.sbox(b: LcSpBox, inv: Bool, v: U32) -> U32:
  L.lc.at(sp.pick(inv, b), U32.to_nat(v))

# Four bits: bit j of X0, X1, X2, X3 (X0's is the low bit of the S-box input)
type LcSpNib is Data:
  LcSpNib{a: Bool, b: Bool, c: Bool, d: Bool}

def sp.na(n: LcSpNib) -> Bool:
  match n:
    case LcSpNib{a, b, c, d}:
      a

def sp.nb(n: LcSpNib) -> Bool:
  match n:
    case LcSpNib{a, b, c, d}:
      b

def sp.nc(n: LcSpNib) -> Bool:
  match n:
    case LcSpNib{a, b, c, d}:
      c

def sp.nd(n: LcSpNib) -> Bool:
  match n:
    case LcSpNib{a, b, c, d}:
      d

def sp.bit(+v: U32, i: Nat) -> Bool:
  U32.is_eq(L.lc.bit(v, i), 1)

def sp.nib(b: LcSpBox, inv: Bool, n: LcSpNib) -> LcSpNib:
  match n:
    case LcSpNib{x0, x1, x2, x3}:
      +v = U32.or(U32.or(Bool.to_u32(x0), U32.shl(Bool.to_u32(x1))), U32.or(U32.shln(Bool.to_u32(x2), 2n), U32.shln(Bool.to_u32(x3), 3n)))
      +w = sp.sbox(b, inv, v)
      LcSpNib{sp.bit(w, 0n), sp.bit(w, 1n), sp.bit(w, 2n), sp.bit(w, 3n)}

# Four m-bit words
type LcSpQ<-m: Nat> is Data:
  LcSpQ{a: Word(m), b: Word(m), c: Word(m), d: Word(m)}

def sp.qa(-m: Nat, q: LcSpQ<m>) -> Word(m):
  match q:
    case LcSpQ{a, b, c, d}:
      a

def sp.qb(-m: Nat, q: LcSpQ<m>) -> Word(m):
  match q:
    case LcSpQ{a, b, c, d}:
      b

def sp.qc(-m: Nat, q: LcSpQ<m>) -> Word(m):
  match q:
    case LcSpQ{a, b, c, d}:
      c

def sp.qd(-m: Nat, q: LcSpQ<m>) -> Word(m):
  match q:
    case LcSpQ{a, b, c, d}:
      d

# the S-box (or its inverse) at every bit position of four m-bit words
def sp.layer(+b: LcSpBox, +inv: Bool, m: Nat, q: LcSpQ<m>) -> LcSpQ<m>:
  match m:
    case 0n:
      q
    case 1n+p:
      match q:
        case LcSpQ{WCon{x0, t0}, WCon{x1, t1}, WCon{x2, t2}, WCon{x3, t3}}:
          +o = sp.nib(b, inv, LcSpNib{x0, x1, x2, x3})
          +r = sp.layer(b, inv, p, LcSpQ{t0, t1, t2, t3})
          LcSpQ{WCon{sp.na(o), sp.qa(p, r)}, WCon{sp.nb(o), sp.qb(p, r)}, WCon{sp.nc(o), sp.qc(p, r)}, WCon{sp.nd(o), sp.qd(p, r)}}

# the S-box layer (or its inverse) on the state X0..X3
def sp.sop(+b: LcSpBox, +inv: Bool, s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{U32{w0}, U32{w1}, U32{w2}, U32{w3}}:
      +r = sp.layer(b, inv, 32n, LcSpQ{w0, w1, w2, w3})
      M.CmBlock{U32{sp.qa(32n, r)}, U32{sp.qb(32n, r)}, U32{sp.qc(32n, r)}, U32{sp.qd(32n, r)}}

# The linear transformation (section 2), step by step, and each step undone

def sp.lt1(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{L.lc.rotl13.bits(x0), x1, x2, x3}

def sp.lt2(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{x0, x1, L.lc.rotl3.bits(x2), x3}

# X1 = X1 xor X0 xor X2 (its own inverse)
def sp.lt3(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{+x0, x1, +x2, x3}:
      M.CmBlock{x0, U32.xor(x1, U32.xor(x0, x2)), x2, x3}

# X3 = X3 xor X2 xor (X0 << 3) (its own inverse)
def sp.lt4(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{+x0, x1, +x2, x3}:
      M.CmBlock{x0, x1, x2, U32.xor(x3, U32.xor(x2, U32.shln(x0, 3n)))}

def sp.lt5(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{x0, L.lc.rotl1.bits(x1), x2, L.lc.rotl7.bits(x3)}

# X0 = X0 xor X1 xor X3 (its own inverse)
def sp.lt6(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, +x1, x2, +x3}:
      M.CmBlock{U32.xor(x0, U32.xor(x1, x3)), x1, x2, x3}

# X2 = X2 xor X3 xor (X1 << 7) (its own inverse)
def sp.lt7(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, +x1, x2, +x3}:
      M.CmBlock{x0, x1, U32.xor(x2, U32.xor(x3, U32.shln(x1, 7n))), x3}

def sp.lt8(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{L.lc.rotl5.bits(x0), x1, L.lc.rotl22.bits(x2), x3}

def sp.ilt1(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{L.lc.rotl19.bits(x0), x1, x2, x3}

def sp.ilt2(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{x0, x1, L.lc.rotl29.bits(x2), x3}

def sp.ilt5(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{x0, L.lc.rotl31.bits(x1), x2, L.lc.rotl25.bits(x3)}

def sp.ilt8(s: M.CmBlock) -> M.CmBlock:
  match s:
    case M.CmBlock{x0, x1, x2, x3}:
      M.CmBlock{L.lc.rotl27.bits(x0), x1, L.lc.rotl10.bits(x2), x3}

def sp.lt(s: M.CmBlock) -> M.CmBlock:
  sp.lt8(sp.lt7(sp.lt6(sp.lt5(sp.lt4(sp.lt3(sp.lt2(sp.lt1(s))))))))

def sp.ilt(s: M.CmBlock) -> M.CmBlock:
  sp.ilt1(sp.ilt2(sp.lt3(sp.lt4(sp.ilt5(sp.lt6(sp.lt7(sp.ilt8(s))))))))

# The steps of the cipher (internal)
type LcSpOp is Data:
  LcSpBswap{}
  LcSpKey{k: M.CmBlock}
  LcSpS{b: LcSpBox}
  LcSpLt{}

def sp.op(o: LcSpOp, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcSpBswap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          M.CmBlock{L.lc.bswap.bits(a), L.lc.bswap.bits(b), L.lc.bswap.bits(c), L.lc.bswap.bits(d)}
    case LcSpKey{k}:
      M.CmBlock.xor(s, k)
    case LcSpS{b}:
      sp.sop(b, False{}, s)
    case LcSpLt{}:
      sp.lt(s)

# the step undone
def sp.unop(o: LcSpOp, s: M.CmBlock) -> M.CmBlock:
  match o:
    case LcSpBswap{}:
      match s:
        case M.CmBlock{a, b, c, d}:
          M.CmBlock{L.lc.bswap.bits(a), L.lc.bswap.bits(b), L.lc.bswap.bits(c), L.lc.bswap.bits(d)}
    case LcSpKey{k}:
      M.CmBlock.xor(s, k)
    case LcSpS{b}:
      sp.sop(b, True{}, s)
    case LcSpLt{}:
      sp.ilt(s)

def sp.run(os: List<&2, LcSpOp>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      sp.run(t, sp.op(o, s))

def sp.unrun(os: List<&2, LcSpOp>, s: M.CmBlock) -> M.CmBlock:
  match os:
    case Nil{}:
      s
    case Con{o, t}:
      sp.unop(o, sp.unrun(t, s))

# The key schedule (section 2, "the key schedule")


# S-box n (n = 0 to 7)
def sp.box.go(n: Nat) -> LcSpBox:
  match n:
    case 0n:
      LcSp0{}
    case 1n:
      LcSp1{}
    case 2n:
      LcSp2{}
    case 3n:
      LcSp3{}
    case 4n:
      LcSp4{}
    case 5n:
      LcSp5{}
    case 6n:
      LcSp6{}
    case _:
      LcSp7{}

# the prekeys w_i = (w_(i-8) xor w_(i-5) xor w_(i-3) xor w_(i-1) xor phi xor
# i) <<< 11, for n more words from i; win holds w_(i-8) .. w_(i-1)
# S-box n mod 8
def sp.box(n: Nat) -> LcSpBox:
  sp.box.go(Nat.mod(n, 8n))

def sp.prekeys(n: Nat, +i: U32, win: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match win:
        case Con{a, Con{b, Con{c, Con{+d, Con{e, Con{+f, Con{g, Con{+h, t}}}}}}}}:
          +w = L.lc.rotl(U32.xor(U32.xor(U32.xor(a, d), U32.xor(f, h)), U32.xor(2654435769, i)), 11n)
          Con{w, sp.prekeys(p, U32.add(i, 1), [b, c, d, e, f, g, h, w])}
        case _:
          Nil{}

# round key K_i = S_((3 - i) mod 8)(w_(4i) .. w_(4i+3)), as an XOR step, for
# n more round keys from i
def sp.round_keys(n: Nat, +i: Nat, ws: List<&2, U32>) -> List<&2, M.CmBlock>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match ws:
        case Con{a, Con{b, Con{c, Con{d, t}}}}:
          Con{sp.sop(sp.box(Nat.sub(35n, i)), False{}, M.CmBlock{a, b, c, d}), sp.round_keys(p, Nat.add(i, 1n), t)}
        case _:
          Nil{}

# the steps of the 32 rounds from round i: K_i, S_(i mod 8), then LT (rounds
# 0 to 30) or K_32 (round 31)
def sp.rounds(ks: List<&2, M.CmBlock>, +i: Nat) -> List<&2, LcSpOp>:
  match ks:
    case Con{k, Con{k32, Nil{}}}:
      [LcSpKey{k}, LcSpS{sp.box(i)}, LcSpKey{k32}]
    case Con{k, t}:
      Con{LcSpKey{k}, Con{LcSpS{sp.box(i)}, Con{LcSpLt{}, sp.rounds(t, Nat.add(i, 1n))}}}
    case Nil{}:
      Nil{}

def sp.append(xs: List<&2, LcSpOp>, ys: List<&2, LcSpOp>) -> List<&2, LcSpOp>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, sp.append(t, ys)}

# A Serpent key: the steps of the cipher (opaque; built by LcSerpent.key)
type LcSerpentKey is Data:
  LcSerpentKey{ops: List<&2, LcSpOp>}

def sp.pad.pick(short: Bool, +xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  match short:
    case True{}:
      B.append(xs, Con{1, B.zeros(Nat.sub(31n, n))})
    case False{}:
      xs

# the key bytes padded to 256 bits: a 1 bit after the key, then zeros
def sp.pad(+xs: List<&2, U32>, +n: Nat) -> List<&2, U32>:
  sp.pad.pick(Nat.is_lt(n, 32n), xs, n)

def sp.le(+xs: List<&2, U32>, +i: Nat) -> U32:
  +j = Nat.mul(4n, i)
  L.lc.le(L.lc.at(xs, j), L.lc.at(xs, Nat.add(j, 1n)), L.lc.at(xs, Nat.add(j, 2n)), L.lc.at(xs, Nat.add(j, 3n)))

def sp.key(+xs: List<&2, U32>) -> LcSerpentKey:
  +k = sp.pad(xs, B.len(xs))
  +win = {[sp.le(k, 0n), sp.le(k, 1n), sp.le(k, 2n), sp.le(k, 3n), sp.le(k, 4n), sp.le(k, 5n), sp.le(k, 6n), sp.le(k, 7n)] : List<&2, U32>}
  LcSerpentKey{Con{LcSpBswap{}, sp.append(sp.rounds(sp.round_keys(33n, 0n, sp.prekeys(132n, 0, win)), 0n), [LcSpBswap{}])}}

def sp.key.pick(ok: Bool, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcSerpentKey>:
  match ok:
    case True{}:
      Done{sp.key(xs)}
    case False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# The cipher

# a key of 0 to 32 bytes (16, 24 and 32 are the usual sizes; a shorter key is
# padded as the specification says)
def LcSerpent.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcSerpentKey>:
  +xs = B.Octets.to_list(o)
  sp.key.pick(Nat.is_le(B.len(xs), 32n), xs)

def LcSerpent.encrypt(k: LcSerpentKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcSerpentKey{ops}:
      sp.run(ops, b)

def LcSerpent.decrypt(k: LcSerpentKey, b: M.CmBlock) -> M.CmBlock:
  match k:
    case LcSerpentKey{ops}:
      sp.unrun(ops, b)
