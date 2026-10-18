# bend-osdev-ext2: block and inode bitmaps (Poirier, "Block Bitmap" and
# "Inode Bitmap"): bit k of a bitmap is bit k mod 8 of byte k div 8, and a
# set bit is a used block or inode. Every operation walks the bitmap's bytes
# once, as a tail call per byte.
import Base
import ../bytes/bytes.bend as B
import ./field.bend as F

# bit j (0 to 7) of byte b
def Ext2Bitmap.bit(+b: U32, j: Nat) -> Bool:
  Bool.not(U32.is_eq(U32.and(1, U32.shrn(b, j)), 0))

# byte b with bit j set (v) or cleared
def Ext2Bitmap.put(v: Bool, +b: U32, +j: Nat) -> U32:
  match v:
    case True{}:
      U32.or(U32.shln(1, j), b)
    case False{}:
      U32.and(U32.not(U32.shln(1, j)), b)

# whether bit k is set (bits past the end read as clear)
def Ext2Bitmap.test(+bm: B.Octets, +k: Nat) -> Bool:
  Ext2Bitmap.bit(F.Ext2Field.u8(bm, Nat.div(k, 8n)), Nat.mod(k, 8n))

# whether the first of ks falls in byte i
def Ext2Bitmap.here(ks: List<&2, Nat>, +i: Nat) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+k, t}:
      Nat.is_eq(Nat.div(k, 8n), i)

# byte i (b) with the leading bits of ks that fall in it set to v; the rest
# of ks
def Ext2Bitmap.apply(ks: List<&2, Nat>, here: Bool, +i: Nat, +b: U32, +v: Bool) -> U32 & List<&2, Nat>:
  match ks:
    case Nil{}:
      (b, Nil{})
    case Con{+k, +t}:
      match here:
        case False{}:
          (b, Con{k, t})
        case True{}:
          Ext2Bitmap.apply(t, Ext2Bitmap.here(t, i), i, Ext2Bitmap.put(v, b, Nat.mod(k, 8n)), v)

def Ext2Bitmap.with_byte(p: U32 & List<&2, Nat>, k: U32 -> List<&2, Nat> -> List<&2, U32>) -> List<&2, U32>:
  (a, b) = p
  k(a, b)

def Ext2Bitmap.update.go(xs: List<&2, U32>, ks: List<&2, Nat>, +i: Nat, +v: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match xs ks:
    case _ Nil{}:
      List.reverse.go(&2, U32, acc, xs)
    case Nil{} Con{k, t}:
      List.reverse(&2, U32, acc)
    case Con{b, t} Con{+k, kt}:
      Ext2Bitmap.with_byte(Ext2Bitmap.apply(Con{k, kt}, Nat.is_eq(Nat.div(k, 8n), i), i, b, v), b2 => rest => Ext2Bitmap.update.go(t, rest, Nat.add(i, 1n), v, Con{b2, acc}))

# the bitmap with every bit of ks (in ascending order; bits past the end are
# ignored) set to v, in one pass
def Ext2Bitmap.update(+bm: B.Octets, ks: List<&2, Nat>, +v: Bool) -> B.Octets:
  B.Octets.of_list(Ext2Bitmap.update.go(B.Octets.to_list(bm), ks, 0n, v, Nil{}))

def Ext2Bitmap.set(+bm: B.Octets, +k: Nat) -> B.Octets:
  Ext2Bitmap.update(bm, [k], True{})

def Ext2Bitmap.clear(+bm: B.Octets, +k: Nat) -> B.Octets:
  Ext2Bitmap.update(bm, [k], False{})

# Counting: the clear bits of a byte, and of the first n bits

def Ext2Bitmap.ones(+b: U32) -> Nat:
  +a = U32.add(U32.and(85, b), U32.and(85, U32.shrn(b, 1n)))
  +c = U32.add(U32.and(51, a), U32.and(51, U32.shrn(a, 2n)))
  U32.to_nat(U32.add(U32.and(15, c), U32.and(15, U32.shrn(c, 4n))))

# the clear bits among the low j bits of b
def Ext2Bitmap.zeros_low(j: Nat, +b: U32, acc: Nat) -> Nat:
  match j:
    case 0n:
      acc
    case 1n+(+p):
      Ext2Bitmap.zeros_low(p, b, Nat.add(acc, U32.to_nat(Bool.to_u32(Bool.not(Ext2Bitmap.bit(b, p))))))

def Ext2Bitmap.count.pick(full: Bool, +n: Nat, +b: U32, +acc: Nat) -> Nat & Nat:
  match full:
    case True{}:
      (Nat.sub(n, 8n), Nat.add(acc, Nat.sub(8n, Ext2Bitmap.ones(U32.and(255, b)))))
    case False{}:
      (0n, Ext2Bitmap.zeros_low(n, b, acc))

def Ext2Bitmap.with_count(p: Nat & Nat, k: Nat -> Nat -> Nat) -> Nat:
  (a, b) = p
  k(a, b)

def Ext2Bitmap.count.go(xs: List<&2, U32>, +n: Nat, acc: Nat) -> Nat:
  match xs n:
    case _ 0n:
      acc
    case Nil{} 1n+p:
      Nat.add(acc, 1n+p)
    case Con{+b, t} 1n+(+p):
      Ext2Bitmap.with_count(Ext2Bitmap.count.pick(Nat.is_le(8n, 1n+p), 1n+p, b, acc), rest => acc2 => Ext2Bitmap.count.go(t, rest, acc2))

# the clear bits among bits 0 to n - 1 (bits past the end count as clear)
def Ext2Bitmap.count_clear(+bm: B.Octets, +n: Nat) -> Nat:
  Ext2Bitmap.count.go(B.Octets.to_list(bm), n, 0n)

# The numbers from lo to hi - 1, ascending
def Ext2Bitmap.range.go(n: Nat, +hi: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +h = Nat.sub(hi, 1n)
      Ext2Bitmap.range.go(p, h, Con{h, acc})

def Ext2Bitmap.range(+lo: Nat, +hi: Nat) -> List<&2, Nat>:
  Ext2Bitmap.range.go(Nat.sub(hi, lo), hi, Nil{})

# Finding clear bits

# bit k taken if hit (clear and below the limit) and more are wanted
def Ext2Bitmap.find.bit(hit: Bool, +k: Nat, want: Nat, acc: List<&2, Nat>) -> Nat & List<&2, Nat>:
  match hit want:
    case True{} 1n+w:
      (w, Con{k, acc})
    case _ _:
      (want, acc)

def Ext2Bitmap.find.hit(+b: U32, +k: Nat, +limit: Nat) -> Bool:
  Bool.and(Nat.is_lt(k, limit), Bool.not(Ext2Bitmap.bit(b, Nat.mod(k, 8n))))

def Ext2Bitmap.with_found(p: Nat & List<&2, Nat>, k: Nat -> List<&2, Nat> -> Nat & List<&2, Nat>) -> Nat & List<&2, Nat>:
  (a, b) = p
  k(a, b)

def Ext2Bitmap.with_found_list(p: Nat & List<&2, Nat>, k: Nat -> List<&2, Nat> -> List<&2, Nat>) -> List<&2, Nat>:
  (a, b) = p
  k(a, b)

# the n bits of byte b from bit k on (hit: what bit k is)
def Ext2Bitmap.find.byte(n: Nat, hit: Bool, +b: U32, +k: Nat, +limit: Nat, +want: Nat, acc: List<&2, Nat>) -> Nat & List<&2, Nat>:
  match n:
    case 0n:
      (want, acc)
    case 1n+p:
      +k2 = Nat.add(k, 1n)
      Ext2Bitmap.with_found(Ext2Bitmap.find.bit(hit, k, want, acc), w2 => acc2 => Ext2Bitmap.find.byte(p, Ext2Bitmap.find.hit(b, k2, limit), b, k2, limit, w2, acc2))

# the bytes xs, the first holding bit k, while more are wanted below limit
def Ext2Bitmap.find.go(xs: List<&2, U32>, more: Bool, +k: Nat, +limit: Nat, +want: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs more:
    case _ False{}:
      List.reverse(&2, Nat, acc)
    case Nil{} True{}:
      List.reverse(&2, Nat, acc)
    case Con{+b, t} True{}:
      +j = Nat.mod(k, 8n)
      +k2 = Nat.add(Nat.sub(k, j), 8n)
      Ext2Bitmap.with_found_list(Ext2Bitmap.find.byte(Nat.sub(8n, j), Ext2Bitmap.find.hit(b, k, limit), b, k, limit, want, acc), +w2 => acc2 => Ext2Bitmap.find.go(t, Bool.and(Nat.is_lt(0n, w2), Nat.is_lt(k2, limit)), k2, limit, w2, acc2))

# up to want clear bits from bit `from` on, below limit (and within the
# bitmap), in ascending order
def Ext2Bitmap.find(+bm: B.Octets, +from: Nat, +limit: Nat, +want: Nat) -> List<&2, Nat>:
  Ext2Bitmap.find.go(B.Octets.to_list(B.Octets.drop(Nat.div(from, 8n), bm)), Bool.and(Nat.is_lt(0n, want), Nat.is_lt(from, limit)), from, limit, want, Nil{})

# Building: n bytes whose bits below used are set, bits from used to bits
# clear, and bits from bits on (padding past a group's end) set

def Ext2Bitmap.make.byte(j: Nat, +k: Nat, +used: Nat, +bits: Nat, acc: U32) -> U32:
  match j:
    case 0n:
      acc
    case 1n+(+p):
      +idx = Nat.add(k, p)
      Ext2Bitmap.make.byte(p, k, used, bits, Ext2Bitmap.put(Bool.or(Nat.is_lt(idx, used), Nat.is_le(bits, idx)), acc, p))

def Ext2Bitmap.make.go(n: Nat, +k: Nat, +used: Nat, +bits: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      Ext2Bitmap.make.go(p, Nat.add(k, 8n), used, bits, Con{Ext2Bitmap.make.byte(8n, k, used, bits, 0), acc})

def Ext2Bitmap.make(n: Nat, +used: Nat, +bits: Nat) -> B.Octets:
  B.Octets.of_list(Ext2Bitmap.make.go(n, 0n, used, bits, Nil{}))

def Ext2Bitmap.set_bits.keep(hit: Bool, +idx: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      Con{idx, acc}
    case False{}:
      acc

# The set bits among bits 0 to n - 1, ascending

def Ext2Bitmap.set_bits.byte(j: Nat, +b: U32, +k: Nat, +n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match j:
    case 0n:
      acc
    case 1n+(+p):
      +idx = Nat.add(k, Nat.sub(7n, p))
      Ext2Bitmap.set_bits.byte(p, b, k, n, Ext2Bitmap.set_bits.keep(Bool.and(Nat.is_lt(idx, n), Ext2Bitmap.bit(b, Nat.sub(7n, p))), idx, acc))

def Ext2Bitmap.set_bits.go(xs: List<&2, U32>, +k: Nat, +n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{+b, t}:
      Ext2Bitmap.set_bits.go(t, Nat.add(k, 8n), n, Ext2Bitmap.set_bits.byte(8n, b, k, n, acc))

def Ext2Bitmap.set_bits(+bm: B.Octets, +n: Nat) -> List<&2, Nat>:
  Ext2Bitmap.set_bits.go(B.Octets.to_list(B.Octets.take(Nat.div(Nat.add(n, 7n), 8n), bm)), 0n, n, Nil{})

# whether bytes a and b agree on their low k bits
def Ext2Bitmap.same.byte(+k: Nat, +a: U32, +b: U32) -> Bool:
  +m = U32.sub(U32.shln(1, k), 1)
  U32.is_eq(U32.and(m, a), U32.and(m, b))

def Ext2Bitmap.same.go(xs: List<&2, U32>, ys: List<&2, U32>, +n: Nat) -> Bool:
  match xs ys:
    case Con{+a, xt} Con{+b, yt}:
      Bool.and(Ext2Bitmap.same.byte(Nat.min(n, 8n), a, b), Bool.or(Nat.is_le(n, 8n), Ext2Bitmap.same.go(xt, yt, Nat.sub(n, 8n))))
    case _ _:
      Nat.is_eq(n, 0n)

# whether two bitmaps agree on bits 0 to n - 1
def Ext2Bitmap.same(+a: B.Octets, +b: B.Octets, +n: Nat) -> Bool:
  Ext2Bitmap.same.go(B.Octets.to_list(a), B.Octets.to_list(b), n)
