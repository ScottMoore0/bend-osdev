# bend-osdev-fat, table.bend: the File Allocation Table. Reading and writing
# the entry of a cluster for each FAT type, what an entry means, and following
# a cluster chain with a bound.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# section 4 ("FAT Data Structure"): the entry of cluster n is at byte n * 4 of
# the FAT on FAT32 (its low 28 bits; the high 4 are reserved and kept when
# writing), n * 2 on FAT16, and n + n / 2 on FAT12, where it is 12 bits of the
# 16-bit word there: the low 12 bits when n is even, the high 12 when n is odd.
# A FAT12 entry may span two sectors. Entry values: 0 free; 0xFF7 / 0xFFF7 /
# 0x0FFFFFF7 a bad cluster; 0xFF8 / 0xFFF8 / 0x0FFFFFF8 and above the end of
# a chain; anything else the next cluster, which must be a cluster of the
# volume (2 to the count of clusters + 1).
#
# The FAT12 and FAT32 packing works on bits (slicing and joining words), so
# its laws hold for every value.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P

# Reading the device: len bytes at byte offset off, a device error wrapped

def FatIo.lift(r: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, E.FatError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{E.FatDev{e}}
    case Done{o}:
      Done{o}

def FatIo.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, off: Nat, +len: Nat) -> Result<&2, &2, E.FatError, B.Octets>:
  FatIo.lift(D.Dev.read_bytes(~Dv, ~block_size, ~read_block, d, off, len))

# FAT12 packing. The two bytes at offset n + n / 2 of the FAT hold the entry
# of cluster n: the low 8 bits of an even entry in the first byte and its high
# 4 in the low half of the second; the low 4 bits of an odd entry in the high
# half of the first byte and its high 8 in the second.

type Fat12Window is Data:
  Fat12Window{first: U32, second: U32}

def Fat12Window.first(w: Fat12Window) -> U32:
  match w:
    case Fat12Window{a, b}:
      a

def Fat12Window.second(w: Fat12Window) -> U32:
  match w:
    case Fat12Window{a, b}:
      b

def Fat12.bits8(b: U32) -> Word(8n):
  match b:
    case U32{w}:
      W.W64.bits.lo(8n, 24n, w)

def Fat12.byte(s: Word(8n)) -> U32:
  U32{W.W64.bits.cat(8n, 24n, s, Word.zero(24n))}

def Fat12.bits12(v: U32) -> Word(12n):
  match v:
    case U32{w}:
      W.W64.bits.lo(12n, 20n, w)

def Fat12.get.go(odd: Bool, +a: Word(8n), +b: Word(8n)) -> Word(12n):
  match odd:
    case False{}:
      W.W64.bits.cat(8n, 4n, a, W.W64.bits.lo(4n, 4n, b))
    case True{}:
      W.W64.bits.cat(4n, 8n, W.W64.bits.hi(4n, 4n, a), b)

# the entry the window holds: the even entry (odd = False) or the odd one
def Fat12.get(odd: Bool, w: Fat12Window) -> U32:
  match w:
    case Fat12Window{a, b}:
      U32{W.W64.bits.cat(12n, 20n, Fat12.get.go(odd, Fat12.bits8(a), Fat12.bits8(b)), Word.zero(20n))}

def Fat12.set.go(odd: Bool, +a: Word(8n), +b: Word(8n), +v: Word(12n)) -> Fat12Window:
  match odd:
    case False{}:
      Fat12Window{Fat12.byte(W.W64.bits.lo(8n, 4n, v)), Fat12.byte(W.W64.bits.cat(4n, 4n, W.W64.bits.hi(8n, 4n, v), W.W64.bits.hi(4n, 4n, b)))}
    case True{}:
      Fat12Window{Fat12.byte(W.W64.bits.cat(4n, 4n, W.W64.bits.lo(4n, 4n, a), W.W64.bits.lo(4n, 8n, v))), Fat12.byte(W.W64.bits.hi(4n, 8n, v))}

# the window with its even (odd = False) or odd entry replaced by the low 12
# bits of v, and the other entry's bits unchanged
def Fat12.set(odd: Bool, w: Fat12Window, v: U32) -> Fat12Window:
  match w:
    case Fat12Window{a, b}:
      Fat12.set.go(odd, Fat12.bits8(a), Fat12.bits8(b), Fat12.bits12(v))

# FAT32 packing: the low 28 bits are the entry; the high 4 are reserved

def Fat32.get(v: U32) -> U32:
  U32.and(268435455, v)

# the stored word old with its entry replaced by the low 28 bits of v, its
# reserved high 4 bits kept
def Fat32.set(old: U32, v: U32) -> U32:
  match old v:
    case U32{o} U32{x}:
      U32{W.W64.bits.cat(28n, 4n, W.W64.bits.lo(28n, 4n, x), W.W64.bits.hi(28n, 4n, o))}

# What an entry means

type FatEntry is Data:
  FatFree{}
  FatNext{cluster: U32}
  FatBad{}
  FatEnd{}

def FatEntry.bad(t: P.FatType) -> U32:
  match t:
    case P.Fat12{}:
      4087
    case P.Fat16{}:
      65527
    case P.Fat32{}:
      268435447

def FatEntry.of.pick(zero: Bool, bad: Bool, end: Bool, v: U32) -> FatEntry:
  match zero bad end:
    case True{} _ _:
      FatFree{}
    case False{} True{} _:
      FatBad{}
    case False{} False{} True{}:
      FatEnd{}
    case False{} False{} False{}:
      FatNext{v}

# the meaning of entry value v on a FAT of type t
def FatEntry.of(+t: P.FatType, +v: U32) -> FatEntry:
  +bad = FatEntry.bad(t)
  FatEntry.of.pick(U32.is_eq(v, 0), U32.is_eq(v, bad), U32.is_gt(v, bad), v)

# the value that marks the end of a chain (the one formatters write)
def FatEntry.end_value(t: P.FatType) -> U32:
  match t:
    case P.Fat12{}:
      4095
    case P.Fat16{}:
      65535
    case P.Fat32{}:
      268435455

# the value an entry is stored as
def FatEntry.value(+t: P.FatType, e: FatEntry) -> U32:
  match e:
    case FatFree{}:
      0
    case FatNext{c}:
      c
    case FatBad{}:
      FatEntry.bad(t)
    case FatEnd{}:
      FatEntry.end_value(t)

# The byte offset of cluster n's entry in a FAT, and its width

def FatTable.offset(t: P.FatType, +n: Nat) -> Nat:
  match t:
    case P.Fat12{}:
      Nat.add(n, Nat.div(n, 2n))
    case P.Fat16{}:
      Nat.mul(n, 2n)
    case P.Fat32{}:
      Nat.mul(n, 4n)

def FatTable.width(t: P.FatType) -> Nat:
  match t:
    case P.Fat32{}:
      4n
    case _:
      2n

def FatTable.odd(+n: Nat) -> Bool:
  Nat.is_eq(Nat.mod(n, 2n), 1n)

def FatTable.decode.fin(m: Maybe<&2, U32>) -> Result<&2, &2, E.FatError, U32>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{E.FatTooShort{}}

def FatTable.decode.w12(+odd: Bool, xs: List<&2, U32>) -> Maybe<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      Some{Fat12.get(odd, Fat12Window{a, b})}
    case _:
      None{}

# the entry of cluster n from the bytes at its offset
def FatTable.decode(t: P.FatType, +n: Nat, +xs: List<&2, U32>) -> Maybe<&2, U32>:
  match t:
    case P.Fat12{}:
      FatTable.decode.w12(FatTable.odd(n), xs)
    case P.Fat16{}:
      B.le16_at(xs, 0n)
    case P.Fat32{}:
      Maybe.map(&2, U32, U32, Fat32.get, B.le32_at(xs, 0n))

# the entry of cluster n in the volume's active FAT, read from the device
# (two or four bytes: only the blocks they are in)
def FatTable.get(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +n: U32) -> Result<&2, &2, E.FatError, U32>:
  +t = P.FatVolume.kind(vol)
  +k = U32.to_nat(n)
  do Result<&2, &2, E.FatError, U32>:
    o : B.Octets <- FatIo.read(~Dv, ~block_size, ~read_block, d, Nat.add(P.FatVolume.fat_start(vol), FatTable.offset(t, k)), FatTable.width(t))
    FatTable.decode.fin(FatTable.decode(t, k, B.Octets.to_list(o)))

# The FAT as bytes in memory (for building images): reading and writing the
# entry of cluster n. A write past the end leaves the bytes unchanged.

def FatTable.get_in(+t: P.FatType, fat: B.Octets, +n: U32) -> Maybe<&2, U32>:
  +k = U32.to_nat(n)
  FatTable.decode(t, k, B.Octets.to_list(B.Octets.slice(FatTable.offset(t, k), FatTable.width(t), fat)))

def FatTable.encode.win(w: Fat12Window) -> List<&2, U32>:
  match w:
    case Fat12Window{a, b}:
      [a, b]

def FatTable.encode.w12(+odd: Bool, xs: List<&2, U32>, +v: U32) -> List<&2, U32>:
  match xs:
    case Con{a, Con{b, t}}:
      FatTable.encode.win(Fat12.set(odd, Fat12Window{a, b}, v))
    case _:
      xs

def FatTable.encode.w32(m: Maybe<&2, U32>, +v: U32) -> List<&2, U32>:
  match m:
    case Some{old}:
      B.le32(Fat32.set(old, v))
    case None{}:
      Nil{}

# the bytes of cluster n's entry, xs, with the entry replaced by v
def FatTable.encode(t: P.FatType, +n: Nat, +xs: List<&2, U32>, +v: U32) -> List<&2, U32>:
  match t:
    case P.Fat12{}:
      FatTable.encode.w12(FatTable.odd(n), xs, v)
    case P.Fat16{}:
      B.le16(v)
    case P.Fat32{}:
      FatTable.encode.w32(B.le32_at(xs, 0n), v)

def FatTable.set_in.fits(ok: Bool, +t: P.FatType, +fat: B.Octets, +k: Nat, +v: U32) -> B.Octets:
  match ok:
    case True{}:
      +off = FatTable.offset(t, k)
      +w = FatTable.width(t)
      B.Octets.append(B.Octets.take(off, fat), B.Octets.append(B.Octets.of_list(FatTable.encode(t, k, B.Octets.to_list(B.Octets.slice(off, w, fat)), v)), B.Octets.drop(Nat.add(off, w), fat)))
    case False{}:
      fat

def FatTable.set_in(+t: P.FatType, +fat: B.Octets, +n: U32, +v: U32) -> B.Octets:
  +k = U32.to_nat(n)
  FatTable.set_in.fits(Nat.is_le(Nat.add(FatTable.offset(t, k), FatTable.width(t)), B.Octets.len(fat)), t, fat, k, v)

# Cluster chains

# where a chain goes after a cluster: it ends, or it continues at a cluster of
# the volume
type FatLink is Data:
  FatLinkEnd{}
  FatLinkNext{cluster: U32}

def FatChain.link.check(ok: Bool, +n: U32) -> Result<&2, &2, E.FatError, FatLink>:
  match ok:
    case True{}:
      Done{FatLinkNext{n}}
    case False{}:
      Fail{E.FatBadCluster{n}}

def FatChain.link(+vol: P.FatVolume, +c: U32, e: FatEntry) -> Result<&2, &2, E.FatError, FatLink>:
  match e:
    case FatFree{}:
      Fail{E.FatFreeInChain{c}}
    case FatBad{}:
      Fail{E.FatBadInChain{c}}
    case FatEnd{}:
      Done{FatLinkEnd{}}
    case FatNext{+n}:
      FatChain.link.check(P.FatVolume.valid_cluster(vol, n), n)

# where the chain goes after cluster c (its entry read from the device)
def FatChain.next(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +c: U32) -> Result<&2, &2, E.FatError, FatLink>:
  do Result<&2, &2, E.FatError, FatLink>:
    v : U32 <- FatTable.get(~Dv, ~block_size, ~read_block, d, vol, c)
    FatChain.link(vol, c, FatEntry.of(P.FatVolume.kind(vol), v))

def FatChain.cons(c: U32, r: Result<&2, &2, E.FatError, List<&2, U32>>) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{Con{c, cs}}

# The reference walk, structural: the chain from cluster c, whose link is
# l, in at most fuel clusters. It recurses once per cluster; FatChain.go
# below is the same as a loop (PROOF.bend proves the two equal for every
# input, and the chain bound is proved on this one).
def FatChain.go.ref(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, fuel: Nat, +c: U32, l: Result<&2, &2, E.FatError, FatLink>) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match fuel:
    case 0n:
      Fail{E.FatChainLoop{}}
    case 1n+p:
      match l:
        case Fail{e}:
          Fail{e}
        case Done{FatLinkEnd{}}:
          Done{[c]}
        case Done{FatLinkNext{+n}}:
          FatChain.cons(c, FatChain.go.ref(~Dv, ~block_size, ~read_block, d, vol, p, n, FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n)))

# xs reversed onto acc
def FatChain.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatChain.rev(t, Con{h, acc})

# the chain from cluster c, whose link is l, in at most fuel clusters, as a
# loop: acc holds the clusters before c, latest first
def FatChain.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, fuel: Nat, +c: U32, l: Result<&2, &2, E.FatError, FatLink>, acc: List<&2, U32>) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match fuel:
    case 0n:
      Fail{E.FatChainLoop{}}
    case 1n+p:
      match l:
        case Fail{e}:
          Fail{e}
        case Done{FatLinkEnd{}}:
          Done{FatChain.rev(Con{c, acc}, Nil{})}
        case Done{FatLinkNext{+n}}:
          FatChain.go(~Dv, ~block_size, ~read_block, d, vol, p, n, FatChain.next(~Dv, ~block_size, ~read_block, d, vol, n), Con{c, acc})

def FatChain.walk.from(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, empty: Bool, ok: Bool, +d: Dv, +vol: P.FatVolume, +start: U32) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match empty ok:
    case True{} _:
      Done{[]}
    case False{} False{}:
      Fail{E.FatBadCluster{start}}
    case False{} True{}:
      FatChain.go(~Dv, ~block_size, ~read_block, d, vol, U32.to_nat(P.FatVolume.clusters(vol)), start, FatChain.next(~Dv, ~block_size, ~read_block, d, vol, start), Nil{})

# the clusters of the chain that starts at start (none when start is 0, an
# empty file's first cluster). A chain longer than the volume's count of
# clusters must revisit a cluster, so it is refused (FatChainLoop): the
# chain never has more clusters than that.
def FatChain.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +vol: P.FatVolume, +start: U32) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  FatChain.walk.from(~Dv, ~block_size, ~read_block, U32.is_eq(start, 0), P.FatVolume.valid_cluster(vol, start), d, vol, start)
