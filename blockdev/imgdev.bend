# ImgDev: an owned device (blockdev's owned interface) holding a disk image
# in an Array<U32>, four bytes to a slot, least significant byte first.
# Block n is the slots n * words to n * words + words - 1, where a block is
# `words` slots (4 * words bytes). An image is a single-owner value, so
# every operation hands it back; reads and writes cost O(words) array
# operations, each O(1) natively.
import Base
import ../bytes/bytes.bend as B
import ../array/array.bend as A
import ./blockdev.bend as D

type ImgDev is Type:
  ImgDev{words: Nat, count: Nat, depth: Nat, data: Array<U32>}

# Bytes and words: four bytes to a word, least significant first

def ImgDev.word(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  U32.or(U32.shln(U32.and(255, b3), 24n), U32.or(U32.shln(U32.and(255, b2), 16n), U32.or(U32.shln(U32.and(255, b1), 8n), U32.and(255, b0))))

# the four bytes of a word, onto acc
def ImgDev.unword(+x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  Con{U32.and(255, x), Con{U32.and(255, U32.shrn(x, 8n)), Con{U32.and(255, U32.shrn(x, 16n)), Con{U32.and(255, U32.shrn(x, 24n)), acc}}}}

# The depth of array that holds n slots: the smallest d (up to 31) with
# 2^d >= n
def ImgDev.depth_for.go(fuel: Nat, +n: Nat, +d: Nat, fits: Bool) -> Nat:
  match fuel fits:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+f False{}:
      ImgDev.depth_for.go(f, n, 1n+d, Nat.is_le(n, A.Arrays.slots(1n+d)))

def ImgDev.depth_for(+n: Nat) -> Nat:
  ImgDev.depth_for.go(31n, n, 0n, Nat.is_le(n, 1n))

# count zero blocks of `words` slots each, in an array of depth d
def ImgDev.blank.at(+d: Nat, words: Nat, count: Nat) -> ImgDev:
  ImgDev{words, count, d, Array.new(U32, d, 0)}

# count zero blocks of `words` slots (4 * words bytes) each
def ImgDev.blank(+words: Nat, +count: Nat) -> ImgDev:
  ImgDev.blank.at(ImgDev.depth_for(Nat.mul(count, words)), words, count)

# The owned interface

def ImgDev.block_size(img: ImgDev) -> ImgDev & Nat:
  match img:
    case ImgDev{+w, c, d, a}:
      (ImgDev{w, c, d, a}, Nat.mul(w, 4n))

def ImgDev.block_count(img: ImgDev) -> ImgDev & Nat:
  match img:
    case ImgDev{w, +c, d, a}:
      (ImgDev{w, c, d, a}, c)

def ImgDev.read.word(r: Array<U32> & U32, k: Array<U32> -> U32 -> Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, x) = r
  k(a, x)

def ImgDev.read.cons(+x: U32, r: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  (a, bs) = r
  (a, ImgDev.unword(x, bs))

# the bytes of k slots from slot s
def ImgDev.read.go(k: Nat, +s: Nat, a: Array<U32>) -> Array<U32> & List<&2, U32>:
  match k:
    case 0n:
      (a, Nil{})
    case 1n+p:
      ImgDev.read.word(Array.get(U32, a, U32.from_nat(s)), a2 => x => ImgDev.read.cons(x, ImgDev.read.go(p, Nat.add(s, 1n), a2)))

def ImgDev.read.fin(+w: Nat, +c: Nat, +d: Nat, r: Array<U32> & List<&2, U32>) -> ImgDev & Result<&2, &2, D.DevError, B.Octets>:
  (a, bs) = r
  (ImgDev{w, c, d, a}, Done{B.Octets.of_list(bs)})

def ImgDev.read.check(ok: Bool, +w: Nat, +c: Nat, +d: Nat, a: Array<U32>, +n: Nat) -> ImgDev & Result<&2, &2, D.DevError, B.Octets>:
  match ok:
    case True{}:
      ImgDev.read.fin(w, c, d, ImgDev.read.go(w, Nat.mul(n, w), a))
    case False{}:
      (ImgDev{w, c, d, a}, Fail{D.DevOutOfRange{n}})

def ImgDev.read_block.go(img: ImgDev, +n: Nat) -> ImgDev & Result<&2, &2, D.DevError, B.Octets>:
  match img:
    case ImgDev{+w, +c, +d, a}:
      ImgDev.read.check(Nat.is_lt(n, c), w, c, d, a, n)

# block n, and the image back
def ImgDev.read_block(img: ImgDev, n: Nat) -> ImgDev & Result<&2, &2, D.DevError, B.Octets>:
  ImgDev.read_block.go(img, n)

# the bytes xs written four to a slot from slot s
def ImgDev.write.go(xs: List<&2, U32>, +s: Nat, a: Array<U32>) -> Array<U32>:
  match xs:
    case Con{b0, Con{b1, Con{b2, Con{b3, t}}}}:
      ImgDev.write.go(t, Nat.add(s, 1n), Array.set(U32, a, U32.from_nat(s), ImgDev.word(b0, b1, b2, b3)))
    case _:
      a

def ImgDev.write.check(okl: Bool, okn: Bool, +w: Nat, +c: Nat, +d: Nat, a: Array<U32>, +n: Nat, data: B.Octets) -> ImgDev & Result<&2, &2, D.DevError, Unit>:
  match okl okn:
    case True{} True{}:
      (ImgDev{w, c, d, ImgDev.write.go(B.Octets.to_list(data), Nat.mul(n, w), a)}, Done{Unit{}})
    case False{} _:
      (ImgDev{w, c, d, a}, Fail{D.DevBadLength{Nat.mul(w, 4n), B.Octets.len(data)}})
    case True{} False{}:
      (ImgDev{w, c, d, a}, Fail{D.DevOutOfRange{n}})

def ImgDev.write_block.go(img: ImgDev, +n: Nat, +data: B.Octets) -> ImgDev & Result<&2, &2, D.DevError, Unit>:
  match img:
    case ImgDev{+w, +c, +d, a}:
      ImgDev.write.check(Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)), Nat.is_lt(n, c), w, c, d, a, n, data)

# block n replaced by data (exactly one block), or why not (the image then
# unchanged)
def ImgDev.write_block(img: ImgDev, n: Nat, data: B.Octets) -> ImgDev & Result<&2, &2, D.DevError, Unit>:
  ImgDev.write_block.go(img, n, data)

# Building an image from its blocks

def ImgDev.of_blocks.step(r: ImgDev & Result<&2, &2, D.DevError, Unit>) -> ImgDev:
  (img, res) = r
  img

def ImgDev.of_blocks.go(bs: List<&2, B.Octets>, +n: Nat, img: ImgDev) -> ImgDev:
  match bs:
    case Nil{}:
      img
    case Con{b, t}:
      ImgDev.of_blocks.go(t, 1n+n, ImgDev.of_blocks.step(ImgDev.write_block(img, n, b)))

# an image of `words` slots to a block holding the blocks bs in order (a
# block of the wrong length is left as zeros), in an array of depth d
def ImgDev.of_blocks.at(+d: Nat, +words: Nat, +bs: List<&2, B.Octets>) -> ImgDev:
  ImgDev.of_blocks.go(bs, 0n, ImgDev.blank.at(d, words, List.length(&2, B.Octets, bs)))

def ImgDev.of_blocks(+words: Nat, +bs: List<&2, B.Octets>) -> ImgDev:
  ImgDev.of_blocks.at(ImgDev.depth_for(Nat.mul(List.length(&2, B.Octets, bs), words)), words, bs)

# an image as a device of 4 * words byte blocks (a final partial block
# padded with zeros)
def ImgDev.of_octets(+words: Nat, +o: B.Octets) -> ImgDev:
  +bs = Nat.mul(words, 4n)
  +n = Nat.div(Nat.add(B.Octets.len(o), Nat.sub(bs, 1n)), bs)
  ImgDev.of_blocks(words, D.MemDev.blocks.rev_onto(D.MemDev.split.go(n, bs, o, Nil{}), Nil{}))

# The image as a pure device: every block read into a MemDev (a copy, for
# the read-only filesystems, which take the pure interface)

def ImgDev.freeze.got(r: ImgDev & Result<&2, &2, D.DevError, B.Octets>, k: ImgDev -> B.Octets -> List<&2, B.Octets>) -> List<&2, B.Octets>:
  (img, res) = r
  match res:
    case Done{o}:
      k(img, o)
    case Fail{e}:
      k(img, B.Octets.empty())

# blocks 0 to k - 1, onto acc
def ImgDev.freeze.go(k: Nat, img: ImgDev, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match k:
    case 0n:
      acc
    case 1n+ +p:
      ImgDev.freeze.got(ImgDev.read_block(img, p), i2 => o => ImgDev.freeze.go(p, i2, Con{o, acc}))

def ImgDev.freeze(img: ImgDev) -> D.MemDev:
  match img:
    case ImgDev{+w, +c, d, a}:
      D.MemDev{Nat.mul(w, 4n), c, D.MemTree.of_list(c, ImgDev.freeze.go(c, ImgDev{w, c, d, a}, Nil{}))}

# Specifications (for the laws; they look inside the array, so they do not
# run compiled)

# a well-formed image: a perfect array of depth d < 32 with room for every
# block (what blank.at and of_blocks.at build, and write_block keeps)
def ImgDev.valid(img: ImgDev) -> Bool:
  match img:
    case ImgDev{+w, +c, +d, a}:
      Bool.and(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)))

# whether every block of bs has n bytes
def ImgDev.all_len(bs: List<&2, B.Octets>, +n: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, t}:
      Bool.and(Nat.is_eq(B.Octets.len(b), n), ImgDev.all_len(t, n))
