# DRAFT: not yet reviewed by the maintainer
#
# Properties of the in-memory device, for every device, block index and
# block: reading a block back after writing it gives what was written; a
# write changes no other block; a write keeps the block size and count.
# Vectors: the generic helpers (read_blocks, read_bytes) on small devices,
# including reads that span blocks and reads past the end.
import Base
import ../bytes/bytes.bend as B
import ./blockdev.bend as D
import ./imgdev.bend as I
import ../array/array.bend as A

law read_after_update:
  for d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  for len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}
  for in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}
  {D.MemDev.read_block(D.MemDev.update(d, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}

law update_other:
  for d: D.MemDev
  for +n: Nat
  for +m: Nat
  for +data: B.Octets
  for diff: {Nat.is_eq(m, n) == False{} : Bool}
  {D.MemDev.read_block(D.MemDev.update(d, n, data), m) == D.MemDev.read_block(d, m) : Result<&2, &2, D.DevError, B.Octets>}

law update_keeps_size:
  for d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  {D.MemDev.block_size(D.MemDev.update(d, n, data)) == D.MemDev.block_size(d) : Nat}

law update_keeps_count:
  for d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  {D.MemDev.block_count(D.MemDev.update(d, n, data)) == D.MemDev.block_count(d) : Nat}

# Vectors: a 3-block device of 4-byte blocks holding "abcdefghij" (padded)

def dev() -> D.MemDev:
  D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij"))

def text(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      "error"

law vector_count:
  {D.MemDev.block_count(dev()) == 3n : Nat}

law vector_block:
  {text(D.MemDev.read_block(dev(), 1n)) == "efgh" : String}

law vector_out_of_range:
  {D.MemDev.read_block(dev(), 3n) == Fail{D.DevOutOfRange{3n}} : Result<&2, &2, D.DevError, B.Octets>}

law vector_span:
  {text(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dev(), 2n, 7n)) == "cdefghi" : String}

law vector_span_past_end:
  {text(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, dev(), 10n, 4n)) == "error" : String}

law vector_write:
  {text(Result.bind(&2, &2, D.DevError, D.MemDev, B.Octets, D.MemDev.write_block(dev(), 2n, B.Octets.of_string("WXYZ")), x => D.MemDev.read_block(x, 2n))) == "WXYZ" : String}

law vector_write_bad_length:
  {Result.is_fail(&2, &2, D.DevError, D.MemDev, D.MemDev.write_block(dev(), 0n, B.Octets.of_string("xyz"))) == True{} : Bool}

law vector_blank:
  {text(D.MemDev.read_block(D.MemDev.update(D.MemDev.blank(2n, 5n), 3n, B.Octets.of_string("ab")), 1n)) == text(Done{B.Octets.zeros(2n)}) : String}

# The owned interface on an adapted pure device: the owned helpers hand the
# device back unchanged and answer what the pure helpers answer, for every
# device and range (so existing code and laws carry over to the owned
# interface)

law own_read_blocks:
  for d: D.MemDev
  for count: Nat
  for first: Nat
  {D.ODev.read_blocks(~D.MemDev, ~D.MemDev.own_read_block, count, d, first) == (d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first)) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}

law own_read_bytes:
  for d: D.MemDev
  for off: Nat
  for +len: Nat
  {D.ODev.read_bytes(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, d, off, len) == (d, D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, off, len)) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}

law own_write_ok:
  for +d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  for len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}
  for in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}
  {D.MemDev.own_write_block(d, n, data) == (D.MemDev.update(d, n, data), Done{Unit{}}) : D.MemDev & Result<&2, &2, D.DevError, Unit>}

def own_text(r: D.MemDev & Result<&2, &2, D.DevError, B.Octets>) -> String:
  (d, x) = r
  text(x)

law vector_own_span:
  {own_text(D.ODev.read_bytes(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, dev(), 2n, 7n)) == "cdefghi" : String}

# ImgDev (imgdev.bend): an owned device held in an Array<U32>. For every
# valid image (one built by blank.at or of_blocks.at, then written), block
# number and block:

law img_read_write:
  for img: I.ImgDev
  for h: {I.ImgDev.valid(img) == True{} : Bool}
  for +n: Nat
  for +data: B.Octets
  for len_ok: {Nat.is_eq(B.Octets.len(data), Pair.snd(I.ImgDev, Nat, I.ImgDev.block_size(img))) == True{} : Bool}
  for in_range: {Nat.is_lt(n, Pair.snd(I.ImgDev, Nat, I.ImgDev.block_count(img))) == True{} : Bool}
  {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(img, n, data)), n)) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}

law img_write_other:
  for img: I.ImgDev
  for h: {I.ImgDev.valid(img) == True{} : Bool}
  for +n: Nat
  for +m: Nat
  for +data: B.Octets
  for len_ok: {Nat.is_eq(B.Octets.len(data), Pair.snd(I.ImgDev, Nat, I.ImgDev.block_size(img))) == True{} : Bool}
  for in_range: {Nat.is_lt(n, Pair.snd(I.ImgDev, Nat, I.ImgDev.block_count(img))) == True{} : Bool}
  for diff: {Nat.is_eq(m, n) == False{} : Bool}
  {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(img, n, data)), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(img, m)) : Result<&2, &2, D.DevError, B.Octets>}

law img_write_valid:
  for img: I.ImgDev
  for h: {I.ImgDev.valid(img) == True{} : Bool}
  for +n: Nat
  for +data: B.Octets
  {I.ImgDev.valid(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(img, n, data))) == True{} : Bool}

law img_read_same:
  for img: I.ImgDev
  for h: {I.ImgDev.valid(img) == True{} : Bool}
  for +n: Nat
  {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(img, n)) == img : I.ImgDev}

law img_blank_valid:
  for +d: Nat
  for +w: Nat
  for +c: Nat
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}
  {I.ImgDev.valid(I.ImgDev.blank.at(d, w, c)) == True{} : Bool}

# reading back what an image was built from gives that image
law img_of_blocks:
  for +d: Nat
  for +w: Nat
  for +bs: List<&2, B.Octets>
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.mul(List.length(&2, B.Octets, bs), w), A.Arrays.slots(d)) == True{} : Bool}
  for +hal: {I.ImgDev.all_len(bs, Nat.mul(w, 4n)) == True{} : Bool}
  for +n: Nat
  for +hn: {Nat.is_lt(n, List.length(&2, B.Octets, bs)) == True{} : Bool}
  {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev.of_blocks.at(d, w, bs), n)) == Done{A.Arrays.nth(B.Octets, bs, n, B.Octets.empty())} : Result<&2, &2, D.DevError, B.Octets>}

# Witnesses and vectors: three blocks of four bytes in a depth-2 array

def img_blocks() -> List<&2, B.Octets>:
  [B.Octets.of_string("abcd"), B.Octets.of_string("efgh"), B.Octets.of_string("ijkl")]

law img_witness:
  {Bool.and(Nat.is_lt(2n, 32n), Bool.and(Nat.is_le(Nat.mul(List.length(&2, B.Octets, img_blocks()), 1n), A.Arrays.slots(2n)), I.ImgDev.all_len(img_blocks(), Nat.mul(1n, 4n)))) == True{} : Bool}

def img_text(r: I.ImgDev & Result<&2, &2, D.DevError, B.Octets>) -> String:
  (img, x) = r
  text(x)

law img_vector_built:
  {img_text(I.ImgDev.read_block(I.ImgDev.of_blocks.at(2n, 1n, img_blocks()), 2n)) == "ijkl" : String}

law img_vector_write:
  {img_text(I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev.of_blocks.at(2n, 1n, img_blocks()), 0n, B.Octets.of_string("WXYZ"))), 0n)) == "WXYZ" : String}

law img_vector_octets:
  {img_text(I.ImgDev.read_block(I.ImgDev.of_octets(1n, B.Octets.of_string("abcdefghij")), 2n)) == text(Done{B.Octets.of_list([105, 106, 0, 0])}) : String}

law img_vector_out_of_range:
  {img_text(I.ImgDev.read_block(I.ImgDev.blank(1n, 3n), 3n)) == "error" : String}
