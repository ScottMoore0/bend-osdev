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
