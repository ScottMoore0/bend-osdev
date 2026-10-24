# What the pure helpers read, and what a write does to a device's image.
#
# On every pure device whose first n blocks each read as a whole block
# (Dev.uniform): Dev.read_bytes reads the bytes [off, off + len) of those
# blocks joined, for every range inside them; Dev.read_blocks is
# Dev.read_list's blocks joined.
#
# Patching an image (Dev.patch, what writing data at an offset does): the
# patched range reads back as the data, the bytes before and after it are
# unchanged, two adjacent patches are one, and patching with the bytes
# already there around the data is patching the data alone.
#
# MemDev, for every valid device (MemDev.valid: every block a whole block;
# of_octets, blank and update build only valid devices): a block, a run of
# blocks and a byte range read as the slices of to_octets(d) they name;
# a nonempty byte range that passes the end fails with the first block
# past the end it needs; a block update patches to_octets(d).
import Base
import ../bytes/bytes.bend as B
import ./blockdev.bend as D

# Every pure device

law read_bytes_image:
  for ~D: Data
  for ~block_size: D -> Nat
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for +d: D
  for +bp: Nat
  for +n: Nat
  for +off: Nat
  for +len: Nat
  for hbs: {block_size(d) == 1n+bp : Nat}
  for hu: {D.Dev.uniform(~D, ~block_size, ~read_block, d, n) == True{} : Bool}
  for hr: {Nat.is_le(Nat.add(off, len), Nat.mul(n, 1n+bp)) == True{} : Bool}
  {D.Dev.read_bytes(~D, ~block_size, ~read_block, d, off, len) == Result.map(&2, &2, D.DevError, B.Octets, B.Octets, o => B.Octets.slice(off, len, o), D.Dev.read_blocks(~D, ~read_block, d, n, 0n)) : Result<&2, &2, D.DevError, B.Octets>}

law read_blocks_list:
  for ~D: Data
  for ~read_block: D -> Nat -> Result<&2, &2, D.DevError, B.Octets>
  for +d: D
  for count: Nat
  for +first: Nat
  {D.Dev.read_blocks(~D, ~read_block, d, count, first) == Result.map(&2, &2, D.DevError, List<&2, B.Octets>, B.Octets, xs => B.Octets.concat(xs), D.Dev.read_list(~D, ~read_block, d, count, first)) : Result<&2, &2, D.DevError, B.Octets>}

# Patching an image

law patch_len:
  for +off: Nat
  for +data: B.Octets
  for +o: B.Octets
  for h: {Nat.is_le(Nat.add(off, B.Octets.len(data)), B.Octets.len(o)) == True{} : Bool}
  {B.Octets.len(D.Dev.patch(off, data, o)) == B.Octets.len(o) : Nat}

law patch_slice:
  for +off: Nat
  for +data: B.Octets
  for +o: B.Octets
  for h: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}
  {B.Octets.slice(off, B.Octets.len(data), D.Dev.patch(off, data, o)) == data : B.Octets}

law patch_before:
  for +i: Nat
  for +n: Nat
  for +off: Nat
  for +data: B.Octets
  for +o: B.Octets
  for h: {Nat.is_le(Nat.add(i, n), off) == True{} : Bool}
  for ho: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}
  {B.Octets.slice(i, n, D.Dev.patch(off, data, o)) == B.Octets.slice(i, n, o) : B.Octets}

law patch_after:
  for +i: Nat
  for +n: Nat
  for +off: Nat
  for +data: B.Octets
  for +o: B.Octets
  for h: {Nat.is_le(Nat.add(off, B.Octets.len(data)), i) == True{} : Bool}
  for ho: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}
  {B.Octets.slice(i, n, D.Dev.patch(off, data, o)) == B.Octets.slice(i, n, o) : B.Octets}

law patch_patch:
  for +off: Nat
  for +a: B.Octets
  for +b: B.Octets
  for +o: B.Octets
  for h: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}
  {D.Dev.patch(Nat.add(off, B.Octets.len(a)), b, D.Dev.patch(off, a, o)) == D.Dev.patch(off, B.Octets.append(a, b), o) : B.Octets}

# patching with the i bytes before data and the j after it as they are is
# patching data alone (a read-modify-write of whole blocks)
law patch_keep:
  for +a: Nat
  for +i: Nat
  for +data: B.Octets
  for +j: Nat
  for +o: B.Octets
  for h: {Nat.is_le(Nat.add(Nat.add(Nat.add(a, i), B.Octets.len(data)), j), B.Octets.len(o)) == True{} : Bool}
  {D.Dev.patch(a, B.Octets.append(B.Octets.slice(a, i, o), B.Octets.append(data, B.Octets.slice(Nat.add(Nat.add(a, i), B.Octets.len(data)), j, o))), o) == D.Dev.patch(Nat.add(a, i), data, o) : B.Octets}

# MemDev

law read_block_out:
  for +d: D.MemDev
  for +n: Nat
  for h: {Nat.is_lt(n, D.MemDev.block_count(d)) == False{} : Bool}
  {D.MemDev.read_block(d, n) == Fail{D.DevOutOfRange{n}} : Result<&2, &2, D.DevError, B.Octets>}

law valid_blank:
  for +bs: Nat
  for +count: Nat
  {D.MemDev.valid(D.MemDev.blank(bs, count)) == True{} : Bool}

law valid_of_octets:
  for +bs: Nat
  for +o: B.Octets
  {D.MemDev.valid(D.MemDev.of_octets(bs, o)) == True{} : Bool}

law valid_update:
  for +d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  {D.MemDev.valid(D.MemDev.update(d, n, data)) == True{} : Bool}

law to_octets_len:
  for +d: D.MemDev
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  {B.Octets.len(D.MemDev.to_octets(d)) == Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d)) : Nat}

law to_octets_update:
  for +d: D.MemDev
  for +n: Nat
  for +data: B.Octets
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}
  for in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}
  {D.MemDev.to_octets(D.MemDev.update(d, n, data)) == D.Dev.patch(Nat.mul(n, D.MemDev.block_size(d)), data, D.MemDev.to_octets(d)) : B.Octets}

law read_block_mem:
  for +d: D.MemDev
  for +n: Nat
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}
  {D.MemDev.read_block(d, n) == Done{B.Octets.slice(Nat.mul(n, D.MemDev.block_size(d)), D.MemDev.block_size(d), D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}

law read_blocks_mem:
  for +d: D.MemDev
  for +count: Nat
  for +first: Nat
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for h: {Nat.is_le(Nat.add(first, count), D.MemDev.block_count(d)) == True{} : Bool}
  {D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first) == Done{B.Octets.slice(Nat.mul(first, D.MemDev.block_size(d)), Nat.mul(count, D.MemDev.block_size(d)), D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}

law read_bytes_mem:
  for +d: D.MemDev
  for +off: Nat
  for +len: Nat
  for hv: {D.MemDev.valid(d) == True{} : Bool}
  for h: {Nat.is_le(Nat.add(off, len), Nat.mul(D.MemDev.block_count(d), D.MemDev.block_size(d))) == True{} : Bool}
  {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, off, len) == Done{B.Octets.slice(off, len, D.MemDev.to_octets(d))} : Result<&2, &2, D.DevError, B.Octets>}

law read_bytes_past_end:
  for +d: D.MemDev
  for +bp: Nat
  for +off: Nat
  for +lp: Nat
  for hbs: {D.MemDev.block_size(d) == 1n+bp : Nat}
  for h: {Nat.is_lt(Nat.mul(D.MemDev.block_count(d), 1n+bp), Nat.add(off, 1n+lp)) == True{} : Bool}
  {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, off, 1n+lp) == Fail{D.DevOutOfRange{Nat.max(Nat.div(off, 1n+bp), D.MemDev.block_count(d))}} : Result<&2, &2, D.DevError, B.Octets>}

# Vectors: the 3-block device of LAWS.bend is valid; a patch

law vector_valid:
  {D.MemDev.valid(D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij"))) == True{} : Bool}

law vector_patch:
  {B.Octets.to_string(D.Dev.patch(3n, B.Octets.of_string("XYZ"), B.Octets.of_string("abcdefgh"))) == "abcXYZgh" : String}

law vector_read_bytes_mem:
  {D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev.of_octets(4n, B.Octets.of_string("abcdefghij")), 11n, 2n) == Fail{D.DevOutOfRange{3n}} : Result<&2, &2, D.DevError, B.Octets>}
