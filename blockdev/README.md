# bend-osdev-blockdev

The block-device interface that bend-osdev's filesystems read through, generic
helpers built on it, and an in-memory device.

## The interface

A device is a value `d` of some `Data` type `D`, with two operations:

| Operation | Type | Meaning |
|---|---|---|
| `block_size` | `D -> Nat` | bytes per block |
| `read_block` | `D -> Nat -> Result<&2, &2, DevError, Octets>` | block `n`, exactly `block_size(d)` bytes |

A filesystem takes `~D`, `~block_size` and `~read_block` as **template
arguments**, so it is specialised to its device at compile time: the interface
costs nothing at run time, and the filesystem works on any device that
provides the two operations. Errors are `DevError`: `DevOutOfRange{block}`,
`DevBadLength{expected, got}`, `DevFailed{code}`.

## Files and API

`blockdev.bend` holds everything (one concern: devices).

| Def | Meaning |
|---|---|
| `Dev.read_blocks(~D, ~read_block, d, count, first)` | `count` blocks from block `first`, joined |
| `Dev.read_bytes(~D, ~block_size, ~read_block, d, off, len)` | `len` bytes from byte offset `off`, across block boundaries; a zero-length read always succeeds |
| `MemDev.of_octets(bs, o)` | an image as a device of `bs`-byte blocks (a final partial block is padded with zeros) |
| `MemDev.blank(bs, count)` | `count` zero blocks |
| `MemDev.block_size`, `MemDev.read_block` | the interface, for `MemDev` |
| `MemDev.block_count`, `MemDev.to_octets` | the device's size, and its whole image |
| `MemDev.write_block(d, n, data)` | block `n` replaced, or why not (`Result`) |
| `MemDev.update(d, n, data)` | the same, total: the device unchanged on a bad write |

`MemDev`'s representation (a list of blocks) is internal. Its block lists
are built, counted and updated by tail calls, so a device may have any number
of blocks (a 2 MB image of 131,072 blocks of 16 bytes builds, updates, reads
and joins back in about 4 s); the proofs reason about the structural
`MemDev.set.ref` and tie it to the running `MemDev.set` by a lemma. Reading
block `n` walks `n` list cells, and a write rebuilds the list up to `n`.

## Extension points

* **Any device:** a file, a partition of another device, a driver, a cache, a
  device that counts reads: provide `block_size` and `read_block` for its type
  and pass them as template arguments. Nothing in a filesystem changes.
* **Partitions:** a device wrapping another device with an offset and a length
  is a natural next package (it needs only the two operations of the device it
  wraps).
* **Writing:** `MemDev` has writes; a write operation for the interface itself
  (for filesystems that write) can be added the same way, as a third template
  argument.
* **Faster random access:** a `MemDev` backed by a tree (xarray, or a trie
  on the block number) would make reads and writes logarithmic in the block
  count, behind the same interface and laws.
* **Effects:** this interface is pure. A device backed by a real file needs
  an `IO` version of `read_block`; that belongs in its own package.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every device, block index and block:** reading a block back after
  writing it gives what was written (when the block exists and has the right
  length); a write changes no other block; a write keeps the block size and
  block count;
* **vectors:** block counts, reads in and out of range, `read_bytes` across
  block boundaries and past the end, and `write_block` with good and bad
  lengths.

`Dev.read_bytes` is covered by vectors and the differential test, not yet by a
law for every input.

## Tests

`ref/run.sh` compares `Dev.read_bytes` on `MemDev` with a model written from
this README's description, on 60 random images, block sizes and ranges.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 60 cases match, `scripts/deps.sh` passes.
