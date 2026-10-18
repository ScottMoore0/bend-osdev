# bend-osdev-blockdev

The block-device interfaces that bend-osdev's filesystems read (and later
write) through, generic helpers built on them, an in-memory device
(`MemDev`), and a disk image held in an `Array<U32>` (`ImgDev`), with laws
proved for every input.

## The interfaces

A filesystem takes its device as **template arguments**, so it is
specialised to the device at compile time: the interface costs nothing at
run time, and any device that provides the operations works.

**The pure interface** (unchanged): a device is a value `d` of a `Data` type
`D`, read as often as one likes.

| Operation | Type | Meaning |
|---|---|---|
| `block_size` | `D -> Nat` | bytes per block |
| `read_block` | `D -> Nat -> Result<&2, &2, DevError, Octets>` | block `n`, exactly `block_size(d)` bytes |

**The owned interface** (new): every operation hands the device back, so `D`
may be a single-owner `Type`: an `Array`, or (later) a file handle.

| Operation | Type | Meaning |
|---|---|---|
| `block_size` | `D -> D & Nat` | bytes per block |
| `read_block` | `D -> Nat -> D & Result<&2, &2, DevError, Octets>` | block `n` |
| `write_block` | `D -> Nat -> Octets -> D & Result<&2, &2, DevError, Unit>` | block `n` replaced by exactly one block of data, or why not (the device then unchanged) |

**The adapter:** every pure device is an owned device. `Dev.own_block_size`,
`Dev.own_read_block` and `Dev.own_write_block` (from a pure write
`D -> Nat -> Octets -> Result<&2, &2, DevError, D>`) hand back the device
itself; the laws `own_read_blocks` and `own_read_bytes` prove that the owned
helpers on an adapted `MemDev` answer exactly what the pure helpers answer,
for every device and range. So a component written against the owned
interface runs on every pure device, and one written against the pure
interface keeps its code and laws.

Errors are `DevError`: `DevOutOfRange{block}`, `DevBadLength{expected, got}`,
`DevFailed{code}`.

### The filesystems' readers stay on the pure interface

The readers of fat, iso9660 and ext2 take the pure interface. fat's writer
(`fat/write.bend`) uses the owned interface, with `~write_block`, and reads
back through the same owned device. The readers are left on the pure
interface, unchanged, for these reasons:

* every one of their laws that mentions a device (fat's `chain_bound`,
  iso9660's `dir_records_fenced` and `stream_*` laws, ext2's `map_*`,
  `extent_depth_bound` and `next_at_end`, and their `MemDev` vectors) is a
  statement about a pure read's `Result`. On the owned interface every read
  answers a pair, so each of these statements would change (a breaking
  change to the laws under CONVENTIONS.md), and each proof would have to be
  redone through pairs without an eta rule;
* their reference tests (fat 956 cases, iso9660 48 images, ext2 2949 cases)
  read through `MemDev` and keep passing unchanged;
* the pure interface is the owned interface's special case for `Data`
  devices (the adapter above, with its laws), so nothing is lost: a
  read-only filesystem never needs the device back, and a pure device can
  be shared by many readers.

A filesystem can read an `ImgDev` today through `ImgDev.freeze` (a copy into
a `MemDev`). Writing filesystems, and devices that must stay single-owner
(an `Array`, a file), are what the owned interface is for: a writing FAT or
ext2 would take `~write_block` as a fourth template argument.

## Files and API

| File | Holds |
|---|---|
| `blockdev.bend` | `DevError`; the pure helpers; the adapters; the owned helpers; `MemDev` |
| `imgdev.bend` | `ImgDev`, the array image device |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs (`PROOF.bend` holds every lemma: `BP.` for `MemDev` and the adapters, `IP.` for `ImgDev`) |
| `check.bend` | a runnable check of every device and helper |
| `ref/gen.py`, `ref/run.sh` | the differential test (`gen.py` writes `ref/cases.bend` and `ref/expected.txt`, which `ref/.gitignore` lists) |

### blockdev.bend

| Def | Meaning |
|---|---|
| `Dev.read_blocks(~D, ~read_block, d, count, first)` | pure: `count` blocks from block `first`, joined |
| `Dev.read_bytes(~D, ~block_size, ~read_block, d, off, len)` | pure: `len` bytes from byte offset `off`, across block boundaries; a zero-length read always succeeds |
| `Dev.own_block_size(~D, ~block_size, d)`, `Dev.own_read_block(~D, ~read_block, d, n)`, `Dev.own_write_block(~D, ~write_block, d, n, data)` | the adapters: a pure device's operations on the owned interface |
| `ODev.read_blocks(~D, ~read_block, count, d, first)` | owned: the same, the device handed back however the reads end |
| `ODev.read_bytes(~D, ~block_size, ~read_block, d, off, len)` | owned: the same |
| `MemDev.of_octets(bs, o)` | an image as a pure device of `bs`-byte blocks (a final partial block padded with zeros) |
| `MemDev.blank(bs, count)` | `count` zero blocks (O(1): a block never written reads as zeros) |
| `MemDev.block_size`, `MemDev.read_block` | the pure interface, for `MemDev` |
| `MemDev.block_count`, `MemDev.to_octets` | the device's size, and its whole image |
| `MemDev.write_block(d, n, data)` | block `n` replaced, or why not (`Result`) |
| `MemDev.update(d, n, data)` | the same, total: the device unchanged on a bad write |
| `MemDev.own_block_size`, `MemDev.own_read_block`, `MemDev.own_write_block` | `MemDev` on the owned interface |

`MemDev`'s representation is internal: a tree split by block number (a node
holds how many block numbers lie to its left), built balanced by
`of_octets`, so a read or write walks one path, O(log n), where the old list
of blocks walked `n` cells. Writing a block past the tree's reach adds a
node, so the laws hold for every value of the type.

### imgdev.bend

An `ImgDev` holds an image in an `Array<U32>`, four bytes to a slot, least
significant byte first; block `n` is the slots `n * words` to
`n * words + words - 1` (`words` slots, `4 * words` bytes, to a block). A
read or write costs `words` array operations, each O(1) natively.

| Def | Meaning |
|---|---|
| `ImgDev.blank(words, count)`, `ImgDev.blank.at(d, words, count)` | `count` zero blocks (in an array of depth `d`, or the smallest that holds them) |
| `ImgDev.of_blocks(words, bs)`, `ImgDev.of_blocks.at(d, words, bs)` | an image holding the blocks `bs` in order (a block of the wrong length is left as zeros) |
| `ImgDev.of_octets(words, o)` | an image of `o`, cut into `4 * words`-byte blocks, the last padded |
| `ImgDev.block_size`, `ImgDev.block_count`, `ImgDev.read_block`, `ImgDev.write_block` | the owned interface |
| `ImgDev.freeze(img)` | the image copied into a `MemDev` (for the pure-interface filesystems) |
| `ImgDev.word(b0, b1, b2, b3)`, `ImgDev.unword(x, acc)` | four bytes as a slot, and back |
| `ImgDev.valid(img)`, `ImgDev.all_len(bs, n)` | specifications for the laws (they look inside the array, so they do not run compiled) |

`ImgDev`'s fields are internal; `ImgDev.valid` states what the defs keep: a
perfect array of depth below 32 with room for every block.

## Extension points

* **Any device:** a file, a partition, a driver, a cache, a device that
  counts reads: provide the operations of either interface for its type and
  pass them as template arguments. A pure device can always be used where
  the owned interface is expected, through the adapters.
* **Single-owner devices:** an `Array` (`ImgDev`) today; a file-backed device
  needs its operations in `IO`, which a template over a pure function type
  cannot express yet. Its shape is the owned interface's (an `IO` handle is
  handed back the same way), so an `IO` twin of `ODev.read_bytes` is a
  mechanical next step, in its own package.
* **Writing filesystems:** `write_block` is part of the owned interface;
  `ODev` helpers for writing ranges can be added beside the reading ones.
* **Partitions:** a device wrapping another with an offset and a length is a
  natural next package (iso9660's `IsoFence` is one, for reads).
* **`MemDev`'s tree and `ImgDev`'s layout** are internal and can change
  behind the same laws.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

**`MemDev`, for every device, block number and block:** reading a block back
after writing it gives what was written, when the block exists and has the
right length (`read_after_update`); a write changes no other block
(`update_other`); a write keeps the block size and count. The statements are
unchanged from the list representation.

**The adapter, for every device and range:** `ODev.read_blocks` and
`ODev.read_bytes` on an adapted `MemDev` hand back the device and answer
what `Dev.read_blocks` and `Dev.read_bytes` answer (`own_read_blocks`,
`own_read_bytes`); a good owned write is the pure `update`
(`own_write_ok`).

**`ImgDev`, for every valid image, block number and block** (proved through
bend-osdev-array's laws: the image's array is reflected once into
`Arrays.of_list(d, L, 0)` and every read and write is followed on the list
`L`):

* `img_read_write`: reading a block after writing it gives what was written;
* `img_write_other`: writing one block leaves every other block's read
  unchanged (including reads past the end);
* `img_write_valid`, `img_read_same`: a write keeps an image valid, and a
  read hands back the same image;
* `img_blank_valid`: `blank.at(d, w, c)` is valid when `d < 32` and
  `c * w <= 2^d`;
* `img_of_blocks`: reading back what an image was built from gives that
  image: block `n` of `of_blocks.at(d, w, bs)` is the `n`-th of `bs`, for
  blocks of `4 * w` bytes.

The byte packing is proved by computation on symbolic bits: a slot's four
bytes are the four bytes packed into it, each masked to 8 bits
(`IP.unword_word`, with the 32 bits of each byte as pattern variables), and
then bytes' laws (`octets_to_of`, `octets_of_list_idempotent`,
`octets_of_to`, `octets_len_list`) give back the block.

**Witnesses and vectors:** three blocks of four bytes in a depth-2 array
(the hypotheses of `img_of_blocks` hold together); a built image, a write,
`of_octets` padding, a read past the end; `MemDev`'s earlier vectors, a
blank `MemDev`, and an owned read across blocks.

`Dev.read_bytes` itself is covered by vectors and the differential test, not
by a law for every input.

## Tests

`ref/run.sh` compares, against a model written here from this README's
description (it shares an author with the package): `Dev.read_bytes` on
`MemDev` (60 random images, block sizes and ranges), `ODev.read_bytes` on
`ImgDev` (40), and random sequences of `ImgDev.write_block` with good and
bad lengths and block numbers, each followed by the whole image read back
(40). The cases run as one native program.

## Sizes and speed

Measured natively (Bend 2.0.37, WSL2), not in CI:

| Run | Time | Peak RAM |
|---|---|---|
| a 64 MB `ImgDev` (16384 blocks of 4 KB): built block by block from generated data, then every block read back and compared | 17.0 s | 66.9 MB |
| a 2 MB `MemDev` of 131072 16-byte blocks: built, one block updated, every block read one at a time | 0.43 s | 203 MB |

The `ImgDev` image costs its own size (an `Array<U32>` holds 4 bytes per
slot) plus the runtime's 2 to 3 MB; the time includes generating and
comparing 128 MB of `Octets`. A `MemDev` holds `Octets` blocks (about 150
bytes per byte, bytes' compact storage), so large images belong in an
`ImgDev`.

## Dependencies

`bytes` (byte strings); `array` (bend-osdev-array: `Arrays.slots` and the
specification of a perfect array in `ImgDev.valid`, and its laws in the
proofs). No other.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 140 cases match (60 pure reads on `MemDev`,
40 owned reads on `ImgDev`, 40 `ImgDev` write sequences),
`scripts/deps.sh blockdev` ok. The 64 MB `ImgDev` and 2 MB `MemDev` runs
above were measured separately, natively.
