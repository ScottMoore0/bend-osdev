# bend-osdev-crc

Cyclic redundancy checks in the Rocksoft parameter model (Ross Williams, "A
Painless Guide to CRC Error Detection Algorithms", 1993; parameters from the
CRC catalogue at reveng.sourceforge.io).

Inputs are `Octets` (bend-osdev-bytes). A CRC is fixed by its width, polynomial (normal, most significant bit first),
initial register value, bit order and final XOR. `Crc32Spec` covers widths 8
to 32 on `U32`; `Crc64Spec` covers width 64 on `W64` (bend-osdev-word64).

## Files

| File | Holds |
|---|---|
| `crc.bend` | the parameter model, the bitwise engines (the reference), the named CRCs, streaming |
| `table.bend` | the table-driven fast path: `Crc32Spec.update_fast` / `compute_fast` and `Crc64Spec.update_fast` / `compute_fast` |

## The named CRCs

| Def | CRC | Used by | Check value of "123456789" |
|---|---|---|---|
| `crc32c` | CRC-32C (Castagnoli), poly 0x1EDC6F41 | iSCSI, ext4, btrfs | 0xE3069283 |
| `crc16` | CRC-16/ARC, poly 0x8005 | the kernel's `crc16`; ext4 group descriptors | 0xBB3D |
| `crc_t10dif` | CRC-16/T10-DIF, poly 0x8BB7 | SCSI data integrity | 0xD0DB |
| `crc64_ecma` | CRC-64/ECMA-182, MSB first | the kernel's `crc64_be` | 0x6C40DF5F0B497347 |
| `crc64_xz` | CRC-64/XZ | the XZ format's check | 0x995DC9BBDF1939FA |
| `crc64_nvme` | CRC-64/NVME | NVMe | 0xAE8B14860A799888 |
| `crc32` | CRC-32/ISO-HDLC | zlib, Ethernet (also in bend-kit-hash) | 0xCBF43926 |

## Computing a CRC in pieces

`Crc32Spec.start(spec)` gives the initial register, `Crc32Spec.update(spec, c,
xs)` folds bytes into a register, and `Crc32Spec.finish(spec, c)` applies the
final XOR; `Crc32Spec.compute` is the three in a row. The same for
`Crc64Spec`. ext4 stores the raw register: its superblock checksum is
`Crc32Spec.update(crc32c.spec(), 4294967295, bytes)`.

## Extension points

* **Any CRC of width 8 to 32 or 64:** build a `Crc32Spec` or `Crc64Spec` with
  its catalogue parameters; the named CRCs are just such values. A CRC whose
  input and output bit orders differ (refin ≠ refout) is not covered yet.
* **Streaming:** `start`/`update`/`finish` let a caller feed data in pieces
  (a block at a time, a packet at a time), with the law that pieces give the
  whole's CRC.
* **Fast paths:** `table.bend` is the first, kept beside the bitwise reference.
  Others (several bytes per step, a table kept between calls) can be added the
  same way, each tied to the reference.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every input, and every parameter set:** a CRC computed in pieces is the
  CRC of the whole: `update(spec, c, a ++ b) == update(spec, update(spec, c, a),
  b)` for all `Octets` `a` and `b`, at both word sizes, proved by induction
  through bytes' interface law `octets_append_list`;
* **vectors:** the catalogue's check value for each named CRC, and the empty
  input;
* **the fast path, as vectors:** the check values computed table-driven, and
  agreement with the reference on a longer input. A law for every input would
  need lemmas about `Array`'s internals, so the fast path is tied to the
  reference by these vectors and by the differential test.

## Tests

`ref/run.sh` compares every CRC, through both the reference and the fast
path, on random inputs (277 cases) with:

* an independent implementation of the parameter model (`ref/gen.py`);
* Python's `binascii.crc32` (zlib), for CRC-32;
* the check field of real `.xz` streams (Python's `lzma`), for CRC-64/XZ;
* the superblock checksums `mke2fs` writes for ext4 with `metadata_csum`, for
  CRC32C.

## Speed

**Lanes.** The figures in this section were measured on bend's JavaScript lane
(`bend file.bend`, which runs `main` inside the bend process). That lane's
stack overflows at some tens of thousands of nested non-tail calls, and it
uses several times the memory of a native build (`bend file.bend -o prog`),
which has a 2 GB stack; see AGENTS.md, "Runtime and checker limits". They
will be re-measured natively once W64-heavy code builds natively
(bendlang/bend#1069).

The reference engines in `crc.bend` run bit by bit. The fast path in
`table.bend` looks up one 256-entry table per byte instead of eight bit
steps: on a native build, CRC32C over 400 KB took 3 ms bit by bit and 1 ms
table-driven (Bend 2.0.37, WSL2). The 64-bit CRCs use `W64`, which is slow
until Base has a native `U64`; the table matters most there.

The fast path builds its table once per call (an `Array`, threaded through
the loop), so it pays off on inputs longer than a few hundred bytes.

## Sizes

Every engine, bitwise and table-driven, is a tail-recursive loop over the
bytes, so there is no length limit beyond memory. Measured on Bend 2.0.37
(native build, WSL2) over 1 MB of pseudo-random bytes, each run including
building the input (all seven results checked against `ref/gen.py`'s model,
zlib and xz):

| Run, 1 MB | Time | Peak RAM |
|---|---|---|
| `crc32c`, bitwise | 3.0 s | 1.30 GB |
| `crc32c`, table-driven | 3.7 s | 1.30 GB |
| `crc64_ecma`, bitwise | 17.7 s | 1.36 GB |
| `crc64_ecma`, table-driven | 10.0 s | 1.36 GB |
| all seven named CRCs, bitwise | 60 s | 1.74 GB |
| all seven named CRCs, table-driven | 35 s | 1.79 GB |

Most of the memory is the 1 MB `Octets` (about 940 bytes per byte
when measured; bytes' compact `OctByte` storage, merged since, holds an
`Octets` in about a third of that, about 150 bytes per byte, and these
figures have not been re-measured)
and its list form. `check.bend` runs CRC32C both ways and CRC-64/XZ
table-driven over 100 KB as a regression test.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 277 cases match, `scripts/deps.sh` passes.
