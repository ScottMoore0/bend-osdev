# bend-osdev-crc

Cyclic redundancy checks in the Rocksoft parameter model (Ross Williams, "A
Painless Guide to CRC Error Detection Algorithms", 1993; parameters from the
CRC catalogue at reveng.sourceforge.io).

Inputs are `Octets` (bend-osdev-bytes). A CRC is fixed by its width, polynomial (normal, most significant bit first),
initial register value, bit order and final XOR. `Crc32Spec` covers widths 8
to 32 on `U32`; `Crc64Spec` covers width 64 on `W64` (bend-osdev-word64).

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
* **Fast paths** (table-driven, several bytes at a time) can be added behind
  the same defs, with the bitwise engines kept as the reference.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer):

* **for every input, and every parameter set:** a CRC computed in pieces is the
  CRC of the whole: `update(spec, c, a ++ b) == update(spec, update(spec, c, a),
  b)` for all `Octets` `a` and `b`, at both word sizes, proved by induction
  through bytes' interface law `octets_append_list`;
* **vectors:** the catalogue's check value for each named CRC, and the empty
  input.

## Tests

`ref/run.sh` compares every CRC on random inputs (140 cases) with:

* an independent implementation of the parameter model (`ref/gen.py`);
* Python's `binascii.crc32` (zlib), for CRC-32;
* the check field of real `.xz` streams (Python's `lzma`), for CRC-64/XZ;
* the superblock checksums `mke2fs` writes for ext4 with `metadata_csum`, for
  CRC32C.

## Speed

The 32-bit CRCs run bit by bit on native `U32` arithmetic. The 64-bit ones use
`W64`, which is slow until Base has a native `U64`. Neither is table-driven
yet.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 140 cases match.
