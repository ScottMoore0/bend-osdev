# bend-osdev-crc

Cyclic redundancy checks in the Rocksoft parameter model (Ross Williams, "A
Painless Guide to CRC Error Detection Algorithms", 1993; parameters from the
CRC catalogue at reveng.sourceforge.io).

Inputs are `Octets` (bend-osdev-bytes). A CRC is fixed by its width, polynomial (normal, most significant bit first),
initial register value, bit order and final XOR. `Crc32Spec` covers widths 1
to 32 on `U32` (below 8, a most-significant-first CRC takes its input a bit
at a time, since a byte does not fit at the register's top); `Crc64Spec` covers width 64 on `W64` (bend-osdev-word64).

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
| `crc4_itu` | CRC-4/G-704 (CRC-4/ITU), poly 0x3, reflected | ITU-T G.704 framing | 0x7 |
| `crc7_mmc` | CRC-7/MMC, poly 0x09 | SD/MMC commands | 0x75 |
| `crc8_smbus` | CRC-8/SMBUS, poly 0x07 | SMBus packet error checking | 0xF4 |
| `crc8_itu` | CRC-8/I-432-1 (CRC-8/ITU), poly 0x07, xorout 0x55 | ATM header error control | 0xA1 |
| `crc8_maxim` | CRC-8/MAXIM-DOW, poly 0x31, reflected | Dallas/Maxim 1-Wire | 0xA1 |
| `crc8_dvb_s2` | CRC-8/DVB-S2, poly 0xD5 | DVB-S2 | 0xBC |
| `crc8_autosar` | CRC-8/AUTOSAR, poly 0x2F, init and xorout 0xFF | AUTOSAR | 0xDF |
| `crc16_kermit` | CRC-16/KERMIT (CRC-16/CCITT), poly 0x1021, reflected | the kernel's `crc_ccitt` | 0x2189 |
| `crc16_ccitt_false` | CRC-16/IBM-3740 (CRC-16/CCITT-FALSE), poly 0x1021, init 0xFFFF | | 0x29B1 |
| `crc16_xmodem` | CRC-16/XMODEM (CRC-16/ITU-T), poly 0x1021 | the kernel's `crc_itu_t` | 0x31C3 |

## Computing a CRC in pieces

`Crc32Spec.start(spec)` gives the initial register, `Crc32Spec.update(spec, c,
xs)` folds bytes into a register, and `Crc32Spec.finish(spec, c)` applies the
final XOR; `Crc32Spec.compute` is the three in a row. The same for
`Crc64Spec`. ext4 stores the raw register: its superblock checksum is
`Crc32Spec.update(crc32c.spec(), 4294967295, bytes)`.

## Extension points

* **Any CRC of width 1 to 32 or 64:** build a `Crc32Spec` or `Crc64Spec` with
  its catalogue parameters; the named CRCs are just such values. A CRC whose
  input and output bit orders differ (refin ≠ refout) is not covered yet.
* **Streaming:** `start`/`update`/`finish` let a caller feed data in pieces
  (a block at a time, a packet at a time), with the law that pieces give the
  whole's CRC.
* **Fast paths:** `table.bend` is the first, kept beside the bitwise reference.
  Others (several bytes per step, a table kept between calls) can be added the
  same way, each tied to the reference.

## Laws

`LAWS.bend`:

* **for every input, and every parameter set:** a CRC computed in pieces is the
  CRC of the whole: `update(spec, c, a ++ b) == update(spec, update(spec, c, a),
  b)` for all `Octets` `a` and `b`, at both word sizes, proved by induction
  through bytes' interface law `octets_append_list`;
* **vectors:** the catalogue's check value for each named CRC, and the empty
  input;
* **the fast path, as vectors:** the check values computed table-driven, and
  agreement with the reference on a longer input. Below width 8, a
  most-significant-first CRC's fast path is the bitwise engine (no table).
  A law for every input would need lemmas about `Array`'s internals, so the fast path is tied to the
  reference by these vectors and by the differential test.

## Tests

`ref/run.sh` compares every CRC, through both the reference and the fast
path, on random inputs (737 cases) with:

* an independent implementation of the parameter model (`ref/gen.py`);
* Python's `binascii.crc32` (zlib), for CRC-32;
* the check field of real `.xz` streams (Python's `lzma`), for CRC-64/XZ;
* the superblock checksums `mke2fs` writes for ext4 with `metadata_csum`, for
  CRC32C.

## Speed

The reference engines in `crc.bend` run bit by bit. The fast path in
`table.bend` looks up one 256-entry table per byte instead of eight bit
steps: on a native build, CRC32C over 400 KB took 3 ms bit by bit and 1 ms
table-driven (Bend 2.0.37, WSL2). The 64-bit CRCs use `W64`; natively they
run about as fast as the 32-bit ones (see the table below), so the table
gains less than it did on the JavaScript lane.

The fast path builds its table once per call (an `Array`, threaded through
the loop), so it pays off on inputs longer than a few hundred bytes.

## Sizes

Every engine, bitwise and table-driven, is a tail-recursive loop over the
bytes, so there is no length limit beyond memory. Measured on Bend 2.0.37
(native build, `bend file.bend -o prog`, WSL2) over pseudo-random bytes,
each run including building the input (results checked against an
independent Python CRC):

| Run | Time, native | Peak RAM, native | JavaScript lane, before |
|---|---|---|---|
| building the 1 MB input alone | 0.07 s | 84 MB | |
| `crc32c`, bitwise, 1 MB | 0.13 s | 84 MB | 3.0 s, 1.30 GB |
| `crc32c`, table-driven, 1 MB | 0.12 s | 84 MB | 3.7 s, 1.30 GB |
| `crc64_ecma`, bitwise, 1 MB | 0.12 s | 84 MB | 17.7 s, 1.36 GB |
| `crc64_ecma`, table-driven, 1 MB | 0.13 s | 84 MB | 10.0 s, 1.36 GB |
| all seven named CRCs, bitwise, 1 MB | 1.1 s | 125 MB | 60 s, 1.74 GB |
| all seven named CRCs, table-driven, 1 MB | 0.55 s | 100 MB | 35 s, 1.79 GB |
| building the 16 MB input alone | 1.2 s | 1.31 GB | |
| `crc32c`, bitwise / table-driven, 16 MB | 2.3 s / 2.2 s | 1.31 GB | |
| `crc64_ecma`, bitwise / table-driven, 16 MB | 2.0 s / 2.0 s | 1.31 GB | |

Most of the memory is the input `Octets` (about 80 bytes per byte held,
natively) and its list form, so the CRC itself adds little.
`check.bend` runs CRC32C both ways and CRC-64/XZ
table-driven over 100 KB as a regression test.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 737 cases match, `scripts/deps.sh` passes.
