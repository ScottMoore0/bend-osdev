# bend-osdev-uuid

Universally unique identifiers, as RFC 9562 defines them ("Universally Unique
IDentifiers (UUIDs)", K. Davis, B. Peabody, P. Leach, May 2024, which
obsoletes RFC 4122): the 16 octets, the 8-4-4-4-12 text form, the version
and variant fields, the Nil and Max UUIDs, and the mixed-endian GUID layout
that GPT stores (UEFI Specification, chapter 5, "GUID Partition Table (GPT)
Disk Layout", and appendix A, "GUID and Time Formats").

It does not generate UUIDs: that needs a clock, randomness or a hash, which
belong to the caller (`Uuid.make` builds one from its bytes).

## Files

| File | Holds |
|---|---|
| `uuid.bend` | the package: the `Uuid` type, bytes, the GUID layout, text, version and variant |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `gen/genproof.py` | writes `PROOF.bend` (its bit-split patterns are long): `python3 uuid/gen/genproof.py` |
| `check.bend` | a runnable check of the RFC's examples |
| `ref/gen.py`, `ref/run.sh` | the differential test against Python's `uuid` module (`gen.py` writes `ref/cases.bend` and `ref/expected.txt`, which `ref/.gitignore` lists) |

## API

`Uuid` is opaque: use it only through these defs.

| Def | Meaning |
|---|---|
| `Uuid.parse(s)` | the UUID of the 36-character text form, hex digits in either case; `Fail{UuidBadLength{}}`, `Fail{UuidBadDash{}}` or `Fail{UuidBadDigit{}}` if malformed |
| `Uuid.show(u)` | the text form, in lower case (RFC 9562 section 4) |
| `Uuid.to_bytes(u)`, `Uuid.from_bytes(o)` | the 16 bytes (`Octets`) in RFC order; `from_bytes` needs exactly 16 (`Fail{UuidBadLength{}}` otherwise) |
| `Uuid.to_guid(u)`, `Uuid.from_guid(o)` | the 16 bytes in the GUID layout: the first three fields (`time_low`, `time_mid`, `time_hi_and_version`) least significant byte first, the last eight octets as they are. Python's `uuid.bytes_le` |
| `Uuid.to_guid_list(u)`, `Uuid.from_guid_list(xs)` | the same on `List<&2, U32>`, for packages that work on lists |
| `Uuid.from_bytes_at(o, i)`, `Uuid.from_guid_at(o, i)` | field readers: the 16 bytes at offset `i` of a longer byte string, or `None` |
| `Uuid.make(a0, …, a15)`, `Uuid.byte(u, i)` | a UUID from its 16 bytes in RFC order (each masked to 8 bits), and byte `i` of one |
| `Uuid.version(u)` | the version field, the high nibble of octet 6 (meaningful when the variant is `UuidRfc`) |
| `Uuid.variant(u)` | `UuidNcs{}`, `UuidRfc{}`, `UuidMicrosoft{}` or `UuidFuture{}`, from the top bits of octet 8 (section 4.1); `UuidVariant.show` names it |
| `Uuid.nil()`, `Uuid.max()` | all zeros and all ones (sections 5.9 and 5.10) |
| `Uuid.is_eq(a, b)`, `Uuid.is_nil(u)` | comparisons |
| `UuidError`, `UuidError.show` | why text or bytes were refused |

## Extension points

* **The representation of `Uuid` is internal** (today four native `U32`
  words; see Representation). Other packages, and their proofs, see a UUID
  only as its bytes: the law
  `make_bytes` (`make(byte(u, 0), …, byte(u, 15)) == u`) lets a proof treat
  any `Uuid` as 16 `U32`s without opening the type, as partition's proofs do.
* **Generating UUIDs** (versions 4 and 7 from randomness and a clock, 3 and
  5 from MD5 and SHA-1) can be added on top of `Uuid.make`, which sets no
  version or variant bits itself.

## Representation

A `Uuid` is four native `U32` words, each holding four octets most
significant first (`w0` octets 0 to 3, ..., `w3` octets 12 to 15), so every
value of the type is a UUID. Bytes are read out with native shifts and masks
(`U32.and(255, U32.shrn(w, k))`) and joined by bit slicing (word64's
`W64.bits.cat`), which proofs compute through on symbolic bits. Bend's C
backend lays a `Word(n)` out as n slots, so the sixteen `Word(8n)` octets
used before cost 128 slots a UUID, and the widest segment of `check.bend`
was 256 (`Uuid.is_nil`), past the 247 the backend compiles
(bendlang/bend#1069); a `Uuid` now costs 4, and the widest segment is 97.
The text form is still written and read through `Word(8n)` octets and
`Word(4n)` nibbles (internal), which is what the text round trip is proved
on.

The package uses only bytes' public defs (`Octets.*`, `at`) and, in proofs,
its law `octets_to_of` and `mask`.

## Laws

`LAWS.bend`:

* **for every UUID** (proved by splitting each of its four words into its 32
  bits and computing):
  * `from_bytes(to_bytes(u)) == Done{u}` and `from_guid(to_guid(u)) == Done{u}`,
    and `from_guid_list(to_guid_list(u)) == Done{u}`;
  * `make(byte(u, 0), …, byte(u, 15)) == u`;
  * `parse(show(u)) == Done{u}`, and `parse(String.to_upper(show(u))) ==
    Done{u}`: the text form reads back in either case. Proved by induction on
    the octets, from a 16-case lemma that each nibble's digit reads back;
  * `show(u)` has 36 characters;
* **for every 16 bytes:** reading them in the GUID layout is reading them in
  RFC order with the first three fields byte-reversed;
* **vectors:** RFC 9562's example UUIDs (appendices A and B: versions 1, 3, 4,
  5, 6, 7 and both version 8 examples) read from the text the RFC prints (some
  upper case) and written back in lower case, with their versions and
  variants; the Nil and Max UUIDs and their variants; a Microsoft-variant
  value; byte orders (the v4 example in RFC order, the v1 example and the EFI
  System Partition type GUID in the GUID layout); and malformed text and
  bytes, with the failure each gives.

Not proved: that every string `parse` accepts is written back by `show` as
its lower-case form. The text round trip is proved in the direction that
starts from a UUID.

The byte round trips convert a list to `Octets` and back through bytes'
interface law `octets_to_of`, so no proof depends on how `Octets` stores its
bytes.

## Tests

`ref/run.sh` compares the package with Python's `uuid` module on 112 UUIDs
(random version 4 ones; version 1, 3 and 5 ones; random values with octet 8
in each variant's range; Nil and Max): reading the text in lower and upper
case, reading `bytes_le`, and writing the text, `bytes`, `bytes_le`, the
version field and the variant.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes and `ref/run.sh` 112 cases match, both as native binaries
(`VERDICT=1 scripts/check.sh uuid`: no JavaScript-lane fallback);
`scripts/deps.sh uuid` ok. Native sizes: `check.bend` builds in 2 s
(170 MB) to a 206 KB binary that runs in under 0.01 s in 2.4 MB; the ref
cases build in 5 s (430 MB) to a 690 KB binary (under 0.01 s, 2.9 MB).
partition and ext2, which use `Uuid`, pass their checks unchanged.
