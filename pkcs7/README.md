# bend-osdev-pkcs7

PKCS #7 padding, for any block size from 1 to 255: padding to a whole
number of blocks and unpadding back, with unpadding proved to undo padding
for every block size and message, and every padded message proved a whole
number of blocks.

The directory is `pkcs7` and the entry file `pkcs7/pkcs7.bend`; the hub name
is `bend-osdev-pkcs7`. It is one of the packages split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was): mode-core, one package per mode (cbc, xts, ccm, cmac,
pkcs7), aes and aes-modes.

## Specifications

Written from the public specification only:

* **PKCS #7 padding:** RFC 5652, *Cryptographic Message Syntax*, section
  6.3.

## Files

| File | Holds |
|---|---|
| `pkcs7.bend` | `Pkcs7.pad`, `Pkcs7.unpad` |
| `LAWS.bend`, `PROOF.bend` | the laws, and their proofs |
| `gen/pkcs7_proof.py` | writes the generated regions of `PROOF.bend` (a byte's bits, and the values 0 to 255); `--check` checks they are current |
| `check.bend` | padding and unpadding, and every refusal, with expected output |

## Public interface

| Def | Meaning |
|---|---|
| `Pkcs7.pad(bs, m)` | `m` padded to blocks of `bs` bytes (`CmBadBlockSize` unless 1 <= bs <= 255) |
| `Pkcs7.unpad(bs, m)` | the padding removed (`CmBadBlockSize`, `CmTooShort` for the empty string, `CmNotBlockMultiple`, `CmBadPadding`) |

Both answer `Result<&2, &2, CmError, Octets>`, with mode-core's error type.
Everything else (`pkcs7.*`, `Pkcs7.pad.go`, `Pkcs7.unpad.go`) is internal.
cbc pads with block size 16; cipher-core's 64-bit modes can use block size 8;
aead's CBC-HMAC uses it too.

## Extension points

* **The block size** is a parameter.
* **Side channels:** unpadding reports whether the padding was good, which,
  exposed to an attacker, is a padding oracle (cbc's README, Notes).

## Laws

`LAWS.bend` (8 laws).

**For every block size `bs` and message `m`:**

* `pkcs7_round_trip`: `bind(pad(bs, m), c => unpad(bs, c)) == map(c => m,
  pad(bs, m))`: for a block size the padding takes (1 to 255), unpadding
  the padded message gives `m`; for any other, both refuse alike
  (`CmBadBlockSize`);
* `pkcs7_pad_blocks`: a padded message is a whole number of blocks (its
  length mod `bs` is 0);
* `pkcs7_unpad_empty`: for a block size the padding takes, unpadding an
  empty string is refused (`CmTooShort{0}`).

The arithmetic is on Base's `Nat.divmod` (as kmath's division lemmas are):
with `bs = 1 + q` and `L` the message's length, `L mod bs` is at most `q`,
so the padding `p = bs - L mod bs` is `1 + (q - L mod bs)`, from 1 to `bs`,
and `L + p` is a multiple of `bs` (`pk.mod_le`, `pk.mod_pad`, by induction
on Base's `Nat.divmod.go`). Unpadding reads the last byte back as `p`
(`U32.to_nat` of the byte of `U32.from_nat(p)` is `p` for every `p` up to
255, checked value by value: `gen/pkcs7_proof.py`'s "u8" region), the last
`p` bytes all equal it (each XOR itself is 0, bit by bit), and the first `L`
bytes are `m` (bytes' laws on `take`, `drop` and `at` of an append).

**Vectors** (RFC 5652's padding, by computation): `pkcs7_pad_empty` (the
empty message becomes a whole block of 16s), `pkcs7_pad_15`,
`pkcs7_unpad_15`, and bad padding refused: `pkcs7_unpad_zero` (a last byte
of 0) and `pkcs7_unpad_mixed` (a last byte the bytes before it contradict).

**Not proved:** that unpadding refuses every bad padding (the two vectors,
cbc's differential test of padded CBC and `check.bend` cover it).

## Tests

* `check.bend`: padding to 16 bytes (the empty message, 15 bytes) and to 8,
  unpadding back (also at block size 255 over 1000 bytes), and every
  refusal. The padded bytes are RFC 5652's rule, checked by hand.
* cbc's `ref/run.sh` tests padded CBC over AES against Python's
  `cryptography` (its PKCS #7 padder), so this padding with it.

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(2 s, 0.34 GB peak; `--verdict` 5 s, 0.40 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s, 0.34 GB peak), `--verdict` ALL PROOFS CHECK (4 s, 0.40 GB peak), `gen/pkcs7_proof.py --check` up to date, `check.bend` passes, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`, and its laws in the proofs), `mode-core` (the
error type `CmError`, and its check helper) and `u32` in the proofs only
(its laws of `Nat` arithmetic).
