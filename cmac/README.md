# bend-osdev-cmac

CMAC, a MAC over any 128-bit block cipher (only its encryption is used):
the subkeys, the MAC in one call, its streaming interface, and a tag check
with no early exit, with a law that pieces give the MAC of the whole.

The directory is `cmac` and the entry file `cmac/cmac.bend`; the hub name is
`bend-osdev-cmac`. It is one of the packages split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was): mode-core, one package per mode (cbc, xts, ccm, cmac,
pkcs7), aes and aes-modes.

## Specifications

Written from the public specifications only:

* **CMAC:** NIST SP 800-38B (2005) and RFC 4493, *The AES-CMAC Algorithm*
  (2006) (its section 4 examples run over AES in aes-modes).

## Files

| File | Holds |
|---|---|
| `cmac.bend` | CMAC subkeys, the MAC, and its streaming interface |
| `LAWS.bend`, `PROOF.bend` | the law, and its proof |
| `check.bend` | CMAC over a toy permutation, with expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test, over AES, against Python's `cryptography` |

## Public interface

The cipher is the template arguments `~K`, `~enc` (mode-core's README).

| Def | Meaning |
|---|---|
| `Cmac.dbl(b)`, `Cmac.subkey1(~K, ~enc, +k)`, `Cmac.subkey2(...)` | the doubling and the subkeys K1, K2 |
| `CmacState`, `Cmac.start()`, `Cmac.update(~K, ~enc, +k, s, m)`, `Cmac.finish(~K, ~enc, +k, s)` | streaming; `CmacState` is opaque |
| `Cmac.mac(~K, ~enc, +k, m) -> Octets` | the 16-byte MAC in one call |
| `Cmac.verify(~K, ~enc, +k, m, tag) -> Bool` | a 16-byte tag, compared with no early exit |

Everything else (`cmac.*`) is internal. With AES: aes-modes' `CmAes.cmac`
takes the raw key.

## Extension points

* **Any 128-bit block cipher** as the template arguments (encryption only).
* **The tag check:** `Cmac.verify`, or `Cmac.mac` and a truncation of the
  caller's choice.
* **Streaming:** `start`/`update`/`finish`, in any pieces.

## Laws

`LAWS.bend` (1 law): `cmac_streaming`: the CMAC state after `a ++ b` is the
state after `a`, then `b`, for every cipher, key and state (so start,
update .. update, finish is the MAC of the pieces joined). Proved by
induction on the bytes, through bytes' `octets_append_list`. The subkey
vector with AES (RFC 4493's K1) is aes-modes' law `cmac_rfc4493_k1`.

## Tests

* `check.bend`: CMAC over a toy permutation (not a cipher): the doubling,
  the subkeys, MACs of no, one and several blocks, the MAC in two pieces
  against the MAC in one call, and tag checks. The subkeys were checked by
  hand against the doubling of SP 800-38B; the other outputs are recorded as
  a regression test.
* `ref/run.sh`: CMAC over AES-128 and AES-256, in one call and in two pieces,
  against Python's `cryptography` (40 cases with the default seed; through
  aes-modes' named defaults and bend-osdev-aes, imported from `ref/` only).
* aes-modes' `check.bend`: RFC 4493 examples 1 to 4 and K2.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s, 0.33 GB peak), `--verdict` ALL PROOFS CHECK (6 s, 0.38 GB peak), `check.bend` passes, `ref/run.sh` 40 cases match, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`, and its laws in the proof) and `mode-core` (the
block and the byte layer).
