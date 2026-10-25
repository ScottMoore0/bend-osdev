# bend-osdev-mode-core

What the block-cipher modes of operation over any 128-bit block cipher
share:

* the 128-bit block `CmBlock` (an open type), its XOR, hex text and byte
  forms;
* the cipher interface the modes take as template arguments, and
  `CmBlock.dec_enc`, the form in which their round-trip laws take
  "decryption undoes encryption";
* the error type `CmError` every mode answers;
* the byte layer the modes are built from: a byte string split into whole
  blocks and a tail, blocks joined back into bytes, byte-wise XOR, a
  comparison with no early exit, and their tail-call forms.

It holds no mode and no cipher. The modes are packages of their own, each on
this one: [cbc](../cbc/) (with and without PKCS #7 padding),
[xts](../xts/), [ccm](../ccm/), [cmac](../cmac/), and [pkcs7](../pkcs7/)
(the padding); [aes](../aes/) is AES as a cipher for them, and
[aes-modes](../aes-modes/) the modes with AES (the named defaults). The
128-bit ciphers [sm4](../sm4/), [camellia](../camellia/),
[serpent](../serpent/), [twofish](../twofish/), [aria](../aria/) and
[cast6](../cast6/) work on `CmBlock` too, so they plug into every mode.

The directory is `mode-core` and the entry file `mode-core/mode-core.bend`
(published as `mode_core.bend`: the hub refuses a `-` in a path); the hub
name is `bend-osdev-mode-core`. It and the packages above were split from
bend-osdev-cipher-modes@0.1.0.0, which they supersede (that version stays on
the hub as it was).

**Names.** The types and helpers keep the names they had in cipher-modes
(`CmBlock`, `CmError`, `CmSplit`, `cm.*`), so no mode's code changes; types
and constructors are global in Bend, and these names collide with nothing.

## Specifications

* **The block:** 16 bytes as four big-endian 32-bit words, as AES (FIPS
  197, section 3.4, the state's columns) and the modes' specifications (NIST
  SP 800-38A, -38B, -38C; IEEE Std 1619-2007) number a block's bytes; the
  modes' specifications are cited by their packages.

## Files

| File | Holds |
|---|---|
| `mode-core.bend` | `CmBlock`, `CmError`, the byte layer (`cm.*`, `CmSplit`) |
| `LAWS.bend`, `PROOF.bend` | the laws (below), and their proofs |
| `check.bend` | the block's forms, XOR and the round-trip hypothesis over a toy permutation, with expected output |

## The block cipher is a parameter

Every mode takes the cipher as template arguments, specialised at compile
time:

```
~K: Data                          the cipher's (expanded) key
~enc: K -> CmBlock -> CmBlock     encrypt one block
~dec: K -> CmBlock -> CmBlock     decrypt one block (CBC and XTS decryption only)
+k: K                             the key
```

The modes never look inside `K`. A `CmBlock` is `CmBlock{w0, w1, w2, w3}`,
four big-endian 32-bit words (byte 0 of the block is the top byte of `w0`);
the type is open, so a cipher adapter may build and match it directly, or
convert with `CmBlock.of_octets` / `CmBlock.to_octets`. Every value of the
type is a block, so "decryption inverts encryption" is a statement about
every value.

## Public interface

**`mode-core.bend`**

| Def / type | Meaning |
|---|---|
| `CmBlock{w0, w1, w2, w3}` | a 128-bit block (open type) |
| `CmBlock.zero()`, `CmBlock.xor(a, b)`, `CmBlock.hex(b)` | the zero block, XOR, hex text |
| `CmBlock.dec_enc(~K, ~enc, ~dec, +k, xs)` | each block of `xs` encrypted and decrypted back under `k`: `xs` itself wherever decryption undoes encryption (the modes' round-trip laws' hypothesis) |
| `CmBlock.of_octets(o) -> Maybe<&2, CmBlock>`, `CmBlock.to_octets(b) -> Octets` | 16 bytes to a block and back (`None` for another length) |
| `CmError` | `CmBadKeyLength{got}`, `CmBadIvLength{got}`, `CmBadTweakLength{got}`, `CmBadNonceLength{got}`, `CmBadTagLength{got}`, `CmBadBlockSize{got}`, `CmNotBlockMultiple{len}`, `CmTooShort{len}`, `CmTooLong{len}`, `CmBadPadding{}`, `CmTagMismatch{}` (open: the modes build it) |

**The byte layer**, public now because the mode packages are built on it
(in cipher-modes it was internal to the package):

| Def / type | Meaning |
|---|---|
| `cm.byte(x)`, `cm.bits8(b)`, `cm.of8(s)`, `cm.word(a, b, c, d)`, `cm.b0(w)` .. `cm.b3(w)`, `cm.unword(w, rest)` | bytes and words, by bit slicing (bend-osdev-word64's `W64.bits`), so the round trips can be proved for every word |
| `cm.w0(b)` .. `cm.w3(b)`, `cm.bytes_onto(b, rest)`, `cm.bytes_of(b)`, `cm.block16(a0, .., a15)`, `cm.block_of(xs)` (and `cm.block_of.full`) | a block's words, its 16 bytes in front of a list, a block from 16 bytes (zero-filled if fewer) |
| `CmSplit{blocks, tail}` (open), `cm.split(xs)`, `cm.split.cons`, `cm.split.blocks`, `cm.split.tail` | a byte list as its whole blocks and the 0 to 15 bytes after them |
| `cm.join_onto(bs, rest)`, `cm.join(bs)` | blocks back into bytes |
| `cm.xor_bytes(xs, ys)`, `cm.diff(xs, ys, acc)`, `cm.ct_eq(xs, ys)`, `cm.mask(b)` | byte-wise XOR; equality with no early exit (a tag check); a bit as a mask |
| `cm.split.fast`, `cm.split.go`, `cm.join_onto.fast`, `cm.join.go`, `cm.xor_bytes.fast`, `cm.xor_bytes.go`, `cm.blocks.rev_onto`, `cm.blocks.len`, `cm.blocks.len.go`, `cm.blocks.append` | the tail-call forms the modes run (Bend 2.0.37's JavaScript lane overflows its stack on long structural recursions); the laws `split_fast`, `join_onto_fast` and `blocks_len_fast` tie them to the structural forms the proofs reason about |
| `cm.check(ok, e)`, `cm.need_block(xs, e)`, `cm.need_block.pick`, `CmBlock.of_octets.pick` | checks, as steps of a `Result` block |

## Extension points

* **Any 128-bit block cipher:** pass its key type and block functions as
  the modes' template arguments; nothing in the modes changes. A cipher
  that proves `dec(k, enc(k, b)) == b` gets the modes' round-trip laws: an
  induction on the list turns that law into their hypothesis
  (`CmBlock.dec_enc`), and bend-osdev-cm-instances writes it out for each
  128-bit cipher package.
* **Any mode:** a new mode takes `~K`, `~enc` (and `~dec`) the same way, and
  builds on the byte layer and its laws.
* **Open types:** `CmBlock`, `CmSplit` and `CmError` are open, so a cipher
  or a mode builds and matches them directly.

## Laws

`LAWS.bend` (33 laws), in `PROOF.bend`.

**About the block** (from cipher-modes): `block_octets_round_trip`, a block
written as Octets reads back as itself.

**Shared by the modes' proofs** (new with the split, 32 laws: they were
private lemmas of cipher-modes' `PROOF.bend`, and a package's proofs can use
another package's laws, not its private lemmas). The mode packages use
them under the lemmas' old names (a private def per law, whose body is the
law), so their proofs read as before.

* the byte layer: `split_cons_blocks`, `split_cons_tail`, `split_eta`,
  `split_bytes_onto` (the bytes of a block in front of a list split into
  that block and the split of the list), `mask_bytes_onto`, `join_split`
  (joining the split of a masked byte list gives it back),
  `bytes_onto_block16`, `split_tail_short` (a split's tail is shorter than a
  block), `split_tail_masked`, `split_short` (a list shorter than a block
  splits into no blocks), `block_of_bytes_of`, `mask_join_onto`,
  `split_join_short` (joined blocks in front of a short tail split back into
  them);
* the tail-call forms: `split_fast`, `join_onto_fast`, `blocks_len_fast`;
* bytes' list layer and Base's `Nat`: `byte_byte`, `list_take_append`,
  `list_drop_append`, `list_mask_append`, `list_mask_take`,
  `list_len_append`, `list_len_take`, `nat_lt_le`, `octets_masked`,
  `octets_len`;
* XOR undone: `word_xor_xor`, `u32_xor_xor`, `block_xor_xor`;
* results and the hypothesis: `bind_cong` (a bind whose continuations agree
  on every value agrees), `dec_enc_head` and `dec_enc_tail` (the hypothesis
  on a list gives it on its first block and on the rest).

How they are proved: the bytes of a word and a block on its 32 symbolic bits
(each a deep pattern, then `{==}`); splitting and joining by induction, 16
bytes at a time; the tail-call forms equal to the structural forms by
induction on an accumulator; masks through bytes' interface laws
(`octets_of_to`, `octets_to_of`); nothing looks inside `Octets`.

## Tests

`check.bend` runs the block's hex and byte forms, XOR, `of_octets` refusing
15 bytes, and `CmBlock.dec_enc` over a toy permutation (not a cipher), with
its expected output. The modes are tested in their packages, and over AES
against the specifications' vectors in aes-modes.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (2 s, 0.35 GB peak), `--verdict` ALL PROOFS CHECK (4 s, 0.40 GB peak, with bytes' and u32's proofs), `check.bend` passes, `scripts/deps.sh` and `scripts/publish.py --dry-run` pass.

## Dependencies

`DEPS`: `bytes` (`Octets`, and its list layer), `word64` (the bit slicing
the byte conversions are built from), and `u32` in the proofs only (its laws
of `Nat` arithmetic).
