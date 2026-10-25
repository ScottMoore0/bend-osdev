# bend-osdev-xorblocks

The XOR of byte blocks: the counterpart of the kernel's `xor_blocks` helper,
which XORs any number of source blocks into a destination block. RAID-5's
parity, and RAID-6's P syndrome, are such XORs (H. Peter Anvin, "The
mathematics of RAID-6", first version 20 January 2004, last updated 20
December 2011, section 2, equation (1): P = D_0 + D_1 + ... + D_(n-1), where
"+" on bytes is bitwise XOR, section 1, items 1 and 2). bend-osdev-raid6
builds on this package.

There is no further specification: XOR of two blocks is the bitwise
exclusive or of the bytes at each offset. The one real choice, what to do
when the blocks differ in length, is a parameter. No kernel source was read;
only the helper's purpose is matched, not its signature.

Byte strings are `Octets` (bend-osdev-bytes).

## Files

| File | Holds |
|---|---|
| `xorblocks.bend` | the length policy `XorbLen`, XOR of two blocks under either policy, `into` (xor_blocks) and `all` |

## API

| Def | Meaning |
|---|---|
| `XorbLen`: `XorbLonger{}`, `XorbShorter{}` | the length policy: pad the shorter block with zeros (the result is as long as the longer), or stop where the shorter ends |
| `Xorb.len_default()` | `XorbLonger{}` |
| `Xorb.xor(a, b)` | a XOR b, the shorter padded with zeros |
| `Xorb.xor_cut(a, b)` | a XOR b, as long as the shorter |
| `Xorb.xor_with(p, a, b)` | a XOR b under policy `p` |
| `Xorb.into(dest, srcs)` | xor_blocks: each source XORed into `dest` in turn (zero padding) |
| `Xorb.into_with(p, dest, srcs)` | the same under policy `p` |
| `Xorb.all(srcs)` | the XOR of all the blocks; the empty block for none |
| `Xorb.xor_list(xs, ys)`, `Xorb.xor_cut_list(xs, ys)` | the same two XORs on byte lists (`List<&2, U32>`): the structural forms, public as the bytewise meaning of `xor` and `xor_cut` for dependents' proofs |

With zero padding, XOR is a commutative monoid on `Octets` with the empty
block as its identity, in which every block cancels itself to zeros; that
is why it is the default (and what RAID's parity algebra needs). With
`XorbShorter`, a block XORed with the empty block is empty.

Every function is tail-recursive over the bytes, so blocks of any length run
on both of Bend's lanes; `check.bend` XORs 200,000-byte blocks.

## Extension points

* **Length policy:** `XorbLen` is the parameter; a further policy (for
  example, refusing blocks of unequal length) is one more constructor and
  one more case in `Xorb.xor_with`.
* **Streaming:** XOR works a byte at a time, so blocks of equal length can be
  XORed in pieces: the law `xor_append` says that the XOR of joined pieces is
  the join of the pieces' XORs. There is no separate start/update/finish
  interface, since no state passes from one piece to the next.
* **Fast paths:** the work is done on the blocks' byte lists by
  `xorb.pad.go` and `xorb.cut.go`, each proved equal to its structural
  form (`Xorb.xor_list`, `Xorb.xor_cut_list`) for every input. A
  word-at-a-time path could be added behind the same defs in the same way.

## Laws

`LAWS.bend`, all proved for every input:

* `xor_list`, `xor_cut_list`: the interface laws for dependents' proofs: the
  bytes of `xor(a, b)` are `xor_list` of the bytes of `a` and `b`, and the
  same for `xor_cut` (bend-osdev-raid6's proofs use them);
* `xor_comm`, `xor_assoc`: zero-padded XOR is commutative and associative;
* `xor_empty`: the empty block is its identity;
* `xor_self`: a block XORed with itself is as many zero bytes as it has;
* `xor_zeros`: XORing in no more zero bytes than a block has leaves it
  unchanged;
* `xor_len`: the result is as long as the longer block;
* `xor_append`: for pieces `a1`, `b1` of equal length, `xor(a1 ++ a2, b1 ++
  b2) == xor(a1, b1) ++ xor(a2, b2)` (the streaming law);
* `xor_cut_comm`, `xor_cut_assoc`, `xor_cut_len` (the result is as long as
  the shorter), and `xor_cut_same`: on blocks of equal length the two
  policies agree;
* `xor_with_longer`, `xor_with_shorter`: the policy picks the XOR;
* `into_nil`, `into_cons`: `into` XORs the sources in one at a time;
  `into_all`: `into(d, srcs) == xor(d, all(srcs))`;
* vectors: small blocks under each policy, and `into` of three sources.

The proofs go through bytes' interface laws (`octets_of_to`,
`octets_to_of`, `octets_len_list`, `octets_zeros_list`,
`octets_append_list`): each law over `Octets` becomes a law over the byte
lists, proved by induction, with XOR's algebra proved on the 32 bits of a
word.

## Tests

`check.bend` runs the vectors and checks, on 200,000-byte pseudo-random
blocks, that XOR undoes itself, a block XORed with itself is zeros, the
padded and cut lengths, the streaming law, and `into` with sources that
cancel. `ref/run.sh` (140 cases with the default seed) compares `xor`,
`xor_cut`, `into` under both policies and `all` on random blocks of random,
often unequal, lengths with Python's own bytes. Python has no `xor_blocks`,
so that reference is the definition, written in `ref/gen.py`.

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 140 cases match, `scripts/deps.sh` passes.
