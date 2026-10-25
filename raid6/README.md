# bend-osdev-raid6

RAID-6: the P and Q syndromes of a stripe of data blocks, and the recovery
of any one or two lost blocks of the stripe (data, P or Q), the
counterpart of the kernel's RAID-6 library.

Written from H. Peter Anvin, "The mathematics of RAID-6", first version 20
January 2004, last updated 20 December 2011
(https://www.kernel.org/pub/linux/kernel/people/hpa/raid6.pdf):

* section 1 (items 1 to 15): the field GF(2^8) with x^8 + x^4 + x^3 + x^2
  + 1 (item 5) and the generator g = {02} (item 13), and at most 255 data
  blocks;
* section 2: P = D_0 + ... + D_(n-1) (equation 1), Q = g^0 D_0 + ... +
  g^(n-1) D_(n-1) (equation 2); one data block and P lost: D_x = (Q + Q_x)
  g^(-x) (equations 3 to 5); two data blocks lost: equations 6 to 20, with
  A and B of equations 17 and 18;
* section 3: Q by Horner's rule (equation 21).

The field arithmetic is bend-osdev-gf's GF(2^8) (`Gf8.raid6()`), and P is
bend-osdev-xorblocks' XOR. No kernel source was read. Section 4 (finding a
single corrupt block from the syndromes) is not implemented; see
Extension points.

## Files

| File | Holds |
|---|---|
| `raid6.bend` | `Raid6Spec` (the field), `Raid6Stripe`, the syndromes P and Q, `encode`, blocks by index, `uniform` |
| `scale.bend` | `Raid6.scale`: every byte of a block times one field element |
| `recover.bend` | `Raid6Lost`, `Raid6Error`, `check`, `erase`, the coefficients A and B, `recover` |

## API

| Def | Meaning |
|---|---|
| `Raid6Spec{field}`, `Raid6.spec()` | the field (a bend-osdev-gf `Gf8Field`; g is its generator); the paper's, 0x11D with g = {02} |
| `Raid6.field(s)`, `Raid6.gen(s)`, `Raid6.gpow(s, i)` | the field, g, and g^i |
| `Raid6.p(ds)`, `Raid6.q(s, ds)` | the syndromes of the data blocks `ds` (`List<&2, Octets>`) |
| `Raid6Stripe{data, p, q}`, `Raid6.encode(s, ds)` | a stripe; the stripe of `ds` with its syndromes |
| `Raid6.block(ds, i)`, `Raid6.set_block(ds, i, b)`, `Raid6.width(ds)` | data block i (empty past the end), block i replaced, the number of data blocks |
| `Raid6.uniform(ds)` | whether every data block has the first one's length |
| `Raid6.scale(f, c, b)` (`scale.bend`) | each byte of `b` times `c` in the field `f` |
| `Raid6Lost`: `Raid6LostNone`, `Raid6LostData{x}`, `Raid6LostP`, `Raid6LostQ`, `Raid6LostDataData{x, y}`, `Raid6LostDataP{x}`, `Raid6LostDataQ{x}`, `Raid6LostPQ` | which blocks are lost |
| `Raid6Error`: `Raid6TooManyDisks{n}`, `Raid6BadIndex{i}`, `Raid6SameIndex{i}` | why a loss cannot be recovered |
| `Raid6.max_disks()` | 255 |
| `Raid6.check(n, lost)` | `None` if `lost` can be recovered in a stripe of `n` data blocks, else `Some` of the reason |
| `Raid6.erase(st, lost)` | the lost blocks set to the empty block |
| `Raid6.coef_a(s, x, y)`, `Raid6.coef_b(s, x, y)` | A and B of equations 17 and 18 |
| `Raid6.recover(s, st, lost)` | `Done` of the stripe with the lost blocks rebuilt (their contents in `st` are never read), or `Fail` of a `Raid6Error` |

Blocks are `Octets`. A stripe's blocks should all have the same length;
blocks of unequal length count as padded with zero bytes (XOR's padding),
and the laws about recovery assume equal lengths.

## Extension points

* **The field and generator:** `Raid6Spec` takes any `Gf8Field`; the
  syndromes and their splitting laws hold for every field. Recovery needs
  the generator's powers g^0 .. g^254 to be distinct, which the laws prove
  for the paper's field; another field with a generator of order 255 works
  the same way.
* **Fast paths:** scaling is bend-osdev-gf's bit-level reference
  multiplication, a byte at a time. The paper's section 3 (multiplication
  by {02} on whole words) and gf's log/exp tables (`tables.bend`) are faster
  ways to compute the same bytes; either can be added beside `Raid6.scale`
  and tied to it by a law or a differential test.
* **More syndromes:** the paper's section 5 (more than two parity blocks)
  is one more syndrome with another generator, built the same way as Q.
* **Corruption:** section 4 (locating one corrupt block from P* and Q*)
  needs only `p`, `q`, `scale` and gf's logarithm, and is not implemented
  yet.

## Laws

`LAWS.bend`, proved for every input:

* `p_cons`, `q_cons`: P is the XOR of the data blocks, and Q is computed by
  Horner's rule (equations 1, 2 and 21);
* `p_split`, `q_split`: for every block index x and every field, P = D_x +
  P_x and Q = g^x D_x + Q_x, where P_x and Q_x are computed with D_x set to
  zero (equations 3 and 6);
* `scale_xor`, `scale_scale`, `scale_add`, `scale_one`, `scale_zero`,
  `scale_len`: scaling distributes over XOR, c (d B) = (c d) B, c B + d B =
  (c + d) B, 1 B = B, 0 B is zeros, and the length is kept, for every field;
* `gpow_nonzero`, `gpow_distinct`: in the paper's field, g^x is never zero,
  and g^x, x < 255, are distinct (section 1, item 13);
* `recover_any`: for every list of data blocks of equal length and every
  loss of up to two blocks that `Raid6.check` accepts, recovering the
  stripe with the lost blocks erased gives the stripe back;
* `recover_ignores`: recovery does the same whatever the lost blocks hold,
  so overwriting them with anything changes nothing;
* vectors: {02}^8 = {1d}, {02}^4 = {10}, log {10} = 4, and A {8d} = A {02}^7
  + A {02}^3 + A {02}^2 + A for A = {57} (the paper's examples, section 1,
  items 11 and 14), P and Q of a small stripe, rebuilding two data blocks
  of it, and each of `check`'s refusals.

The proofs use bend-osdev-gf's ring laws, its inverse law for the paper's
field (`mul_inv_rs`) and its public bit representation `Gf8Bits`;
xorblocks' laws (including `xor_list`, the bytewise meaning of XOR); and
bytes' interface laws. That g^1 .. g^254 are not 1 is computed once, by a
walk through the powers (`r6p.walk`), from which the distinctness of g^x
for every x < 255 follows by induction and cancellation.

## Tests

`check.bend` checks the paper's examples, P and Q of a small stripe, and,
on a stripe of seven 64-byte blocks, every one of the 42 ordered pairs of
lost data blocks, every single data loss with and without P or Q, and the
losses of P, Q or both, with the lost blocks overwritten with junk first;
two losses on a stripe of four 30,000-byte blocks; and each of `check`'s
refusals. `ref/run.sh` (191 cases with the default seed) compares P, Q and
recovery after each kind of loss, on random stripes of 1 to 12 blocks,
with an independent model written in `ref/gen.py` from the paper (Q as a
sum of terms rather than by Horner's rule, and recovery by equations 5 and
16 to 20, each checked against the original blocks).

## Dependencies

bend-osdev-u32, in the proofs only: its laws of `Nat` arithmetic and words'
values (`LAWS.bend`) and the order of `Nat` and words (`LAWS_order.bend`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 191 cases match, `scripts/deps.sh` passes.
