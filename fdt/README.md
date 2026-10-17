# bend-osdev-fdt

The flattened devicetree: reading and writing the Devicetree Blob (DTB)
format that firmware and boot loaders hand to an operating system to
describe the machine. Fdt.parse checks a blob and reads its header,
memory reservations and tree. Fdt.build writes a tree back as a blob. There
are typed decoders for property values, and lookups by path, alias and
phandle. Byte strings are `Octets` (bend-osdev-bytes); 64-bit values are
`W64` (bend-osdev-word64).

## Specification

* *Devicetree Specification*, release v0.4 (devicetree.org),
  chapter 5 "Flattened Devicetree (DTB) Format": the header (5.2), the
  memory reservation block (5.3), the structure block and its tokens (5.4)
  and the strings block (5.5). Chapter 2 gives the property value types
  (2.2.4), path names and unit addresses (2.2.1, 2.2.3), the standard
  properties (2.3: `#address-cells`, `#size-cells`, `reg`, `phandle`) and
  `/aliases` (3.3). The specification is published under the Apache 2.0
  licence. The package was written from the specification alone; no libfdt
  or dtc source was read.

A blob is a 40-byte header, then the reservation block (8-aligned), the
structure block (4-aligned) and the strings block, at the offsets the header
gives, all big-endian. The header holds `magic` (0xd00dfeed), `totalsize`,
`off_dt_struct`, `off_dt_strings`, `off_mem_rsvmap`, `version`,
`last_comp_version`, `boot_cpuid_phys`, `size_dt_strings` and
`size_dt_struct` (from version 17). The structure block is a run of tokens:
`FDT_BEGIN_NODE` (a NUL-terminated name, padded to 4 bytes), `FDT_PROP`
(length, offset of the name in the strings block, value padded to 4 bytes),
`FDT_END_NODE`, `FDT_NOP`, and `FDT_END` last.

Choices this package makes where the specification leaves room:

* **Version.** It writes version 17 with `last_comp_version` 16. By
  default it reads versions 16 and 17. For version 16, which has no
  `size_dt_struct`, the structure block runs from `off_dt_struct` to
  `totalsize`, and bytes after `FDT_END` are not read. Other version
  policies are options (below).
* **Layout written.** Header, then the reservation block at offset 40, then
  the structure block, then the strings block, with no gaps. `totalsize` is
  exact.
* **Strings block written.** `Fdt.build` writes each property's name in
  turn, repeats included (the "simple" block; the round-trip law is proved
  for it). `Fdt.build_with(FdtStringsDedup{}, ...)` writes each name's bytes
  once. A name whose bytes and NUL already occur in the block, also as the
  tail of a longer name, gets that offset, as dtc does. For the same tree,
  reservations and boot CPU its output is byte-identical to `dtc -I dts
  -O dtb` (checked on the spec example and on random trees).
* **Checks on reading.** The magic; an accepted version; `last_comp_version`
  at most 17 and at most `version`; `totalsize` from 40 to the blob's
  length (a blob may be longer than `totalsize`); the reservation block
  8-aligned, after the header, within `totalsize`; the structure block
  4-aligned, after the header, ending within `totalsize`; the strings block
  after the header and within `totalsize`. Blocks are not checked for
  overlap, and padding bytes are not checked for zeros. For version 17 and
  later, `FDT_END` must be the structure block's last token.
* **Names.** Node and property names are bytes; the character sets of
  section 2.2 are not enforced.

## Files

| File | Holds |
|---|---|
| `fdt.bend` | the entry: `FdtOptions`, `FdtBlob`, `Fdt.parse`, `Fdt.build`, `Fdt.build_with`, `Fdt.buildable` |
| `header.bend` | the header: `FdtHeader`, its encoding, decoding and checks, `FdtVersions` |
| `rsvmap.bend` | the memory reservation block: `FdtRsv` |
| `structure.bend` | the structure block's tokens, `FdtToken`, and the streaming lexer `FdtLexer` |
| `tree.bend` | the tree: `FdtNode`, `FdtProp`, tokens and strings block to tree and back, `FdtTreeRules`, `FdtStrings` |
| `props.bend` | typed property values: u32, u64, string, stringlist, cells, reg |
| `path.bend` | lookups: property, child, path, alias, phandle, cells, reg |
| `error.bend` | `FdtError` |
| `example.bend` | `FdtExample`: the sample tree used by the tests |
| `layout.bend` | internal: sizes, padding, alignment, NUL scanning |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test |

## Public interface

`fdt.bend`:

| Def or type | Meaning |
|---|---|
| `FdtBlob{version, boot_cpuid_phys, reservations, root}` | what a blob holds |
| `FdtOptions{versions, rules}`, `FdtOptions.default()` | what a reader accepts; the default reads versions 16 and 17, skips NOPs, and requires properties before child nodes |
| `Fdt.parse(opts, o) -> Result<…, FdtError, FdtBlob>` | check and read a blob. Checked in order: the magic (`FdtBadMagic`; `FdtTooShort` below 4 bytes, or below 40 after a good magic), the header, the reservation block, the structure block's tokens, the tree. |
| `Fdt.build(root, rsv, boot) -> Octets` | a version-17 blob with the simple strings block |
| `Fdt.build_with(how, root, rsv, boot)` | the same, with `FdtStringsSimple{}` or `FdtStringsDedup{}` (dtc's layout) |
| `Fdt.buildable(root, rsv) -> Bool` | the trees `Fdt.build` can write so that `Fdt.parse` reads them back: names without NULs, values and blob shorter than 4 GiB, no reservation equal to the `0, 0` terminator |

`header.bend`: `FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings,
off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys,
size_dt_strings, size_dt_struct}` (all `U32`); `FdtHeader.encode(h) ->
Octets`; `FdtHeader.decode(o) -> Result<…, FdtHeader>` (the 40 bytes as
they are, `FdtTooShort` if fewer); `FdtHeader.check(versions, h, len) ->
Result<…, Unit>` (the checks above, for a blob of `len` bytes);
`FdtHeader.magic_value()`, `FdtHeader.size()`; `FdtVersions`:
`FdtV16V17{}` (the default, `FdtVersions.default()`), `FdtV17Only{}`,
`FdtVCompatible{}` (any version from 16 whose `last_comp_version` is at most
17, as section 5.2 lets a later version declare itself readable).

`rsvmap.bend`: `FdtRsv{address, size}` (`W64`s); `FdtRsv.encode(rs)`
(the entries, then the terminator); `FdtRsv.decode(o)` (the entries before
the terminator, `FdtRsvUnterminated` if the bytes run out first);
`FdtRsv.is_end(r)`, `FdtRsv.valid_all(rs)`.

`structure.bend`: `FdtToken`: `FdtTokBegin{name}`, `FdtTokEnd{}`,
`FdtTokProp{nameoff, value}`, `FdtTokNop{}` (`FDT_END` is the end of the
list); `FdtToken.encode_all(ts)` (the tokens, then `FDT_END`);
`FdtToken.decode_all(o)`; `FdtToken.valid(t)`, `FdtToken.valid_all(ts)`;
the streaming lexer `FdtLexer.start()`, `FdtLexer.feed(st, o)`,
`FdtLexer.finish(strict, st)` (`strict`: refuse bytes after `FDT_END`).
`FdtLexer`'s fields are internal.

`tree.bend`: `FdtNode{name, props, children}`, `FdtProp{name, value}` (all
`Octets`; the root's name is empty); `FdtNode.to_tokens(root)` and
`FdtNode.to_tokens_with(how, root) -> FdtFlat{tokens, strings}`;
`FdtNode.of_tokens(rules, tokens, strings)`, `FdtNode.of_flat(rules, flat)
-> Result<…, FdtNode>`; `FdtTreeRules{nop_ok, props_first}` and
`FdtTreeRules.default()` (both true); `FdtStrings`: `FdtStringsSimple{}`
(`FdtStrings.default()`), `FdtStringsDedup{}`; `FdtNode.names_ok(root)`,
`FdtNode.wf(root)` (names without NULs, values below 4 GiB),
`FdtNode.flat_ok(root)` (names without NULs, strings block below 4 GiB);
`FdtNode.dump(root)` (one line of text, for debugging).

`props.bend`: `FdtProp.u32` / `of_u32`, `FdtProp.u64` / `of_u64`,
`FdtProp.string` / `of_string` (`Octets`, without the NUL),
`FdtProp.text` / `of_text` (the same as `String`), `FdtProp.strings` /
`of_strings` (a stringlist), `FdtProp.cells` / `of_cells` (32-bit cells),
`FdtProp.reg(ac, sc, v)` / `of_reg(ac, sc, rs)` (`FdtReg{address, size}`
pairs with `ac` address cells and `sc` size cells, each 0, 1 or 2),
`FdtProp.string_ok(s)`, `FdtProp.strings_ok(ss)`. A decoder fails with
`FdtBadLength` (a u32 value that is not four bytes, a u64 value that is not
eight, cells that are not a whole number of four bytes or of pairs),
`FdtBadString` (no NUL at the end, or a NUL inside a string) or
`FdtBadCells` (more than 2 cells, or none at all).

`path.bend`: `FdtNode.prop(n, k)`, `FdtNode.get(n, "name")` (the first
property with that name); `FdtNode.child(n, k)` (the child named `k`, or,
if `k` has no `@`, the first child whose name without its unit address is
`k`); `FdtNode.find(root, path)` (`"/cpus/cpu@0"`; a path without a leading
`/` starts with an alias from `/aliases`); `FdtNode.find_prop(root, path,
name)`; `FdtNode.find_phandle(root, ph)` (`phandle`, or the older
`linux,phandle`; the first in depth-first order); `FdtNode.address_cells(n)`
and `FdtNode.size_cells(n)` (2 and 1 when absent or not a `<u32>`);
`FdtNode.reg(parent, node)`, `FdtNode.find_reg(root, path)` (the `reg`
pairs, with the parent's cell counts).

`error.bend`: `FdtError`, one constructor per failure: `FdtTooShort`,
`FdtBadMagic`, `FdtBadVersion`, `FdtBadLastComp`, `FdtBadTotalSize`,
`FdtBadRsvmap`, `FdtBadStruct`, `FdtBadStrings`, `FdtRsvUnterminated`,
`FdtBadToken{tag}`, `FdtTruncated`, `FdtAfterEnd`, `FdtUnbalanced`,
`FdtNoRoot`, `FdtPropAfterNode`, `FdtNopRefused`, `FdtBadNameOff`,
`FdtBadLength`, `FdtBadString`, `FdtBadCells` (each documented in the
file).

`example.bend`: `FdtExample.tree()`, `FdtExample.rsv()`: a sample board
(two CPUs, memory, a serial port, `/chosen`, `/aliases`), modelled on the
example devicetree in chapter 2 of the specification.

Everything else (the `hdr.*`, `rsv.*`, `tok.*`, `toks.*`, `lx.*`,
`flat.*`, `prop.*`, `pstrs.*`, `strs.*`, `ptoks.*`, `ftoks.*`, `pnames.*`,
`names.*`, `pvalues.*`, `values.*`, `dedup.*`, `tb.*`, `pr.*`, `lk.*`,
`parse.*`, `build.*`, `buildable.ref` and `fdt.*` defs, the `*.ref`
reference forms, `FdtFrame`, `FdtTb`, `LxMode`, …) is internal.

## Extension points

* **Options with named defaults.** `FdtOptions` picks the versions a reader
  accepts (`FdtVersions`) and the tree rules (`FdtTreeRules`: NOPs skipped
  or refused, properties before children required or not).
  `Fdt.build_with` picks the strings-block layout (`FdtStrings`). The
  round-trip law holds for every `FdtOptions`.
* **The layers can be used on their own.** `FdtHeader`, `FdtRsv`,
  `FdtToken` / `FdtLexer` and `FdtNode.of_tokens` / `to_tokens` each have
  their own encoder, decoder and law. For example, a boot loader that only
  needs the memory reservations reads the header and the reservation block,
  and a tool can rewrite the token stream (insert NOPs, drop nodes) without
  building a tree.
* **Streaming.** The structure block can arrive in pieces:
  `FdtLexer.feed` takes any split, and a law says that feeding `a` then `b`
  is feeding `a ++ b`. `Fdt.parse` itself takes the whole blob in one
  `Octets`, since the header's offsets point anywhere in it.
* **Reference and fast forms.** The structural forms the proofs compute
  through (`parse.p1`, `build.simple`, `toks.list`, `flat.toks`,
  `flat.strs`, `pr.cells.list`, `pr.sl.list`, the `*.ref` checks) stay
  beside the tail-recursive forms the package runs, and `PROOF.bend`
  proves each pair equal for every input (Laws). A faster form (an index
  of the strings block by offset, say) can replace a fast form, as long as
  its lemma is proved again; the laws do not change.
* **New property types** are decoders over `Octets` beside those in
  `props.bend`; `FdtProp.cells` is the base for the prop-encoded arrays
  (`interrupts`, `ranges`, …).
* **Not covered yet:** writing version 16 or padding (`dtc -p`/`-S`),
  checking that the blocks do not overlap, and `ranges` address
  translation.

## Laws

`LAWS.bend` (a draft, not yet reviewed by the maintainer) has 68 laws.

The package runs tail-recursive forms of its writers, its reader's slicing
and its checks (the `.fast` and `.go` defs; see Speed and size). The proofs
compute through structural reference forms, which are easier to reason
about, and `PROOF.bend` proves each fast form equal to its reference for
every input (`half_fast`, `u32n_fast`, `fits_fast`, `nonul_fast`,
`toks_fast`, `valid_fast`, `valid_all_fast`, `strs_fast`, `ftoks_fast`,
`names_fast`, `wf_fast`, `flat_ok_fast`, `layout_fast`, `build_fast`,
`buildable_fast`, `parse_fast`, `strings_ok_fast`, `sl_fast`,
`cells_fast`). Each law's proof first rewrites the public defs to their
references with these lemmas, so the laws hold for the code as it runs.

**Properties, for every input (15):**

* `parse_build`: for every options value, tree, reservation list and boot
  CPU that `Fdt.buildable` admits, `Fdt.parse(opts, Fdt.build(root, rsv,
  boot)) == Done{FdtBlob{17, boot, rsv, root}}`. No normalisation is
  needed: on that class the tree comes back exactly. The proof composes the
  layer laws below. Every header check is shown to pass, and every size and
  offset to survive its 32-bit field, using only the hypothesis that the
  whole blob is under 4 GiB (sub-lengths are bounded by monotonicity
  lemmas). The `Octets` steps use bytes' interface laws (`octets_to_of`,
  `octets_of_to`, `octets_append_list`, …) and `W64` steps use word64's
  `parts_of`.
* `header_round_trip`: `FdtHeader.decode(FdtHeader.encode(h)) == Done{h}`;
  `bad_magic`: every blob whose first four bytes are not 0xd00dfeed is
  refused with `FdtBadMagic`, whatever follows, for every option value;
* `rsv_round_trip`: every reservation list without a `0, 0` entry;
* `lexer_streaming`: `feed(feed(st, a), b) == feed(st, append(a, b))`;
  `tokens_round_trip`: `FdtToken.decode_all(encode_all(ts)) == Done{ts}`
  for valid tokens;
* `tree_round_trip`: `FdtNode.of_flat(rules, FdtNode.to_tokens(root)) ==
  Done{root}` for every rules value and every tree `flat_ok` admits;
* `u32_round_trip`, `u64_round_trip`, `string_round_trip` (strings without
  NULs), `strings_round_trip` (lists of them), `cells_round_trip`;
* `prop_head`, `child_head`: a node's first property and first child are
  found by name; `find_root`: `FdtNode.find(root, "/") == Some{root}`.

**Satisfiability witnesses (7):** each hypothesis above holds for an
ordinary input (`buildable_example`, `flat_ok_example`, …), so no law is
vacuous.

**Vectors (46):** the sample tree's blob as `Fdt.build` writes it, and the
708 bytes `dtc` 1.7.0 writes for the same source, which
`Fdt.build_with(FdtStringsDedup{}, …)` reproduces exactly and `Fdt.parse`
reads back as the sample tree. Lookups in the sample tree: a path, a base
name, an alias, a missing node, `reg` through the parent's cells,
`/chosen`'s `bootargs`, a phandle. Property decoders, both well-formed and
malformed. One blob for each way `Fdt.parse` can refuse one, each with the
error ref/gen.py's reader gives. The option variants: NOPs refused,
properties after children allowed, version 16 refused by
`FdtV17Only`.

The `FdtStringsDedup` writer, `FdtNode.find`'s alias and base-name rules,
`find_phandle` and the `reg` decoder are covered by vectors and the
differential test, not by laws for every input.

## Tests

`ref/run.sh` (839 cases) compares the package with `ref/gen.py`, an
independent writer and reader written in Python from the same
specification, and with `dtc` and `fdtdump` (device-tree-compiler 1.7.0),
which are third-party:

* **large** (3): a tree of 600 devices built by a generator on both sides
  (73 KB with the simple strings block, 58 KB deduplicated, past the sizes
  the package overflowed at before its list code was made
  tail-recursive). Both writers' bytes must match the Python writer's (as
  their length and FNV-1a hash), the deduplicated blob must be
  byte-identical to `dtc`'s, and `Fdt.parse` must read it back.
* **build** (60): 30 random trees with reservations and boot CPUs. Each
  must give the bytes the Python writer gives, with both strings layouts.
  The deduplicated blob must also be byte-identical to what `dtc -I dts -O
  dtb` writes for the same tree as a `.dts` source.
* **parse** (147): 140 blobs from the Python writer (some version 16, with
  NOPs, gaps between blocks, bytes after `totalsize`, either strings
  layout), half of them corrupted (truncation, magic, version,
  `last_comp_version`, `totalsize`, offsets, sizes, a random byte, a token,
  a nameoff, an `FDT_END_NODE`, a reservation entry). Plus 7 option
  variants. `Fdt.parse` must give the tree, or the error, the Python reader
  gives.
* **dtc** (25): random `.dts` sources compiled by `dtc`. `Fdt.parse` must
  read the tree the source describes.
* **values** (360): `u32`, `u64`, `string`, `strings`, `cells` and `reg`
  against the Python decoders.
* **lookups** (244): paths (exact, base name, missing), aliases and
  phandles in random trees.
* **post-check** (60 blobs): every blob `Fdt.build` and `Fdt.build_with`
  wrote above is read by `dtc -I dtb` (and must come back as the same
  tree), decompiled by `dtc -I dtb -O dts` (every node named), and dumped
  by `fdtdump`.

The Python reference **shares an author with the package**: it was written
from the same reading of the specification, so it can catch slips of
implementation but not a shared misreading. `dtc` and `fdtdump` do not
share that weakness, and they agree with the package on every blob above.
`run.sh` exits 77 (skip) when `python3` is missing. When `dtc` or
`fdtdump` is missing it still runs the Python cases and then exits 77; CI
needs the apt package `device-tree-compiler`.

## Limitations

* The proofs reach `Octets` only through bytes' interface laws and its list
  layer (with its fast-form laws `len_fast`, `take_fast` and
  `append_fast`), and `W64` only through word64's `parts_of`, with one
  exception.
  The proof of `rsv_round_trip` (and so of `parse_build`) computes that the
  all-zero entry is the terminator, `FdtRsv.is_end` of the two words read
  from zero bytes, through word64's definitions. This is a closed
  computation, like a vector. The header, token and property proofs
  compute through `B.be32`, `B.mask` and `B.be32_at` on words split into
  their bits, as bytes' own proofs do. These proofs would need revisiting
  if those packages' representations changed; the laws would not change.
* `Fdt.build` does not refuse a tree that `Fdt.buildable` rejects (a name
  with a NUL, a blob of 4 GiB or more); such a blob does not read back.

## Speed and size

The package works on `Octets`, and has no length limit of its own: every
loop over a blob's bytes, its tokens, its strings block, a property's value
or a list of strings or cells is a tail call (bytes' `Octets` operations and
its fast list forms, and this package's `.fast` and `.go` defs). What still
recurses is bounded by the tree: the writers and the checks recurse into a
node's children (the tree's depth), and the lookups (`FdtNode.find`,
`find_phandle`, `child`, `prop`) and `FdtNode.dump` recurse once per
sibling or property: the lookups pass with 10,000 siblings under one node,
and `dump` with 5,000. The
reservation block's writer and `FdtRsv.valid_all` recurse once per
reservation (there are a handful). The reader keeps an explicit stack, so a
deep tree does not deepen its recursion.

Measured with Bend 2.0.37 (`bend file.bend`, WSL2), on generated trees of
buses and devices (four properties each), times and peak memory for the
whole run, building the tree included:

| Input | Operation | Time | Peak RAM |
|---|---|---|---|
| 1,000 nodes, 130 KB | `Fdt.build`; `Fdt.parse` and build again | 1.1 s; 2.8 s | 300 MB; 500 MB |
| 5,000 nodes, 654 KB | `Fdt.build` | 5.5 s | 930 MB |
| 5,000 nodes, 501 KB | `Fdt.build_with(FdtStringsDedup{}, …)` | 3.3 s | 840 MB |
| 5,000 nodes, 650 KB | `Fdt.build`, then `Fdt.parse` | 9 to 18 s | 1.3 GB |
| 5,000 nodes | `FdtToken.decode_all` (the lexer), 30,408 tokens | 5.9 s | 1.2 GB |
| 10,102 nodes, 1,001,053 bytes | `Fdt.build_with(FdtStringsDedup{}, …)`: byte-identical to `dtc -I dts -O dtb` | 8.4 s | 1.8 GB |
| 10,000 siblings | `FdtNode.find`, `find_phandle` | 5.7 s | 1.6 GB |
| a 500 KB property value | `Fdt.build`, then `Fdt.parse` | 2.9 s | 1.4 GB |
| 100,000 cells; 50,000 strings | `FdtProp.of_cells`; `of_strings` then `strings` | 1.8 s | 440 MB; 480 MB |

Before these loops were made tail-recursive, a 300-node tree (39 KB) did
not parse and a 1,000-node tree did not build: Bend 2.0.37's runtime
overflows its stack after some 10,000 to 40,000 nested calls.

The limit now is memory: an `Octets` costs about 940 bytes of RAM per byte
in bytes' current representation, and the reader holds the blob, its byte
list and the tree at once, so reading a 1 MB blob would need more than
2 GB (not run here, on a shared machine). That will shrink when bytes makes
`Octets` compact.

Two costs grow faster than the blob. The reader finds each property's name
by walking the strings block from its start, so its time grows with the
number of properties times the size of the strings block: dtc's
deduplicated blobs have small strings blocks, but the simple layout repeats
every name (the 650 KB blob above has a 125 KB strings block and 20,000
properties). And the deduplicating writer searches the block so far for
each name, so a tree whose property names are all different costs time
proportional to the square of its strings block. An index of the strings
block by offset would remove both. Sizes and offsets are `Nat`.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 839 cases match (with dtc 1.7.0 and
fdtdump installed), `scripts/deps.sh fdt` ok.
