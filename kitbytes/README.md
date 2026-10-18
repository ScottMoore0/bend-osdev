# bend-osdev-kitbytes

An adapter between bend-osdev's byte strings (`Octets`, from
bend-osdev-bytes) and bend-kit's `Bytes` (bend-kit-bytes@0.3.2.0, an
array-backed buffer packed four bytes to a word).

The core bend-osdev packages never depend on another library's types. A
program that uses both bend-osdev and bend-kit converts at its edges, with this
package.

## API

| Def | Meaning |
|---|---|
| `of_octets(o)` | a bend-kit buffer holding the bytes of `o` |
| `to_octets(b)` | the bytes of a bend-kit buffer, handed back beside the buffer (it is affine) |
| `round_trip(o)` | `of_octets` then `to_octets`, dropping the buffer |

## Extension points

* Adapters for other libraries' byte types belong in packages like this one,
  never in the core packages.

## Laws

`LAWS.bend` has **vectors
only**: round trips on text, on the byte values at the edges (0, 127, 128,
255) and on the empty string, and a buffer built by bend-kit's own
`from_string`. A proof for every input would have to reason about bend-kit's
array internals, which bend-osdev does not do.

## Sizes

Every conversion is a tail-recursive loop, so there is no length limit
beyond memory. Measured on a native build (`bend file.bend -o prog`,
Bend 2.0.37, WSL2), with 1 MB of pseudo-random bytes, each run including
building the input:

| Run | Time, native | Peak RAM, native | JavaScript lane, before |
|---|---|---|---|
| building the 1 MB input alone | 0.05 s | 84 MB | |
| `of_octets`, 1 MB | 0.12 s | 85 MB | 6.9 s, 1.35 GB |
| `round_trip` (both ways), 1 MB | 0.14 s | 85 MB | 9.6 s, 1.86 GB |

Most of the memory is the `Octets` itself (about 80 bytes per byte held,
natively)
and its list form. `check.bend` round-trips 100 KB as a regression test.
Before this, `of_octets` overflowed the JavaScript lane's stack at 64 KB (it took
the length through bytes' structural `B.len`; it now uses `B.len.fast`).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes.
