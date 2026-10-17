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

`LAWS.bend` (a draft, not yet reviewed by the maintainer) has **vectors
only**: round trips on text, on the byte values at the edges (0, 127, 128,
255) and on the empty string, and a buffer built by bend-kit's own
`from_string`. A proof for every input would have to reason about bend-kit's
array internals, which bend-osdev does not do.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes.
