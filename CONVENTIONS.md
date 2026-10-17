# Conventions

These rules keep the packages consistent, so they compose. A change to one of
them is a change to every package.

## Packages

- A package lives in its own directory `x/`, with entry file `x/x.bend`, and is
  published on BendHub as `bend-osdev-x`.
- Every package directory holds:
  - `x.bend`: the code;
  - `LAWS.bend`: the claims (see Laws below);
  - `PROOF.bend`: imports `LAWS.bend` and proves each law;
  - `check.bend`: a runnable `main` whose output is fixed by the `#|` lines at
    the end of the file;
  - `README.md`: what the package does, and the specification it follows;
  - `VERSION`: four numbers, `0.1.0.0` to start; a change to `x.bend` raises it;
  - `LICENSE`: the MIT licence, beside the entry file, so `--publish` takes it;
  - optionally `ref/`: a differential test against an independent
    implementation (see Testing).
- A package imports its siblings by relative path (`../bytes/bytes.bend`)
  until they are published; at publishing time those become hub imports.

## Names

- Base's names are global, and a redeclared Base name is refused
  (bendlang/bend#1042). So a package never declares a type, constructor or def
  under a bare name Base may add later: no `U8`, `U16`, `U64`, `I64`, `F64`,
  `U128` or `Byte`. Types get package-specific names (`W64`, `CpioEntry`).
- Defs are named `Type.verb` or `module_verb`, as Base does.

## Bytes

- A byte string is a `List<&2, U32>` whose elements are 0 to 255: Base's own
  I/O (`File.read_bytes`, `TCP.send_bytes`) uses this shape.
- Functions that read a byte string answer `Maybe` (or a result type) when the
  input may be malformed; they never assume an element is below 256 without
  masking it.
- Shared helpers (slicing, big- and little-endian fields) live in
  `bend-osdev-bytes`; packages use them instead of writing their own.

## 64-bit values

- Only through `bend-osdev-word64` and its type `W64`. No package uses another
  64-bit type directly. When Base gains a native `U64`, only `word64` changes.

## Specifications and licensing

- Every package is MIT-licensed and written from a public specification, which
  its `README.md` cites. Code is never translated from, or written while
  reading, GPL source (the Linux kernel, or GPL reference implementations).
- A package whose format has no independent specification says so in its
  `README.md`, and is not written until that is resolved.

## Laws

- Bend's convention is that a human writes `LAWS.bend` and the AI writes
  `PROOF.bend` and the code. In this repository the laws were drafted by an AI,
  so every `LAWS.bend` opens with `# DRAFT: not yet reviewed by the maintainer`
  until the maintainer has read and accepted it.
- Laws come in two kinds:
  - **vectors**: the specification's own test values, as equalities proved by
    computation (`{==}`);
  - **properties**: claims for every input (a round trip, an invariant, a
    bound), proved by induction.
- `bend x/PROOF.bend` must print `ALL PROOFS CHECK`. `--verdict` (the Lean
  kernel) is run too, and a package's `README.md` records whether it passes.

## Testing

- `scripts/check.sh x` runs, for package `x`: the proofs (`--check-only` on
  `PROOF.bend`), `check.bend` against its `#|` lines, and `ref/run.sh` if the
  tools it needs are installed.
- A differential test compares the package against an independent
  implementation on many inputs: a system tool (`readelf`, `sgdisk`,
  `debugfs`, `xz`) or a library outside this repository (Python's `zlib`,
  `lzma`, `cryptography`). A package with no independent reference says so,
  and tests against hand-built examples from its specification.

## Bend version

- The packages are checked with the Bend release in `BEND_VERSION`.
  `scripts/install-bend.sh` installs that exact release and verifies its
  hash; CI uses it.
