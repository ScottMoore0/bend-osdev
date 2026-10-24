# Conventions

These rules keep the packages consistent, so they compose, and keep each one
easy to change, restructure, customise and reuse without breaking the others.
A change to one of these rules is a change to every package.

## Packages

- A package lives in its own directory `x/`, with entry file `x/x.bend`, and is
  published on BendHub as `bend-osdev-x`.
- Every package directory holds:
  - `x.bend` (and, where a package has several concerns, one file per concern;
    see below);
  - `LAWS.bend`: the claims (see Laws below);
  - `PROOF.bend`: imports `LAWS.bend` and proves each law;
  - optionally further pairs `LAWS_<part>.bend` and `PROOF_<part>.bend`,
    and lemma files `proof_<name>.bend` (see Laws below);
  - `check.bend`: a runnable `main` whose output is fixed by the `#|` lines at
    the end of the file;
  - `README.md`: what the package does, the specification it follows, and its
    extension points (see below);
  - `VERSION`: the version (see Versions below);
  - `DEPS`: the packages it may import, one per line (see Dependencies);
  - `LICENSE`: the MIT licence, beside the entry file, so `--publish` takes it;
  - optionally `ref/`: a differential test against an independent
    implementation (see Testing).
- A package imports its siblings by relative path (`../bytes/bytes.bend`);
  `scripts/publish.py` publishes a copy in which those become hub imports
  (`bend-osdev-bytes@0.1.0.0/bytes.bend`), dependencies first, and
  `scripts/publish.py --check` checks that copy against a local stand-in for
  the hub before anything is published.

## One file per concern

- A package with more than one concern puts each in its own file, so a user
  imports only what they need: `partition/mbr.bend` and `partition/gpt.bend`,
  not one file holding both. Bend imports do not re-export, so the entry file
  is the main concern, not an index; the README lists every file and what it
  holds.

## Interfaces

- **Public and internal.** A package's public interface is the defs and types
  its README lists. Everything else is internal and may change at any time.
  Other packages use only the public interface: never another package's
  internal helpers, and never the inside of its types (no matching on another
  package's constructors, unless its README says the type is open).
- **Opaque types.** A type whose representation may change (`W64`, `Octets`)
  is used only through its package's defs, so the representation can change
  without touching any other package.
- **Parameters instead of fixed choices.** Where the domain has real choices
  (a CRC's polynomial, a block device's read function, a size limit), a package
  takes them as a parameter record or a template argument (`~dev`), with the
  usual choice provided as a named default. A template argument is
  specialised at compile time, so it costs nothing at run time.
- **Streaming.** Where data can arrive in pieces, a package offers
  `start`/`update`/`finish` (or an incremental parser) beside the one-shot
  function, as `crc` does.

## Errors

- A function that can fail on bad input answers `Result<&2, &2, E, A>` (Base's
  `Fail{error}` / `Done{value}`), where `E` is the package's own error type
  naming each failure (`CpioError`: `CpioTooShort`, `CpioBadMagic`, …), so a
  caller can tell failures apart. Low-level field readers (in `bytes`) answer
  `Maybe`.
- Constructor names are global too, so error constructors carry the package
  prefix.

## Names

- Base's names are global, and a redeclared Base name is refused
  (bendlang/bend#1042). So a package never declares a type, constructor or def
  under a bare name Base may add later: no `U8`, `U16`, `U64`, `I64`, `F64`,
  `U128`, `Byte`, `Bytes`, or `Word.lo`-style helpers. Types get
  package-specific names (`W64`, `Octets`, `CpioEntry`).
- Defs are named `Type.verb` or `module_verb`, as Base does.

## Bytes

- Byte strings are `Octets` (from `bend-osdev-bytes`): an opaque type whose
  bytes are 0 to 255. Public interfaces take and answer `Octets`; a package
  never depends on how `Octets` stores its bytes.
- `Octets.of_list` and `Octets.to_list` convert to and from `List<&2, U32>`,
  the shape Base's own I/O uses (`File.read_bytes`, `TCP.send_bytes`).
  `of_list` masks each element to 8 bits.
- Shared helpers (slicing, big- and little-endian fields) live in `bytes`;
  packages use them instead of writing their own.

## 64-bit values

- Only through `bend-osdev-word64` and its opaque type `W64`. When Base gains
  a native `U64`, only `word64` changes.

## Reference and fast implementations

- Where speed matters, a package keeps a simple reference implementation,
  written to be obviously correct and easy to prove things about, beside any
  fast implementation. A law proves the two agree for every input; where that
  proof is out of reach, a differential test holds them together and the
  README says so.

## Specifications and licensing

- Every package is MIT-licensed and written from a public specification, which
  its `README.md` cites. Code is never translated from, or written while
  reading, GPL source (the Linux kernel, or GPL reference implementations).
- A package whose format has no independent specification says so in its
  `README.md`, and is not written until that is resolved.

## Laws

- Bend's convention is that a human writes `LAWS.bend` and the AI writes
  `PROOF.bend` and the code. In this repository the laws are drafted by an AI
  and reviewed by the maintainer continually, as they are written, so laws
  carry no draft marker.
- Laws state the behaviour of the **public interface** only, never of
  internal helpers, so internals can be restructured without changing a law.
  Lemmas about internals live in the proof files.
- Laws come in two kinds:
  - **vectors**: the specification's own test values, as equalities proved by
    computation (`{==}`);
  - **properties**: claims for every input (a round trip, an invariant, a
    bound), proved by induction.
- `bend x/PROOF.bend` must print `ALL PROOFS CHECK`, and so must each
  further proof file (below). `--verdict` (the Lean kernel) is run too, and
  a package's `README.md` records whether it passes.
- **Lemma files.** Lemmas a proof file needs may live in lemma files,
  `proof_<name>.bend` (crc's and gf's `proof_*.bend`), which prove no law and
  are imported by the proof files that use them.
- **Several pairs of law and proof files.** A check of a proof file takes in
  the proofs of every package it imports, so when one proof file would
  outgrow what a check process can hold (AGENTS.md, Checker memory), the
  package splits its laws into pairs: `LAWS.bend` with `PROOF.bend`, and
  `LAWS_<part>.bend` with `PROOF_<part>.bend`, each proof file importing its
  own law file as `Laws` and only the proofs its laws rest on, so that each
  is checked in a process of its own. Laws are grouped by what their proofs
  need (crypto: its generic laws in `LAWS.bend`, and one pair for each
  package its instances come from). A proof elsewhere imports the pair that
  holds the law it uses, so the README says which pair holds which laws,
  and moving a law to another pair changes what its users import: like a
  rename, it is a breaking change (Versions).

## Versions

- `VERSION` holds four numbers, `0.1.0.0` to start. Before 1.0, the second
  number rises for a **breaking** change: a changed or removed public def or
  type, or a changed or removed law. The third rises for additions (new defs,
  new laws). The fourth rises for anything else that changes a published file.
  After 1.0 the first number takes the second's role.
- A publish is permanent, so a published package's directory is never renamed
  or moved.

## Dependencies

- `DEPS` lists, one per line, the bend-osdev packages (by directory name) and
  hub packages (`name@version`) the package may import. `scripts/deps.sh`
  checks every import against it, and CI runs it, so a new dependency is
  always a deliberate change to `DEPS`.
- Interoperation with other libraries lives in adapter packages (for example
  `kitbytes`, between `Octets` and bend-kit's `Bytes`), never in the core
  packages, so no core package depends on another library's types.

## Extension points

- Every README has an "Extension points" section: what can be customised
  (parameters, templates, defaults), what can be replaced (opaque types,
  reference and fast implementations), and how.

## Testing

- `scripts/check.sh x` runs, for package `x`: the proofs (`--check-only` on
  `PROOF.bend` and on each `PROOF_<part>.bend`, one process each),
  `check.bend` against its `#|` lines, and `ref/run.sh` if the tools it needs
  are installed.
- A differential test compares the package against an independent
  implementation on many inputs: a system tool (`readelf`, `sgdisk`,
  `debugfs`, `xz`) or a library outside this repository (Python's `zlib`,
  `lzma`, `cryptography`). A package with no independent reference says so,
  and tests against hand-built examples from its specification.

## Bend version

- The packages are checked with the Bend release in `BEND_VERSION`.
  `scripts/install-bend.sh` installs that exact release and verifies its
  hash; CI uses it.
