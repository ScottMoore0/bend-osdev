# Working on bend-osdev

Read `CONVENTIONS.md` first; it is binding, and `REVIEW.md` is the checklist
every package must pass before it is committed. This file is the practical side:
how a package is built, and the Bend rules that bite. `crc/` is the template
package: copy its shape.

## Building a package

1. Read the specification the package implements, and note its citation for
   the README. Never read GPL source while writing a package (the Linux kernel,
   GPL reference implementations): the packages are MIT and written from
   public specifications only.
2. Write `x/x.bend` (one file per concern if the package has several). Take
   and answer `Octets` (from `../bytes/bytes.bend`) for byte strings, use
   `../word64/word64.bend` for anything 64-bit, answer `Result<&2, &2, E, A>`
   with the package's own error type `E` where input can be malformed, and
   take real choices as parameters or templates with named defaults. Use
   other packages only through their public interfaces.
3. Write `x/LAWS.bend` (no draft marker: the maintainer reviews laws as they
   are written). Aim for:
   - **properties for every input** where they can be proved: round trips
     (parse after serialise gives the value back), invariants, the result of
     an operation on a structure;
   - **vectors** from the specification's own examples, proved by `{==}`.
4. Write `x/PROOF.bend`: `import ./LAWS.bend as Laws`, then one
   `def Laws.name(params):` per law. Helper lemmas are ordinary typed defs in
   the same file, or in a lemma file `proof_<name>.bend` that the proof files
   using them import. Import only the proofs the laws rest on: a package
   whose proofs would outgrow one check process splits its laws into pairs,
   `LAWS_<part>.bend` with `PROOF_<part>.bend`, each checked on its own
   (CONVENTIONS.md, Laws; crypto has ten).
5. Write `x/check.bend`: an `IO` main that prints results, followed by the
   expected output as `#|` lines.
6. Write `x/ref/gen.py` and `x/ref/run.sh` if anything outside this
   repository can produce reference results (a system tool or a Python
   library), as `crc/ref/` does. `run.sh` exits 77 when its tools are missing.
7. Write `x/README.md` (what it does, the specification, the files, the
   public API, the extension points, the laws, the tests, the status line),
   copy `LICENSE` and a `VERSION` of `0.1.0.0` into the directory, and list
   its imports in `x/DEPS`.
8. `scripts/check.sh x` and `scripts/deps.sh x` must pass, and
   `VERDICT=1 scripts/check.sh x` should; record the results in the README's
   status line.
9. State laws over the public interface only; keep lemmas about internals in
   the proof files.

## Bend rules that bite

- **No forward references, no mutual recursion.** A def may only call defs
  above it. Put helpers first.
- **`match` takes a parameter or a pattern-bound variable**, never a computed
  value. To branch on `U32.is_lt(x, 10)`, call a helper whose first
  parameter is that `Bool` and match on it there.
- **Termination is read left to right.** In a recursive call, every argument
  must be passed unchanged until one is a smaller part of its parameter (from
  a match); put the shrinking parameter first.
- **Affine by default.** A variable used twice must be reusable: `+x` on the
  parameter, `+x` on a pattern field, or `+x = v` for a let. Only `Data` can
  be reusable. A field bound from a `+` scrutinee is reusable already.
- **Shifts:** `U32.shl`/`U32.shr` shift by one bit; `U32.shln(a, n)` and
  `U32.shrn(a, n)` shift by a `Nat`.
- **No hex literals.** Write decimal, and compute the conversion with a tool
  rather than by hand. A `Nat` literal stops at `4294967295n`.
- **Names:** never declare a bare name Base might add (`U8`, `U16`, `U64`,
  `I64`, `F64`, `Byte`, `Word.lo`, …). Prefix types and helpers with the
  package (`Crc32Spec`, `W64.bits.lo`). Base's names are global, and a
  redeclared one is refused.
- **Proving a law for every `U32`:** split the value into its 32 bits with a
  deep pattern, `case U32{WCon{b0, WCon{b1, … WNil{}}}}` (generate it with a
  script), and then `{==}`. This works only if the code computes on symbolic
  bits: bit slicing (`W64.bits.lo/hi/cat`) does, and so does a mask with the
  constant **first** (`U32.and(255, v)`), but `Bool.and`/`Bool.or` match their
  first argument, so a symbolic first operand gets stuck.
- **Rewriting:** `%e : P` with `e : {a == b : T}` takes `P` to be the current
  goal with `_` where `b` occurs, and continues with `_` replaced by `a`. For
  example, to use `e : {A == t}` on the goal `{Con{h, A} == Con{h, t}}`, write
  `%e : {Con{h, A} == Con{h, _} : …}`; the goal becomes reflexive.
- **Induction:** a recursive call of the proof def is the induction
  hypothesis. When the goal after one step unfolds to exactly the hypothesis's
  type, return the recursive call itself.
- **`check.bend` mains return `IO(Unit)`**: `scripts/check.sh` builds them,
  and the ref tests' case files, into native binaries (`scripts/bend-run.sh`);
  a pure main is normalised by the checker, which is slow.
- **Imports:** siblings by relative path (`import ../bytes/bytes.bend as B`);
  hub packages by name (`import bend-kit-int@0.2.0.0/int.bend as Int`).

## Runtime and checker limits (Bend 2.0.37)

- **Two lanes:** `bend file.bend` checks the file and runs `main` on its
  JavaScript lane, in the bend process; `bend file.bend -o prog` builds a
  native binary (with clang 14 or newer, from `$CC` or PATH). The native
  binary starts at about 2 MB; the `bend` process itself (Bun plus the
  checker) takes about 120 MB. `scripts/check.sh` runs programs natively
  through `scripts/bend-run.sh`; measure sizes and times on native builds.
- **Recursion depth:** only the JavaScript lane has a small stack: it fails
  ("memory fault (machine stack overflow?)") somewhere between 10,000 and
  40,000 nested non-tail calls. A native binary has a 2 GB stack for its own
  calls (5,000,000 nested calls run fine). Library code still uses tail calls
  over long data, so that it runs on both lanes and stays fast: if a proof
  needs the structural form, keep it as the reference and prove the tail form
  equal to it, as bytes does (`PROOF.bend`, the `F_*` lemmas). `Octets`
  operations have no length limit; the `List<&2, U32>` list layer in bytes is
  structural, with `*.fast` forms beside it.
- **Memory:** natively, an `Array<U32>` holds 4 bytes per slot, an `Octets`
  about 80 bytes per byte held, and a 1 MB `Octets` pipeline (build, append,
  cut, print) peaks at about 166 MB (about 960 MB on the JavaScript lane).
  Hold images of more than a few MB a block at a time, or in an `Array<U32>`
  (blockdev's `ImgDev`: a 64 MB image in about 67 MB).
- **List literals** of more than about 3,000 elements overflow: build long
  test inputs in pieces or with a generator function.
- **Native builds:** code with more than 247 live one-word values in one
  segment fails to compile to C ("an arity over 247", bendlang/bend#1069).
  A `W64` is two native `U32`s and caps' and uuid's sets and identifiers are
  native words, so ordinary code stays well under it; what still hits it is a
  value built from bits (a `Word(n)` of more than a few dozen bits held whole)
  or a generated `main` with hundreds of live results: split it into helper
  defs (ext2's and caps' ref tests do). `scripts/bend-run.sh` runs a program
  the backend refuses on the JavaScript lane and `check.sh` reports it
  (`js` lines); a native build killed for memory (a generated case file of
  more than a few hundred KB) falls back the same way.
- **`--verdict`:** it cannot model a template parameter whose type is a
  proposition (`~inv: {...}`); a large `Nat` literal (about 2^24 and up)
  bound to a reused `+` parameter trips a kernel mismatch
  (bendlang/bend#1322), so use `U32` for limits and sizes; and very long
  closed `Nat` computations run out of kernel fuel.
- **Checker memory:** a check process is killed at about 3 GB; keep each
  generated proof or case file to a few hundred KB. A proof file's check
  takes in the proofs of every package it imports, checked again in each
  file that imports them, so under `--verdict` its peak is about the sum of
  theirs (alone: cipher-modes' about 1.2 GB, crc's 0.7 GB, hashes' and
  legacy-ciphers' 0.6 GB, bend-collections-laws-crypto's hash proofs 0.5 GB,
  bytes' 0.25 GB). Import only the proofs a file's laws rest on, and split a
  package's laws into pairs of files when one proof file nears 2 GB
  (CONVENTIONS.md, Laws).

## Proof limits documented in package READMEs (Bend 2.0.37)

Each is explained where it was met; read that section before working
around it.

- **A step budget per def** in the kernel: split a large computation into
  one def per case (bch `README.md`, Laws; gf `README.md`, Laws: 32 cases
  per def to stay within `--verdict`'s fuel).
- **No eta rule:** a pair is not equal to the pair of its projections, so
  laws state what a pair *is* (array `README.md`, Laws, "Pairs"); a
  continuation or lambda passed on (as a template argument, or to `IO`)
  is written out in full, in the code and in the proofs (iodev
  `README.md`, Laws, "A note for the proof kernel").
- **A proof passed as a hypothesis is not `Data`:** a function from
  elements to proofs can be used only once, and `--verdict` cannot model
  one passed as a template, so laws quantify over a concrete order instead
  (ksort `README.md`, Laws, "What is not proved, and why").
- **`Nat` is unary inside the checkers:** keep vector numbers small
  (kmath, ext2 and algo `README.md`, Laws). A *closed* large `Nat` (2^32,
  `Nat.add(4294967295n, 1n)`, `U32.to_nat(4294967295)`) in a type is
  expanded whenever the checker compares that type by computation, and
  overflows its stack, even beside unknown values; so state bounds as "no
  more than a word's value", and powers of two as `U32Nat.dbl(n, x)` with
  `n` a variable or `x` unknown (u32 `README.md`, Laws, "Stating the
  bounds"; word64 `README.md`, Laws).
- **The kernel is slow on computation with free variables:** a large
  computation on symbolic bits (AES rounds, GF(2^128) multiplication) is
  out of reach even when it would terminate (cipher-modes `README.md`,
  "AES and bend-collections"; gf `README.md`, Laws).
- **`--verdict` memory:** crypto's laws are in ten pairs of law and proof
  files, each checked on its own (under `--verdict`, 0.3 to 1.3 GB peak;
  in one file they peaked at 3.26 GB); a new law goes in the pair whose
  proofs it rests on, or in a new pair (crypto `README.md`, Laws and
  Status).
