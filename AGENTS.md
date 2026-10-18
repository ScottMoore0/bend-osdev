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
3. Write `x/LAWS.bend`, opening with `# DRAFT: not yet reviewed by the
   maintainer`. Aim for:
   - **properties for every input** where they can be proved: round trips
     (parse after serialise gives the value back), invariants, the result of
     an operation on a structure;
   - **vectors** from the specification's own examples, proved by `{==}`.
4. Write `x/PROOF.bend`: `import ./LAWS.bend as Laws`, then one
   `def Laws.name(params):` per law. Helper lemmas are ordinary typed defs in
   the same file.
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
   `PROOF.bend`.

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
- **`check.bend` mains return `IO(Unit)`**, so they compile to native code; a
  pure main is normalised by the checker, which is slow.
- **Imports:** siblings by relative path (`import ../bytes/bytes.bend as B`);
  hub packages by name (`import bend-kit-int@0.2.0.0/int.bend as Int`).

## Runtime and checker limits (Bend 2.0.37)

- **Recursion depth:** the runtime overflows its own fixed stack ("memory
  fault (machine stack overflow?)") somewhere between 10,000 and 40,000 nested
  non-tail calls; `ulimit -s` does not help. Write loops over long data as tail
  calls with an accumulator. If a proof needs the structural form, keep it as
  the reference and prove the tail form equal to it, as bytes does
  (`PROOF.bend`, the `F_*` lemmas). `Octets` operations have no length limit;
  the `List<&2, U32>` list layer in bytes is structural.
- **Octets memory:** about 150 bytes of memory per byte held (each byte is
  one `OctByte` record of eight `Bool`s); a pipeline that builds, copies and
  reads data peaks at several times its size. Hold images of more than a few
  MB a block at a time.
- **List literals** of more than about 3,000 elements overflow: build long
  test inputs in pieces or with a generator function.
- **Native builds:** a record with four or more `W64` fields fails to compile
  to C ("an arity over 247"); `bend file.bend` still runs it. Group `W64`
  fields into sub-records.
- **`--verdict`:** it cannot model a template parameter whose type is a
  proposition (`~inv: {...}`); a large `Nat` literal (about 2^24 and up)
  bound to a reused `+` parameter trips a kernel mismatch
  (bendlang/bend#1322), so use `U32` for limits and sizes; and very long
  closed `Nat` computations run out of kernel fuel.
- **Checker memory:** a check process is killed at about 3 GB; keep each
  generated proof or case file to a few hundred KB.
