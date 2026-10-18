# Review checklist

Every package is checked against this list before it is committed, whoever
wrote it. Each item protects a property: that a package stays a separate,
replaceable component, and that it can be changed, restructured and
customised without breaking anything else.

## Interfaces

- [ ] The README lists the public interface (files, defs, types); everything
      else is internal.
- [ ] No other package's internals are used: no matching on or building of
      another package's constructors (`Octets`, `W64`, …), no calls to its
      unlisted helpers. Proofs too: they use the other package's laws.
- [ ] Byte strings in the public interface are `Octets`, 64-bit values `W64`.
- [ ] One file per concern; nothing a user needs alone is buried in a file
      with unrelated code.
- [ ] Real choices are parameters or templates with named defaults; nothing
      that a user might reasonably vary is hard-coded.
- [ ] Data that can arrive in pieces has a streaming interface (or the README
      says why not).

## Errors and names

- [ ] Fallible functions answer `Result<&2, &2, E, A>` with the package's own
      error type, one constructor per failure, package-prefixed.
- [ ] No declared name Base might add (see CONVENTIONS.md, Names).

## Laws

- [ ] A new `LAWS.bend` opens with the DRAFT line, and a new or changed law in
      an accepted package has a DRAFT line above it, until the maintainer
      accepts it.
- [ ] Laws are about the public interface only; lemmas about internals are in
      `PROOF.bend`.
- [ ] At least one law holds for every input, where tractable; any package
      with vectors only says so and why.
- [ ] No proof is faked: no `@unsafe`, no `?TODO`, no law weakened into a
      tautology, no vector standing in for a claim it does not cover.
- [ ] Where a fast implementation exists, a law (or a differential test, said
      plainly) ties it to the reference implementation.

## Dependencies and licensing

- [ ] `DEPS` is exact and `scripts/deps.sh` passes; any new dependency is
      justified in the README.
- [ ] Interoperation with other libraries is in an adapter package, not here.
- [ ] Written from the public specification the README cites; no GPL source
      was read. MIT `LICENSE` present.

## Tests and status

- [ ] `scripts/check.sh` passes; `--verdict` is run and its result recorded.
- [ ] A differential test against an independent implementation exists, or
      the README says why not and what stands in for it.
- [ ] No scratch files left in the package directory.
- [ ] The README has its "Extension points" section and an honest status
      line.
