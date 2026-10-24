# bend-osdev-textsearch

Finding a pattern in a byte stream that arrives in pieces: the counterpart
of the kernel's textsearch framework (`textsearch_prepare`,
`textsearch_find`, `textsearch_next`, and its algorithms `ts_kmp`, `ts_bm`
and `ts_fsm`), which netfilter's string match and others use to search
packet data spread over several buffers. One interface, three algorithms
behind it, and a reference they are held to.

## What it implements

The interface follows the framework's documented shape: an algorithm is
prepared from a pattern, then fed the text one block at a time, and reports
matches across block boundaries. The algorithms are written from their
published descriptions: Knuth, Morris and Pratt, "Fast pattern matching in
strings" (SIAM J. Computing, 1977); Boyer and Moore, "A fast string
searching algorithm" (CACM, 1977), with the strong good-suffix rule as
textbooks state it; Horspool, "Practical fast searching in strings"
(Software: Practice and Experience, 1980). The token automaton follows the
idea of `ts_fsm` (a pattern of character classes, each with a repetition)
as an NFA simulation. No kernel source was read.

* **The interface.** An algorithm is a state type `~S` and a feed,
  `~feed: S -> Nat -> List<&2, U32> -> S & List<&2, Nat>`: given the state,
  the offset of a chunk's first byte in the stream and the chunk, it answers
  the new state and the matches the chunk completes. `ts.run` drives it
  over a list of chunks, `ts.find_all` and `ts.find` over `Octets` chunks. A
  match is given by its **end**, the offset just past its last byte;
  `ts.starts(m, ends)` turns ends into starts for a pattern of `m` bytes.
  Matches are reported once each, in order, overlapping ones included.
* **Byte automata** (`auto.bend`): any state and step on one byte,
  `~step: S -> U32 -> S & Bool` (whether a match ends with the byte), made
  into a feed: `ts.auto.feed`, `ts.auto.run`, `ts.auto.ends`.
* **KMP** (`kmp.bend`): the automaton keeps how many of the pattern's bytes
  the text read so far ends with; on a byte that does not extend it, the
  prefix table gives the next shorter candidate, so no byte is read twice.
* **Boyer-Moore** (`bm.bend`): the pattern is compared from its last byte
  back, then moved right. `TsHorspool` shifts by Horspool's bad-character
  rule (the text byte under the pattern's last position); `TsGoodSuffix`, the
  default, takes the larger of that and the strong good-suffix shift
  (computed from its definition: the least shift that lines the matched
  suffix up with an equal run of the pattern and brings a different byte
  under the mismatch). Between chunks it keeps the last `m - 1` bytes seen.
* **Token automaton** (`fsm.bend`): a pattern is a list of `TsToken{class,
  recur}`: a class (`TsIs{b}`, `TsRange{lo, hi}`, `TsOneOf{bytes}`,
  `TsAnyByte`; `ts.fsm.digit()`, `lower()`, `upper()`, `space()`) and a count
  (`TsOne`, `TsPerhaps`, `TsStar`, `TsPlus`). A match is a non-empty run of
  bytes the tokens describe, starting anywhere; the automaton keeps the set
  of token positions reached and starts a new match at every byte.
* **Ignoring case** (`TS_IGNORECASE`): KMP and Boyer-Moore take `icase`,
  which folds ASCII upper case to lower case on both sides; `ts.exact()` is
  the default (exact bytes).
* **An empty pattern** matches nowhere (the kernel refuses one).

## Files

| File | Holds |
|---|---|
| `textsearch.bend` | the entry file: the interface's driver (`ts.run`, `ts.find_all`, `ts.find`), chunks, `ts.starts`, case folding |
| `auto.bend` | byte automata as feeds |
| `kmp.bend` | Knuth-Morris-Pratt: `TsKmp`, the prefix table, the step |
| `bm.bend` | Boyer-Moore: `TsBmRule`, `TsBmConf`, `TsBm`, the shift rules, the window scan, the feed with its kept bytes |
| `fsm.bend` | the token automaton: `TsClass`, `TsRecur`, `TsToken`, `TsFsm`, the step; and its reference, `ts.fsm.naive` |
| `naive.bend` | the reference for plain patterns: the pattern tried at every offset |
| `spec.bend` | bounded exhaustive agreement with the references, for the laws |
| `LAWS.bend`, `PROOF.bend` | the laws for every automaton and the bounded ones, and their proofs |
| `LAWS_kmp.bend`, `PROOF_kmp.bend` | KMP against the reference, and its proof (the theory of borders) |
| `LAWS_fsm.bend`, `PROOF_fsm.bend` | the token automaton against its backtracking reference, and its proof |
| `proof_lib.bend` | lemmas the proof files share (no law) |
| `check.bend` | examples and large exhaustive comparisons, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `ts.run(~S, ~feed, s, pos, cs)` | the match ends in chunks `cs` (lists of bytes), the first at offset `pos`, from state `s` |
| `ts.find_all(~S, ~feed, s, cs)`, `ts.find(~S, ~feed, s, cs)` | the same over `Octets` chunks from offset 0; the first match (`textsearch_find`) |
| `ts.starts(m, ends)`, `ts.concat(cs)`, `ts.chunks(cs)` | ends as starts; the bytes of all chunks; `Octets` chunks as lists |
| `ts.fold(icase, c)`, `ts.same(icase, a, b)`, `ts.exact()` | case folding, and the default (exact) |
| `ts.auto.feed(~S, ~step, s, pos, xs)`, `ts.auto.then`, `ts.auto.ends`, `ts.auto.run` (auto.bend) | a byte automaton as a feed; a feed's outcome then more bytes; the ends in one chunk; over chunks |
| `TsKmp`, `ts.kmp.start(icase, p)`, `ts.kmp.step`, `ts.kmp.feed` (kmp.bend) | KMP's state, before any text; its step; its feed |
| `ts.kmp.ends(icase, p, xs)`, `ts.kmp.search(icase, p, cs)` | the ends of `p` in one text; in chunks |
| `TsBmRule`: `TsHorspool`, `TsGoodSuffix`; `ts.bm.rule_default()` (bm.bend) | the shift rule, good suffix by default |
| `TsBm`, `ts.bm.start(icase, rule, p)`, `ts.bm.feed` | Boyer-Moore's state and feed |
| `ts.bm.ends(icase, rule, p, xs)`, `ts.bm.search(icase, rule, p, cs)` | the ends of `p` in one text; in chunks |
| `TsClass`, `TsRecur`, `TsToken`, `ts.fsm.digit()`, `ts.fsm.lower()`, `ts.fsm.upper()`, `ts.fsm.space()`, `ts.fsm.literal(p)` (fsm.bend) | token patterns; a byte string as tokens |
| `TsFsm`, `ts.fsm.start(tks)`, `ts.fsm.step`, `ts.fsm.feed`, `ts.fsm.ends(tks, xs)`, `ts.fsm.search(tks, cs)` | the token automaton |
| `ts.fsm.naive(tks, xs)` | the token reference: every offset where some non-empty run ending there matches |
| `ts.naive.ends(icase, p, xs)` (naive.bend) | the plain reference |

`TsKmp`, `TsBm`, `TsBmConf` and `TsFsm` are opaque; `TsBmRule`, `TsClass`,
`TsRecur` and `TsToken` are open. The other defs (`ts.run.go`,
`ts.auto.go`/`hit`/`cons`/`pre`/`snd`, `ts.kmp.at`/`back`/`next`/`pi`/`done`,
the `ts.bm.*` tables and scan, the `ts.fsm.*` steps, `ts.naive.at`/`go`, and
`spec.bend`) are internal.

## Extension points

* **A new algorithm** is a state type and a feed passed to `ts.run`; one
  that reads a byte at a time needs only a step, and `auto.bend` gives it
  the chunking and its laws for free (`auto_split` holds for every step).
* **Boyer-Moore's shift** is a parameter (`TsBmRule`); a new rule is a case
  of `ts.bm.shift` (each must be safe: never skip an occurrence).
* **Case** is a parameter (`icase`); other byte equivalences would replace
  `ts.fold`.
* **Classes** in the token automaton are open data; a new class is a
  constructor and a case of `ts.fsm.member`.

## Laws

`LAWS.bend`:

* `auto_append`: for **every** byte automaton (state type and step), state,
  offset and bytes, feeding `xs ++ ys` is feeding `xs` and then `ys` from
  where it ended (its state, its matches after `xs`'s);
* `auto_split`: so feeding **any** list of chunks finds exactly the matches
  of feeding their bytes whole; `kmp_split` and `fsm_split`: hence KMP and
  the token automaton, for every pattern and every chunking of every text;
* bounded exhaustive agreement with the references (closed computations
  over every case): `small_plain` (KMP and both Boyer-Moore rules find what
  `ts.naive.ends` finds, for every pattern of 1 or 2 bytes over a two-byte
  alphabet in every text of up to 4, the text whole, one byte per chunk, and
  cut in two at every offset), `small_plain3` (3-byte patterns in 4-byte
  texts), `small_icase` (ignoring case, over `A` and `a`), `small_tokens`
  and `small_tokens2` (the token automaton against `ts.fsm.naive`, every
  single token of three classes in four counts, and pairs);
* **vectors:** KMP across chunks, both Boyer-Moore rules (one ignoring
  case), and the token automaton with a range and `TsPlus`.

`LAWS_kmp.bend`, **for every input**, proved in `PROOF_kmp.bend`:

* `kmp_ref`: KMP finds exactly what the reference finds,
  `ts.kmp.ends(icase, p, xs) == ts.naive.ends(icase, p, xs)`, for every
  pattern (the empty one included), exactly or ignoring case, and every
  text; `kmp_search_ref`: so does `ts.kmp.search` for every chunking
  (with `kmp_split`).

The proof is a theory of borders on sets of prefix lengths (lists of
Bools, entry j for the prefix of j bytes). Reading byte c takes a set S to
the empty prefix and j + 1 for each j in S whose next pattern byte is c
(the shift-and automaton); B(k), that set after the pattern's own first k
bytes, is the set of borders of those bytes. Then:

* the prefix table is right (`bd.pi_ok`): for every k, B(k) is k added to
  B(table entry k - 1), and the entry is below k. The table is built by
  KMP's own step, so this goes along the table's construction, with
* following the table loses no border (`bd.back_ok`, `bd.next_ok`): from a
  prefix of k bytes, the prefix KMP's step finds after byte c, q2, has
  B(q2) equal to the set after c from B(k) (strong induction along the
  table's entries);
* the shift-and automaton's semantics (`kp.gstep`): from a set S it
  reports, on the rest of the text, the matches of the prefixes in S still
  to be completed, then the reference's;
* so KMP's one number q stands for the whole set B(q) (`kp.run`), and from
  B(0) nothing is pending: KMP reports what the reference reports. Ignoring
  case is the same search on the folded pattern and text.

`LAWS_fsm.bend`, **for every input**, proved in `PROOF_fsm.bend`:

* `fsm_ref`: the token automaton finds exactly what its backtracking
  reference finds, `ts.fsm.ends(tks, xs) == ts.fsm.naive(tks, xs)`, for
  every token pattern (every class and count, `TsPlus` included) and every
  text; `fsm_search_ref`: so does `ts.fsm.search` for every chunking.

The proof transfers apparmor's `glob_run` method. The reference's
backtracking matcher is taken without its fuel (`fs.full`; the fuel
`ts.fsm.naive` gives, two per token and one per byte, is always enough,
`fs.fuel_ok`), and `TsPlus` written as `TsOne` then `TsStar`, as the
automaton keeps it, matches the same (`fs.exp_ok`). A set of positions
means what it accepts: some active position whose remaining tokens match
the rest exactly (`fs.sem`). Each pass of the step takes one meaning to the
next: closing over optional tokens adds nothing (`fs.CL`), reading a byte
moves a closed set's meaning on by that byte (`fs.AL`, `fs.CA`), starting a
match adds the whole pattern (`fs.ST`); so after byte c the positions
accept w exactly when, before it, they accepted c then w or the pattern
matches c then w (`fs.STEP`), and the report, the last position, is the
set accepting no more bytes (`fs.HIT`). From a set, the automaton reports
at each later end whether a match begun before is accepted or some
non-empty run within the rest matches (`fs.run`); from the start nothing is
under way, which is the reference.

**Not proved, and why.** That Boyer-Moore finds exactly what the reference
finds **in general**, and its chunking law in general. Its correctness
rests on each shift being safe, a substantial development not done here.
It is held instead by the bounded laws above (proved by computation, kept
small because the checker bounds the work of one law), by `check.bend`'s
much larger exhaustive comparisons, and by `ref/`.

## Tests

* `check.bend`: examples (KMP over `Octets` chunks with a match across a
  boundary, starts, Boyer-Moore's first match and a case-ignoring search,
  overlapping matches, the token automaton across chunks, an empty pattern),
  then exhaustive comparisons with the references, each over the text whole,
  one byte per chunk and cut in two at every offset: every pattern of 1 to 5
  bytes over two letters in every text of up to 10 (1,523,650 chunked
  texts, each searched by KMP and both Boyer-Moore rules), 1 to 3 over
  three letters in up to 6 (362,466), ignoring case over `A`, `a`, `b` (32,796), literal tokens
  against the plain reference (15,330), and every pattern of one or two
  tokens of three classes in every text of up to 7 (359,268). All agree. A
  deliberately wrong shift or prefix-table reset makes thousands disagree.
* `ref/run.sh` compares 200 random cases with Python: 120 plain patterns
  (alphabets of 2, 4 and 256 bytes, mixed case, planted occurrences, up to
  160 bytes in random chunks) against `bytes.find`, and 80 token patterns
  against the `re` module (each token a class with no suffix, `?`, `*` or
  `+`; a match is a non-empty run `re.fullmatch` accepts). It exits 77
  without `python3`.

## Limitations

* The kernel's `TS_FSM_HEAD_IGNORE` (skipping a prefix before an anchored
  match) is not modelled: matches start anywhere. Classes are explicit
  byte sets and ranges, not the kernel's ctype classes.
* Texts are lists; Boyer-Moore's windows are list slices, so its skips save
  comparisons but not the walk along the list.
* Each match is reported by its end; a token pattern's matches have no
  single start.

## Dependencies

`bend-osdev-bytes` (`Octets` chunks).

## Status

Bend 2.0.37: `PROOF.bend`, `PROOF_kmp.bend` and `PROOF_fsm.bend` ALL
PROOFS CHECK, and under `--verdict` (each in its own process, under 0.3
GB), `check.bend` passes, `ref/run.sh` 200 cases match, `scripts/deps.sh
textsearch` ok.
