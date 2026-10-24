# bend-osdev-rhash

A resizable hash table with incremental resizing: the Bend counterpart of
Linux's rhashtable. While the table grows or shrinks, the old and the new
bucket arrays coexist; every insert and remove moves a few old buckets into
the new array (a parameter), lookups look in the new array and then in the
old one, and so every key that is present is found at every step of a
migration. A resize can also be started, stepped and finished explicitly.

Linux resizes its table while other CPUs read it under RCU. Bend has no
shared memory, so this table is a value: every operation takes a table and
answers a new one. What carries over is the shape of the resize, and the
property it exists for.

The directory is `rhash` and the entry file `rhash/rhash.bend`; the hub name
is `bend-osdev-rhash`.

## Sources

Written from published descriptions of incremental rehashing and of
rhashtable; no kernel source was read.

* Jonathan Corbet, "Relativistic hash tables, part 1: Algorithms", LWN.net,
  17 September 2014, https://lwn.net/Articles/612021/: the old and the new
  bucket arrays coexisting during a resize, sizes changing by a factor of
  two, and lookups staying correct because they compare keys and so
  tolerate extra entries in a chain.
* Neil Brown, "Rhashtables: under the hood", LWN.net, 21 April 2018,
  https://lwn.net/Articles/751974/: lookups and removals check each bucket
  table in turn while inserts go only into the last; the growth trigger
  (more entries than 70% of the buckets) and the shrink trigger (fewer than
  30%, only with `automatic_shrinking`); doubling and halving; `min_size`
  (at least four buckets), `max_size` (2^31 by default), the default of 64
  buckets; a new hash seed for each new table; an object moved by adding it
  to the new chain before removing it from the old, so it is never absent.
* Wikipedia, "Hash table", sections "Dynamic resizing" and "Alternatives
  to all-at-once rehashing" (read 18 October 2026): resizing gradually,
  with the old and the new hash function both kept and buckets "cleaned"
  as operations touch them.

The default hash is Bob Jenkins' lookup3 (`hashword`), as khash implements
it (see khash's README for its sources).

## Files

| File | Holds |
|---|---|
| `rhash.bend` | the table: types, the policy, buckets, bucket arrays, migration, the interface |
| `model.bend` | the reference model: an association list that never resizes, for the laws |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `check.bend` | examples, a migration checked step by step, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test against a Python dict |

## Keys, hashes and buckets

* **Keys** of any type `K` are compared and hashed through an encoding as
  a list of words, `~kenc: K -> List<&2, U32>`, as the kernel compares
  `key_len` bytes and hashes them: two keys are the same key exactly when
  their encodings are equal (`RHash.same_key`). Named encodings:
  `RHash.key_u32` (a `U32` as one word) and `RHash.key_words` (a word list
  as itself). Each entry keeps its key's encoding, so migration rehashes it
  without the template.
* **The hash** is a template argument `~hash: U32 -> List<&2, U32> -> U32`
  (seed, words), named default `RHash.jhash2` (khash's `Jhash.jhash2`).
  Each bucket array has its own seed; a new array's seed is the old one's
  plus the policy's `seed_step` (the kernel takes a new random `hash_rnd`;
  a pure table takes its seeds from its policy, and an explicit resize
  takes one from the caller).
* **Buckets:** an array of 2^log buckets is a complete binary tree of depth
  log. A key's bucket is chosen by the low log bits of its hash, least
  significant first (the kernel's `hash & (size - 1)`). A bucket is a list
  of entries; an insert puts its key first in its bucket, a migrated entry
  goes last.

## API

Every def takes the key and value types as template arguments `~K, ~V`,
and the ones that hash take `~hash` (and `~kenc` when given a key); for
example `RHash.insert(~U32, ~U32, ~RHash.key_u32, ~RHash.jhash2, t, k, v)`.

| Def | Meaning |
|---|---|
| `RHash.new(p)` | an empty table with the policy `p` (2^init_log buckets) |
| `RHash.insert(t, k, v)` | k bound to v, replacing any value it had; then the resize work |
| `RHash.remove(t, k)` | k removed if present; then the resize work |
| `RHash.lookup(t, k)` | `Some{v}` if k is bound to v, else `None{}` |
| `RHash.contains(t, k)`, `RHash.size(t)` | whether k is present; the number of keys |
| `RHash.same_key(a, b)` | whether two keys are the same key (equal encodings) |
| `RHash.step(t)`, `RHash.steps(t, n)` | one (n) migration steps: the old bucket at the cursor moves into the new array; nothing when no resize is under way |
| `RHash.drain(t)` | a resize under way finished (one step per old bucket) |
| `RHash.resize(t, log, seed)` | an explicit resize to 2^min(log, `RHash.log_limit()`) buckets (a larger log is clamped): any resize under way is finished first, then the new one starts, and its steps follow later operations or `RHash.step` |
| `RHash.resizing(t)`, `RHash.log(t)` | whether a resize is under way; the current array's log of its size |
| `RHash.log_limit()` | 31: the most any array's log can be (2^31 buckets). A bound of the representation, not of the policy: the migration cursor is a U32 that wraps through the U32 mask 2^log - 1, and a bucket's path is the low log bits of a 32-bit hash, so a log of 32 or more breaks both. An explicit resize, `init_log` and `max_log` are all clamped to it |
| `RHash.apply(t, op)`, `RHash.run(t, ops)` | operations (`RhOp`: `RhIns{k, v}`, `RhDel{k}`, `RhStep{}`, `RhResize{log, seed}`), in order |
| `RHash.replay(p, tr)` | a trace, the latest operation first, replayed on a new table |
| `RHash.jhash2`, `RHash.key_u32`, `RHash.key_words` | the named defaults above |
| `RhParams{...}`, `RhParams.default()`, `RhParams.shrinking()` | the policy (below) |
| `RhModel.empty`, `.apply`, `.replay`, `.lookup`, `.size`, `.after` (`model.bend`) | the reference model the laws use |

Types: `RHash<K, V>` (opaque), `RhParams` (open), `RhOp<K, V>` (open),
`RhEntry<K, V>` (open: the model's entries). `RhTree`, `RhTab`, `RhBop`,
`RhTake` and every `rh.*` def are internal.

## Parameters

`RhParams{grow_pct, shrink_pct, auto_shrink, min_log, max_log, init_log,
steps, seed, seed_step}`. After every insert and remove the table moves
`steps` old buckets; then, if no resize is under way, it doubles when it
holds more than `grow_pct` percent of its buckets (below 2^max_log), and,
when `auto_shrink` is set, halves when it holds fewer than `shrink_pct`
percent (above 2^min_log). `init_log` and `max_log` are clamped to
`RHash.log_limit()` (31): a policy cannot ask for more than 2^31 buckets.

| Named default | grow_pct | shrink_pct | auto_shrink | min_log | max_log | init_log | steps | seed | seed_step |
|---|---|---|---|---|---|---|---|---|---|
| `RhParams.default()` | 70 | 30 | False | 2 | 31 | 6 | 4 | 0 | 2654435769 |
| `RhParams.shrinking()` | 70 | 30 | True | 2 | 31 | 6 | 4 | 0 | 2654435769 |

The percentages, the four-bucket minimum, the 2^31 maximum, the 64 buckets
to start and shrinking only when asked are the kernel's, as Brown
describes them. `steps` has no kernel counterpart (the kernel migrates in a
worker); four buckets per operation finish a doubling, which starts at 70%
load, well before the new array reaches 70% itself.

## How a lookup stays right

Lookups need no invariant, so every law holds for every table value, not
only for tables built through the interface:

* an insert removes the key from both arrays before putting it in the
  current one, and a remove takes it out of both, so neither depends on
  where the key was;
* a migration step takes the old bucket at the cursor out of the old
  array, and appends to the current array only the entries whose key
  belongs in that bucket (the others were never found by a lookup), after
  any entries the current array already has for those keys. A key whose
  old bucket was taken is then found in the current array exactly as it
  was found before; any other key is untouched;
* a resize starts only when the old array is empty, and a node whose two
  halves are empty collapses, so the old array becomes empty exactly when
  its last bucket has been taken.

## Extension points

* **The hash** (`~hash`) and **the key encoding** (`~kenc`) are template
  arguments; any function of the right type works, and the laws hold for
  every one (the reference test also runs a hash that sends every key to
  bucket 0).
* **The policy** is the `RhParams` record: thresholds, bounds, the initial
  size, the steps per operation and the seeds. Its sizes are bounded by
  `RHash.log_limit()` (31), which is not a parameter: it comes from the U32
  cursor and the 32-bit hash, and a `max_log` or `init_log` above it acts
  as 31, as an explicit resize past it does.
* **Explicit control:** `RHash.step`, `RHash.steps`, `RHash.drain` and
  `RHash.resize` drive a resize without inserts or removes, as the kernel's
  worker would.
* **The model** in `model.bend` states what any replacement table must do.

## Laws

`LAWS.bend`, 22 laws, all proved, for every key type, value type, key
encoding, hash, policy and table:

* **A new table:** `lookup_new`, `size_new`.
* **The map:** `lookup_insert`, `lookup_insert_other`, `lookup_remove`,
  `lookup_remove_other` (another key: one that is not the same key),
  `lookup_same_key`.
* **Size:** `size_insert_absent` (+1), `size_insert_present` (+0),
  `size_remove_present` (−1), `size_remove_absent` (+0).
* **Migration** (the property rhashtable exists for): `lookup_step`,
  `size_step`, `lookup_steps`, `lookup_drain`, `lookup_resize`,
  `size_resize`: no migration step, any number of them, drain or explicit
  resize changes any key's lookup or the size.
* **Any interleaving of operations and migration steps:** `lookup_run`
  (from any table, each key's lookup moves exactly as the model moves it,
  `RhModel.after`), `lookup_replay` and `size_replay` (a trace replayed on
  a new table holds what the model holds, and as many keys: the model binds
  each key once, which the proof shows).
* **Vectors:** `vec_lookup`, `vec_size` (two inserts and a remove under
  the default policy and hash).

Not a law: that a resize finishes. For tables built through the interface,
draining (one step per old bucket) empties the old array, but for an
arbitrary table value it need not, and nothing depends on it: lookups are
right whether or not it does. `check.bend` and the reference test show it
finishing. A proof would need a reachability invariant over every
interface operation: the old array is a complete tree of depth `old_log`
in which the buckets the cursor has passed are taken, a node whose buckets
are all taken has collapsed, and the cursor walks 0, 1, ..., 2^old_log - 1
(`rh.next`'s mask, `2^old_log - 1` as a U32, is right because a log is at
most 31); then the bucket the cursor takes last in each subtree collapses
it, so after 2^old_log steps from a fresh start, or from any point of a
walk, the old array is one empty bucket. Not proved here.

Every size is clamped to `RHash.log_limit()`, 31: an explicit resize
(`RHash.resize`, `RhResize`), and the policy's `init_log` and `max_log`
(growth stops there whatever `max_log` says). The
cursor is a U32, and with log 32 or more its wrap mask `2^log - 1` and the
bucket paths' bits past 31 go wrong (a resize to 2^34 and then another could
leave the old array never emptied, and later resizes ignored). `check.bend`
asks for 2^40 buckets and gets 2^31.

## Tests

* `check.bend`: 1000 keys (2^11 buckets after growing), removes, an
  explicit resize to 2^3 checked after every 16 steps until it finishes
  (every present key found each time), drain, word-list keys, the
  shrinking policy, and an explicit resize asking for 2^40 buckets (2^31
  given, keys still found).
* `ref/run.sh`: four scenarios against a Python dict, 3800 random
  operations in 38 batches (inserts, removes, explicit steps, explicit
  resizes to random sizes), every key's lookup and the size compared after
  each batch: the default policy and hash; one step per operation with
  shrinking; a hash that sends every key to bucket 0; word-list keys of one
  to three words. Nearly every batch ends with a resize under way.

## Dependencies

`khash` (lookup3, the default hash). No other.

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 3800 operations in 38 batches match (the
whole `VERDICT=1 scripts/check.sh rhash` about 21 s, peak 0.37 GB),
`scripts/deps.sh` passes. Every size is clamped to `RHash.log_limit()`;
that a resize started through the interface finishes is not proved (Laws).
