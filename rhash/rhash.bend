# bend-osdev-rhash: a resizable hash table with incremental resizing, the
# Bend counterpart of Linux's rhashtable.
#
# Linux resizes its table while other CPUs read it under RCU. Bend has no
# shared memory, so this table is a value, and what carries over is the
# shape of the resize: while a table grows or shrinks, the old and the new
# bucket arrays coexist, every operation moves a few of the old buckets
# into the new array (a parameter), and lookups look in the new array and
# then in the old one, so every key that is present is found at every step
# of a migration. A resize can also be started and stepped explicitly.
#
# Keys: a key of any type K is compared and hashed through its encoding as
# a list of U32 words (~kenc), as the kernel compares key_len bytes with
# memcmp and hashes them with jhash: two keys are the same key exactly when
# their encodings are equal. The hash (~hash: seed, words -> U32) is a
# template argument, khash's jhash2 by default; each bucket array has its
# own seed, as each of the kernel's bucket tables has its own hash_rnd.
#
# Buckets: an array of 2^log buckets is a complete binary tree of depth
# log, a bucket chosen by the low log bits of the key's hash, least
# significant bit first (the kernel's hash & (size - 1)). A bucket is a
# list of entries, each holding its key's encoding, the key and the value.
#
# Written from the published descriptions of incremental rehashing and of
# rhashtable (README.md, "Sources"); no kernel source was read.
import Base
import ../khash/khash.bend as KH

# ---------------------------------------------------------------- types

# An entry: the key's encoding (what the table compares and hashes), the
# key and its value
type RhEntry<-K: Data, -V: Data> is Data:
  RhEntry{kw: List<&2, U32>, key: K, val: V}

# A bucket array: a tree whose leaves are buckets
type RhTree<-K: Data, -V: Data> is Data:
  RhLeaf{es: List<&2, RhEntry<K, V>>}
  RhNode{lo: RhTree<K, V>, hi: RhTree<K, V>}

# A bucket array with its size (2^log buckets) and its hash seed
type RhTab<-K: Data, -V: Data> is Data:
  RhTab{log: Nat, seed: U32, tree: RhTree<K, V>}

# The policy (README.md, "Parameters"): grow when the entries exceed
# grow_pct percent of the buckets, shrink (when auto_shrink is set) when
# they fall below shrink_pct percent, between 2^min_log and 2^max_log
# buckets; move steps old buckets per operation during a resize; start
# with 2^init_log buckets and seed, and give each new array the seed of
# the one before plus seed_step.
type RhParams is Data:
  RhParams{grow_pct: Nat, shrink_pct: Nat, auto_shrink: Bool, min_log: Nat, max_log: Nat, init_log: Nat, steps: Nat, seed: U32, seed_step: U32}

# The table: its policy, the number of keys, the current bucket array
# (where inserts go), the old one (empty unless a resize is under way) and
# the next old bucket to move
type RHash<-K: Data, -V: Data> is Data:
  RHash{params: RhParams, count: Nat, cur: RhTab<K, V>, old: RhTab<K, V>, cursor: U32}

# An operation, for running a sequence of them (RHash.run, RHash.replay)
type RhOp<-K: Data, -V: Data> is Data:
  RhIns{key: K, val: V}
  RhDel{key: K}
  RhStep{}
  RhResize{log: Nat, seed: U32}

# What a bucket operation does to one bucket (internal)
type RhBop<-K: Data, -V: Data> is Data:
  RhBIns{e: RhEntry<K, V>}
  RhBDel{kw: List<&2, U32>}
  RhBApp{e: RhEntry<K, V>}

# A bucket taken out of a tree: the path to it, its entries, and the tree
# without it (internal)
type RhTake<-K: Data, -V: Data> is Data:
  RhTake{path: List<&2, Bool>, es: List<&2, RhEntry<K, V>>, rest: RhTree<K, V>}

# ---------------------------------------------------------------- defaults

# The kernel's defaults as LWN describes them (README.md): grow past 70%,
# shrink below 30% when asked to, at least 4 buckets, at most 2^31, 64 to
# start; four old buckets moved per operation
def RhParams.default() -> RhParams:
  RhParams{70n, 30n, False{}, 2n, 31n, 6n, 4n, 0, 2654435769}

# The same, shrinking as well as growing
def RhParams.shrinking() -> RhParams:
  RhParams{70n, 30n, True{}, 2n, 31n, 6n, 4n, 0, 2654435769}

# The default hash: lookup3's hashword (khash's jhash2) of the words
def RHash.jhash2(seed: U32, ws: List<&2, U32>) -> U32:
  KH.Jhash.jhash2(ws, seed)

# Key encodings: a U32 key as one word, a word-list key as itself
def RHash.key_u32(k: U32) -> List<&2, U32>:
  [k]

def RHash.key_words(ws: List<&2, U32>) -> List<&2, U32>:
  ws

# ---------------------------------------------------------------- helpers

# equality of two encodings
def rh.weq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(U32.is_eq(x, y), rh.weq(xt, yt))
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}

# the first of two answers that is Some
def rh.orelse(~V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>) -> Maybe<&2, V>:
  match a:
    case Some{v}:
      Some{v}
    case None{}:
      b

def rh.hit(~V: Data, b: Bool, v: V, r: Maybe<&2, V>) -> Maybe<&2, V>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      r

def rh.miss(~V: Data, b: Bool, r: Maybe<&2, V>) -> Maybe<&2, V>:
  match b:
    case True{}:
      None{}
    case False{}:
      r

# the value of the first entry whose encoding is kw
def rh.find(~K: Data, ~V: Data, +kw: List<&2, U32>, es: List<&2, RhEntry<K, V>>) -> Maybe<&2, V>:
  match es:
    case Nil{}:
      None{}
    case Con{e, t}:
      match e:
        case RhEntry{w, k, v}:
          rh.hit(~V, rh.weq(kw, w), v, rh.find(~K, ~V, kw, t))

def rh.keep(~K: Data, ~V: Data, b: Bool, e: RhEntry<K, V>, r: List<&2, RhEntry<K, V>>) -> List<&2, RhEntry<K, V>>:
  match b:
    case True{}:
      r
    case False{}:
      Con{e, r}

# the entries whose encoding is not kw
def rh.drop(~K: Data, ~V: Data, +kw: List<&2, U32>, es: List<&2, RhEntry<K, V>>) -> List<&2, RhEntry<K, V>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      match e:
        case RhEntry{+w, k, v}:
          rh.keep(~K, ~V, rh.weq(kw, w), RhEntry{w, k, v}, rh.drop(~K, ~V, kw, t))

def rh.snoc(~K: Data, ~V: Data, es: List<&2, RhEntry<K, V>>, e: RhEntry<K, V>) -> List<&2, RhEntry<K, V>>:
  match es:
    case Nil{}:
      [e]
    case Con{h, t}:
      Con{h, rh.snoc(~K, ~V, t, e)}

def rh.apply(~K: Data, ~V: Data, op: RhBop<K, V>, es: List<&2, RhEntry<K, V>>) -> List<&2, RhEntry<K, V>>:
  match op:
    case RhBIns{e}:
      match e:
        case RhEntry{+w, k, v}:
          Con{RhEntry{w, k, v}, rh.drop(~K, ~V, w, es)}
    case RhBDel{w}:
      rh.drop(~K, ~V, w, es)
    case RhBApp{e}:
      rh.snoc(~K, ~V, es, e)

# the low n bits of h, least significant first: the path to h's bucket in
# an array of 2^n buckets
def rh.path(n: Nat, +h: U32) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{U32.is_eq(U32.and(1, h), 1), rh.path(p, U32.shr(h))}

def rh.pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(rh.pow2(p))

# ---------------------------------------------------------------- trees

# a complete tree of 2^n empty buckets
def RhTree.full(~K: Data, ~V: Data, n: Nat) -> RhTree<K, V>:
  match n:
    case 0n:
      RhLeaf{Nil{}}
    case 1n+p:
      +s = RhTree.full(~K, ~V, p)
      RhNode{s, s}

# the bucket a path leads to (past the end of the path, the low side)
def RhTree.get(~K: Data, ~V: Data, t: RhTree<K, V>, p: List<&2, Bool>) -> List<&2, RhEntry<K, V>>:
  match t:
    case RhLeaf{es}:
      es
    case RhNode{lo, hi}:
      match p:
        case Nil{}:
          RhTree.get(~K, ~V, lo, Nil{})
        case Con{b, ps}:
          match b:
            case True{}:
              RhTree.get(~K, ~V, hi, ps)
            case False{}:
              RhTree.get(~K, ~V, lo, ps)

# the tree with a bucket operation done on the bucket a path leads to
def RhTree.put(~K: Data, ~V: Data, t: RhTree<K, V>, p: List<&2, Bool>, op: RhBop<K, V>) -> RhTree<K, V>:
  match t:
    case RhLeaf{es}:
      RhLeaf{rh.apply(~K, ~V, op, es)}
    case RhNode{lo, hi}:
      match p:
        case Nil{}:
          RhNode{RhTree.put(~K, ~V, lo, Nil{}, op), hi}
        case Con{b, ps}:
          match b:
            case True{}:
              RhNode{lo, RhTree.put(~K, ~V, hi, ps, op)}
            case False{}:
              RhNode{RhTree.put(~K, ~V, lo, ps, op), hi}

def rh.is_empty(~K: Data, ~V: Data, t: RhTree<K, V>) -> Bool:
  match t:
    case RhLeaf{es}:
      match es:
        case Nil{}:
          True{}
        case Con{e, r}:
          False{}
    case RhNode{lo, hi}:
      False{}

def rh.prune.go(~K: Data, ~V: Data, ea: Bool, eb: Bool, a: RhTree<K, V>, b: RhTree<K, V>) -> RhTree<K, V>:
  match ea:
    case True{}:
      match eb:
        case True{}:
          RhLeaf{Nil{}}
        case False{}:
          RhNode{a, b}
    case False{}:
      RhNode{a, b}

# a node, collapsed to one empty bucket when both halves are empty
def rh.prune(~K: Data, ~V: Data, a: RhTree<K, V>, b: RhTree<K, V>) -> RhTree<K, V>:
  match a:
    case RhLeaf{+x}:
      match b:
        case RhLeaf{+y}:
          rh.prune.go(~K, ~V, rh.is_empty(~K, ~V, RhLeaf{x}), rh.is_empty(~K, ~V, RhLeaf{y}), RhLeaf{x}, RhLeaf{y})
        case RhNode{c, d}:
          RhNode{RhLeaf{x}, RhNode{c, d}}
    case RhNode{c, d}:
      RhNode{RhNode{c, d}, b}

def rh.take.lo(~K: Data, ~V: Data, r: RhTake<K, V>, hi: RhTree<K, V>) -> RhTake<K, V>:
  match r:
    case RhTake{tp, es, rest}:
      RhTake{Con{False{}, tp}, es, rh.prune(~K, ~V, rest, hi)}

def rh.take.hi(~K: Data, ~V: Data, lo: RhTree<K, V>, r: RhTake<K, V>) -> RhTake<K, V>:
  match r:
    case RhTake{tp, es, rest}:
      RhTake{Con{True{}, tp}, es, rh.prune(~K, ~V, lo, rest)}

# the bucket a path leads to, taken out of the tree: its entries, the path
# actually followed, and the tree with that bucket emptied (and nodes whose
# halves are both empty collapsed)
def rh.take(~K: Data, ~V: Data, t: RhTree<K, V>, p: List<&2, Bool>) -> RhTake<K, V>:
  match t:
    case RhLeaf{es}:
      RhTake{Nil{}, es, RhLeaf{Nil{}}}
    case RhNode{lo, hi}:
      match p:
        case Nil{}:
          rh.take.lo(~K, ~V, rh.take(~K, ~V, lo, Nil{}), hi)
        case Con{b, ps}:
          match b:
            case True{}:
              rh.take.hi(~K, ~V, lo, rh.take(~K, ~V, hi, ps))
            case False{}:
              rh.take.lo(~K, ~V, rh.take(~K, ~V, lo, ps), hi)

# whether a path q leads to the bucket that the followed path tp reached
def rh.follows(tp: List<&2, Bool>, q: List<&2, Bool>) -> Bool:
  match tp:
    case Nil{}:
      True{}
    case Con{b, tps}:
      match b:
        case True{}:
          match q:
            case Nil{}:
              False{}
            case Con{c, qs}:
              match c:
                case True{}:
                  rh.follows(tps, qs)
                case False{}:
                  False{}
        case False{}:
          match q:
            case Nil{}:
              rh.follows(tps, Nil{})
            case Con{c, qs}:
              match c:
                case True{}:
                  False{}
                case False{}:
                  rh.follows(tps, qs)

# ---------------------------------------------------------------- tables

# the path to a key's bucket in a bucket array
def RhTab.path(~hash: U32 -> List<&2, U32> -> U32, log: Nat, seed: U32, kw: List<&2, U32>) -> List<&2, Bool>:
  rh.path(log, hash(seed, kw))

def RhTab.find(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, tab: RhTab<K, V>, +kw: List<&2, U32>) -> Maybe<&2, V>:
  match tab:
    case RhTab{log, seed, tree}:
      rh.find(~K, ~V, kw, RhTree.get(~K, ~V, tree, RhTab.path(~hash, log, seed, kw)))

def RhTab.put(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, tab: RhTab<K, V>, +kw: List<&2, U32>, op: RhBop<K, V>) -> RhTab<K, V>:
  match tab:
    case RhTab{+log, +seed, tree}:
      RhTab{log, seed, RhTree.put(~K, ~V, tree, RhTab.path(~hash, log, seed, kw), op)}

def RhTab.empty(~K: Data, ~V: Data, +log: Nat, seed: U32) -> RhTab<K, V>:
  RhTab{log, seed, RhTree.full(~K, ~V, log)}

# ---------------------------------------------------------------- the table by encodings (internal)

# the value of a key: in the current array, then in the old one
def rh.lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>, +kw: List<&2, U32>) -> Maybe<&2, V>:
  match t:
    case RHash{p, n, cur, old, c}:
      rh.orelse(~V, RhTab.find(~K, ~V, ~hash, cur, kw), RhTab.find(~K, ~V, ~hash, old, kw))

def rh.bump(present: Bool, n: Nat) -> Nat:
  match present:
    case True{}:
      n
    case False{}:
      1n+n

def rh.unbump(present: Bool, n: Nat) -> Nat:
  match present:
    case True{}:
      Nat.sub(n, 1n)
    case False{}:
      n

def rh.present(~V: Data, m: Maybe<&2, V>) -> Bool:
  match m:
    case Some{v}:
      True{}
    case None{}:
      False{}

# insert or replace, before any resize work: the key leaves both arrays and
# goes to the front of its bucket in the current one
def rh.ins(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, present: Bool, t: RHash<K, V>, +kw: List<&2, U32>, k: K, v: V) -> RHash<K, V>:
  match t:
    case RHash{p, n, cur, old, c}:
      RHash{p, rh.bump(present, n), RhTab.put(~K, ~V, ~hash, cur, kw, RhBIns{RhEntry{kw, k, v}}), RhTab.put(~K, ~V, ~hash, old, kw, RhBDel{kw}), c}

# remove, before any resize work: the key leaves both arrays
def rh.del(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, present: Bool, t: RHash<K, V>, +kw: List<&2, U32>) -> RHash<K, V>:
  match t:
    case RHash{p, n, cur, old, c}:
      RHash{p, rh.unbump(present, n), RhTab.put(~K, ~V, ~hash, cur, kw, RhBDel{kw}), RhTab.put(~K, ~V, ~hash, old, kw, RhBDel{kw}), c}

# ---------------------------------------------------------------- migration

def rh.mig1.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, vis: Bool, cur: RhTab<K, V>, e: RhEntry<K, V>) -> RhTab<K, V>:
  match vis:
    case True{}:
      match e:
        case RhEntry{+w, k, v}:
          RhTab.put(~K, ~V, ~hash, cur, w, RhBApp{RhEntry{w, k, v}})
    case False{}:
      cur

# one entry of a taken old bucket into the current array, at the end of
# its bucket, if its key belongs in the bucket taken (one that does not was
# never found by a lookup, and is dropped)
def rh.mig1(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, cur: RhTab<K, V>, e: RhEntry<K, V>) -> RhTab<K, V>:
  match e:
    case RhEntry{+w, k, v}:
      rh.mig1.go(~K, ~V, ~hash, rh.follows(tp, RhTab.path(~hash, olog, oseed, w)), cur, RhEntry{w, k, v})

def rh.mig(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, es: List<&2, RhEntry<K, V>>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, cur: RhTab<K, V>) -> RhTab<K, V>:
  match es:
    case Nil{}:
      cur
    case Con{e, t}:
      rh.mig(~K, ~V, ~hash, t, tp, olog, oseed, rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, e))

# the next old bucket after c in an array of 2^log buckets (wrapping)
def rh.next(c: U32, log: Nat) -> U32:
  U32.and(U32.add(c, 1), U32.sub(U32.shln(1, log), 1))

def rh.step.take(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, p: RhParams, n: Nat, cur: RhTab<K, V>, +olog: Nat, +oseed: U32, +c: U32, r: RhTake<K, V>) -> RHash<K, V>:
  match r:
    case RhTake{+tp, es, rest}:
      RHash{p, n, rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), RhTab{olog, oseed, rest}, rh.next(c, olog)}

def rh.step.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, done: Bool, p: RhParams, n: Nat, cur: RhTab<K, V>, old: RhTab<K, V>, +c: U32) -> RHash<K, V>:
  match done:
    case True{}:
      RHash{p, n, cur, old, c}
    case False{}:
      match old:
        case RhTab{+olog, +oseed, otree}:
          rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, rh.take(~K, ~V, otree, rh.path(olog, c)))

def rh.old_empty(~K: Data, ~V: Data, old: RhTab<K, V>) -> Bool:
  match old:
    case RhTab{log, seed, tree}:
      rh.is_empty(~K, ~V, tree)

# one migration step: the old bucket at the cursor moves into the current
# array; nothing when no resize is under way
def rh.step(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>) -> RHash<K, V>:
  match t:
    case RHash{p, n, cur, +old, c}:
      rh.step.go(~K, ~V, ~hash, rh.old_empty(~K, ~V, old), p, n, cur, old, c)

def rh.steps(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, k: Nat, t: RHash<K, V>) -> RHash<K, V>:
  match k:
    case 0n:
      t
    case 1n+j:
      rh.steps(~K, ~V, ~hash, j, rh.step(~K, ~V, ~hash, t))

# ---------------------------------------------------------------- resizing

def rh.start.go(~K: Data, ~V: Data, idle: Bool, t: RHash<K, V>, log: Nat, seed: U32) -> RHash<K, V>:
  match idle:
    case True{}:
      match t:
        case RHash{p, n, cur, old, c}:
          RHash{p, n, RhTab.empty(~K, ~V, log, seed), cur, 0}
    case False{}:
      t

def rh.idle(~K: Data, ~V: Data, t: RHash<K, V>) -> Bool:
  match t:
    case RHash{p, n, cur, old, c}:
      rh.old_empty(~K, ~V, old)

# start a resize to 2^log buckets with a seed: the current array becomes
# the old one; nothing if a resize is already under way
def rh.start(~K: Data, ~V: Data, +t: RHash<K, V>, log: Nat, seed: U32) -> RHash<K, V>:
  rh.start.go(~K, ~V, rh.idle(~K, ~V, t), t, log, seed)

# the size the policy asks for, if it asks for one
def rh.want.go(grow: Bool, shrink: Bool, +log: Nat) -> Maybe<&2, Nat>:
  match grow:
    case True{}:
      Some{1n+log}
    case False{}:
      match shrink:
        case True{}:
          Some{Nat.sub(log, 1n)}
        case False{}:
          None{}

def rh.want(p: RhParams, +n: Nat, +log: Nat) -> Maybe<&2, Nat>:
  match p:
    case RhParams{gp, sp, auto, minl, maxl, il, st, s0, ss}:
      rh.want.go(Bool.and(Nat.is_lt(log, maxl), Nat.is_lt(Nat.mul(gp, rh.pow2(log)), Nat.mul(n, 100n))), Bool.and(auto, Bool.and(Nat.is_lt(minl, log), Nat.is_lt(Nat.mul(n, 100n), Nat.mul(sp, rh.pow2(log))))), log)

def rh.auto.go(~K: Data, ~V: Data, w: Maybe<&2, Nat>, +t: RHash<K, V>, seed: U32) -> RHash<K, V>:
  match w:
    case None{}:
      t
    case Some{log}:
      rh.start(~K, ~V, t, log, seed)

def rh.seed_step(p: RhParams) -> U32:
  match p:
    case RhParams{gp, sp, auto, minl, maxl, il, st, s0, ss}:
      ss

def rh.nsteps(p: RhParams) -> Nat:
  match p:
    case RhParams{gp, sp, auto, minl, maxl, il, st, s0, ss}:
      st

# after an operation: a resize when idle and the policy asks for one
def rh.auto(~K: Data, ~V: Data, t: RHash<K, V>) -> RHash<K, V>:
  match t:
    case RHash{+p, +n, cur, old, c}:
      match cur:
        case RhTab{+log, +seed, tree}:
          rh.auto.go(~K, ~V, rh.want(p, n, log), RHash{p, n, RhTab{log, seed, tree}, old, c}, U32.add(seed, rh.seed_step(p)))

# the resize work that follows every operation: steps, then the policy
def rh.after(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>) -> RHash<K, V>:
  match t:
    case RHash{+p, n, cur, old, c}:
      rh.auto(~K, ~V, rh.steps(~K, ~V, ~hash, rh.nsteps(p), RHash{p, n, cur, old, c}))

def rh.old_log(~K: Data, ~V: Data, t: RHash<K, V>) -> Nat:
  match t:
    case RHash{p, n, cur, old, c}:
      match old:
        case RhTab{log, seed, tree}:
          log

# ---------------------------------------------------------------- the interface

# an empty table with a policy
def RHash.new(~K: Data, ~V: Data, +p: RhParams) -> RHash<K, V>:
  match p:
    case RhParams{gp, sp, auto, minl, maxl, +il, st, +s0, ss}:
      RHash{RhParams{gp, sp, auto, minl, maxl, il, st, s0, ss}, 0n, RhTab.empty(~K, ~V, il, s0), RhTab{0n, s0, RhLeaf{Nil{}}}, 0}

# the value of a key, if it is present
def RHash.lookup(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>, k: K) -> Maybe<&2, V>:
  rh.lookup(~K, ~V, ~hash, t, kenc(k))

def RHash.contains(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>, k: K) -> Bool:
  rh.present(~V, RHash.lookup(~K, ~V, ~kenc, ~hash, t, k))

# the number of keys present
def RHash.size(~K: Data, ~V: Data, t: RHash<K, V>) -> Nat:
  match t:
    case RHash{p, n, cur, old, c}:
      n

# whether two keys are the same key (their encodings are equal)
def RHash.same_key(~K: Data, ~kenc: K -> List<&2, U32>, a: K, b: K) -> Bool:
  rh.weq(kenc(a), kenc(b))

# k bound to v (replacing any value it had), then the resize work
def RHash.insert(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: RHash<K, V>, +k: K, v: V) -> RHash<K, V>:
  rh.after(~K, ~V, ~hash, rh.ins(~K, ~V, ~hash, RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v))

# k removed (if present), then the resize work
def RHash.remove(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: RHash<K, V>, +k: K) -> RHash<K, V>:
  rh.after(~K, ~V, ~hash, rh.del(~K, ~V, ~hash, RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)))

# one migration step, explicitly (nothing when no resize is under way)
def RHash.step(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>) -> RHash<K, V>:
  rh.step(~K, ~V, ~hash, t)

def RHash.steps(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, k: Nat, t: RHash<K, V>) -> RHash<K, V>:
  rh.steps(~K, ~V, ~hash, k, t)

# whether a resize is under way (the old array still holds buckets)
def RHash.resizing(~K: Data, ~V: Data, t: RHash<K, V>) -> Bool:
  Bool.not(rh.idle(~K, ~V, t))

# the current array has 2^log buckets
def RHash.log(~K: Data, ~V: Data, t: RHash<K, V>) -> Nat:
  match t:
    case RHash{p, n, cur, old, c}:
      match cur:
        case RhTab{log, seed, tree}:
          log

# a resize under way finished: one step per old bucket
def RHash.drain(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: RHash<K, V>) -> RHash<K, V>:
  rh.steps(~K, ~V, ~hash, rh.pow2(rh.old_log(~K, ~V, t)), t)

# an explicit resize to 2^log buckets with a seed: any resize under way is
# finished first, and then the new one starts (its steps follow later
# operations, or RHash.step)
def RHash.resize(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>, log: Nat, seed: U32) -> RHash<K, V>:
  rh.start(~K, ~V, RHash.drain(~K, ~V, ~hash, t), log, seed)

# one operation
def RHash.apply(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>, op: RhOp<K, V>) -> RHash<K, V>:
  match op:
    case RhIns{k, v}:
      RHash.insert(~K, ~V, ~kenc, ~hash, t, k, v)
    case RhDel{k}:
      RHash.remove(~K, ~V, ~kenc, ~hash, t, k)
    case RhStep{}:
      RHash.step(~K, ~V, ~hash, t)
    case RhResize{log, seed}:
      RHash.resize(~K, ~V, ~hash, t, log, seed)

# operations in order, the first first
def rh.run(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, ops: List<&2, RhOp<K, V>>, t: RHash<K, V>) -> RHash<K, V>:
  match ops:
    case Nil{}:
      t
    case Con{op, rest}:
      rh.run(~K, ~V, ~kenc, ~hash, rest, RHash.apply(~K, ~V, ~kenc, ~hash, t, op))

def RHash.run(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, t: RHash<K, V>, ops: List<&2, RhOp<K, V>>) -> RHash<K, V>:
  rh.run(~K, ~V, ~kenc, ~hash, ops, t)

# a trace, the latest operation first, replayed on an empty table
def RHash.replay(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +p: RhParams, tr: List<&2, RhOp<K, V>>) -> RHash<K, V>:
  match tr:
    case Nil{}:
      RHash.new(~K, ~V, p)
    case Con{op, older}:
      RHash.apply(~K, ~V, ~kenc, ~hash, RHash.replay(~K, ~V, ~kenc, ~hash, p, older), op)
