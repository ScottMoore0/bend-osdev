# The laws of the resizable hash table, for every key type K and value
# type V, every key encoding (~kenc), every hash function (~hash), every
# table t and every key, over the public interface only. Two keys are the
# same key when RHash.same_key says so (their encodings are equal).
#
# The map: a new table holds nothing; after an insert a key's lookup is
# its value, and every other key's lookup is unchanged; after a remove a
# key's lookup is None, and every other key's is unchanged. size counts
# keys: an insert of an absent key adds one, of a present key nothing; a
# remove of a present key takes one away, of an absent key nothing.
#
# The property rhashtable exists for: a resize is in progress across
# operations, and a migration step (RHash.step), any number of them, a
# drain and an explicit resize change no key's lookup and not the size;
# so at every intermediate step of a migration, lookup finds every key
# that is present. Over any interleaving of operations and migration
# steps: replaying a trace on a new table gives, for every key, the
# reference model's value (model.bend: an association list that never
# resizes), and the model's number of keys; and running operations on any
# table moves each key's lookup exactly as the model moves it.
#
# These hold for every state, not only for states reached from RHash.new:
# the table needs no invariant for lookups to be right (README.md, "How a
# lookup stays right").
#
# Vectors: a few operations on a table with the default policy and hash.
import Base
import ./rhash.bend as R
import ./model.bend as M

# A new table

law lookup_new:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +p: R.RhParams
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.new(~K, ~V, p), k) == None{} : Maybe<&2, V>}

law size_new:
  for ~K: Data
  for ~V: Data
  for +p: R.RhParams
  {R.RHash.size(~K, ~V, R.RHash.new(~K, ~V, p)) == 0n : Nat}

# The map laws

law lookup_insert:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for +v: V
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k, v), k) == Some{v} : Maybe<&2, V>}

law lookup_insert_other:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for +j: K
  for +v: V
  for e: {R.RHash.same_key(~K, ~kenc, k, j) == False{} : Bool}
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k, v), j) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, j) : Maybe<&2, V>}

law lookup_remove:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k), k) == None{} : Maybe<&2, V>}

law lookup_remove_other:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for +j: K
  for e: {R.RHash.same_key(~K, ~kenc, k, j) == False{} : Bool}
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k), j) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, j) : Maybe<&2, V>}

# a key's lookup sees the same key under any encoding-equal name
law lookup_same_key:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for +j: K
  for e: {R.RHash.same_key(~K, ~kenc, k, j) == True{} : Bool}
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, j) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k) : Maybe<&2, V>}

# Size

law size_insert_absent:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for +v: V
  for h: {R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k) == False{} : Bool}
  {R.RHash.size(~K, ~V, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k, v)) == 1n+R.RHash.size(~K, ~V, t) : Nat}

law size_insert_present:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for +v: V
  for h: {R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k) == True{} : Bool}
  {R.RHash.size(~K, ~V, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k, v)) == R.RHash.size(~K, ~V, t) : Nat}

law size_remove_present:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for h: {R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k) == True{} : Bool}
  {R.RHash.size(~K, ~V, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k)) == Nat.sub(R.RHash.size(~K, ~V, t), 1n) : Nat}

law size_remove_absent:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  for h: {R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k) == False{} : Bool}
  {R.RHash.size(~K, ~V, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k)) == R.RHash.size(~K, ~V, t) : Nat}

# Migration: no step of a resize changes what the table holds

law lookup_step:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.step(~K, ~V, ~hash, t), k) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k) : Maybe<&2, V>}

law size_step:
  for ~K: Data
  for ~V: Data
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  {R.RHash.size(~K, ~V, R.RHash.step(~K, ~V, ~hash, t)) == R.RHash.size(~K, ~V, t) : Nat}

law lookup_steps:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +n: Nat
  for +t: R.RHash<K, V>
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.steps(~K, ~V, ~hash, n, t), k) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k) : Maybe<&2, V>}

law lookup_drain:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.drain(~K, ~V, ~hash, t), k) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k) : Maybe<&2, V>}

law lookup_resize:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +log: Nat
  for +seed: U32
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.resize(~K, ~V, ~hash, t, log, seed), k) == R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k) : Maybe<&2, V>}

law size_resize:
  for ~K: Data
  for ~V: Data
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +log: Nat
  for +seed: U32
  {R.RHash.size(~K, ~V, R.RHash.resize(~K, ~V, ~hash, t, log, seed)) == R.RHash.size(~K, ~V, t) : Nat}

# Any interleaving of operations and migration steps

# from any table: each key's lookup moves as the model moves it
law lookup_run:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +t: R.RHash<K, V>
  for +ops: List<&2, R.RhOp<K, V>>
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.run(~K, ~V, ~kenc, ~hash, t, ops), k) == M.RhModel.after(~K, ~V, ~kenc, ops, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}

# from a new table: the table holds what the model holds
law lookup_replay:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +p: R.RhParams
  for +tr: List<&2, R.RhOp<K, V>>
  for +k: K
  {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr), k) == M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, tr), k) : Maybe<&2, V>}

law size_replay:
  for ~K: Data
  for ~V: Data
  for ~kenc: K -> List<&2, U32>
  for ~hash: U32 -> List<&2, U32> -> U32
  for +p: R.RhParams
  for +tr: List<&2, R.RhOp<K, V>>
  {R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr)) == M.RhModel.size(~K, ~V, M.RhModel.replay(~K, ~V, ~kenc, tr)) : Nat}

# Vectors: U32 keys and values, the default policy and hash
law vec_lookup:
  {R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.remove(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.insert(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.insert(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.new(~U32, ~U32, R.RhParams.default()), 1, 10), 2, 20), 1), 2) == Some{20} : Maybe<&2, U32>}

law vec_size:
  {R.RHash.size(~U32, ~U32, R.RHash.remove(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.insert(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.insert(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, R.RHash.new(~U32, ~U32, R.RhParams.default()), 1, 10), 2, 20), 1)) == 1n : Nat}
