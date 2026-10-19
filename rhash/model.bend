# The reference model of the table: an association list, newest binding
# first, with no resizing at all, so that the laws (LAWS.bend) can say what
# the table holds after any sequence of operations, resize steps among
# them. A key is bound at most once (an insert drops the key's old binding
# before adding the new one), so its length is the number of keys.
import Base
import ./rhash.bend as R

def RhModel.empty(~K: Data, ~V: Data) -> List<&2, R.RhEntry<K, V>>:
  Nil{}

# one operation on the model: a resize or a step changes nothing
def RhModel.apply(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, m: List<&2, R.RhEntry<K, V>>, op: R.RhOp<K, V>) -> List<&2, R.RhEntry<K, V>>:
  match op:
    case R.RhIns{+k, v}:
      Con{R.RhEntry{kenc(k), k, v}, R.rh.drop(~K, ~V, kenc(k), m)}
    case R.RhDel{k}:
      R.rh.drop(~K, ~V, kenc(k), m)
    case R.RhStep{}:
      m
    case R.RhResize{log, seed}:
      m

# a trace, the latest operation first, replayed on the empty model
def RhModel.replay(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, tr: List<&2, R.RhOp<K, V>>) -> List<&2, R.RhEntry<K, V>>:
  match tr:
    case Nil{}:
      Nil{}
    case Con{op, older}:
      RhModel.apply(~K, ~V, ~kenc, RhModel.replay(~K, ~V, ~kenc, older), op)

def RhModel.lookup(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, m: List<&2, R.RhEntry<K, V>>, k: K) -> Maybe<&2, V>:
  R.rh.find(~K, ~V, kenc(k), m)

def RhModel.size(~K: Data, ~V: Data, m: List<&2, R.RhEntry<K, V>>) -> Nat:
  List.length(&2, R.RhEntry<K, V>, m)

# One key's value through operations in order, the first first, starting
# from its value before them: an insert of the same key binds it, a remove
# of it unbinds it, and nothing else changes it
def RhModel.after.op(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, op: R.RhOp<K, V>, +k: K, m: Maybe<&2, V>) -> Maybe<&2, V>:
  match op:
    case R.RhIns{k2, v}:
      R.rh.hit(~V, R.RHash.same_key(~K, ~kenc, k2, k), v, m)
    case R.RhDel{k2}:
      R.rh.miss(~V, R.RHash.same_key(~K, ~kenc, k2, k), m)
    case R.RhStep{}:
      m
    case R.RhResize{log, seed}:
      m

def RhModel.after(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ops: List<&2, R.RhOp<K, V>>, +k: K, m: Maybe<&2, V>) -> Maybe<&2, V>:
  match ops:
    case Nil{}:
      m
    case Con{op, rest}:
      RhModel.after(~K, ~V, ~kenc, rest, k, RhModel.after.op(~K, ~V, ~kenc, op, k, m))
