import Base
import ./rhash.bend as R

def show(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

def ins_from(n: Nat, +i: U32, t: R.RHash<U32, U32>) -> R.RHash<U32, U32>:
  match n:
    case 0n:
      t
    case 1n+p:
      ins_from(p, U32.add(i, 1), R.RHash.insert(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t, i, U32.mul(i, 3)))

# remove i, i + step, i + 2 step, ... (n keys)
def del_from(n: Nat, +i: U32, +step: U32, t: R.RHash<U32, U32>) -> R.RHash<U32, U32>:
  match n:
    case 0n:
      t
    case 1n+p:
      del_from(p, U32.add(i, step), step, R.RHash.remove(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t, i))

def found.go(ok: Bool, m: Maybe<&2, U32>, +want: U32) -> Bool:
  match ok:
    case False{}:
      False{}
    case True{}:
      match m:
        case None{}:
          False{}
        case Some{v}:
          U32.is_eq(v, want)

# whether the odd keys below 2n are all present with their values
def odd_found(n: Nat, +i: U32, +t: R.RHash<U32, U32>, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok
    case 1n+p:
      odd_found(p, U32.add(i, 2), t, found.go(ok, R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t, i), U32.mul(i, 3)))

def step_n(n: Nat, t: R.RHash<U32, U32>) -> R.RHash<U32, U32>:
  R.RHash.steps(~U32, ~U32, ~R.RHash.jhash2, n, t)

# 16 migration steps at a time, n times, checking every odd key after each
def batches(n: Nat, t: R.RHash<U32, U32>, ok: Bool) -> Bool:
  match n:
    case 0n:
      ok
    case 1n+p:
      +t2 = step_n(16n, t)
      batches(p, t2, Bool.and(ok, odd_found(500n, 1, t2, True{})))

def wkey(a: U32, b: U32) -> List<&2, U32>:
  [a, b]

def main() -> IO(Unit):
  +t1 = ins_from(1000n, 0, R.RHash.new(~U32, ~U32, R.RhParams.default()))
  +t2 = del_from(500n, 0, 2, t1)
  +t3 = R.RHash.resize(~U32, ~U32, ~R.RHash.jhash2, t2, 3n, 5)
  +t4 = step_n(100n, t3)
  +t5 = R.RHash.drain(~U32, ~U32, ~R.RHash.jhash2, t3)
  +w0 = R.RHash.new(~List<&2, U32>, ~U32, R.RhParams.default())
  +w1 = R.RHash.insert(~List<&2, U32>, ~U32, ~R.RHash.key_words, ~R.RHash.jhash2, R.RHash.insert(~List<&2, U32>, ~U32, ~R.RHash.key_words, ~R.RHash.jhash2, w0, wkey(1, 2), 12), wkey(2, 1), 21)
  +s1 = ins_from(300n, 0, R.RHash.new(~U32, ~U32, R.RhParams.shrinking()))
  +s2 = R.RHash.drain(~U32, ~U32, ~R.RHash.jhash2, del_from(290n, 0, 1, s1))
  +s3 = R.RHash.drain(~U32, ~U32, ~R.RHash.jhash2, R.RHash.remove(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, s2, 299))
  do IO<Unit>:
    IO.print("1000 keys: size " ++ Nat.show(R.RHash.size(~U32, ~U32, t1)) ++ ", 2^" ++ Nat.show(R.RHash.log(~U32, ~U32, t1)) ++ " buckets")
    IO.print("lookup 7: " ++ show(R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t1, 7)) ++ ", 999: " ++ show(R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t1, 999)) ++ ", 1000: " ++ show(R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t1, 1000)))
    IO.print("evens removed: size " ++ Nat.show(R.RHash.size(~U32, ~U32, t2)) ++ ", lookup 8: " ++ show(R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t2, 8)) ++ ", 9: " ++ show(R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, t2, 9)))
    IO.print("resize to 2^3: resizing " ++ Bool.show(R.RHash.resizing(~U32, ~U32, t3)) ++ ", every odd key found: " ++ Bool.show(odd_found(500n, 1, t3, True{})))
    IO.print("100 steps in: resizing " ++ Bool.show(R.RHash.resizing(~U32, ~U32, t4)) ++ ", size " ++ Nat.show(R.RHash.size(~U32, ~U32, t4)) ++ ", every odd key found: " ++ Bool.show(odd_found(500n, 1, t4, True{})))
    IO.print("128 batches of 16 steps, every odd key found after each: " ++ Bool.show(batches(128n, t3, True{})) ++ ", resizing after them: " ++ Bool.show(R.RHash.resizing(~U32, ~U32, step_n(2048n, t3))))
    IO.print("drained: resizing " ++ Bool.show(R.RHash.resizing(~U32, ~U32, t5)) ++ ", 2^" ++ Nat.show(R.RHash.log(~U32, ~U32, t5)) ++ " buckets, every odd key found: " ++ Bool.show(odd_found(500n, 1, t5, True{})))
    IO.print("word keys: [1, 2] " ++ show(R.RHash.lookup(~List<&2, U32>, ~U32, ~R.RHash.key_words, ~R.RHash.jhash2, w1, wkey(1, 2))) ++ ", [2, 1] " ++ show(R.RHash.lookup(~List<&2, U32>, ~U32, ~R.RHash.key_words, ~R.RHash.jhash2, w1, wkey(2, 1))) ++ ", [1] " ++ show(R.RHash.lookup(~List<&2, U32>, ~U32, ~R.RHash.key_words, ~R.RHash.jhash2, w1, [1])))
    IO.print("shrinking: 300 keys 2^" ++ Nat.show(R.RHash.log(~U32, ~U32, s1)) ++ ", 10 left 2^" ++ Nat.show(R.RHash.log(~U32, ~U32, s2)) ++ ", 9 left 2^" ++ Nat.show(R.RHash.log(~U32, ~U32, s3)) ++ ", lookup 295: " ++ show(R.RHash.lookup(~U32, ~U32, ~R.RHash.key_u32, ~R.RHash.jhash2, s3, 295)))

#|1000 keys: size 1000, 2^11 buckets
#|lookup 7: 21, 999: 2997, 1000: none
#|evens removed: size 500, lookup 8: none, 9: 27
#|resize to 2^3: resizing True, every odd key found: True
#|100 steps in: resizing True, size 500, every odd key found: True
#|128 batches of 16 steps, every odd key found after each: True, resizing after them: False
#|drained: resizing False, 2^3 buckets, every odd key found: True
#|word keys: [1, 2] 12, [2, 1] 21, [1] none
#|shrinking: 300 keys 2^9, 10 left 2^7, 9 left 2^6, lookup 295: 885
