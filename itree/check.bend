import Base
import ../word64/word64.bend as W
import ./itree.bend as T

def show_e(e: T.ITreeEntry<U32, U32>) -> String:
  match e:
    case T.ITreeEntry{s, l, v}:
      U32.show(s) ++ "-" ++ U32.show(l) ++ ":" ++ U32.show(v)

def show_list(xs: List<&2, T.ITreeEntry<U32, U32>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      " " ++ show_e(x) ++ show_list(r)

def show_maybe(m: Maybe<&2, T.ITreeEntry<U32, U32>>) -> String:
  match m:
    case None{}:
      " none"
    case Some{x}:
      " " ++ show_e(x)

def show_value(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

def show_insert(r: Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, U32>>) -> String:
  match r:
    case Fail{T.ITreeInverted{s, l}}:
      "inverted " ++ U32.show(s) ++ " " ++ U32.show(l)
    case Done{t}:
      "ok"

# [10, 20], [5, 8], [15, 30], [25, 26], [1, 3], with values 1 to 5
def demo() -> T.ITree<U32, U32>:
  T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.set(U32, T.ITree32.empty(U32), 10, 20, 1), 5, 8, 2), 15, 30, 3), 25, 26, 4), 1, 3, 5)

# iteration: first, then next from each answer
def walk(fuel: Nat, +t: T.ITree<U32, U32>, +a: U32, +b: U32, cur: Maybe<&2, T.ITreeEntry<U32, U32>>) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+p:
      match cur:
        case None{}:
          ""
        case Some{+x}:
          " " ++ show_e(x) ++ walk(p, t, a, b, T.ITree32.next(U32, t, a, b, T.ITreeEntry.start(U32, U32, x), T.ITreeEntry.last(U32, U32, x)))

# [k, k + 10] holding k, for k below n
def build(n: Nat, t: T.ITree<U32, U32>) -> T.ITree<U32, U32>:
  match n:
    case 0n:
      t
    case 1n+ +p:
      +k = U32.from_nat(p)
      build(p, T.ITree32.set(U32, t, k, (k + 10 : U32), k))

# without [k, k + 10] for the even k below n
def drop_even(n: Nat, t: T.ITree<U32, U32>) -> T.ITree<U32, U32>:
  match n:
    case 0n:
      t
    case 1n+ +p:
      +k = U32.from_nat(Nat.mul(2n, p))
      drop_even(p, T.ITree32.remove(U32, t, k, (k + 10 : U32)))

def stats(+t: T.ITree<U32, U32>) -> String:
  "size " ++ Nat.show(T.ITree32.size(U32, t)) ++ " height " ++ Nat.show(T.ITree32.height(U32, t)) ++ " valid " ++ Bool.show(T.ITree32.valid(U32, t)) ++ " balanced " ++ Bool.show(T.ITree32.balanced(U32, t))

# a tree keyed by W64: the same code, with W64's order as the template
def mapping() -> T.ITree<W.W64, U32>:
  T.ITree.set(~W.W64, ~W.W64.cmp, U32, T.ITree.set(~W.W64, ~W.W64.cmp, U32, T.ITree.empty(W.W64, U32), W.W64.from_parts(1, 0), W.W64.from_parts(1, 4095), 7), W.W64.from_parts(2, 0), W.W64.from_parts(2, 8191), 8)

def show_w(m: Maybe<&2, T.ITreeEntry<W.W64, U32>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{T.ITreeEntry{s, l, v}}:
      W.W64.show_hex(s) ++ "-" ++ W.W64.show_hex(l) ++ ":" ++ U32.show(v)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("contents:" ++ show_list(T.ITree32.to_list(U32, demo())))
    IO.print("overlapping 7 12:" ++ show_list(T.ITree32.overlapping(U32, demo(), 7, 12)))
    IO.print("stab 25:" ++ show_list(T.ITree32.stab(U32, demo(), 25)))
    IO.print("first 9 40:" ++ show_maybe(T.ITree32.first(U32, demo(), 9, 40)))
    IO.print("next 9 40 after 10-20:" ++ show_maybe(T.ITree32.next(U32, demo(), 9, 40, 10, 20)))
    IO.print("walk 9 40:" ++ walk(10n, demo(), 9, 40, T.ITree32.first(U32, demo(), 9, 40)))
    IO.print("first 31 40:" ++ show_maybe(T.ITree32.first(U32, demo(), 31, 40)))
    IO.print("lookup 15 30: " ++ show_value(T.ITree32.lookup(U32, demo(), 15, 30)))
    IO.print("lookup 15 31: " ++ show_value(T.ITree32.lookup(U32, demo(), 15, 31)))
    IO.print("set 15 30 to 9, lookup: " ++ show_value(T.ITree32.lookup(U32, T.ITree32.set(U32, demo(), 15, 30, 9), 15, 30)))
    IO.print("remove 15 30, overlapping 21 40:" ++ show_list(T.ITree32.overlapping(U32, T.ITree32.remove(U32, demo(), 15, 30), 21, 40)))
    IO.print("insert 9 3: " ++ show_insert(T.ITree32.insert(U32, demo(), 9, 3, 0)))
    IO.print("insert 3 9: " ++ show_insert(T.ITree32.insert(U32, demo(), 3, 9, 0)))
    IO.print("max_last: " ++ show_value(T.ITree32.max_last(U32, demo())))
    IO.print("demo: " ++ stats(demo()))
    IO.print("1000 intervals: " ++ stats(build(1000n, T.ITree32.empty(U32))))
    IO.print("stab 500 of 1000: " ++ Nat.show(List.length(&2, T.ITreeEntry<U32, U32>, T.ITree32.stab(U32, build(1000n, T.ITree32.empty(U32)), 500))))
    IO.print("odd ones left: " ++ stats(drop_even(500n, build(1000n, T.ITree32.empty(U32)))))
    IO.print("stab 500 of odd: " ++ Nat.show(List.length(&2, T.ITreeEntry<U32, U32>, T.ITree32.stab(U32, drop_even(500n, build(1000n, T.ITree32.empty(U32))), 500))))
    IO.print("W64 stab 2:100: " ++ show_w(T.ITree.first(~W.W64, ~W.W64.cmp, U32, mapping(), W.W64.from_parts(2, 100), W.W64.from_parts(2, 100))))
    IO.print("W64 stab 1:5000: " ++ show_w(T.ITree.first(~W.W64, ~W.W64.cmp, U32, mapping(), W.W64.from_parts(1, 5000), W.W64.from_parts(1, 5000))))

#|contents: 1-3:5 5-8:2 10-20:1 15-30:3 25-26:4
#|overlapping 7 12: 5-8:2 10-20:1
#|stab 25: 15-30:3 25-26:4
#|first 9 40: 10-20:1
#|next 9 40 after 10-20: 15-30:3
#|walk 9 40: 10-20:1 15-30:3 25-26:4
#|first 31 40: none
#|lookup 15 30: 3
#|lookup 15 31: none
#|set 15 30 to 9, lookup: 9
#|remove 15 30, overlapping 21 40: 25-26:4
#|insert 9 3: inverted 9 3
#|insert 3 9: ok
#|max_last: 30
#|demo: size 5 height 3 valid True balanced True
#|1000 intervals: size 1000 height 10 valid True balanced True
#|stab 500 of 1000: 11
#|odd ones left: size 500 height 9 valid True balanced True
#|stab 500 of odd: 5
#|W64 stab 2:100: 0000000200000000-0000000200001fff:8
#|W64 stab 1:5000: none
