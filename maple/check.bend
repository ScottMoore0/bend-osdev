import Base
import ../word64/word64.bend as W
import ./model.bend as M
import ./node.bend as N
import ./maple.bend as T
import ./gap.bend as G

def show_e(e: M.MapleEntry<U32, U32>) -> String:
  match e:
    case M.MapleEntry{f, l, v}:
      U32.show(f) ++ "-" ++ U32.show(l) ++ ":" ++ U32.show(v)

def show_list(xs: List<&2, M.MapleEntry<U32, U32>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      " " ++ show_e(x) ++ show_list(r)

def show_maybe(m: Maybe<&2, M.MapleEntry<U32, U32>>) -> String:
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

def show_gap(r: Result<&2, &2, M.MapleError<U32>, U32>) -> String:
  match r:
    case Done{s}:
      U32.show(s)
    case Fail{M.MapleBusy{}}:
      "busy"
    case Fail{M.MapleBadSize{}}:
      "bad size"
    case Fail{M.MapleBadRange{a, b}}:
      "bad range " ++ U32.show(a) ++ " " ++ U32.show(b)
    case Fail{M.MapleInverted{a, b}}:
      "inverted"

def show_store(r: Result<&2, &2, M.MapleError<U32>, N.MapleTree<U32, U32>>) -> String:
  match r:
    case Fail{M.MapleInverted{a, b}}:
      "inverted " ++ U32.show(a) ++ " " ++ U32.show(b)
    case Fail{e}:
      "other error"
    case Done{t}:
      "ok"

def stats(+t: N.MapleTree<U32, U32>) -> String:
  "size " ++ Nat.show(T.Maple32.size(U32, t)) ++ " height " ++ Nat.show(T.Maple32.height(U32, t)) ++ " valid " ++ Bool.show(T.Maple32.valid(U32, t)) ++ " balanced " ++ Bool.show(T.Maple32.balanced(U32, t)) ++ " leveled " ++ Bool.show(T.Maple32.leveled(U32, t))

# [10, 20] -> 1, [30, 40] -> 2, then [15, 35] -> 3 over both
def demo() -> N.MapleTree<U32, U32>:
  T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 10, 20, 1), 30, 40, 2), 15, 35, 3)

# [100, 200] -> 4, then 150 -> 5 inside it
def split() -> N.MapleTree<U32, U32>:
  T.Maple32.store(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 100, 200, 4), 150, 5)

# [10k, 10k + 5] -> k, for k below n
def build(n: Nat, t: N.MapleTree<U32, U32>) -> N.MapleTree<U32, U32>:
  match n:
    case 0n:
      t
    case 1n+ +p:
      +k = U32.from_nat(p)
      build(p, T.Maple32.set_range(U32, t, (k * 10 : U32), (k * 10 + 5 : U32), k))

# [20k, 20k + 9] cleared, for k below n
def clear_some(n: Nat, t: N.MapleTree<U32, U32>) -> N.MapleTree<U32, U32>:
  match n:
    case 0n:
      t
    case 1n+ +p:
      +k = U32.from_nat(p)
      clear_some(p, T.Maple32.clear_range(U32, t, (k * 20 : U32), (k * 20 + 9 : U32)))

# iteration: next from each answer
def walk(fuel: Nat, +t: N.MapleTree<U32, U32>, cur: Maybe<&2, M.MapleEntry<U32, U32>>) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+p:
      match cur:
        case None{}:
          ""
        case Some{+x}:
          " " ++ show_e(x) ++ walk(p, t, T.Maple32.next(U32, t, M.MapleEntry.last(U32, U32, x)))

# a tree keyed by W64: the same code, with W64's order and arithmetic
def w_inc(a: W.W64) -> W.W64:
  W.W64.add(a, W.W64.one())

def w_dec(a: W.W64) -> W.W64:
  W.W64.sub(a, W.W64.one())

def mapping() -> N.MapleTree<W.W64, U32>:
  T.Maple.set_range(~W.W64, ~W.W64.cmp, ~w_inc, ~w_dec, U32, T.Maple.set_range(~W.W64, ~W.W64.cmp, ~w_inc, ~w_dec, U32, T.Maple.empty(W.W64, U32, N.MapleOptions.default()), W.W64.from_parts(1, 0), W.W64.from_parts(1, 4095), 7), W.W64.from_parts(1, 1024), W.W64.from_parts(1, 2047), 8)

def show_w(m: Maybe<&2, M.MapleEntry<W.W64, U32>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{M.MapleEntry{f, l, v}}:
      W.W64.show_hex(f) ++ "-" ++ W.W64.show_hex(l) ++ ":" ++ U32.show(v)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("demo:" ++ show_list(T.Maple32.entries(U32, demo())))
    IO.print("split:" ++ show_list(T.Maple32.entries(U32, split())))
    IO.print("load 14 15 35 36 41: " ++ show_value(T.Maple32.load(U32, demo(), 14)) ++ " " ++ show_value(T.Maple32.load(U32, demo(), 15)) ++ " " ++ show_value(T.Maple32.load(U32, demo(), 35)) ++ " " ++ show_value(T.Maple32.load(U32, demo(), 36)) ++ " " ++ show_value(T.Maple32.load(U32, demo(), 41)))
    IO.print("clear 12 16:" ++ show_list(T.Maple32.entries(U32, T.Maple32.clear_range(U32, demo(), 12, 16))))
    IO.print("erase 150:" ++ show_list(T.Maple32.entries(U32, T.Maple32.erase(U32, split(), 150))))
    IO.print("erase 99:" ++ show_list(T.Maple32.entries(U32, T.Maple32.erase(U32, split(), 99))))
    IO.print("lookup 160:" ++ show_maybe(T.Maple32.lookup(U32, split(), 160)))
    IO.print("find 21 41:" ++ show_maybe(T.Maple32.find(U32, demo(), 21)) ++ show_maybe(T.Maple32.find(U32, demo(), 41)))
    IO.print("next 15 35:" ++ show_maybe(T.Maple32.next(U32, demo(), 15)) ++ show_maybe(T.Maple32.next(U32, demo(), 36)))
    IO.print("prev 15 50:" ++ show_maybe(T.Maple32.prev(U32, demo(), 15)) ++ show_maybe(T.Maple32.prev(U32, demo(), 50)))
    IO.print("walk:" ++ walk(10n, split(), T.Maple32.find(U32, split(), 0)))
    IO.print("store 9 3: " ++ show_store(T.Maple32.store_range(U32, demo(), 9, 3, 0)))
    IO.print("gap 0 100 10: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 0, 100, 10)))
    IO.print("gap 5 100 11: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 5, 100, 11)))
    IO.print("gap 0 45 5: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 0, 45, 5)))
    IO.print("gap 0 45 6: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 0, 45, 6)))
    IO.print("gap 10 40 1: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 10, 40, 1)))
    IO.print("gap size 0: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 0, 100, 0)))
    IO.print("gap 9 3: " ++ show_gap(G.Maple32.empty_area(U32, demo(), 9, 3, 1)))
    IO.print("gap top: " ++ show_gap(G.Maple32.empty_area(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 0, 4294967290, 1), 0, 4294967295, 5)))
    IO.print("gap top 6: " ++ show_gap(G.Maple32.empty_area(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 0, 4294967290, 1), 0, 4294967295, 6)))
    IO.print("whole range:" ++ show_list(T.Maple32.entries(U32, T.Maple32.store(U32, T.Maple32.set_range(U32, T.Maple32.empty(U32), 0, 4294967295, 1), 4294967295, 2))))
    IO.print("demo: " ++ stats(demo()))
    IO.print("1000 ranges: " ++ stats(build(1000n, T.Maple32.empty(U32))))
    IO.print("load 5005 5006: " ++ show_value(T.Maple32.load(U32, build(1000n, T.Maple32.empty(U32)), 5005)) ++ " " ++ show_value(T.Maple32.load(U32, build(1000n, T.Maple32.empty(U32)), 5006)))
    IO.print("cleared: " ++ stats(clear_some(500n, build(1000n, T.Maple32.empty(U32)))))
    IO.print("order 3: " ++ stats(build(1000n, T.Maple32.empty_with(U32, N.MapleOptions{3n}))))
    IO.print("W64 load 1:1500: " ++ show_value(T.Maple.load(~W.W64, ~W.W64.cmp, U32, mapping(), W.W64.from_parts(1, 1500))))
    IO.print("W64 find 1:2048: " ++ show_w(T.Maple.find(~W.W64, ~W.W64.cmp, U32, mapping(), W.W64.from_parts(1, 2048))))

#|demo: 10-14:1 15-35:3 36-40:2
#|split: 100-149:4 150-150:5 151-200:4
#|load 14 15 35 36 41: 1 3 3 2 none
#|clear 12 16: 10-11:1 17-35:3 36-40:2
#|erase 150: 100-149:4 151-200:4
#|erase 99: 100-149:4 150-150:5 151-200:4
#|lookup 160: 151-200:4
#|find 21 41: 15-35:3 none
#|next 15 35: 36-40:2 none
#|prev 15 50: 10-14:1 36-40:2
#|walk: 100-149:4 150-150:5 151-200:4
#|store 9 3: inverted 9 3
#|gap 0 100 10: 0
#|gap 5 100 11: 41
#|gap 0 45 5: 0
#|gap 0 45 6: 0
#|gap 10 40 1: busy
#|gap size 0: bad size
#|gap 9 3: bad range 9 3
#|gap top: 4294967291
#|gap top 6: busy
#|whole range: 0-4294967294:1 4294967295-4294967295:2
#|demo: size 3 height 0 valid True balanced True leveled True
#|1000 ranges: size 1000 height 2 valid True balanced True leveled True
#|load 5005 5006: 500 none
#|cleared: size 500 height 2 valid True balanced True leveled True
#|order 3: size 1000 height 6 valid True balanced True leveled True
#|W64 load 1:1500: 8
#|W64 find 1:2048: 0000000100000800-0000000100000fff:7
