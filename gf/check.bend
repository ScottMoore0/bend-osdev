import Base
import ../bytes/bytes.bend as B
import ./gf.bend as G
import ./tables.bend as T
import ./gf128.bend as H
import ./gfm.bend as M

def show(x: U32) -> String:
  U32.show(x)

# The table path against the reference over every pair of bytes (and every
# inverse): the number of disagreements. r is the table and its answer for
# (a, b).
def tab.count(ok: Bool, bad: Nat) -> Nat:
  match ok:
    case True{}:
      bad
    case False{}:
      1n+bad

def tab.row(n: Nat, +f: G.Gf8Field, r: T.Gf8Tab & U32, +a: U32, +b: U32, bad: Nat) -> T.Gf8Tab & Nat:
  match n:
    case 0n:
      (t, v) = r
      (t, bad)
    case 1n+k:
      (t, +v) = r
      +b1 = U32.add(b, 1)
      tab.row(k, f, T.Gf8Tab.mul(t, a, b1), a, b1, tab.count(U32.is_eq(v, G.Gf8.mul(f, a, b)), bad))

def tab.all(n: Nat, +f: G.Gf8Field, r: T.Gf8Tab & Nat, +a: U32) -> T.Gf8Tab & Nat:
  match n:
    case 0n:
      r
    case 1n+k:
      (t, bad) = r
      tab.all(k, f, tab.row(256n, f, T.Gf8Tab.mul(t, a, 0), a, 0, bad), U32.add(a, 1))

def tab.inv(n: Nat, +f: G.Gf8Field, r: T.Gf8Tab & U32, +a: U32, bad: Nat) -> Nat:
  match n:
    case 0n:
      bad
    case 1n+k:
      (t, +v) = r
      +a1 = U32.add(a, 1)
      tab.inv(k, f, T.Gf8Tab.inv(t, a1), a1, tab.count(U32.is_eq(v, G.Gf8.inv(f, a)), bad))

def tab.snd(r: T.Gf8Tab & Nat) -> Nat:
  (t, n) = r
  n

def tab.check(+f: G.Gf8Field) -> Nat:
  Nat.add(tab.snd(tab.all(256n, f, (T.Gf8Tab.new(f), 0n), 0)), tab.inv(256n, f, T.Gf8Tab.inv(T.Gf8Tab.new(f), 0), 0, 0n))

def gcm_h() -> H.Gf128:
  H.Gf128.of_words(1726565332, 4018809915, 2286746201, 3392416558)

def gcm_c() -> H.Gf128:
  H.Gf128.of_words(59300558, 1622582162, 4079534777, 1907555960)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(G.Gf8.mul(G.Gf8.aes(), 87, 131)))
    IO.print(show(G.Gf8.mul(G.Gf8.aes(), 87, 19)))
    IO.print(show(G.Gf8.xtime(G.Gf8.aes(), 87)))
    IO.print(show(G.Gf8.inv(G.Gf8.aes(), 83)))
    IO.print(Nat.show(G.Gf8.log(G.Gf8.aes(), 83)))
    IO.print(show(G.Gf8.exp(G.Gf8.aes(), G.Gf8.log(G.Gf8.aes(), 83))))
    IO.print(show(G.Gf8.exp(G.Gf8.rs(), 8n)))
    IO.print(show(G.Gf8.div(G.Gf8.rs(), 1, 2)))
    IO.print(Nat.show(tab.check(G.Gf8.aes())))
    IO.print(Nat.show(tab.check(G.Gf8.rs())))
    IO.print(H.Gf128.hex(H.Gf128.mul_gcm(gcm_c(), gcm_h())))
    IO.print(H.Gf128.hex(H.Gf128.ghash(gcm_h(), [gcm_c(), H.Gf128.of_words(0, 0, 0, 128)])))
    IO.print(H.Gf128.hex(H.Gf128.double_be(H.Gf128.of_words(2113366796, 448305587, 1044574279, 3105576047))))
    IO.print(H.Gf128.hex(H.Gf128.double_le(H.Gf128.of_words(0, 0, 0, 255))))
    IO.print(show(M.Gfm.mul(M.Gfm.bch13(), 1234, 5678)))
    IO.print(show(M.Gfm.inv(M.Gfm.bch13(), 1234)))
    IO.print(show(M.Gfm.log(M.Gfm.bch13(), 1234)))
    IO.print(show(M.Gfm.exp(M.Gfm.bch14(), 16383)))

#|193
#|254
#|174
#|202
#|48
#|83
#|29
#|142
#|0
#|0
#|5e2ec746917062882c85b0685353deb7
#|f38cbb1ad69223dcc3457ae5b6b0f885
#|fbeed618357133667c85e08f7236a8de
#|870000000000000000000000000000fe
#|4994
#|2297
#|2924
#|1
