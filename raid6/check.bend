import Base
import ../bytes/bytes.bend as B
import ../gf/gf.bend as G
import ./raid6.bend as R
import ./scale.bend as S
import ./recover.bend as V

# n pseudo-random bytes (a linear congruential generator), built tail-recursively
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat, seed: U32) -> B.Octets:
  B.Octets.of_list(bulk.go(n, seed, Nil{}))

# k data blocks of n bytes each
def blocks(k: Nat, +n: Nat, +seed: U32) -> List<&2, B.Octets>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      Con{bulk(n, seed), blocks(j, n, U32.add(seed, 101))}

def yes(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def blocks_eq(xs: List<&2, B.Octets>, ys: List<&2, B.Octets>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      Bool.and(B.Octets.is_eq(x, y), blocks_eq(s, t))
    case _ _:
      False{}

def stripe_eq(a: R.Raid6Stripe, b: R.Raid6Stripe) -> Bool:
  match a b:
    case R.Raid6Stripe{da, pa, qa} R.Raid6Stripe{db, pb, qb}:
      Bool.and(blocks_eq(da, db), Bool.and(B.Octets.is_eq(pa, pb), B.Octets.is_eq(qa, qb)))

# the lost blocks overwritten with junk, then recovered: 1 if the stripe
# comes back, else 0
def damage(st: R.Raid6Stripe, lost: V.Raid6Lost) -> R.Raid6Stripe:
  match st:
    case R.Raid6Stripe{ds, p, q}:
      match lost:
        case V.Raid6LostNone{}:
          R.Raid6Stripe{ds, p, q}
        case V.Raid6LostData{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, bulk(9n, 5)), p, q}
        case V.Raid6LostP{}:
          R.Raid6Stripe{ds, bulk(3n, 6), q}
        case V.Raid6LostQ{}:
          R.Raid6Stripe{ds, p, bulk(70n, 7)}
        case V.Raid6LostDataData{x, y}:
          R.Raid6Stripe{R.Raid6.set_block(R.Raid6.set_block(ds, x, bulk(64n, 8)), y, bulk(1n, 9)), p, q}
        case V.Raid6LostDataP{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, bulk(64n, 10)), B.Octets.empty(), q}
        case V.Raid6LostDataQ{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, B.Octets.empty()), p, bulk(64n, 11)}
        case V.Raid6LostPQ{}:
          R.Raid6Stripe{ds, bulk(64n, 12), B.Octets.empty()}

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def ok(r: Result<&2, &2, V.Raid6Error, R.Raid6Stripe>, +st: R.Raid6Stripe) -> Nat:
  match r:
    case Done{s}:
      one(stripe_eq(s, st))
    case Fail{e}:
      0n

def try(+st: R.Raid6Stripe, +lost: V.Raid6Lost) -> Nat:
  ok(V.Raid6.recover(R.Raid6.spec(), damage(st, lost), lost), st)

# every pair x < y below n, with y from j: the number recovered
def pairs.y(j: Nat, +st: R.Raid6Stripe, +x: Nat, +y: Nat, acc: Nat) -> Nat:
  match j:
    case 0n:
      acc
    case 1n+k:
      pairs.y(k, st, x, 1n+y, Nat.add(acc, Nat.add(try(st, V.Raid6LostDataData{x, y}), try(st, V.Raid6LostDataData{y, x}))))

def pairs(i: Nat, +st: R.Raid6Stripe, +n: Nat, +x: Nat, acc: Nat) -> Nat:
  match i:
    case 0n:
      acc
    case 1n+k:
      pairs(k, st, n, 1n+x, pairs.y(Nat.sub(n, 1n+x), st, x, 1n+x, acc))

# every single data loss, with and without P or Q
def singles(i: Nat, +st: R.Raid6Stripe, +x: Nat, acc: Nat) -> Nat:
  match i:
    case 0n:
      acc
    case 1n+k:
      singles(k, st, 1n+x, Nat.add(acc, Nat.add(try(st, V.Raid6LostData{x}), Nat.add(try(st, V.Raid6LostDataP{x}), try(st, V.Raid6LostDataQ{x})))))

def err(r: Result<&2, &2, V.Raid6Error, R.Raid6Stripe>) -> String:
  match r:
    case Done{s}:
      "done"
    case Fail{e}:
      match e:
        case V.Raid6TooManyDisks{n}:
          "too many disks"
        case V.Raid6BadIndex{i}:
          "bad index " ++ Nat.show(i)
        case V.Raid6SameIndex{i}:
          "same index " ++ Nat.show(i)

def small_stripe() -> List<&2, B.Octets>:
  [B.Octets.of_list([1, 2, 3, 4]), B.Octets.of_list([16, 32, 48, 64]), B.Octets.of_list([255, 254, 253, 252])]

def main() -> IO(Unit):
  +sp = R.Raid6.spec()
  +f = G.Gf8.raid6()
  +small = small_stripe()
  +st = R.Raid6.encode(sp, blocks(7n, 64n, 3))
  +big = R.Raid6.encode(sp, blocks(4n, 30000n, 17))
  do IO<Unit>:
    IO.print(U32.show(R.Raid6.gpow(sp, 8n)))
    IO.print(U32.show(R.Raid6.gpow(sp, 4n)))
    IO.print(Nat.show(G.Gf8.log(f, 16)))
    IO.print(yes(U32.is_eq(G.Gf8.mul(f, 87, 141), G.Gf8.add(G.Gf8.add(G.Gf8.mul(f, 87, R.Raid6.gpow(sp, 7n)), G.Gf8.mul(f, 87, R.Raid6.gpow(sp, 3n))), G.Gf8.add(G.Gf8.mul(f, 87, R.Raid6.gpow(sp, 2n)), 87)))))
    IO.print(B.Octets.hex(R.Raid6.p(small)))
    IO.print(B.Octets.hex(R.Raid6.q(sp, small)))
    IO.print(B.Octets.hex(S.Raid6.scale(f, 2, B.Octets.of_list([1, 128, 255]))))
    IO.print(Nat.show(try(st, V.Raid6LostNone{})))
    IO.print(Nat.show(Nat.add(try(st, V.Raid6LostP{}), Nat.add(try(st, V.Raid6LostQ{}), try(st, V.Raid6LostPQ{})))))
    IO.print(Nat.show(singles(7n, st, 0n, 0n)))
    IO.print(Nat.show(pairs(7n, st, 7n, 0n, 0n)))
    IO.print(Nat.show(Nat.add(try(big, V.Raid6LostDataData{1n, 3n}), try(big, V.Raid6LostDataP{2n}))))
    IO.print(err(V.Raid6.recover(sp, st, V.Raid6LostData{7n})))
    IO.print(err(V.Raid6.recover(sp, st, V.Raid6LostDataData{2n, 2n})))
    IO.print(err(V.Raid6.recover(sp, R.Raid6.encode(sp, blocks(256n, 1n, 1)), V.Raid6LostP{})))

#|29
#|16
#|4
#|yes
#|eedcceb8
#|fa9db053
#|021de3
#|1
#|3
#|21
#|42
#|2
#|bad index 7
#|same index 2
#|too many disks
