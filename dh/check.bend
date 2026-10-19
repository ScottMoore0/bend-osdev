import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ./dh.bend as D
import ./groups.bend as G

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def err(e: D.DhError) -> String:
  match e:
    case D.DhBadPrivateKey{}:
      "bad-private"
    case D.DhBadPublicKey{}:
      "bad-public"
    case D.DhBadSharedSecret{}:
      "bad-shared"
    case D.DhBadLength{}:
      "bad-length"

def ro(r: Result<&2, &2, D.DhError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{+o}:
      B.Octets.hex(B.Octets.take(16n, o)) ++ ".." ++ B.Octets.hex(B.Octets.drop(240n, o))

def rn(r: Result<&2, &2, D.DhError, N.BnNat>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{x}:
      N.BnNat.hex(x)

def p16(+g: D.DhGroup) -> String:
  Nat.show(N.BnNat.bit_len(D.DhGroup.p(g))) ++ " bits"

def xa() -> N.BnNat:
  h("1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f")

def xb() -> N.BnNat:
  h("2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e")

def main() -> IO(Unit):
  +g = G.DhGroups.ffdhe2048()
  +ya = D.Dh.public(g, xa())
  +yb = D.Dh.public(g, xb())
  do IO<Unit>:
    IO.print("ffdhe2048 " ++ p16(G.DhGroups.ffdhe2048()) ++ ", ffdhe8192 " ++ p16(G.DhGroups.ffdhe8192()) ++ ", modp1536 " ++ p16(G.DhGroups.modp1536()) ++ ", modp8192 " ++ p16(G.DhGroups.modp8192()))
    IO.print("public " ++ B.Octets.hex(B.Octets.take(16n, D.Dh.public_to(g, ya))))
    IO.print("agree a " ++ ro(D.Dh.agree_safe(g, xa(), yb)))
    IO.print("agree b " ++ ro(D.Dh.agree(g, xb(), ya)))
    IO.print("valid " ++ bs(D.Dh.check_full(g, ya)) ++ " " ++ bs(D.Dh.check_safe(g, ya)))
    IO.print("refused " ++ ro(D.Dh.agree_safe(g, xa(), N.BnNat.one())) ++ " " ++ ro(D.Dh.agree_safe(g, xa(), N.BnNat.sub(D.DhGroup.p(g), N.BnNat.one()))))
    IO.print("form " ++ rn(D.Dh.public_of(g, B.Octets.of_list([1, 2, 3]))) ++ " " ++ bs(N.BnNat.is_eq(Result.default(&2, &2, D.DhError, N.BnNat, D.Dh.public_of(g, D.Dh.public_to(g, ya)), N.BnNat.zero()), ya)))
    IO.print("private " ++ rn(D.Dh.private_of(g, B.Octets.of_list([0]))))
#|ffdhe2048 2048 bits, ffdhe8192 8192 bits, modp1536 1536 bits, modp8192 8192 bits
#|public d7f02beafd291cfe49772666e2dfa579
#|agree a 41a93e6ebeaa98f56397db4e7aae52f9..8217a023369a1e98799f9aa2b9da1bb4
#|agree b 41a93e6ebeaa98f56397db4e7aae52f9..8217a023369a1e98799f9aa2b9da1bb4
#|valid yes yes
#|refused bad-public bad-public
#|form bad-length yes
#|private bad-private
