# The keys' byte forms in this package's raw format: each integer as a
# four-byte big-endian length and then its shortest big-endian bytes,
#   public:  n, e
#   private: n, e, d, p, q   (dP, dQ and qInv are recomputed, and the key
#                             checked, when it is read)
# This is the form bend-osdev-pubkey's signature instances carry; reading
# PKCS #1's DER (RFC 8017, Appendix A.1: RSAPublicKey, RSAPrivateKey) or an
# X.509 SubjectPublicKeyInfo is an extension point, for an ASN.1 package,
# whose results go to Rsa.public_of and Rsa.private_of.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ./rsa.bend as R

def rsa.field(+x: N.BnNat) -> B.Octets:
  +o = N.BnNat.to_octets_min(x)
  B.Octets.append(B.Octets.be32(U32.from_nat(B.Octets.len(o))), o)

# The form of a public key
def RsaKeys.public_to(pk: R.RsaPublic) -> B.Octets:
  match pk:
    case R.RsaPublic{n, e}:
      B.Octets.append(rsa.field(n), rsa.field(e))

# The form of a private key
def RsaKeys.private_to(sk: R.RsaPrivate) -> B.Octets:
  match sk:
    case R.RsaPrivate{n, e, d, p, q, dp, dq, qinv}:
      B.Octets.concat([rsa.field(n), rsa.field(e), rsa.field(d), rsa.field(p), rsa.field(q)])

# A parsed integer and the bytes after it (open)
type RsaField is Data:
  RsaField{x: N.BnNat, rest: B.Octets}

def rsa.take.go(fits: Bool, +n: Nat, +body: B.Octets) -> Result<&2, &2, R.RsaError, RsaField>:
  match fits:
    case True{}:
      Done{RsaField{N.BnNat.of_octets(B.Octets.take(n, body)), B.Octets.drop(n, body)}}
    case False{}:
      Fail{R.RsaBadFormat{}}

def rsa.take(len: Maybe<&2, U32>, +o: B.Octets) -> Result<&2, &2, R.RsaError, RsaField>:
  match len:
    case None{}:
      Fail{R.RsaBadFormat{}}
    case Some{l}:
      +n = U32.to_nat(l)
      +body = B.Octets.drop(4n, o)
      rsa.take.go(Nat.is_le(n, B.Octets.len(body)), n, body)

# the first integer of a form, and the rest
def rsa.read(+o: B.Octets) -> Result<&2, &2, R.RsaError, RsaField>:
  rsa.take(B.Octets.be32_at(o, 0n), o)

def rsa.read.end(+o: B.Octets) -> Result<&2, &2, R.RsaError, Unit>:
  R.RsaError.check(Nat.is_eq(B.Octets.len(o), 0n), R.RsaBadFormat{})

def rsa.read.pub2(+n: N.BnNat, b: Result<&2, &2, R.RsaError, RsaField>) -> Result<&2, &2, R.RsaError, R.RsaPublic>:
  match b:
    case Fail{e}:
      Fail{e}
    case Done{RsaField{e, r}}:
      Result.bind(&2, &2, R.RsaError, Unit, R.RsaPublic, rsa.read.end(r), u => R.Rsa.public_of(n, e))

def rsa.read.pub(a: RsaField) -> Result<&2, &2, R.RsaError, R.RsaPublic>:
  match a:
    case RsaField{n, r}:
      rsa.read.pub2(n, rsa.read(r))

# A public key from its form: RsaBadFormat for malformed bytes, RsaBadKey
# for a key Rsa.public_of refuses
def RsaKeys.public_of(+o: B.Octets) -> Result<&2, &2, R.RsaError, R.RsaPublic>:
  Result.bind(&2, &2, R.RsaError, RsaField, R.RsaPublic, rsa.read(o), a => rsa.read.pub(a))

def RsaField.x(a: RsaField) -> N.BnNat:
  match a:
    case RsaField{x, r}:
      x

def RsaField.rest(a: RsaField) -> B.Octets:
  match a:
    case RsaField{x, r}:
      r

# exactly f integers, and nothing after them (RsaBadFormat otherwise)
def rsa.read.n(f: Nat, +o: B.Octets) -> Result<&2, &2, R.RsaError, List<&2, N.BnNat>>:
  match f:
    case 0n:
      Result.map(&2, &2, R.RsaError, Unit, List<&2, N.BnNat>, u => Nil{}, rsa.read.end(o))
    case 1n+p:
      Result.bind(&2, &2, R.RsaError, RsaField, List<&2, N.BnNat>, rsa.read(o), +a => Result.map(&2, &2, R.RsaError, List<&2, N.BnNat>, List<&2, N.BnNat>, t => Con{RsaField.x(a), t}, rsa.read.n(p, RsaField.rest(a))))

def rsa.read.priv(xs: List<&2, N.BnNat>) -> Result<&2, &2, R.RsaError, R.RsaPrivate>:
  match xs:
    case Con{n, Con{e, Con{d, Con{p, Con{q, Nil{}}}}}}:
      R.Rsa.private_of(n, e, d, p, q)
    case _:
      Fail{R.RsaBadFormat{}}

# A private key from its form: RsaBadFormat for malformed bytes, RsaBadKey
# for a key Rsa.private_of refuses
def RsaKeys.private_of(+o: B.Octets) -> Result<&2, &2, R.RsaError, R.RsaPrivate>:
  Result.bind(&2, &2, R.RsaError, List<&2, N.BnNat>, R.RsaPrivate, rsa.read.n(5n, o), xs => rsa.read.priv(xs))
