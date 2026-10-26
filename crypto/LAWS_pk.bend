# Laws of sign.bend's and kex.bend's generic helpers, for every signature
# scheme and key agreement: LAWS.bend's sign_verify_bytes_if and
# kex_agree_if (the same statements), and what CrSign.verify_bytes and
# CrKex.agree compute once the keys have parsed, in a pair of their own so
# that a proof elsewhere can use them without importing PROOF.bend; PROOF.bend
# proves its two from these.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./sign.bend as Sg
import ./kex.bend as Kx

# a signature checked from the bytes of a public key that parses (hp) is
# the scheme's verdict under that key
law sign_verify_bytes_done:
  for ~PK: Data
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~verify: PK -> B.Octets -> B.Octets -> Bool
  for +pk: B.Octets
  for +m: B.Octets
  for +sig: B.Octets
  for +p: PK
  for hp: {pk_of(pk) == Done{p} : Result<&2, &2, Cr.CrError, PK>}
  {Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, pk, m, sig) == verify(p, m, sig) : Bool}

# a signature checked from the public key's bytes is accepted, for every
# scheme, secret key and message, when the scheme's pk_format and accepts
# laws hold there (hf, ha)
law sign_verify_bytes_if:
  for ~SK: Data
  for ~PK: Data
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~sign: SK -> B.Octets -> B.Octets
  for ~verify: PK -> B.Octets -> B.Octets -> Bool
  for +sk: SK
  for +m: B.Octets
  for hf: {pk_of(pk_to(public(sk))) == Done{public(sk)} : Result<&2, &2, Cr.CrError, PK>}
  for ha: {verify(public(sk), m, sign(sk, m)) == True{} : Bool}
  {Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, pk_to(public(sk)), m, sign(sk, m)) == True{} : Bool}

# the agreed secret, from a secret key's bytes and a peer's public-key bytes
# that both parse (hx, hp), is the scheme's shared secret of the two keys
law kex_agree_done:
  for ~SK: Data
  for ~PK: Data
  for ~secret: B.Octets -> Result<&2, &2, Cr.CrError, SK>
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~shared: SK -> PK -> Result<&2, &2, Cr.CrError, B.Octets>
  for +sk: B.Octets
  for +peer: B.Octets
  for +x: SK
  for +p: PK
  for hx: {secret(sk) == Done{x} : Result<&2, &2, Cr.CrError, SK>}
  for hp: {pk_of(peer) == Done{p} : Result<&2, &2, Cr.CrError, PK>}
  {Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, sk, peer) == shared(x, p) : Result<&2, &2, Cr.CrError, B.Octets>}

# two parties agree from each other's public-key bytes, for every scheme and
# pair of secret keys, when the keys parse (hx, hy), the public keys survive
# their bytes (hfx, hfy) and the scheme's agree law holds for them (h)
law kex_agree_if:
  for ~SK: Data
  for ~PK: Data
  for ~secret: B.Octets -> Result<&2, &2, Cr.CrError, SK>
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~shared: SK -> PK -> Result<&2, &2, Cr.CrError, B.Octets>
  for +a: B.Octets
  for +b: B.Octets
  for +x: SK
  for +y: SK
  for hx: {secret(a) == Done{x} : Result<&2, &2, Cr.CrError, SK>}
  for hy: {secret(b) == Done{y} : Result<&2, &2, Cr.CrError, SK>}
  for hfx: {pk_of(pk_to(public(x))) == Done{public(x)} : Result<&2, &2, Cr.CrError, PK>}
  for hfy: {pk_of(pk_to(public(y))) == Done{public(y)} : Result<&2, &2, Cr.CrError, PK>}
  for h: {shared(x, public(y)) == shared(y, public(x)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, a, pk_to(public(y))) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}
