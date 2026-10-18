# The key-agreement interface.
#
# A key agreement (template arguments, in this order):
#   ~SK: Data                                      a secret key
#   ~PK: Data                                      a public key
#   ~secret: B.Octets -> Result<&2, &2, CrError, SK>
#                                                  a secret key from its
#                                                  bytes, refusing a
#                                                  malformed one
#   ~public: SK -> PK                              its public key
#   ~pk_of: B.Octets -> Result<&2, &2, CrError, PK>
#                                                  a peer's public key from
#                                                  its bytes (CrBadPublicKey)
#   ~pk_to: PK -> B.Octets                         a public key's bytes
#   ~shared: SK -> PK -> Result<&2, &2, CrError, B.Octets>
#                                                  the shared secret, or the
#                                                  refusal of a peer key the
#                                                  scheme rejects (CrBadKey)
# Laws (README.md, "Laws"):
#   agree      shared(a, public(b)) == shared(b, public(a)), for every two
#              secret keys: both sides compute the same secret
#   pk_format  pk_of(pk_to(p)) == Done{p}
#
# No algorithm of bend-osdev is a key agreement yet; one plugs in by
# supplying these defs (README.md, "Extension points"). A shared secret is
# keying material for a KDF (kdf.bend), not a key.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

def cr.kex.with(~SK: Data, ~PK: Data, ~shared: SK -> PK -> Result<&2, &2, Cr.CrError, B.Octets>, sk: Result<&2, &2, Cr.CrError, SK>, pk: Result<&2, &2, Cr.CrError, PK>) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match sk pk:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{a} Done{p}:
      shared(a, p)

# The shared secret of one's secret key's bytes and the peer's public key's
# bytes
def CrKex.agree(~SK: Data, ~PK: Data, ~secret: B.Octets -> Result<&2, &2, Cr.CrError, SK>, ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>, ~shared: SK -> PK -> Result<&2, &2, Cr.CrError, B.Octets>, sk: B.Octets, peer: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cr.kex.with(~SK, ~PK, ~shared, secret(sk), pk_of(peer))
