# The signature interface.
#
# A signature scheme (template arguments, in this order):
#   ~SK: Data                                      a secret key
#   ~PK: Data                                      a public key
#   ~secret: B.Octets -> Result<&2, &2, CrError, SK>
#                                                  a secret key from its
#                                                  bytes (or seed), refusing
#                                                  a malformed one
#   ~public: SK -> PK                              its public key
#   ~pk_of: B.Octets -> Result<&2, &2, CrError, PK>
#                                                  a public key from its
#                                                  bytes (CrBadPublicKey)
#   ~pk_to: PK -> B.Octets                         a public key's bytes
#   ~sign: SK -> B.Octets -> B.Octets              the signature of a message
#   ~verify: PK -> B.Octets -> B.Octets -> Bool    whether a signature is
#                                                  valid for a message
# Laws (README.md, "Laws"):
#   accepts    verify(public(sk), m, sign(sk, m)) == True, for every secret
#              key and message
#   pk_format  pk_of(pk_to(p)) == Done{p}
#   forgery    a changed message or signature is refused (tested)
#
# No algorithm of bend-osdev is a signature scheme yet; one plugs in by
# supplying these defs (README.md, "Extension points").
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

# A secret key and its public key (open type)
type CrKeypair<-SK: Data, -PK: Data> is Data:
  CrKeypair{secret: SK, public: PK}

# The key pair of a secret key's bytes
def CrSign.keypair(~SK: Data, ~PK: Data, ~secret: B.Octets -> Result<&2, &2, Cr.CrError, SK>, ~public: SK -> PK, o: B.Octets) -> Result<&2, &2, Cr.CrError, CrKeypair<SK, PK>>:
  Result.map(&2, &2, Cr.CrError, SK, CrKeypair<SK, PK>, +sk => CrKeypair{sk, public(sk)}, secret(o))

def cr.sign.check(~PK: Data, ~verify: PK -> B.Octets -> B.Octets -> Bool, r: Result<&2, &2, Cr.CrError, PK>, m: B.Octets, sig: B.Octets) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{pk}:
      verify(pk, m, sig)

# Whether sig is valid for m under the public key with these bytes (False for
# a malformed key)
def CrSign.verify_bytes(~PK: Data, ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>, ~verify: PK -> B.Octets -> B.Octets -> Bool, pk: B.Octets, m: B.Octets, sig: B.Octets) -> Bool:
  cr.sign.check(~PK, ~verify, pk_of(pk), m, sig)
