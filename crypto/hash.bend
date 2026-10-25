# The hash interface.
#
# A hash (template arguments, in this order):
#   ~H: Data                          the state
#   ~bsize: Nat                       the block size in bytes (HMAC's B)
#   ~dsize: Nat                       the digest size in bytes (HMAC's L)
#   ~init: H                          the state before any byte
#   ~update: H -> B.Octets -> H       the state after more bytes
#   ~final: H -> B.Octets             the digest of the bytes so far
#   ~digest: B.Octets -> B.Octets     the digest in one call
# Laws (README.md, "Laws"):
#   streaming  update(s, a ++ b) == update(update(s, a), b), for every state
#              s, so pieces may be fed in any split
#   split      final(update(update(init, a), b)) == digest(a ++ b): the
#              streaming result equals the one-shot result for every split
#   length     final(s) has dsize bytes (tested)
#
# A hash whose one-shot form is not separate code takes CrHash.digest_of (the
# streaming form in one call) as its ~digest. The instances: inst_crc.bend
# (CRC-32 and CRC-64 of any parameter set, non-cryptographic), inst_sha2.bend
# (SHA-256, SHA-512), and MD4, MD5, SHA-1, RIPEMD-160, SM3 and Streebog
# from their packages (md4, md5, sha1, ripemd160, sm3, streebog: their defs
# directly; each file's header gives its tuple).
# Generic algorithms over any hash: hmac.bend, hkdf.bend.
import Base
import ../bytes/bytes.bend as B

def cr.hash.feed(~H: Data, ~update: H -> B.Octets -> H, ps: List<&2, B.Octets>, s: H) -> H:
  match ps:
    case Nil{}:
      s
    case Con{p, t}:
      cr.hash.feed(~H, ~update, t, update(s, p))

# the state after each piece in turn
def CrHash.update_all(~H: Data, ~update: H -> B.Octets -> H, s: H, ps: List<&2, B.Octets>) -> H:
  cr.hash.feed(~H, ~update, ps, s)

# the digest of the pieces joined, through the streaming interface
def CrHash.of_pieces(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ps: List<&2, B.Octets>) -> B.Octets:
  final(CrHash.update_all(~H, ~update, init, ps))

# the streaming interface in one call: a ~digest for a hash with no one-shot
# code of its own
def CrHash.digest_of(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, m: B.Octets) -> B.Octets:
  final(update(init, m))
