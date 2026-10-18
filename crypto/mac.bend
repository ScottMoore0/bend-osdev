# The MAC interface (message authentication codes).
#
# A MAC (template arguments, in this order):
#   ~K: Data                                       its key, prepared
#   ~key: B.Octets -> Result<&2, &2, CrError, K>   the key of a raw key,
#                                                  refusing a length the MAC
#                                                  does not take
#   ~compute: K -> B.Octets -> B.Octets            the tag of a message
#   ~verify: K -> B.Octets -> B.Octets -> Bool     whether a tag is the
#                                                  message's
# Laws (README.md, "Laws"):
#   accepts  verify(k, m, compute(k, m)) == True, for every key and message
#   agrees   verify(k, m, t) == B.Octets.is_eq(compute(k, m), t), for every
#            tag t: verify accepts exactly the computed tag
#
# CrMac.verify_tag is the named default ~verify: it compares the computed
# tag with every byte of the given one (no early exit; Octets.is_eq), and
# satisfies both laws for every ~compute (LAWS.bend: mac_verify_tag_*). The
# instances: HMAC over any hash (hmac.bend) and CMAC over any 128-bit block
# cipher (cipher-modes' Cmac.mac).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

# whether t is m's tag, comparing every byte
def CrMac.verify_tag(~K: Data, ~compute: K -> B.Octets -> B.Octets, k: K, m: B.Octets, t: B.Octets) -> Bool:
  B.Octets.is_eq(compute(k, m), t)

# the tag of m under a raw key
def CrMac.compute_with(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, key_o: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, K, B.Octets, k => compute(k, m), key(key_o))
