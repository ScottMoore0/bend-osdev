# The named PBKDF2 instances (pbkdf2.bend): PBKDF2-HMAC-SHA-256 (over
# bend-collections' SHA-256, inst_sha2.bend) and PBKDF2-HMAC-SHA-1 (over the
# sha1 package's SHA-1), each taking the password, salt, iteration count
# and output length. As KDFs (kdf.bend), with c iterations:
#   ~Pb.CrPbkdf2.derive(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256), ~Hm.CrHmac.mac(~SH.CrSha2.sha256), ~32n, ~c)
#   ~Pb.CrPbkdf2.derive(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~S1.HsSha1.digest), ~Hm.CrHmac.mac(~S1.HsSha1.digest), ~20n, ~c)
# PBKDF2 over HMAC over any other hash is the same tuple with that hash's
# block size, one-shot digest and digest size.
import Base
import ../bytes/bytes.bend as B
import ../sha1/sha1.bend as S1
import ./crypto.bend as Cr
import ./hmac.bend as Hm
import ./pbkdf2.bend as Pb
import ./inst_sha2.bend as SH

def CrPbkdf2.hmac_sha256(password: B.Octets, salt: B.Octets, c: U32, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Pb.CrPbkdf2.pbkdf2(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256), ~Hm.CrHmac.mac(~SH.CrSha2.sha256), ~32n, password, salt, c, n)

def CrPbkdf2.hmac_sha1(password: B.Octets, salt: B.Octets, c: U32, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Pb.CrPbkdf2.pbkdf2(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~S1.HsSha1.digest), ~Hm.CrHmac.mac(~S1.HsSha1.digest), ~20n, password, salt, c, n)
