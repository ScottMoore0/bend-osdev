# The named SP 800-108 KDFs (kbkdf.bend) over HMAC-SHA-256 (inst_sha2.bend),
# with a 32-bit counter and a 32-bit [L]_2: counter mode, and feedback mode
# with the counter. As a KDF (kdf.bend), counter mode is
#   ~Kb.CrKbkdf.derive(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256), ~Hm.CrHmac.mac(~SH.CrSha2.sha256), ~32n, ~4n, ~4n)
# and the same tuple with another MAC, its tag length, or other field
# widths gives the other members of the family.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./hmac.bend as Hm
import ./kbkdf.bend as Kb
import ./inst_sha2.bend as SH

def CrKbkdf.hmac_sha256_counter(ki: B.Octets, label: B.Octets, context: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Kb.CrKbkdf.counter_kdf(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256), ~Hm.CrHmac.mac(~SH.CrSha2.sha256), ~32n, ~4n, ~4n, ki, label, context, n)

def CrKbkdf.hmac_sha256_feedback(ki: B.Octets, iv: B.Octets, label: B.Octets, context: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Kb.CrKbkdf.feedback_kdf(~Hm.CrHmacKey, ~Hm.CrHmac.key_of(~64n, ~SH.CrSha2.sha256), ~Hm.CrHmac.mac(~SH.CrSha2.sha256), ~32n, ~4n, ~4n, ki, iv, label, context, n)
