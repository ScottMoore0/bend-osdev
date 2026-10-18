# Michael (IEEE 802.11i's TKIP MIC; hashes/michael.bend) as a MAC: the
# adapter for the hashes package's Michael, its key error mapped onto
# CrError. The instance:
#   ~Hs.HsW2, ~CrMichael.key, ~MI.HsMichael.mic, ~CrMichael.verify
# (a key of 8 bytes; the tag is 8 bytes). Michael is weak by design (see
# hashes/README.md): it is here for TKIP.
import Base
import ../bytes/bytes.bend as B
import ../hashes/hashes.bend as Hs
import ../hashes/michael.bend as MI
import ./crypto.bend as Cr
import ./mac.bend as Mc

def CrMichael.err(e: Hs.HsError) -> Cr.CrError:
  match e:
    case Hs.HsBadKeyLength{n}:
      Cr.CrBadKeyLength{n}

# the key of 8 raw bytes (CrBadKeyLength otherwise)
def CrMichael.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, Hs.HsW2>:
  Cr.CrError.lift(~Hs.HsError, ~Hs.HsW2, ~CrMichael.err, MI.HsMichael.key(o))

# whether t is m's tag (the named default verify: every byte compared)
def CrMichael.verify(k: Hs.HsW2, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~Hs.HsW2, ~MI.HsMichael.mic, k, m, t)
