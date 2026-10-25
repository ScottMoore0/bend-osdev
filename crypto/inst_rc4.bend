# RC4 as a stream cipher: the rc4 package's RC4 (RFC 6229's description), and
# RC4-drop[n] (RFC 4345). RC4 is broken (RFC 7465 forbids it in TLS): it is
# here to read and write what already uses it. The instance:
#   ~R.LcRc4State, ~R.LcRc4Out, ~CrRc4.start, ~R.LcRc4.update,
#   ~R.LcRc4.out_state, ~R.LcRc4.out_data
# and with the first n keystream bytes dropped, ~CrRc4.start_drop(~n) in
# place of ~CrRc4.start.
import Base
import ../bytes/bytes.bend as B
import ../cipher-core/cipher-core.bend as L
import ../rc4/rc4.bend as R
import ./crypto.bend as Cr
import ./inst_lc.bend as LC

def cr.rc4.start(+n: Nat, r: Result<&2, &2, L.LcError, R.LcRc4State>) -> Result<&2, &2, Cr.CrError, R.LcRc4State>:
  do Result<&2, &2, Cr.CrError, R.LcRc4State>:
    Cr.CrError.check(Nat.is_eq(n, 0n), Cr.CrBadIvLength{n})
    LC.CrLc.lift(~R.LcRc4State, r)

# the state for a key of 1 to 256 bytes (CrBadKeyLength otherwise); RC4 has
# no IV, so the IV must be empty (CrBadIvLength otherwise)
def CrRc4.start(key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, R.LcRc4State>:
  cr.rc4.start(B.Octets.len(iv), R.LcRc4.start(key))

# the same, with the first n keystream bytes dropped (RC4-drop[n])
def CrRc4.start_drop(~n: Nat, key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, R.LcRc4State>:
  cr.rc4.start(B.Octets.len(iv), R.LcRc4.start_drop(key, n))
