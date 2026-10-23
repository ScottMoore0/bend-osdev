# Keccak-256 as a hash: bend-collections' Keccak-256 (keccak/keccak.bend),
# the Keccak submission's padding (pad10*1 after the message, no SHA-3
# domain bits) at rate 1088 and capacity 512, as Ethereum uses it; it is
# not SHA3-256, which appends the domain bits 01 first (FIPS 202 section
# 6.1; SHA3-256 is crypto's inst_sha3.bend). bend-collections proves it
# equal to its sponge specification over FIPS 202's Keccak-f[1600], for
# every packed array and length (ethereum_keccak256).
#
# The instance (a buffered state, collections-crypto.bend's CcBuf; block
# size 136, the rate in bytes):
#   ~CcBuf, ~136n, ~32n, ~CcBuf.init(), ~CcBuf.update,
#   ~CcBuf.final(~CcKeccak.keccak256), ~CcKeccak.keccak256
import Base
import ../bytes/bytes.bend as B
import ./blake.bend as Bl
import bend-collections-laws-crypto@1.0.0.0/src/crypto/keccak/keccak.bend as K

# Keccak-256, 32 bytes (the message packed as for BLAKE: CcBlake.pack)
def cc.keccak.keccak256(+o: B.Octets) -> B.Octets:
  Bl.CcBlake.out(8n, K.keccak256(Bl.CcBlake.pack(o), B.Octets.len(o)))

def CcKeccak.keccak256(o: B.Octets) -> B.Octets:
  cc.keccak.keccak256(o)
