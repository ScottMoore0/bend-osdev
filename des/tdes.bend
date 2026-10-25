# Triple DES, TDEA (NIST SP 800-67 Rev. 2, 2017): three DES keys, encryption
# E_K3(D_K2(E_K1(b))) and decryption D_K1(E_K2(D_K3(c))), with DES from
# des.bend. SP 800-67 Rev. 2 allows keying option 1 only (three distinct
# keys, 24 bytes); keying option 2 (K3 = K1, 16 bytes) is here for reading
# old data, as the kernel's des3_ede accepts it too. SP 800-67 also requires
# the keys to differ; that is not checked here.
import Base
import ../bytes/bytes.bend as B
import ../cipher-core/cipher-core.bend as L
import ./des.bend as D

# A TDEA key bundle: three DES keys (opaque)
type LcTdesKey is Data:
  LcTdesKey{k1: D.LcDesKey, k2: D.LcDesKey, k3: D.LcDesKey}

# the bundle of three DES keys, in the order K1, K2, K3
def LcTdes.of_des(k1: D.LcDesKey, k2: D.LcDesKey, k3: D.LcDesKey) -> LcTdesKey:
  LcTdesKey{k1, k2, k3}

def tdes.des_key(+xs: List<&2, U32>) -> D.LcDesKey:
  D.des.key_of(L.lc.be(L.lc.at(xs, 0n), L.lc.at(xs, 1n), L.lc.at(xs, 2n), L.lc.at(xs, 3n)), L.lc.be(L.lc.at(xs, 4n), L.lc.at(xs, 5n), L.lc.at(xs, 6n), L.lc.at(xs, 7n)))

def tdes.key3(+xs: List<&2, U32>) -> LcTdesKey:
  LcTdesKey{tdes.des_key(xs), tdes.des_key(B.drop(8n, xs)), tdes.des_key(B.drop(16n, xs))}

def tdes.key2(+xs: List<&2, U32>) -> LcTdesKey:
  LcTdesKey{tdes.des_key(xs), tdes.des_key(B.drop(8n, xs)), tdes.des_key(xs)}

def tdes.key.pick(three: Bool, two: Bool, +xs: List<&2, U32>) -> Result<&2, &2, L.LcError, LcTdesKey>:
  match three two:
    case True{} _:
      Done{tdes.key3(xs)}
    case False{} True{}:
      Done{tdes.key2(xs)}
    case False{} False{}:
      Fail{L.LcBadKeyLength{B.len(xs)}}

# keying option 1: K1, K2, K3 as 24 bytes
def LcTdes.key3(o: B.Octets) -> Result<&2, &2, L.LcError, LcTdesKey>:
  +xs = B.Octets.to_list(o)
  tdes.key.pick(Nat.is_eq(B.len(xs), 24n), False{}, xs)

# keying option 2: K1, K2 as 16 bytes, and K3 = K1
def LcTdes.key2(o: B.Octets) -> Result<&2, &2, L.LcError, LcTdesKey>:
  +xs = B.Octets.to_list(o)
  tdes.key.pick(False{}, Nat.is_eq(B.len(xs), 16n), xs)

# option 1 for 24 bytes, option 2 for 16
def LcTdes.key(o: B.Octets) -> Result<&2, &2, L.LcError, LcTdesKey>:
  +xs = B.Octets.to_list(o)
  +n = B.len(xs)
  tdes.key.pick(Nat.is_eq(n, 24n), Nat.is_eq(n, 16n), xs)

def LcTdes.encrypt(k: LcTdesKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcTdesKey{k1, k2, k3}:
      D.LcDes.encrypt(k3, D.LcDes.decrypt(k2, D.LcDes.encrypt(k1, b)))

def LcTdes.decrypt(k: LcTdesKey, b: L.LcBlock64) -> L.LcBlock64:
  match k:
    case LcTdesKey{k1, k2, k3}:
      D.LcDes.decrypt(k1, D.LcDes.encrypt(k2, D.LcDes.decrypt(k3, b)))
