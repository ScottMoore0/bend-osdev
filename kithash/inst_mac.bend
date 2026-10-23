# bend-osdev-kithash: SipHash as instances of crypto's MAC interface
# (crypto/mac.bend): bend-kit-hash's SipHash-1-3, and the siphash package's
# SipHash-c-d and HalfSipHash-c-d for every parameter set (bend-kit-hash has
# neither SipHash-2-4 nor HalfSipHash; Linux uses SipHash-2-4 as siphash,
# and SipHash-1-3 or HalfSipHash-1-3 as hsiphash). The key errors map onto
# CrError; verify is crypto's named default (every byte compared).
#
# Every SipHash instance takes the same 16-byte key (siphash's SipKey: k0
# and k1, little-endian) and gives the same tag form (the 64-bit output
# little-endian, as the reference implementation writes it), so
# bend-kit-hash's SipHash-1-3 and siphash's are interchangeable (LAWS.bend:
# sip13_agrees_*). The instances:
#   SipHash-c-d          ~S.SipKey, ~KhSip.key, ~KhSip.compute(~prm), ~KhSip.verify(~prm)
#     prm S.SipParams.sip24() (SipHash-2-4), .sip13(), .sip48(), .sip24_wide() (128-bit tag)
#   bend-kit-hash's SipHash-1-3
#                        ~S.SipKey, ~KhSip.key, ~KhSip13.compute, ~KhSip13.verify
#   HalfSipHash-c-d      ~HS.HsipKey, ~KhHsip.key, ~KhHsip.compute(~prm), ~KhHsip.verify(~prm)
#     prm HS.HalfSipParams.hsip24(), .hsip13(), .hsip24_wide() (64-bit tag); an 8-byte key
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/mac.bend as Mc
import ../siphash/siphash.bend as S
import ../siphash/halfsiphash.bend as HS
import ./kithash.bend as K

def KhSip.err(e: S.SipError) -> Cr.CrError:
  match e:
    case S.SipBadKeyLength{n}:
      Cr.CrBadKeyLength{n}

# Keys: 16 bytes for SipHash, 8 for HalfSipHash (CrBadKeyLength otherwise)

def KhSip.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, S.SipKey>:
  Cr.CrError.lift(~S.SipError, ~S.SipKey, ~KhSip.err, S.SipKey.of_octets(o))

def KhHsip.key(o: B.Octets) -> Result<&2, &2, Cr.CrError, HS.HsipKey>:
  Cr.CrError.lift(~S.SipError, ~HS.HsipKey, ~KhSip.err, HS.HsipKey.of_octets(o))

# SipHash-c-d (the siphash package)

def KhSip.compute(~prm: S.SipParams, k: S.SipKey, m: B.Octets) -> B.Octets:
  S.SipHash.hash(prm, k, m)

def KhSip.verify(~prm: S.SipParams, k: S.SipKey, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~S.SipKey, ~KhSip.compute(~prm), k, m, t)

# bend-kit-hash's SipHash-1-3

def kh.sip13(+k: S.SipKey, m: B.Octets) -> B.Octets:
  B.Octets.le64(K.KhSip13.value(S.SipKey.k0(k), S.SipKey.k1(k), m))

def KhSip13.compute(k: S.SipKey, m: B.Octets) -> B.Octets:
  kh.sip13(k, m)

def KhSip13.verify(k: S.SipKey, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~S.SipKey, ~KhSip13.compute, k, m, t)

# HalfSipHash-c-d (the siphash package)

def KhHsip.compute(~prm: S.SipParams, k: HS.HsipKey, m: B.Octets) -> B.Octets:
  HS.HalfSipHash.hash(prm, k, m)

def KhHsip.verify(~prm: S.SipParams, k: HS.HsipKey, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~HS.HsipKey, ~KhHsip.compute(~prm), k, m, t)
