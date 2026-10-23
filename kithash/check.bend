# bend-osdev-kithash: every instance through crypto's interfaces, and
# bend-kit-hash against bend-osdev's own implementations on 10,000 bytes.
# Expected values: CRC-32 and Adler-32 Python's zlib; XXH32, XXH64 and
# FNV-1a ref/model.py's (checked against the lz4 and zstd commands and RFC
# 9923's vectors); SipHash the openssl command's and vectors.h's;
# HalfSipHash-1-3 siphash/ref/model.py's.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/hash.bend as Hh
import ../crypto/mac.bend as Mc
import ../crc/crc.bend as C
import ../deflate/adler32.bend as A
import ../zstd/xxh64.bend as X
import ../siphash/siphash.bend as S
import ../siphash/halfsiphash.bend as HS
import ./kithash.bend as K
import ./inst_hash.bend as IH
import ./inst_mac.bend as IM

def nine() -> B.Octets:
  B.Octets.of_string("123456789")

def pieces() -> List<&2, B.Octets>:
  [B.Octets.of_string("1234"), B.Octets.of_string("5"), B.Octets.of_string("6789")]

# the one-shot digest of "123456789", and its digest in three pieces
# through the hash interface
def both(~digest: B.Octets -> B.Octets) -> String:
  B.Octets.hex(digest(nine())) ++ " " ++ B.Octets.hex(Hh.CrHash.of_pieces(~IH.KhBuf, ~IH.KhBuf.init(), ~IH.KhBuf.update, ~IH.KhBuf.final(~digest), pieces()))

# the bytes 0, 1, .., n - 1
def iota.go(+n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      iota.go(p, Con{U32.from_nat(p), acc})

def msg(n: Nat) -> B.Octets:
  B.Octets.of_list(iota.go(n, Nil{}))

# n pseudo-random bytes (a linear congruential generator)
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat) -> B.Octets:
  B.Octets.of_list(bulk.go(n, 7, Nil{}))

def show(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{Cr.CrBadKeyLength{n}}:
      "refused " ++ Nat.show(n)
    case Fail{e}:
      "refused"

def sipkey() -> S.SipKey:
  S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048))

def hsipkey() -> HS.HsipKey:
  HS.HsipKey.of_words(50462976, 117835012)

def first(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{v}:
      v
    case None{}:
      0

# verify of the computed tag, and of the tag with its first byte changed
def verifies(~verify: S.SipKey -> B.Octets -> B.Octets -> Bool, +t: B.Octets) -> String:
  Bool.show(verify(sipkey(), msg(15n), t)) ++ " " ++ Bool.show(verify(sipkey(), msg(15n), B.Octets.cons(U32.xor(255, first(B.Octets.at(t, 0n))), B.Octets.drop(1n, t))))

def main() -> IO(Unit):
  +big = bulk(10000n)
  +tag24 = IM.KhSip.compute(~S.SipParams.sip24(), sipkey(), msg(15n))
  +tag13 = IM.KhSip13.compute(sipkey(), msg(15n))
  do IO<Unit>:
    IO.print("crc32 " ++ both(~IH.KhCrc32.digest))
    IO.print("adler32 " ++ both(~IH.KhAdler32.digest))
    IO.print("fnv1a32 " ++ both(~IH.KhFnv1a32.digest))
    IO.print("fnv1a64 " ++ both(~IH.KhFnv1a64.digest))
    IO.print("xxh32 " ++ both(~IH.KhXxh32.digest(~0)))
    IO.print("xxh32 seed 1 " ++ both(~IH.KhXxh32.digest(~1)))
    IO.print("xxh64 " ++ both(~IH.KhXxh64.digest(~W.W64.zero())))
    IO.print("xxh64 seed 1 " ++ both(~IH.KhXxh64.digest(~W.W64.from_u32(1))))
    IO.print("crc32 bulk " ++ U32.show(K.KhCrc32.value(big)) ++ " " ++ U32.show(C.crc32(big)))
    IO.print("adler32 bulk " ++ U32.show(K.KhAdler32.value(big)) ++ " " ++ U32.show(A.adler32(big)))
    IO.print("xxh64 bulk " ++ W.W64.show_hex(K.KhXxh64.value(W.W64.zero(), big)) ++ " " ++ W.W64.show_hex(X.ZstdXxh64.hash(W.W64.zero(), big)))
    IO.print("xxh32 bulk " ++ U32.show(K.KhXxh32.value(0, big)))
    IO.print("fnv1a64 bulk " ++ W.W64.show_hex(K.KhFnv1a64.value(big)))
    IO.print("sip13 bulk " ++ B.Octets.hex(IM.KhSip13.compute(sipkey(), big)) ++ " " ++ B.Octets.hex(IM.KhSip.compute(~S.SipParams.sip13(), sipkey(), big)))
    IO.print("siphash24 " ++ show(Mc.CrMac.compute_with(~S.SipKey, ~IM.KhSip.key, ~IM.KhSip.compute(~S.SipParams.sip24()), msg(16n), msg(15n))))
    IO.print("siphash24 verify " ++ verifies(~IM.KhSip.verify(~S.SipParams.sip24()), tag24))
    IO.print("siphash24 wide " ++ show(Mc.CrMac.compute_with(~S.SipKey, ~IM.KhSip.key, ~IM.KhSip.compute(~S.SipParams.sip24_wide()), msg(16n), msg(15n))))
    IO.print("kit siphash13 " ++ show(Mc.CrMac.compute_with(~S.SipKey, ~IM.KhSip.key, ~IM.KhSip13.compute, msg(16n), msg(15n))))
    IO.print("kit siphash13 verify " ++ verifies(~IM.KhSip13.verify, tag13))
    IO.print("siphash13 " ++ show(Mc.CrMac.compute_with(~S.SipKey, ~IM.KhSip.key, ~IM.KhSip.compute(~S.SipParams.sip13()), msg(16n), msg(15n))))
    IO.print("halfsiphash24 " ++ show(Mc.CrMac.compute_with(~HS.HsipKey, ~IM.KhHsip.key, ~IM.KhHsip.compute(~HS.HalfSipParams.hsip24()), msg(8n), msg(15n))))
    IO.print("halfsiphash13 " ++ show(Mc.CrMac.compute_with(~HS.HsipKey, ~IM.KhHsip.key, ~IM.KhHsip.compute(~HS.HalfSipParams.hsip13()), msg(8n), msg(15n))))
    IO.print("halfsiphash24 verify " ++ Bool.show(IM.KhHsip.verify(~HS.HalfSipParams.hsip24(), hsipkey(), msg(15n), HS.halfsiphash24(hsipkey(), msg(15n)))))
    IO.print("siphash key 15 " ++ show(Mc.CrMac.compute_with(~S.SipKey, ~IM.KhSip.key, ~IM.KhSip13.compute, msg(15n), msg(3n))))
    IO.print("halfsiphash key 16 " ++ show(Mc.CrMac.compute_with(~HS.HsipKey, ~IM.KhHsip.key, ~IM.KhHsip.compute(~HS.HalfSipParams.hsip13()), msg(16n), msg(3n))))

#|crc32 cbf43926 cbf43926
#|adler32 091e01de 091e01de
#|fnv1a32 bb86b11c bb86b11c
#|fnv1a64 06d5573923c6cdfc 06d5573923c6cdfc
#|xxh32 937bad67 937bad67
#|xxh32 seed 1 f261918c f261918c
#|xxh64 8cb841db40e6ae83 8cb841db40e6ae83
#|xxh64 seed 1 1a4cc2c9e8079790 1a4cc2c9e8079790
#|crc32 bulk 4170391814 4170391814
#|adler32 bulk 2456902729 2456902729
#|xxh64 bulk 2c8fe3c4fe925b22 2c8fe3c4fe925b22
#|xxh32 bulk 618823599
#|fnv1a64 bulk 7b802b4ca7f21800
#|sip13 bulk aeca9bc2d37385ac aeca9bc2d37385ac
#|siphash24 e545be4961ca29a1
#|siphash24 verify True False
#|siphash24 wide 5493e99933b0a8117e08ec0f97cfc3d9
#|kit siphash13 5699512a6dd820d3
#|kit siphash13 verify True False
#|siphash13 5699512a6dd820d3
#|halfsiphash24 74fe2b97
#|halfsiphash13 047b25d0
#|halfsiphash24 verify True
#|siphash key 15 refused 15
#|halfsiphash key 16 refused 16
