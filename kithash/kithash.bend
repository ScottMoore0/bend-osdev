# bend-osdev-kithash: an adapter for bend-kit-hash@0.2.0.0 (FNV-1a,
# xxHash, SipHash-1-3, CRC-32 and Adler-32 over bend-kit's Bytes). This file:
# each of its hashes on Octets, with bend-osdev's W64 for 64-bit seeds, keys
# and results, so that no other package sees bend-kit's types.
#
# Bytes cross through bend-kit-hash's own byte-string forms (`*.str`, one
# Char per octet: bend-kit-bytes' from_string), as lz4 does for XXH32.
# 64-bit words cross through bend-kit-hash's arithmetic (mul32, W64.swap,
# W64.add, W64.lo), never its W64 constructor: it publishes no constructor
# def and no accessor of the high half (AUDIT.md).
#
# inst_hash.bend makes the unkeyed hashes instances of crypto's hash
# interface; inst_mac.bend makes SipHash-1-3, and the siphash package's
# SipHash-c-d and HalfSipHash-c-d, instances of its MAC interface.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import bend-kit-hash@0.2.0.0/hash.bend as H

# Words

# bend-osdev's W64 as bend-kit-hash's: hi * 2^32 + lo, from full products
# by 1 (mul32(1, x) is x in the low half)
def kh.to_kit(+v: W.W64) -> H.W64:
  H.W64.add(H.W64.swap(H.mul32(1, W.W64.hi(v))), H.mul32(1, W.W64.lo(v)))

# bend-kit-hash's W64 as bend-osdev's
def kh.of_kit(+v: H.W64) -> W.W64:
  W.W64.from_parts(H.W64.lo(H.W64.swap(v)), H.W64.lo(v))

# the bytes as bend-kit's byte string
def kh.str(o: B.Octets) -> String:
  B.Octets.to_string(o)

# The hashes

# CRC-32 (ISO-HDLC: zlib, gzip, Ethernet)
def KhCrc32.value(o: B.Octets) -> U32:
  H.crc32.str(kh.str(o))

# Adler-32 (RFC 1950)
def KhAdler32.value(o: B.Octets) -> U32:
  H.adler32.str(kh.str(o))

# FNV-1a, 32 and 64 bits
def KhFnv1a32.value(o: B.Octets) -> U32:
  H.fnv1a32.str(kh.str(o))

def KhFnv1a64.value(o: B.Octets) -> W.W64:
  kh.of_kit(H.fnv1a64.str(kh.str(o)))

# XXH32 and XXH64 with a seed
def KhXxh32.value(+seed: U32, o: B.Octets) -> U32:
  H.xxh32.str(kh.str(o), seed)

def KhXxh64.value(+seed: W.W64, o: B.Octets) -> W.W64:
  kh.of_kit(H.xxh64.str(kh.str(o), kh.to_kit(seed)))

# SipHash-1-3 under the key words k0, k1 (the key's bytes 0..7 and 8..15,
# little-endian)
def KhSip13.value(+k0: W.W64, +k1: W.W64, o: B.Octets) -> W.W64:
  kh.of_kit(H.siphash13.str(kh.str(o), kh.to_kit(k0), kh.to_kit(k1)))
