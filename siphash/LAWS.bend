# bend-osdev-siphash: the laws of SipHash-c-d and HalfSipHash-c-d.
#
# Properties, for every parameter set (c, d, output width), key, state and
# message: streaming (bytes in any split give the state of the whole), the
# one-shot form is the streaming one, and the output length. Vectors: the
# paper's Appendix A, entries of the reference implementation's vectors.h,
# and the openssl command's SipHash-1-3, proved by computation.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./siphash.bend as S
import ./halfsiphash.bend as H

# SipHash: the state after a ++ b is the state after a, then b

law siphash_streaming:
  for +s: S.SipState
  for +a: B.Octets
  for +b: B.Octets
  {S.SipHash.update(s, B.Octets.append(a, b)) == S.SipHash.update(S.SipHash.update(s, a), b) : S.SipState}

law siphash_update_empty:
  for +s: S.SipState
  {S.SipHash.update(s, B.Octets.empty()) == s : S.SipState}

# streaming over any split gives the one-shot output
law siphash_split:
  for +prm: S.SipParams
  for +k: S.SipKey
  for +a: B.Octets
  for +b: B.Octets
  {S.SipHash.finish(S.SipHash.update(S.SipHash.update(S.SipHash.start(prm, k), a), b)) == S.SipHash.hash(prm, k, B.Octets.append(a, b)) : B.Octets}

# the output has 8 bytes, or 16 when wide, from every state
law siphash_length:
  for +s: S.SipState
  {B.Octets.len(S.SipHash.finish(s)) == S.SipParams.out_len(S.SipHash.params(s)) : Nat}

# HalfSipHash: the same

law halfsiphash_streaming:
  for +s: H.HsipState
  for +a: B.Octets
  for +b: B.Octets
  {H.HalfSipHash.update(s, B.Octets.append(a, b)) == H.HalfSipHash.update(H.HalfSipHash.update(s, a), b) : H.HsipState}

law halfsiphash_update_empty:
  for +s: H.HsipState
  {H.HalfSipHash.update(s, B.Octets.empty()) == s : H.HsipState}

law halfsiphash_split:
  for +prm: S.SipParams
  for +k: H.HsipKey
  for +a: B.Octets
  for +b: B.Octets
  {H.HalfSipHash.finish(H.HalfSipHash.update(H.HalfSipHash.update(H.HalfSipHash.start(prm, k), a), b)) == H.HalfSipHash.hash(prm, k, B.Octets.append(a, b)) : B.Octets}

# the output has 4 bytes, or 8 when wide, from every state
law halfsiphash_length:
  for +s: H.HsipState
  {B.Octets.len(H.HalfSipHash.finish(s)) == H.HalfSipParams.out_len(H.HalfSipHash.params(s)) : Nat}

# Vectors

# the paper's Appendix A: the key 00 01 .. 0f read little-endian as
# k0 = 0706050403020100, k1 = 0f0e0d0c0b0a0908
law siphash_key_paper:
  {S.SipKey.of_octets(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])) == Done{S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048))} : Result<&2, &2, S.SipError, S.SipKey>}

# and SipHash-2-4 of the 15 bytes 00 01 .. 0e is a129ca6149be45e5
# (written little-endian)
law siphash24_paper:
  {S.siphash24(S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048)), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])) == B.Octets.of_list([229, 69, 190, 73, 97, 202, 41, 161]) : B.Octets}

# vectors.h: vectors_sip64[0] and [8], vectors_sip128[15] (the same key)
law siphash24_vector_0:
  {S.siphash24(S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048)), B.Octets.empty()) == B.Octets.of_list([49, 14, 14, 221, 71, 219, 111, 114]) : B.Octets}

law siphash24_vector_8:
  {S.siphash24(S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048)), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7])) == B.Octets.of_list([98, 36, 147, 154, 121, 245, 245, 147]) : B.Octets}

law siphash24_wide_vector_15:
  {S.SipHash.hash(S.SipParams.sip24_wide(), S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048)), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])) == B.Octets.of_list([84, 147, 233, 153, 51, 176, 168, 17, 126, 8, 236, 15, 151, 207, 195, 217]) : B.Octets}

# SipHash-1-3 of the same 15 bytes: the openssl command's value
law siphash13_openssl:
  {S.siphash13(S.SipKey.of_words(W.W64.from_parts(117835012, 50462976), W.W64.from_parts(252579084, 185207048)), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])) == B.Octets.of_list([86, 153, 81, 42, 109, 216, 32, 211]) : B.Octets}

# vectors.h: vectors_hsip32[0] and [7], vectors_hsip64[15] (the key 00 .. 07)
law halfsiphash24_vector_0:
  {H.halfsiphash24(H.HsipKey.of_words(50462976, 117835012), B.Octets.empty()) == B.Octets.of_list([169, 53, 159, 91]) : B.Octets}

law halfsiphash24_vector_7:
  {H.halfsiphash24(H.HsipKey.of_words(50462976, 117835012), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6])) == B.Octets.of_list([139, 207, 99, 197]) : B.Octets}

law halfsiphash24_wide_vector_15:
  {H.HalfSipHash.hash(H.HalfSipParams.hsip24_wide(), H.HsipKey.of_words(50462976, 117835012), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])) == B.Octets.of_list([33, 125, 11, 203, 78, 129, 201, 2]) : B.Octets}

# keys of the wrong length are refused
law siphash_key_15:
  {S.SipKey.of_octets(B.Octets.zeros(15n)) == Fail{S.SipBadKeyLength{15n}} : Result<&2, &2, S.SipError, S.SipKey>}

law halfsiphash_key_16:
  {H.HsipKey.of_octets(B.Octets.zeros(16n)) == Fail{S.SipBadKeyLength{16n}} : Result<&2, &2, S.SipError, H.HsipKey>}
