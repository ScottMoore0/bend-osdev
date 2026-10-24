# Laws of the interfaces and of the generic algorithms built on them: each
# holds for every algorithm that has an interface's shape, so it is stated
# once over the template arguments and needs nothing from the algorithm but
# its type. A law that needs a property of the algorithm takes it as an
# ordinary hypothesis at the arguments it is used at (lift_round_trip,
# sign_verify_bytes_if, kex_agree_if).
#
# The laws about the instances, the algorithms of other packages through the
# interfaces, are in one pair of law and proof files per package they come
# from, each importing only the proofs it rests on and checked on its own
# (all of them in one file outgrew a check process's memory under
# --verdict; README.md, Laws). A proof elsewhere that uses a law imports
# the pair that holds it:
#   LAWS_cm.bend   cipher-modes' AES, CMAC and CCM, and its 128-bit block
#   LAWS_lc.bend   legacy-ciphers' block ciphers and RC4, and its 64-bit block
#   LAWS_crc.bend  crc's CRCs as hashes, and HMAC and HKDF over them
#   LAWS_sha.bend  bend-collections' SHA-256, SHA-512 and SHA3-256, and HMAC,
#                  HKDF, PBKDF2 and the SP 800-108 KDFs over them
#   LAWS_hs.bend   the hashes package's hashes and Michael, and HMAC and
#                  PBKDF2 over them
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./stream.bend as St
import ./modes.bend as Md
import ./xcbc.bend as Xc
import ./vmac.bend as Vm
import ./mac.bend as Mc
import ./hmac.bend as Hm
import ./sign.bend as Sg
import ./kex.bend as Kx
import ./pbkdf2.bend as Pb
import ./kbkdf.bend as Kb

# Stream ciphers from keystream generators (stream.bend): for every keystream
# generator, CrXor satisfies the stream-cipher laws

# the cipher is its own inverse: from one state, applied twice, the data
# comes back
law xor_involution:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +m: B.Octets
  {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, m)))) == m : B.Octets}

# data in pieces: the output of a ++ b is the output of a, then the output of
# b from the state after a
law xor_streaming_data:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == B.Octets.append(St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, s, a)), St.CrXor.out_data(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, a)), b))) : B.Octets}

law xor_streaming_state:
  for ~S: Data
  for ~next: S -> St.CrKsStep<S>
  for +s: S
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, B.Octets.append(a, b))) == St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, St.CrXor.out_state(~S, St.CrXor.update(~S, ~next, s, a)), b)) : S}

# CTR over any block cipher (modes.bend) is CrXor over its keystream
# generator, so it satisfies the stream-cipher laws for every block cipher

law ctr_involution:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +s: Md.CrCtrState<K>
  for +m: B.Octets
  {St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, m)))) == m : B.Octets}

law ctr_streaming_data:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +s: Md.CrCtrState<K>
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, B.Octets.append(a, b))) == B.Octets.append(St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a)), St.CrXor.out_data(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a)), b))) : B.Octets}

law ctr_streaming_state:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +s: Md.CrCtrState<K>
  for +a: B.Octets
  for +b: B.Octets
  {St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, B.Octets.append(a, b))) == St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, St.CrXor.out_state(~Md.CrCtrState<K>, Md.CrCtr.update(~K, ~Blk, ~enc, ~blk_of, ~blk_to, s, a)), b)) : Md.CrCtrState<K>}

# MACs (mac.bend): the named default verify accepts the computed tag, and
# exactly it, for every MAC; so HMAC over any hash accepts what it computes
# (and CMAC over any 128-bit block cipher, cmac_accepts in LAWS_cm.bend)

law mac_verify_tag_accepts:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +m: B.Octets
  {Mc.CrMac.verify_tag(~K, ~compute, k, m, compute(k, m)) == True{} : Bool}

law mac_verify_tag_agrees:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +m: B.Octets
  for t: B.Octets
  {Mc.CrMac.verify_tag(~K, ~compute, k, m, t) == B.Octets.is_eq(compute(k, m), t) : Bool}

law hmac_accepts:
  for ~digest: B.Octets -> B.Octets
  for +kk: Hm.CrHmacKey
  for +m: B.Octets
  {Hm.CrHmac.verify(~digest, kk, m, Hm.CrHmac.mac(~digest, kk, m)) == True{} : Bool}

# XCBC-MAC over every block cipher (xcbc.bend) accepts what it computes
law xcbc_accepts:
  for ~K: Data
  for ~Blk: Data
  for ~bsize: Nat
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +kk: Xc.CrXcbcKey<K>
  for +m: B.Octets
  {Xc.CrXcbc.verify(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, m, Xc.CrXcbc.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, kk, m)) == True{} : Bool}

# VMAC over every block cipher and nonce length (vmac.bend) accepts what it
# computes
law vmac_accepts:
  for ~K: Data
  for ~Blk: Data
  for ~bsize: Nat
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for ~nlen: Nat
  for +kk: Vm.CrVmacKey<K>
  for +m: B.Octets
  {Vm.CrVmac.verify(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen, kk, m, Vm.CrVmac.mac(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ~nlen, kk, m)) == True{} : Bool}

# AEADs: an algorithm's round trip survives the mapping of its errors onto
# CrError, for every algorithm (r: its encryption's result, d: its
# decryption)

law lift_round_trip:
  for ~E: Data
  for ~f: E -> Cr.CrError
  for d: B.Octets -> Result<&2, &2, E, B.Octets>
  for r: Result<&2, &2, E, B.Octets>
  for +p: B.Octets
  for h: {Result.bind(&2, &2, E, B.Octets, B.Octets, r, d) == Result.map(&2, &2, E, B.Octets, B.Octets, c => p, r) : Result<&2, &2, E, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Cr.CrError.lift(~E, ~B.Octets, ~f, r), c => Cr.CrError.lift(~E, ~B.Octets, ~f, d(c))) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Cr.CrError.lift(~E, ~B.Octets, ~f, r)) : Result<&2, &2, Cr.CrError, B.Octets>}

# Signatures and key agreement (sign.bend, kex.bend): the generic helpers
# keep the interface laws (README.md); the instances (RSA, DH, ECDSA, ECDH,
# SM2, EC-RDSA) and their laws are in bend-osdev-pubkey. A signature
# checked from the public key's bytes is accepted, for every scheme, secret
# key and message, when the scheme's pk_format and accepts laws hold there
# (hf, ha)
law sign_verify_bytes_if:
  for ~SK: Data
  for ~PK: Data
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~sign: SK -> B.Octets -> B.Octets
  for ~verify: PK -> B.Octets -> B.Octets -> Bool
  for +sk: SK
  for +m: B.Octets
  for hf: {pk_of(pk_to(public(sk))) == Done{public(sk)} : Result<&2, &2, Cr.CrError, PK>}
  for ha: {verify(public(sk), m, sign(sk, m)) == True{} : Bool}
  {Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, pk_to(public(sk)), m, sign(sk, m)) == True{} : Bool}

# two parties agree from each other's public-key bytes, for every scheme and
# pair of secret keys, when the keys parse (hx, hy), the public keys survive
# their bytes (hfx, hfy) and the scheme's agree law holds for them (h)
law kex_agree_if:
  for ~SK: Data
  for ~PK: Data
  for ~secret: B.Octets -> Result<&2, &2, Cr.CrError, SK>
  for ~public: SK -> PK
  for ~pk_of: B.Octets -> Result<&2, &2, Cr.CrError, PK>
  for ~pk_to: PK -> B.Octets
  for ~shared: SK -> PK -> Result<&2, &2, Cr.CrError, B.Octets>
  for +a: B.Octets
  for +b: B.Octets
  for +x: SK
  for +y: SK
  for hx: {secret(a) == Done{x} : Result<&2, &2, Cr.CrError, SK>}
  for hy: {secret(b) == Done{y} : Result<&2, &2, Cr.CrError, SK>}
  for hfx: {pk_of(pk_to(public(x))) == Done{public(x)} : Result<&2, &2, Cr.CrError, PK>}
  for hfy: {pk_of(pk_to(public(y))) == Done{public(y)} : Result<&2, &2, Cr.CrError, PK>}
  for h: {shared(x, public(y)) == shared(y, public(x)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, a, pk_to(public(y))) == Kx.CrKex.agree(~SK, ~PK, ~secret, ~pk_of, ~shared, b, pk_to(public(x))) : Result<&2, &2, Cr.CrError, B.Octets>}

# PBKDF2 over any MAC (pbkdf2.bend), for every MAC, password, salt,
# iteration count and length: a derivation that succeeds gives exactly the
# length asked for (the KDF interface's length law); the unchecked stream
# has that length, and a shorter stream is a prefix of a longer (the KDF
# interface's prefix law)
law pbkdf2_length:
  for ~K: Data
  for ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>
  for ~compute: K -> B.Octets -> B.Octets
  for ~hlen: Nat
  for +p: B.Octets
  for +salt: B.Octets
  for +c: U32
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Pb.CrPbkdf2.pbkdf2(~K, ~key, ~compute, ~hlen, p, salt, c, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Pb.CrPbkdf2.pbkdf2(~K, ~key, ~compute, ~hlen, p, salt, c, n)) : Result<&2, &2, Cr.CrError, Nat>}

law pbkdf2_stream_length:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +salt: B.Octets
  for +c: U32
  for +n: Nat
  {B.Octets.len(Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, n)) == n : Nat}

law pbkdf2_stream_prefix:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for +k: K
  for +salt: B.Octets
  for +c: U32
  for +n: Nat
  for +j: Nat
  {B.Octets.take(n, Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, Nat.add(n, j))) == Pb.CrPbkdf2.stream(~K, ~compute, k, salt, c, n) : B.Octets}

# SP 800-108 KDFs over any MAC (kbkdf.bend), for every MAC, key, fixed
# input data and length: each stream has the length asked for, a shorter
# stream is a prefix of a longer one with the same fixed input (and IV), and
# a derivation that succeeds has the length asked for. (The interface's
# prefix law holds of the streams: a derivation binds its length L into
# the fixed input, so derivations of two lengths differ.)
law kbkdf_counter_stream_length:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +fixed: B.Octets
  for +n: Nat
  {B.Octets.len(Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, n)) == n : Nat}

law kbkdf_counter_stream_prefix:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +fixed: B.Octets
  for +n: Nat
  for +j: Nat
  {B.Octets.take(n, Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, Nat.add(n, j))) == Kb.CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, n) : B.Octets}

law kbkdf_feedback_stream_length:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +iv: B.Octets
  for +fixed: B.Octets
  for +n: Nat
  {B.Octets.len(Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, n)) == n : Nat}

law kbkdf_feedback_stream_prefix:
  for ~K: Data
  for ~compute: K -> B.Octets -> B.Octets
  for ~rlen: Nat
  for +k: K
  for +iv: B.Octets
  for +fixed: B.Octets
  for +n: Nat
  for +j: Nat
  {B.Octets.take(n, Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, Nat.add(n, j))) == Kb.CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, n) : B.Octets}

law kbkdf_counter_length:
  for ~K: Data
  for ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>
  for ~compute: K -> B.Octets -> B.Octets
  for ~hlen: Nat
  for ~rlen: Nat
  for ~llen: Nat
  for +ki: B.Octets
  for +label: B.Octets
  for +context: B.Octets
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.CrKbkdf.counter_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, label, context, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.CrKbkdf.counter_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, label, context, n)) : Result<&2, &2, Cr.CrError, Nat>}

law kbkdf_feedback_length:
  for ~K: Data
  for ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>
  for ~compute: K -> B.Octets -> B.Octets
  for ~hlen: Nat
  for ~rlen: Nat
  for ~llen: Nat
  for +ki: B.Octets
  for +iv: B.Octets
  for +label: B.Octets
  for +context: B.Octets
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Kb.CrKbkdf.feedback_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, iv, label, context, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Kb.CrKbkdf.feedback_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, ki, iv, label, context, n)) : Result<&2, &2, Cr.CrError, Nat>}
