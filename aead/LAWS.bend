# Laws about the public interface of the aead package.
#
# Every construction is an AEAD of the crypto package's AEAD interface,
# whose round-trip law is stated as there: open accepts what seal produced
# and gives the plaintext back, and when seal refuses, open-after-seal
# refuses alike,
#   bind(seal(k, n, a, p), c => open(k, n, a, c)) == map(c => p, seal(k, n, a, p))
#
# AEGIS-128 satisfies it for every key, nonce, associated data and message.
# The generic constructions satisfy it wherever what they are built from
# does, at the very arguments they use (a hypothesis h, used once: crypto's
# README, "How the laws are stated"): encrypt-then-MAC wherever its cipher's
# decryption undoes its encryption, ESSIV wherever the wrapped cipher or
# AEAD undoes itself at the derived IV, seqiv and echainiv wherever the
# wrapped AEAD does at the generated IV (of the nonce's length, hl).
#
# A changed tag: AEGIS-128 and encrypt-then-MAC refuse every tag but the one
# they compute (CrTagMismatch), for every key, nonce, associated data and
# ciphertext; a forgery's chance of hitting the right tag is 2^-8tlen, a
# matter of the MAC's or AEGIS's security, not of a law.
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ./aead.bend as Ad
import ./aesround.bend as R
import ./aegis128.bend as G
import ./authenc.bend as Au
import ./essiv.bend as Es
import ./seqiv.bend as Sq
import ./echainiv.bend as Ec

# AEGIS-128 (aegis128.bend)

law aegis128_round_trip:
  for +k: G.AdAegisKey
  for +n: B.Octets
  for +a: B.Octets
  for +p: B.Octets
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, G.AdAegis128.seal(k, n, a, p), c => G.AdAegis128.open(k, n, a, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, G.AdAegis128.seal(k, n, a, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

# a tag of 16 bytes other than the one AEGIS-128 computes for the ciphertext
# is refused, under a 16-byte nonce
law aegis128_tamper:
  for +k: G.AdAegisKey
  for +n: B.Octets
  for +a: B.Octets
  for +c: B.Octets
  for +t: B.Octets
  for hn: {B.Octets.len(n) == 16n : Nat}
  for hl: {B.Octets.len(t) == 16n : Nat}
  for ht: {Ad.AdTag.is_eq(G.AdAegis128.tag_of(k, n, a, c), t) == False{} : Bool}
  {G.AdAegis128.open(k, n, a, B.Octets.append(c, t)) == Fail{Cr.CrTagMismatch{}} : Result<&2, &2, Cr.CrError, B.Octets>}

# RFC 10032, Appendix A.1: AESRound(000102..0f, 101112..1f) =
# 7a7b4e5638782546a8c0477a3b813f43
law aesround_rfc10032:
  {R.AdAes.round(R.AdAes.sbox(), R.AdBlk{66051, 67438087, 134810123, 202182159}, R.AdBlk{269554195, 336926231, 404298267, 471670303}) == R.AdBlk{2054901334, 947397958, 2831173498, 998326083} : R.AdBlk}

# Encrypt-then-MAC (authenc.bend), over every cipher and MAC

law authenc_round_trip_if:
  for ~KE: Data
  for ~KM: Data
  for ~enc: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~dec: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~mac: KM -> B.Octets -> B.Octets
  for ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets
  for ~tlen: Nat
  for +ke: KE
  for +km: KM
  for +iv: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  for h: {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, enc(ke, iv, p), c => dec(ke, iv, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, enc(ke, iv, p)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Au.AdAuthenc.seal(~KE, ~KM, ~enc, ~mac, ~input, ~tlen, Au.AdAuthencKey{ke, km}, iv, aad, p), c => Au.AdAuthenc.open(~KE, ~KM, ~dec, ~mac, ~input, ~tlen, Au.AdAuthencKey{ke, km}, iv, aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Au.AdAuthenc.seal(~KE, ~KM, ~enc, ~mac, ~input, ~tlen, Au.AdAuthencKey{ke, km}, iv, aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

# a tag of tlen bytes other than the computed one is refused, and the
# cipher never runs
law authenc_tamper:
  for ~KE: Data
  for ~KM: Data
  for ~dec: KE -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~mac: KM -> B.Octets -> B.Octets
  for ~input: B.Octets -> B.Octets -> B.Octets -> B.Octets
  for ~tlen: Nat
  for +k: Au.AdAuthencKey<KE, KM>
  for +iv: B.Octets
  for +aad: B.Octets
  for +c: B.Octets
  for +t: B.Octets
  for hl: {B.Octets.len(t) == tlen : Nat}
  for ht: {Ad.AdTag.is_eq(Au.AdAuthenc.tag(~KE, ~KM, ~mac, ~input, ~tlen, k, aad, iv, c), t) == False{} : Bool}
  {Au.AdAuthenc.open(~KE, ~KM, ~dec, ~mac, ~input, ~tlen, k, iv, aad, B.Octets.append(c, t)) == Fail{Cr.CrTagMismatch{}} : Result<&2, &2, Cr.CrError, B.Octets>}

# ESSIV (essiv.bend): over a cipher with an IV, and over an AEAD

law essiv_round_trip_if:
  for ~KD: Data
  for ~KS: Data
  for ~Blk: Data
  for ~enc: KS -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for ~cenc: KD -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~cdec: KD -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for +kd: KD
  for +ks: KS
  for +iv: B.Octets
  for +m: B.Octets
  for h: {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, cenc(kd, Es.AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, Es.AdEssivKey{kd, ks}, iv), m), c => cdec(kd, Es.AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, Es.AdEssivKey{kd, ks}, iv), c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => m, cenc(kd, Es.AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, Es.AdEssivKey{kd, ks}, iv), m)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Es.AdEssiv.encrypt(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~cenc, Es.AdEssivKey{kd, ks}, iv, m), c => Es.AdEssiv.decrypt(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~cdec, Es.AdEssivKey{kd, ks}, iv, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => m, Es.AdEssiv.encrypt(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~cenc, Es.AdEssivKey{kd, ks}, iv, m)) : Result<&2, &2, Cr.CrError, B.Octets>}

law essiv_aead_round_trip_if:
  for ~KD: Data
  for ~KS: Data
  for ~Blk: Data
  for ~enc: KS -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for ~seal: KD -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~open: KD -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for +kd: KD
  for +ks: KS
  for +iv: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  for h: {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, seal(kd, Es.AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, Es.AdEssivKey{kd, ks}, iv), aad, p), c => open(kd, Es.AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, Es.AdEssivKey{kd, ks}, iv), aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, seal(kd, Es.AdEssiv.iv(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, Es.AdEssivKey{kd, ks}, iv), aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Es.AdEssiv.seal(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~seal, Es.AdEssivKey{kd, ks}, iv, aad, p), c => Es.AdEssiv.open(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~open, Es.AdEssivKey{kd, ks}, iv, aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Es.AdEssiv.seal(~KD, ~KS, ~Blk, ~enc, ~blk_of, ~blk_to, ~seal, Es.AdEssivKey{kd, ks}, iv, aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

# seqiv (seqiv.bend) and echainiv (echainiv.bend): the generated IV, ivlen
# bytes long (hl), travels in front of the ciphertext, and the wrapped AEAD
# authenticates it as associated data after A

law seqiv_round_trip_if:
  for ~KA: Data
  for ~seal: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~ivlen: Nat
  for +ka: KA
  for +salt: B.Octets
  for +seq: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  for hl: {B.Octets.len(Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq)) == ivlen : Nat}
  for h: {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, seal(ka, Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq), B.Octets.append(aad, Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq)), p), c => open(ka, Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq), B.Octets.append(aad, Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq)), c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, seal(ka, Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq), B.Octets.append(aad, Sq.AdSeqiv.iv(~KA, Sq.AdSeqivKey{ka, salt}, seq)), p)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Sq.AdSeqiv.seal(~KA, ~seal, Sq.AdSeqivKey{ka, salt}, seq, aad, p), c => Sq.AdSeqiv.open(~KA, ~open, ~ivlen, Sq.AdSeqivKey{ka, salt}, seq, aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Sq.AdSeqiv.seal(~KA, ~seal, Sq.AdSeqivKey{ka, salt}, seq, aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}

law echainiv_round_trip_if:
  for ~KA: Data
  for ~KC: Data
  for ~Blk: Data
  for ~enc: KC -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for ~seal: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~open: KA -> B.Octets -> B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, B.Octets>
  for ~ivlen: Nat
  for +ka: KA
  for +kc: KC
  for +salt: B.Octets
  for +seq: B.Octets
  for +aad: B.Octets
  for +p: B.Octets
  for hl: {B.Octets.len(Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq)) == ivlen : Nat}
  for h: {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, seal(ka, Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq), B.Octets.append(aad, Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq)), p), c => open(ka, Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq), B.Octets.append(aad, Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq)), c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, seal(ka, Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq), B.Octets.append(aad, Ec.AdEchainiv.iv(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, Ec.AdEchainivKey{ka, kc, salt}, seq)), p)) : Result<&2, &2, Cr.CrError, B.Octets>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Ec.AdEchainiv.seal(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, ~seal, Ec.AdEchainivKey{ka, kc, salt}, seq, aad, p), c => Ec.AdEchainiv.open(~KA, ~KC, ~open, ~ivlen, Ec.AdEchainivKey{ka, kc, salt}, seq, aad, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => p, Ec.AdEchainiv.seal(~KA, ~KC, ~Blk, ~enc, ~blk_of, ~blk_to, ~seal, Ec.AdEchainivKey{ka, kc, salt}, seq, aad, p)) : Result<&2, &2, Cr.CrError, B.Octets>}
