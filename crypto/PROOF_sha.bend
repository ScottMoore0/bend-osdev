# Proofs of LAWS_sha.bend, from bend-collections-laws-crypto's laws.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./hmac.bend as Hm
import ./inst_sha2.bend as SH
import ./inst_sha3.bend as S3
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc
import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/hash/laws.bend as HL
import bend-collections-laws-crypto@1.0.0.0/proofs/crypto/hash/proof.bend as HP
import ./proof_bits.bend as Bits
import ./LAWS_sha.bend as Laws

# SHA-256, SHA-512 and SHA3-256: bend-collections-laws-crypto's laws,
# through Octets

def Laws.sha256_spec(o):
  %HL.Sha256.value(B.Octets.to_list(o)) : {SH.CrSha2.sha256(o) == B.Octets.of_list(_) : B.Octets}
  {==}

def Laws.sha256_hash_split(a, b):
  %Equal.sym(List<&2, U32>, Hc.digest(Hc.update(Hc.update(Hc.new_sha256(), B.Octets.to_list(a)), B.Octets.to_list(b))), Hc.sha256(List.append(&2, U32, B.Octets.to_list(a), B.Octets.to_list(b))), HL.Split.sha256(B.Octets.to_list(a), B.Octets.to_list(b))) : {B.Octets.of_list(_) == SH.CrSha2.sha256(B.Octets.append(a, b)) : B.Octets}
  %BL.octets_append_list(a, b) : {B.Octets.of_list(Hc.sha256(_)) == SH.CrSha2.sha256(B.Octets.append(a, b)) : B.Octets}
  {==}

def Laws.sha256_hash_split3(a, b, c):
  %Equal.sym(List<&2, U32>, Hc.digest(Hc.update(Hc.update(Hc.update(Hc.new_sha256(), B.Octets.to_list(a)), B.Octets.to_list(b)), B.Octets.to_list(c))), Hc.sha256(List.concat(&2, U32, [B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c)])), HL.Incremental.sha256([B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c)])) : {B.Octets.of_list(_) == SH.CrSha2.sha256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %Bits.append_nil(B.Octets.to_list(c)) : {B.Octets.of_list(Hc.sha256(List.append(&2, U32, B.Octets.to_list(a), List.append(&2, U32, B.Octets.to_list(b), _)))) == SH.CrSha2.sha256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %BL.octets_append_list(b, c) : {B.Octets.of_list(Hc.sha256(List.append(&2, U32, B.Octets.to_list(a), _))) == SH.CrSha2.sha256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %BL.octets_append_list(a, B.Octets.append(b, c)) : {B.Octets.of_list(Hc.sha256(_)) == SH.CrSha2.sha256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  {==}

def Laws.sha256_hash_length(o):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Hc.sha256(B.Octets.to_list(o)))), B.len(Hc.sha256(B.Octets.to_list(o))), Bits.octets_len_of(Hc.sha256(B.Octets.to_list(o)))) : {_ == 32n : Nat}
  HL.Sha256.length(B.Octets.to_list(o))

def Laws.sha512_spec(o):
  %HL.Sha512.value(B.Octets.to_list(o)) : {SH.CrSha2.sha512(o) == B.Octets.of_list(_) : B.Octets}
  {==}

def Laws.sha512_hash_split(a, b):
  %Equal.sym(List<&2, U32>, Hc.digest(Hc.update(Hc.update(Hc.new_sha512(), B.Octets.to_list(a)), B.Octets.to_list(b))), Hc.sha512(List.append(&2, U32, B.Octets.to_list(a), B.Octets.to_list(b))), HL.Split.sha512(B.Octets.to_list(a), B.Octets.to_list(b))) : {B.Octets.of_list(_) == SH.CrSha2.sha512(B.Octets.append(a, b)) : B.Octets}
  %BL.octets_append_list(a, b) : {B.Octets.of_list(Hc.sha512(_)) == SH.CrSha2.sha512(B.Octets.append(a, b)) : B.Octets}
  {==}

def Laws.sha512_hash_split3(a, b, c):
  %Equal.sym(List<&2, U32>, Hc.digest(Hc.update(Hc.update(Hc.update(Hc.new_sha512(), B.Octets.to_list(a)), B.Octets.to_list(b)), B.Octets.to_list(c))), Hc.sha512(List.concat(&2, U32, [B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c)])), HL.Incremental.sha512([B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c)])) : {B.Octets.of_list(_) == SH.CrSha2.sha512(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %Bits.append_nil(B.Octets.to_list(c)) : {B.Octets.of_list(Hc.sha512(List.append(&2, U32, B.Octets.to_list(a), List.append(&2, U32, B.Octets.to_list(b), _)))) == SH.CrSha2.sha512(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %BL.octets_append_list(b, c) : {B.Octets.of_list(Hc.sha512(List.append(&2, U32, B.Octets.to_list(a), _))) == SH.CrSha2.sha512(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %BL.octets_append_list(a, B.Octets.append(b, c)) : {B.Octets.of_list(Hc.sha512(_)) == SH.CrSha2.sha512(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  {==}

def Laws.sha512_hash_length(o):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Hc.sha512(B.Octets.to_list(o)))), B.len(Hc.sha512(B.Octets.to_list(o))), Bits.octets_len_of(Hc.sha512(B.Octets.to_list(o)))) : {_ == 64n : Nat}
  HL.Sha512.length(B.Octets.to_list(o))

def Laws.sha3_256_spec(o):
  %HL.Sha3_256.value(B.Octets.to_list(o)) : {S3.CrSha3.sha3_256(o) == B.Octets.of_list(_) : B.Octets}
  {==}

def Laws.sha3_256_hash_split(a, b):
  %Equal.sym(List<&2, U32>, Hc.digest(Hc.update(Hc.update(Hc.new_sha3_256(), B.Octets.to_list(a)), B.Octets.to_list(b))), Hc.sha3_256(List.append(&2, U32, B.Octets.to_list(a), B.Octets.to_list(b))), HL.Split.sha3_256(B.Octets.to_list(a), B.Octets.to_list(b))) : {B.Octets.of_list(_) == S3.CrSha3.sha3_256(B.Octets.append(a, b)) : B.Octets}
  %BL.octets_append_list(a, b) : {B.Octets.of_list(Hc.sha3_256(_)) == S3.CrSha3.sha3_256(B.Octets.append(a, b)) : B.Octets}
  {==}

def Laws.sha3_256_hash_split3(a, b, c):
  %Equal.sym(List<&2, U32>, Hc.digest(Hc.update(Hc.update(Hc.update(Hc.new_sha3_256(), B.Octets.to_list(a)), B.Octets.to_list(b)), B.Octets.to_list(c))), Hc.sha3_256(List.concat(&2, U32, [B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c)])), HL.Incremental.sha3_256([B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c)])) : {B.Octets.of_list(_) == S3.CrSha3.sha3_256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %Bits.append_nil(B.Octets.to_list(c)) : {B.Octets.of_list(Hc.sha3_256(List.append(&2, U32, B.Octets.to_list(a), List.append(&2, U32, B.Octets.to_list(b), _)))) == S3.CrSha3.sha3_256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %BL.octets_append_list(b, c) : {B.Octets.of_list(Hc.sha3_256(List.append(&2, U32, B.Octets.to_list(a), _))) == S3.CrSha3.sha3_256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  %BL.octets_append_list(a, B.Octets.append(b, c)) : {B.Octets.of_list(Hc.sha3_256(_)) == S3.CrSha3.sha3_256(B.Octets.append(a, B.Octets.append(b, c))) : B.Octets}
  {==}

def Laws.sha3_256_hash_length(o):
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(Hc.sha3_256(B.Octets.to_list(o)))), B.len(Hc.sha3_256(B.Octets.to_list(o))), Bits.octets_len_of(Hc.sha3_256(B.Octets.to_list(o)))) : {_ == 32n : Nat}
  HL.Sha3_256.length(B.Octets.to_list(o))

# Vectors and a refusal, by computation

def Laws.hkdf_sha256_too_long():
  {==}

def Laws.sha256_abc():
  {==}

def Laws.sha3_256_abc():
  {==}

def Laws.hmac_sha256_rfc4231_2():
  {==}

def Laws.pbkdf2_hmac_sha256_rfc7914_1():
  {==}

def Laws.kbkdf_hmac_sha256_vector():
  {==}

# Per-instance proofs (gen/instances.py)

# BEGIN GENERATED by gen/instances.py: proofs
def Laws.hmac_sha256_split(kk, a, b):
  match kk:
    case Hm.CrHmacKey{+i, +o}:
      %Equal.sym(B.Octets, SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init256(), i), a), b)), SH.CrSha2.sha256(B.Octets.append(i, B.Octets.append(a, b))), Laws.sha256_hash_split3(i, a, b)) : {SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init256(), o), _)) == SH.CrSha2.sha256(B.Octets.append(o, SH.CrSha2.sha256(B.Octets.append(i, B.Octets.append(a, b))))) : B.Octets}
      %Equal.sym(B.Octets, SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init256(), o), SH.CrSha2.sha256(B.Octets.append(i, B.Octets.append(a, b))))), SH.CrSha2.sha256(B.Octets.append(o, SH.CrSha2.sha256(B.Octets.append(i, B.Octets.append(a, b))))), Laws.sha256_hash_split(o, SH.CrSha2.sha256(B.Octets.append(i, B.Octets.append(a, b))))) : {_ == SH.CrSha2.sha256(B.Octets.append(o, SH.CrSha2.sha256(B.Octets.append(i, B.Octets.append(a, b))))) : B.Octets}
      {==}

def Laws.hmac_sha512_split(kk, a, b):
  match kk:
    case Hm.CrHmacKey{+i, +o}:
      %Equal.sym(B.Octets, SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init512(), i), a), b)), SH.CrSha2.sha512(B.Octets.append(i, B.Octets.append(a, b))), Laws.sha512_hash_split3(i, a, b)) : {SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init512(), o), _)) == SH.CrSha2.sha512(B.Octets.append(o, SH.CrSha2.sha512(B.Octets.append(i, B.Octets.append(a, b))))) : B.Octets}
      %Equal.sym(B.Octets, SH.CrSha2.final(SH.CrSha2.update(SH.CrSha2.update(SH.CrSha2.init512(), o), SH.CrSha2.sha512(B.Octets.append(i, B.Octets.append(a, b))))), SH.CrSha2.sha512(B.Octets.append(o, SH.CrSha2.sha512(B.Octets.append(i, B.Octets.append(a, b))))), Laws.sha512_hash_split(o, SH.CrSha2.sha512(B.Octets.append(i, B.Octets.append(a, b))))) : {_ == SH.CrSha2.sha512(B.Octets.append(o, SH.CrSha2.sha512(B.Octets.append(i, B.Octets.append(a, b))))) : B.Octets}
      {==}

def Laws.hmac_sha3_256_split(kk, a, b):
  match kk:
    case Hm.CrHmacKey{+i, +o}:
      %Equal.sym(B.Octets, S3.CrSha3.final(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.init(), i), a), b)), S3.CrSha3.sha3_256(B.Octets.append(i, B.Octets.append(a, b))), Laws.sha3_256_hash_split3(i, a, b)) : {S3.CrSha3.final(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.init(), o), _)) == S3.CrSha3.sha3_256(B.Octets.append(o, S3.CrSha3.sha3_256(B.Octets.append(i, B.Octets.append(a, b))))) : B.Octets}
      %Equal.sym(B.Octets, S3.CrSha3.final(S3.CrSha3.update(S3.CrSha3.update(S3.CrSha3.init(), o), S3.CrSha3.sha3_256(B.Octets.append(i, B.Octets.append(a, b))))), S3.CrSha3.sha3_256(B.Octets.append(o, S3.CrSha3.sha3_256(B.Octets.append(i, B.Octets.append(a, b))))), Laws.sha3_256_hash_split(o, S3.CrSha3.sha3_256(B.Octets.append(i, B.Octets.append(a, b))))) : {_ == S3.CrSha3.sha3_256(B.Octets.append(o, S3.CrSha3.sha3_256(B.Octets.append(i, B.Octets.append(a, b))))) : B.Octets}
      {==}
# END GENERATED: proofs
