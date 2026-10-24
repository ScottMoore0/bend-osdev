# Proofs of LAWS.bend, written by gen/instances.py: each c_dec_enc by
# induction on the list, with the cipher's own round-trip law (legacy-ciphers'
# LAWS.bend, or cipher-modes' aes_round_trip) at every block; each mode law is
# cipher-modes' law at the cipher's template arguments, with c_dec_enc as its
# hypothesis.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ../cipher-modes/xts.bend as XT
import ../cipher-modes/LAWS.bend as CML
import ../cipher-modes/PROOF.bend as CMP
import ../legacy-ciphers/sm4.bend as S
import ../legacy-ciphers/camellia.bend as Ca
import ../legacy-ciphers/serpent.bend as Sp
import ../legacy-ciphers/twofish.bend as Tf
import ../legacy-ciphers/aria.bend as Ar
import ../legacy-ciphers/cast6.bend as C6
import ../cipher-modes/aes.bend as X
import ../legacy-ciphers/LAWS.bend as LL
import ../legacy-ciphers/PROOF.bend as LP
import ./LAWS.bend as Laws

# SM4 (legacy-ciphers)

def Laws.sm4_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, S.LcSm4.decrypt(k, S.LcSm4.encrypt(k, x)), x, LL.sm4_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, t), t, Laws.sm4_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.sm4_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, xs => Laws.sm4_dec_enc(k, xs), iv, bs)

def Laws.sm4_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, xs => Laws.sm4_dec_enc(k, xs), iv, m, hi, hm)

def Laws.sm4_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k1, xs => Laws.sm4_dec_enc(k1, xs), t, bs)

def Laws.sm4_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k1, k2, xs => Laws.sm4_dec_enc(k1, xs), i, p, hi, hp)

# Camellia (legacy-ciphers)

def Laws.camellia_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Ca.LcCamellia.decrypt(k, Ca.LcCamellia.encrypt(k, x)), x, LL.camellia_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, t), t, Laws.camellia_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.camellia_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, xs => Laws.camellia_dec_enc(k, xs), iv, bs)

def Laws.camellia_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, xs => Laws.camellia_dec_enc(k, xs), iv, m, hi, hm)

def Laws.camellia_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k1, xs => Laws.camellia_dec_enc(k1, xs), t, bs)

def Laws.camellia_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k1, k2, xs => Laws.camellia_dec_enc(k1, xs), i, p, hi, hp)

# Serpent (legacy-ciphers)

def Laws.serpent_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Sp.LcSerpent.decrypt(k, Sp.LcSerpent.encrypt(k, x)), x, LL.serpent_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, t), t, Laws.serpent_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.serpent_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, xs => Laws.serpent_dec_enc(k, xs), iv, bs)

def Laws.serpent_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, xs => Laws.serpent_dec_enc(k, xs), iv, m, hi, hm)

def Laws.serpent_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k1, xs => Laws.serpent_dec_enc(k1, xs), t, bs)

def Laws.serpent_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k1, k2, xs => Laws.serpent_dec_enc(k1, xs), i, p, hi, hp)

# Twofish (legacy-ciphers)

def Laws.twofish_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Tf.LcTwofish.decrypt(k, Tf.LcTwofish.encrypt(k, x)), x, LL.twofish_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, t), t, Laws.twofish_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.twofish_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, xs => Laws.twofish_dec_enc(k, xs), iv, bs)

def Laws.twofish_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, xs => Laws.twofish_dec_enc(k, xs), iv, m, hi, hm)

def Laws.twofish_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k1, xs => Laws.twofish_dec_enc(k1, xs), t, bs)

def Laws.twofish_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k1, k2, xs => Laws.twofish_dec_enc(k1, xs), i, p, hi, hp)

# ARIA (legacy-ciphers)

def Laws.aria_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Ar.LcAria.decrypt(k, Ar.LcAria.encrypt(k, x)), x, LL.aria_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, t), t, Laws.aria_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.aria_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, xs => Laws.aria_dec_enc(k, xs), iv, bs)

def Laws.aria_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, xs => Laws.aria_dec_enc(k, xs), iv, m, hi, hm)

def Laws.aria_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k1, xs => Laws.aria_dec_enc(k1, xs), t, bs)

def Laws.aria_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k1, k2, xs => Laws.aria_dec_enc(k1, xs), i, p, hi, hp)

# CAST-256 (legacy-ciphers)

def Laws.cast6_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, C6.LcCast6.decrypt(k, C6.LcCast6.encrypt(k, x)), x, LL.cast6_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, t), t, Laws.cast6_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.cast6_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, xs => Laws.cast6_dec_enc(k, xs), iv, bs)

def Laws.cast6_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, xs => Laws.cast6_dec_enc(k, xs), iv, m, hi, hm)

def Laws.cast6_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k1, xs => Laws.cast6_dec_enc(k1, xs), t, bs)

def Laws.cast6_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k1, k2, xs => Laws.cast6_dec_enc(k1, xs), i, p, hi, hp)

# AES-128, AES-192 and AES-256 (cipher-modes)

def Laws.aes_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, X.CmAes.decrypt(k, X.CmAes.encrypt(k, x)), x, CML.aes_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, t), t, Laws.aes_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.aes_cbc_blocks_round_trip(k, iv, bs):
  CML.cbc_blocks_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, xs => Laws.aes_dec_enc(k, xs), iv, bs)

def Laws.aes_cbc_round_trip(k, iv, m, hi, hm):
  CML.cbc_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, xs => Laws.aes_dec_enc(k, xs), iv, m, hi, hm)

def Laws.aes_xts_blocks_round_trip(k1, t, bs):
  CML.xts_blocks_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k1, xs => Laws.aes_dec_enc(k1, xs), t, bs)

def Laws.aes_xts_round_trip(k1, k2, i, p, hi, hp):
  CML.xts_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k1, k2, xs => Laws.aes_dec_enc(k1, xs), i, p, hi, hp)
