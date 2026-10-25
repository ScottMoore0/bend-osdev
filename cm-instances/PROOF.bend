# Proofs of LAWS.bend, written by gen/instances.py: each c_dec_enc by
# induction on the list, with the cipher's own round-trip law (its package's
# LAWS.bend: aes_round_trip for AES) at every block; each mode law is
# cbc's or xts' law at the cipher's template arguments, with c_dec_enc as its
# hypothesis.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../cbc/cbc.bend as CB
import ../xts/xts.bend as XT
import ../cbc/LAWS.bend as CbcL
import ../cbc/PROOF.bend as CbcP
import ../xts/LAWS.bend as XtsL
import ../xts/PROOF.bend as XtsP
import ../sm4/sm4.bend as S
import ../camellia/camellia.bend as Ca
import ../serpent/serpent.bend as Sp
import ../twofish/twofish.bend as Tf
import ../aria/aria.bend as Ar
import ../cast6/cast6.bend as C6
import ../aes/aes.bend as X
import ../sm4/LAWS.bend as Sm4L
import ../sm4/PROOF.bend as Sm4P
import ../camellia/LAWS.bend as CamL
import ../camellia/PROOF.bend as CamP
import ../serpent/LAWS.bend as SerpL
import ../serpent/PROOF.bend as SerpP
import ../twofish/LAWS.bend as TwofL
import ../twofish/PROOF.bend as TwofP
import ../aria/LAWS.bend as AriaL
import ../aria/PROOF.bend as AriaP
import ../cast6/LAWS.bend as Cast6L
import ../cast6/PROOF.bend as Cast6P
import ../aes/LAWS.bend as AesL
import ../aes/PROOF.bend as AesP
import ./LAWS.bend as Laws

# SM4 (the sm4 package)

def Laws.sm4_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, S.LcSm4.decrypt(k, S.LcSm4.encrypt(k, x)), x, Sm4L.sm4_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, t), t, Laws.sm4_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.sm4_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, xs => Laws.sm4_dec_enc(k, xs), iv, bs)

def Laws.sm4_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k, xs => Laws.sm4_dec_enc(k, xs), iv, m, hi, hm)

def Laws.sm4_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k1, xs => Laws.sm4_dec_enc(k1, xs), t, bs)

def Laws.sm4_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, k1, k2, xs => Laws.sm4_dec_enc(k1, xs), i, p, hi, hp)

# Camellia (the camellia package)

def Laws.camellia_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Ca.LcCamellia.decrypt(k, Ca.LcCamellia.encrypt(k, x)), x, CamL.camellia_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, t), t, Laws.camellia_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.camellia_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, xs => Laws.camellia_dec_enc(k, xs), iv, bs)

def Laws.camellia_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k, xs => Laws.camellia_dec_enc(k, xs), iv, m, hi, hm)

def Laws.camellia_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k1, xs => Laws.camellia_dec_enc(k1, xs), t, bs)

def Laws.camellia_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, k1, k2, xs => Laws.camellia_dec_enc(k1, xs), i, p, hi, hp)

# Serpent (the serpent package)

def Laws.serpent_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Sp.LcSerpent.decrypt(k, Sp.LcSerpent.encrypt(k, x)), x, SerpL.serpent_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, t), t, Laws.serpent_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.serpent_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, xs => Laws.serpent_dec_enc(k, xs), iv, bs)

def Laws.serpent_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k, xs => Laws.serpent_dec_enc(k, xs), iv, m, hi, hm)

def Laws.serpent_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k1, xs => Laws.serpent_dec_enc(k1, xs), t, bs)

def Laws.serpent_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, k1, k2, xs => Laws.serpent_dec_enc(k1, xs), i, p, hi, hp)

# Twofish (the twofish package)

def Laws.twofish_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Tf.LcTwofish.decrypt(k, Tf.LcTwofish.encrypt(k, x)), x, TwofL.twofish_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, t), t, Laws.twofish_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.twofish_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, xs => Laws.twofish_dec_enc(k, xs), iv, bs)

def Laws.twofish_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k, xs => Laws.twofish_dec_enc(k, xs), iv, m, hi, hm)

def Laws.twofish_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k1, xs => Laws.twofish_dec_enc(k1, xs), t, bs)

def Laws.twofish_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, k1, k2, xs => Laws.twofish_dec_enc(k1, xs), i, p, hi, hp)

# ARIA (the aria package)

def Laws.aria_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, Ar.LcAria.decrypt(k, Ar.LcAria.encrypt(k, x)), x, AriaL.aria_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, t), t, Laws.aria_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.aria_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, xs => Laws.aria_dec_enc(k, xs), iv, bs)

def Laws.aria_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k, xs => Laws.aria_dec_enc(k, xs), iv, m, hi, hm)

def Laws.aria_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k1, xs => Laws.aria_dec_enc(k1, xs), t, bs)

def Laws.aria_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, k1, k2, xs => Laws.aria_dec_enc(k1, xs), i, p, hi, hp)

# CAST-256 (the cast6 package)

def Laws.cast6_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, C6.LcCast6.decrypt(k, C6.LcCast6.encrypt(k, x)), x, Cast6L.cast6_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, t), t, Laws.cast6_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.cast6_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, xs => Laws.cast6_dec_enc(k, xs), iv, bs)

def Laws.cast6_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k, xs => Laws.cast6_dec_enc(k, xs), iv, m, hi, hm)

def Laws.cast6_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k1, xs => Laws.cast6_dec_enc(k1, xs), t, bs)

def Laws.cast6_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, k1, k2, xs => Laws.cast6_dec_enc(k1, xs), i, p, hi, hp)

# AES-128, AES-192 and AES-256 (the aes package)

def Laws.aes_dec_enc(k, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(M.CmBlock, X.CmAes.decrypt(k, X.CmAes.encrypt(k, x)), x, AesL.aes_round_trip(k, x)) : {Con{_, M.CmBlock.dec_enc(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, t)} == Con{x, t} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, t), t, Laws.aes_dec_enc(k, t)) : {Con{x, _} == Con{x, t} : List<&2, M.CmBlock>}
      {==}

def Laws.aes_cbc_blocks_round_trip(k, iv, bs):
  CbcL.cbc_blocks_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, xs => Laws.aes_dec_enc(k, xs), iv, bs)

def Laws.aes_cbc_round_trip(k, iv, m, hi, hm):
  CbcL.cbc_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k, xs => Laws.aes_dec_enc(k, xs), iv, m, hi, hm)

def Laws.aes_xts_blocks_round_trip(k1, t, bs):
  XtsL.xts_blocks_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k1, xs => Laws.aes_dec_enc(k1, xs), t, bs)

def Laws.aes_xts_round_trip(k1, k2, i, p, hi, hp):
  XtsL.xts_round_trip(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, k1, k2, xs => Laws.aes_dec_enc(k1, xs), i, p, hi, hp)
