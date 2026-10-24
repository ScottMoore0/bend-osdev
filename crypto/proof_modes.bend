# Proof helpers for crypto: the loops of ECB, CBC (modes.bend), PCBC
# (pcbc.bend) and LRW (lrw.bend) that run are their structural forms, for
# every block cipher. The per-instance round trips (PROOF_cm.bend,
# PROOF_lc.bend) rest on them.
import Base
import ../bytes/bytes.bend as B
import ./modes.bend as Md
import ./pcbc.bend as Pc
import ./lrw.bend as Lw
import ../gf/gf128.bend as G

# ECB and CBC: the loops that run are the structural forms (for every block
# cipher; the round trips, which need the cipher's own law, are per instance)

def ecb_tr(~K: Data, ~Blk: Data, ~f: K -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +acc: List<&2, Blk>) -> {Md.cr.ecb.go(~K, ~Blk, ~f, k, bs, acc) == Md.cr.blks.rev_onto(~Blk, acc, Md.cr.ecb(~K, ~Blk, ~f, k, bs)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{b, t}:
      ecb_tr(~K, ~Blk, ~f, k, t, Con{f(k, b), acc})

def ecb_pub(~K: Data, ~Blk: Data, ~f: K -> Blk -> Blk, +k: K, bs: List<&2, Blk>) -> {Md.cr.ecb.go(~K, ~Blk, ~f, k, bs, Nil{}) == Md.cr.ecb(~K, ~Blk, ~f, k, bs) : List<&2, Blk>}:
  ecb_tr(~K, ~Blk, ~f, k, bs, Nil{})

def cbc_enc_tr(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +iv: Blk, +acc: List<&2, Blk>) -> {Md.cr.cbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, bs, iv, acc) == Md.cr.blks.rev_onto(~Blk, acc, Md.cr.cbc.enc(~K, ~Blk, ~enc, ~bxor, k, bs, iv)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, t}:
      cbc_enc_tr(~K, ~Blk, ~enc, ~bxor, k, t, enc(k, bxor(p, iv)), Con{enc(k, bxor(p, iv)), acc})

def cbc_dec_tr(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +iv: Blk, +acc: List<&2, Blk>) -> {Md.cr.cbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, bs, iv, acc) == Md.cr.blks.rev_onto(~Blk, acc, Md.cr.cbc.dec(~K, ~Blk, ~dec, ~bxor, k, bs, iv)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, t}:
      cbc_dec_tr(~K, ~Blk, ~dec, ~bxor, k, t, c, Con{bxor(dec(k, c), iv), acc})

def cbc_enc_pub(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +iv: Blk) -> {Md.cr.cbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, bs, iv, Nil{}) == Md.cr.cbc.enc(~K, ~Blk, ~enc, ~bxor, k, bs, iv) : List<&2, Blk>}:
  cbc_enc_tr(~K, ~Blk, ~enc, ~bxor, k, bs, iv, Nil{})

def cbc_dec_pub(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +iv: Blk) -> {Md.cr.cbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, bs, iv, Nil{}) == Md.cr.cbc.dec(~K, ~Blk, ~dec, ~bxor, k, bs, iv) : List<&2, Blk>}:
  cbc_dec_tr(~K, ~Blk, ~dec, ~bxor, k, bs, iv, Nil{})

# PCBC (pcbc.bend): the loops that run are the structural forms

def pcbc_enc_tr(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +v: Blk, +acc: List<&2, Blk>) -> {Pc.cr.pcbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, bs, v, acc) == Md.cr.blks.rev_onto(~Blk, acc, Pc.cr.pcbc.enc(~K, ~Blk, ~enc, ~bxor, k, bs, v)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, t}:
      pcbc_enc_tr(~K, ~Blk, ~enc, ~bxor, k, t, bxor(p, enc(k, bxor(p, v))), Con{enc(k, bxor(p, v)), acc})

def pcbc_dec_tr(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +v: Blk, +acc: List<&2, Blk>) -> {Pc.cr.pcbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, bs, v, acc) == Md.cr.blks.rev_onto(~Blk, acc, Pc.cr.pcbc.dec(~K, ~Blk, ~dec, ~bxor, k, bs, v)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, t}:
      pcbc_dec_tr(~K, ~Blk, ~dec, ~bxor, k, t, bxor(bxor(dec(k, c), v), c), Con{bxor(dec(k, c), v), acc})

def pcbc_enc_pub(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +v: Blk) -> {Pc.cr.pcbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, bs, v, Nil{}) == Pc.cr.pcbc.enc(~K, ~Blk, ~enc, ~bxor, k, bs, v) : List<&2, Blk>}:
  pcbc_enc_tr(~K, ~Blk, ~enc, ~bxor, k, bs, v, Nil{})

def pcbc_dec_pub(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, +v: Blk) -> {Pc.cr.pcbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, bs, v, Nil{}) == Pc.cr.pcbc.dec(~K, ~Blk, ~dec, ~bxor, k, bs, v) : List<&2, Blk>}:
  pcbc_dec_tr(~K, ~Blk, ~dec, ~bxor, k, bs, v, Nil{})

# LRW (lrw.bend): the loops that run are the structural forms

def lrw_enc_tr(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128, +acc: List<&2, Blk>) -> {Lw.cr.lrw.enc.go(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, bs, i, acc) == Md.cr.blks.rev_onto(~Blk, acc, Lw.cr.lrw.enc(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, bs, i)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{p, t}:
      lrw_enc_tr(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, t, Lw.cr.lrw.inc(i), Con{Lw.cr.lrw.benc(~K, ~Blk, ~enc, ~bxor, k, Lw.cr.lrw.tweak(~Blk, ~blk_of, k2, i), p), acc})

def lrw_dec_tr(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128, +acc: List<&2, Blk>) -> {Lw.cr.lrw.dec.go(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, bs, i, acc) == Md.cr.blks.rev_onto(~Blk, acc, Lw.cr.lrw.dec(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, bs, i)) : List<&2, Blk>}:
  match bs:
    case Nil{}:
      {==}
    case Con{c, t}:
      lrw_dec_tr(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, t, Lw.cr.lrw.inc(i), Con{Lw.cr.lrw.bdec(~K, ~Blk, ~dec, ~bxor, k, Lw.cr.lrw.tweak(~Blk, ~blk_of, k2, i), c), acc})

def lrw_enc_pub(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128) -> {Lw.cr.lrw.enc.go(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, bs, i, Nil{}) == Lw.cr.lrw.enc(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, bs, i) : List<&2, Blk>}:
  lrw_enc_tr(~K, ~Blk, ~enc, ~bxor, ~blk_of, k, k2, bs, i, Nil{})

def lrw_dec_pub(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, +k: K, +k2: G.Gf128, bs: List<&2, Blk>, +i: G.Gf128) -> {Lw.cr.lrw.dec.go(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, bs, i, Nil{}) == Lw.cr.lrw.dec(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, bs, i) : List<&2, Blk>}:
  lrw_dec_tr(~K, ~Blk, ~dec, ~bxor, ~blk_of, k, k2, bs, i, Nil{})
