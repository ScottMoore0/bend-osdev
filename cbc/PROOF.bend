# Proofs of LAWS.bend (CBC). The byte layer's lemmas the modes share
# (splitting bytes into blocks and joining them back, masks, the tail-call
# forms) are mode-core's laws, used under the names below.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../mode-core/mode-core.bend as M
import ./cbc.bend as C
import ../mode-core/LAWS.bend as CoreL
import ../mode-core/PROOF.bend as CoreP
import ./LAWS.bend as Laws

# mode-core's laws, under the names these proofs use

def sp.cons_tail(b: M.CmBlock, s: M.CmSplit) -> {M.cm.split.tail(M.cm.split.cons(b, s)) == M.cm.split.tail(s) : List<&2, U32>}:
  CoreL.split_cons_tail(b, s)

def sp.eta(s: M.CmSplit) -> {M.CmSplit{M.cm.split.blocks(s), M.cm.split.tail(s)} == s : M.CmSplit}:
  CoreL.split_eta(s)

def sp.blk(b: M.CmBlock, rest: List<&2, U32>) -> {M.cm.split(M.cm.bytes_onto(b, rest)) == M.cm.split.cons(b, M.cm.split(rest)) : M.CmSplit}:
  CoreL.split_bytes_onto(b, rest)

def sp.mask_blk(b: M.CmBlock, rest: List<&2, U32>) -> {B.mask(M.cm.bytes_onto(b, rest)) == M.cm.bytes_onto(b, B.mask(rest)) : List<&2, U32>}:
  CoreL.mask_bytes_onto(b, rest)

def sp.join_split(ys: List<&2, U32>) -> {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), M.cm.split.tail(M.cm.split(B.mask(ys)))) == B.mask(ys) : List<&2, U32>}:
  CoreL.join_split(ys)

def oc.masked(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  CoreL.octets_masked(o)

def oc.len(+o: B.Octets, +n: Nat, h: {B.Octets.len(o) == n : Nat}) -> {B.len(B.Octets.to_list(o)) == n : Nat}:
  CoreL.octets_len(o, n, h)

def tr.split_eq(+xs: List<&2, U32>) -> {M.cm.split(xs) == M.cm.split.fast(xs) : M.CmSplit}:
  CoreL.split_fast(xs)

def tr.join_eq(+bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.join_onto(bs, rest) == M.cm.join_onto.fast(bs, rest) : List<&2, U32>}:
  CoreL.join_onto_fast(bs, rest)

def tr.bind_cong(r: Result<&2, &2, M.CmError, B.Octets>, f: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, g: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, h: @c: B.Octets -> {f(c) == g(c) : Result<&2, &2, M.CmError, B.Octets>}) -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, f) == Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, g) : Result<&2, &2, M.CmError, B.Octets>}:
  CoreL.bind_cong(r, f, g, h)

def cmp.hd(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +x: M.CmBlock, +xs: List<&2, M.CmBlock>, +h: {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, Con{x, xs}) == Con{x, xs} : List<&2, M.CmBlock>}) -> {dec(k, enc(k, x)) == x : M.CmBlock}:
  CoreL.dec_enc_head(~K, ~enc, ~dec, k, x, xs, h)

def cmp.tl(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +x: M.CmBlock, +xs: List<&2, M.CmBlock>, +h: {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, Con{x, xs}) == Con{x, xs} : List<&2, M.CmBlock>}) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}:
  CoreL.dec_enc_tail(~K, ~enc, ~dec, k, x, xs, h)

# XOR

def bx.bool(a: Bool, b: Bool) -> {Bool.xor(a, Bool.xor(a, b)) == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def bx.word(n: Nat, a: Word(n), b: Word(n)) -> {Word.xor(n, a, Word.xor(n, a, b)) == b : Word(n)}:
  match n:
    case 0n:
      match b:
        case WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %bx.bool(ah, bh) : {WCon{Bool.xor(ah, Bool.xor(ah, bh)), Word.xor(p, at, Word.xor(p, at, bt))} == WCon{_, bt} : Word(1n+p)}
          %bx.word(p, at, bt) : {WCon{Bool.xor(ah, Bool.xor(ah, bh)), Word.xor(p, at, Word.xor(p, at, bt))} == WCon{Bool.xor(ah, Bool.xor(ah, bh)), _} : Word(1n+p)}
          {==}

def bx.u32(a: U32, b: U32) -> {U32.xor(a, U32.xor(a, b)) == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %bx.word(32n, x, y) : {U32{Word.xor(32n, x, Word.xor(32n, x, y))} == U32{_} : U32}
      {==}

# xor(a, xor(a, b)) == b on blocks
def bx.block(+a: M.CmBlock, +b: M.CmBlock) -> {M.CmBlock.xor(a, M.CmBlock.xor(a, b)) == b : M.CmBlock}:
  match a b:
    case M.CmBlock{a0, a1, a2, a3} M.CmBlock{b0, b1, b2, b3}:
      %bx.u32(a0, b0) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{_, b1, b2, b3} : M.CmBlock}
      %bx.u32(a1, b1) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{U32.xor(a0, U32.xor(a0, b0)), _, b2, b3} : M.CmBlock}
      %bx.u32(a2, b2) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{U32.xor(a0, U32.xor(a0, b0)), U32.xor(a1, U32.xor(a1, b1)), _, b3} : M.CmBlock}
      %bx.u32(a3, b3) : {M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock.xor(M.CmBlock{a0, a1, a2, a3}, M.CmBlock{b0, b1, b2, b3})) == M.CmBlock{U32.xor(a0, U32.xor(a0, b0)), U32.xor(a1, U32.xor(a1, b1)), U32.xor(a2, U32.xor(a2, b2)), _} : M.CmBlock}
      {==}

# Arithmetic: n + 16 and n leave the same remainder mod 16

def sp.disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def sp.absurd(p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : sp.disc(_)
  Unit{}

def sp.absurd_tail(p: Nat, xs: List<&2, U32>, h: {1n+p == 0n : Nat}) -> {M.cm.split.tail(M.cm.split(B.mask(xs))) == Nil{} : List<&2, U32>}:
  Empty.absurd({M.cm.split.tail(M.cm.split(B.mask(xs))) == Nil{} : List<&2, U32>}, sp.absurd(p, h))

def sp.snd_go(n: Nat, m: Nat, d1: Nat, d2: Nat, r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d1, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d2, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          sp.snd_go(np, r, 1n+d1, 1n+d2, 0n)
        case 1n+mp:
          sp.snd_go(np, mp, d1, d2, 1n+r)

def sp.mod16(n: Nat) -> {Nat.mod(Nat.add(16n, n), 16n) == Nat.mod(n, 16n) : Nat}:
  sp.snd_go(n, 15n, 1n, 0n, 0n)

# a list of whole blocks splits with no tail
def sp.mod_tail(ys: List<&2, U32>) -> {Nat.mod(B.len(ys), 16n) == 0n : Nat} -> {M.cm.split.tail(M.cm.split(B.mask(ys))) == Nil{} : List<&2, U32>}:
  match ys:
    case Nil{}:
      h => {==}
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => sp.absurd_tail(0n, Con{y0, Nil{}}, h)
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => sp.absurd_tail(1n, Con{y0, Con{y1, Nil{}}}, h)
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => sp.absurd_tail(2n, Con{y0, Con{y1, Con{y2, Nil{}}}}, h)
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => sp.absurd_tail(3n, Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}, h)
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => sp.absurd_tail(4n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}, h)
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => sp.absurd_tail(5n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}, h)
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => sp.absurd_tail(6n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}, h)
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => sp.absurd_tail(7n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}, h)
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => sp.absurd_tail(8n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}, h)
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => sp.absurd_tail(9n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}, h)
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => sp.absurd_tail(10n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}, h)
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => sp.absurd_tail(11n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}, h)
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => sp.absurd_tail(12n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}, h)
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => sp.absurd_tail(13n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}, h)
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => sp.absurd_tail(14n, Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}, h)
                                                                case Con{+y15, +t}:
                                                                  h => %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), M.cm.split.tail(M.cm.split(B.mask(t))), sp.cons_tail(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {_ == Nil{} : List<&2, U32>}
                                                                    sp.mod_tail(t)(Equal.trans(Nat, Nat.mod(B.len(t), 16n), Nat.mod(Nat.add(16n, B.len(t)), 16n), 0n, Equal.sym(Nat, Nat.mod(Nat.add(16n, B.len(t)), 16n), Nat.mod(B.len(t), 16n), sp.mod16(B.len(t))), h))

# Joining and splitting

def sp.split_join(bs: List<&2, M.CmBlock>) -> {M.cm.split(M.cm.join_onto(bs, Nil{})) == M.CmSplit{bs, Nil{}} : M.CmSplit}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(M.CmSplit, M.cm.split(M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{}))), M.cm.split.cons(b, M.cm.split(M.cm.join_onto(t, Nil{}))), sp.blk(b, M.cm.join_onto(t, Nil{}))) : {_ == M.CmSplit{Con{b, t}, Nil{}} : M.CmSplit}
      %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(t, Nil{})), M.CmSplit{t, Nil{}}, sp.split_join(t)) : {M.cm.split.cons(b, _) == M.CmSplit{Con{b, t}, Nil{}} : M.CmSplit}
      {==}

def sp.mask_join(bs: List<&2, M.CmBlock>) -> {B.mask(M.cm.join_onto(bs, Nil{})) == M.cm.join_onto(bs, Nil{}) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{}))), M.cm.bytes_onto(b, B.mask(M.cm.join_onto(t, Nil{}))), sp.mask_blk(b, M.cm.join_onto(t, Nil{}))) : {_ == M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{})) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(t, Nil{})), M.cm.join_onto(t, Nil{}), sp.mask_join(t)) : {M.cm.bytes_onto(b, _) == M.cm.bytes_onto(b, M.cm.join_onto(t, Nil{})) : List<&2, U32>}
      {==}

def oc.mod(+o: B.Octets, h: {Nat.mod(B.Octets.len(o), 16n) == 0n : Nat}) -> {Nat.mod(B.len(B.Octets.to_list(o)), 16n) == 0n : Nat}:
  Equal.trans(Nat, Nat.mod(B.len(B.Octets.to_list(o)), 16n), Nat.mod(B.Octets.len(o), 16n), 0n, Equal.sym(Nat, Nat.mod(B.Octets.len(o), 16n), Nat.mod(B.len(B.Octets.to_list(o)), 16n), Equal.cong(Nat, Nat, n => Nat.mod(n, 16n), B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o))), h)

# a 16-byte IV is the block of its bytes
def cbcp.iv(+iv: B.Octets, h: {B.Octets.len(iv) == 16n : Nat}) -> {C.cbc.iv(iv) == Done{M.cm.block_of(B.Octets.to_list(iv))} : Result<&2, &2, M.CmError, M.CmBlock>}:
  %Equal.sym(Nat, B.len(B.Octets.to_list(iv)), 16n, oc.len(iv, 16n, h)) : {M.cm.need_block.pick(Nat.is_eq(_, 16n), B.Octets.to_list(iv), M.CmBadIvLength{B.len(B.Octets.to_list(iv))}) == Done{M.cm.block_of(B.Octets.to_list(iv))} : Result<&2, &2, M.CmError, M.CmBlock>}
  {==}

# The modes on blocks

def tr.cbc_enc_go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {C.cbc.enc.go(~K, ~enc, k, bs, iv, acc) == M.cm.blocks.rev_onto(acc, C.cbc.enc(~K, ~enc, k, bs, iv)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      tr.cbc_enc_go(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p)), Con{enc(k, M.CmBlock.xor(iv, p)), acc})

def tr.cbc_enc_eq(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> {C.cbc.enc(~K, ~enc, k, bs, iv) == C.cbc.enc.fast(~K, ~enc, k, bs, iv) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, C.cbc.enc.fast(~K, ~enc, k, bs, iv), C.cbc.enc(~K, ~enc, k, bs, iv), tr.cbc_enc_go(~K, ~enc, k, bs, iv, Nil{}))

def tr.cbc_dec_go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {C.cbc.dec.go(~K, ~dec, k, bs, iv, acc) == M.cm.blocks.rev_onto(acc, C.cbc.dec(~K, ~dec, k, bs, iv)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      tr.cbc_dec_go(~K, ~dec, k, t, c, Con{M.CmBlock.xor(iv, dec(k, c)), acc})

def tr.cbc_dec_eq(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> {C.cbc.dec(~K, ~dec, k, bs, iv) == C.cbc.dec.fast(~K, ~dec, k, bs, iv) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, C.cbc.dec.fast(~K, ~dec, k, bs, iv), C.cbc.dec(~K, ~dec, k, bs, iv), tr.cbc_dec_go(~K, ~dec, k, bs, iv, Nil{}))

# The byte layers

def tr.cbc_e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +v: M.CmBlock, s: M.CmSplit, +n: Nat) -> {C.cbc.e2(~K, ~enc, k, v, s, n) == C.cbc.e2.fast(~K, ~enc, k, v, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{+bs, tail}:
      match tail:
        case Nil{}:
          %tr.cbc_enc_eq(~K, ~enc, k, bs, v) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, bs, v), Nil{}))} == Done{B.Octets.of_list(M.cm.join_onto.fast(_, Nil{}))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.join_eq(C.cbc.enc(~K, ~enc, k, bs, v), Nil{}) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, bs, v), Nil{}))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}
        case Con{h, t}:
          {==}

def tr.cbc_e1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {C.cbc.e1(~K, ~enc, k, r, xs) == C.cbc.e1.fast(~K, ~enc, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      %tr.split_eq(xs) : {C.cbc.e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.e2.fast(~K, ~enc, k, v, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {C.cbc.e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.e2.fast(~K, ~enc, k, v, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.cbc_e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs))

def tr.cbc_d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +v: M.CmBlock, s: M.CmSplit, +n: Nat) -> {C.cbc.d2(~K, ~dec, k, v, s, n) == C.cbc.d2.fast(~K, ~dec, k, v, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{+bs, tail}:
      match tail:
        case Nil{}:
          %tr.cbc_dec_eq(~K, ~dec, k, bs, v) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.dec(~K, ~dec, k, bs, v), Nil{}))} == Done{B.Octets.of_list(M.cm.join_onto.fast(_, Nil{}))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.join_eq(C.cbc.dec(~K, ~dec, k, bs, v), Nil{}) : {Done{B.Octets.of_list(M.cm.join_onto(C.cbc.dec(~K, ~dec, k, bs, v), Nil{}))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}
        case Con{h, t}:
          {==}

def tr.cbc_d1(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {C.cbc.d1(~K, ~dec, k, r, xs) == C.cbc.d1.fast(~K, ~dec, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+v}:
      %tr.split_eq(xs) : {C.cbc.d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.d2.fast(~K, ~dec, k, v, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {C.cbc.d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs)) == C.cbc.d2.fast(~K, ~dec, k, v, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.cbc_d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs))

def tr.cbc_encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +m: B.Octets) -> {C.Cbc.encrypt.ref(~K, ~enc, k, iv, m) == C.Cbc.encrypt(~K, ~enc, k, iv, m) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.cbc_e1(~K, ~enc, k, C.cbc.iv(iv), B.Octets.to_list(m))

def tr.cbc_decrypt(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +c: B.Octets) -> {C.Cbc.decrypt.ref(~K, ~dec, k, iv, c) == C.Cbc.decrypt(~K, ~dec, k, iv, c) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.cbc_d1(~K, ~dec, k, C.cbc.iv(iv), B.Octets.to_list(c))

# the blocks CBC encryption gives the cipher: each plaintext block XOR the
# block before it (the IV first)
def cbcp.ins(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      Con{M.CmBlock.xor(iv, p), cbcp.ins(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p)))}

# CBC on blocks

def cbcp.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +iv: M.CmBlock) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, cbcp.ins(~K, ~enc, k, bs, iv)) == cbcp.ins(~K, ~enc, k, bs, iv) : List<&2, M.CmBlock>} -> {C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, bs, iv), iv) == bs : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+p, +t}:
      +h => %Equal.sym(M.CmBlock, dec(k, enc(k, M.CmBlock.xor(iv, p))), M.CmBlock.xor(iv, p), cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(iv, p), cbcp.ins(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), h)) : {Con{M.CmBlock.xor(iv, _), C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), enc(k, M.CmBlock.xor(iv, p)))} == Con{p, t} : List<&2, M.CmBlock>}
        %bx.block(iv, p) : {Con{M.CmBlock.xor(iv, M.CmBlock.xor(iv, p)), C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), enc(k, M.CmBlock.xor(iv, p)))} == Con{_, t} : List<&2, M.CmBlock>}
        %cbcp.go(~K, ~enc, ~dec, k, t, enc(k, M.CmBlock.xor(iv, p)))(cmp.tl(~K, ~enc, ~dec, k, M.CmBlock.xor(iv, p), cbcp.ins(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), h)) : {Con{M.CmBlock.xor(iv, M.CmBlock.xor(iv, p)), C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, t, enc(k, M.CmBlock.xor(iv, p))), enc(k, M.CmBlock.xor(iv, p)))} == Con{M.CmBlock.xor(iv, M.CmBlock.xor(iv, p)), _} : List<&2, M.CmBlock>}
        {==}

def Laws.cbc_blocks_round_trip(K, enc, dec, k, inv, iv, bs):
  +v = iv
  +b = bs
  # the tail-recursive forms are the structural ones
  %tr.cbc_enc_eq(~K, ~enc, k, b, v) : {C.cbc.dec.fast(~K, ~dec, k, _, iv) == bs : List<&2, M.CmBlock>}
  %tr.cbc_dec_eq(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, b, v), v) : {_ == bs : List<&2, M.CmBlock>}
  cbcp.go(~K, ~enc, ~dec, k, b, v)(inv(cbcp.ins(~K, ~enc, k, b, v)))

def Laws.cbc_round_trip(K, enc, dec, k, inv, iv, m, hi, hm):
  +et = sp.mod_tail(B.Octets.to_list(m))(oc.mod(m, hm))
  # the public defs are the structural ones
  %tr.cbc_encrypt(~K, ~enc, k, iv, m) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, c => C.Cbc.decrypt(~K, ~dec, k, iv, c)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %tr.bind_cong(C.Cbc.encrypt.ref(~K, ~enc, k, iv, m), c => C.Cbc.decrypt.ref(~K, ~dec, k, iv, c), c => C.Cbc.decrypt(~K, ~dec, k, iv, c), c => tr.cbc_decrypt(~K, ~dec, k, iv, c)) : {_ == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the IV is a block
  %Equal.sym(Result<&2, &2, M.CmError, M.CmBlock>, C.cbc.iv(iv), Done{M.cm.block_of(B.Octets.to_list(iv))}, cbcp.iv(iv, hi)) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e1(~K, ~enc, k, _, B.Octets.to_list(m)), c => C.cbc.d1(~K, ~dec, k, _, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the message is masked
  %oc.masked(m) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e2(~K, ~enc, k, M.cm.block_of(B.Octets.to_list(iv)), M.cm.split(_), B.len(B.Octets.to_list(m))), c => C.cbc.d1(~K, ~dec, k, Done{M.cm.block_of(B.Octets.to_list(iv))}, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # its split is its blocks and tail
  %sp.eta(M.cm.split(B.mask(B.Octets.to_list(m)))) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e2(~K, ~enc, k, M.cm.block_of(B.Octets.to_list(iv)), _, B.len(B.Octets.to_list(m))), c => C.cbc.d1(~K, ~dec, k, Done{M.cm.block_of(B.Octets.to_list(iv))}, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # whole blocks leave no tail, so encryption succeeds
  %Equal.sym(List<&2, U32>, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(m)))), Nil{}, et) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, C.cbc.e2(~K, ~enc, k, M.cm.block_of(B.Octets.to_list(iv)), M.CmSplit{M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), _}, B.len(B.Octets.to_list(m))), c => C.cbc.d1(~K, ~dec, k, Done{M.cm.block_of(B.Octets.to_list(iv))}, B.Octets.to_list(c))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # decryption reads the ciphertext's bytes back, masked
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))), B.mask(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{})), BL.octets_to_of(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))) : {C.cbc.d2(~K, ~dec, k, M.cm.block_of(B.Octets.to_list(iv)), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # which they already are
  %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{})), M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}), sp.mask_join(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))))) : {C.cbc.d2(~K, ~dec, k, M.cm.block_of(B.Octets.to_list(iv)), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # and they split into the ciphertext blocks
  %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{})), M.CmSplit{C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}}, sp.split_join(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))))) : {C.cbc.d2(~K, ~dec, k, M.cm.block_of(B.Octets.to_list(iv)), _, B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), Nil{}))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # CBC on blocks
  %Equal.sym(List<&2, M.CmBlock>, C.cbc.dec(~K, ~dec, k, C.cbc.enc(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv))), M.cm.block_of(B.Octets.to_list(iv))), M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), cbcp.go(~K, ~enc, ~dec, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv)))(inv(cbcp.ins(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.block_of(B.Octets.to_list(iv)))))) : {Done{B.Octets.of_list(M.cm.join_onto(_, Nil{}))} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the plaintext blocks and the empty tail
  %et : {Done{B.Octets.of_list(M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), _))} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # join back to the message
  %Equal.sym(List<&2, U32>, M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(m)))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(m))))), B.mask(B.Octets.to_list(m)), sp.join_split(B.Octets.to_list(m))) : {Done{B.Octets.of_list(_)} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, U32>, B.mask(B.Octets.to_list(m)), B.Octets.to_list(m), oc.masked(m)) : {Done{B.Octets.of_list(_)} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(m)), m, BL.octets_of_to(m)) : {Done{_} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  {==}
