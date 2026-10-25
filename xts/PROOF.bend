# Proofs of LAWS.bend (XTS). The byte layer's lemmas the modes share are
# mode-core's laws, used under the names below.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../mode-core/mode-core.bend as M
import ./xts.bend as T
import ../mode-core/LAWS.bend as CoreL
import ../mode-core/PROOF.bend as CoreP
import ./LAWS.bend as Laws

# mode-core's laws, under the names these proofs use

def sp.cons_blocks(b: M.CmBlock, s: M.CmSplit) -> {M.cm.split.blocks(M.cm.split.cons(b, s)) == Con{b, M.cm.split.blocks(s)} : List<&2, M.CmBlock>}:
  CoreL.split_cons_blocks(b, s)

def sp.eta(s: M.CmSplit) -> {M.CmSplit{M.cm.split.blocks(s), M.cm.split.tail(s)} == s : M.CmSplit}:
  CoreL.split_eta(s)

def li.take_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.take(B.len(a), B.append(a, b)) == a : List<&2, U32>}:
  CoreL.list_take_append(a, b)

def li.drop_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.drop(B.len(a), B.append(a, b)) == b : List<&2, U32>}:
  CoreL.list_drop_append(a, b)

def li.mask_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.mask(B.append(a, b)) == B.append(B.mask(a), B.mask(b)) : List<&2, U32>}:
  CoreL.list_mask_append(a, b)

def li.mask_take(+n: Nat, +xs: List<&2, U32>) -> {B.mask(B.take(n, xs)) == B.take(n, B.mask(xs)) : List<&2, U32>}:
  CoreL.list_mask_take(n, xs)

def li.len_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}:
  CoreL.list_len_append(a, b)

def li.len_take(+n: Nat, +xs: List<&2, U32>) -> {Nat.is_le(n, B.len(xs)) == True{} : Bool} -> {B.len(B.take(n, xs)) == n : Nat}:
  h1 => CoreL.list_len_take(n, xs, h1)

def na.lt_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool}:
  h1 => CoreL.nat_lt_le(a, b, h1)

def sp.mask_blk(b: M.CmBlock, rest: List<&2, U32>) -> {B.mask(M.cm.bytes_onto(b, rest)) == M.cm.bytes_onto(b, B.mask(rest)) : List<&2, U32>}:
  CoreL.mask_bytes_onto(b, rest)

def sp.join_split(ys: List<&2, U32>) -> {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), M.cm.split.tail(M.cm.split(B.mask(ys)))) == B.mask(ys) : List<&2, U32>}:
  CoreL.join_split(ys)

def sp.blk16g(z0: U32, z1: U32, z2: U32, z3: U32, z4: U32, z5: U32, z6: U32, z7: U32, z8: U32, z9: U32, z10: U32, z11: U32, z12: U32, z13: U32, z14: U32, z15: U32, rest: List<&2, U32>) -> {M.cm.bytes_onto(M.cm.block16(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15), rest) == Con{B.byte(z0), Con{B.byte(z1), Con{B.byte(z2), Con{B.byte(z3), Con{B.byte(z4), Con{B.byte(z5), Con{B.byte(z6), Con{B.byte(z7), Con{B.byte(z8), Con{B.byte(z9), Con{B.byte(z10), Con{B.byte(z11), Con{B.byte(z12), Con{B.byte(z13), Con{B.byte(z14), Con{B.byte(z15), rest}}}}}}}}}}}}}}}} : List<&2, U32>}:
  CoreL.bytes_onto_block16(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, rest)

def sp.tail_short(ys: List<&2, U32>) -> {Nat.is_lt(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n) == True{} : Bool}:
  CoreL.split_tail_short(ys)

def sp.tail_masked(ys: List<&2, U32>) -> {B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))) == M.cm.split.tail(M.cm.split(B.mask(ys))) : List<&2, U32>}:
  CoreL.split_tail_masked(ys)

def sp.short_split(ys: List<&2, U32>) -> {Nat.is_lt(B.len(ys), 16n) == True{} : Bool} -> {M.cm.split(ys) == M.CmSplit{Nil{}, ys} : M.CmSplit}:
  h1 => CoreL.split_short(ys, h1)

def sp.block_bytes(b: M.CmBlock) -> {M.cm.block_of(M.cm.bytes_of(b)) == b : M.CmBlock}:
  CoreL.block_of_bytes_of(b)

def oc.masked(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  CoreL.octets_masked(o)

def oc.len(+o: B.Octets, +n: Nat, h: {B.Octets.len(o) == n : Nat}) -> {B.len(B.Octets.to_list(o)) == n : Nat}:
  CoreL.octets_len(o, n, h)

def tr.len_eq(+bs: List<&2, M.CmBlock>) -> {List.length(&2, M.CmBlock, bs) == M.cm.blocks.len(bs) : Nat}:
  CoreL.blocks_len_fast(bs)

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

def bx.rblock(+a: M.CmBlock, +b: M.CmBlock) -> {M.CmBlock.xor(M.CmBlock.xor(a, b), b) == a : M.CmBlock}:
  CoreL.block_xor_xor(a, b)

def sp.mask_join_onto(bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {B.mask(M.cm.join_onto(bs, rest)) == M.cm.join_onto(bs, B.mask(rest)) : List<&2, U32>}:
  CoreL.mask_join_onto(bs, rest)

def sp.split_join_short(bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.split(rest) == M.CmSplit{Nil{}, rest} : M.CmSplit} -> {M.cm.split(M.cm.join_onto(bs, rest)) == M.CmSplit{bs, rest} : M.CmSplit}:
  h1 => CoreL.split_join_short(bs, rest, h1)

# Booleans: False is not True

def bo.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def bo.empty(h: {False{} == True{} : Bool}) -> Empty:
  %h : bo.disc(_)
  Unit{}

def bo.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, bo.empty(h))

def li.mask_drop(+n: Nat, +xs: List<&2, U32>) -> {B.mask(B.drop(n, xs)) == B.drop(n, B.mask(xs)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          li.mask_drop(p, t)

def li.len_drop(+n: Nat, +xs: List<&2, U32>) -> {B.len(B.drop(n, xs)) == Nat.sub(B.len(xs), n) : Nat}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          li.len_drop(p, t)

# Naturals

def na.add_sub(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+bp:
      h => {==}
    case 1n+ap 0n:
      h => bo.absurd({Nat.add(1n+ap, Nat.sub(0n, 1n+ap)) == 0n : Nat}, h)
    case 1n+ap 1n+bp:
      h => %na.add_sub(ap, bp)(h) : {1n+Nat.add(ap, Nat.sub(bp, ap)) == 1n+_ : Nat}
        {==}

# Blocks in lists

def sp.hd(bs: List<&2, M.CmBlock>) -> M.CmBlock:
  match bs:
    case Nil{}:
      M.CmBlock.zero()
    case Con{b, t}:
      b

def sp.tl(bs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      t

# a byte string of at least 16 bytes has a first block
def sp.nonempty(ys: List<&2, U32>) -> {Nat.is_le(16n, B.len(ys)) == True{} : Bool} -> {Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(ys)))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(ys))))} == M.cm.split.blocks(M.cm.split(B.mask(ys))) : List<&2, M.CmBlock>}:
  match ys:
    case Nil{}:
      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Nil{})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Nil{}))))} == M.cm.split.blocks(M.cm.split(B.mask(Nil{}))) : List<&2, M.CmBlock>}, h)
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Nil{}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Nil{}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Nil{}}))) : List<&2, M.CmBlock>}, h)
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Nil{}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Nil{}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Nil{}}}))) : List<&2, M.CmBlock>}, h)
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}}))) : List<&2, M.CmBlock>}, h)
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}))) : List<&2, M.CmBlock>}, h)
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}))) : List<&2, M.CmBlock>}, h)
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}))) : List<&2, M.CmBlock>}, h)
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => bo.absurd({Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}})))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}))))} == M.cm.split.blocks(M.cm.split(B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}))) : List<&2, M.CmBlock>}, h)
                                                                case Con{+y15, +t}:
                                                                  h => %Equal.sym(List<&2, M.CmBlock>, M.cm.split.blocks(M.cm.split.cons(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))), Con{M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split.blocks(M.cm.split(B.mask(t)))}, sp.cons_blocks(M.cm.block16(B.byte(y0), B.byte(y1), B.byte(y2), B.byte(y3), B.byte(y4), B.byte(y5), B.byte(y6), B.byte(y7), B.byte(y8), B.byte(y9), B.byte(y10), B.byte(y11), B.byte(y12), B.byte(y13), B.byte(y14), B.byte(y15)), M.cm.split(B.mask(t)))) : {Con{sp.hd(_), sp.tl(_)} == _ : List<&2, M.CmBlock>}
                                                                    {==}

# a block of exactly 16 bytes gives them back, masked
def sp.bb16(ys: List<&2, U32>) -> {Nat.is_eq(B.len(ys), 16n) == True{} : Bool} -> {M.cm.bytes_of(M.cm.block_of(ys)) == B.mask(ys) : List<&2, U32>}:
  match ys:
    case Nil{}:
      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Nil{})) == B.mask(Nil{}) : List<&2, U32>}, h)
    case Con{+y0, +r0}:
      match r0:
        case Nil{}:
          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Nil{}})) == B.mask(Con{y0, Nil{}}) : List<&2, U32>}, h)
        case Con{+y1, +r1}:
          match r1:
            case Nil{}:
              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Nil{}}})) == B.mask(Con{y0, Con{y1, Nil{}}}) : List<&2, U32>}, h)
            case Con{+y2, +r2}:
              match r2:
                case Nil{}:
                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Nil{}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Nil{}}}}) : List<&2, U32>}, h)
                case Con{+y3, +r3}:
                  match r3:
                    case Nil{}:
                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Nil{}}}}}) : List<&2, U32>}, h)
                    case Con{+y4, +r4}:
                      match r4:
                        case Nil{}:
                          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Nil{}}}}}}) : List<&2, U32>}, h)
                        case Con{+y5, +r5}:
                          match r5:
                            case Nil{}:
                              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Nil{}}}}}}}) : List<&2, U32>}, h)
                            case Con{+y6, +r6}:
                              match r6:
                                case Nil{}:
                                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Nil{}}}}}}}}) : List<&2, U32>}, h)
                                case Con{+y7, +r7}:
                                  match r7:
                                    case Nil{}:
                                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Nil{}}}}}}}}}) : List<&2, U32>}, h)
                                    case Con{+y8, +r8}:
                                      match r8:
                                        case Nil{}:
                                          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Nil{}}}}}}}}}}) : List<&2, U32>}, h)
                                        case Con{+y9, +r9}:
                                          match r9:
                                            case Nil{}:
                                              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Nil{}}}}}}}}}}}) : List<&2, U32>}, h)
                                            case Con{+y10, +r10}:
                                              match r10:
                                                case Nil{}:
                                                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Nil{}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                case Con{+y11, +r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Nil{}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                    case Con{+y12, +r12}:
                                                      match r12:
                                                        case Nil{}:
                                                          h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Nil{}}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                        case Con{+y13, +r13}:
                                                          match r13:
                                                            case Nil{}:
                                                              h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Nil{}}}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                            case Con{+y14, +r14}:
                                                              match r14:
                                                                case Nil{}:
                                                                  h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Nil{}}}}}}}}}}}}}}}}) : List<&2, U32>}, h)
                                                                case Con{+y15, +t}:
                                                                  match t:
                                                                    case Nil{}:
                                                                      h => sp.blk16g(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, Nil{})
                                                                    case Con{+z, +zs}:
                                                                      h => bo.absurd({M.cm.bytes_of(M.cm.block_of(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Con{z, zs}}}}}}}}}}}}}}}}})) == B.mask(Con{y0, Con{y1, Con{y2, Con{y3, Con{y4, Con{y5, Con{y6, Con{y7, Con{y8, Con{y9, Con{y10, Con{y11, Con{y12, Con{y13, Con{y14, Con{y15, Con{z, zs}}}}}}}}}}}}}}}}}) : List<&2, U32>}, h)

# The tail-recursive forms the modes run are the structural ones, for every
# input: each loop with an accumulator is its structural form reversed onto
# the accumulator, and reversing twice gives the order back. Then the byte
# layers built from them are the structural byte layers, and so are the
# public defs (Cbc.encrypt == Cbc.encrypt.ref, ...).

def tr.rr(xs: List<&2, M.CmBlock>, acc: List<&2, M.CmBlock>, b: List<&2, M.CmBlock>) -> {M.cm.blocks.rev_onto(M.cm.blocks.rev_onto(xs, acc), b) == M.cm.blocks.rev_onto(acc, List.append(&2, M.CmBlock, xs, b)) : List<&2, M.CmBlock>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      tr.rr(t, Con{h, acc}, b)

def tr.append_eq(+xs: List<&2, M.CmBlock>, +ys: List<&2, M.CmBlock>) -> {List.append(&2, M.CmBlock, xs, ys) == M.cm.blocks.append(xs, ys) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, M.cm.blocks.append(xs, ys), List.append(&2, M.CmBlock, xs, ys), tr.rr(xs, Nil{}, ys))

def tr.xts_enc_go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {T.xts.enc.go(~K, ~enc, k, bs, t, acc) == M.cm.blocks.rev_onto(acc, T.xts.enc(~K, ~enc, k, bs, t)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      tr.xts_enc_go(~K, ~enc, k, rest, T.Xts.mul_alpha(t), Con{T.xts.benc(~K, ~enc, k, p, t), acc})

def tr.xts_enc_eq(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {T.xts.enc(~K, ~enc, k, bs, t) == T.xts.enc.fast(~K, ~enc, k, bs, t) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, T.xts.enc.fast(~K, ~enc, k, bs, t), T.xts.enc(~K, ~enc, k, bs, t), tr.xts_enc_go(~K, ~enc, k, bs, t, Nil{}))

def tr.xts_dec_go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {T.xts.dec.go(~K, ~dec, k, bs, t, acc) == M.cm.blocks.rev_onto(acc, T.xts.dec(~K, ~dec, k, bs, t)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      tr.xts_dec_go(~K, ~dec, k, rest, T.Xts.mul_alpha(t), Con{T.xts.bdec(~K, ~dec, k, c, t), acc})

def tr.xts_dec_eq(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {T.xts.dec(~K, ~dec, k, bs, t) == T.xts.dec.fast(~K, ~dec, k, bs, t) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, T.xts.dec.fast(~K, ~dec, k, bs, t), T.xts.dec(~K, ~dec, k, bs, t), tr.xts_dec_go(~K, ~dec, k, bs, t, Nil{}))

def tr.init_go(rest: List<&2, M.CmBlock>, +p: M.CmBlock, +acc: List<&2, M.CmBlock>) -> {T.xts.init.go(rest, p, acc) == M.cm.blocks.rev_onto(acc, T.xts.init(rest, p)) : List<&2, M.CmBlock>}:
  match rest:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      tr.init_go(r, q, Con{p, acc})

def tr.init_eq(+rest: List<&2, M.CmBlock>, +p: M.CmBlock) -> {T.xts.init(rest, p) == T.xts.init.fast(rest, p) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, T.xts.init.fast(rest, p), T.xts.init(rest, p), tr.init_go(rest, p, Nil{}))

def tr.xts_eout(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> {T.xts.eout(~K, ~enc, k, t, init, last, tail) == T.xts.eout.fast(~K, ~enc, k, t, init, last, tail) : List<&2, U32>}:
  %tr.len_eq(init) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == M.cm.join_onto.fast(M.cm.blocks.append(T.xts.enc.fast(~K, ~enc, k, init, t), Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(_, t)), Nil{}}), T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(_, t))) : List<&2, U32>}
  %tr.xts_enc_eq(~K, ~enc, k, init, t) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == M.cm.join_onto.fast(M.cm.blocks.append(_, Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t)), Nil{}}), T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : List<&2, U32>}
  %tr.append_eq(T.xts.enc(~K, ~enc, k, init, t), Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t)), Nil{}}) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == M.cm.join_onto.fast(_, T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : List<&2, U32>}
  %tr.join_eq(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k, init, t), Con{T.xts.steal_c(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t)), Nil{}}), T.xts.steal_t(~K, ~enc, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : {T.xts.eout(~K, ~enc, k, t, init, last, tail) == _ : List<&2, U32>}
  {==}

def tr.xts_dout(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, +init: List<&2, M.CmBlock>, +last: M.CmBlock, +tail: List<&2, U32>) -> {T.xts.dout(~K, ~dec, k, t, init, last, tail) == T.xts.dout.fast(~K, ~dec, k, t, init, last, tail) : List<&2, U32>}:
  %tr.len_eq(init) : {T.xts.dout(~K, ~dec, k, t, init, last, tail) == M.cm.join_onto.fast(T.xts.dec.fast(~K, ~dec, k, init, t), T.xts.dsteal(~K, ~dec, k, last, tail, T.xts.alpha_n(_, t))) : List<&2, U32>}
  %tr.xts_dec_eq(~K, ~dec, k, init, t) : {T.xts.dout(~K, ~dec, k, t, init, last, tail) == M.cm.join_onto.fast(_, T.xts.dsteal(~K, ~dec, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : List<&2, U32>}
  %tr.join_eq(T.xts.dec(~K, ~dec, k, init, t), T.xts.dsteal(~K, ~dec, k, last, tail, T.xts.alpha_n(List.length(&2, M.CmBlock, init), t))) : {T.xts.dout(~K, ~dec, k, t, init, last, tail) == _ : List<&2, U32>}
  {==}

def tr.xts_e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> {T.xts.e2(~K, ~enc, k, t, s, n) == T.xts.e2.fast(~K, ~enc, k, t, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{bs, +tail}:
      match bs:
        case Nil{}:
          {==}
        case Con{+p, +rest}:
          %tr.init_eq(rest, p) : {Done{B.Octets.of_list(T.xts.eout(~K, ~enc, k, t, T.xts.init(rest, p), T.xts.last(rest, p), tail))} == Done{B.Octets.of_list(T.xts.eout.fast(~K, ~enc, k, t, _, T.xts.last(rest, p), tail))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.xts_eout(~K, ~enc, k, t, T.xts.init(rest, p), T.xts.last(rest, p), tail) : {Done{B.Octets.of_list(T.xts.eout(~K, ~enc, k, t, T.xts.init(rest, p), T.xts.last(rest, p), tail))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}

def tr.xts_d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, s: M.CmSplit, +n: Nat) -> {T.xts.d2(~K, ~dec, k, t, s, n) == T.xts.d2.fast(~K, ~dec, k, t, s, n) : Result<&2, &2, M.CmError, B.Octets>}:
  match s:
    case M.CmSplit{bs, +tail}:
      match bs:
        case Nil{}:
          {==}
        case Con{+c, +rest}:
          %tr.init_eq(rest, c) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, T.xts.init(rest, c), T.xts.last(rest, c), tail))} == Done{B.Octets.of_list(T.xts.dout.fast(~K, ~dec, k, t, _, T.xts.last(rest, c), tail))} : Result<&2, &2, M.CmError, B.Octets>}
          %tr.xts_dout(~K, ~dec, k, t, T.xts.init(rest, c), T.xts.last(rest, c), tail) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, T.xts.init(rest, c), T.xts.last(rest, c), tail))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
          {==}

def tr.xts_e1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {T.xts.e1(~K, ~enc, k, r, xs) == T.xts.e1.fast(~K, ~enc, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+t}:
      %tr.split_eq(xs) : {T.xts.e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs)) == T.xts.e2.fast(~K, ~enc, k, t, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {T.xts.e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs)) == T.xts.e2.fast(~K, ~enc, k, t, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.xts_e2(~K, ~enc, k, t, M.cm.split(xs), B.len(xs))

def tr.xts_d1(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> {T.xts.d1(~K, ~dec, k, r, xs) == T.xts.d1.fast(~K, ~dec, k, r, xs) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{+t}:
      %tr.split_eq(xs) : {T.xts.d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs)) == T.xts.d2.fast(~K, ~dec, k, t, _, B.len.fast(xs)) : Result<&2, &2, M.CmError, B.Octets>}
      %BL.len_fast(xs) : {T.xts.d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs)) == T.xts.d2.fast(~K, ~dec, k, t, M.cm.split(xs), _) : Result<&2, &2, M.CmError, B.Octets>}
      tr.xts_d2(~K, ~dec, k, t, M.cm.split(xs), B.len(xs))

def tr.xts_encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, +i: B.Octets, +p: B.Octets) -> {T.Xts.encrypt.ref(~K, ~enc, k1, k2, i, p) == T.Xts.encrypt(~K, ~enc, k1, k2, i, p) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.xts_e1(~K, ~enc, k1, T.xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(p))

def tr.xts_decrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k1: K, +k2: K, +i: B.Octets, +c: B.Octets) -> {T.Xts.decrypt.ref(~K, ~enc, ~dec, k1, k2, i, c) == T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c) : Result<&2, &2, M.CmError, B.Octets>}:
  tr.xts_d1(~K, ~dec, k1, T.xts.tweak(~K, ~enc, k2, i), B.Octets.to_list(c))

# the round trip of a ++ b gives a's, and b's
def cmp.app_l(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, a: List<&2, M.CmBlock>, +b: List<&2, M.CmBlock>) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, List.append(&2, M.CmBlock, a, b)) == List.append(&2, M.CmBlock, a, b) : List<&2, M.CmBlock>} -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, a) == a : List<&2, M.CmBlock>}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      +h => %Equal.sym(M.CmBlock, dec(k, enc(k, x)), x, cmp.hd(~K, ~enc, ~dec, k, x, List.append(&2, M.CmBlock, r, b), h)) : {Con{_, M.CmBlock.dec_enc(~K, ~enc, ~dec, k, r)} == Con{x, r} : List<&2, M.CmBlock>}
        %Equal.sym(List<&2, M.CmBlock>, M.CmBlock.dec_enc(~K, ~enc, ~dec, k, r), r, cmp.app_l(~K, ~enc, ~dec, k, r, b)(cmp.tl(~K, ~enc, ~dec, k, x, List.append(&2, M.CmBlock, r, b), h))) : {Con{x, _} == Con{x, r} : List<&2, M.CmBlock>}
        {==}

def cmp.app_r(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, a: List<&2, M.CmBlock>, +b: List<&2, M.CmBlock>) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, List.append(&2, M.CmBlock, a, b)) == List.append(&2, M.CmBlock, a, b) : List<&2, M.CmBlock>} -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, b) == b : List<&2, M.CmBlock>}:
  match a:
    case Nil{}:
      h => h
    case Con{+x, +r}:
      h => cmp.app_r(~K, ~enc, ~dec, k, r, b)(cmp.tl(~K, ~enc, ~dec, k, x, List.append(&2, M.CmBlock, r, b), h))

# the blocks XTS gives the cipher under k1: each block XOR its tweak
def xtsp.ins(bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      Con{M.CmBlock.xor(p, t), xtsp.ins(rest, T.Xts.mul_alpha(t))}

# and ciphertext stealing's: the last whole block XOR its tweak, then (with a
# tail) the block the tail steals into XOR the next tweak
def xtsp.sins(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> List<&2, M.CmBlock>:
  match tl:
    case Nil{}:
      Con{M.CmBlock.xor(p, t), Nil{}}
    case Con{+h, +r}:
      Con{M.CmBlock.xor(p, t), Con{M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}}}

# XTS on blocks

# one block under one tweak: D(E(p xor t) xor t xor t) xor t == p
def xtsp.blk(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, +t: M.CmBlock, hb: {dec(k, enc(k, M.CmBlock.xor(p, t))) == M.CmBlock.xor(p, t) : M.CmBlock}) -> {T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t) == p : M.CmBlock}:
  %Equal.sym(M.CmBlock, M.CmBlock.xor(M.CmBlock.xor(enc(k, M.CmBlock.xor(p, t)), t), t), enc(k, M.CmBlock.xor(p, t)), bx.rblock(enc(k, M.CmBlock.xor(p, t)), t)) : {M.CmBlock.xor(dec(k, _), t) == p : M.CmBlock}
  %Equal.sym(M.CmBlock, dec(k, enc(k, M.CmBlock.xor(p, t))), M.CmBlock.xor(p, t), hb) : {M.CmBlock.xor(_, t) == p : M.CmBlock}
  bx.rblock(p, t)

def xtsp.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xtsp.ins(bs, t)) == xtsp.ins(bs, t) : List<&2, M.CmBlock>} -> {T.xts.dec(~K, ~dec, k, T.xts.enc(~K, ~enc, k, bs, t), t) == bs : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+p, +rest}:
      +h => %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t), p, xtsp.blk(~K, ~enc, ~dec, k, p, t, cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), xtsp.ins(rest, T.Xts.mul_alpha(t)), h))) : {Con{_, T.xts.dec(~K, ~dec, k, T.xts.enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t)), T.Xts.mul_alpha(t))} == Con{p, rest} : List<&2, M.CmBlock>}
        %Equal.sym(List<&2, M.CmBlock>, T.xts.dec(~K, ~dec, k, T.xts.enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t)), T.Xts.mul_alpha(t)), rest, xtsp.go(~K, ~enc, ~dec, k, rest, T.Xts.mul_alpha(t))(cmp.tl(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), xtsp.ins(rest, T.Xts.mul_alpha(t)), h))) : {Con{p, _} == Con{p, rest} : List<&2, M.CmBlock>}
        {==}

def Laws.xts_blocks_round_trip(K, enc, dec, k1, inv, t, bs):
  +v = t
  +b = bs
  # the tail-recursive forms are the structural ones
  %tr.xts_enc_eq(~K, ~enc, k1, b, v) : {T.xts.dec.fast(~K, ~dec, k1, _, t) == bs : List<&2, M.CmBlock>}
  %tr.xts_dec_eq(~K, ~dec, k1, T.xts.enc(~K, ~enc, k1, b, v), v) : {_ == bs : List<&2, M.CmBlock>}
  xtsp.go(~K, ~enc, ~dec, k1, b, v)(inv(xtsp.ins(b, v)))

def sp.join_append(bs: List<&2, M.CmBlock>, +x: M.CmBlock, +rest: List<&2, U32>) -> {M.cm.join_onto(List.append(&2, M.CmBlock, bs, Con{x, Nil{}}), rest) == M.cm.join_onto(bs, M.cm.bytes_onto(x, rest)) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %sp.join_append(t, x, rest) : {M.cm.bytes_onto(b, M.cm.join_onto(List.append(&2, M.CmBlock, t, Con{x, Nil{}}), rest)) == M.cm.bytes_onto(b, _) : List<&2, U32>}
      {==}

# The last block and the others

def li.init_app(es: List<&2, M.CmBlock>, +x: M.CmBlock, +e: M.CmBlock) -> {T.xts.init(List.append(&2, M.CmBlock, es, Con{x, Nil{}}), e) == Con{e, es} : List<&2, M.CmBlock>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e2, +es2}:
      %li.init_app(es2, x, e2) : {Con{e, T.xts.init(List.append(&2, M.CmBlock, es2, Con{x, Nil{}}), e2)} == Con{e, _} : List<&2, M.CmBlock>}
      {==}

def li.last_app(es: List<&2, M.CmBlock>, +x: M.CmBlock, +e: M.CmBlock) -> {T.xts.last(List.append(&2, M.CmBlock, es, Con{x, Nil{}}), e) == x : M.CmBlock}:
  match es:
    case Nil{}:
      {==}
    case Con{+e2, +es2}:
      li.last_app(es2, x, e2)

def li.init_last(rest: List<&2, M.CmBlock>, +p: M.CmBlock) -> {List.append(&2, M.CmBlock, T.xts.init(rest, p), Con{T.xts.last(rest, p), Nil{}}) == Con{p, rest} : List<&2, M.CmBlock>}:
  match rest:
    case Nil{}:
      {==}
    case Con{+q, +r}:
      %li.init_last(r, q) : {Con{p, List.append(&2, M.CmBlock, T.xts.init(r, q), Con{T.xts.last(r, q), Nil{}})} == Con{p, _} : List<&2, M.CmBlock>}
      {==}

def li.len_enc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +t: M.CmBlock) -> {List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k, bs, t)) == List.length(&2, M.CmBlock, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      %li.len_enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t)) : {1n+List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k, rest, T.Xts.mul_alpha(t))) == 1n+_ : Nat}
      {==}

# The byte layer

def oc.le16(+o: B.Octets, h: {Nat.is_le(16n, B.Octets.len(o)) == True{} : Bool}) -> {Nat.is_le(16n, B.len(B.Octets.to_list(o))) == True{} : Bool}:
  %BL.octets_len_list(o) : {Nat.is_le(16n, _) == True{} : Bool}
  h

def xtsp.tweak(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k2: K, +i: B.Octets, h: {B.Octets.len(i) == 16n : Nat}) -> {T.xts.tweak(~K, ~enc, k2, i) == Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))} : Result<&2, &2, M.CmError, M.CmBlock>}:
  %Equal.sym(Nat, B.len(B.Octets.to_list(i)), 16n, oc.len(i, 16n, h)) : {T.xts.tweak.go(~K, ~enc, k2, M.cm.need_block.pick(Nat.is_eq(_, 16n), B.Octets.to_list(i), M.CmBadTweakLength{B.len(B.Octets.to_list(i))})) == Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))} : Result<&2, &2, M.CmError, M.CmBlock>}
  {==}

# the final partial ciphertext block is masked, and splits into no blocks
def xtsp.mask_steal_t(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> {B.mask(T.xts.steal_t(~K, ~enc, k, p, tl, t)) == T.xts.steal_t(~K, ~enc, k, p, tl, t) : List<&2, U32>}:
  match tl:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      %Equal.sym(List<&2, U32>, B.mask(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), B.take(B.len(Con{h, r}), B.mask(M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), li.mask_take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))) : {_ == B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(T.xts.benc(~K, ~enc, k, p, t), Nil{})), M.cm.bytes_onto(T.xts.benc(~K, ~enc, k, p, t), B.mask(Nil{})), sp.mask_blk(T.xts.benc(~K, ~enc, k, p, t), Nil{})) : {B.take(B.len(Con{h, r}), _) == B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))) : List<&2, U32>}
      {==}

def xtsp.lt_take(+n: Nat, +b: M.CmBlock, +h: {Nat.is_lt(n, 16n) == True{} : Bool}) -> {Nat.is_lt(B.len(B.take(n, M.cm.bytes_of(b))), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(B.take(n, M.cm.bytes_of(b))), n, li.len_take(n, M.cm.bytes_of(b))(na.lt_le(n, 16n)(h))) : {Nat.is_lt(_, 16n) == True{} : Bool}
  h

def xtsp.split_steal_t(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> {Nat.is_lt(B.len(tl), 16n) == True{} : Bool} -> {M.cm.split(T.xts.steal_t(~K, ~enc, k, p, tl, t)) == M.CmSplit{Nil{}, T.xts.steal_t(~K, ~enc, k, p, tl, t)} : M.CmSplit}:
  match tl:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      h => sp.short_split(B.take(B.len(Con{x, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))(xtsp.lt_take(B.len(Con{x, r}), T.xts.benc(~K, ~enc, k, p, t), h))

# the bytes the stealing passes through: tl, then the stolen tail of b
def xtsp.len16(+tl: List<&2, U32>, +b: M.CmBlock, h: {Nat.is_lt(B.len(tl), 16n) == True{} : Bool}) -> {Nat.is_eq(B.len(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), Nat.add(B.len(tl), B.len(B.drop(B.len(tl), M.cm.bytes_of(b)))), li.len_append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))) : {Nat.is_eq(_, 16n) == True{} : Bool}
  %Equal.sym(Nat, B.len(B.drop(B.len(tl), M.cm.bytes_of(b))), Nat.sub(16n, B.len(tl)), li.len_drop(B.len(tl), M.cm.bytes_of(b))) : {Nat.is_eq(Nat.add(B.len(tl), _), 16n) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(B.len(tl), Nat.sub(16n, B.len(tl))), 16n, na.add_sub(B.len(tl), 16n)(na.lt_le(B.len(tl), 16n)(h))) : {Nat.is_eq(_, 16n) == True{} : Bool}
  {==}

def xtsp.maskY(+tl: List<&2, U32>, +b: M.CmBlock, hm: {B.mask(tl) == tl : List<&2, U32>}) -> {B.mask(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), B.append(B.mask(tl), B.mask(B.drop(B.len(tl), M.cm.bytes_of(b)))), li.mask_append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))) : {_ == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(B.drop(B.len(tl), M.cm.bytes_of(b))), B.drop(B.len(tl), B.mask(M.cm.bytes_of(b))), li.mask_drop(B.len(tl), M.cm.bytes_of(b))) : {B.append(B.mask(tl), _) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(b, Nil{})), M.cm.bytes_onto(b, B.mask(Nil{})), sp.mask_blk(b, Nil{})) : {B.append(B.mask(tl), B.drop(B.len(tl), _)) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(tl), tl, hm) : {B.append(_, B.drop(B.len(tl), M.cm.bytes_of(b))) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}
  {==}

def xtsp.ppY(+tl: List<&2, U32>, +b: M.CmBlock, hm: {B.mask(tl) == tl : List<&2, U32>}, hl: {Nat.is_lt(B.len(tl), 16n) == True{} : Bool}) -> {M.cm.bytes_of(M.cm.block_of(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))))) == B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, M.cm.bytes_of(M.cm.block_of(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))))), B.mask(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b)))), B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))), sp.bb16(B.append(tl, B.drop(B.len(tl), M.cm.bytes_of(b))))(xtsp.len16(tl, b, hl)), xtsp.maskY(tl, b, hm))

# Ciphertext stealing undoes itself: the last whole block p and a tail tl
# (masked, fewer than 16 bytes), encrypted by steal_c and steal_t and
# decrypted by dsteal, come back as p's bytes and then tl
def xtsp.steal(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +p: M.CmBlock, tl: List<&2, U32>, +t: M.CmBlock) -> {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xtsp.sins(~K, ~enc, k, p, tl, t)) == xtsp.sins(~K, ~enc, k, p, tl, t) : List<&2, M.CmBlock>} -> {B.mask(tl) == tl : List<&2, U32>} -> {Nat.is_lt(B.len(tl), 16n) == True{} : Bool} -> {T.xts.dsteal(~K, ~dec, k, T.xts.steal_c(~K, ~enc, k, p, tl, t), T.xts.steal_t(~K, ~enc, k, p, tl, t), t) == M.cm.bytes_onto(p, tl) : List<&2, U32>}:
  match tl:
    case Nil{}:
      hs => hm => hl => %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t), p, xtsp.blk(~K, ~enc, ~dec, k, p, t, cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), Nil{}, hs))) : {M.cm.bytes_of(_) == M.cm.bytes_onto(p, Nil{}) : List<&2, U32>}
        {==}
    case Con{+h, +r}:
      +hs => +hm => +hl => %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), T.Xts.mul_alpha(t)), M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), xtsp.blk(~K, ~enc, ~dec, k, M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t), cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}, cmp.tl(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), Con{M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}}, hs)))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), M.cm.bytes_of(_)))), t), B.take(B.len(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), M.cm.bytes_of(_))) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(Nat, B.len(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), B.len(Con{h, r}), li.len_take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))(na.lt_le(B.len(Con{h, r}), 16n)(hl))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(_, M.cm.bytes_of(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))))))), t), B.take(_, M.cm.bytes_of(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))))))) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, M.cm.bytes_of(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))))), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), xtsp.ppY(Con{h, r}, T.xts.benc(~K, ~enc, k, p, t), hm, hl)) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(Con{h, r}), _))), t), B.take(B.len(Con{h, r}), _)) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, B.take(B.len(Con{h, r}), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), Con{h, r}, li.take_append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(Con{h, r}), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))))), t), _) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, B.drop(B.len(Con{h, r}), B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), li.drop_append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), _)), t), Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(List<&2, U32>, B.append(B.take(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)), BL.take_drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t)))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, M.cm.block_of(_), t), Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(M.CmBlock, M.cm.block_of(M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))), T.xts.benc(~K, ~enc, k, p, t), sp.block_bytes(T.xts.benc(~K, ~enc, k, p, t))) : {M.cm.bytes_onto(T.xts.bdec(~K, ~dec, k, _, t), Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
              %Equal.sym(M.CmBlock, T.xts.bdec(~K, ~dec, k, T.xts.benc(~K, ~enc, k, p, t), t), p, xtsp.blk(~K, ~enc, ~dec, k, p, t, cmp.hd(~K, ~enc, ~dec, k, M.CmBlock.xor(p, t), Con{M.CmBlock.xor(M.cm.block_of(B.append(Con{h, r}, B.drop(B.len(Con{h, r}), M.cm.bytes_of(T.xts.benc(~K, ~enc, k, p, t))))), T.Xts.mul_alpha(t)), Nil{}}, hs))) : {M.cm.bytes_onto(_, Con{h, r}) == M.cm.bytes_onto(p, Con{h, r}) : List<&2, U32>}
        {==}

def xtsp.d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +t: M.CmBlock, ec: List<&2, M.CmBlock>, +sc: M.CmBlock, +st: List<&2, U32>, +n: Nat) -> {T.xts.d2(~K, ~dec, k, t, M.CmSplit{List.append(&2, M.CmBlock, ec, Con{sc, Nil{}}), st}, n) == Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, ec, sc, st))} : Result<&2, &2, M.CmError, B.Octets>}:
  match ec:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %Equal.sym(List<&2, M.CmBlock>, T.xts.init(List.append(&2, M.CmBlock, es, Con{sc, Nil{}}), e), Con{e, es}, li.init_app(es, sc, e)) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, _, T.xts.last(List.append(&2, M.CmBlock, es, Con{sc, Nil{}}), e), st))} == Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, Con{e, es}, sc, st))} : Result<&2, &2, M.CmError, B.Octets>}
      %Equal.sym(M.CmBlock, T.xts.last(List.append(&2, M.CmBlock, es, Con{sc, Nil{}}), e), sc, li.last_app(es, sc, e)) : {Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, Con{e, es}, _, st))} == Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k, t, Con{e, es}, sc, st))} : Result<&2, &2, M.CmError, B.Octets>}
      {==}

def Laws.xts_round_trip(K, enc, dec, k1, k2, inv, i, p, hi, hp):
  # the hypothesis, at the blocks the cipher is given: ciphertext stealing's, then the others
  +hh = inv(List.append(&2, M.CmBlock, xtsp.sins(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.ins(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))
  +hne = sp.nonempty(B.Octets.to_list(p))(oc.le16(p, hp))
  +mo = Equal.trans(List<&2, U32>, B.mask(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), B.mask(T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), sp.mask_join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), Equal.cong(List<&2, U32>, List<&2, U32>, x => M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), x), B.mask(T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.mask_steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))
  # the public defs are the structural ones
  %tr.xts_encrypt(~K, ~enc, k1, k2, i, p) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, c => T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  %tr.bind_cong(T.Xts.encrypt.ref(~K, ~enc, k1, k2, i, p), c => T.Xts.decrypt.ref(~K, ~enc, ~dec, k1, k2, i, c), c => T.Xts.decrypt(~K, ~enc, ~dec, k1, k2, i, c), c => tr.xts_decrypt(~K, ~enc, ~dec, k1, k2, i, c)) : {_ == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # the tweak
  %Equal.sym(Result<&2, &2, M.CmError, M.CmBlock>, T.xts.tweak(~K, ~enc, k2, i), Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, xtsp.tweak(~K, ~enc, k2, i, hi)) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e1(~K, ~enc, k1, _, B.Octets.to_list(p)), c => T.xts.d1(~K, ~dec, k1, _, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # the data unit is masked
  %oc.masked(p) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e2(~K, ~enc, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.cm.split(_), B.len(B.Octets.to_list(p))), c => T.xts.d1(~K, ~dec, k1, Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # its blocks and tail
  %sp.eta(M.cm.split(B.mask(B.Octets.to_list(p)))) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e2(~K, ~enc, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), _, B.len(B.Octets.to_list(p))), c => T.xts.d1(~K, ~dec, k1, Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # at least one block, so encryption succeeds
  %hne : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, T.xts.e2(~K, ~enc, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.CmSplit{_, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))}, B.len(B.Octets.to_list(p))), c => T.xts.d1(~K, ~dec, k1, Done{enc(k2, M.cm.block_of(B.Octets.to_list(i)))}, B.Octets.to_list(c))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # decryption reads the ciphertext back, masked
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))), B.mask(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), BL.octets_to_of(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))) : {T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # which it already is
  %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))), mo) : {T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.cm.split(_), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # it splits into the ciphertext blocks and the partial block
  %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))), M.CmSplit{List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))}, sp.split_join_short(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))(xtsp.split_steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))(sp.tail_short(B.Octets.to_list(p))))) : {T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), _, B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # decryption takes the last block apart
  %Equal.sym(Result<&2, &2, M.CmError, B.Octets>, T.xts.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), M.CmSplit{List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))}, B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))))), Done{B.Octets.of_list(T.xts.dout(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))}, xtsp.d2(~K, ~dec, k1, enc(k2, M.cm.block_of(B.Octets.to_list(i))), T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), B.len(B.Octets.to_list(B.Octets.of_list(M.cm.join_onto(List.append(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), Con{T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), Nil{}}), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))))))))) : {_ == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # XTS on blocks
  %Equal.sym(List<&2, M.CmBlock>, T.xts.dec(~K, ~dec, k1, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), xtsp.go(~K, ~enc, ~dec, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))(cmp.app_r(~K, ~enc, ~dec, k1, xtsp.sins(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.ins(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), hh))) : {Done{B.Octets.of_list(M.cm.join_onto(_, T.xts.dsteal(~K, ~dec, k1, T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # as many ciphertext blocks as plaintext blocks: the same last tweak
  %Equal.sym(Nat, List.length(&2, M.CmBlock, T.xts.enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), li.len_enc(~K, ~enc, k1, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))) : {Done{B.Octets.of_list(M.cm.join_onto(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), T.xts.dsteal(~K, ~dec, k1, T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.alpha_n(_, enc(k2, M.cm.block_of(B.Octets.to_list(i)))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # ciphertext stealing undoes itself
  %Equal.sym(List<&2, U32>, T.xts.dsteal(~K, ~dec, k1, T.xts.steal_c(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.steal_t(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), M.cm.bytes_onto(T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))), xtsp.steal(~K, ~enc, ~dec, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))))(cmp.app_l(~K, ~enc, ~dec, k1, xtsp.sins(~K, ~enc, k1, T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p)))), T.xts.alpha_n(List.length(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))), enc(k2, M.cm.block_of(B.Octets.to_list(i))))), xtsp.ins(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), enc(k2, M.cm.block_of(B.Octets.to_list(i)))), hh))(sp.tail_masked(B.Octets.to_list(p)))(sp.tail_short(B.Octets.to_list(p)))) : {Done{B.Octets.of_list(M.cm.join_onto(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), _))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # the blocks back together
  %sp.join_append(T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))) : {Done{B.Octets.of_list(_)} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, M.CmBlock>, List.append(&2, M.CmBlock, T.xts.init(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), Con{T.xts.last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))), Nil{}}), Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))}, li.init_last(sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))))) : {Done{B.Octets.of_list(M.cm.join_onto(_, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, M.CmBlock>, Con{sp.hd(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p))))), sp.tl(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))))}, M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))), hne) : {Done{B.Octets.of_list(M.cm.join_onto(_, M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))))} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # and with the tail, the data unit
  %Equal.sym(List<&2, U32>, M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(B.Octets.to_list(p)))), M.cm.split.tail(M.cm.split(B.mask(B.Octets.to_list(p))))), B.mask(B.Octets.to_list(p)), sp.join_split(B.Octets.to_list(p))) : {Done{B.Octets.of_list(_)} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(List<&2, U32>, B.mask(B.Octets.to_list(p)), B.Octets.to_list(p), oc.masked(p)) : {Done{B.Octets.of_list(_)} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  # 
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(p)), p, BL.octets_of_to(p)) : {Done{_} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
  {==}

def Laws.xts_sector():
  {==}
