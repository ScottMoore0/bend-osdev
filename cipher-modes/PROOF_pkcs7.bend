import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./cipher-modes.bend as M
import ./pkcs7.bend as P
import ./LAWS_pkcs7.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# How the proofs go. Padding m (L bytes) to blocks of bs = 1 + q bytes
# appends p = bs - (L mod bs) bytes of value p. The arithmetic: L mod bs is
# at most q, so p = 1 + (q - L mod bs) is 1 to bs, and L + p is a multiple
# of bs (pk.mod_pad, on Base's Nat.divmod.go, as kmath's division lemmas
# are). Unpadding reads the last byte back: p is at most 255, and U32's
# value of the byte of p is p (pk.u8, every value checked by computation:
# U32.from_nat builds a word by increments, so no general lemma is needed);
# the last p bytes are all p, so their XOR difference is 0 (pk.diff_fill:
# each byte XOR itself is 0, bit by bit); and the first L bytes are m (the
# bytes interface laws on take, drop and at of an append). Nothing looks
# inside Octets.

# Booleans: False is not True

def pk.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def pk.empty(h: {False{} == True{} : Bool}) -> Empty:
  %h : pk.disc(_)
  Unit{}

def pk.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, pk.empty(h))

# Naturals

def pk.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (L + k) - k is L
def pk.add_sub(+l: Nat, +k: Nat) -> {Nat.sub(Nat.add(l, k), k) == l : Nat}:
  match k:
    case 0n:
      %UL.nat_add_zero(l) : {Nat.sub(Nat.add(l, 0n), 0n) == _ : Nat}
      pk.sub_zero(Nat.add(l, 0n))
    case 1n+kp:
      %Equal.sym(Nat, Nat.add(l, 1n+kp), 1n+Nat.add(l, kp), UL.nat_add_succ(l, kp)) : {Nat.sub(_, 1n+kp) == l : Nat}
      pk.add_sub(l, kp)

def pk.le_step(+x: Nat, +y: Nat) -> {Nat.is_le(x, y) == True{} : Bool} -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      h => {==}
    case 1n+xp 0n:
      h => pk.absurd({Nat.is_le(1n+xp, 1n) == True{} : Bool}, h)
    case 1n+xp 1n+yp:
      h => pk.le_step(xp, yp)(h)

# q - r <= q
def pk.le_sub(+q: Nat, +r: Nat) -> {Nat.is_le(Nat.sub(q, r), q) == True{} : Bool}:
  match q r:
    case 0n _:
      {==}
    case 1n+qp 0n:
      UL.nat_le_refl(qp)
    case 1n+qp 1n+rp:
      pk.le_step(Nat.sub(qp, rp), qp)(pk.le_sub(qp, rp))

# r <= q gives (1 + q) - r = 1 + (q - r)
def pk.sub_succ(+r: Nat, +q: Nat) -> {Nat.is_le(r, q) == True{} : Bool} -> {Nat.sub(1n+q, r) == 1n+Nat.sub(q, r) : Nat}:
  match r q:
    case 0n _:
      h => %Equal.sym(Nat, Nat.sub(q, 0n), q, pk.sub_zero(q)) : {1n+q == 1n+_ : Nat}
        {==}
    case 1n+rp 0n:
      h => pk.absurd({Nat.sub(1n, 1n+rp) == 1n+Nat.sub(0n, 1n+rp) : Nat}, h)
    case 1n+rp 1n+qp:
      h => pk.sub_succ(rp, qp)(h)

def pk.le_trans(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(b, c) == True{} : Bool} -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      h1 => h2 => {==}
    case 0n _ 1n+cp:
      h1 => h2 => {==}
    case 1n+ap 0n _:
      h1 => h2 => pk.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, h1)
    case 1n+ap 1n+bp 0n:
      h1 => h2 => pk.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, h2)
    case 1n+ap 1n+bp 1n+cp:
      h1 => h2 => pk.le_trans(ap, bp, cp)(h1)(h2)

def pk.le0(+y: Nat) -> {Nat.is_le(0n, y) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+yp:
      {==}

def pk.lt0(+x: Nat) -> {Nat.is_lt(x, 0n) == True{} : Bool} -> {False{} == True{} : Bool}:
  match x:
    case 0n:
      h => h
    case 1n+xp:
      h => h

def pk.lt_le(+x: Nat, +y: Nat) -> {Nat.is_lt(x, 1n+y) == True{} : Bool} -> {Nat.is_le(x, y) == True{} : Bool}:
  match x:
    case 0n:
      h => pk.le0(y)
    case 1n+xp:
      match y:
        case 0n:
          h => pk.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, pk.lt0(xp)(h))
        case 1n+yp:
          h => pk.lt_le(xp, yp)(h)

# Base's division: n counts down the dividend, m the steps left before the
# remainder wraps, d the quotient, r the remainder so far (m + r = q, for a
# divisor 1 + q)

# 1 + m + x steps from (m, d, r) take one wrap and leave x
def pk.go_skip(+m: Nat, +x: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(1n+Nat.add(m, x), m, d, r) == Nat.divmod.go(x, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      Equal.trans(Nat & Nat, Nat.divmod.go(1n+Nat.add(mp, x), mp, d, 1n+r), Nat.divmod.go(x, Nat.add(mp, 1n+r), 1n+d, 0n), Nat.divmod.go(x, 1n+Nat.add(mp, r), 1n+d, 0n), pk.go_skip(mp, x, d, 1n+r), Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(x, z, 1n+d, 0n), Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), UL.nat_add_succ(mp, r)))

# (1 + m + r) - r = 1 + m
def pk.sub_add_r(+m: Nat, +r: Nat) -> {Nat.sub(1n+Nat.add(m, r), r) == 1n+m : Nat}:
  match r:
    case 0n:
      %UL.nat_add_zero(m) : {Nat.sub(1n+Nat.add(m, 0n), 0n) == 1n+_ : Nat}
      {==}
    case 1n+rp:
      %Equal.sym(Nat, Nat.add(m, 1n+rp), 1n+Nat.add(m, rp), UL.nat_add_succ(m, rp)) : {Nat.sub(1n+_, 1n+rp) == 1n+m : Nat}
      pk.sub_add_r(m, rp)

# the remainder is at most q
def pk.mod_le(+a: Nat, +m: Nat, +d: Nat, +r: Nat, +q: Nat) -> {Nat.add(m, r) == q : Nat} -> {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r)), q) == True{} : Bool}:
  match a:
    case 0n:
      inv => %inv : {Nat.is_le(r, _) == True{} : Bool}
        UL.nat_le_add(r, m)
    case 1n+ap:
      match m:
        case 0n:
          inv => pk.mod_le(ap, r, 1n+d, 0n, q)(Equal.trans(Nat, Nat.add(r, 0n), r, q, UL.nat_add_zero(r), inv))
        case 1n+mp:
          inv => pk.mod_le(ap, mp, d, 1n+r, q)(Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), q, UL.nat_add_succ(mp, r), inv))

# a + (1 + q - (a mod (1 + q))) is a multiple of 1 + q
def pk.mod_pad(+a: Nat, +m: Nat, +d: Nat, +r: Nat, +q: Nat) -> {Nat.add(m, r) == q : Nat} -> {Pair.snd(Nat, Nat, Nat.divmod.go(Nat.add(a, Nat.sub(1n+q, Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r)))), m, d, r)) == 0n : Nat}:
  match a:
    case 0n:
      inv => %inv : {Pair.snd(Nat, Nat, Nat.divmod.go(Nat.sub(1n+_, r), m, d, r)) == 0n : Nat}
        %Equal.sym(Nat, Nat.sub(1n+Nat.add(m, r), r), 1n+m, pk.sub_add_r(m, r)) : {Pair.snd(Nat, Nat, Nat.divmod.go(_, m, d, r)) == 0n : Nat}
        %UL.nat_add_zero(m) : {Pair.snd(Nat, Nat, Nat.divmod.go(1n+_, m, d, r)) == 0n : Nat}
        %Equal.sym(Nat & Nat, Nat.divmod.go(1n+Nat.add(m, 0n), m, d, r), Nat.divmod.go(0n, Nat.add(m, r), 1n+d, 0n), pk.go_skip(m, 0n, d, r)) : {Pair.snd(Nat, Nat, _) == 0n : Nat}
        {==}
    case 1n+ap:
      match m:
        case 0n:
          inv => pk.mod_pad(ap, r, 1n+d, 0n, q)(Equal.trans(Nat, Nat.add(r, 0n), r, q, UL.nat_add_zero(r), inv))
        case 1n+mp:
          inv => pk.mod_pad(ap, mp, d, 1n+r, q)(Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), q, UL.nat_add_succ(mp, r), inv))

# The padding bytes

def pk.fill_len(+n: Nat, +v: U32) -> {B.len(P.pkcs7.fill(n, v)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %pk.fill_len(p, v) : {1n+B.len(P.pkcs7.fill(p, v)) == 1n+_ : Nat}
      {==}

def pk.mask_fill(+n: Nat, +v: U32) -> {B.mask(P.pkcs7.fill(n, v)) == P.pkcs7.fill(n, B.byte(v)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %pk.mask_fill(p, v) : {Con{B.byte(v), B.mask(P.pkcs7.fill(p, v))} == Con{B.byte(v), _} : List<&2, U32>}
      {==}

def pk.drop_fill(+k: Nat, +v: U32) -> {B.drop(k, P.pkcs7.fill(1n+k, v)) == Con{v, Nil{}} : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      pk.drop_fill(kp, v)

# BEGIN GENERATED by gen/pkcs7_proof.py: bits
# a byte's byte is itself
def pk.bb(u: U32) -> {B.byte(B.byte(u)) == B.byte(u) : U32}:
  match u:
    case U32{WCon{u0, WCon{u1, WCon{u2, WCon{u3, WCon{u4, WCon{u5, WCon{u6, WCon{u7, WCon{u8, WCon{u9, WCon{u10, WCon{u11, WCon{u12, WCon{u13, WCon{u14, WCon{u15, WCon{u16, WCon{u17, WCon{u18, WCon{u19, WCon{u20, WCon{u21, WCon{u22, WCon{u23, WCon{u24, WCon{u25, WCon{u26, WCon{u27, WCon{u28, WCon{u29, WCon{u30, WCon{u31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}
# END GENERATED: bits

# a word XOR itself is zero, bit by bit
def pk.wself(+n: Nat, w: Word(n)) -> {Word.xor(n, w, w) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{h, t}:
          match h:
            case False{}:
              %pk.wself(p, t) : {WCon{False{}, Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
              {==}
            case True{}:
              %pk.wself(p, t) : {WCon{False{}, Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
              {==}

def pk.xor_self(+a: U32) -> {U32.xor(a, a) == 0 : U32}:
  match a:
    case U32{x}:
      %Equal.sym(Word(32n), Word.xor(32n, x, x), Word.zero(32n), pk.wself(32n, x)) : {U32{_} == 0 : U32}
      {==}

# the padding's difference from its own byte is 0
def pk.diff_fill(+n: Nat, +u: U32) -> {P.pkcs7.diff(P.pkcs7.fill(n, B.byte(u)), B.byte(u), 0) == 0 : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, B.byte(B.byte(u)), B.byte(u), pk.bb(u)) : {P.pkcs7.diff(P.pkcs7.fill(p, B.byte(u)), B.byte(u), U32.or(0, U32.xor(_, B.byte(u)))) == 0 : U32}
      %Equal.sym(U32, U32.xor(B.byte(u), B.byte(u)), 0, pk.xor_self(B.byte(u))) : {P.pkcs7.diff(P.pkcs7.fill(p, B.byte(u)), B.byte(u), U32.or(0, _)) == 0 : U32}
      pk.diff_fill(p, u)

# BEGIN GENERATED by gen/pkcs7_proof.py: u8
# the values 224 to 255
def pk.u8.c7(r: Nat) -> {Nat.is_le(224n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(224n+r))) == 224n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  h => pk.absurd({U32.to_nat(B.byte(U32.from_nat(256n+r32))) == 256n+r32 : Nat}, h)

# the values 192 to 223
def pk.u8.c6(r: Nat) -> {Nat.is_le(192n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(192n+r))) == 192n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c7(r32)

# the values 160 to 191
def pk.u8.c5(r: Nat) -> {Nat.is_le(160n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(160n+r))) == 160n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c6(r32)

# the values 128 to 159
def pk.u8.c4(r: Nat) -> {Nat.is_le(128n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(128n+r))) == 128n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c5(r32)

# the values 96 to 127
def pk.u8.c3(r: Nat) -> {Nat.is_le(96n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(96n+r))) == 96n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c4(r32)

# the values 64 to 95
def pk.u8.c2(r: Nat) -> {Nat.is_le(64n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(64n+r))) == 64n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c3(r32)

# the values 32 to 63
def pk.u8.c1(r: Nat) -> {Nat.is_le(32n+r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(32n+r))) == 32n+r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c2(r32)

# the values 0 to 31
def pk.u8(r: Nat) -> {Nat.is_le(r, 255n) == True{} : Bool} -> {U32.to_nat(B.byte(U32.from_nat(r))) == r : Nat}:
  match r:
    case 0n:
      h => {==}
    case 1n+r1:
      match r1:
        case 0n:
          h => {==}
        case 1n+r2:
          match r2:
            case 0n:
              h => {==}
            case 1n+r3:
              match r3:
                case 0n:
                  h => {==}
                case 1n+r4:
                  match r4:
                    case 0n:
                      h => {==}
                    case 1n+r5:
                      match r5:
                        case 0n:
                          h => {==}
                        case 1n+r6:
                          match r6:
                            case 0n:
                              h => {==}
                            case 1n+r7:
                              match r7:
                                case 0n:
                                  h => {==}
                                case 1n+r8:
                                  match r8:
                                    case 0n:
                                      h => {==}
                                    case 1n+r9:
                                      match r9:
                                        case 0n:
                                          h => {==}
                                        case 1n+r10:
                                          match r10:
                                            case 0n:
                                              h => {==}
                                            case 1n+r11:
                                              match r11:
                                                case 0n:
                                                  h => {==}
                                                case 1n+r12:
                                                  match r12:
                                                    case 0n:
                                                      h => {==}
                                                    case 1n+r13:
                                                      match r13:
                                                        case 0n:
                                                          h => {==}
                                                        case 1n+r14:
                                                          match r14:
                                                            case 0n:
                                                              h => {==}
                                                            case 1n+r15:
                                                              match r15:
                                                                case 0n:
                                                                  h => {==}
                                                                case 1n+r16:
                                                                  match r16:
                                                                    case 0n:
                                                                      h => {==}
                                                                    case 1n+r17:
                                                                      match r17:
                                                                        case 0n:
                                                                          h => {==}
                                                                        case 1n+r18:
                                                                          match r18:
                                                                            case 0n:
                                                                              h => {==}
                                                                            case 1n+r19:
                                                                              match r19:
                                                                                case 0n:
                                                                                  h => {==}
                                                                                case 1n+r20:
                                                                                  match r20:
                                                                                    case 0n:
                                                                                      h => {==}
                                                                                    case 1n+r21:
                                                                                      match r21:
                                                                                        case 0n:
                                                                                          h => {==}
                                                                                        case 1n+r22:
                                                                                          match r22:
                                                                                            case 0n:
                                                                                              h => {==}
                                                                                            case 1n+r23:
                                                                                              match r23:
                                                                                                case 0n:
                                                                                                  h => {==}
                                                                                                case 1n+r24:
                                                                                                  match r24:
                                                                                                    case 0n:
                                                                                                      h => {==}
                                                                                                    case 1n+r25:
                                                                                                      match r25:
                                                                                                        case 0n:
                                                                                                          h => {==}
                                                                                                        case 1n+r26:
                                                                                                          match r26:
                                                                                                            case 0n:
                                                                                                              h => {==}
                                                                                                            case 1n+r27:
                                                                                                              match r27:
                                                                                                                case 0n:
                                                                                                                  h => {==}
                                                                                                                case 1n+r28:
                                                                                                                  match r28:
                                                                                                                    case 0n:
                                                                                                                      h => {==}
                                                                                                                    case 1n+r29:
                                                                                                                      match r29:
                                                                                                                        case 0n:
                                                                                                                          h => {==}
                                                                                                                        case 1n+r30:
                                                                                                                          match r30:
                                                                                                                            case 0n:
                                                                                                                              h => {==}
                                                                                                                            case 1n+r31:
                                                                                                                              match r31:
                                                                                                                                case 0n:
                                                                                                                                  h => {==}
                                                                                                                                case 1n+r32:
                                                                                                                                  pk.u8.c1(r32)
# END GENERATED: u8

# The round trip

# Pkcs7.unpad's checks and its unpad.oct, with what they compute as
# arguments, so that each can be rewritten on its own
def pk.ug(+bs: Nat, +m: B.Octets, +n: Nat, +md: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    M.cm.check(Nat.is_lt(0n, n), M.CmTooShort{n})
    M.cm.check(Nat.is_eq(md, 0n), M.CmNotBlockMultiple{n})
    P.pkcs7.unpad.oct(bs, m, n)

def pk.k2(+bs: Nat, +m: B.Octets, +n: Nat, +p: Nat, le: Bool, +d: U32) -> Result<&2, &2, M.CmError, B.Octets>:
  P.pkcs7.strip(Bool.and(Nat.is_lt(0n, p), Bool.and(le, U32.is_eq(d, 0))), n, p, m)

def pk.k(+bs: Nat, +m: B.Octets, +n: Nat, +v: U32, +p: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  pk.k2(bs, m, n, p, Nat.is_le(p, bs), P.pkcs7.diff(B.Octets.to_list(B.Octets.drop(Nat.sub(n, p), m)), v, 0))

# the padding of 1 + p1 bytes
def pk.pad(+p1: Nat) -> B.Octets:
  B.Octets.of_list(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1)))

# its last byte, at L + p1 of m and it
def pk.at(+m: B.Octets, +p1: Nat) -> {B.Octets.at(B.Octets.append(m, pk.pad(p1)), Nat.add(B.Octets.len(m), p1)) == Some{B.byte(U32.from_nat(1n+p1))} : Maybe<&2, U32>}:
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.append(m, pk.pad(p1)), Nat.add(B.Octets.len(m), p1)), B.Octets.at(pk.pad(p1), p1), BL.octets_at_append_add(m, pk.pad(p1), p1)) : {_ == Some{B.byte(U32.from_nat(1n+p1))} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(pk.pad(p1), p1), B.at(B.Octets.to_list(pk.pad(p1)), p1), BL.octets_at_list(pk.pad(p1), p1)) : {_ == Some{B.byte(U32.from_nat(1n+p1))} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(pk.pad(p1)), B.mask(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1))), BL.octets_to_of(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1)))) : {B.at(_, p1) == Some{B.byte(U32.from_nat(1n+p1))} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1))), P.pkcs7.fill(1n+p1, B.byte(U32.from_nat(1n+p1))), pk.mask_fill(1n+p1, U32.from_nat(1n+p1))) : {B.at(_, p1) == Some{B.byte(U32.from_nat(1n+p1))} : Maybe<&2, U32>}
  %Equal.sym(List<&2, U32>, B.drop(p1, P.pkcs7.fill(1n+p1, B.byte(U32.from_nat(1n+p1)))), Con{B.byte(U32.from_nat(1n+p1)), Nil{}}, pk.drop_fill(p1, B.byte(U32.from_nat(1n+p1)))) : {B.at.head(_) == Some{B.byte(U32.from_nat(1n+p1))} : Maybe<&2, U32>}
  %pk.bb(U32.from_nat(1n+p1)) : {Some{B.byte(B.byte(U32.from_nat(1n+p1)))} == Some{_} : Maybe<&2, U32>}
  {==}

# the padded message's length
def pk.len(+m: B.Octets, +p1: Nat) -> {B.Octets.len(B.Octets.append(m, pk.pad(p1))) == 1n+Nat.add(B.Octets.len(m), p1) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(m, pk.pad(p1))), Nat.add(B.Octets.len(m), B.Octets.len(pk.pad(p1))), BL.octets_len_append(m, pk.pad(p1))) : {_ == 1n+Nat.add(B.Octets.len(m), p1) : Nat}
  %Equal.sym(Nat, B.Octets.len(pk.pad(p1)), B.len(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1))), BL.octets_len_of_list(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1)))) : {Nat.add(B.Octets.len(m), _) == 1n+Nat.add(B.Octets.len(m), p1) : Nat}
  %Equal.sym(Nat, B.len(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1))), 1n+p1, pk.fill_len(1n+p1, U32.from_nat(1n+p1))) : {Nat.add(B.Octets.len(m), _) == 1n+Nat.add(B.Octets.len(m), p1) : Nat}
  UL.nat_add_succ(B.Octets.len(m), p1)

# unpad.oct on m and a padding of 1 + p1 bytes (p1 below 255) gives m
def pk.oct(+bs: Nat, +m: B.Octets, +p1: Nat, hle: {Nat.is_le(1n+p1, bs) == True{} : Bool}, hb: {Nat.is_le(1n+p1, 255n) == True{} : Bool}) -> {P.pkcs7.unpad.oct(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}:
  +el = pk.add_sub(B.Octets.len(m), p1)
  # the last byte is the byte of 1 + p1
  %Equal.sym(Nat, Nat.sub(Nat.add(B.Octets.len(m), p1), 0n), Nat.add(B.Octets.len(m), p1), pk.sub_zero(Nat.add(B.Octets.len(m), p1))) : {pk.k(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), P.pkcs7.last(B.Octets.at(B.Octets.append(m, pk.pad(p1)), _), 0), U32.to_nat(P.pkcs7.last(B.Octets.at(B.Octets.append(m, pk.pad(p1)), _), 0))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.append(m, pk.pad(p1)), Nat.add(B.Octets.len(m), p1)), Some{B.byte(U32.from_nat(1n+p1))}, pk.at(m, p1)) : {pk.k(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), P.pkcs7.last(_, 0), U32.to_nat(P.pkcs7.last(_, 0))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # whose value is 1 + p1
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(1n+p1))), 1n+p1, pk.u8(1n+p1)(hb)) : {pk.k(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), B.byte(U32.from_nat(1n+p1)), _) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # at most the block size
  %Equal.sym(Bool, Nat.is_le(1n+p1, bs), True{}, hle) : {pk.k2(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), 1n+p1, _, P.pkcs7.diff(B.Octets.to_list(B.Octets.drop(Nat.sub(Nat.add(B.Octets.len(m), p1), p1), B.Octets.append(m, pk.pad(p1)))), B.byte(U32.from_nat(1n+p1)), 0)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the last 1 + p1 bytes are the padding
  %Equal.sym(Nat, Nat.sub(Nat.add(B.Octets.len(m), p1), p1), B.Octets.len(m), el) : {pk.k2(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), 1n+p1, True{}, P.pkcs7.diff(B.Octets.to_list(B.Octets.drop(_, B.Octets.append(m, pk.pad(p1)))), B.byte(U32.from_nat(1n+p1)), 0)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(m), B.Octets.append(m, pk.pad(p1))), pk.pad(p1), BL.octets_drop_append(m, pk.pad(p1))) : {pk.k2(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), 1n+p1, True{}, P.pkcs7.diff(B.Octets.to_list(_), B.byte(U32.from_nat(1n+p1)), 0)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(pk.pad(p1)), B.mask(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1))), BL.octets_to_of(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1)))) : {pk.k2(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), 1n+p1, True{}, P.pkcs7.diff(_, B.byte(U32.from_nat(1n+p1)), 0)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.mask(P.pkcs7.fill(1n+p1, U32.from_nat(1n+p1))), P.pkcs7.fill(1n+p1, B.byte(U32.from_nat(1n+p1))), pk.mask_fill(1n+p1, U32.from_nat(1n+p1))) : {pk.k2(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), 1n+p1, True{}, P.pkcs7.diff(_, B.byte(U32.from_nat(1n+p1)), 0)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # all of them the byte
  %Equal.sym(U32, P.pkcs7.diff(P.pkcs7.fill(1n+p1, B.byte(U32.from_nat(1n+p1))), B.byte(U32.from_nat(1n+p1)), 0), 0, pk.diff_fill(1n+p1, U32.from_nat(1n+p1))) : {pk.k2(bs, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), 1n+p1, True{}, _) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # so the first L bytes are kept
  %Equal.sym(Nat, Nat.sub(Nat.add(B.Octets.len(m), p1), p1), B.Octets.len(m), el) : {Done{B.Octets.take(_, B.Octets.append(m, pk.pad(p1)))} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(m), B.Octets.append(m, pk.pad(p1))), m, BL.octets_take_append(m, pk.pad(p1))) : {Done{_} == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  {==}

# the round trip for a block size 1 + q (q below 255) and a padding of
# 1 + p1 bytes, p1 <= q, that makes whole blocks
def pk.main2(+q: Nat, +m: B.Octets, +p1: Nat, +hle: {Nat.is_le(p1, q) == True{} : Bool}, hb: {Nat.is_le(1n+q, 255n) == True{} : Bool}, hm: {Nat.mod(1n+Nat.add(B.Octets.len(m), p1), 1n+q) == 0n : Nat}) -> {P.Pkcs7.unpad.go(True{}, 1n+q, B.Octets.append(m, pk.pad(p1))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(m, pk.pad(p1))), 1n+Nat.add(B.Octets.len(m), p1), pk.len(m, p1)) : {pk.ug(1n+q, B.Octets.append(m, pk.pad(p1)), _, Nat.mod(_, 1n+q)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  %Equal.sym(Nat, Nat.mod(1n+Nat.add(B.Octets.len(m), p1), 1n+q), 0n, hm) : {pk.ug(1n+q, B.Octets.append(m, pk.pad(p1)), 1n+Nat.add(B.Octets.len(m), p1), _) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  pk.oct(1n+q, m, p1, hle, pk.le_trans(1n+p1, 1n+q, 255n)(hle)(hb))

# 1 + L + (q - L mod (1 + q)) is a multiple of 1 + q
def pk.hm(+q: Nat, +m: B.Octets) -> {Nat.mod(1n+Nat.add(B.Octets.len(m), Nat.sub(q, Nat.mod(B.Octets.len(m), 1n+q))), 1n+q) == 0n : Nat}:
  +hs = pk.sub_succ(Nat.mod(B.Octets.len(m), 1n+q), q)(pk.mod_le(B.Octets.len(m), q, 0n, 0n, q)(UL.nat_add_zero(q)))
  %UL.nat_add_succ(B.Octets.len(m), Nat.sub(q, Nat.mod(B.Octets.len(m), 1n+q))) : {Nat.mod(_, 1n+q) == 0n : Nat}
  %hs : {Nat.mod(Nat.add(B.Octets.len(m), _), 1n+q) == 0n : Nat}
  pk.mod_pad(B.Octets.len(m), q, 0n, 0n, q)(UL.nat_add_zero(q))

def pk.main(+q: Nat, +m: B.Octets, +e: {Nat.is_lt(1n+q, 256n) == True{} : Bool}) -> {P.Pkcs7.unpad(1n+q, P.pkcs7.pad.oct(1n+q, m)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}:
  +hs = pk.sub_succ(Nat.mod(B.Octets.len(m), 1n+q), q)(pk.mod_le(B.Octets.len(m), q, 0n, 0n, q)(UL.nat_add_zero(q)))
  # the padding is 1 + (q - L mod (1 + q)) bytes
  %Equal.sym(Nat, Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), 1n+Nat.sub(q, Nat.mod(B.Octets.len(m), 1n+q)), hs) : {P.Pkcs7.unpad(1n+q, B.Octets.append(m, B.Octets.of_list(P.pkcs7.fill(_, U32.from_nat(_))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # the block size is one the padding takes
  %Equal.sym(Bool, Nat.is_lt(1n+q, 256n), True{}, e) : {P.Pkcs7.unpad.go(_, 1n+q, B.Octets.append(m, pk.pad(Nat.sub(q, Nat.mod(B.Octets.len(m), 1n+q))))) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}
  # and the padded length is a multiple of it (pk.hm)
  pk.main2(q, m, Nat.sub(q, Nat.mod(B.Octets.len(m), 1n+q)), pk.le_sub(q, Nat.mod(B.Octets.len(m), 1n+q)), pk.lt_le(1n+q, 255n)(e), pk.hm(q, m))

def pk.rt(ok: Bool, +bs: Nat, +m: B.Octets) -> {P.pkcs7.size_ok(bs) == ok : Bool} -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, P.Pkcs7.pad.go(ok, bs, m), c => P.Pkcs7.unpad(bs, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => m, P.Pkcs7.pad.go(ok, bs, m)) : Result<&2, &2, M.CmError, B.Octets>}:
  match ok:
    case False{}:
      e => {==}
    case True{}:
      match bs:
        case 0n:
          e => pk.absurd({P.Pkcs7.unpad(0n, P.pkcs7.pad.oct(0n, m)) == Done{m} : Result<&2, &2, M.CmError, B.Octets>}, e)
        case 1n+q:
          e => pk.main(q, m, e)

def Laws.pkcs7_round_trip(bs, m):
  pk.rt(P.pkcs7.size_ok(bs), bs, m)({==})

# Padding gives whole blocks: L + p, p = 1 + q - L mod (1 + q), is a
# multiple of 1 + q (pk.mod_pad)

def pk.blocks(ok: Bool, +bs: Nat, +m: B.Octets) -> {P.pkcs7.size_ok(bs) == ok : Bool} -> {Result.map(&2, &2, M.CmError, B.Octets, Nat, c => Nat.mod(B.Octets.len(c), bs), P.Pkcs7.pad.go(ok, bs, m)) == Result.map(&2, &2, M.CmError, B.Octets, Nat, c => 0n, P.Pkcs7.pad.go(ok, bs, m)) : Result<&2, &2, M.CmError, Nat>}:
  match ok:
    case False{}:
      e => {==}
    case True{}:
      match bs:
        case 0n:
          e => pk.absurd({Done{Nat.mod(B.Octets.len(P.pkcs7.pad.oct(0n, m)), 0n)} == Done{0n} : Result<&2, &2, M.CmError, Nat>}, e)
        case 1n+q:
          e => %Equal.sym(Nat, B.Octets.len(P.pkcs7.pad.oct(1n+q, m)), Nat.add(B.Octets.len(m), B.Octets.len(B.Octets.of_list(P.pkcs7.fill(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q))))))), BL.octets_len_append(m, B.Octets.of_list(P.pkcs7.fill(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q))))))) : {Done{Nat.mod(_, 1n+q)} == Done{0n} : Result<&2, &2, M.CmError, Nat>}
            %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(P.pkcs7.fill(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)))))), B.len(P.pkcs7.fill(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q))))), BL.octets_len_of_list(P.pkcs7.fill(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)))))) : {Done{Nat.mod(Nat.add(B.Octets.len(m), _), 1n+q)} == Done{0n} : Result<&2, &2, M.CmError, Nat>}
            %Equal.sym(Nat, B.len(P.pkcs7.fill(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q))))), Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), pk.fill_len(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q)), U32.from_nat(Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q))))) : {Done{Nat.mod(Nat.add(B.Octets.len(m), _), 1n+q)} == Done{0n} : Result<&2, &2, M.CmError, Nat>}
            %Equal.sym(Nat, Nat.mod(Nat.add(B.Octets.len(m), Nat.sub(1n+q, Nat.mod(B.Octets.len(m), 1n+q))), 1n+q), 0n, pk.mod_pad(B.Octets.len(m), q, 0n, 0n, q)(UL.nat_add_zero(q))) : {Done{_} == Done{0n} : Result<&2, &2, M.CmError, Nat>}
            {==}

def Laws.pkcs7_pad_blocks(bs, m):
  pk.blocks(P.pkcs7.size_ok(bs), bs, m)({==})
