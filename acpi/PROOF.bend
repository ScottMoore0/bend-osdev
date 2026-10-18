import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./error.bend as E
import ./aml_pkglength.bend as K
import ./aml_name.bend as N
import ./header.bend as H
import ./checksum.bend as C
import ./fields.bend as F
import ./rsdp.bend as P
import ./registry.bend as R
import ./aml_value.bend as V
import ./aml_host.bend as Hs
import ./aml_interp.bend as I
import ./aml.bend as A
import ./aml_term.bend as T
import ./aml_device.bend as Dv
import ./mcfg.bend as Mc
import ./example.bend as X
import ./LAWS.bend as Laws

# The proofs reach Octets only through bytes' interface laws (octets_to_of,
# octets_of_to, octets_append_list, octets_len_list, octets_split_at_append,
# octets_le32_round_trip) and its list layer (B.append, B.mask, B.byte),
# and W64 only through word64's public defs. The PkgLength proof and the
# field lengths compute through B.mask and B.le32 on words split into their
# bits, as bytes' own proofs do.

# Contradictions

def bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ft_absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

# PkgLength: with the value split into its 32 bits, and the bits above the
# highest one set taken one by one from the top, the encoder's choice of
# form and the decoder's reading compute; values of 2^28 and up are refused
# by the hypothesis

def pk_abs(+v: U32, +r: List<&2, U32>, e: Empty) -> {K.pk.pub(K.pk.dec(B.append(B.mask(K.pk.enc(v)), r))) == Done{K.AmlPkgLen{v, B.Octets.of_list(r)}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}:
  Empty.absurd({K.pk.pub(K.pk.dec(B.append(B.mask(K.pk.enc(v)), r))) == Done{K.AmlPkgLen{v, B.Octets.of_list(r)}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}, e)

# the bits from the top down, so that they are matched in binder order
def pk_bits(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool, +r: List<&2, U32>, +fits: {K.AmlPkgLength.fits(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) == True{} : Bool}) -> {K.pk.pub(K.pk.dec(B.append(B.mask(K.pk.enc(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})), r))) == Done{K.AmlPkgLen{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, B.Octets.of_list(r)}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}:
  match b31:
    case True{}:
      pk_abs(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r, ft_absurd(fits))
    case False{}:
      match b30:
        case True{}:
          pk_abs(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r, ft_absurd(fits))
        case False{}:
          match b29:
            case True{}:
              pk_abs(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r, ft_absurd(fits))
            case False{}:
              match b28:
                case True{}:
                  pk_abs(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r, ft_absurd(fits))
                case False{}:
                  match b27:
                    case True{}:
                      {==}
                    case False{}:
                      match b26:
                        case True{}:
                          {==}
                        case False{}:
                          match b25:
                            case True{}:
                              {==}
                            case False{}:
                              match b24:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b23:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  {==}
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      {==}
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          {==}
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              {==}
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  {==}
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      {==}
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          {==}
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              {==}
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  {==}
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      {==}
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          {==}
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              {==}
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  {==}
                                                                                                case False{}:
                                                                                                  match b7:
                                                                                                    case True{}:
                                                                                                      {==}
                                                                                                    case False{}:
                                                                                                      match b6:
                                                                                                        case True{}:
                                                                                                          {==}
                                                                                                        case False{}:
                                                                                                          {==}

def pk_rt(+v: U32, +r: List<&2, U32>, +fits: {K.AmlPkgLength.fits(v) == True{} : Bool}) -> {K.pk.pub(K.pk.dec(B.append(B.mask(K.pk.enc(v)), r))) == Done{K.AmlPkgLen{v, B.Octets.of_list(r)}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}:
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      pk_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, r, fits)

# The SegCount of a MultiNamePath: a count below 256 survives being written
# as a byte, by a chain of lemmas cnt.d (for k + d, d from 0 to 256), each a
# closed computation or a step to the next

def cnt_abs(+k: Nat, e: Empty) -> {U32.to_nat(B.byte(U32.from_nat(k))) == k : Nat}:
  Empty.absurd({U32.to_nat(B.byte(U32.from_nat(k))) == k : Nat}, e)

def cnt.d256(+k: Nat, +lt: {Nat.is_lt(Nat.add(256n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(256n, k)))) == Nat.add(256n, k) : Nat}:
  match k:
    case 0n:
      cnt_abs(Nat.add(256n, 0n), ft_absurd(lt))
    case 1n+p:
      cnt_abs(Nat.add(256n, 1n+p), ft_absurd(lt))

def cnt.d255(+k: Nat, +lt: {Nat.is_lt(Nat.add(255n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(255n, k)))) == Nat.add(255n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d256(p, lt)

def cnt.d254(+k: Nat, +lt: {Nat.is_lt(Nat.add(254n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(254n, k)))) == Nat.add(254n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d255(p, lt)

def cnt.d253(+k: Nat, +lt: {Nat.is_lt(Nat.add(253n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(253n, k)))) == Nat.add(253n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d254(p, lt)

def cnt.d252(+k: Nat, +lt: {Nat.is_lt(Nat.add(252n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(252n, k)))) == Nat.add(252n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d253(p, lt)

def cnt.d251(+k: Nat, +lt: {Nat.is_lt(Nat.add(251n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(251n, k)))) == Nat.add(251n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d252(p, lt)

def cnt.d250(+k: Nat, +lt: {Nat.is_lt(Nat.add(250n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(250n, k)))) == Nat.add(250n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d251(p, lt)

def cnt.d249(+k: Nat, +lt: {Nat.is_lt(Nat.add(249n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(249n, k)))) == Nat.add(249n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d250(p, lt)

def cnt.d248(+k: Nat, +lt: {Nat.is_lt(Nat.add(248n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(248n, k)))) == Nat.add(248n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d249(p, lt)

def cnt.d247(+k: Nat, +lt: {Nat.is_lt(Nat.add(247n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(247n, k)))) == Nat.add(247n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d248(p, lt)

def cnt.d246(+k: Nat, +lt: {Nat.is_lt(Nat.add(246n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(246n, k)))) == Nat.add(246n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d247(p, lt)

def cnt.d245(+k: Nat, +lt: {Nat.is_lt(Nat.add(245n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(245n, k)))) == Nat.add(245n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d246(p, lt)

def cnt.d244(+k: Nat, +lt: {Nat.is_lt(Nat.add(244n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(244n, k)))) == Nat.add(244n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d245(p, lt)

def cnt.d243(+k: Nat, +lt: {Nat.is_lt(Nat.add(243n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(243n, k)))) == Nat.add(243n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d244(p, lt)

def cnt.d242(+k: Nat, +lt: {Nat.is_lt(Nat.add(242n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(242n, k)))) == Nat.add(242n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d243(p, lt)

def cnt.d241(+k: Nat, +lt: {Nat.is_lt(Nat.add(241n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(241n, k)))) == Nat.add(241n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d242(p, lt)

def cnt.d240(+k: Nat, +lt: {Nat.is_lt(Nat.add(240n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(240n, k)))) == Nat.add(240n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d241(p, lt)

def cnt.d239(+k: Nat, +lt: {Nat.is_lt(Nat.add(239n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(239n, k)))) == Nat.add(239n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d240(p, lt)

def cnt.d238(+k: Nat, +lt: {Nat.is_lt(Nat.add(238n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(238n, k)))) == Nat.add(238n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d239(p, lt)

def cnt.d237(+k: Nat, +lt: {Nat.is_lt(Nat.add(237n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(237n, k)))) == Nat.add(237n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d238(p, lt)

def cnt.d236(+k: Nat, +lt: {Nat.is_lt(Nat.add(236n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(236n, k)))) == Nat.add(236n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d237(p, lt)

def cnt.d235(+k: Nat, +lt: {Nat.is_lt(Nat.add(235n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(235n, k)))) == Nat.add(235n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d236(p, lt)

def cnt.d234(+k: Nat, +lt: {Nat.is_lt(Nat.add(234n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(234n, k)))) == Nat.add(234n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d235(p, lt)

def cnt.d233(+k: Nat, +lt: {Nat.is_lt(Nat.add(233n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(233n, k)))) == Nat.add(233n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d234(p, lt)

def cnt.d232(+k: Nat, +lt: {Nat.is_lt(Nat.add(232n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(232n, k)))) == Nat.add(232n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d233(p, lt)

def cnt.d231(+k: Nat, +lt: {Nat.is_lt(Nat.add(231n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(231n, k)))) == Nat.add(231n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d232(p, lt)

def cnt.d230(+k: Nat, +lt: {Nat.is_lt(Nat.add(230n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(230n, k)))) == Nat.add(230n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d231(p, lt)

def cnt.d229(+k: Nat, +lt: {Nat.is_lt(Nat.add(229n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(229n, k)))) == Nat.add(229n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d230(p, lt)

def cnt.d228(+k: Nat, +lt: {Nat.is_lt(Nat.add(228n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(228n, k)))) == Nat.add(228n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d229(p, lt)

def cnt.d227(+k: Nat, +lt: {Nat.is_lt(Nat.add(227n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(227n, k)))) == Nat.add(227n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d228(p, lt)

def cnt.d226(+k: Nat, +lt: {Nat.is_lt(Nat.add(226n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(226n, k)))) == Nat.add(226n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d227(p, lt)

def cnt.d225(+k: Nat, +lt: {Nat.is_lt(Nat.add(225n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(225n, k)))) == Nat.add(225n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d226(p, lt)

def cnt.d224(+k: Nat, +lt: {Nat.is_lt(Nat.add(224n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(224n, k)))) == Nat.add(224n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d225(p, lt)

def cnt.d223(+k: Nat, +lt: {Nat.is_lt(Nat.add(223n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(223n, k)))) == Nat.add(223n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d224(p, lt)

def cnt.d222(+k: Nat, +lt: {Nat.is_lt(Nat.add(222n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(222n, k)))) == Nat.add(222n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d223(p, lt)

def cnt.d221(+k: Nat, +lt: {Nat.is_lt(Nat.add(221n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(221n, k)))) == Nat.add(221n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d222(p, lt)

def cnt.d220(+k: Nat, +lt: {Nat.is_lt(Nat.add(220n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(220n, k)))) == Nat.add(220n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d221(p, lt)

def cnt.d219(+k: Nat, +lt: {Nat.is_lt(Nat.add(219n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(219n, k)))) == Nat.add(219n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d220(p, lt)

def cnt.d218(+k: Nat, +lt: {Nat.is_lt(Nat.add(218n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(218n, k)))) == Nat.add(218n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d219(p, lt)

def cnt.d217(+k: Nat, +lt: {Nat.is_lt(Nat.add(217n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(217n, k)))) == Nat.add(217n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d218(p, lt)

def cnt.d216(+k: Nat, +lt: {Nat.is_lt(Nat.add(216n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(216n, k)))) == Nat.add(216n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d217(p, lt)

def cnt.d215(+k: Nat, +lt: {Nat.is_lt(Nat.add(215n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(215n, k)))) == Nat.add(215n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d216(p, lt)

def cnt.d214(+k: Nat, +lt: {Nat.is_lt(Nat.add(214n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(214n, k)))) == Nat.add(214n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d215(p, lt)

def cnt.d213(+k: Nat, +lt: {Nat.is_lt(Nat.add(213n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(213n, k)))) == Nat.add(213n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d214(p, lt)

def cnt.d212(+k: Nat, +lt: {Nat.is_lt(Nat.add(212n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(212n, k)))) == Nat.add(212n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d213(p, lt)

def cnt.d211(+k: Nat, +lt: {Nat.is_lt(Nat.add(211n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(211n, k)))) == Nat.add(211n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d212(p, lt)

def cnt.d210(+k: Nat, +lt: {Nat.is_lt(Nat.add(210n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(210n, k)))) == Nat.add(210n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d211(p, lt)

def cnt.d209(+k: Nat, +lt: {Nat.is_lt(Nat.add(209n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(209n, k)))) == Nat.add(209n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d210(p, lt)

def cnt.d208(+k: Nat, +lt: {Nat.is_lt(Nat.add(208n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(208n, k)))) == Nat.add(208n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d209(p, lt)

def cnt.d207(+k: Nat, +lt: {Nat.is_lt(Nat.add(207n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(207n, k)))) == Nat.add(207n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d208(p, lt)

def cnt.d206(+k: Nat, +lt: {Nat.is_lt(Nat.add(206n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(206n, k)))) == Nat.add(206n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d207(p, lt)

def cnt.d205(+k: Nat, +lt: {Nat.is_lt(Nat.add(205n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(205n, k)))) == Nat.add(205n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d206(p, lt)

def cnt.d204(+k: Nat, +lt: {Nat.is_lt(Nat.add(204n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(204n, k)))) == Nat.add(204n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d205(p, lt)

def cnt.d203(+k: Nat, +lt: {Nat.is_lt(Nat.add(203n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(203n, k)))) == Nat.add(203n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d204(p, lt)

def cnt.d202(+k: Nat, +lt: {Nat.is_lt(Nat.add(202n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(202n, k)))) == Nat.add(202n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d203(p, lt)

def cnt.d201(+k: Nat, +lt: {Nat.is_lt(Nat.add(201n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(201n, k)))) == Nat.add(201n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d202(p, lt)

def cnt.d200(+k: Nat, +lt: {Nat.is_lt(Nat.add(200n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(200n, k)))) == Nat.add(200n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d201(p, lt)

def cnt.d199(+k: Nat, +lt: {Nat.is_lt(Nat.add(199n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(199n, k)))) == Nat.add(199n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d200(p, lt)

def cnt.d198(+k: Nat, +lt: {Nat.is_lt(Nat.add(198n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(198n, k)))) == Nat.add(198n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d199(p, lt)

def cnt.d197(+k: Nat, +lt: {Nat.is_lt(Nat.add(197n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(197n, k)))) == Nat.add(197n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d198(p, lt)

def cnt.d196(+k: Nat, +lt: {Nat.is_lt(Nat.add(196n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(196n, k)))) == Nat.add(196n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d197(p, lt)

def cnt.d195(+k: Nat, +lt: {Nat.is_lt(Nat.add(195n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(195n, k)))) == Nat.add(195n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d196(p, lt)

def cnt.d194(+k: Nat, +lt: {Nat.is_lt(Nat.add(194n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(194n, k)))) == Nat.add(194n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d195(p, lt)

def cnt.d193(+k: Nat, +lt: {Nat.is_lt(Nat.add(193n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(193n, k)))) == Nat.add(193n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d194(p, lt)

def cnt.d192(+k: Nat, +lt: {Nat.is_lt(Nat.add(192n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(192n, k)))) == Nat.add(192n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d193(p, lt)

def cnt.d191(+k: Nat, +lt: {Nat.is_lt(Nat.add(191n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(191n, k)))) == Nat.add(191n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d192(p, lt)

def cnt.d190(+k: Nat, +lt: {Nat.is_lt(Nat.add(190n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(190n, k)))) == Nat.add(190n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d191(p, lt)

def cnt.d189(+k: Nat, +lt: {Nat.is_lt(Nat.add(189n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(189n, k)))) == Nat.add(189n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d190(p, lt)

def cnt.d188(+k: Nat, +lt: {Nat.is_lt(Nat.add(188n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(188n, k)))) == Nat.add(188n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d189(p, lt)

def cnt.d187(+k: Nat, +lt: {Nat.is_lt(Nat.add(187n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(187n, k)))) == Nat.add(187n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d188(p, lt)

def cnt.d186(+k: Nat, +lt: {Nat.is_lt(Nat.add(186n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(186n, k)))) == Nat.add(186n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d187(p, lt)

def cnt.d185(+k: Nat, +lt: {Nat.is_lt(Nat.add(185n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(185n, k)))) == Nat.add(185n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d186(p, lt)

def cnt.d184(+k: Nat, +lt: {Nat.is_lt(Nat.add(184n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(184n, k)))) == Nat.add(184n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d185(p, lt)

def cnt.d183(+k: Nat, +lt: {Nat.is_lt(Nat.add(183n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(183n, k)))) == Nat.add(183n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d184(p, lt)

def cnt.d182(+k: Nat, +lt: {Nat.is_lt(Nat.add(182n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(182n, k)))) == Nat.add(182n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d183(p, lt)

def cnt.d181(+k: Nat, +lt: {Nat.is_lt(Nat.add(181n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(181n, k)))) == Nat.add(181n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d182(p, lt)

def cnt.d180(+k: Nat, +lt: {Nat.is_lt(Nat.add(180n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(180n, k)))) == Nat.add(180n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d181(p, lt)

def cnt.d179(+k: Nat, +lt: {Nat.is_lt(Nat.add(179n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(179n, k)))) == Nat.add(179n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d180(p, lt)

def cnt.d178(+k: Nat, +lt: {Nat.is_lt(Nat.add(178n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(178n, k)))) == Nat.add(178n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d179(p, lt)

def cnt.d177(+k: Nat, +lt: {Nat.is_lt(Nat.add(177n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(177n, k)))) == Nat.add(177n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d178(p, lt)

def cnt.d176(+k: Nat, +lt: {Nat.is_lt(Nat.add(176n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(176n, k)))) == Nat.add(176n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d177(p, lt)

def cnt.d175(+k: Nat, +lt: {Nat.is_lt(Nat.add(175n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(175n, k)))) == Nat.add(175n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d176(p, lt)

def cnt.d174(+k: Nat, +lt: {Nat.is_lt(Nat.add(174n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(174n, k)))) == Nat.add(174n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d175(p, lt)

def cnt.d173(+k: Nat, +lt: {Nat.is_lt(Nat.add(173n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(173n, k)))) == Nat.add(173n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d174(p, lt)

def cnt.d172(+k: Nat, +lt: {Nat.is_lt(Nat.add(172n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(172n, k)))) == Nat.add(172n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d173(p, lt)

def cnt.d171(+k: Nat, +lt: {Nat.is_lt(Nat.add(171n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(171n, k)))) == Nat.add(171n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d172(p, lt)

def cnt.d170(+k: Nat, +lt: {Nat.is_lt(Nat.add(170n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(170n, k)))) == Nat.add(170n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d171(p, lt)

def cnt.d169(+k: Nat, +lt: {Nat.is_lt(Nat.add(169n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(169n, k)))) == Nat.add(169n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d170(p, lt)

def cnt.d168(+k: Nat, +lt: {Nat.is_lt(Nat.add(168n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(168n, k)))) == Nat.add(168n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d169(p, lt)

def cnt.d167(+k: Nat, +lt: {Nat.is_lt(Nat.add(167n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(167n, k)))) == Nat.add(167n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d168(p, lt)

def cnt.d166(+k: Nat, +lt: {Nat.is_lt(Nat.add(166n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(166n, k)))) == Nat.add(166n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d167(p, lt)

def cnt.d165(+k: Nat, +lt: {Nat.is_lt(Nat.add(165n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(165n, k)))) == Nat.add(165n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d166(p, lt)

def cnt.d164(+k: Nat, +lt: {Nat.is_lt(Nat.add(164n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(164n, k)))) == Nat.add(164n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d165(p, lt)

def cnt.d163(+k: Nat, +lt: {Nat.is_lt(Nat.add(163n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(163n, k)))) == Nat.add(163n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d164(p, lt)

def cnt.d162(+k: Nat, +lt: {Nat.is_lt(Nat.add(162n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(162n, k)))) == Nat.add(162n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d163(p, lt)

def cnt.d161(+k: Nat, +lt: {Nat.is_lt(Nat.add(161n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(161n, k)))) == Nat.add(161n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d162(p, lt)

def cnt.d160(+k: Nat, +lt: {Nat.is_lt(Nat.add(160n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(160n, k)))) == Nat.add(160n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d161(p, lt)

def cnt.d159(+k: Nat, +lt: {Nat.is_lt(Nat.add(159n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(159n, k)))) == Nat.add(159n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d160(p, lt)

def cnt.d158(+k: Nat, +lt: {Nat.is_lt(Nat.add(158n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(158n, k)))) == Nat.add(158n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d159(p, lt)

def cnt.d157(+k: Nat, +lt: {Nat.is_lt(Nat.add(157n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(157n, k)))) == Nat.add(157n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d158(p, lt)

def cnt.d156(+k: Nat, +lt: {Nat.is_lt(Nat.add(156n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(156n, k)))) == Nat.add(156n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d157(p, lt)

def cnt.d155(+k: Nat, +lt: {Nat.is_lt(Nat.add(155n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(155n, k)))) == Nat.add(155n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d156(p, lt)

def cnt.d154(+k: Nat, +lt: {Nat.is_lt(Nat.add(154n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(154n, k)))) == Nat.add(154n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d155(p, lt)

def cnt.d153(+k: Nat, +lt: {Nat.is_lt(Nat.add(153n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(153n, k)))) == Nat.add(153n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d154(p, lt)

def cnt.d152(+k: Nat, +lt: {Nat.is_lt(Nat.add(152n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(152n, k)))) == Nat.add(152n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d153(p, lt)

def cnt.d151(+k: Nat, +lt: {Nat.is_lt(Nat.add(151n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(151n, k)))) == Nat.add(151n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d152(p, lt)

def cnt.d150(+k: Nat, +lt: {Nat.is_lt(Nat.add(150n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(150n, k)))) == Nat.add(150n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d151(p, lt)

def cnt.d149(+k: Nat, +lt: {Nat.is_lt(Nat.add(149n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(149n, k)))) == Nat.add(149n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d150(p, lt)

def cnt.d148(+k: Nat, +lt: {Nat.is_lt(Nat.add(148n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(148n, k)))) == Nat.add(148n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d149(p, lt)

def cnt.d147(+k: Nat, +lt: {Nat.is_lt(Nat.add(147n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(147n, k)))) == Nat.add(147n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d148(p, lt)

def cnt.d146(+k: Nat, +lt: {Nat.is_lt(Nat.add(146n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(146n, k)))) == Nat.add(146n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d147(p, lt)

def cnt.d145(+k: Nat, +lt: {Nat.is_lt(Nat.add(145n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(145n, k)))) == Nat.add(145n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d146(p, lt)

def cnt.d144(+k: Nat, +lt: {Nat.is_lt(Nat.add(144n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(144n, k)))) == Nat.add(144n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d145(p, lt)

def cnt.d143(+k: Nat, +lt: {Nat.is_lt(Nat.add(143n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(143n, k)))) == Nat.add(143n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d144(p, lt)

def cnt.d142(+k: Nat, +lt: {Nat.is_lt(Nat.add(142n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(142n, k)))) == Nat.add(142n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d143(p, lt)

def cnt.d141(+k: Nat, +lt: {Nat.is_lt(Nat.add(141n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(141n, k)))) == Nat.add(141n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d142(p, lt)

def cnt.d140(+k: Nat, +lt: {Nat.is_lt(Nat.add(140n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(140n, k)))) == Nat.add(140n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d141(p, lt)

def cnt.d139(+k: Nat, +lt: {Nat.is_lt(Nat.add(139n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(139n, k)))) == Nat.add(139n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d140(p, lt)

def cnt.d138(+k: Nat, +lt: {Nat.is_lt(Nat.add(138n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(138n, k)))) == Nat.add(138n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d139(p, lt)

def cnt.d137(+k: Nat, +lt: {Nat.is_lt(Nat.add(137n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(137n, k)))) == Nat.add(137n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d138(p, lt)

def cnt.d136(+k: Nat, +lt: {Nat.is_lt(Nat.add(136n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(136n, k)))) == Nat.add(136n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d137(p, lt)

def cnt.d135(+k: Nat, +lt: {Nat.is_lt(Nat.add(135n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(135n, k)))) == Nat.add(135n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d136(p, lt)

def cnt.d134(+k: Nat, +lt: {Nat.is_lt(Nat.add(134n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(134n, k)))) == Nat.add(134n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d135(p, lt)

def cnt.d133(+k: Nat, +lt: {Nat.is_lt(Nat.add(133n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(133n, k)))) == Nat.add(133n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d134(p, lt)

def cnt.d132(+k: Nat, +lt: {Nat.is_lt(Nat.add(132n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(132n, k)))) == Nat.add(132n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d133(p, lt)

def cnt.d131(+k: Nat, +lt: {Nat.is_lt(Nat.add(131n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(131n, k)))) == Nat.add(131n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d132(p, lt)

def cnt.d130(+k: Nat, +lt: {Nat.is_lt(Nat.add(130n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(130n, k)))) == Nat.add(130n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d131(p, lt)

def cnt.d129(+k: Nat, +lt: {Nat.is_lt(Nat.add(129n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(129n, k)))) == Nat.add(129n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d130(p, lt)

def cnt.d128(+k: Nat, +lt: {Nat.is_lt(Nat.add(128n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(128n, k)))) == Nat.add(128n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d129(p, lt)

def cnt.d127(+k: Nat, +lt: {Nat.is_lt(Nat.add(127n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(127n, k)))) == Nat.add(127n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d128(p, lt)

def cnt.d126(+k: Nat, +lt: {Nat.is_lt(Nat.add(126n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(126n, k)))) == Nat.add(126n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d127(p, lt)

def cnt.d125(+k: Nat, +lt: {Nat.is_lt(Nat.add(125n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(125n, k)))) == Nat.add(125n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d126(p, lt)

def cnt.d124(+k: Nat, +lt: {Nat.is_lt(Nat.add(124n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(124n, k)))) == Nat.add(124n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d125(p, lt)

def cnt.d123(+k: Nat, +lt: {Nat.is_lt(Nat.add(123n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(123n, k)))) == Nat.add(123n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d124(p, lt)

def cnt.d122(+k: Nat, +lt: {Nat.is_lt(Nat.add(122n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(122n, k)))) == Nat.add(122n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d123(p, lt)

def cnt.d121(+k: Nat, +lt: {Nat.is_lt(Nat.add(121n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(121n, k)))) == Nat.add(121n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d122(p, lt)

def cnt.d120(+k: Nat, +lt: {Nat.is_lt(Nat.add(120n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(120n, k)))) == Nat.add(120n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d121(p, lt)

def cnt.d119(+k: Nat, +lt: {Nat.is_lt(Nat.add(119n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(119n, k)))) == Nat.add(119n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d120(p, lt)

def cnt.d118(+k: Nat, +lt: {Nat.is_lt(Nat.add(118n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(118n, k)))) == Nat.add(118n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d119(p, lt)

def cnt.d117(+k: Nat, +lt: {Nat.is_lt(Nat.add(117n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(117n, k)))) == Nat.add(117n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d118(p, lt)

def cnt.d116(+k: Nat, +lt: {Nat.is_lt(Nat.add(116n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(116n, k)))) == Nat.add(116n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d117(p, lt)

def cnt.d115(+k: Nat, +lt: {Nat.is_lt(Nat.add(115n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(115n, k)))) == Nat.add(115n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d116(p, lt)

def cnt.d114(+k: Nat, +lt: {Nat.is_lt(Nat.add(114n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(114n, k)))) == Nat.add(114n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d115(p, lt)

def cnt.d113(+k: Nat, +lt: {Nat.is_lt(Nat.add(113n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(113n, k)))) == Nat.add(113n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d114(p, lt)

def cnt.d112(+k: Nat, +lt: {Nat.is_lt(Nat.add(112n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(112n, k)))) == Nat.add(112n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d113(p, lt)

def cnt.d111(+k: Nat, +lt: {Nat.is_lt(Nat.add(111n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(111n, k)))) == Nat.add(111n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d112(p, lt)

def cnt.d110(+k: Nat, +lt: {Nat.is_lt(Nat.add(110n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(110n, k)))) == Nat.add(110n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d111(p, lt)

def cnt.d109(+k: Nat, +lt: {Nat.is_lt(Nat.add(109n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(109n, k)))) == Nat.add(109n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d110(p, lt)

def cnt.d108(+k: Nat, +lt: {Nat.is_lt(Nat.add(108n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(108n, k)))) == Nat.add(108n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d109(p, lt)

def cnt.d107(+k: Nat, +lt: {Nat.is_lt(Nat.add(107n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(107n, k)))) == Nat.add(107n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d108(p, lt)

def cnt.d106(+k: Nat, +lt: {Nat.is_lt(Nat.add(106n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(106n, k)))) == Nat.add(106n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d107(p, lt)

def cnt.d105(+k: Nat, +lt: {Nat.is_lt(Nat.add(105n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(105n, k)))) == Nat.add(105n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d106(p, lt)

def cnt.d104(+k: Nat, +lt: {Nat.is_lt(Nat.add(104n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(104n, k)))) == Nat.add(104n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d105(p, lt)

def cnt.d103(+k: Nat, +lt: {Nat.is_lt(Nat.add(103n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(103n, k)))) == Nat.add(103n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d104(p, lt)

def cnt.d102(+k: Nat, +lt: {Nat.is_lt(Nat.add(102n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(102n, k)))) == Nat.add(102n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d103(p, lt)

def cnt.d101(+k: Nat, +lt: {Nat.is_lt(Nat.add(101n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(101n, k)))) == Nat.add(101n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d102(p, lt)

def cnt.d100(+k: Nat, +lt: {Nat.is_lt(Nat.add(100n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(100n, k)))) == Nat.add(100n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d101(p, lt)

def cnt.d99(+k: Nat, +lt: {Nat.is_lt(Nat.add(99n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(99n, k)))) == Nat.add(99n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d100(p, lt)

def cnt.d98(+k: Nat, +lt: {Nat.is_lt(Nat.add(98n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(98n, k)))) == Nat.add(98n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d99(p, lt)

def cnt.d97(+k: Nat, +lt: {Nat.is_lt(Nat.add(97n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(97n, k)))) == Nat.add(97n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d98(p, lt)

def cnt.d96(+k: Nat, +lt: {Nat.is_lt(Nat.add(96n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(96n, k)))) == Nat.add(96n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d97(p, lt)

def cnt.d95(+k: Nat, +lt: {Nat.is_lt(Nat.add(95n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(95n, k)))) == Nat.add(95n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d96(p, lt)

def cnt.d94(+k: Nat, +lt: {Nat.is_lt(Nat.add(94n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(94n, k)))) == Nat.add(94n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d95(p, lt)

def cnt.d93(+k: Nat, +lt: {Nat.is_lt(Nat.add(93n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(93n, k)))) == Nat.add(93n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d94(p, lt)

def cnt.d92(+k: Nat, +lt: {Nat.is_lt(Nat.add(92n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(92n, k)))) == Nat.add(92n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d93(p, lt)

def cnt.d91(+k: Nat, +lt: {Nat.is_lt(Nat.add(91n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(91n, k)))) == Nat.add(91n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d92(p, lt)

def cnt.d90(+k: Nat, +lt: {Nat.is_lt(Nat.add(90n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(90n, k)))) == Nat.add(90n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d91(p, lt)

def cnt.d89(+k: Nat, +lt: {Nat.is_lt(Nat.add(89n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(89n, k)))) == Nat.add(89n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d90(p, lt)

def cnt.d88(+k: Nat, +lt: {Nat.is_lt(Nat.add(88n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(88n, k)))) == Nat.add(88n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d89(p, lt)

def cnt.d87(+k: Nat, +lt: {Nat.is_lt(Nat.add(87n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(87n, k)))) == Nat.add(87n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d88(p, lt)

def cnt.d86(+k: Nat, +lt: {Nat.is_lt(Nat.add(86n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(86n, k)))) == Nat.add(86n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d87(p, lt)

def cnt.d85(+k: Nat, +lt: {Nat.is_lt(Nat.add(85n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(85n, k)))) == Nat.add(85n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d86(p, lt)

def cnt.d84(+k: Nat, +lt: {Nat.is_lt(Nat.add(84n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(84n, k)))) == Nat.add(84n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d85(p, lt)

def cnt.d83(+k: Nat, +lt: {Nat.is_lt(Nat.add(83n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(83n, k)))) == Nat.add(83n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d84(p, lt)

def cnt.d82(+k: Nat, +lt: {Nat.is_lt(Nat.add(82n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(82n, k)))) == Nat.add(82n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d83(p, lt)

def cnt.d81(+k: Nat, +lt: {Nat.is_lt(Nat.add(81n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(81n, k)))) == Nat.add(81n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d82(p, lt)

def cnt.d80(+k: Nat, +lt: {Nat.is_lt(Nat.add(80n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(80n, k)))) == Nat.add(80n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d81(p, lt)

def cnt.d79(+k: Nat, +lt: {Nat.is_lt(Nat.add(79n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(79n, k)))) == Nat.add(79n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d80(p, lt)

def cnt.d78(+k: Nat, +lt: {Nat.is_lt(Nat.add(78n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(78n, k)))) == Nat.add(78n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d79(p, lt)

def cnt.d77(+k: Nat, +lt: {Nat.is_lt(Nat.add(77n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(77n, k)))) == Nat.add(77n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d78(p, lt)

def cnt.d76(+k: Nat, +lt: {Nat.is_lt(Nat.add(76n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(76n, k)))) == Nat.add(76n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d77(p, lt)

def cnt.d75(+k: Nat, +lt: {Nat.is_lt(Nat.add(75n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(75n, k)))) == Nat.add(75n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d76(p, lt)

def cnt.d74(+k: Nat, +lt: {Nat.is_lt(Nat.add(74n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(74n, k)))) == Nat.add(74n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d75(p, lt)

def cnt.d73(+k: Nat, +lt: {Nat.is_lt(Nat.add(73n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(73n, k)))) == Nat.add(73n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d74(p, lt)

def cnt.d72(+k: Nat, +lt: {Nat.is_lt(Nat.add(72n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(72n, k)))) == Nat.add(72n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d73(p, lt)

def cnt.d71(+k: Nat, +lt: {Nat.is_lt(Nat.add(71n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(71n, k)))) == Nat.add(71n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d72(p, lt)

def cnt.d70(+k: Nat, +lt: {Nat.is_lt(Nat.add(70n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(70n, k)))) == Nat.add(70n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d71(p, lt)

def cnt.d69(+k: Nat, +lt: {Nat.is_lt(Nat.add(69n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(69n, k)))) == Nat.add(69n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d70(p, lt)

def cnt.d68(+k: Nat, +lt: {Nat.is_lt(Nat.add(68n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(68n, k)))) == Nat.add(68n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d69(p, lt)

def cnt.d67(+k: Nat, +lt: {Nat.is_lt(Nat.add(67n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(67n, k)))) == Nat.add(67n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d68(p, lt)

def cnt.d66(+k: Nat, +lt: {Nat.is_lt(Nat.add(66n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(66n, k)))) == Nat.add(66n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d67(p, lt)

def cnt.d65(+k: Nat, +lt: {Nat.is_lt(Nat.add(65n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(65n, k)))) == Nat.add(65n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d66(p, lt)

def cnt.d64(+k: Nat, +lt: {Nat.is_lt(Nat.add(64n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(64n, k)))) == Nat.add(64n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d65(p, lt)

def cnt.d63(+k: Nat, +lt: {Nat.is_lt(Nat.add(63n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(63n, k)))) == Nat.add(63n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d64(p, lt)

def cnt.d62(+k: Nat, +lt: {Nat.is_lt(Nat.add(62n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(62n, k)))) == Nat.add(62n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d63(p, lt)

def cnt.d61(+k: Nat, +lt: {Nat.is_lt(Nat.add(61n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(61n, k)))) == Nat.add(61n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d62(p, lt)

def cnt.d60(+k: Nat, +lt: {Nat.is_lt(Nat.add(60n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(60n, k)))) == Nat.add(60n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d61(p, lt)

def cnt.d59(+k: Nat, +lt: {Nat.is_lt(Nat.add(59n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(59n, k)))) == Nat.add(59n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d60(p, lt)

def cnt.d58(+k: Nat, +lt: {Nat.is_lt(Nat.add(58n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(58n, k)))) == Nat.add(58n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d59(p, lt)

def cnt.d57(+k: Nat, +lt: {Nat.is_lt(Nat.add(57n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(57n, k)))) == Nat.add(57n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d58(p, lt)

def cnt.d56(+k: Nat, +lt: {Nat.is_lt(Nat.add(56n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(56n, k)))) == Nat.add(56n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d57(p, lt)

def cnt.d55(+k: Nat, +lt: {Nat.is_lt(Nat.add(55n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(55n, k)))) == Nat.add(55n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d56(p, lt)

def cnt.d54(+k: Nat, +lt: {Nat.is_lt(Nat.add(54n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(54n, k)))) == Nat.add(54n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d55(p, lt)

def cnt.d53(+k: Nat, +lt: {Nat.is_lt(Nat.add(53n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(53n, k)))) == Nat.add(53n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d54(p, lt)

def cnt.d52(+k: Nat, +lt: {Nat.is_lt(Nat.add(52n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(52n, k)))) == Nat.add(52n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d53(p, lt)

def cnt.d51(+k: Nat, +lt: {Nat.is_lt(Nat.add(51n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(51n, k)))) == Nat.add(51n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d52(p, lt)

def cnt.d50(+k: Nat, +lt: {Nat.is_lt(Nat.add(50n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(50n, k)))) == Nat.add(50n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d51(p, lt)

def cnt.d49(+k: Nat, +lt: {Nat.is_lt(Nat.add(49n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(49n, k)))) == Nat.add(49n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d50(p, lt)

def cnt.d48(+k: Nat, +lt: {Nat.is_lt(Nat.add(48n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(48n, k)))) == Nat.add(48n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d49(p, lt)

def cnt.d47(+k: Nat, +lt: {Nat.is_lt(Nat.add(47n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(47n, k)))) == Nat.add(47n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d48(p, lt)

def cnt.d46(+k: Nat, +lt: {Nat.is_lt(Nat.add(46n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(46n, k)))) == Nat.add(46n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d47(p, lt)

def cnt.d45(+k: Nat, +lt: {Nat.is_lt(Nat.add(45n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(45n, k)))) == Nat.add(45n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d46(p, lt)

def cnt.d44(+k: Nat, +lt: {Nat.is_lt(Nat.add(44n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(44n, k)))) == Nat.add(44n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d45(p, lt)

def cnt.d43(+k: Nat, +lt: {Nat.is_lt(Nat.add(43n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(43n, k)))) == Nat.add(43n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d44(p, lt)

def cnt.d42(+k: Nat, +lt: {Nat.is_lt(Nat.add(42n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(42n, k)))) == Nat.add(42n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d43(p, lt)

def cnt.d41(+k: Nat, +lt: {Nat.is_lt(Nat.add(41n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(41n, k)))) == Nat.add(41n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d42(p, lt)

def cnt.d40(+k: Nat, +lt: {Nat.is_lt(Nat.add(40n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(40n, k)))) == Nat.add(40n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d41(p, lt)

def cnt.d39(+k: Nat, +lt: {Nat.is_lt(Nat.add(39n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(39n, k)))) == Nat.add(39n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d40(p, lt)

def cnt.d38(+k: Nat, +lt: {Nat.is_lt(Nat.add(38n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(38n, k)))) == Nat.add(38n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d39(p, lt)

def cnt.d37(+k: Nat, +lt: {Nat.is_lt(Nat.add(37n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(37n, k)))) == Nat.add(37n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d38(p, lt)

def cnt.d36(+k: Nat, +lt: {Nat.is_lt(Nat.add(36n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(36n, k)))) == Nat.add(36n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d37(p, lt)

def cnt.d35(+k: Nat, +lt: {Nat.is_lt(Nat.add(35n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(35n, k)))) == Nat.add(35n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d36(p, lt)

def cnt.d34(+k: Nat, +lt: {Nat.is_lt(Nat.add(34n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(34n, k)))) == Nat.add(34n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d35(p, lt)

def cnt.d33(+k: Nat, +lt: {Nat.is_lt(Nat.add(33n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(33n, k)))) == Nat.add(33n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d34(p, lt)

def cnt.d32(+k: Nat, +lt: {Nat.is_lt(Nat.add(32n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(32n, k)))) == Nat.add(32n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d33(p, lt)

def cnt.d31(+k: Nat, +lt: {Nat.is_lt(Nat.add(31n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(31n, k)))) == Nat.add(31n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d32(p, lt)

def cnt.d30(+k: Nat, +lt: {Nat.is_lt(Nat.add(30n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(30n, k)))) == Nat.add(30n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d31(p, lt)

def cnt.d29(+k: Nat, +lt: {Nat.is_lt(Nat.add(29n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(29n, k)))) == Nat.add(29n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d30(p, lt)

def cnt.d28(+k: Nat, +lt: {Nat.is_lt(Nat.add(28n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(28n, k)))) == Nat.add(28n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d29(p, lt)

def cnt.d27(+k: Nat, +lt: {Nat.is_lt(Nat.add(27n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(27n, k)))) == Nat.add(27n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d28(p, lt)

def cnt.d26(+k: Nat, +lt: {Nat.is_lt(Nat.add(26n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(26n, k)))) == Nat.add(26n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d27(p, lt)

def cnt.d25(+k: Nat, +lt: {Nat.is_lt(Nat.add(25n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(25n, k)))) == Nat.add(25n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d26(p, lt)

def cnt.d24(+k: Nat, +lt: {Nat.is_lt(Nat.add(24n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(24n, k)))) == Nat.add(24n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d25(p, lt)

def cnt.d23(+k: Nat, +lt: {Nat.is_lt(Nat.add(23n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(23n, k)))) == Nat.add(23n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d24(p, lt)

def cnt.d22(+k: Nat, +lt: {Nat.is_lt(Nat.add(22n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(22n, k)))) == Nat.add(22n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d23(p, lt)

def cnt.d21(+k: Nat, +lt: {Nat.is_lt(Nat.add(21n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(21n, k)))) == Nat.add(21n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d22(p, lt)

def cnt.d20(+k: Nat, +lt: {Nat.is_lt(Nat.add(20n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(20n, k)))) == Nat.add(20n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d21(p, lt)

def cnt.d19(+k: Nat, +lt: {Nat.is_lt(Nat.add(19n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(19n, k)))) == Nat.add(19n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d20(p, lt)

def cnt.d18(+k: Nat, +lt: {Nat.is_lt(Nat.add(18n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(18n, k)))) == Nat.add(18n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d19(p, lt)

def cnt.d17(+k: Nat, +lt: {Nat.is_lt(Nat.add(17n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(17n, k)))) == Nat.add(17n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d18(p, lt)

def cnt.d16(+k: Nat, +lt: {Nat.is_lt(Nat.add(16n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(16n, k)))) == Nat.add(16n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d17(p, lt)

def cnt.d15(+k: Nat, +lt: {Nat.is_lt(Nat.add(15n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(15n, k)))) == Nat.add(15n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d16(p, lt)

def cnt.d14(+k: Nat, +lt: {Nat.is_lt(Nat.add(14n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(14n, k)))) == Nat.add(14n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d15(p, lt)

def cnt.d13(+k: Nat, +lt: {Nat.is_lt(Nat.add(13n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(13n, k)))) == Nat.add(13n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d14(p, lt)

def cnt.d12(+k: Nat, +lt: {Nat.is_lt(Nat.add(12n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(12n, k)))) == Nat.add(12n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d13(p, lt)

def cnt.d11(+k: Nat, +lt: {Nat.is_lt(Nat.add(11n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(11n, k)))) == Nat.add(11n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d12(p, lt)

def cnt.d10(+k: Nat, +lt: {Nat.is_lt(Nat.add(10n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(10n, k)))) == Nat.add(10n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d11(p, lt)

def cnt.d9(+k: Nat, +lt: {Nat.is_lt(Nat.add(9n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(9n, k)))) == Nat.add(9n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d10(p, lt)

def cnt.d8(+k: Nat, +lt: {Nat.is_lt(Nat.add(8n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(8n, k)))) == Nat.add(8n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d9(p, lt)

def cnt.d7(+k: Nat, +lt: {Nat.is_lt(Nat.add(7n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(7n, k)))) == Nat.add(7n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d8(p, lt)

def cnt.d6(+k: Nat, +lt: {Nat.is_lt(Nat.add(6n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(6n, k)))) == Nat.add(6n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d7(p, lt)

def cnt.d5(+k: Nat, +lt: {Nat.is_lt(Nat.add(5n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(5n, k)))) == Nat.add(5n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d6(p, lt)

def cnt.d4(+k: Nat, +lt: {Nat.is_lt(Nat.add(4n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(4n, k)))) == Nat.add(4n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d5(p, lt)

def cnt.d3(+k: Nat, +lt: {Nat.is_lt(Nat.add(3n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(3n, k)))) == Nat.add(3n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d4(p, lt)

def cnt.d2(+k: Nat, +lt: {Nat.is_lt(Nat.add(2n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(2n, k)))) == Nat.add(2n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d3(p, lt)

def cnt.d1(+k: Nat, +lt: {Nat.is_lt(Nat.add(1n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(1n, k)))) == Nat.add(1n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d2(p, lt)

def cnt.d0(+k: Nat, +lt: {Nat.is_lt(Nat.add(0n, k), 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(Nat.add(0n, k)))) == Nat.add(0n, k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cnt.d1(p, lt)

def cnt_rt(+k: Nat, +lt: {Nat.is_lt(k, 256n) == True{} : Bool}) -> {U32.to_nat(B.byte(U32.from_nat(k))) == k : Nat}:
  cnt.d0(k, lt)

def Laws.pkglength_round_trip(v, rest, fits):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(K.AmlPkgLength.encode(v), rest)), B.append(B.Octets.to_list(K.AmlPkgLength.encode(v)), B.Octets.to_list(rest)), BL.octets_append_list(K.AmlPkgLength.encode(v), rest)) : {K.pk.pub(K.pk.dec(_)) == Done{K.AmlPkgLen{v, rest}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(K.pk.enc(v))), B.mask(K.pk.enc(v)), BL.octets_to_of(K.pk.enc(v))) : {K.pk.pub(K.pk.dec(B.append(_, B.Octets.to_list(rest)))) == Done{K.AmlPkgLen{v, rest}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}
  %BL.octets_of_to(rest) : {K.pk.pub(K.pk.dec(B.append(B.mask(K.pk.enc(v)), B.Octets.to_list(rest)))) == Done{K.AmlPkgLen{v, _}} : Result<&2, &2, E.AcpiError, K.AmlPkgLen>}
  pk_rt(v, B.Octets.to_list(rest), fits)
# Lists and masks

def app_assoc(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {B.append(a, B.append(b, c)) == B.append(B.append(a, b), c) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %app_assoc(t, b, c) : {Con{h, B.append(t, B.append(b, c))} == Con{h, _} : List<&2, U32>}
      {==}

def mask_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.append(B.mask(a), B.mask(b)) == B.mask(B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mask_app(t, b) : {Con{B.byte(h), B.append(B.mask(t), B.mask(b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def mask_tl(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(o)) : {B.Octets.to_list(o) == _ : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {B.Octets.to_list(o) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

def and_l(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ft_absurd(e))

def and_r(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, ft_absurd(e))

# NameStrings. The encoder's bytes are bytes already: masking them changes
# nothing but the SegCount, which stays byte(from_nat(count)).

def mask_segs(+ss: List<&2, B.Octets>) -> {N.nm.segs.list(ss) == B.mask(N.nm.segs.list(ss)) : List<&2, U32>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      %mask_app(B.Octets.to_list(s), N.nm.segs.list(t)) : {B.append(B.Octets.to_list(s), N.nm.segs.list(t)) == _ : List<&2, U32>}
      %mask_tl(s) : {B.append(B.Octets.to_list(s), N.nm.segs.list(t)) == B.append(_, B.mask(N.nm.segs.list(t))) : List<&2, U32>}
      %mask_segs(t) : {B.append(B.Octets.to_list(s), N.nm.segs.list(t)) == B.append(B.Octets.to_list(s), _) : List<&2, U32>}
      {==}

def mask_carets(+u: Nat) -> {N.nm.carets(u) == B.mask(N.nm.carets(u)) : List<&2, U32>}:
  match u:
    case 0n:
      {==}
    case 1n+p:
      %mask_carets(p) : {Con{94, N.nm.carets(p)} == Con{94, _} : List<&2, U32>}
      {==}

def is_seg_t(+k: N.AmlLeadKind, +e: {N.AmlLead.is_seg(k) == True{} : Bool}) -> {N.AmlLSeg{} == k : N.AmlLeadKind}:
  match k:
    case N.AmlLSeg{}:
      {==}
    case N.AmlLRoot{}:
      Empty.absurd({N.AmlLSeg{} == N.AmlLRoot{} : N.AmlLeadKind}, ft_absurd(e))
    case N.AmlLParent{}:
      Empty.absurd({N.AmlLSeg{} == N.AmlLParent{} : N.AmlLeadKind}, ft_absurd(e))
    case N.AmlLDual{}:
      Empty.absurd({N.AmlLSeg{} == N.AmlLDual{} : N.AmlLeadKind}, ft_absurd(e))
    case N.AmlLMulti{}:
      Empty.absurd({N.AmlLSeg{} == N.AmlLMulti{} : N.AmlLeadKind}, ft_absurd(e))
    case N.AmlLNull{}:
      Empty.absurd({N.AmlLSeg{} == N.AmlLNull{} : N.AmlLeadKind}, ft_absurd(e))
    case N.AmlLOther{}:
      Empty.absurd({N.AmlLSeg{} == N.AmlLOther{} : N.AmlLeadKind}, ft_absurd(e))

# a NameSeg's first byte is a LeadNameChar
def seg_kind(+c0: U32, +c1: U32, +c2: U32, +c3: U32, +ok: {N.nm.seg_ok4(c0, c1, c2, c3) == True{} : Bool}) -> {N.AmlLSeg{} == N.AmlLead.classify(c0) : N.AmlLeadKind}:
  is_seg_t(N.AmlLead.classify(c0), and_l(N.AmlLead.is_seg(N.AmlLead.classify(c0)), Bool.and(N.AmlName.name_char(c1), Bool.and(N.AmlName.name_char(c2), N.AmlName.name_char(c3))), ok))

def seg_l(+s: B.Octets, +L: List<&2, U32>, +R: List<&2, U32>, +e: {B.Octets.to_list(s) == L : List<&2, U32>}, +ok: {N.nm.seg_ok.list(L) == True{} : Bool}) -> {Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(L, R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}:
  match L:
    case Nil{}:
      Empty.absurd({Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(Nil{}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}, ft_absurd(ok))
    case Con{c0, L1}:
      match L1:
        case Nil{}:
          Empty.absurd({Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(Con{c0, Nil{}}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}, ft_absurd(ok))
        case Con{c1, L2}:
          match L2:
            case Nil{}:
              Empty.absurd({Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(Con{c0, Con{c1, Nil{}}}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}, ft_absurd(ok))
            case Con{c2, L3}:
              match L3:
                case Nil{}:
                  Empty.absurd({Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(Con{c0, Con{c1, Con{c2, Nil{}}}}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}, ft_absurd(ok))
                case Con{c3, L4}:
                  match L4:
                    case Con{c4, L5}:
                      Empty.absurd({Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, L5}}}}}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}, ft_absurd(ok))
                    case Nil{}:
                      %Equal.sym(Bool, N.nm.seg_ok4(c0, c1, c2, c3), True{}, ok) : {Done{N.AmlSegL{s, R}} == N.nm.seg.pick(_, c0, c1, c2, c3, R) : Result<&2, &2, E.AcpiError, N.AmlSegL>}
                      %BL.octets_of_to(s) : {Done{N.AmlSegL{_, R}} == Done{N.AmlSegL{B.Octets.of_list(Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}), R}} : Result<&2, &2, E.AcpiError, N.AmlSegL>}
                      %e : {Done{N.AmlSegL{B.Octets.of_list(B.Octets.to_list(s)), R}} == Done{N.AmlSegL{B.Octets.of_list(_), R}} : Result<&2, &2, E.AcpiError, N.AmlSegL>}
                      {==}

def pth1_dpath(+s: B.Octets, +L: List<&2, U32>, +R: List<&2, U32>, +e: {B.Octets.to_list(s) == L : List<&2, U32>}, +ok: {N.nm.seg_ok.list(L) == True{} : Bool}) -> {Done{N.AmlSegsL{[s], R}} == N.nm.dpath(B.append(B.append(L, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}:
  match L:
    case Nil{}:
      Empty.absurd({Done{N.AmlSegsL{[s], R}} == N.nm.dpath(B.append(B.append(Nil{}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}, ft_absurd(ok))
    case Con{c0, L1}:
      match L1:
        case Nil{}:
          Empty.absurd({Done{N.AmlSegsL{[s], R}} == N.nm.dpath(B.append(B.append(Con{c0, Nil{}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}, ft_absurd(ok))
        case Con{c1, L2}:
          match L2:
            case Nil{}:
              Empty.absurd({Done{N.AmlSegsL{[s], R}} == N.nm.dpath(B.append(B.append(Con{c0, Con{c1, Nil{}}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}, ft_absurd(ok))
            case Con{c2, L3}:
              match L3:
                case Nil{}:
                  Empty.absurd({Done{N.AmlSegsL{[s], R}} == N.nm.dpath(B.append(B.append(Con{c0, Con{c1, Con{c2, Nil{}}}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}, ft_absurd(ok))
                case Con{c3, L4}:
                  match L4:
                    case Con{c4, L5}:
                      Empty.absurd({Done{N.AmlSegsL{[s], R}} == N.nm.dpath(B.append(B.append(Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, L5}}}}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}, ft_absurd(ok))
                    case Nil{}:
                      %seg_kind(c0, c1, c2, c3, ok) : {Done{N.AmlSegsL{[s], R}} == N.nm.path.k(_, c0, Con{c1, Con{c2, Con{c3, R}}}) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
                      %seg_l(s, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}, R, e, ok) : {Done{N.AmlSegsL{[s], R}} == N.nm.segs.go(0n, _) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
                      {==}

def pth1_dec(+s: B.Octets, +L: List<&2, U32>, +R: List<&2, U32>, +e: {B.Octets.to_list(s) == L : List<&2, U32>}, +ok: {N.nm.seg_ok.list(L) == True{} : Bool}) -> {Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec(B.append(B.append(L, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}:
  match L:
    case Nil{}:
      Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec(B.append(B.append(Nil{}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
    case Con{c0, L1}:
      match L1:
        case Nil{}:
          Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec(B.append(B.append(Con{c0, Nil{}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
        case Con{c1, L2}:
          match L2:
            case Nil{}:
              Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec(B.append(B.append(Con{c0, Con{c1, Nil{}}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
            case Con{c2, L3}:
              match L3:
                case Nil{}:
                  Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec(B.append(B.append(Con{c0, Con{c1, Con{c2, Nil{}}}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
                case Con{c3, L4}:
                  match L4:
                    case Con{c4, L5}:
                      Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec(B.append(B.append(Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, L5}}}}}, Nil{}), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
                    case Nil{}:
                      %seg_kind(c0, c1, c2, c3, ok) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.dec.k(_, c0, Con{c1, Con{c2, Con{c3, R}}}) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
                      %seg_l(s, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}, R, e, ok) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.named(False{}, 0n, N.nm.segs.go(0n, _)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
                      {==}

def pth1_ups(+s: B.Octets, +L: List<&2, U32>, +R: List<&2, U32>, +e: {B.Octets.to_list(s) == L : List<&2, U32>}, +ok: {N.nm.seg_ok.list(L) == True{} : Bool}) -> {Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(B.append(B.append(L, Nil{}), R), N.nm.head_kind(B.append(B.append(L, Nil{}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}:
  match L:
    case Nil{}:
      Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(B.append(B.append(Nil{}, Nil{}), R), N.nm.head_kind(B.append(B.append(Nil{}, Nil{}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
    case Con{c0, L1}:
      match L1:
        case Nil{}:
          Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(B.append(B.append(Con{c0, Nil{}}, Nil{}), R), N.nm.head_kind(B.append(B.append(Con{c0, Nil{}}, Nil{}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
        case Con{c1, L2}:
          match L2:
            case Nil{}:
              Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(B.append(B.append(Con{c0, Con{c1, Nil{}}}, Nil{}), R), N.nm.head_kind(B.append(B.append(Con{c0, Con{c1, Nil{}}}, Nil{}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
            case Con{c2, L3}:
              match L3:
                case Nil{}:
                  Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(B.append(B.append(Con{c0, Con{c1, Con{c2, Nil{}}}}, Nil{}), R), N.nm.head_kind(B.append(B.append(Con{c0, Con{c1, Con{c2, Nil{}}}}, Nil{}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
                case Con{c3, L4}:
                  match L4:
                    case Con{c4, L5}:
                      Empty.absurd({Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(B.append(B.append(Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, L5}}}}}, Nil{}), R), N.nm.head_kind(B.append(B.append(Con{c0, Con{c1, Con{c2, Con{c3, Con{c4, L5}}}}}, Nil{}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
                    case Nil{}:
                      %seg_kind(c0, c1, c2, c3, ok) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.ups(Con{c0, Con{c1, Con{c2, Con{c3, R}}}}, _) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
                      %seg_l(s, Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}, R, e, ok) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, [s]}, R}} == N.nm.named(False{}, 0n, N.nm.segs.go(0n, _)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
                      {==}

def seg_rt(+s: B.Octets, +R: List<&2, U32>, +ok: {N.AmlName.seg_ok(s) == True{} : Bool}) -> {Done{N.AmlSegL{s, R}} == N.nm.seg(B.append(B.Octets.to_list(s), R)) : Result<&2, &2, E.AcpiError, N.AmlSegL>}:
  seg_l(s, B.Octets.to_list(s), R, {==}, ok)

# segments read back one after another
def segs_go_rt(+t: List<&2, B.Octets>, +s: B.Octets, +R: List<&2, U32>, +oks: {N.AmlName.segs_ok(Con{s, t}) == True{} : Bool}) -> {Done{N.AmlSegsL{Con{s, t}, R}} == N.nm.segs.go(N.nm.len(t), N.nm.seg(B.append(B.Octets.to_list(s), B.append(N.nm.segs.list(t), R)))) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}:
  match t:
    case Nil{}:
      %seg_rt(s, R, and_l(N.AmlName.seg_ok(s), True{}, oks)) : {Done{N.AmlSegsL{[s], R}} == N.nm.segs.go(0n, _) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
      {==}
    case Con{s2, t2}:
      %seg_rt(s, B.append(N.nm.segs.list(Con{s2, t2}), R), and_l(N.AmlName.seg_ok(s), N.AmlName.segs_ok(Con{s2, t2}), oks)) : {Done{N.AmlSegsL{Con{s, Con{s2, t2}}, R}} == N.nm.segs.go(1n+N.nm.len(t2), _) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
      %app_assoc(B.Octets.to_list(s2), N.nm.segs.list(t2), R) : {Done{N.AmlSegsL{Con{s, Con{s2, t2}}, R}} == N.nm.cons(s, N.nm.segs.go(N.nm.len(t2), N.nm.seg(_))) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
      %segs_go_rt(t2, s2, R, and_r(N.AmlName.seg_ok(s), N.AmlName.segs_ok(Con{s2, t2}), oks)) : {Done{N.AmlSegsL{Con{s, Con{s2, t2}}, R}} == N.nm.cons(s, _) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
      {==}

def segs_rt(+ss: List<&2, B.Octets>, +R: List<&2, U32>, +oks: {N.AmlName.segs_ok(ss) == True{} : Bool}) -> {Done{N.AmlSegsL{ss, R}} == N.nm.segs(N.nm.len(ss), B.append(N.nm.segs.list(ss), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      %app_assoc(B.Octets.to_list(s), N.nm.segs.list(t), R) : {Done{N.AmlSegsL{Con{s, t}, R}} == N.nm.segs.go(N.nm.len(t), N.nm.seg(_)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
      segs_go_rt(t, s, R, oks)

def pth_dpath(+ss: List<&2, B.Octets>, +R: List<&2, U32>, +oks: {N.AmlName.segs_ok(ss) == True{} : Bool}, +lt: {Nat.is_lt(N.nm.len(ss), 256n) == True{} : Bool}) -> {Done{N.AmlSegsL{ss, R}} == N.nm.dpath(B.append(B.mask(N.nm.path(ss)), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      match t:
        case Nil{}:
          %mask_segs(Con{s, Nil{}}) : {Done{N.AmlSegsL{Con{s, Nil{}}, R}} == N.nm.dpath(B.append(_, R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
          pth1_dpath(s, B.Octets.to_list(s), R, {==}, and_l(N.AmlName.seg_ok(s), True{}, oks))
        case Con{s2, t2}:
          match t2:
            case Nil{}:
              %mask_segs(Con{s, Con{s2, Nil{}}}) : {Done{N.AmlSegsL{Con{s, Con{s2, Nil{}}}, R}} == N.nm.dpath(B.append(Con{46, _}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
              segs_rt(Con{s, Con{s2, Nil{}}}, R, oks)
            case Con{s3, t3}:
              %mask_segs(Con{s, Con{s2, Con{s3, t3}}}) : {Done{N.AmlSegsL{Con{s, Con{s2, Con{s3, t3}}}, R}} == N.nm.dpath(B.append(Con{47, Con{B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3)))), _}}, R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
              %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3))))), Nat.add(3n, N.nm.len(t3)), cnt_rt(Nat.add(3n, N.nm.len(t3)), lt)) : {Done{N.AmlSegsL{Con{s, Con{s2, Con{s3, t3}}}, R}} == N.nm.multi.k(Nat.is_eq(_, 0n), _, B.append(N.nm.segs.list(Con{s, Con{s2, Con{s3, t3}}}), R)) : Result<&2, &2, E.AcpiError, N.AmlSegsL>}
              segs_rt(Con{s, Con{s2, Con{s3, t3}}}, R, oks)

def pth_dec(+ss: List<&2, B.Octets>, +R: List<&2, U32>, +oks: {N.AmlName.segs_ok(ss) == True{} : Bool}, +lt: {Nat.is_lt(N.nm.len(ss), 256n) == True{} : Bool}) -> {Done{N.AmlNameL{N.AmlName{False{}, 0n, ss}, R}} == N.nm.dec(B.append(B.mask(N.nm.path(ss)), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      match t:
        case Nil{}:
          %mask_segs(Con{s, Nil{}}) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Nil{}}}, R}} == N.nm.dec(B.append(_, R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
          pth1_dec(s, B.Octets.to_list(s), R, {==}, and_l(N.AmlName.seg_ok(s), True{}, oks))
        case Con{s2, t2}:
          match t2:
            case Nil{}:
              %mask_segs(Con{s, Con{s2, Nil{}}}) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Nil{}}}}, R}} == N.nm.dec(B.append(Con{46, _}, R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %segs_rt(Con{s, Con{s2, Nil{}}}, R, oks) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Nil{}}}}, R}} == N.nm.named(False{}, 0n, _) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              {==}
            case Con{s3, t3}:
              %mask_segs(Con{s, Con{s2, Con{s3, t3}}}) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Con{s3, t3}}}}, R}} == N.nm.dec(B.append(Con{47, Con{B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3)))), _}}, R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3))))), Nat.add(3n, N.nm.len(t3)), cnt_rt(Nat.add(3n, N.nm.len(t3)), lt)) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Con{s3, t3}}}}, R}} == N.nm.named(False{}, 0n, N.nm.multi.k(Nat.is_eq(_, 0n), _, B.append(N.nm.segs.list(Con{s, Con{s2, Con{s3, t3}}}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %segs_rt(Con{s, Con{s2, Con{s3, t3}}}, R, oks) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Con{s3, t3}}}}, R}} == N.nm.named(False{}, 0n, _) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              {==}

def pth_ups(+ss: List<&2, B.Octets>, +R: List<&2, U32>, +oks: {N.AmlName.segs_ok(ss) == True{} : Bool}, +lt: {Nat.is_lt(N.nm.len(ss), 256n) == True{} : Bool}) -> {Done{N.AmlNameL{N.AmlName{False{}, 0n, ss}, R}} == N.nm.ups(B.append(B.mask(N.nm.path(ss)), R), N.nm.head_kind(B.append(B.mask(N.nm.path(ss)), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      match t:
        case Nil{}:
          %mask_segs(Con{s, Nil{}}) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Nil{}}}, R}} == N.nm.ups(B.append(_, R), N.nm.head_kind(B.append(_, R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
          pth1_ups(s, B.Octets.to_list(s), R, {==}, and_l(N.AmlName.seg_ok(s), True{}, oks))
        case Con{s2, t2}:
          match t2:
            case Nil{}:
              %mask_segs(Con{s, Con{s2, Nil{}}}) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Nil{}}}}, R}} == N.nm.ups(B.append(Con{46, _}, R), N.nm.head_kind(B.append(Con{46, _}, R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %segs_rt(Con{s, Con{s2, Nil{}}}, R, oks) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Nil{}}}}, R}} == N.nm.named(False{}, 0n, _) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              {==}
            case Con{s3, t3}:
              %mask_segs(Con{s, Con{s2, Con{s3, t3}}}) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Con{s3, t3}}}}, R}} == N.nm.ups(B.append(Con{47, Con{B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3)))), _}}, R), N.nm.head_kind(B.append(Con{47, Con{B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3)))), _}}, R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.add(3n, N.nm.len(t3))))), Nat.add(3n, N.nm.len(t3)), cnt_rt(Nat.add(3n, N.nm.len(t3)), lt)) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Con{s3, t3}}}}, R}} == N.nm.named(False{}, 0n, N.nm.multi.k(Nat.is_eq(_, 0n), _, B.append(N.nm.segs.list(Con{s, Con{s2, Con{s3, t3}}}), R))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %segs_rt(Con{s, Con{s2, Con{s3, t3}}}, R, oks) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, Con{s, Con{s2, Con{s3, t3}}}}, R}} == N.nm.named(False{}, 0n, _) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              {==}

def ups_rt(+u: Nat, +ss: List<&2, B.Octets>, +R: List<&2, U32>, +oks: {N.AmlName.segs_ok(ss) == True{} : Bool}, +lt: {Nat.is_lt(N.nm.len(ss), 256n) == True{} : Bool}) -> {Done{N.AmlNameL{N.AmlName{False{}, u, ss}, R}} == N.nm.ups(B.append(N.nm.carets(u), B.append(B.mask(N.nm.path(ss)), R)), N.nm.head_kind(B.append(N.nm.carets(u), B.append(B.mask(N.nm.path(ss)), R)))) : Result<&2, &2, E.AcpiError, N.AmlNameL>}:
  match u:
    case 0n:
      pth_ups(ss, R, oks, lt)
    case 1n+p:
      %ups_rt(p, ss, R, oks, lt) : {Done{N.AmlNameL{N.AmlName{False{}, 1n+p, ss}, R}} == N.nm.up1(_) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
      {==}

def dec_rt(+n: N.AmlName, +R: List<&2, U32>, +ok: {N.AmlName.valid(n) == True{} : Bool}) -> {Done{N.AmlNameL{n, R}} == N.nm.dec(B.append(B.mask(N.nm.enc(n)), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}:
  match n:
    case N.AmlName{r, u, ss}:
      match r:
        case True{}:
          match u:
            case 0n:
              %mask_app([92], N.nm.path(ss)) : {Done{N.AmlNameL{N.AmlName{True{}, 0n, ss}, R}} == N.nm.dec(B.append(_, R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %pth_dpath(ss, R, and_l(N.AmlName.segs_ok(ss), Nat.is_lt(N.nm.len(ss), 256n), ok), and_r(N.AmlName.segs_ok(ss), Nat.is_lt(N.nm.len(ss), 256n), ok)) : {Done{N.AmlNameL{N.AmlName{True{}, 0n, ss}, R}} == N.nm.named(True{}, 0n, _) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              {==}
            case 1n+p:
              Empty.absurd({Done{N.AmlNameL{N.AmlName{True{}, 1n+p, ss}, R}} == N.nm.dec(B.append(B.mask(N.nm.enc(N.AmlName{True{}, 1n+p, ss})), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}, ft_absurd(ok))
        case False{}:
          match u:
            case 0n:
              %mask_app(N.nm.carets(0n), N.nm.path(ss)) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, ss}, R}} == N.nm.dec(B.append(_, R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %mask_carets(0n) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, ss}, R}} == N.nm.dec(B.append(B.append(_, B.mask(N.nm.path(ss))), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %app_assoc(N.nm.carets(0n), B.mask(N.nm.path(ss)), R) : {Done{N.AmlNameL{N.AmlName{False{}, 0n, ss}, R}} == N.nm.dec(_) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              pth_dec(ss, R, and_l(N.AmlName.segs_ok(ss), Nat.is_lt(N.nm.len(ss), 256n), ok), and_r(N.AmlName.segs_ok(ss), Nat.is_lt(N.nm.len(ss), 256n), ok))
            case 1n+p:
              %mask_app(N.nm.carets(1n+p), N.nm.path(ss)) : {Done{N.AmlNameL{N.AmlName{False{}, 1n+p, ss}, R}} == N.nm.dec(B.append(_, R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %mask_carets(1n+p) : {Done{N.AmlNameL{N.AmlName{False{}, 1n+p, ss}, R}} == N.nm.dec(B.append(B.append(_, B.mask(N.nm.path(ss))), R)) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              %app_assoc(N.nm.carets(1n+p), B.mask(N.nm.path(ss)), R) : {Done{N.AmlNameL{N.AmlName{False{}, 1n+p, ss}, R}} == N.nm.dec(_) : Result<&2, &2, E.AcpiError, N.AmlNameL>}
              ups_rt(1n+p, ss, R, and_l(N.AmlName.segs_ok(ss), Nat.is_lt(N.nm.len(ss), 256n), ok), and_r(N.AmlName.segs_ok(ss), Nat.is_lt(N.nm.len(ss), 256n), ok))

def Laws.namestring_round_trip(n, rest, ok):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(N.AmlName.encode(n), rest)), B.append(B.Octets.to_list(N.AmlName.encode(n)), B.Octets.to_list(rest)), BL.octets_append_list(N.AmlName.encode(n), rest)) : {N.nm.pub(N.nm.dec(_)) == Done{N.AmlNameParsed{n, rest}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(N.nm.enc(n))), B.mask(N.nm.enc(n)), BL.octets_to_of(N.nm.enc(n))) : {N.nm.pub(N.nm.dec(B.append(_, B.Octets.to_list(rest)))) == Done{N.AmlNameParsed{n, rest}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}
  %BL.octets_of_to(rest) : {N.nm.pub(N.nm.dec(B.append(B.mask(N.nm.enc(n)), B.Octets.to_list(rest)))) == Done{N.AmlNameParsed{n, _}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}
  %dec_rt(n, B.Octets.to_list(rest), ok) : {N.nm.pub(_) == Done{N.AmlNameParsed{n, B.Octets.of_list(B.Octets.to_list(rest))}} : Result<&2, &2, E.AcpiError, N.AmlNameParsed>}
  {==}
# Octets lengths of the fields

def le32_len(+v: U32) -> {B.Octets.len(B.Octets.le32(v)) == 4n : Nat}:
  match v:
    case U32{w}:
      %Equal.sym(Nat, B.Octets.len(B.Octets.le32(U32{w})), B.len(B.Octets.to_list(B.Octets.le32(U32{w}))), BL.octets_len_list(B.Octets.le32(U32{w}))) : {_ == 4n : Nat}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.le32(U32{w}))), B.mask(B.le32(U32{w})), BL.octets_to_of(B.le32(U32{w}))) : {B.len(_) == 4n : Nat}
      {==}

def byte_len(+v: U32) -> {B.Octets.len(B.Octets.of_list([v])) == 1n : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list([v])), B.len(B.Octets.to_list(B.Octets.of_list([v]))), BL.octets_len_list(B.Octets.of_list([v]))) : {_ == 1n : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([v])), B.mask([v]), BL.octets_to_of([v])) : {B.len(_) == 1n : Nat}
  {==}

def hdr_rt(+s: B.Octets, +l: U32, +r: U32, +c: U32, +o: B.Octets, +t: B.Octets, +orv: U32, +ci: B.Octets, +cr: U32, +sig4: {B.Octets.len(s) == 4n : Nat}, +oem6: {B.Octets.len(o) == 6n : Nat}, +tid8: {B.Octets.len(t) == 8n : Nat}, +cid4: {B.Octets.len(ci) == 4n : Nat}, +rev8: {B.byte(r) == r : U32}, +ck8: {B.byte(c) == c : U32}) -> {H.AcpiHeader.decode(H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr})) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}:
  %sig4 : {H.hd.d1(B.Octets.split_at(_, B.Octets.append(s, B.Octets.append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr})) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(s), B.Octets.append(s, B.Octets.append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))))), Some{B.OctetsSplit{s, B.Octets.append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))))}}, BL.octets_split_at_append(s, B.Octets.append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))))) : {H.hd.d1(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr})) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %le32_len(l) : {H.hd.d2(B.Octets.split_at(_, B.Octets.append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(B.Octets.le32(l)), B.Octets.append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))))), Some{B.OctetsSplit{B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))}}, BL.octets_split_at_append(B.Octets.le32(l), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))))) : {H.hd.d2(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %byte_len(r) : {H.hd.d3(B.Octets.split_at(_, B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(H.hd.byte(r)), B.Octets.append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))), Some{B.OctetsSplit{H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))}}, BL.octets_split_at_append(H.hd.byte(r), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))))) : {H.hd.d3(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %byte_len(c) : {H.hd.d4(B.Octets.split_at(_, B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(H.hd.byte(c)), B.Octets.append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))), Some{B.OctetsSplit{H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))}}, BL.octets_split_at_append(H.hd.byte(c), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))))) : {H.hd.d4(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %oem6 : {H.hd.d5(B.Octets.split_at(_, B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(o), B.Octets.append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))), Some{B.OctetsSplit{o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))}}, BL.octets_split_at_append(o, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))))) : {H.hd.d5(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %tid8 : {H.hd.d6(B.Octets.split_at(_, B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(t), B.Octets.append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))), Some{B.OctetsSplit{t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))}}, BL.octets_split_at_append(t, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))))) : {H.hd.d6(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %le32_len(orv) : {H.hd.d7(B.Octets.split_at(_, B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(B.Octets.le32(orv)), B.Octets.append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))), Some{B.OctetsSplit{B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr))}}, BL.octets_split_at_append(B.Octets.le32(orv), B.Octets.append(ci, B.Octets.le32(cr)))) : {H.hd.d7(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %cid4 : {H.hd.d8(B.Octets.split_at(_, B.Octets.append(ci, B.Octets.le32(cr))), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t, H.hd.u32(B.Octets.le32(orv))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, B.OctetsSplit>, B.Octets.split_at(B.Octets.len(ci), B.Octets.append(ci, B.Octets.le32(cr))), Some{B.OctetsSplit{ci, B.Octets.le32(cr)}}, BL.octets_split_at_append(ci, B.Octets.le32(cr))) : {H.hd.d8(_, H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t, H.hd.u32(B.Octets.le32(orv))) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Nat, B.Octets.len(B.Octets.le32(cr)), 4n, le32_len(cr)) : {H.hd.d9(Nat.is_le(4n, _), H.AcpiHeader.encode(H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}), s, H.hd.u32(B.Octets.le32(l)), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t, H.hd.u32(B.Octets.le32(orv)), ci, B.Octets.le32(cr)) == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(B.Octets.le32(l), 0n), Some{l}, BL.octets_le32_round_trip(l)) : {Done{H.AcpiHeader{s, Maybe.default(&2, U32, _, 0), H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t, H.hd.u32(B.Octets.le32(orv)), ci, H.hd.u32(B.Octets.le32(cr))}} == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(B.Octets.le32(orv), 0n), Some{orv}, BL.octets_le32_round_trip(orv)) : {Done{H.AcpiHeader{s, l, H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t, Maybe.default(&2, U32, _, 0), ci, H.hd.u32(B.Octets.le32(cr))}} == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(B.Octets.le32(cr), 0n), Some{cr}, BL.octets_le32_round_trip(cr)) : {Done{H.AcpiHeader{s, l, H.hd.u8(H.hd.byte(r)), H.hd.u8(H.hd.byte(c)), o, t, orv, ci, Maybe.default(&2, U32, _, 0)}} == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([r])), B.mask([r]), BL.octets_to_of([r])) : {Done{H.AcpiHeader{s, l, H.hd.u8.list(_), H.hd.u8(H.hd.byte(c)), o, t, orv, ci, cr}} == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([c])), B.mask([c]), BL.octets_to_of([c])) : {Done{H.AcpiHeader{s, l, B.byte(r), H.hd.u8.list(_), o, t, orv, ci, cr}} == Done{H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %rev8 : {Done{H.AcpiHeader{s, l, B.byte(r), B.byte(c), o, t, orv, ci, cr}} == Done{H.AcpiHeader{s, l, _, c, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  %ck8 : {Done{H.AcpiHeader{s, l, B.byte(r), B.byte(c), o, t, orv, ci, cr}} == Done{H.AcpiHeader{s, l, B.byte(r), _, o, t, orv, ci, cr}} : Result<&2, &2, E.AcpiError, H.AcpiHeader>}
  {==}

def Laws.header_round_trip(h, sig4, oem6, tid8, cid4, rev8, ck8):
  match h:
    case H.AcpiHeader{s, l, r, c, o, t, orv, ci, cr}:
      hdr_rt(s, l, r, c, o, t, orv, ci, cr, sig4, oem6, tid8, cid4, rev8, ck8)

# Checksums: a table is accepted only on the branch where its checksum was
# found to be zero. Each lemma follows one decision of the parser.

def rdisc(-A: Data, +r: Result<&2, &2, E.AcpiError, A>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{x}:
      Empty

def fd_absurd(-A: Data, -x: E.AcpiError, -y: A, +e: {Fail{x} == Done{y} : Result<&2, &2, E.AcpiError, A>}) -> Empty:
  %e : rdisc(A, _)
  Unit{}

def done_inj(-A: Data, +a: A, +b: A, +e: {Done{a} == Done{b} : Result<&2, &2, E.AcpiError, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, E.AcpiError, A>, A, x => Result.default(&2, &2, E.AcpiError, A, x, a), Done{a}, Done{b}, e)

def done_t(-A: Data, +r: Result<&2, &2, E.AcpiError, A>, +x: A, +e: {r == Done{x} : Result<&2, &2, E.AcpiError, A>}) -> {Result.is_done(&2, &2, E.AcpiError, A, r) == True{} : Bool}:
  %Equal.sym(Result<&2, &2, E.AcpiError, A>, r, Done{x}, e) : {Result.is_done(&2, &2, E.AcpiError, A, _) == True{} : Bool}
  {==}

def c3_ok(+b: Bool, +r: B.Octets, +raw: B.Octets, +eb: {C.AcpiChecksum.ok(r) == b : Bool}, +e: {H.sdt.c3(b, r) == Done{raw} : Result<&2, &2, E.AcpiError, B.Octets>}) -> {C.AcpiChecksum.ok(raw) == True{} : Bool}:
  match b:
    case True{}:
      %done_inj(B.Octets, r, raw, e) : {C.AcpiChecksum.ok(_) == True{} : Bool}
      eb
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(raw) == True{} : Bool}, fd_absurd(B.Octets, E.AcpiBadChecksum{C.AcpiChecksum.sum(r)}, raw, e))

def c2_ok(+b: Bool, +l: U32, +o: B.Octets, +raw: B.Octets, +e: {H.sdt.c2(b, l, o) == Done{raw} : Result<&2, &2, E.AcpiError, B.Octets>}) -> {C.AcpiChecksum.ok(raw) == True{} : Bool}:
  match b:
    case True{}:
      c3_ok(C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)), B.Octets.take(U32.to_nat(l), o), raw, {==}, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(raw) == True{} : Bool}, fd_absurd(B.Octets, E.AcpiBadLength{l}, raw, e))

def c1_ok(+m: Maybe<&2, U32>, +o: B.Octets, +raw: B.Octets, +e: {H.sdt.c1(m, o) == Done{raw} : Result<&2, &2, E.AcpiError, B.Octets>}) -> {C.AcpiChecksum.ok(raw) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({C.AcpiChecksum.ok(raw) == True{} : Bool}, fd_absurd(B.Octets, E.AcpiTooShort{36n, B.Octets.len(o)}, raw, e))
    case Some{l}:
      c2_ok(Bool.and(Nat.is_le(36n, U32.to_nat(l)), Nat.is_le(U32.to_nat(l), B.Octets.len(o))), l, o, raw, e)

def Laws.sdt_check_sums(o, raw, e):
  c1_ok(B.Octets.le32_at(o, 4n), o, raw, e)

# the same decisions, from "the check succeeded", to the table's bytes

def c3_d(+b: Bool, +r: B.Octets, +eb: {C.AcpiChecksum.ok(r) == b : Bool}, +e: {Result.is_done(&2, &2, E.AcpiError, B.Octets, H.sdt.c3(b, r)) == True{} : Bool}) -> {C.AcpiChecksum.ok(r) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(r) == True{} : Bool}, ft_absurd(e))

def c2_d(+b: Bool, +l: U32, +o: B.Octets, +e: {Result.is_done(&2, &2, E.AcpiError, B.Octets, H.sdt.c2(b, l, o)) == True{} : Bool}) -> {C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)) == True{} : Bool}:
  match b:
    case True{}:
      c3_d(C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)), B.Octets.take(U32.to_nat(l), o), {==}, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)) == True{} : Bool}, ft_absurd(e))

def c1_d(+m: Maybe<&2, U32>, +o: B.Octets, +e: {Result.is_done(&2, &2, E.AcpiError, B.Octets, H.sdt.c1(m, o)) == True{} : Bool}) -> {C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(Maybe.default(&2, U32, m, 4294967295)), o)) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(Maybe.default(&2, U32, None{}, 4294967295)), o)) == True{} : Bool}, ft_absurd(e))
    case Some{l}:
      c2_d(Bool.and(Nat.is_le(36n, U32.to_nat(l)), Nat.is_le(U32.to_nat(l), B.Octets.len(o))), l, o, e)

def check_d(+o: B.Octets, +e: {Result.is_done(&2, &2, E.AcpiError, B.Octets, H.AcpiSdt.check(o)) == True{} : Bool}) -> {C.AcpiChecksum.ok(H.AcpiSdt.bytes(o)) == True{} : Bool}:
  c1_d(B.Octets.le32_at(o, 4n), o, e)

def sdt_go_d(+c: Result<&2, &2, E.AcpiError, B.Octets>, +e: {Result.is_done(&2, &2, E.AcpiError, H.AcpiSdt, H.sdt.parse.go(c)) == True{} : Bool}) -> {Result.is_done(&2, &2, E.AcpiError, B.Octets, c) == True{} : Bool}:
  match c:
    case Fail{x}:
      Empty.absurd({Result.is_done(&2, &2, E.AcpiError, B.Octets, Fail{x}) == True{} : Bool}, ft_absurd(e))
    case Done{raw}:
      {==}

def reg_go_d(+reg: R.AcpiRegistry, +r: Result<&2, &2, E.AcpiError, H.AcpiSdt>, +t: R.AcpiTable<R.AcpiNoExt>, +e: {R.reg.go(~R.AcpiNoExt, ~R.AcpiNoExt.parse, reg, r) == Done{t} : Result<&2, &2, E.AcpiError, R.AcpiTable<R.AcpiNoExt>>}) -> {Result.is_done(&2, &2, E.AcpiError, H.AcpiSdt, r) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Result.is_done(&2, &2, E.AcpiError, H.AcpiSdt, Fail{x}) == True{} : Bool}, fd_absurd(R.AcpiTable<R.AcpiNoExt>, x, t, e))
    case Done{x}:
      {==}

def Laws.table_checksums(reg, o, t, e):
  check_d(o, sdt_go_d(H.AcpiSdt.check(o), reg_go_d(reg, H.AcpiSdt.parse(o), t, e)))

# The RSDP

def rp3_d(+b: Bool, +o: B.Octets, +e: {Result.is_done(&2, &2, E.AcpiError, P.AcpiRsdp, P.rs.p3(b, o)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ft_absurd(e))

def rp2_d(+b: Bool, +o: B.Octets, +e: {Result.is_done(&2, &2, E.AcpiError, P.AcpiRsdp, P.rs.p2(b, o)) == True{} : Bool}) -> {C.AcpiChecksum.ok(B.Octets.take(20n, o)) == True{} : Bool}:
  match b:
    case True{}:
      rp3_d(C.AcpiChecksum.ok(B.Octets.take(20n, o)), o, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(20n, o)) == True{} : Bool}, ft_absurd(e))

def rp1_d(+b: Bool, +o: B.Octets, +e: {Result.is_done(&2, &2, E.AcpiError, P.AcpiRsdp, P.rs.p1(b, o)) == True{} : Bool}) -> {C.AcpiChecksum.ok(B.Octets.take(20n, o)) == True{} : Bool}:
  match b:
    case True{}:
      rp2_d(B.Octets.is_eq(B.Octets.take(8n, o), P.AcpiRsdp.signature()), o, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(20n, o)) == True{} : Bool}, ft_absurd(e))

def Laws.rsdp_checksum(o, r, e):
  rp1_d(Nat.is_le(20n, B.Octets.len(o)), o, done_t(P.AcpiRsdp, P.AcpiRsdp.parse(o), r, e))

# the extended checksum: followed to the structure answered, whose checked
# length is the one summed

def rx7(+b: Bool, +l: U32, +o: B.Octets, +r: P.AcpiRsdp, +eb: {C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)) == b : Bool}, +e: {P.rs.p7(b, l, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      %done_inj(P.AcpiRsdp, P.AcpiRsdp{F.AcpiF.bytes(o, 9n, 6n), F.AcpiF.u8(o, 15n), F.AcpiF.u32(o, 16n), Some{P.AcpiRsdpExt{l, F.AcpiF.u64(o, 24n)}}}, r, e) : {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(_), o)) == True{} : Bool}
      eb
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}, fd_absurd(P.AcpiRsdp, E.AcpiRsdpBadExtChecksum{C.AcpiChecksum.sum(B.Octets.take(U32.to_nat(l), o))}, r, e))

def rx6(+b: Bool, +l: U32, +o: B.Octets, +r: P.AcpiRsdp, +e: {P.rs.p6(b, l, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      rx7(C.AcpiChecksum.ok(B.Octets.take(U32.to_nat(l), o)), l, o, r, {==}, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}, fd_absurd(P.AcpiRsdp, E.AcpiBadLength{l}, r, e))

def rx5(+b: Bool, +o: B.Octets, +r: P.AcpiRsdp, +e: {P.rs.p5(b, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      rx6(Bool.and(Nat.is_le(36n, U32.to_nat(F.AcpiF.u32(o, 20n))), Nat.is_le(U32.to_nat(F.AcpiF.u32(o, 20n)), B.Octets.len(o))), F.AcpiF.u32(o, 20n), o, r, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}, fd_absurd(P.AcpiRsdp, E.AcpiTooShort{36n, B.Octets.len(o)}, r, e))

def rx4(+b: Bool, +o: B.Octets, +r: P.AcpiRsdp, +ok20: {C.AcpiChecksum.ok(B.Octets.take(20n, o)) == True{} : Bool}, +e: {P.rs.p4(b, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      %done_inj(P.AcpiRsdp, P.AcpiRsdp{F.AcpiF.bytes(o, 9n, 6n), F.AcpiF.u8(o, 15n), F.AcpiF.u32(o, 16n), None{}}, r, e) : {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(_), o)) == True{} : Bool}
      ok20
    case False{}:
      rx5(Nat.is_le(36n, B.Octets.len(o)), o, r, e)

def rx3(+b: Bool, +o: B.Octets, +r: P.AcpiRsdp, +eb: {C.AcpiChecksum.ok(B.Octets.take(20n, o)) == b : Bool}, +e: {P.rs.p3(b, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      rx4(U32.is_lt(F.AcpiF.u8(o, 15n), 2), o, r, eb, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}, fd_absurd(P.AcpiRsdp, E.AcpiRsdpBadChecksum{C.AcpiChecksum.sum(B.Octets.take(20n, o))}, r, e))

def rx2(+b: Bool, +o: B.Octets, +r: P.AcpiRsdp, +e: {P.rs.p2(b, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      rx3(C.AcpiChecksum.ok(B.Octets.take(20n, o)), o, r, {==}, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}, fd_absurd(P.AcpiRsdp, E.AcpiBadSignature{B.Octets.take(8n, o)}, r, e))

def rx1(+b: Bool, +o: B.Octets, +r: P.AcpiRsdp, +e: {P.rs.p1(b, o) == Done{r} : Result<&2, &2, E.AcpiError, P.AcpiRsdp>}) -> {C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}:
  match b:
    case True{}:
      rx2(B.Octets.is_eq(B.Octets.take(8n, o), P.AcpiRsdp.signature()), o, r, e)
    case False{}:
      Empty.absurd({C.AcpiChecksum.ok(B.Octets.take(P.AcpiRsdp.checked(r), o)) == True{} : Bool}, fd_absurd(P.AcpiRsdp, E.AcpiTooShort{20n, B.Octets.len(o)}, r, e))

def Laws.rsdp_ext_checksum(o, r, e):
  rx1(Nat.is_le(20n, B.Octets.len(o)), o, r, e)

# The step bound: AmlM.run.go counts each step it takes, and stops when its
# fuel runs out

def le_refl(+u: Nat) -> {Nat.is_le(u, u) == True{} : Bool}:
  match u:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_step(+a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n+0n) == True{} : Bool}, ft_absurd(e))
    case 1n+ap 1n+bp:
      le_step(ap, bp, e)

def le_add(+p: Nat, +u: Nat) -> {Nat.is_le(u, Nat.add(p, u)) == True{} : Bool}:
  match p:
    case 0n:
      le_refl(u)
    case 1n+q:
      le_step(u, Nat.add(q, u), le_add(q, u))

def add_succ(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def run_go_le(+n: Nat, +h: Bool, +m: I.AmlMachine<Hs.AmlMemHost>, +u: Nat) -> {Nat.is_le(I.AmlRun.steps(Hs.AmlMemHost, I.AmlM.run.go(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, n, h, m, u)), Nat.add(n, u)) == True{} : Bool}:
  match n:
    case 0n:
      le_refl(u)
    case 1n+p:
      match h:
        case True{}:
          le_step(u, Nat.add(p, u), le_add(p, u))
        case False{}:
          %Equal.sym(Nat, 1n+Nat.add(p, u), Nat.add(p, 1n+u), add_succ(p, u)) : {Nat.is_le(I.AmlRun.steps(Hs.AmlMemHost, I.AmlM.run.go(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, p, I.AmlMachine.halted(Hs.AmlMemHost, I.AmlM.step(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, m)), I.AmlM.step(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, m), 1n+u)), _) == True{} : Bool}
          run_go_le(p, I.AmlMachine.halted(Hs.AmlMemHost, I.AmlM.step(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, m)), I.AmlM.step(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, m), 1n+u)

def Laws.run_steps_bound(n, m):
  %add_zero(n) : {Nat.is_le(I.AmlRun.steps(Hs.AmlMemHost, I.AmlM.run.go(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, n, I.AmlMachine.halted(Hs.AmlMemHost, m), m, 0n)), _) == True{} : Bool}
  run_go_le(n, I.AmlMachine.halted(Hs.AmlMemHost, m), m, 0n)

# an outcome counts the steps of its run
def outcome_steps(+r: I.AmlRun<Hs.AmlMemHost>) -> {I.AmlRun.steps(Hs.AmlMemHost, r) == A.AmlOutcome.steps(Hs.AmlMemHost, A.AmlOutcome.of_run(Hs.AmlMemHost, r)) : Nat}:
  match r:
    case I.AmlRun{m, s}:
      match m:
        case I.AmlMachine{md, c, fs, w}:
          match w:
            case I.AmlWorld{ctx, ns, h, e}:
              match e:
                case I.AmlEnv{wd, o, nts, d, cl}:
                  {==}

def Laws.load_steps_bound(s, aml, n):
  %outcome_steps(I.AmlM.run(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, n, A.AmlSystem.loader(Hs.AmlMemHost, s, aml))) : {Nat.is_le(_, n) == True{} : Bool}
  Laws.run_steps_bound(n, A.AmlSystem.loader(Hs.AmlMemHost, s, aml))

def Laws.eval_steps_bound(s, p, args, n):
  %outcome_steps(I.AmlM.run(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, n, A.AmlSystem.caller(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, p, args))) : {Nat.is_le(_, n) == True{} : Bool}
  Laws.run_steps_bound(n, A.AmlSystem.caller(~Hs.AmlMemHost, ~Hs.AmlMemHost.io, s, p, args))

# Witnesses and vectors: by computation

def Laws.pkglength_example():
  Laws.pkglength_round_trip(1000, B.Octets.of_string("AML"), {==})

def Laws.namestring_example():
  Laws.namestring_round_trip(N.AmlName.of_text("\\_SB.PCI0.LPCB"), B.Octets.of_string("x"), {==})

def Laws.header_example():
  Laws.header_round_trip(X.ex.hdr("APIC", 5), {==}, {==}, {==}, {==}, {==}, {==})

def Laws.check_example():
  {==}

def Laws.parse_example():
  {==}

def Laws.rsdp_example():
  {==}

def Laws.rsdp_v1_example():
  {==}

def Laws.pkglength_63():
  {==}

def Laws.pkglength_64():
  {==}

def Laws.pkglength_4095():
  {==}

def Laws.pkglength_4096():
  {==}

def Laws.pkglength_max():
  {==}

def Laws.pkglength_reserved():
  {==}

def Laws.name_dual():
  {==}

def Laws.name_multi():
  {==}

def Laws.name_parents():
  {==}

def Laws.name_root():
  {==}

def Laws.name_bad_seg():
  {==}

def Laws.eisaid_power_button():
  {==}

def Laws.eisaid_pci():
  {==}

def Laws.aml_name_hid():
  {==}

def Laws.aml_method_sta():
  {==}

def Laws.checksum_built():
  {==}

def Laws.checksum_broken():
  {==}

def Laws.aml_eval_sta():
  {==}
