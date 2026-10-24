# Proof helpers for bend-osdev-asn1: the typed readers of BOOLEAN, NULL,
# OCTET STRING, BIT STRING, the character strings and the constructed types
# read back what their writers write, and what they accept. Each reader
# takes the tag it expects, compared with the element's (pi.tag_refl); a
# bit string's leading octet is its count of unused bits (a value below
# 8, ab.byte), and DER's check that those bits are zero holds trivially
# when there are none (pp.and0: any word masked by zero is zero).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P
import ./bits.bend as Bi
import ./string.bend as S
import ./build.bend as Bu
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_byte.bend as AB
import ./proof_int.bend as PI
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# Bool

def pp.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.when_true(on: Bool) -> {R.a1.when(on, True{}) == True{} : Bool}:
  match on:
    case True{}:
      {==}
    case False{}:
      {==}

# Words masked by zero

def pp.wand0(n: Nat, w: Word(n)) -> {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{h, +t}:
          match h:
            case True{}:
              %pp.wand0(p, t) : {WCon{False{}, Word.and(p, t, Word.zero(p))} == WCon{False{}, _} : Word.Con<p>}
              {==}
            case False{}:
              %pp.wand0(p, t) : {WCon{False{}, Word.and(p, t, Word.zero(p))} == WCon{False{}, _} : Word.Con<p>}
              {==}

def pp.and0(x: U32) -> {U32.and(x, 0) == 0 : U32}:
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, v => U32{v}, Word.and(32n, w, Word.zero(32n)), Word.zero(32n), pp.wand0(32n, w))

# BOOLEAN

def pp.bool_rt(+r: R.Asn1Rules, b: Bool) -> {P.Asn1.get_bool(r, P.Asn1.bool(b)) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# OCTET STRING

def pp.octets_rt(+r: R.Asn1Rules, +t: T.Asn1Tag, +o: B.Octets) -> {P.Asn1.get_octets_as(r, t, P.Asn1.octets_as(t, o)) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, PI.pi.tag_refl(t)) : {P.a1.prim_as.pick(_, o) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}
  {==}

# BIT STRING

# a primitive BIT STRING element of tag t: its contents as a bit string
def pp.bits_prim(+r: R.Asn1Rules, +t: T.Asn1Tag, +c: B.Octets) -> {Bi.a1.bits.of_prim(R.Asn1Rules.values(r), B.Octets.to_list(c)) == Bi.Asn1.get_bits_as(r, t, N.Asn1Prim{t, c}) : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}:
  %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, PI.pi.tag_refl(t)) : {Bi.a1.bits.of_prim(R.Asn1Rules.values(r), B.Octets.to_list(c)) == Bi.a1.bits.prim(_, R.Asn1Rules.values(r), c) : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  {==}

# without DER's check of the unused bits, every well-formed bit string
def pp.bits_ber(+r: R.Asn1Rules, +hv: {R.Asn1Rules.values(r) == False{} : Bool}, +t: T.Asn1Tag, +u: Nat, +o: B.Octets, +hok: {Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}) == True{} : Bool}) -> {Bi.Asn1.get_bits_as(r, t, Bi.Asn1.bits_as(t, Bi.Asn1Bits{u, o})) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}:
  +hu = AN.an.and_l(Nat.is_le(u, 7n), Bool.or(Nat.is_lt(0n, B.Octets.len(o)), Nat.is_eq(u, 0n)), hok)
  +hb = AB.ab.byte(u, AN.an.le_lt_succ(u, 255n, UO.nat_le_trans(u, 7n, 255n, hu, {==})))
  %pp.bits_prim(r, t, B.Octets.cons(U32.from_nat(u), o)) : {_ == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, R.Asn1Rules.values(r), False{}, hv) : {Bi.a1.bits.of_prim(_, B.Octets.to_list(B.Octets.cons(U32.from_nat(u), o))) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(U32.from_nat(u), o)), Con{B.byte(U32.from_nat(u)), B.Octets.to_list(o)}, BL.octets_cons_list(U32.from_nat(u), o)) : {Bi.a1.bits.of_prim(False{}, _) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(u))), u, hb) : {Bi.a1.bits.check(Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{_, B.Octets.of_list(B.Octets.to_list(o))}), True{}), Bi.Asn1Bits{_, B.Octets.of_list(B.Octets.to_list(o))}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, AL.al.of_to(o)) : {Bi.a1.bits.check(Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{u, _}), True{}), Bi.Asn1Bits{u, _}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}), True{}, hok) : {Bi.a1.bits.check(Bool.and(_, True{}), Bi.Asn1Bits{u, o}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  {==}

# under any rules, a well-formed bit string whose unused bits are zero
def pp.bits_rt(+r: R.Asn1Rules, +t: T.Asn1Tag, +u: Nat, +o: B.Octets, +hok: {Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}) == True{} : Bool}, +hc: {Bi.a1.bits.clear(u, o) == True{} : Bool}) -> {Bi.Asn1.get_bits_as(r, t, Bi.Asn1.bits_as(t, Bi.Asn1Bits{u, o})) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}:
  +hu = AN.an.and_l(Nat.is_le(u, 7n), Bool.or(Nat.is_lt(0n, B.Octets.len(o)), Nat.is_eq(u, 0n)), hok)
  +hb = AB.ab.byte(u, AN.an.le_lt_succ(u, 255n, UO.nat_le_trans(u, 7n, 255n, hu, {==})))
  +der = R.Asn1Rules.values(r)
  %pp.bits_prim(r, t, B.Octets.cons(U32.from_nat(u), o)) : {_ == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(U32.from_nat(u), o)), Con{B.byte(U32.from_nat(u)), B.Octets.to_list(o)}, BL.octets_cons_list(U32.from_nat(u), o)) : {Bi.a1.bits.of_prim(der, _) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(u))), u, hb) : {Bi.a1.bits.check(Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{_, B.Octets.of_list(B.Octets.to_list(o))}), R.a1.when(der, Bi.a1.bits.clear(_, B.Octets.of_list(B.Octets.to_list(o))))), Bi.Asn1Bits{_, B.Octets.of_list(B.Octets.to_list(o))}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, AL.al.of_to(o)) : {Bi.a1.bits.check(Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{u, _}), R.a1.when(der, Bi.a1.bits.clear(u, _))), Bi.Asn1Bits{u, _}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}), True{}, hok) : {Bi.a1.bits.check(Bool.and(_, R.a1.when(der, Bi.a1.bits.clear(u, o))), Bi.Asn1Bits{u, o}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, Bi.a1.bits.clear(u, o), True{}, hc) : {Bi.a1.bits.check(R.a1.when(der, _), Bi.Asn1Bits{u, o}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, R.a1.when(der, True{}), True{}, pp.when_true(der)) : {Bi.a1.bits.check(_, Bi.Asn1Bits{u, o}) == Done{Bi.Asn1Bits{u, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  {==}

# under any rules, a bit string of whole octets
def pp.bits_whole(+r: R.Asn1Rules, +t: T.Asn1Tag, +o: B.Octets) -> {Bi.Asn1.get_bits_as(r, t, Bi.Asn1.bits_as(t, Bi.Asn1Bits.of_octets(o))) == Done{Bi.Asn1Bits.of_octets(o)} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}:
  %pp.bits_prim(r, t, B.Octets.cons(0, o)) : {_ == Done{Bi.Asn1Bits{0n, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.cons(0, o)), Con{B.byte(0), B.Octets.to_list(o)}, BL.octets_cons_list(0, o)) : {Bi.a1.bits.of_prim(R.Asn1Rules.values(r), _) == Done{Bi.Asn1Bits{0n, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, AL.al.of_to(o)) : {Bi.a1.bits.check(Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{0n, _}), R.a1.when(R.Asn1Rules.values(r), Bi.a1.bits.clear(0n, _))), Bi.Asn1Bits{0n, _}) == Done{Bi.Asn1Bits{0n, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, Bool.or(Nat.is_lt(0n, B.Octets.len(o)), True{}), True{}, pp.or_true(Nat.is_lt(0n, B.Octets.len(o)))) : {Bi.a1.bits.check(Bool.and(_, R.a1.when(R.Asn1Rules.values(r), Bi.a1.bits.clear(0n, o))), Bi.Asn1Bits{0n, o}) == Done{Bi.Asn1Bits{0n, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(U32, U32.and(Bi.a1.bits.last(B.Octets.to_list(o), 0), 0), 0, pp.and0(Bi.a1.bits.last(B.Octets.to_list(o), 0))) : {Bi.a1.bits.check(R.a1.when(R.Asn1Rules.values(r), U32.is_eq(_, 0)), Bi.Asn1Bits{0n, o}) == Done{Bi.Asn1Bits{0n, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  %Equal.sym(Bool, R.a1.when(R.Asn1Rules.values(r), True{}), True{}, pp.when_true(R.Asn1Rules.values(r))) : {Bi.a1.bits.check(_, Bi.Asn1Bits{0n, o}) == Done{Bi.Asn1Bits{0n, o}} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}
  {==}

# Character strings

def pp.of_tag(k: S.Asn1StrKind) -> {S.Asn1StrKind.of_tag(S.Asn1StrKind.tag(k)) == Some{k} : Maybe<&2, S.Asn1StrKind>}:
  match k:
    case S.Asn1Utf8{}:
      {==}
    case S.Asn1Numeric{}:
      {==}
    case S.Asn1Printable{}:
      {==}
    case S.Asn1Teletex{}:
      {==}
    case S.Asn1Ia5{}:
      {==}
    case S.Asn1Visible{}:
      {==}
    case S.Asn1UniversalStr{}:
      {==}
    case S.Asn1Bmp{}:
      {==}

# a string element of tag t holding a valid string of type k
def pp.str_got(+r: R.Asn1Rules, +t: T.Asn1Tag, +k: S.Asn1StrKind, +o: B.Octets, +hv: {S.Asn1Str.valid(S.Asn1Str{k, o}) == True{} : Bool}) -> {S.a1.str.got(k, P.a1.string_value(R.Asn1Rules.prim_strings(r), t, S.Asn1StrKind.tag(k), N.Asn1Prim{t, o})) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}:
  %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, PI.pi.tag_refl(t)) : {S.a1.str.got(k, P.a1.prim_as.pick(_, o)) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  %Equal.sym(Bool, S.Asn1Str.valid(S.Asn1Str{k, o}), True{}, hv) : {S.a1.str.check.pick(_, S.Asn1Str{k, o}) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  {==}

def pp.str_rt(+r: R.Asn1Rules, +k: S.Asn1StrKind, +o: B.Octets, +hv: {S.Asn1Str.valid(S.Asn1Str{k, o}) == True{} : Bool}) -> {S.Asn1.get_string(r, S.Asn1.string(S.Asn1Str{k, o})) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}:
  %Equal.sym(Maybe<&2, S.Asn1StrKind>, S.Asn1StrKind.of_tag(S.Asn1StrKind.tag(k)), Some{k}, pp.of_tag(k)) : {S.a1.str.read(_, r, N.Asn1Prim{S.Asn1StrKind.tag(k), o}) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}
  pp.str_got(r, S.Asn1StrKind.tag(k), k, o, hv)

def pp.str_as_rt(+r: R.Asn1Rules, +t: T.Asn1Tag, +k: S.Asn1StrKind, +o: B.Octets, +hv: {S.Asn1Str.valid(S.Asn1Str{k, o}) == True{} : Bool}) -> {S.Asn1.get_string_as(r, t, k, Bu.Asn1.implicit(t, S.Asn1.string(S.Asn1Str{k, o}))) == Done{S.Asn1Str{k, o}} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}:
  pp.str_got(r, t, k, o, hv)

# Constructed values and tags

def pp.cons_rt(+t: T.Asn1Tag, +xs: List<&2, N.Asn1Node>) -> {Bu.Asn1.cons_as(t, N.Asn1Cons{t, xs}) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}:
  %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, PI.pi.tag_refl(t)) : {Bu.a1.cons_as.pick(_, xs) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}
  {==}

def pp.explicit_rt(+n: Nat, +x: N.Asn1Node) -> {Bu.Asn1.get_explicit(n, Bu.Asn1.explicit(n, x)) == Done{x} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}:
  %Equal.sym(Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>, Bu.Asn1.cons_as(T.Asn1Tag.context(n), N.Asn1Cons{T.Asn1Tag.context(n), [x]}), Done{[x]}, pp.cons_rt(T.Asn1Tag.context(n), [x])) : {Bu.a1.one_of(_) == Done{x} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
  {==}

def pp.untag_rt(+t: T.Asn1Tag, +u: T.Asn1Tag, x: N.Asn1Node) -> {Bu.Asn1.untag(t, u, Bu.Asn1.implicit(t, x)) == Done{Bu.Asn1.implicit(u, x)} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}:
  match x:
    case N.Asn1Prim{v, +o}:
      %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, PI.pi.tag_refl(t)) : {Bu.a1.untag.pick(_, u, N.Asn1Prim{t, o}) == Done{N.Asn1Prim{u, o}} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
      {==}
    case N.Asn1Cons{v, +xs}:
      %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, PI.pi.tag_refl(t)) : {Bu.a1.untag.pick(_, u, N.Asn1Cons{t, xs}) == Done{N.Asn1Cons{u, xs}} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
      {==}

def pp.has_tag(+t: T.Asn1Tag, x: N.Asn1Node) -> {Bu.Asn1.has_tag(t, Bu.Asn1.implicit(t, x)) == True{} : Bool}:
  match x:
    case N.Asn1Prim{v, o}:
      PI.pi.tag_refl(t)
    case N.Asn1Cons{v, xs}:
      PI.pi.tag_refl(t)
