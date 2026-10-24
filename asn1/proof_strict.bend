# Proof helpers for bend-osdev-asn1: the typed readers accept exactly what
# the writers write. An element a reader answers for is the element the
# writer writes for that answer: the tag read is the tag expected (tags
# compared equal are equal, sx.tag_eq), BOOLEAN's octet is 00 or, under
# DER's value checks, FF; NULL has no octets; a string under DER's
# primitive-only rule is primitive; a bit string's first octet, a count
# of unused bits below 8, is the octet the writer puts down for it. And a
# string read is valid for its type.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P
import ./bits.bend as Bi
import ./string.bend as S
import ./build.bend as Bu
import ./time.bend as Ti
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_u32.bend as AU
import ./proof_byte.bend as AB
import ./proof_oct.bend as OA

# Results

def sx.disc(-A: Kind(&2), r: Result<&2, &2, E.Asn1Error, A>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

# a failure is not an answer
def sx.fd(-A: Kind(&2), -x: E.Asn1Error, -y: A, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, A>}) -> Empty:
  %e : sx.disc(A, _)
  Unit{}

def sx.val(-A: Kind(&2), r: Result<&2, &2, E.Asn1Error, A>, d: A) -> A:
  match r:
    case Fail{x}:
      d
    case Done{y}:
      y

# answers are equal when their values are
def sx.dd(-A: Kind(&2), -a: A, -b: A, e: {Done{a} == Done{b} : Result<&2, &2, E.Asn1Error, A>}) -> {a == b : A}:
  Equal.cong(Result<&2, &2, E.Asn1Error, A>, A, r => sx.val(A, r, a), Done{a}, Done{b}, e)

# Tags

def sx.cls_eq(c: T.Asn1Class, d: T.Asn1Class, +h: {T.Asn1Class.is_eq(c, d) == True{} : Bool}) -> {c == d : T.Asn1Class}:
  match c d:
    case T.Asn1Universal{} T.Asn1Universal{}:
      {==}
    case T.Asn1Universal{} T.Asn1Application{}:
      Empty.absurd({T.Asn1Universal{} == T.Asn1Application{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Universal{} T.Asn1Context{}:
      Empty.absurd({T.Asn1Universal{} == T.Asn1Context{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Universal{} T.Asn1Private{}:
      Empty.absurd({T.Asn1Universal{} == T.Asn1Private{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Application{} T.Asn1Universal{}:
      Empty.absurd({T.Asn1Application{} == T.Asn1Universal{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Application{} T.Asn1Application{}:
      {==}
    case T.Asn1Application{} T.Asn1Context{}:
      Empty.absurd({T.Asn1Application{} == T.Asn1Context{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Application{} T.Asn1Private{}:
      Empty.absurd({T.Asn1Application{} == T.Asn1Private{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Context{} T.Asn1Universal{}:
      Empty.absurd({T.Asn1Context{} == T.Asn1Universal{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Context{} T.Asn1Application{}:
      Empty.absurd({T.Asn1Context{} == T.Asn1Application{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Context{} T.Asn1Context{}:
      {==}
    case T.Asn1Context{} T.Asn1Private{}:
      Empty.absurd({T.Asn1Context{} == T.Asn1Private{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Universal{}:
      Empty.absurd({T.Asn1Private{} == T.Asn1Universal{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Application{}:
      Empty.absurd({T.Asn1Private{} == T.Asn1Application{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Context{}:
      Empty.absurd({T.Asn1Private{} == T.Asn1Context{} : T.Asn1Class}, AN.an.ft(h))
    case T.Asn1Private{} T.Asn1Private{}:
      {==}

# tags compared equal are equal
def sx.tag_eq(t: T.Asn1Tag, u: T.Asn1Tag, +h: {T.Asn1Tag.is_eq(t, u) == True{} : Bool}) -> {t == u : T.Asn1Tag}:
  match t u:
    case T.Asn1Tag{+c, +n} T.Asn1Tag{+d, +k}:
      +hc = sx.cls_eq(c, d, AN.an.and_l(T.Asn1Class.is_eq(c, d), Nat.is_eq(n, k), h))
      +hn = AN.an.eq_sound(n, k, AN.an.and_r(T.Asn1Class.is_eq(c, d), Nat.is_eq(n, k), h))
      %hc : {T.Asn1Tag{c, n} == T.Asn1Tag{_, k} : T.Asn1Tag}
      %hn : {T.Asn1Tag{c, n} == T.Asn1Tag{c, _} : T.Asn1Tag}
      {==}

# Octets

def sx.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

def sx.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

# an octet of an Octets is its own byte, and its tail is masked
def sx.cons_fix(+x: U32, +t: List<&2, U32>, +h: {B.mask(Con{x, t}) == Con{x, t} : List<&2, U32>}) -> {B.byte(x) == x : U32}:
  Equal.cong(List<&2, U32>, U32, l => sx.head(l), B.mask(Con{x, t}), Con{x, t}, h)

def sx.cons_fix_t(+x: U32, +t: List<&2, U32>, +h: {B.mask(Con{x, t}) == Con{x, t} : List<&2, U32>}) -> {B.mask(t) == t : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, l => sx.tail(l), B.mask(Con{x, t}), Con{x, t}, h)

# Octets are the Octets of their list
def sx.of_to(+o: B.Octets) -> {o == B.Octets.of_list(B.Octets.to_list(o)) : B.Octets}:
  Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, AL.al.of_to(o))

# BOOLEAN

def sx.bool_v(z: Bool, f: Bool, +v: U32, -b: Bool, +hz: {U32.is_eq(v, 0) == z : Bool}, +hf: {U32.is_eq(v, 255) == f : Bool}, +e: {P.a1.bool.pick(z, f, True{}) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}) -> {B.Octets.of_list([v]) == B.Octets.of_list([Bool.pick(U32, b, 255, 0)]) : B.Octets}:
  match z f:
    case True{} _:
      +ev = AU.au.is_eq_sound(v, 0, hz)
      +eb = sx.dd(Bool, False{}, b, e)
      %eb : {B.Octets.of_list([v]) == B.Octets.of_list([Bool.pick(U32, _, 255, 0)]) : B.Octets}
      %ev : {B.Octets.of_list([v]) == B.Octets.of_list([_]) : B.Octets}
      {==}
    case False{} True{}:
      +ev = AU.au.is_eq_sound(v, 255, hf)
      +eb = sx.dd(Bool, True{}, b, e)
      %eb : {B.Octets.of_list([v]) == B.Octets.of_list([Bool.pick(U32, _, 255, 0)]) : B.Octets}
      %ev : {B.Octets.of_list([v]) == B.Octets.of_list([_]) : B.Octets}
      {==}
    case False{} False{}:
      Empty.absurd({B.Octets.of_list([v]) == B.Octets.of_list([Bool.pick(U32, b, 255, 0)]) : B.Octets}, sx.fd(Bool, E.Asn1BadValue{}, b, e))

def sx.bool_read(xs: List<&2, U32>, -b: Bool, +e: {P.a1.bool.read(xs, True{}) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}) -> {B.Octets.of_list(xs) == B.Octets.of_list([Bool.pick(U32, b, 255, 0)]) : B.Octets}:
  match xs:
    case Nil{}:
      Empty.absurd({B.Octets.of_list(Nil{}) == B.Octets.of_list([Bool.pick(U32, b, 255, 0)]) : B.Octets}, sx.fd(Bool, E.Asn1BadValue{}, b, e))
    case Con{+v, Nil{}}:
      sx.bool_v(U32.is_eq(v, 0), U32.is_eq(v, 255), v, b, {==}, {==}, e)
    case Con{v, Con{w, t}}:
      Empty.absurd({B.Octets.of_list(Con{v, Con{w, t}}) == B.Octets.of_list([Bool.pick(U32, b, 255, 0)]) : B.Octets}, sx.fd(Bool, E.Asn1BadValue{}, b, e))

def sx.bool_tag(ok: Bool, +u: T.Asn1Tag, +o: B.Octets, -b: Bool, +hok: {T.Asn1Tag.is_eq(T.Asn1Tag.boolean(), u) == ok : Bool}, +e: {P.a1.bool.from(P.a1.prim_as.pick(ok, o), True{}) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}) -> {P.Asn1.bool(b) == N.Asn1Prim{u, o} : N.Asn1Node}:
  match ok:
    case True{}:
      +et = sx.tag_eq(T.Asn1Tag.boolean(), u, hok)
      +eo = sx.bool_read(B.Octets.to_list(o), b, e)
      %et : {P.Asn1.bool(b) == N.Asn1Prim{_, o} : N.Asn1Node}
      %AL.al.of_to(o) : {P.Asn1.bool(b) == N.Asn1Prim{T.Asn1Tag.boolean(), _} : N.Asn1Node}
      %eo : {N.Asn1Prim{T.Asn1Tag.boolean(), _} == N.Asn1Prim{T.Asn1Tag.boolean(), B.Octets.of_list(B.Octets.to_list(o))} : N.Asn1Node}
      {==}
    case False{}:
      Empty.absurd({P.Asn1.bool(b) == N.Asn1Prim{u, o} : N.Asn1Node}, sx.fd(Bool, E.Asn1Unexpected{}, b, e))

# under DER's value checks, a BOOLEAN read is the element written for it
def sx.bool_c(+r: R.Asn1Rules, +hv: {R.Asn1Rules.values(r) == True{} : Bool}, n: N.Asn1Node, -b: Bool, +e: {P.Asn1.get_bool(r, n) == Done{b} : Result<&2, &2, E.Asn1Error, Bool>}) -> {P.Asn1.bool(b) == n : N.Asn1Node}:
  match n:
    case N.Asn1Prim{+u, +o}:
      +ex = Equal.cong(Bool, Result<&2, &2, E.Asn1Error, Bool>, v => P.a1.bool.from(P.a1.prim_as.pick(T.Asn1Tag.is_eq(T.Asn1Tag.boolean(), u), o), v), True{}, R.Asn1Rules.values(r), Equal.sym(Bool, R.Asn1Rules.values(r), True{}, hv))
      sx.bool_tag(T.Asn1Tag.is_eq(T.Asn1Tag.boolean(), u), u, o, b, {==}, Equal.trans(Result<&2, &2, E.Asn1Error, Bool>, P.a1.bool.from(P.a1.prim_as.pick(T.Asn1Tag.is_eq(T.Asn1Tag.boolean(), u), o), True{}), P.Asn1.get_bool(r, N.Asn1Prim{u, o}), Done{b}, ex, e))
    case N.Asn1Cons{u, xs}:
      Empty.absurd({P.Asn1.bool(b) == N.Asn1Cons{u, xs} : N.Asn1Node}, sx.fd(Bool, E.Asn1Unexpected{}, b, e))

# NULL

def sx.len0(xs: List<&2, U32>, +h: {List.length(&2, U32, xs) == 0n : Nat}) -> {xs == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, U32>}, AN.an.ft(Equal.cong(Nat, Bool, k => Nat.is_eq(k, 0n), 1n+List.length(&2, U32, t), 0n, h)))

def sx.null_need(z: Bool, +o: B.Octets, -u: Unit, +hz: {Nat.is_eq(B.Octets.len(o), 0n) == z : Bool}, +e: {P.a1.need(z, E.Asn1BadValue{}) == Done{u} : Result<&2, &2, E.Asn1Error, Unit>}) -> {B.Octets.empty() == o : B.Octets}:
  match z:
    case True{}:
      +hl = Equal.trans(Nat, List.length(&2, U32, B.Octets.to_list(o)), B.Octets.len(o), 0n, Equal.sym(Nat, B.Octets.len(o), List.length(&2, U32, B.Octets.to_list(o)), AL.al.olen(o)), AN.an.eq_sound(B.Octets.len(o), 0n, hz))
      %AL.al.of_to(o) : {B.Octets.empty() == _ : B.Octets}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(o), Nil{}, sx.len0(B.Octets.to_list(o), hl)) : {B.Octets.empty() == B.Octets.of_list(_) : B.Octets}
      {==}
    case False{}:
      Empty.absurd({B.Octets.empty() == o : B.Octets}, sx.fd(Unit, E.Asn1BadValue{}, u, e))

def sx.null_tag(ok: Bool, +v: T.Asn1Tag, +o: B.Octets, -u: Unit, +hok: {T.Asn1Tag.is_eq(T.Asn1Tag.null(), v) == ok : Bool}, +e: {P.a1.null.from(P.a1.prim_as.pick(ok, o)) == Done{u} : Result<&2, &2, E.Asn1Error, Unit>}) -> {P.Asn1.null() == N.Asn1Prim{v, o} : N.Asn1Node}:
  match ok:
    case True{}:
      +et = sx.tag_eq(T.Asn1Tag.null(), v, hok)
      %et : {P.Asn1.null() == N.Asn1Prim{_, o} : N.Asn1Node}
      %sx.null_need(Nat.is_eq(B.Octets.len(o), 0n), o, u, {==}, e) : {N.Asn1Prim{T.Asn1Tag.null(), B.Octets.empty()} == N.Asn1Prim{T.Asn1Tag.null(), _} : N.Asn1Node}
      {==}
    case False{}:
      Empty.absurd({P.Asn1.null() == N.Asn1Prim{v, o} : N.Asn1Node}, sx.fd(Unit, E.Asn1Unexpected{}, u, e))

# a NULL read is the element written
def sx.null_c(n: N.Asn1Node, -u: Unit, +e: {P.Asn1.get_null(n) == Done{u} : Result<&2, &2, E.Asn1Error, Unit>}) -> {P.Asn1.null() == n : N.Asn1Node}:
  match n:
    case N.Asn1Prim{+v, +o}:
      sx.null_tag(T.Asn1Tag.is_eq(T.Asn1Tag.null(), v), v, o, u, {==}, e)
    case N.Asn1Cons{v, xs}:
      Empty.absurd({P.Asn1.null() == N.Asn1Cons{v, xs} : N.Asn1Node}, sx.fd(Unit, E.Asn1Unexpected{}, u, e))

# Strings: a string-like value read under the primitive-only rule

def sx.sv_prim(ok: Bool, +t: T.Asn1Tag, +v: T.Asn1Tag, +c: B.Octets, -o: B.Octets, +hok: {T.Asn1Tag.is_eq(t, v) == ok : Bool}, +e: {P.a1.prim_as.pick(ok, c) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> {N.Asn1Prim{t, o} == N.Asn1Prim{v, c} : N.Asn1Node}:
  match ok:
    case True{}:
      +et = sx.tag_eq(t, v, hok)
      +eo = sx.dd(B.Octets, c, o, e)
      %et : {N.Asn1Prim{t, o} == N.Asn1Prim{_, c} : N.Asn1Node}
      %eo : {N.Asn1Prim{t, _} == N.Asn1Prim{t, c} : N.Asn1Node}
      {==}
    case False{}:
      Empty.absurd({N.Asn1Prim{t, o} == N.Asn1Prim{v, c} : N.Asn1Node}, sx.fd(B.Octets, E.Asn1Unexpected{}, o, e))

def sx.sv_cons(ok: Bool, +t: T.Asn1Tag, +v: T.Asn1Tag, +u: T.Asn1Tag, xs: List<&2, N.Asn1Node>, -o: B.Octets, +e: {P.a1.str.cons(ok, True{}, xs, u) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> {N.Asn1Prim{t, o} == N.Asn1Cons{v, xs} : N.Asn1Node}:
  match ok:
    case True{}:
      Empty.absurd({N.Asn1Prim{t, o} == N.Asn1Cons{v, xs} : N.Asn1Node}, sx.fd(B.Octets, E.Asn1BadForm{}, o, e))
    case False{}:
      Empty.absurd({N.Asn1Prim{t, o} == N.Asn1Cons{v, xs} : N.Asn1Node}, sx.fd(B.Octets, E.Asn1Unexpected{}, o, e))

# the value of a string-like element of tag t, primitive only: the element
# is the primitive one of tag t with those contents
def sx.sv(+t: T.Asn1Tag, +u: T.Asn1Tag, n: N.Asn1Node, -o: B.Octets, +e: {P.a1.string_value(True{}, t, u, n) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> {N.Asn1Prim{t, o} == n : N.Asn1Node}:
  match n:
    case N.Asn1Prim{+v, +c}:
      sx.sv_prim(T.Asn1Tag.is_eq(t, v), t, v, c, o, {==}, e)
    case N.Asn1Cons{+v, +xs}:
      sx.sv_cons(T.Asn1Tag.is_eq(t, v), t, v, u, xs, o, e)

def sx.prim_rw(+r: R.Asn1Rules, +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}, +t: T.Asn1Tag, +u: T.Asn1Tag, +n: N.Asn1Node) -> {P.a1.string_value(True{}, t, u, n) == P.a1.string_value(R.Asn1Rules.prim_strings(r), t, u, n) : Result<&2, &2, E.Asn1Error, B.Octets>}:
  Equal.cong(Bool, Result<&2, &2, E.Asn1Error, B.Octets>, p => P.a1.string_value(p, t, u, n), True{}, R.Asn1Rules.prim_strings(r), Equal.sym(Bool, R.Asn1Rules.prim_strings(r), True{}, hp))

# under the primitive-only rule, an OCTET STRING read is the element written
def sx.octets_c(+r: R.Asn1Rules, +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}, +t: T.Asn1Tag, +n: N.Asn1Node, -o: B.Octets, +e: {P.Asn1.get_octets_as(r, t, n) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> {P.Asn1.octets_as(t, o) == n : N.Asn1Node}:
  sx.sv(t, T.Asn1Tag.octet_string(), n, o, Equal.trans(Result<&2, &2, E.Asn1Error, B.Octets>, P.a1.string_value(True{}, t, T.Asn1Tag.octet_string(), n), P.a1.string_value(R.Asn1Rules.prim_strings(r), t, T.Asn1Tag.octet_string(), n), Done{o}, sx.prim_rw(r, hp, t, T.Asn1Tag.octet_string(), n), e))

# Character strings

def sx.str_check(ok: Bool, +k: S.Asn1StrKind, +o: B.Octets, -s: S.Asn1Str, +hok: {S.Asn1Str.valid(S.Asn1Str{k, o}) == ok : Bool}, +e: {S.a1.str.check.pick(ok, S.Asn1Str{k, o}) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {S.Asn1Str{k, o} == s : S.Asn1Str}:
  match ok:
    case True{}:
      sx.dd(S.Asn1Str, S.Asn1Str{k, o}, s, e)
    case False{}:
      Empty.absurd({S.Asn1Str{k, o} == s : S.Asn1Str}, sx.fd(S.Asn1Str, E.Asn1BadString{}, s, e))

def sx.str_check_v(ok: Bool, +k: S.Asn1StrKind, +o: B.Octets, -s: S.Asn1Str, +hok: {S.Asn1Str.valid(S.Asn1Str{k, o}) == ok : Bool}, +e: {S.a1.str.check.pick(ok, S.Asn1Str{k, o}) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {S.Asn1Str.valid(s) == True{} : Bool}:
  match ok:
    case True{}:
      %sx.dd(S.Asn1Str, S.Asn1Str{k, o}, s, e) : {S.Asn1Str.valid(_) == True{} : Bool}
      hok
    case False{}:
      Empty.absurd({S.Asn1Str.valid(s) == True{} : Bool}, sx.fd(S.Asn1Str, E.Asn1BadString{}, s, e))

def sx.str_got_v(+k: S.Asn1StrKind, res: Result<&2, &2, E.Asn1Error, B.Octets>, -s: S.Asn1Str, +e: {S.a1.str.got(k, res) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {S.Asn1Str.valid(s) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({S.Asn1Str.valid(s) == True{} : Bool}, sx.fd(S.Asn1Str, x, s, e))
    case Done{+o}:
      sx.str_check_v(S.Asn1Str.valid(S.Asn1Str{k, o}), k, o, s, {==}, e)

def sx.str_read_v(m: Maybe<&2, S.Asn1StrKind>, +r: R.Asn1Rules, +n: N.Asn1Node, -s: S.Asn1Str, +e: {S.a1.str.read(m, r, n) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {S.Asn1Str.valid(s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({S.Asn1Str.valid(s) == True{} : Bool}, sx.fd(S.Asn1Str, E.Asn1Unexpected{}, s, e))
    case Some{+k}:
      sx.str_got_v(k, P.a1.string_value(R.Asn1Rules.prim_strings(r), S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n), s, e)

def sx.str_got_c(+r: R.Asn1Rules, +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}, +t: T.Asn1Tag, +k: S.Asn1StrKind, +n: N.Asn1Node, res: Result<&2, &2, E.Asn1Error, B.Octets>, +hres: {P.a1.string_value(R.Asn1Rules.prim_strings(r), t, S.Asn1StrKind.tag(k), n) == res : Result<&2, &2, E.Asn1Error, B.Octets>}, -s: S.Asn1Str, +e: {S.a1.str.got(k, res) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {Bu.Asn1.implicit(t, S.Asn1.string(s)) == n : N.Asn1Node}:
  match res:
    case Fail{x}:
      Empty.absurd({Bu.Asn1.implicit(t, S.Asn1.string(s)) == n : N.Asn1Node}, sx.fd(S.Asn1Str, x, s, e))
    case Done{+o}:
      +hs = sx.str_check(S.Asn1Str.valid(S.Asn1Str{k, o}), k, o, s, {==}, e)
      +hn = sx.sv(t, S.Asn1StrKind.tag(k), n, o, Equal.trans(Result<&2, &2, E.Asn1Error, B.Octets>, P.a1.string_value(True{}, t, S.Asn1StrKind.tag(k), n), P.a1.string_value(R.Asn1Rules.prim_strings(r), t, S.Asn1StrKind.tag(k), n), Done{o}, sx.prim_rw(r, hp, t, S.Asn1StrKind.tag(k), n), hres))
      %hs : {Bu.Asn1.implicit(t, S.Asn1.string(_)) == n : N.Asn1Node}
      hn

def sx.str_got_c0(+r: R.Asn1Rules, +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}, +k: S.Asn1StrKind, +n: N.Asn1Node, res: Result<&2, &2, E.Asn1Error, B.Octets>, +hres: {P.a1.string_value(R.Asn1Rules.prim_strings(r), S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n) == res : Result<&2, &2, E.Asn1Error, B.Octets>}, -s: S.Asn1Str, +e: {S.a1.str.got(k, res) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {S.Asn1.string(s) == n : N.Asn1Node}:
  match res:
    case Fail{x}:
      Empty.absurd({S.Asn1.string(s) == n : N.Asn1Node}, sx.fd(S.Asn1Str, x, s, e))
    case Done{+o}:
      +hs = sx.str_check(S.Asn1Str.valid(S.Asn1Str{k, o}), k, o, s, {==}, e)
      +hn = sx.sv(S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n, o, Equal.trans(Result<&2, &2, E.Asn1Error, B.Octets>, P.a1.string_value(True{}, S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n), P.a1.string_value(R.Asn1Rules.prim_strings(r), S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n), Done{o}, sx.prim_rw(r, hp, S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n), hres))
      %hs : {S.Asn1.string(_) == n : N.Asn1Node}
      hn

def sx.str_read_c(m: Maybe<&2, S.Asn1StrKind>, +r: R.Asn1Rules, +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}, +n: N.Asn1Node, -s: S.Asn1Str, +e: {S.a1.str.read(m, r, n) == Done{s} : Result<&2, &2, E.Asn1Error, S.Asn1Str>}) -> {S.Asn1.string(s) == n : N.Asn1Node}:
  match m:
    case None{}:
      Empty.absurd({S.Asn1.string(s) == n : N.Asn1Node}, sx.fd(S.Asn1Str, E.Asn1Unexpected{}, s, e))
    case Some{+k}:
      sx.str_got_c0(r, hp, k, n, P.a1.string_value(R.Asn1Rules.prim_strings(r), S.Asn1StrKind.tag(k), S.Asn1StrKind.tag(k), n), {==}, s, e)

# BIT STRING

def sx.small(v: Nat, +h: {Nat.is_le(v, 7n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(v)) == v : Nat}:
  match v:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n+k:
      Empty.absurd({U32.to_nat(U32.from_nat(8n+k)) == 8n+k : Nat}, AN.an.ft(h))

def sx.bits_ok(okb: Bool, +der: Bool, +x: U32, +tl: List<&2, U32>, +t: T.Asn1Tag, -b: Bi.Asn1Bits, +hok: {Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{U32.to_nat(x), B.Octets.of_list(tl)}), R.a1.when(der, Bi.a1.bits.clear(U32.to_nat(x), B.Octets.of_list(tl)))) == okb : Bool}, +e: {Bi.a1.bits.check(okb, Bi.Asn1Bits{U32.to_nat(x), B.Octets.of_list(tl)}) == Done{b} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}) -> {Bi.Asn1.bits_as(t, b) == N.Asn1Prim{t, B.Octets.of_list(Con{x, tl})} : N.Asn1Node}:
  match okb:
    case True{}:
      +u = U32.to_nat(x)
      +o = B.Octets.of_list(tl)
      +eb = sx.dd(Bi.Asn1Bits, Bi.Asn1Bits{u, o}, b, e)
      +hb = AN.an.and_l(Bi.Asn1Bits.ok(Bi.Asn1Bits{u, o}), R.a1.when(der, Bi.a1.bits.clear(u, o)), hok)
      +h7 = AN.an.and_l(Nat.is_le(u, 7n), Bool.or(Nat.is_lt(0n, B.Octets.len(o)), Nat.is_eq(u, 0n)), hb)
      +ex = UL.u32_value_eq(U32.from_nat(u), x, sx.small(u, h7))
      +hl = Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.cons(x, o)), Con{B.byte(x), B.Octets.to_list(o)}, B.Octets.to_list(B.Octets.of_list(Con{x, tl})), BL.octets_cons_list(x, o), Equal.trans(List<&2, U32>, Con{B.byte(x), B.Octets.to_list(o)}, Con{B.byte(x), B.mask(tl)}, B.Octets.to_list(B.Octets.of_list(Con{x, tl})), Equal.cong(List<&2, U32>, List<&2, U32>, l => Con{B.byte(x), l}, B.Octets.to_list(o), B.mask(tl), AL.al.to_of(tl)), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{x, tl})), B.mask(Con{x, tl}), AL.al.to_of(Con{x, tl}))))
      +eo = OA.oa.ext(B.Octets.cons(x, o), B.Octets.of_list(Con{x, tl}), hl)
      %eb : {Bi.Asn1.bits_as(t, _) == N.Asn1Prim{t, B.Octets.of_list(Con{x, tl})} : N.Asn1Node}
      %Equal.sym(U32, U32.from_nat(u), x, ex) : {N.Asn1Prim{t, B.Octets.cons(_, o)} == N.Asn1Prim{t, B.Octets.of_list(Con{x, tl})} : N.Asn1Node}
      %eo : {N.Asn1Prim{t, B.Octets.cons(x, o)} == N.Asn1Prim{t, _} : N.Asn1Node}
      {==}
    case False{}:
      Empty.absurd({Bi.Asn1.bits_as(t, b) == N.Asn1Prim{t, B.Octets.of_list(Con{x, tl})} : N.Asn1Node}, sx.fd(Bi.Asn1Bits, E.Asn1BadBits{}, b, e))

def sx.bits_of(+der: Bool, xs: List<&2, U32>, +t: T.Asn1Tag, -b: Bi.Asn1Bits, +e: {Bi.a1.bits.of_prim(der, xs) == Done{b} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}) -> {Bi.Asn1.bits_as(t, b) == N.Asn1Prim{t, B.Octets.of_list(xs)} : N.Asn1Node}:
  match xs:
    case Nil{}:
      Empty.absurd({Bi.Asn1.bits_as(t, b) == N.Asn1Prim{t, B.Octets.of_list(Nil{})} : N.Asn1Node}, sx.fd(Bi.Asn1Bits, E.Asn1BadBits{}, b, e))
    case Con{+x, +tl}:
      sx.bits_ok(Bool.and(Bi.Asn1Bits.ok(Bi.Asn1Bits{U32.to_nat(x), B.Octets.of_list(tl)}), R.a1.when(der, Bi.a1.bits.clear(U32.to_nat(x), B.Octets.of_list(tl)))), der, x, tl, t, b, {==}, e)

def sx.bits_prim_c(ok: Bool, +der: Bool, +t: T.Asn1Tag, +v: T.Asn1Tag, +c: B.Octets, -b: Bi.Asn1Bits, +hok: {T.Asn1Tag.is_eq(t, v) == ok : Bool}, +e: {Bi.a1.bits.prim(ok, der, c) == Done{b} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}) -> {Bi.Asn1.bits_as(t, b) == N.Asn1Prim{v, c} : N.Asn1Node}:
  match ok:
    case True{}:
      +et = sx.tag_eq(t, v, hok)
      %et : {Bi.Asn1.bits_as(t, b) == N.Asn1Prim{_, c} : N.Asn1Node}
      %AL.al.of_to(c) : {Bi.Asn1.bits_as(t, b) == N.Asn1Prim{t, _} : N.Asn1Node}
      sx.bits_of(der, B.Octets.to_list(c), t, b, e)
    case False{}:
      Empty.absurd({Bi.Asn1.bits_as(t, b) == N.Asn1Prim{v, c} : N.Asn1Node}, sx.fd(Bi.Asn1Bits, E.Asn1Unexpected{}, b, e))

def sx.bits_cons_c(ok: Bool, +der: Bool, +t: T.Asn1Tag, +v: T.Asn1Tag, xs: List<&2, N.Asn1Node>, -b: Bi.Asn1Bits, +e: {Bi.a1.bits.cons(ok, True{}, xs, der) == Done{b} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}) -> {Bi.Asn1.bits_as(t, b) == N.Asn1Cons{v, xs} : N.Asn1Node}:
  match ok:
    case True{}:
      Empty.absurd({Bi.Asn1.bits_as(t, b) == N.Asn1Cons{v, xs} : N.Asn1Node}, sx.fd(Bi.Asn1Bits, E.Asn1BadForm{}, b, e))
    case False{}:
      Empty.absurd({Bi.Asn1.bits_as(t, b) == N.Asn1Cons{v, xs} : N.Asn1Node}, sx.fd(Bi.Asn1Bits, E.Asn1Unexpected{}, b, e))

# under the primitive-only rule, a BIT STRING read is the element written
def sx.bits_c(+r: R.Asn1Rules, +hp: {R.Asn1Rules.prim_strings(r) == True{} : Bool}, +t: T.Asn1Tag, n: N.Asn1Node, -b: Bi.Asn1Bits, +e: {Bi.Asn1.get_bits_as(r, t, n) == Done{b} : Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>}) -> {Bi.Asn1.bits_as(t, b) == n : N.Asn1Node}:
  match n:
    case N.Asn1Prim{+v, +c}:
      sx.bits_prim_c(T.Asn1Tag.is_eq(t, v), R.Asn1Rules.values(r), t, v, c, b, {==}, e)
    case N.Asn1Cons{+v, +xs}:
      +ex = Equal.cong(Bool, Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>, p => Bi.a1.bits.cons(T.Asn1Tag.is_eq(t, v), p, xs, R.Asn1Rules.values(r)), True{}, R.Asn1Rules.prim_strings(r), Equal.sym(Bool, R.Asn1Rules.prim_strings(r), True{}, hp))
      sx.bits_cons_c(T.Asn1Tag.is_eq(t, v), R.Asn1Rules.values(r), t, v, xs, b, Equal.trans(Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>, Bi.a1.bits.cons(T.Asn1Tag.is_eq(t, v), True{}, xs, R.Asn1Rules.values(r)), Bi.Asn1.get_bits_as(r, t, N.Asn1Cons{v, xs}), Done{b}, ex, e))

# Constructed values

def sx.cons_pick(ok: Bool, +t: T.Asn1Tag, +u: T.Asn1Tag, +ys: List<&2, N.Asn1Node>, -xs: List<&2, N.Asn1Node>, +hok: {T.Asn1Tag.is_eq(t, u) == ok : Bool}, +e: {Bu.a1.cons_as.pick(ok, ys) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}) -> {N.Asn1Cons{t, xs} == N.Asn1Cons{u, ys} : N.Asn1Node}:
  match ok:
    case True{}:
      +et = sx.tag_eq(t, u, hok)
      +ex = sx.dd(List<&2, N.Asn1Node>, ys, xs, e)
      %et : {N.Asn1Cons{t, xs} == N.Asn1Cons{_, ys} : N.Asn1Node}
      %ex : {N.Asn1Cons{t, _} == N.Asn1Cons{t, ys} : N.Asn1Node}
      {==}
    case False{}:
      Empty.absurd({N.Asn1Cons{t, xs} == N.Asn1Cons{u, ys} : N.Asn1Node}, sx.fd(List<&2, N.Asn1Node>, E.Asn1Unexpected{}, xs, e))

# a constructed element read with tag t is the constructed element of tag t
# of the elements read
def sx.cons_c(+t: T.Asn1Tag, n: N.Asn1Node, -xs: List<&2, N.Asn1Node>, +e: {Bu.Asn1.cons_as(t, n) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}) -> {N.Asn1Cons{t, xs} == n : N.Asn1Node}:
  match n:
    case N.Asn1Cons{+u, +ys}:
      sx.cons_pick(T.Asn1Tag.is_eq(t, u), t, u, ys, xs, {==}, e)
    case N.Asn1Prim{u, o}:
      Empty.absurd({N.Asn1Cons{t, xs} == N.Asn1Prim{u, o} : N.Asn1Node}, sx.fd(List<&2, N.Asn1Node>, E.Asn1Unexpected{}, xs, e))

def sx.one_c(res: Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>, -x: N.Asn1Node, +e: {Bu.a1.one_of(res) == Done{x} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> {res == Done{[x]} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}:
  match res:
    case Fail{y}:
      Empty.absurd({Fail{y} == Done{[x]} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}, sx.fd(N.Asn1Node, y, x, e))
    case Done{ys}:
      match ys:
        case Nil{}:
          Empty.absurd({Done{Nil{}} == Done{[x]} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}, sx.fd(N.Asn1Node, E.Asn1Unexpected{}, x, e))
        case Con{+y, Nil{}}:
          Equal.cong(N.Asn1Node, Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>, z => Done{[z]}, y, x, sx.dd(N.Asn1Node, y, x, e))
        case Con{y, Con{w, t}}:
          Empty.absurd({Done{Con{y, Con{w, t}}} == Done{[x]} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}, sx.fd(N.Asn1Node, E.Asn1Unexpected{}, x, e))

# the element inside [k] EXPLICIT, read: the element is [k] EXPLICIT of it
def sx.explicit_c(+k: Nat, +n: N.Asn1Node, -x: N.Asn1Node, +e: {Bu.Asn1.get_explicit(k, n) == Done{x} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> {Bu.Asn1.explicit(k, x) == n : N.Asn1Node}:
  sx.cons_c(T.Asn1Tag.context(k), n, [x], sx.one_c(Bu.Asn1.cons_as(T.Asn1Tag.context(k), n), x, e))

# Times: what the checks let through

def sx.zulu(z: Ti.Asn1Zone, +h: {Ti.a1.t.zulu(z) == True{} : Bool}) -> {z == Ti.Asn1Zulu{} : Ti.Asn1Zone}:
  match z:
    case Ti.Asn1Zulu{}:
      {==}
    case Ti.Asn1LocalTime{}:
      Empty.absurd({Ti.Asn1LocalTime{} == Ti.Asn1Zulu{} : Ti.Asn1Zone}, AN.an.ft(h))
    case Ti.Asn1Offset{a, b, c}:
      Empty.absurd({Ti.Asn1Offset{a, b, c} == Ti.Asn1Zulu{} : Ti.Asn1Zone}, AN.an.ft(h))

# what a time the checks let through is: valid, and (under the values rule)
# in Zulu time
type SxT is Data:
  SxT{valid: Bool, zulu: Bool}

def sx.tfacts(+der: Bool, +t: Ti.Asn1Time) -> SxT:
  SxT{Ti.Asn1Time.valid(t), R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t)))}

def sx.check2(ok: Bool, +der: Bool, +t0: Ti.Asn1Time, -t: Ti.Asn1Time, +hok: {Bool.and(Ti.Asn1Time.valid(t0), R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t0)))) == ok : Bool}, +e: {Ti.a1.t.check2(ok, t0) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}) -> {sx.tfacts(der, t) == SxT{True{}, True{}} : SxT}:
  match ok:
    case True{}:
      +et = sx.dd(Ti.Asn1Time, t0, t, e)
      +hv = AN.an.and_l(Ti.Asn1Time.valid(t0), R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t0))), hok)
      +hz = AN.an.and_r(Ti.Asn1Time.valid(t0), R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t0))), hok)
      %et : {sx.tfacts(der, _) == SxT{True{}, True{}} : SxT}
      %Equal.sym(Bool, Ti.Asn1Time.valid(t0), True{}, hv) : {SxT{_, R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t0)))} == SxT{True{}, True{}} : SxT}
      %Equal.sym(Bool, R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t0))), True{}, hz) : {SxT{True{}, _} == SxT{True{}, True{}} : SxT}
      {==}
    case False{}:
      Empty.absurd({sx.tfacts(der, t) == SxT{True{}, True{}} : SxT}, sx.fd(Ti.Asn1Time, E.Asn1BadTime{}, t, e))

def sx.check(+der: Bool, mt: Maybe<&2, Ti.Asn1Time>, -t: Ti.Asn1Time, +e: {Ti.a1.t.check(der, mt) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}) -> {sx.tfacts(der, t) == SxT{True{}, True{}} : SxT}:
  match mt:
    case None{}:
      Empty.absurd({sx.tfacts(der, t) == SxT{True{}, True{}} : SxT}, sx.fd(Ti.Asn1Time, E.Asn1BadTime{}, t, e))
    case Some{+t0}:
      sx.check2(Bool.and(Ti.Asn1Time.valid(t0), R.a1.when(der, Ti.a1.t.zulu(Ti.Asn1Time.zone(t0)))), der, t0, t, {==}, e)

def sx.from(res: Result<&2, &2, E.Asn1Error, B.Octets>, +rr: R.Asn1Rules, +pivot: Nat, utc: Bool, -t: Ti.Asn1Time, +e: {Ti.a1.t.from(res, rr, pivot, utc) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}) -> {sx.tfacts(R.Asn1Rules.values(rr), t) == SxT{True{}, True{}} : SxT}:
  match res utc:
    case Fail{x} _:
      Empty.absurd({sx.tfacts(R.Asn1Rules.values(rr), t) == SxT{True{}, True{}} : SxT}, sx.fd(Ti.Asn1Time, x, t, e))
    case Done{o} True{}:
      sx.check(R.Asn1Rules.values(rr), Ti.a1.utc.parse(Ti.a1.t.nums(5n, B.Octets.to_list(o), True{}, Nil{}), R.Asn1Rules.values(rr), pivot), t, e)
    case Done{o} False{}:
      sx.check(R.Asn1Rules.values(rr), Ti.a1.gen.finish(R.Asn1Rules.values(rr), Ti.a1.gen.frac(R.Asn1Rules.values(rr), Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(Ti.a1.t.nums(5n, B.Octets.to_list(o), True{}, Nil{})))))), t, e)

def sx.either(utc: Bool, +r: R.Asn1Rules, +pivot: Nat, +n: N.Asn1Node, -t: Ti.Asn1Time, +e: {Ti.a1.t.either(utc, r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}) -> {sx.tfacts(R.Asn1Rules.values(r), t) == SxT{True{}, True{}} : SxT}:
  match utc:
    case True{}:
      sx.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.utc_time(), T.Asn1Tag.utc_time(), n), r, pivot, True{}, t, e)
    case False{}:
      sx.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.generalized_time(), T.Asn1Tag.generalized_time(), n), r, 50n, False{}, t, e)

# a time read (either type) passes both checks
def sx.time(+r: R.Asn1Rules, +pivot: Nat, +n: N.Asn1Node, -t: Ti.Asn1Time, +e: {Ti.Asn1.get_time(r, pivot, n) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}) -> {sx.tfacts(R.Asn1Rules.values(r), t) == SxT{True{}, True{}} : SxT}:
  sx.either(T.Asn1Tag.is_eq(N.Asn1Node.tag(n), T.Asn1Tag.utc_time()), r, pivot, n, t, e)

def sx.tv(p: SxT) -> Bool:
  match p:
    case SxT{a, b}:
      a

def sx.tz(p: SxT) -> Bool:
  match p:
    case SxT{a, b}:
      b

def sx.valid_of(+der: Bool, +t: Ti.Asn1Time, +h: {sx.tfacts(der, t) == SxT{True{}, True{}} : SxT}) -> {Ti.Asn1Time.valid(t) == True{} : Bool}:
  Equal.cong(SxT, Bool, p => sx.tv(p), sx.tfacts(der, t), SxT{True{}, True{}}, h)

def sx.zulu_of(+t: Ti.Asn1Time, +h: {sx.tfacts(True{}, t) == SxT{True{}, True{}} : SxT}) -> {Ti.Asn1Time.zone(t) == Ti.Asn1Zulu{} : Ti.Asn1Zone}:
  sx.zulu(Ti.Asn1Time.zone(t), Equal.cong(SxT, Bool, p => sx.tz(p), sx.tfacts(True{}, t), SxT{True{}, True{}}, h))

def sx.der_facts(+r: R.Asn1Rules, +hv: {R.Asn1Rules.values(r) == True{} : Bool}, +t: Ti.Asn1Time, +h: {sx.tfacts(R.Asn1Rules.values(r), t) == SxT{True{}, True{}} : SxT}) -> {sx.tfacts(True{}, t) == SxT{True{}, True{}} : SxT}:
  Equal.trans(SxT, sx.tfacts(True{}, t), sx.tfacts(R.Asn1Rules.values(r), t), SxT{True{}, True{}}, Equal.cong(Bool, SxT, v => sx.tfacts(v, t), True{}, R.Asn1Rules.values(r), Equal.sym(Bool, R.Asn1Rules.values(r), True{}, hv)), h)
