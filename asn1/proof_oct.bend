# Proof helpers for bend-osdev-asn1: Octets joined and cut, through bytes'
# interface laws only (octets_of_to, octets_to_of, octets_append_list):
# two Octets with the same bytes are equal, appending is associative with
# the empty string on either side, and a list's Octets split where the list
# does. oa.sl says o is a slice of c (some octets before it, some after);
# a slice of a slice is a slice. bytes states none of this as laws yet
# (another batch's work, as bytes has many dependents), so it is proved
# here, privately.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./proof_list.bend as AL

# Octets with the same bytes are the same
def oa.ext(+a: B.Octets, +b: B.Octets, +h: {B.Octets.to_list(a) == B.Octets.to_list(b) : List<&2, U32>}) -> {a == b : B.Octets}:
  %BL.octets_of_to(a) : {_ == b : B.Octets}
  %BL.octets_of_to(b) : {B.Octets.of_list(B.Octets.to_list(a)) == _ : B.Octets}
  Equal.cong(List<&2, U32>, B.Octets, z => B.Octets.of_list(z), B.Octets.to_list(a), B.Octets.to_list(b), h)

def oa.empty_list() -> {B.Octets.to_list(B.Octets.empty()) == Nil{} : List<&2, U32>}:
  {==}

def oa.app_empty_l.l(+a: B.Octets) -> {B.Octets.to_list(B.Octets.append(B.Octets.empty(), a)) == B.Octets.to_list(a) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.empty(), a)), B.append(B.Octets.to_list(B.Octets.empty()), B.Octets.to_list(a)), BL.octets_append_list(B.Octets.empty(), a)) : {_ == B.Octets.to_list(a) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.empty()), Nil{}, oa.empty_list()) : {B.append(_, B.Octets.to_list(a)) == B.Octets.to_list(a) : List<&2, U32>}
  {==}

def oa.app_empty_l(+a: B.Octets) -> {B.Octets.append(B.Octets.empty(), a) == a : B.Octets}:
  oa.ext(B.Octets.append(B.Octets.empty(), a), a, oa.app_empty_l.l(a))

def oa.app_empty_r.l(+a: B.Octets) -> {B.Octets.to_list(B.Octets.append(a, B.Octets.empty())) == B.Octets.to_list(a) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, B.Octets.empty())), B.append(B.Octets.to_list(a), B.Octets.to_list(B.Octets.empty())), BL.octets_append_list(a, B.Octets.empty())) : {_ == B.Octets.to_list(a) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.empty()), Nil{}, oa.empty_list()) : {B.append(B.Octets.to_list(a), _) == B.Octets.to_list(a) : List<&2, U32>}
  AL.al.app_nil(B.Octets.to_list(a))

def oa.app_empty_r(+a: B.Octets) -> {B.Octets.append(a, B.Octets.empty()) == a : B.Octets}:
  oa.ext(B.Octets.append(a, B.Octets.empty()), a, oa.app_empty_r.l(a))

def oa.app_assoc.l(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.to_list(B.Octets.append(B.Octets.append(a, b), c)) == B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c))) : List<&2, U32>}:
  +la = B.Octets.to_list(a)
  +lb = B.Octets.to_list(b)
  +lc = B.Octets.to_list(c)
  +rhs = B.Octets.to_list(B.Octets.append(a, B.Octets.append(b, c)))
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.append(a, b), c)), B.append(B.Octets.to_list(B.Octets.append(a, b)), lc), BL.octets_append_list(B.Octets.append(a, b), c)) : {_ == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(la, lb), BL.octets_append_list(a, b)) : {B.append(_, lc) == rhs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, rhs, B.append(la, B.Octets.to_list(B.Octets.append(b, c))), BL.octets_append_list(a, B.Octets.append(b, c))) : {B.append(B.append(la, lb), lc) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(b, c)), B.append(lb, lc), BL.octets_append_list(b, c)) : {B.append(B.append(la, lb), lc) == B.append(la, _) : List<&2, U32>}
  AL.al.app_assoc(la, lb, lc)

def oa.app_assoc(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.append(B.Octets.append(a, b), c) == B.Octets.append(a, B.Octets.append(b, c)) : B.Octets}:
  oa.ext(B.Octets.append(B.Octets.append(a, b), c), B.Octets.append(a, B.Octets.append(b, c)), oa.app_assoc.l(a, b, c))

def oa.of_app.l(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.Octets.to_list(B.Octets.of_list(List.append(&2, U32, xs, ys))) == B.Octets.to_list(B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys))) : List<&2, U32>}:
  +m = B.mask(List.append(&2, U32, xs, ys))
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(List.append(&2, U32, xs, ys))), m, BL.octets_to_of(List.append(&2, U32, xs, ys))) : {_ == B.Octets.to_list(B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys))), B.append(B.Octets.to_list(B.Octets.of_list(xs)), B.Octets.to_list(B.Octets.of_list(ys))), BL.octets_append_list(B.Octets.of_list(xs), B.Octets.of_list(ys))) : {m == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {m == B.append(_, B.Octets.to_list(B.Octets.of_list(ys))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(ys)), B.mask(ys), BL.octets_to_of(ys)) : {m == B.append(B.mask(xs), _) : List<&2, U32>}
  AL.al.mask_app(xs, ys)

# a list's Octets split where the list does
def oa.of_app(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.Octets.of_list(List.append(&2, U32, xs, ys)) == B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys)) : B.Octets}:
  oa.ext(B.Octets.of_list(List.append(&2, U32, xs, ys)), B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys)), oa.of_app.l(xs, ys))

# Slices: o is c's octets from some offset on, with some after it

def oa.sl(o: B.Octets, c: B.Octets) -> Type:
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {c == B.Octets.append(u, B.Octets.append(o, v)) : B.Octets}>>

def oa.sl_refl.e(+c: B.Octets) -> {c == B.Octets.append(B.Octets.empty(), B.Octets.append(c, B.Octets.empty())) : B.Octets}:
  +x = B.Octets.append(c, B.Octets.empty())
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), x), x, oa.app_empty_l(x)) : {c == _ : B.Octets}
  Equal.sym(B.Octets, x, c, oa.app_empty_r(c))

def oa.sl_refl(+c: B.Octets) -> oa.sl(c, c):
  (B.Octets.empty(), (B.Octets.empty(), oa.sl_refl.e(c)))

def oa.sl_empty.e(+c: B.Octets) -> {c == B.Octets.append(B.Octets.empty(), B.Octets.append(B.Octets.empty(), c)) : B.Octets}:
  +x = B.Octets.append(B.Octets.empty(), c)
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), x), x, oa.app_empty_l(x)) : {c == _ : B.Octets}
  Equal.sym(B.Octets, x, c, oa.app_empty_l(c))

def oa.sl_empty(+c: B.Octets) -> oa.sl(B.Octets.empty(), c):
  (B.Octets.empty(), (c, oa.sl_empty.e(c)))

# a piece in front, a piece behind, a piece between
def oa.sl_front(+o: B.Octets, +v: B.Octets) -> oa.sl(o, B.Octets.append(o, v)):
  (B.Octets.empty(), (v, Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), B.Octets.append(o, v)), B.Octets.append(o, v), oa.app_empty_l(B.Octets.append(o, v)))))

def oa.sl_back.e(+u: B.Octets, +o: B.Octets) -> {B.Octets.append(u, o) == B.Octets.append(u, B.Octets.append(o, B.Octets.empty())) : B.Octets}:
  %Equal.sym(B.Octets, B.Octets.append(o, B.Octets.empty()), o, oa.app_empty_r(o)) : {B.Octets.append(u, o) == B.Octets.append(u, _) : B.Octets}
  {==}

def oa.sl_back(+u: B.Octets, +o: B.Octets) -> oa.sl(o, B.Octets.append(u, o)):
  (u, (B.Octets.empty(), oa.sl_back.e(u, o)))

def oa.sl_mid(+u: B.Octets, +o: B.Octets, +v: B.Octets) -> oa.sl(o, B.Octets.append(u, B.Octets.append(o, v))):
  (u, (v, {==}))

# equal octets are slices of the same
def oa.sl_eq(+o: B.Octets, +p: B.Octets, +c: B.Octets, +e: {o == p : B.Octets}, h: oa.sl(o, c)) -> oa.sl(p, c):
  %e : oa.sl(_, c)
  h

def oa.sl_trans.e(+o: B.Octets, +m: B.Octets, +c: B.Octets, +u1: B.Octets, +v1: B.Octets, +u2: B.Octets, +v2: B.Octets, +e1: {m == B.Octets.append(u1, B.Octets.append(o, v1)) : B.Octets}, +e2: {c == B.Octets.append(u2, B.Octets.append(m, v2)) : B.Octets}) -> {c == B.Octets.append(B.Octets.append(u2, u1), B.Octets.append(o, B.Octets.append(v1, v2))) : B.Octets}:
  +y = B.Octets.append(o, v1)
  +x = B.Octets.append(o, B.Octets.append(v1, v2))
  +rhs = B.Octets.append(B.Octets.append(u2, u1), x)
  %Equal.sym(B.Octets, c, B.Octets.append(u2, B.Octets.append(m, v2)), e2) : {_ == rhs : B.Octets}
  %Equal.sym(B.Octets, m, B.Octets.append(u1, y), e1) : {B.Octets.append(u2, B.Octets.append(_, v2)) == rhs : B.Octets}
  %Equal.sym(B.Octets, rhs, B.Octets.append(u2, B.Octets.append(u1, x)), oa.app_assoc(u2, u1, x)) : {B.Octets.append(u2, B.Octets.append(B.Octets.append(u1, y), v2)) == _ : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(u1, y), v2), B.Octets.append(u1, B.Octets.append(y, v2)), oa.app_assoc(u1, y, v2)) : {B.Octets.append(u2, _) == B.Octets.append(u2, B.Octets.append(u1, x)) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.append(y, v2), x, oa.app_assoc(o, v1, v2)) : {B.Octets.append(u2, B.Octets.append(u1, _)) == B.Octets.append(u2, B.Octets.append(u1, x)) : B.Octets}
  {==}

# a slice of a slice is a slice
def oa.sl_trans(+o: B.Octets, +m: B.Octets, +c: B.Octets, h1: oa.sl(o, m), h2: oa.sl(m, c)) -> oa.sl(o, c):
  (+u1, (+v1, +e1)) = h1
  (+u2, (+v2, +e2)) = h2
  (B.Octets.append(u2, u1), (B.Octets.append(v1, v2), oa.sl_trans.e(o, m, c, u1, v1, u2, v2, e1, e2)))
