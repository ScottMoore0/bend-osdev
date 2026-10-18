import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./options.bend as O
import ./profile.bend as PR
import ./eval.bend as V
import ./transitions.bend as TR
import ./rule_file.bend as F
import ./rule_capability.bend as RC
import ./rule_network.bend as RN
import ./rule_signal.bend as RS
import ./rule_ptrace.bend as RP
import ./rule_mount.bend as RM
import ./rule_dbus.bend as RD
import ./rule_change_profile.bend as RX
import ./LAWS.bend as Laws

# Bool algebra

def b.or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def b.or_false_r(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def b.and_false_r(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def b.and_true_r(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# (p and n and f) or (p and q) is p and ((n and f) or q)
def b.factor(+p: Bool, +n: Bool, +f: Bool, +q: Bool) -> {Bool.or(Bool.and(Bool.and(p, n), f), Bool.and(p, q)) == Bool.and(p, Bool.or(Bool.and(n, f), q)) : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# Globs: the matcher and the list model

def b.disc(+b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def b.ft(+e: {False{} == True{} : Bool}) -> b.disc(True{}):
  %e : b.disc(_)
  Unit{}

def b.absurd(-T: Type, -x: T, -y: T, +e: {False{} == True{} : Bool}) -> {x == y : T}:
  Empty.absurd({x == y : T}, b.ft(e))

def b.absurd_tf(-T: Type, -x: T, -y: T, +e: {True{} == False{} : Bool}) -> {x == y : T}:
  Empty.absurd({x == y : T}, b.ft(Equal.sym(Bool, True{}, False{}, e)))

# the pieces d fit the tokens r after an empty first piece
def fe(+r: List<&2, G.AaGTok>, d: List<&2, List<&2, U32>>) -> Bool:
  match d:
    case Nil{}:
      False{}
    case Con{p, ps}:
      Bool.and(X.AaText.is_nil(p), G.AaGSeq.fits(r, ps))

def fe_any(+r: List<&2, G.AaGTok>, ds: List<&2, List<&2, List<&2, U32>>>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      Bool.or(fe(r, d), fe_any(r, t))

def fa_app(+seq: List<&2, G.AaGTok>, +xs: List<&2, List<&2, List<&2, U32>>>, +ys: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(seq, G.AaGCuts.append(xs, ys)) == Bool.or(G.AaGSeq.fits_any(seq, xs), G.AaGSeq.fits_any(seq, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{d, t}:
      %Equal.sym(Bool, G.AaGSeq.fits_any(seq, G.AaGCuts.append(t, ys)), Bool.or(G.AaGSeq.fits_any(seq, t), G.AaGSeq.fits_any(seq, ys)), fa_app(seq, t, ys)) : {Bool.or(G.AaGSeq.fits(seq, d), _) == Bool.or(Bool.or(G.AaGSeq.fits(seq, d), G.AaGSeq.fits_any(seq, t)), G.AaGSeq.fits_any(seq, ys)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(G.AaGSeq.fits(seq, d), G.AaGSeq.fits_any(seq, t)), G.AaGSeq.fits_any(seq, ys)), Bool.or(G.AaGSeq.fits(seq, d), Bool.or(G.AaGSeq.fits_any(seq, t), G.AaGSeq.fits_any(seq, ys))), b.or_assoc(G.AaGSeq.fits(seq, d), G.AaGSeq.fits_any(seq, t), G.AaGSeq.fits_any(seq, ys)))

def fe_app(+r: List<&2, G.AaGTok>, +xs: List<&2, List<&2, List<&2, U32>>>, +ys: List<&2, List<&2, List<&2, U32>>>) -> {fe_any(r, G.AaGCuts.append(xs, ys)) == Bool.or(fe_any(r, xs), fe_any(r, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{d, t}:
      %Equal.sym(Bool, fe_any(r, G.AaGCuts.append(t, ys)), Bool.or(fe_any(r, t), fe_any(r, ys)), fe_app(r, t, ys)) : {Bool.or(fe(r, d), _) == Bool.or(Bool.or(fe(r, d), fe_any(r, t)), fe_any(r, ys)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(fe(r, d), fe_any(r, t)), fe_any(r, ys)), Bool.or(fe(r, d), Bool.or(fe_any(r, t), fe_any(r, ys))), b.or_assoc(fe(r, d), fe_any(r, t), fe_any(r, ys)))

# an empty first piece: no single-byte token fits it
def ef_char(+c: U32, +r: List<&2, G.AaGTok>, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.empty_first(ds)) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      ef_char(c, r, t)

def ef_any(+r: List<&2, G.AaGTok>, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.empty_first(ds)) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      ef_any(r, t)

def ef_class(+n: Bool, +rs: List<&2, G.AaGRange>, +r: List<&2, G.AaGTok>, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.empty_first(ds)) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      ef_class(n, rs, r, t)

# ... and a star takes it
def ef_star(+r: List<&2, G.AaGTok>, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.empty_first(ds)) == G.AaGSeq.fits_any(r, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      %ef_star(r, t) : {Bool.or(G.AaGSeq.fits(r, d), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.empty_first(t))) == Bool.or(G.AaGSeq.fits(r, d), _) : Bool}
      {==}

def ef_star2(+r: List<&2, G.AaGTok>, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.empty_first(ds)) == G.AaGSeq.fits_any(r, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      %ef_star2(r, t) : {Bool.or(G.AaGSeq.fits(r, d), G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.empty_first(t))) == Bool.or(G.AaGSeq.fits(r, d), _) : Bool}
      {==}

# a first piece that starts with h: a single-byte token takes h and leaves
# an empty piece
def gr_char(+c: U32, +r: List<&2, G.AaGTok>, +h: U32, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.grow(h, ds)) == Bool.and(U32.is_eq(h, c), fe_any(r, ds)) : Bool}:
  match ds:
    case Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_eq(h, c), False{}), False{}, b.and_false_r(U32.is_eq(h, c)))
    case Con{d, t}:
      match d:
        case Nil{}:
          gr_char(c, r, h, t)
        case Con{p, ps}:
          %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.grow(h, t)), Bool.and(U32.is_eq(h, c), fe_any(r, t)), gr_char(c, r, h, t)) : {Bool.or(Bool.and(Bool.and(U32.is_eq(h, c), X.AaText.is_nil(p)), G.AaGSeq.fits(r, ps)), _) == Bool.and(U32.is_eq(h, c), Bool.or(Bool.and(X.AaText.is_nil(p), G.AaGSeq.fits(r, ps)), fe_any(r, t))) : Bool}
          b.factor(U32.is_eq(h, c), X.AaText.is_nil(p), G.AaGSeq.fits(r, ps), fe_any(r, t))

def gr_any(+r: List<&2, G.AaGTok>, +h: U32, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.grow(h, ds)) == Bool.and(U32.is_ne(h, 47), fe_any(r, ds)) : Bool}:
  match ds:
    case Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_ne(h, 47), False{}), False{}, b.and_false_r(U32.is_ne(h, 47)))
    case Con{d, t}:
      match d:
        case Nil{}:
          gr_any(r, h, t)
        case Con{p, ps}:
          %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.grow(h, t)), Bool.and(U32.is_ne(h, 47), fe_any(r, t)), gr_any(r, h, t)) : {Bool.or(Bool.and(Bool.and(U32.is_ne(h, 47), X.AaText.is_nil(p)), G.AaGSeq.fits(r, ps)), _) == Bool.and(U32.is_ne(h, 47), Bool.or(Bool.and(X.AaText.is_nil(p), G.AaGSeq.fits(r, ps)), fe_any(r, t))) : Bool}
          b.factor(U32.is_ne(h, 47), X.AaText.is_nil(p), G.AaGSeq.fits(r, ps), fe_any(r, t))

def gr_class(+n: Bool, +rs: List<&2, G.AaGRange>, +r: List<&2, G.AaGTok>, +h: U32, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.grow(h, ds)) == Bool.and(G.AaGClass.has(n, rs, h), fe_any(r, ds)) : Bool}:
  match ds:
    case Nil{}:
      Equal.sym(Bool, Bool.and(G.AaGClass.has(n, rs, h), False{}), False{}, b.and_false_r(G.AaGClass.has(n, rs, h)))
    case Con{d, t}:
      match d:
        case Nil{}:
          gr_class(n, rs, r, h, t)
        case Con{p, ps}:
          %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.grow(h, t)), Bool.and(G.AaGClass.has(n, rs, h), fe_any(r, t)), gr_class(n, rs, r, h, t)) : {Bool.or(Bool.and(Bool.and(G.AaGClass.has(n, rs, h), X.AaText.is_nil(p)), G.AaGSeq.fits(r, ps)), _) == Bool.and(G.AaGClass.has(n, rs, h), Bool.or(Bool.and(X.AaText.is_nil(p), G.AaGSeq.fits(r, ps)), fe_any(r, t))) : Bool}
          b.factor(G.AaGClass.has(n, rs, h), X.AaText.is_nil(p), G.AaGSeq.fits(r, ps), fe_any(r, t))

# ... a star takes h if it is not '/', and goes on
def gr_star(+r: List<&2, G.AaGTok>, +h: U32, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.grow(h, ds)) == Bool.and(U32.is_ne(h, 47), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, ds)) : Bool}:
  match ds:
    case Nil{}:
      Equal.sym(Bool, Bool.and(U32.is_ne(h, 47), False{}), False{}, b.and_false_r(U32.is_ne(h, 47)))
    case Con{d, t}:
      match d:
        case Nil{}:
          gr_star(r, h, t)
        case Con{p, ps}:
          %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.grow(h, t)), Bool.and(U32.is_ne(h, 47), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, t)), gr_star(r, h, t)) : {Bool.or(Bool.and(Bool.and(U32.is_ne(h, 47), G.AaGPiece.no_slash(p)), G.AaGSeq.fits(r, ps)), _) == Bool.and(U32.is_ne(h, 47), Bool.or(Bool.and(G.AaGPiece.no_slash(p), G.AaGSeq.fits(r, ps)), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, t))) : Bool}
          b.factor(U32.is_ne(h, 47), G.AaGPiece.no_slash(p), G.AaGSeq.fits(r, ps), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, t))

# ... a double star takes any h
def gr_star2(+r: List<&2, G.AaGTok>, +h: U32, +ds: List<&2, List<&2, List<&2, U32>>>) -> {G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.grow(h, ds)) == G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case Nil{}:
          gr_star2(r, h, t)
        case Con{p, ps}:
          %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.grow(h, t)), G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, t), gr_star2(r, h, t)) : {Bool.or(G.AaGSeq.fits(r, ps), _) == Bool.or(G.AaGSeq.fits(r, ps), G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, t)) : Bool}
          {==}

# cutting into one more piece and asking for an empty first piece is cutting into as many
def fe_ef(+r: List<&2, G.AaGTok>, +ds: List<&2, List<&2, List<&2, U32>>>) -> {fe_any(r, G.AaGCuts.empty_first(ds)) == G.AaGSeq.fits_any(r, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      %fe_ef(r, t) : {Bool.or(G.AaGSeq.fits(r, d), fe_any(r, G.AaGCuts.empty_first(t))) == Bool.or(G.AaGSeq.fits(r, d), _) : Bool}
      {==}

def fe_gr(+r: List<&2, G.AaGTok>, +h: U32, +ds: List<&2, List<&2, List<&2, U32>>>) -> {fe_any(r, G.AaGCuts.grow(h, ds)) == False{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case Nil{}:
          fe_gr(r, h, t)
        case Con{p, ps}:
          fe_gr(r, h, t)

def fe_cuts(+r: List<&2, G.AaGTok>, +s: List<&2, U32>) -> {fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), s)) == G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), s)) : Bool}:
  match s:
    case Nil{}:
      fe_ef(r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))
    case Con{h, t}:
      %Equal.sym(Bool, fe_any(r, G.AaGCuts.append(G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), Bool.or(fe_any(r, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), fe_any(r, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), fe_app(r, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : {_ == G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})) : Bool}
      %Equal.sym(Bool, fe_any(r, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), fe_ef(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))) : {Bool.or(_, fe_any(r, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) == G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})) : Bool}
      %Equal.sym(Bool, fe_any(r, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), False{}, fe_gr(r, h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : {Bool.or(G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), _) == G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})) : Bool}
      b.or_false_r(G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})))

# the matcher agrees with the list model: induction on the sequence, and on
# the path under a star
def glob.thm(+seq: List<&2, G.AaGTok>, +s: List<&2, U32>) -> {G.AaGSeq.matches(seq, s) == G.AaGSeq.model(seq, s) : Bool}:
  match seq:
    case Nil{}:
      match s:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case Con{tok, r}:
      match tok:
        case G.AaGChar{c}:
          match s:
            case Nil{}:
              Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))), False{}, ef_char(c, r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{})))
            case Con{h, t}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.append(G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), Bool.or(G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), fa_app(Con{G.AaGChar{c}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : {Bool.and(U32.is_eq(h, c), G.AaGSeq.matches(r, t)) == _ : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), False{}, ef_char(c, r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))) : {Bool.and(U32.is_eq(h, c), G.AaGSeq.matches(r, t)) == Bool.or(_, G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGChar{c}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), Bool.and(U32.is_eq(h, c), fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), gr_char(c, r, h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : {Bool.and(U32.is_eq(h, c), G.AaGSeq.matches(r, t)) == Bool.or(False{}, _) : Bool}
              %Equal.sym(Bool, fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), t)), fe_cuts(r, t)) : {Bool.and(U32.is_eq(h, c), G.AaGSeq.matches(r, t)) == Bool.or(False{}, Bool.and(U32.is_eq(h, c), _)) : Bool}
              %glob.thm(r, t) : {Bool.and(U32.is_eq(h, c), G.AaGSeq.matches(r, t)) == Bool.or(False{}, Bool.and(U32.is_eq(h, c), _)) : Bool}
              {==}
        case G.AaGAny{}:
          match s:
            case Nil{}:
              Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))), False{}, ef_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{})))
            case Con{h, t}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.append(G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), Bool.or(G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), fa_app(Con{G.AaGAny{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : {Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(r, t)) == _ : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), False{}, ef_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))) : {Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(r, t)) == Bool.or(_, G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGAny{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), Bool.and(U32.is_ne(h, 47), fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), gr_any(r, h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : {Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(r, t)) == Bool.or(False{}, _) : Bool}
              %Equal.sym(Bool, fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), t)), fe_cuts(r, t)) : {Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(r, t)) == Bool.or(False{}, Bool.and(U32.is_ne(h, 47), _)) : Bool}
              %glob.thm(r, t) : {Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(r, t)) == Bool.or(False{}, Bool.and(U32.is_ne(h, 47), _)) : Bool}
              {==}
        case G.AaGClass{n, rs}:
          match s:
            case Nil{}:
              Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))), False{}, ef_class(n, rs, r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{})))
            case Con{h, t}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.append(G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), Bool.or(G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), fa_app(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : {Bool.and(G.AaGClass.has(n, rs, h), G.AaGSeq.matches(r, t)) == _ : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), False{}, ef_class(n, rs, r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))) : {Bool.and(G.AaGClass.has(n, rs, h), G.AaGSeq.matches(r, t)) == Bool.or(_, G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGClass{n, rs}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), Bool.and(G.AaGClass.has(n, rs, h), fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), gr_class(n, rs, r, h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : {Bool.and(G.AaGClass.has(n, rs, h), G.AaGSeq.matches(r, t)) == Bool.or(False{}, _) : Bool}
              %Equal.sym(Bool, fe_any(r, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), t)), fe_cuts(r, t)) : {Bool.and(G.AaGClass.has(n, rs, h), G.AaGSeq.matches(r, t)) == Bool.or(False{}, Bool.and(G.AaGClass.has(n, rs, h), _)) : Bool}
              %glob.thm(r, t) : {Bool.and(G.AaGClass.has(n, rs, h), G.AaGSeq.matches(r, t)) == Bool.or(False{}, Bool.and(G.AaGClass.has(n, rs, h), _)) : Bool}
              {==}
        case G.AaGStar{}:
          match s:
            case Nil{}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{})), ef_star(r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))) : {G.AaGSeq.matches(r, Nil{}) == _ : Bool}
              glob.thm(r, Nil{})
            case Con{h, t}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.append(G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), Bool.or(G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), fa_app(Con{G.AaGStar{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t))) == _ : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), ef_star(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t))) == Bool.or(_, G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), Bool.and(U32.is_ne(h, 47), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), gr_star(r, h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t))) == Bool.or(G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), _) : Bool}
              %glob.thm(r, Con{h, t}) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t))) == Bool.or(_, Bool.and(U32.is_ne(h, 47), G.AaGSeq.fits_any(Con{G.AaGStar{}, r}, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : Bool}
              %glob.thm(seq, t) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t))) == Bool.or(G.AaGSeq.matches(r, Con{h, t}), Bool.and(U32.is_ne(h, 47), _)) : Bool}
              {==}
        case G.AaGStar2{}:
          match s:
            case Nil{}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{})), ef_star2(r, G.AaGCuts.all(G.AaGSeq.len(r), Nil{}))) : {G.AaGSeq.matches(r, Nil{}) == _ : Bool}
              glob.thm(r, Nil{})
            case Con{h, t}:
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.append(G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), Bool.or(G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))), fa_app(Con{G.AaGStar2{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)) == _ : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.empty_first(G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))), G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), ef_star2(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t}))) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)) == Bool.or(_, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)))) : Bool}
              %Equal.sym(Bool, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.grow(h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))), G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.all(1n+G.AaGSeq.len(r), t)), gr_star2(r, h, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)) == Bool.or(G.AaGSeq.fits_any(r, G.AaGCuts.all(G.AaGSeq.len(r), Con{h, t})), _) : Bool}
              %glob.thm(r, Con{h, t}) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)) == Bool.or(_, G.AaGSeq.fits_any(Con{G.AaGStar2{}, r}, G.AaGCuts.all(1n+G.AaGSeq.len(r), t))) : Bool}
              %glob.thm(seq, t) : {Bool.or(G.AaGSeq.matches(r, Con{h, t}), G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)) == Bool.or(G.AaGSeq.matches(r, Con{h, t}), _) : Bool}
              {==}

# The fast matcher equals the backtracking one

# the propositional identities each token's step comes to

def nfa.taut_nil(+a: Bool, +n: Bool, +c: Bool, +b: Bool) -> {Bool.and(a, n) == Bool.or(Bool.and(a, n), Bool.or(Bool.and(c, False{}), Bool.and(b, False{}))) : Bool}:
  match a:
    case True{}:
      match n:
        case True{}:
          match c:
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match c:
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match n:
        case True{}:
          match c:
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match c:
            case True{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match b:
                case True{}:
                  {==}
                case False{}:
                  {==}

def nfa.taut_adv(+hb: Bool, +cin: Bool, +ain: Bool, +e: Bool, +p: Bool, +q: Bool, +r: Bool, +z: Bool) -> {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(hb, cin), False{}), ain), p), Bool.or(Bool.and(Bool.and(Bool.or(hb, cin), e), q), Bool.or(Bool.and(Bool.and(Bool.or(hb, cin), False{}), r), z))) == Bool.or(Bool.and(ain, p), Bool.or(Bool.and(cin, Bool.and(e, q)), Bool.or(Bool.and(hb, Bool.and(e, q)), z))) : Bool}:
  match hb:
    case True{}:
      match cin:
        case True{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
        case False{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
    case False{}:
      match cin:
        case True{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
        case False{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}

def nfa.taut_star(+hb: Bool, +cin: Bool, +ain: Bool, +e: Bool, +p: Bool, +q: Bool, +r: Bool, +z: Bool) -> {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(hb, cin), e), ain), p), Bool.or(Bool.and(Bool.and(Bool.or(hb, cin), False{}), q), Bool.or(Bool.and(Bool.and(Bool.or(hb, cin), True{}), r), z))) == Bool.or(Bool.and(ain, p), Bool.or(Bool.and(cin, Bool.or(r, Bool.and(e, p))), Bool.or(Bool.and(hb, Bool.or(r, Bool.and(e, p))), z))) : Bool}:
  match hb:
    case True{}:
      match cin:
        case True{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
        case False{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
    case False{}:
      match cin:
        case True{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
        case False{}:
          match ain:
            case True{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
            case False{}:
              match e:
                case True{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                case False{}:
                  match p:
                    case True{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                    case False{}:
                      match q:
                        case True{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                        case False{}:
                          match r:
                            case True{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}
                            case False{}:
                              match z:
                                case True{}:
                                  {==}
                                case False{}:
                                  {==}

def nfa.taut_star2(+hb: Bool, +cin: Bool, +ain: Bool, +p: Bool, +q: Bool, +r: Bool, +z: Bool) -> {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(hb, cin), True{}), ain), p), Bool.or(Bool.and(Bool.and(Bool.or(hb, cin), False{}), q), Bool.or(Bool.and(Bool.and(Bool.or(hb, cin), True{}), r), z))) == Bool.or(Bool.and(ain, p), Bool.or(Bool.and(cin, Bool.or(r, p)), Bool.or(Bool.and(hb, Bool.or(r, p)), z))) : Bool}:
  match hb:
    case True{}:
      match cin:
        case True{}:
          match ain:
            case True{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
            case False{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
        case False{}:
          match ain:
            case True{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
            case False{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
    case False{}:
      match cin:
        case True{}:
          match ain:
            case True{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
            case False{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
        case False{}:
          match ain:
            case True{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
            case False{}:
              match p:
                case True{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                case False{}:
                  match q:
                    case True{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                    case False{}:
                      match r:
                        case True{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}
                        case False{}:
                          match z:
                            case True{}:
                              {==}
                            case False{}:
                              {==}

# one byte: the positions after it accept t exactly when, before it, the
# positions (with the carried ones) accept h then t
def nfa.step(+seq: List<&2, G.AaGTok>, +bs: List<&2, Bool>, +cin: Bool, +ain: Bool, +h: U32, +t: List<&2, U32>) -> {G.AaGNfa.sem(seq, G.AaGNfa.next(seq, bs, cin, ain, h), t) == Bool.or(Bool.and(ain, G.AaGSeq.matches(seq, t)), Bool.or(Bool.and(cin, G.AaGSeq.matches(seq, Con{h, t})), G.AaGNfa.sem(seq, bs, Con{h, t}))) : Bool}:
  match seq:
    case Nil{}:
      nfa.taut_nil(ain, X.AaText.is_nil(t), cin, G.AaGNfa.hd(bs))
    case Con{tok, r}:
      match tok:
        case G.AaGChar{c}:
          %Equal.sym(Bool, G.AaGNfa.sem(r, G.AaGNfa.next(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_eq(h, c)), h), t), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_eq(h, c)), G.AaGSeq.matches(r, t)), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), G.AaGSeq.matches(r, Con{h, t})), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))), nfa.step(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_eq(h, c)), h, t)) : {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), ain), G.AaGSeq.matches(Con{G.AaGChar{c}, r}, t)), _) == Bool.or(Bool.and(ain, G.AaGSeq.matches(Con{G.AaGChar{c}, r}, t)), Bool.or(Bool.and(cin, G.AaGSeq.matches(Con{G.AaGChar{c}, r}, Con{h, t})), G.AaGNfa.sem(Con{G.AaGChar{c}, r}, bs, Con{h, t}))) : Bool}
          nfa.taut_adv(G.AaGNfa.hd(bs), cin, ain, U32.is_eq(h, c), G.AaGSeq.matches(Con{G.AaGChar{c}, r}, t), G.AaGSeq.matches(r, t), G.AaGSeq.matches(r, Con{h, t}), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))
        case G.AaGAny{}:
          %Equal.sym(Bool, G.AaGNfa.sem(r, G.AaGNfa.next(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_ne(h, 47)), h), t), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_ne(h, 47)), G.AaGSeq.matches(r, t)), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), G.AaGSeq.matches(r, Con{h, t})), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))), nfa.step(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_ne(h, 47)), h, t)) : {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), ain), G.AaGSeq.matches(Con{G.AaGAny{}, r}, t)), _) == Bool.or(Bool.and(ain, G.AaGSeq.matches(Con{G.AaGAny{}, r}, t)), Bool.or(Bool.and(cin, G.AaGSeq.matches(Con{G.AaGAny{}, r}, Con{h, t})), G.AaGNfa.sem(Con{G.AaGAny{}, r}, bs, Con{h, t}))) : Bool}
          nfa.taut_adv(G.AaGNfa.hd(bs), cin, ain, U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGAny{}, r}, t), G.AaGSeq.matches(r, t), G.AaGSeq.matches(r, Con{h, t}), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))
        case G.AaGClass{n, rs}:
          %Equal.sym(Bool, G.AaGNfa.sem(r, G.AaGNfa.next(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), G.AaGClass.has(n, rs, h)), h), t), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), G.AaGClass.has(n, rs, h)), G.AaGSeq.matches(r, t)), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), G.AaGSeq.matches(r, Con{h, t})), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))), nfa.step(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), G.AaGClass.has(n, rs, h)), h, t)) : {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), ain), G.AaGSeq.matches(Con{G.AaGClass{n, rs}, r}, t)), _) == Bool.or(Bool.and(ain, G.AaGSeq.matches(Con{G.AaGClass{n, rs}, r}, t)), Bool.or(Bool.and(cin, G.AaGSeq.matches(Con{G.AaGClass{n, rs}, r}, Con{h, t})), G.AaGNfa.sem(Con{G.AaGClass{n, rs}, r}, bs, Con{h, t}))) : Bool}
          nfa.taut_adv(G.AaGNfa.hd(bs), cin, ain, G.AaGClass.has(n, rs, h), G.AaGSeq.matches(Con{G.AaGClass{n, rs}, r}, t), G.AaGSeq.matches(r, t), G.AaGSeq.matches(r, Con{h, t}), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))
        case G.AaGStar{}:
          %Equal.sym(Bool, G.AaGNfa.sem(r, G.AaGNfa.next(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), h), t), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), G.AaGSeq.matches(r, t)), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), G.AaGSeq.matches(r, Con{h, t})), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))), nfa.step(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), h, t)) : {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), U32.is_ne(h, 47)), ain), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t)), _) == Bool.or(Bool.and(ain, G.AaGSeq.matches(Con{G.AaGStar{}, r}, t)), Bool.or(Bool.and(cin, G.AaGSeq.matches(Con{G.AaGStar{}, r}, Con{h, t})), G.AaGNfa.sem(Con{G.AaGStar{}, r}, bs, Con{h, t}))) : Bool}
          nfa.taut_star(G.AaGNfa.hd(bs), cin, ain, U32.is_ne(h, 47), G.AaGSeq.matches(Con{G.AaGStar{}, r}, t), G.AaGSeq.matches(r, t), G.AaGSeq.matches(r, Con{h, t}), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))
        case G.AaGStar2{}:
          %Equal.sym(Bool, G.AaGNfa.sem(r, G.AaGNfa.next(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), h), t), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), G.AaGSeq.matches(r, t)), Bool.or(Bool.and(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), G.AaGSeq.matches(r, Con{h, t})), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))), nfa.step(r, G.AaGNfa.tl(bs), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), False{}), h, t)) : {Bool.or(Bool.and(Bool.or(Bool.and(Bool.or(G.AaGNfa.hd(bs), cin), True{}), ain), G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)), _) == Bool.or(Bool.and(ain, G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t)), Bool.or(Bool.and(cin, G.AaGSeq.matches(Con{G.AaGStar2{}, r}, Con{h, t})), G.AaGNfa.sem(Con{G.AaGStar2{}, r}, bs, Con{h, t}))) : Bool}
          nfa.taut_star2(G.AaGNfa.hd(bs), cin, ain, G.AaGSeq.matches(Con{G.AaGStar2{}, r}, t), G.AaGSeq.matches(r, t), G.AaGSeq.matches(r, Con{h, t}), G.AaGNfa.sem(r, G.AaGNfa.tl(bs), Con{h, t}))

# no position active: nothing accepted
def nfa.dead(+seq: List<&2, G.AaGTok>, +bs: List<&2, Bool>, +s: List<&2, U32>, +e: {G.AaGNfa.alive(bs) == False{} : Bool}) -> {G.AaGNfa.sem(seq, bs, s) == False{} : Bool}:
  match seq:
    case Nil{}:
      match bs:
        case Nil{}:
          {==}
        case Con{b, rest}:
          match b:
            case True{}:
              b.absurd_tf(Bool, G.AaGNfa.sem(Nil{}, Con{True{}, rest}, s), False{}, e)
            case False{}:
              {==}
    case Con{tok, r}:
      match bs:
        case Nil{}:
          nfa.dead(r, Nil{}, s, {==})
        case Con{b, rest}:
          match b:
            case True{}:
              b.absurd_tf(Bool, G.AaGNfa.sem(Con{tok, r}, Con{True{}, rest}, s), False{}, e)
            case False{}:
              nfa.dead(r, rest, s, e)

# the run: the positions accept the path (a: whether some position is active)
def nfa.run(+s: List<&2, U32>, +a: Bool, +seq: List<&2, G.AaGTok>, +bs: List<&2, Bool>, +e: {G.AaGNfa.alive(bs) == a : Bool}) -> {G.AaGNfa.run(s, a, seq, bs) == G.AaGNfa.sem(seq, bs, s) : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{h, t}:
      match a:
        case False{}:
          Equal.sym(Bool, G.AaGNfa.sem(seq, bs, Con{h, t}), False{}, nfa.dead(seq, bs, Con{h, t}, e))
        case True{}:
          Equal.trans(Bool, G.AaGNfa.run(t, G.AaGNfa.alive(G.AaGNfa.next(seq, bs, False{}, False{}, h)), seq, G.AaGNfa.next(seq, bs, False{}, False{}, h)), G.AaGNfa.sem(seq, G.AaGNfa.next(seq, bs, False{}, False{}, h), t), G.AaGNfa.sem(seq, bs, Con{h, t}), nfa.run(t, G.AaGNfa.alive(G.AaGNfa.next(seq, bs, False{}, False{}, h)), seq, G.AaGNfa.next(seq, bs, False{}, False{}, h), {==}), nfa.step(seq, bs, False{}, False{}, h, t))

def nfa.falses_dead(+seq: List<&2, G.AaGTok>) -> {G.AaGNfa.alive(G.AaGNfa.falses(seq)) == False{} : Bool}:
  match seq:
    case Nil{}:
      {==}
    case Con{tok, r}:
      nfa.falses_dead(r)

# only the whole sequence active: what the backtracking matcher accepts
def nfa.start(+seq: List<&2, G.AaGTok>, +s: List<&2, U32>) -> {G.AaGNfa.sem(seq, G.AaGNfa.start(seq), s) == G.AaGSeq.matches(seq, s) : Bool}:
  match seq:
    case Nil{}:
      {==}
    case Con{tok, r}:
      %Equal.sym(Bool, G.AaGNfa.sem(r, G.AaGNfa.falses(r), s), False{}, nfa.dead(r, G.AaGNfa.falses(r), s, nfa.falses_dead(r))) : {Bool.or(G.AaGSeq.matches(Con{tok, r}, s), _) == G.AaGSeq.matches(Con{tok, r}, s) : Bool}
      b.or_false_r(G.AaGSeq.matches(Con{tok, r}, s))

def nfa.start_alive(+seq: List<&2, G.AaGTok>) -> {G.AaGNfa.alive(G.AaGNfa.start(seq)) == True{} : Bool}:
  match seq:
    case Nil{}:
      {==}
    case Con{tok, r}:
      {==}

def nfa.thm(+seq: List<&2, G.AaGTok>, +s: List<&2, U32>) -> {G.AaGSeq.run(seq, s) == G.AaGSeq.matches(seq, s) : Bool}:
  Equal.trans(Bool, G.AaGNfa.run(s, True{}, seq, G.AaGNfa.start(seq)), G.AaGNfa.sem(seq, G.AaGNfa.start(seq), s), G.AaGSeq.matches(seq, s), nfa.run(s, True{}, seq, G.AaGNfa.start(seq), nfa.start_alive(seq)), nfa.start(seq, s))

def glob.alts(+alts: List<&2, List<&2, G.AaGTok>>, +s: List<&2, U32>) -> {G.AaGlob.matches.go(alts, s) == G.AaGlob.model.go(alts, s) : Bool}:
  match alts:
    case Nil{}:
      {==}
    case Con{a, t}:
      %glob.thm(a, s) : {Bool.or(G.AaGSeq.run(a, s), G.AaGlob.matches.go(t, s)) == Bool.or(_, G.AaGlob.model.go(t, s)) : Bool}
      %nfa.thm(a, s) : {Bool.or(G.AaGSeq.run(a, s), G.AaGlob.matches.go(t, s)) == Bool.or(_, G.AaGlob.model.go(t, s)) : Bool}
      %glob.alts(t, s) : {Bool.or(G.AaGSeq.run(a, s), G.AaGlob.matches.go(t, s)) == Bool.or(G.AaGSeq.run(a, s), _) : Bool}
      {==}

def glob.alts_ref(+alts: List<&2, List<&2, G.AaGTok>>, +s: List<&2, U32>) -> {G.AaGlob.matches_ref.go(alts, s) == G.AaGlob.model.go(alts, s) : Bool}:
  match alts:
    case Nil{}:
      {==}
    case Con{a, t}:
      %glob.thm(a, s) : {Bool.or(G.AaGSeq.matches(a, s), G.AaGlob.matches_ref.go(t, s)) == Bool.or(_, G.AaGlob.model.go(t, s)) : Bool}
      %glob.alts_ref(t, s) : {Bool.or(G.AaGSeq.matches(a, s), G.AaGlob.matches_ref.go(t, s)) == Bool.or(G.AaGSeq.matches(a, s), _) : Bool}
      {==}

def Laws.glob_seq_model(seq, s):
  glob.thm(seq, s)

def Laws.glob_run(seq, s):
  nfa.thm(seq, s)

def Laws.glob_model(g, s):
  match g:
    case G.AaGlob{alts, lit}:
      glob.alts(alts, s)

def Laws.glob_ref_model(g, s):
  match g:
    case G.AaGlob{alts, lit}:
      glob.alts_ref(alts, s)

# Contradictions

# Permission bits

# what minus leaves never meets what it took away
def bits.minus_meets(+a: List<&2, Bool>, +d: List<&2, Bool>) -> {P.AaBits.meets(P.AaBits.minus(a, d), d) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match x:
        case False{}:
          match d:
            case Nil{}:
              {==}
            case Con{y, ys}:
              bits.minus_meets(xs, ys)
        case True{}:
          match d:
            case Nil{}:
              {==}
            case Con{y, ys}:
              match y:
                case True{}:
                  bits.minus_meets(xs, ys)
                case False{}:
                  bits.minus_meets(xs, ys)

# a request with no bit set meets nothing
def bits.nany_meets(+r: List<&2, Bool>, +d: List<&2, Bool>) -> {Bool.and(Bool.not(P.AaBits.any(r)), P.AaBits.meets(r, d)) == False{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{z, zs}:
      match z:
        case True{}:
          {==}
        case False{}:
          match d:
            case Nil{}:
              b.and_false_r(Bool.not(P.AaBits.any(zs)))
            case Con{y, ys}:
              bits.nany_meets(zs, ys)

# a request that minus(a, d) covers does not meet d
def bits.covers_meets(+a: List<&2, Bool>, +d: List<&2, Bool>, +r: List<&2, Bool>) -> {Bool.and(P.AaBits.covers(P.AaBits.minus(a, d), r), P.AaBits.meets(r, d)) == False{} : Bool}:
  match a:
    case Nil{}:
      match d:
        case Nil{}:
          match r:
            case Nil{}:
              {==}
            case Con{z, zs}:
              b.and_false_r(P.AaBits.covers(Nil{}, Con{z, zs}))
        case Con{y, ys}:
          match r:
            case Nil{}:
              {==}
            case Con{z, zs}:
              match z:
                case True{}:
                  {==}
                case False{}:
                  bits.nany_meets(zs, ys)
    case Con{x, xs}:
      match x:
        case True{}:
          match d:
            case Nil{}:
              match r:
                case Nil{}:
                  {==}
                case Con{z, zs}:
                  b.and_false_r(P.AaBits.covers(Con{True{}, xs}, Con{z, zs}))
            case Con{y, ys}:
              match y:
                case True{}:
                  match r:
                    case Nil{}:
                      {==}
                    case Con{z, zs}:
                      match z:
                        case True{}:
                          {==}
                        case False{}:
                          bits.covers_meets(xs, ys, zs)
                case False{}:
                  match r:
                    case Nil{}:
                      {==}
                    case Con{z, zs}:
                      match z:
                        case True{}:
                          bits.covers_meets(xs, ys, zs)
                        case False{}:
                          bits.covers_meets(xs, ys, zs)
        case False{}:
          match d:
            case Nil{}:
              match r:
                case Nil{}:
                  {==}
                case Con{z, zs}:
                  b.and_false_r(P.AaBits.covers(Con{False{}, xs}, Con{z, zs}))
            case Con{y, ys}:
              match y:
                case True{}:
                  match r:
                    case Nil{}:
                      {==}
                    case Con{z, zs}:
                      match z:
                        case True{}:
                          {==}
                        case False{}:
                          bits.covers_meets(xs, ys, zs)
                case False{}:
                  match r:
                    case Nil{}:
                      {==}
                    case Con{z, zs}:
                      match z:
                        case True{}:
                          {==}
                        case False{}:
                          bits.covers_meets(xs, ys, zs)

def bits.or_assoc(+a: List<&2, Bool>, +b: List<&2, Bool>, +c: List<&2, Bool>) -> {P.AaBits.or(P.AaBits.or(a, b), c) == P.AaBits.or(a, P.AaBits.or(b, c)) : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match b:
        case Nil{}:
          {==}
        case Con{y, ys}:
          match c:
            case Nil{}:
              {==}
            case Con{z, zs}:
              %b.or_assoc(x, y, z) : {Con{Bool.or(Bool.or(x, y), z), P.AaBits.or(P.AaBits.or(xs, ys), zs)} == Con{_, P.AaBits.or(xs, P.AaBits.or(ys, zs))} : List<&2, Bool>}
              %bits.or_assoc(xs, ys, zs) : {Con{Bool.or(Bool.or(x, y), z), P.AaBits.or(P.AaBits.or(xs, ys), zs)} == Con{Bool.or(Bool.or(x, y), z), _} : List<&2, Bool>}
              {==}

def b.or_idem(+a: Bool) -> {Bool.or(a, a) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bits.or_idem(+a: List<&2, Bool>) -> {P.AaBits.or(a, a) == a : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      %b.or_idem(x) : {Con{Bool.or(x, x), P.AaBits.or(xs, xs)} == Con{_, xs} : List<&2, Bool>}
      %bits.or_idem(xs) : {Con{Bool.or(x, x), P.AaBits.or(xs, xs)} == Con{Bool.or(x, x), _} : List<&2, Bool>}
      {==}

def bits.or_nil_r(+a: List<&2, Bool>) -> {P.AaBits.or(a, Nil{}) == a : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      {==}

# The same on permission sets

def pm.covers_meets(+a: P.AaPerms, +d: P.AaPerms, +r: P.AaPerms) -> {Bool.and(P.AaPerms.covers(P.AaPerms.minus(a, d), r), P.AaPerms.meets(r, d)) == False{} : Bool}:
  match a:
    case P.AaPerms{x}:
      match d:
        case P.AaPerms{y}:
          match r:
            case P.AaPerms{z}:
              bits.covers_meets(x, y, z)

def pm.minus_meets(+a: P.AaPerms, +d: P.AaPerms) -> {P.AaPerms.meets(P.AaPerms.minus(a, d), d) == False{} : Bool}:
  match a:
    case P.AaPerms{x}:
      match d:
        case P.AaPerms{y}:
          bits.minus_meets(x, y)

def pm.assoc(+a: P.AaPerms, +b: P.AaPerms, +c: P.AaPerms) -> {P.AaPerms.union(P.AaPerms.union(a, b), c) == P.AaPerms.union(a, P.AaPerms.union(b, c)) : P.AaPerms}:
  match a:
    case P.AaPerms{x}:
      match b:
        case P.AaPerms{y}:
          match c:
            case P.AaPerms{z}:
              Equal.cong(List<&2, Bool>, P.AaPerms, l => P.AaPerms{l}, P.AaBits.or(P.AaBits.or(x, y), z), P.AaBits.or(x, P.AaBits.or(y, z)), bits.or_assoc(x, y, z))

def pm.idem(+a: P.AaPerms) -> {P.AaPerms.union(a, a) == a : P.AaPerms}:
  match a:
    case P.AaPerms{x}:
      Equal.cong(List<&2, Bool>, P.AaPerms, l => P.AaPerms{l}, P.AaBits.or(x, x), x, bits.or_idem(x))

def pm.none_r(+a: P.AaPerms) -> {P.AaPerms.union(a, P.AaPerms.none()) == a : P.AaPerms}:
  match a:
    case P.AaPerms{x}:
      Equal.cong(List<&2, Bool>, P.AaPerms, l => P.AaPerms{l}, P.AaBits.or(x, Nil{}), x, bits.or_nil_r(x))

# Decisions

def dec.ok(+b: Bool) -> {V.AaDecision.allowed(V.AaEval.choose(b, V.AaAudit{}, V.AaAllow{})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a deny rule meets the request (hit), so the grants cannot cover it
def dw.mode(+hit: Bool, +cov: Bool, +m: PR.AaMode, +opts: O.AaOptions, +ok: V.AaDecision, +no: V.AaDecision, +h: {hit == True{} : Bool}, +e: {Bool.and(cov, hit) == False{} : Bool}, +h1: {V.AaEval.deny_applies(opts, m) == True{} : Bool}, +hno: {V.AaDecision.allowed(no) == False{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide.mode(m, cov, hit, O.AaOptions.complain_deny(opts), ok, no)) == False{} : Bool}:
  match hit:
    case False{}:
      b.absurd(Bool, V.AaDecision.allowed(V.AaEval.decide.mode(m, cov, False{}, O.AaOptions.complain_deny(opts), ok, no)), False{}, h)
    case True{}:
      match cov:
        case True{}:
          b.absurd_tf(Bool, V.AaDecision.allowed(V.AaEval.decide.mode(m, True{}, True{}, O.AaOptions.complain_deny(opts), ok, no)), False{}, e)
        case False{}:
          match m:
            case PR.AaModeEnforce{}:
              hno
            case PR.AaModePrompt{}:
              hno
            case PR.AaModeKill{}:
              {==}
            case PR.AaModeDefaultAllow{}:
              hno
            case PR.AaModeUnconfined{}:
              b.absurd(Bool, True{}, False{}, h1)
            case PR.AaModeComplain{}:
              match opts:
                case O.AaOptions{c, d, v}:
                  match c:
                    case True{}:
                      hno
                    case False{}:
                      b.absurd(Bool, True{}, False{}, h1)

def dw.acc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +acc: V.AaAcc, +h1: {V.AaEval.deny_applies(opts, PR.AaFlags.mode(flags)) == True{} : Bool}, +h2: {P.AaPerms.meets(req, V.AaAcc.deny(acc)) == True{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide.acc(opts, flags, req, acc)) == False{} : Bool}:
  match flags:
    case PR.AaFlags{m, fa}:
      match acc:
        case V.AaAcc{al, de, au, qu}:
          dw.mode(P.AaPerms.meets(req, de), P.AaPerms.covers(P.AaPerms.minus(al, de), req), m, opts, V.AaEval.choose(Bool.or(fa, P.AaPerms.meets(req, au)), V.AaAudit{}, V.AaAllow{}), V.AaDeny{Bool.or(fa, Bool.not(P.AaPerms.covers(P.AaPerms.minus(qu, au), P.AaPerms.minus(req, P.AaPerms.minus(al, de)))))}, h2, pm.covers_meets(al, de, req), h1, {==})

# no grant, a nonempty request, an enforcing mode: denied
def ud.mode(+cov: Bool, +m: PR.AaMode, +hit: Bool, +cd: Bool, +ok: V.AaDecision, +no: V.AaDecision, +hc: {cov == False{} : Bool}, +h1: {PR.AaMode.enforcing(m) == True{} : Bool}, +hno: {V.AaDecision.allowed(no) == False{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide.mode(m, cov, hit, cd, ok, no)) == False{} : Bool}:
  match cov:
    case True{}:
      b.absurd_tf(Bool, V.AaDecision.allowed(V.AaEval.decide.mode(m, True{}, hit, cd, ok, no)), False{}, hc)
    case False{}:
      match m:
        case PR.AaModeEnforce{}:
          hno
        case PR.AaModePrompt{}:
          hno
        case PR.AaModeKill{}:
          {==}
        case PR.AaModeDefaultAllow{}:
          b.absurd(Bool, V.AaDecision.allowed(V.AaEval.choose(hit, no, ok)), False{}, h1)
        case PR.AaModeUnconfined{}:
          b.absurd(Bool, True{}, False{}, h1)
        case PR.AaModeComplain{}:
          b.absurd(Bool, V.AaDecision.allowed(V.AaEval.choose(Bool.and(cd, hit), no, V.AaComplain{})), False{}, h1)

# complain mode: allowed unless an applicable deny rule meets the request
def cd.mode(+m: PR.AaMode, +cov: Bool, +hit: Bool, +opts: O.AaOptions, +ok: V.AaDecision, +no: V.AaDecision, +h: {PR.AaMode.is_complain(m) == True{} : Bool}, +e: {Bool.and(cov, hit) == False{} : Bool}, +hok: {V.AaDecision.allowed(ok) == True{} : Bool}, +hno: {V.AaDecision.allowed(no) == False{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide.mode(m, cov, hit, O.AaOptions.complain_deny(opts), ok, no)) == Bool.not(Bool.and(O.AaOptions.complain_deny(opts), hit)) : Bool}:
  match m:
    case PR.AaModeComplain{}:
      match cov:
        case True{}:
          match hit:
            case True{}:
              b.absurd_tf(Bool, V.AaDecision.allowed(ok), Bool.not(Bool.and(O.AaOptions.complain_deny(opts), True{})), e)
            case False{}:
              match opts:
                case O.AaOptions{c, d, v}:
                  match c:
                    case True{}:
                      hok
                    case False{}:
                      hok
        case False{}:
          match hit:
            case True{}:
              match opts:
                case O.AaOptions{c, d, v}:
                  match c:
                    case True{}:
                      hno
                    case False{}:
                      {==}
            case False{}:
              match opts:
                case O.AaOptions{c, d, v}:
                  match c:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
    case PR.AaModeEnforce{}:
      b.absurd(Bool, V.AaDecision.allowed(V.AaEval.choose(cov, ok, no)), Bool.not(Bool.and(O.AaOptions.complain_deny(opts), hit)), h)
    case PR.AaModePrompt{}:
      b.absurd(Bool, V.AaDecision.allowed(V.AaEval.choose(cov, ok, no)), Bool.not(Bool.and(O.AaOptions.complain_deny(opts), hit)), h)
    case PR.AaModeKill{}:
      b.absurd(Bool, V.AaDecision.allowed(V.AaEval.choose(cov, ok, V.AaKill{})), Bool.not(Bool.and(O.AaOptions.complain_deny(opts), hit)), h)
    case PR.AaModeDefaultAllow{}:
      b.absurd(Bool, V.AaDecision.allowed(V.AaEval.choose(hit, no, ok)), Bool.not(Bool.and(O.AaOptions.complain_deny(opts), hit)), h)
    case PR.AaModeUnconfined{}:
      b.absurd(Bool, True{}, Bool.not(Bool.and(O.AaOptions.complain_deny(opts), hit)), h)

def cd.acc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +acc: V.AaAcc, +h: {PR.AaMode.is_complain(PR.AaFlags.mode(flags)) == True{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide.acc(opts, flags, req, acc)) == Bool.not(Bool.and(O.AaOptions.complain_deny(opts), P.AaPerms.meets(req, V.AaAcc.deny(acc)))) : Bool}:
  match flags:
    case PR.AaFlags{m, fa}:
      match acc:
        case V.AaAcc{al, de, au, qu}:
          cd.mode(m, P.AaPerms.covers(P.AaPerms.minus(al, de), req), P.AaPerms.meets(req, de), opts, V.AaEval.choose(Bool.or(fa, P.AaPerms.meets(req, au)), V.AaAudit{}, V.AaAllow{}), V.AaDeny{Bool.or(fa, Bool.not(P.AaPerms.covers(P.AaPerms.minus(qu, au), P.AaPerms.minus(req, P.AaPerms.minus(al, de)))))}, h, pm.covers_meets(al, de, req), dec.ok(Bool.or(fa, P.AaPerms.meets(req, au))), {==})

def gnd.acc(+acc: V.AaAcc) -> {P.AaPerms.meets(V.AaAcc.granted(acc), V.AaAcc.deny(acc)) == False{} : Bool}:
  match acc:
    case V.AaAcc{al, de, au, qu}:
      pm.minus_meets(al, de)

def Laws.granted_never_denied(gs):
  gnd.acc(V.AaAcc.of(gs))

def Laws.deny_wins(opts, gs, flags, req, h1, h2):
  dw.acc(opts, flags, req, V.AaAcc.of(gs), h1, h2)

def ud.law(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +h1: {PR.AaMode.enforcing(PR.AaFlags.mode(flags)) == True{} : Bool}, +h2: {P.AaPerms.any(req) == True{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, Nil{})) == False{} : Bool}:
  match flags:
    case PR.AaFlags{m, fa}:
      match req:
        case P.AaPerms{rb}:
          match rb:
            case Nil{}:
              b.absurd(Bool, V.AaDecision.allowed(V.AaEval.decide(opts, PR.AaFlags{m, fa}, P.AaPerms{Nil{}}, Nil{})), False{}, h2)
            case Con{y, ys}:
              ud.mode(P.AaPerms.covers(P.AaPerms.minus(P.AaPerms.none(), P.AaPerms.none()), P.AaPerms{Con{y, ys}}), m, P.AaPerms.meets(P.AaPerms{Con{y, ys}}, P.AaPerms.none()), O.AaOptions.complain_deny(opts), V.AaEval.choose(Bool.or(fa, P.AaPerms.meets(P.AaPerms{Con{y, ys}}, P.AaPerms.none())), V.AaAudit{}, V.AaAllow{}), V.AaDeny{Bool.or(fa, Bool.not(P.AaPerms.covers(P.AaPerms.minus(P.AaPerms.none(), P.AaPerms.none()), P.AaPerms.minus(P.AaPerms{Con{y, ys}}, P.AaPerms.minus(P.AaPerms.none(), P.AaPerms.none())))))}, Equal.cong(Bool, Bool, x => Bool.not(x), Bool.or(y, P.AaBits.any(ys)), True{}, h2), h1, {==})

def Laws.unmatched_denied(opts, flags, req, h1, h2):
  ud.law(opts, flags, req, h1, h2)

def Laws.complain_decided_by_deny(opts, flags, req, gs, h):
  cd.acc(opts, flags, req, V.AaAcc.of(gs), h)

def cnd.law(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +gs: List<&2, P.AaGrant>, +h1: {O.AaOptions.complain_deny(opts) == False{} : Bool}, +h2: {PR.AaMode.is_complain(PR.AaFlags.mode(flags)) == True{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, gs)) == True{} : Bool}:
  Equal.trans(Bool, V.AaDecision.allowed(V.AaEval.decide(opts, flags, req, gs)), Bool.not(Bool.and(O.AaOptions.complain_deny(opts), P.AaPerms.meets(req, V.AaEval.denied(gs)))), True{}, Laws.complain_decided_by_deny(opts, flags, req, gs, h2), Equal.cong(Bool, Bool, x => Bool.not(Bool.and(x, P.AaPerms.meets(req, V.AaEval.denied(gs)))), O.AaOptions.complain_deny(opts), False{}, h1))

def Laws.complain_never_denies(opts, flags, req, gs, h1, h2):
  cnd.law(opts, flags, req, gs, h1, h2)

def fdw.law(+opts: O.AaOptions, +p: PR.AaProfile, +q: F.AaFileQuery, +h1: {V.AaEval.deny_applies(opts, PR.AaFlags.mode(PR.AaProfile.flags(p))) == True{} : Bool}, +h2: {P.AaPerms.meets(F.AaFileQuery.req(q), V.AaEval.denied(F.AaFileRule.grants(PR.AaRules.files(PR.AaProfile.rules(p)), q))) == True{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.file(opts, p, q)) == False{} : Bool}:
  match q:
    case F.AaFileQuery{path, owner, req}:
      Laws.deny_wins(opts, F.AaFileRule.grants(PR.AaRules.files(PR.AaProfile.rules(p)), F.AaFileQuery{path, owner, req}), PR.AaProfile.flags(p), req, h1, h2)

def Laws.file_deny_wins(opts, p, q, h1, h2):
  fdw.law(opts, p, q, h1, h2)

def fud.law(+opts: O.AaOptions, +p: PR.AaProfile, +q: F.AaFileQuery, +h1: {PR.AaMode.enforcing(PR.AaFlags.mode(PR.AaProfile.flags(p))) == True{} : Bool}, +h2: {F.AaFileRule.matching(PR.AaRules.files(PR.AaProfile.rules(p)), q) == Nil{} : List<&2, F.AaFileRule>}, +h3: {P.AaPerms.any(F.AaFileQuery.req(q)) == True{} : Bool}) -> {V.AaDecision.allowed(V.AaEval.file(opts, p, q)) == False{} : Bool}:
  match q:
    case F.AaFileQuery{path, owner, req}:
      %Equal.sym(List<&2, F.AaFileRule>, F.AaFileRule.matching(PR.AaRules.files(PR.AaProfile.rules(p)), F.AaFileQuery{path, owner, req}), Nil{}, h2) : {V.AaDecision.allowed(V.AaEval.decide(opts, PR.AaProfile.flags(p), req, F.AaFileRule.grants.of(_))) == False{} : Bool}
      Laws.unmatched_denied(opts, PR.AaProfile.flags(p), req, h1, h3)

def Laws.file_unmatched_denied(opts, p, q, h1, h2, h3):
  fud.law(opts, p, q, h1, h2, h3)

# Include: rules added twice decide as rules added once

def acc.join_empty_l(+a: V.AaAcc) -> {V.AaAcc.join(V.AaAcc.empty(), a) == a : V.AaAcc}:
  match a:
    case V.AaAcc{al, de, au, qu}:
      match al:
        case P.AaPerms{x1}:
          match de:
            case P.AaPerms{x2}:
              match au:
                case P.AaPerms{x3}:
                  match qu:
                    case P.AaPerms{x4}:
                      {==}

def acc.join_empty_r(+a: V.AaAcc) -> {V.AaAcc.join(a, V.AaAcc.empty()) == a : V.AaAcc}:
  match a:
    case V.AaAcc{al, de, au, qu}:
      %pm.none_r(al) : {V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), P.AaPerms.union(de, P.AaPerms.none()), P.AaPerms.union(au, P.AaPerms.none()), P.AaPerms.union(qu, P.AaPerms.none())} == V.AaAcc{_, de, au, qu} : V.AaAcc}
      %pm.none_r(de) : {V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), P.AaPerms.union(de, P.AaPerms.none()), P.AaPerms.union(au, P.AaPerms.none()), P.AaPerms.union(qu, P.AaPerms.none())} == V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), _, au, qu} : V.AaAcc}
      %pm.none_r(au) : {V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), P.AaPerms.union(de, P.AaPerms.none()), P.AaPerms.union(au, P.AaPerms.none()), P.AaPerms.union(qu, P.AaPerms.none())} == V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), P.AaPerms.union(de, P.AaPerms.none()), _, qu} : V.AaAcc}
      %pm.none_r(qu) : {V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), P.AaPerms.union(de, P.AaPerms.none()), P.AaPerms.union(au, P.AaPerms.none()), P.AaPerms.union(qu, P.AaPerms.none())} == V.AaAcc{P.AaPerms.union(al, P.AaPerms.none()), P.AaPerms.union(de, P.AaPerms.none()), P.AaPerms.union(au, P.AaPerms.none()), _} : V.AaAcc}
      {==}

def acc.join_assoc(+a: V.AaAcc, +b: V.AaAcc, +c: V.AaAcc) -> {V.AaAcc.join(V.AaAcc.join(a, b), c) == V.AaAcc.join(a, V.AaAcc.join(b, c)) : V.AaAcc}:
  match a:
    case V.AaAcc{al1, de1, au1, qu1}:
      match b:
        case V.AaAcc{al2, de2, au2, qu2}:
          match c:
            case V.AaAcc{al3, de3, au3, qu3}:
              %pm.assoc(al1, al2, al3) : {V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), P.AaPerms.union(P.AaPerms.union(de1, de2), de3), P.AaPerms.union(P.AaPerms.union(au1, au2), au3), P.AaPerms.union(P.AaPerms.union(qu1, qu2), qu3)} == V.AaAcc{_, P.AaPerms.union(de1, P.AaPerms.union(de2, de3)), P.AaPerms.union(au1, P.AaPerms.union(au2, au3)), P.AaPerms.union(qu1, P.AaPerms.union(qu2, qu3))} : V.AaAcc}
              %pm.assoc(de1, de2, de3) : {V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), P.AaPerms.union(P.AaPerms.union(de1, de2), de3), P.AaPerms.union(P.AaPerms.union(au1, au2), au3), P.AaPerms.union(P.AaPerms.union(qu1, qu2), qu3)} == V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), _, P.AaPerms.union(au1, P.AaPerms.union(au2, au3)), P.AaPerms.union(qu1, P.AaPerms.union(qu2, qu3))} : V.AaAcc}
              %pm.assoc(au1, au2, au3) : {V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), P.AaPerms.union(P.AaPerms.union(de1, de2), de3), P.AaPerms.union(P.AaPerms.union(au1, au2), au3), P.AaPerms.union(P.AaPerms.union(qu1, qu2), qu3)} == V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), P.AaPerms.union(P.AaPerms.union(de1, de2), de3), _, P.AaPerms.union(qu1, P.AaPerms.union(qu2, qu3))} : V.AaAcc}
              %pm.assoc(qu1, qu2, qu3) : {V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), P.AaPerms.union(P.AaPerms.union(de1, de2), de3), P.AaPerms.union(P.AaPerms.union(au1, au2), au3), P.AaPerms.union(P.AaPerms.union(qu1, qu2), qu3)} == V.AaAcc{P.AaPerms.union(P.AaPerms.union(al1, al2), al3), P.AaPerms.union(P.AaPerms.union(de1, de2), de3), P.AaPerms.union(P.AaPerms.union(au1, au2), au3), _} : V.AaAcc}
              {==}

def acc.join_idem(+a: V.AaAcc) -> {V.AaAcc.join(a, a) == a : V.AaAcc}:
  match a:
    case V.AaAcc{al, de, au, qu}:
      %pm.idem(al) : {V.AaAcc{P.AaPerms.union(al, al), P.AaPerms.union(de, de), P.AaPerms.union(au, au), P.AaPerms.union(qu, qu)} == V.AaAcc{_, de, au, qu} : V.AaAcc}
      %pm.idem(de) : {V.AaAcc{P.AaPerms.union(al, al), P.AaPerms.union(de, de), P.AaPerms.union(au, au), P.AaPerms.union(qu, qu)} == V.AaAcc{P.AaPerms.union(al, al), _, au, qu} : V.AaAcc}
      %pm.idem(au) : {V.AaAcc{P.AaPerms.union(al, al), P.AaPerms.union(de, de), P.AaPerms.union(au, au), P.AaPerms.union(qu, qu)} == V.AaAcc{P.AaPerms.union(al, al), P.AaPerms.union(de, de), _, qu} : V.AaAcc}
      %pm.idem(qu) : {V.AaAcc{P.AaPerms.union(al, al), P.AaPerms.union(de, de), P.AaPerms.union(au, au), P.AaPerms.union(qu, qu)} == V.AaAcc{P.AaPerms.union(al, al), P.AaPerms.union(de, de), P.AaPerms.union(au, au), _} : V.AaAcc}
      {==}

def from_join(+ys: List<&2, P.AaGrant>, +acc: V.AaAcc) -> {V.AaAcc.from(ys, acc) == V.AaAcc.join(acc, V.AaAcc.from(ys, V.AaAcc.empty())) : V.AaAcc}:
  match ys:
    case Nil{}:
      Equal.sym(V.AaAcc, V.AaAcc.join(acc, V.AaAcc.empty()), acc, acc.join_empty_r(acc))
    case Con{g, t}:
      Equal.trans(V.AaAcc, V.AaAcc.from(t, V.AaAcc.join(acc, V.AaAcc.single(g))), V.AaAcc.join(V.AaAcc.join(acc, V.AaAcc.single(g)), V.AaAcc.from(t, V.AaAcc.empty())), V.AaAcc.join(acc, V.AaAcc.from(t, V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)))), from_join(t, V.AaAcc.join(acc, V.AaAcc.single(g))), Equal.trans(V.AaAcc, V.AaAcc.join(V.AaAcc.join(acc, V.AaAcc.single(g)), V.AaAcc.from(t, V.AaAcc.empty())), V.AaAcc.join(acc, V.AaAcc.join(V.AaAcc.single(g), V.AaAcc.from(t, V.AaAcc.empty()))), V.AaAcc.join(acc, V.AaAcc.from(t, V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)))), acc.join_assoc(acc, V.AaAcc.single(g), V.AaAcc.from(t, V.AaAcc.empty())), Equal.sym(V.AaAcc, V.AaAcc.join(acc, V.AaAcc.from(t, V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)))), V.AaAcc.join(acc, V.AaAcc.join(V.AaAcc.single(g), V.AaAcc.from(t, V.AaAcc.empty()))), Equal.trans(V.AaAcc, V.AaAcc.join(acc, V.AaAcc.from(t, V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)))), V.AaAcc.join(acc, V.AaAcc.join(V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)), V.AaAcc.from(t, V.AaAcc.empty()))), V.AaAcc.join(acc, V.AaAcc.join(V.AaAcc.single(g), V.AaAcc.from(t, V.AaAcc.empty()))), Equal.cong(V.AaAcc, V.AaAcc, x => V.AaAcc.join(acc, x), V.AaAcc.from(t, V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g))), V.AaAcc.join(V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)), V.AaAcc.from(t, V.AaAcc.empty())), from_join(t, V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)))), Equal.cong(V.AaAcc, V.AaAcc, x => V.AaAcc.join(acc, V.AaAcc.join(x, V.AaAcc.from(t, V.AaAcc.empty()))), V.AaAcc.join(V.AaAcc.empty(), V.AaAcc.single(g)), V.AaAcc.single(g), acc.join_empty_l(V.AaAcc.single(g)))))))

def from_idem(+ys: List<&2, P.AaGrant>, +acc: V.AaAcc) -> {V.AaAcc.from(ys, V.AaAcc.from(ys, acc)) == V.AaAcc.from(ys, acc) : V.AaAcc}:
  Equal.trans(V.AaAcc, V.AaAcc.from(ys, V.AaAcc.from(ys, acc)), V.AaAcc.join(V.AaAcc.from(ys, acc), V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, acc), from_join(ys, V.AaAcc.from(ys, acc)), Equal.trans(V.AaAcc, V.AaAcc.join(V.AaAcc.from(ys, acc), V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.join(V.AaAcc.join(acc, V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, acc), Equal.cong(V.AaAcc, V.AaAcc, x => V.AaAcc.join(x, V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, acc), V.AaAcc.join(acc, V.AaAcc.from(ys, V.AaAcc.empty())), from_join(ys, acc)), Equal.trans(V.AaAcc, V.AaAcc.join(V.AaAcc.join(acc, V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.join(acc, V.AaAcc.join(V.AaAcc.from(ys, V.AaAcc.empty()), V.AaAcc.from(ys, V.AaAcc.empty()))), V.AaAcc.from(ys, acc), acc.join_assoc(acc, V.AaAcc.from(ys, V.AaAcc.empty()), V.AaAcc.from(ys, V.AaAcc.empty())), Equal.trans(V.AaAcc, V.AaAcc.join(acc, V.AaAcc.join(V.AaAcc.from(ys, V.AaAcc.empty()), V.AaAcc.from(ys, V.AaAcc.empty()))), V.AaAcc.join(acc, V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, acc), Equal.cong(V.AaAcc, V.AaAcc, x => V.AaAcc.join(acc, x), V.AaAcc.join(V.AaAcc.from(ys, V.AaAcc.empty()), V.AaAcc.from(ys, V.AaAcc.empty())), V.AaAcc.from(ys, V.AaAcc.empty()), acc.join_idem(V.AaAcc.from(ys, V.AaAcc.empty()))), Equal.sym(V.AaAcc, V.AaAcc.from(ys, acc), V.AaAcc.join(acc, V.AaAcc.from(ys, V.AaAcc.empty())), from_join(ys, acc))))))

def from_app(+xs: List<&2, P.AaGrant>, +ys: List<&2, P.AaGrant>, +acc: V.AaAcc) -> {V.AaAcc.from(P.AaGrant.append(xs, ys), acc) == V.AaAcc.from(ys, V.AaAcc.from(xs, acc)) : V.AaAcc}:
  match xs:
    case Nil{}:
      {==}
    case Con{g, t}:
      from_app(t, ys, V.AaAcc.add(acc, g))

def inc.acc(+g0: List<&2, P.AaGrant>, +g1: List<&2, P.AaGrant>) -> {V.AaAcc.of(P.AaGrant.append(P.AaGrant.append(g0, g1), g1)) == V.AaAcc.of(P.AaGrant.append(g0, g1)) : V.AaAcc}:
  Equal.trans(V.AaAcc, V.AaAcc.from(P.AaGrant.append(P.AaGrant.append(g0, g1), g1), V.AaAcc.empty()), V.AaAcc.from(g1, V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty())), V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty()), from_app(P.AaGrant.append(g0, g1), g1, V.AaAcc.empty()), Equal.trans(V.AaAcc, V.AaAcc.from(g1, V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty())), V.AaAcc.from(g1, V.AaAcc.from(g1, V.AaAcc.from(g0, V.AaAcc.empty()))), V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty()), Equal.cong(V.AaAcc, V.AaAcc, x => V.AaAcc.from(g1, x), V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty()), V.AaAcc.from(g1, V.AaAcc.from(g0, V.AaAcc.empty())), from_app(g0, g1, V.AaAcc.empty())), Equal.trans(V.AaAcc, V.AaAcc.from(g1, V.AaAcc.from(g1, V.AaAcc.from(g0, V.AaAcc.empty()))), V.AaAcc.from(g1, V.AaAcc.from(g0, V.AaAcc.empty())), V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty()), from_idem(g1, V.AaAcc.from(g0, V.AaAcc.empty())), Equal.sym(V.AaAcc, V.AaAcc.from(P.AaGrant.append(g0, g1), V.AaAcc.empty()), V.AaAcc.from(g1, V.AaAcc.from(g0, V.AaAcc.empty())), from_app(g0, g1, V.AaAcc.empty())))))

def inc.decide(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +g0: List<&2, P.AaGrant>, +g1: List<&2, P.AaGrant>) -> {V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(g0, g1), g1)) == V.AaEval.decide(opts, flags, req, P.AaGrant.append(g0, g1)) : V.AaDecision}:
  Equal.cong(V.AaAcc, V.AaDecision, a => V.AaEval.decide.acc(opts, flags, req, a), V.AaAcc.of(P.AaGrant.append(P.AaGrant.append(g0, g1), g1)), V.AaAcc.of(P.AaGrant.append(g0, g1)), inc.acc(g0, g1))

# file rules

def file.mgo(+hit: Bool, +r: F.AaFileRule, +a: List<&2, F.AaFileRule>, +b: List<&2, F.AaFileRule>) -> {F.AaFileRule.matching.go(hit, r, F.AaFileRule.append(a, b)) == F.AaFileRule.append(F.AaFileRule.matching.go(hit, r, a), b) : List<&2, F.AaFileRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def file.match_app(+xs: List<&2, F.AaFileRule>, +ys: List<&2, F.AaFileRule>, +q: F.AaFileQuery) -> {F.AaFileRule.matching(F.AaFileRule.append(xs, ys), q) == F.AaFileRule.append(F.AaFileRule.matching(xs, q), F.AaFileRule.matching(ys, q)) : List<&2, F.AaFileRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, F.AaFileRule>, F.AaFileRule.matching.go(F.AaFileRule.matches(r, q), r, F.AaFileRule.matching(F.AaFileRule.append(t, ys), q)), F.AaFileRule.matching.go(F.AaFileRule.matches(r, q), r, F.AaFileRule.append(F.AaFileRule.matching(t, q), F.AaFileRule.matching(ys, q))), F.AaFileRule.append(F.AaFileRule.matching.go(F.AaFileRule.matches(r, q), r, F.AaFileRule.matching(t, q)), F.AaFileRule.matching(ys, q)), Equal.cong(List<&2, F.AaFileRule>, List<&2, F.AaFileRule>, x => F.AaFileRule.matching.go(F.AaFileRule.matches(r, q), r, x), F.AaFileRule.matching(F.AaFileRule.append(t, ys), q), F.AaFileRule.append(F.AaFileRule.matching(t, q), F.AaFileRule.matching(ys, q)), file.match_app(t, ys, q)), file.mgo(F.AaFileRule.matches(r, q), r, F.AaFileRule.matching(t, q), F.AaFileRule.matching(ys, q)))

def file.gof_app(+xs: List<&2, F.AaFileRule>, +ys: List<&2, F.AaFileRule>) -> {F.AaFileRule.grants.of(F.AaFileRule.append(xs, ys)) == P.AaGrant.append(F.AaFileRule.grants.of(xs), F.AaFileRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{F.AaFileRule.grant(r), x}, F.AaFileRule.grants.of(F.AaFileRule.append(t, ys)), P.AaGrant.append(F.AaFileRule.grants.of(t), F.AaFileRule.grants.of(ys)), file.gof_app(t, ys))

def file.gapp(+xs: List<&2, F.AaFileRule>, +ys: List<&2, F.AaFileRule>, +q: F.AaFileQuery) -> {F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q) == P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, F.AaFileRule.grants.of(F.AaFileRule.matching(F.AaFileRule.append(xs, ys), q)), F.AaFileRule.grants.of(F.AaFileRule.append(F.AaFileRule.matching(xs, q), F.AaFileRule.matching(ys, q))), P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), Equal.cong(List<&2, F.AaFileRule>, List<&2, P.AaGrant>, x => F.AaFileRule.grants.of(x), F.AaFileRule.matching(F.AaFileRule.append(xs, ys), q), F.AaFileRule.append(F.AaFileRule.matching(xs, q), F.AaFileRule.matching(ys, q)), file.match_app(xs, ys, q)), file.gof_app(F.AaFileRule.matching(xs, q), F.AaFileRule.matching(ys, q)))

def file.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, F.AaFileRule>, +ys: List<&2, F.AaFileRule>, +q: F.AaFileQuery) -> {V.AaEval.decide(opts, flags, req, F.AaFileRule.grants(F.AaFileRule.append(F.AaFileRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, F.AaFileRule.grants(F.AaFileRule.append(F.AaFileRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), F.AaFileRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), F.AaFileRule.grants(F.AaFileRule.append(F.AaFileRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), F.AaFileRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, F.AaFileRule.grants(F.AaFileRule.append(F.AaFileRule.append(xs, ys), ys), q), P.AaGrant.append(F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q), F.AaFileRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), F.AaFileRule.grants(ys, q)), file.gapp(F.AaFileRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, F.AaFileRule.grants(ys, q)), F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q), P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), file.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), F.AaFileRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q)), inc.decide(opts, flags, req, F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, F.AaFileRule.grants(F.AaFileRule.append(xs, ys), q), P.AaGrant.append(F.AaFileRule.grants(xs, q), F.AaFileRule.grants(ys, q)), file.gapp(xs, ys, q)))))

def file.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: F.AaFileQuery) -> {V.AaEval.file(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.file(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              match q:
                case F.AaFileQuery{path, owner, req}:
                  file.inc(opts, f, req, f0, f1, F.AaFileQuery{path, owner, req})

def Laws.include_idempotent_file(opts, p, r, q):
  file.law(opts, p, r, q)

# capability rules

def cap.mgo(+hit: Bool, +r: RC.AaCapRule, +a: List<&2, RC.AaCapRule>, +b: List<&2, RC.AaCapRule>) -> {RC.AaCapRule.matching.go(hit, r, RC.AaCapRule.append(a, b)) == RC.AaCapRule.append(RC.AaCapRule.matching.go(hit, r, a), b) : List<&2, RC.AaCapRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def cap.match_app(+xs: List<&2, RC.AaCapRule>, +ys: List<&2, RC.AaCapRule>, +q: RC.AaCapQuery) -> {RC.AaCapRule.matching(RC.AaCapRule.append(xs, ys), q) == RC.AaCapRule.append(RC.AaCapRule.matching(xs, q), RC.AaCapRule.matching(ys, q)) : List<&2, RC.AaCapRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RC.AaCapRule>, RC.AaCapRule.matching.go(RC.AaCapRule.matches(r, q), r, RC.AaCapRule.matching(RC.AaCapRule.append(t, ys), q)), RC.AaCapRule.matching.go(RC.AaCapRule.matches(r, q), r, RC.AaCapRule.append(RC.AaCapRule.matching(t, q), RC.AaCapRule.matching(ys, q))), RC.AaCapRule.append(RC.AaCapRule.matching.go(RC.AaCapRule.matches(r, q), r, RC.AaCapRule.matching(t, q)), RC.AaCapRule.matching(ys, q)), Equal.cong(List<&2, RC.AaCapRule>, List<&2, RC.AaCapRule>, x => RC.AaCapRule.matching.go(RC.AaCapRule.matches(r, q), r, x), RC.AaCapRule.matching(RC.AaCapRule.append(t, ys), q), RC.AaCapRule.append(RC.AaCapRule.matching(t, q), RC.AaCapRule.matching(ys, q)), cap.match_app(t, ys, q)), cap.mgo(RC.AaCapRule.matches(r, q), r, RC.AaCapRule.matching(t, q), RC.AaCapRule.matching(ys, q)))

def cap.gof_app(+xs: List<&2, RC.AaCapRule>, +ys: List<&2, RC.AaCapRule>) -> {RC.AaCapRule.grants.of(RC.AaCapRule.append(xs, ys)) == P.AaGrant.append(RC.AaCapRule.grants.of(xs), RC.AaCapRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RC.AaCapRule{qu, ks}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), x}, RC.AaCapRule.grants.of(RC.AaCapRule.append(t, ys)), P.AaGrant.append(RC.AaCapRule.grants.of(t), RC.AaCapRule.grants.of(ys)), cap.gof_app(t, ys))

def cap.gapp(+xs: List<&2, RC.AaCapRule>, +ys: List<&2, RC.AaCapRule>, +q: RC.AaCapQuery) -> {RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q) == P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RC.AaCapRule.grants.of(RC.AaCapRule.matching(RC.AaCapRule.append(xs, ys), q)), RC.AaCapRule.grants.of(RC.AaCapRule.append(RC.AaCapRule.matching(xs, q), RC.AaCapRule.matching(ys, q))), P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), Equal.cong(List<&2, RC.AaCapRule>, List<&2, P.AaGrant>, x => RC.AaCapRule.grants.of(x), RC.AaCapRule.matching(RC.AaCapRule.append(xs, ys), q), RC.AaCapRule.append(RC.AaCapRule.matching(xs, q), RC.AaCapRule.matching(ys, q)), cap.match_app(xs, ys, q)), cap.gof_app(RC.AaCapRule.matching(xs, q), RC.AaCapRule.matching(ys, q)))

def cap.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RC.AaCapRule>, +ys: List<&2, RC.AaCapRule>, +q: RC.AaCapQuery) -> {V.AaEval.decide(opts, flags, req, RC.AaCapRule.grants(RC.AaCapRule.append(RC.AaCapRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RC.AaCapRule.grants(RC.AaCapRule.append(RC.AaCapRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), RC.AaCapRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RC.AaCapRule.grants(RC.AaCapRule.append(RC.AaCapRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), RC.AaCapRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RC.AaCapRule.grants(RC.AaCapRule.append(RC.AaCapRule.append(xs, ys), ys), q), P.AaGrant.append(RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q), RC.AaCapRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), RC.AaCapRule.grants(ys, q)), cap.gapp(RC.AaCapRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RC.AaCapRule.grants(ys, q)), RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q), P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), cap.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), RC.AaCapRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q)), inc.decide(opts, flags, req, RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RC.AaCapRule.grants(RC.AaCapRule.append(xs, ys), q), P.AaGrant.append(RC.AaCapRule.grants(xs, q), RC.AaCapRule.grants(ys, q)), cap.gapp(xs, ys, q)))))

def cap.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RC.AaCapQuery) -> {V.AaEval.capability(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.capability(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              cap.inc(opts, f, RC.AaCapQuery.req(), c0, c1, q)

def Laws.include_idempotent_capability(opts, p, r, q):
  cap.law(opts, p, r, q)

# network rules

def net.mgo(+hit: Bool, +r: RN.AaNetRule, +a: List<&2, RN.AaNetRule>, +b: List<&2, RN.AaNetRule>) -> {RN.AaNetRule.matching.go(hit, r, RN.AaNetRule.append(a, b)) == RN.AaNetRule.append(RN.AaNetRule.matching.go(hit, r, a), b) : List<&2, RN.AaNetRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def net.match_app(+xs: List<&2, RN.AaNetRule>, +ys: List<&2, RN.AaNetRule>, +q: RN.AaNetQuery) -> {RN.AaNetRule.matching(RN.AaNetRule.append(xs, ys), q) == RN.AaNetRule.append(RN.AaNetRule.matching(xs, q), RN.AaNetRule.matching(ys, q)) : List<&2, RN.AaNetRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RN.AaNetRule>, RN.AaNetRule.matching.go(RN.AaNetRule.matches(r, q), r, RN.AaNetRule.matching(RN.AaNetRule.append(t, ys), q)), RN.AaNetRule.matching.go(RN.AaNetRule.matches(r, q), r, RN.AaNetRule.append(RN.AaNetRule.matching(t, q), RN.AaNetRule.matching(ys, q))), RN.AaNetRule.append(RN.AaNetRule.matching.go(RN.AaNetRule.matches(r, q), r, RN.AaNetRule.matching(t, q)), RN.AaNetRule.matching(ys, q)), Equal.cong(List<&2, RN.AaNetRule>, List<&2, RN.AaNetRule>, x => RN.AaNetRule.matching.go(RN.AaNetRule.matches(r, q), r, x), RN.AaNetRule.matching(RN.AaNetRule.append(t, ys), q), RN.AaNetRule.append(RN.AaNetRule.matching(t, q), RN.AaNetRule.matching(ys, q)), net.match_app(t, ys, q)), net.mgo(RN.AaNetRule.matches(r, q), r, RN.AaNetRule.matching(t, q), RN.AaNetRule.matching(ys, q)))

def net.gof_app(+xs: List<&2, RN.AaNetRule>, +ys: List<&2, RN.AaNetRule>) -> {RN.AaNetRule.grants.of(RN.AaNetRule.append(xs, ys)) == P.AaGrant.append(RN.AaNetRule.grants.of(xs), RN.AaNetRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RN.AaNetRule{qu, d, ty, pr}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), x}, RN.AaNetRule.grants.of(RN.AaNetRule.append(t, ys)), P.AaGrant.append(RN.AaNetRule.grants.of(t), RN.AaNetRule.grants.of(ys)), net.gof_app(t, ys))

def net.gapp(+xs: List<&2, RN.AaNetRule>, +ys: List<&2, RN.AaNetRule>, +q: RN.AaNetQuery) -> {RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q) == P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RN.AaNetRule.grants.of(RN.AaNetRule.matching(RN.AaNetRule.append(xs, ys), q)), RN.AaNetRule.grants.of(RN.AaNetRule.append(RN.AaNetRule.matching(xs, q), RN.AaNetRule.matching(ys, q))), P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), Equal.cong(List<&2, RN.AaNetRule>, List<&2, P.AaGrant>, x => RN.AaNetRule.grants.of(x), RN.AaNetRule.matching(RN.AaNetRule.append(xs, ys), q), RN.AaNetRule.append(RN.AaNetRule.matching(xs, q), RN.AaNetRule.matching(ys, q)), net.match_app(xs, ys, q)), net.gof_app(RN.AaNetRule.matching(xs, q), RN.AaNetRule.matching(ys, q)))

def net.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RN.AaNetRule>, +ys: List<&2, RN.AaNetRule>, +q: RN.AaNetQuery) -> {V.AaEval.decide(opts, flags, req, RN.AaNetRule.grants(RN.AaNetRule.append(RN.AaNetRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RN.AaNetRule.grants(RN.AaNetRule.append(RN.AaNetRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), RN.AaNetRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RN.AaNetRule.grants(RN.AaNetRule.append(RN.AaNetRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), RN.AaNetRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RN.AaNetRule.grants(RN.AaNetRule.append(RN.AaNetRule.append(xs, ys), ys), q), P.AaGrant.append(RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q), RN.AaNetRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), RN.AaNetRule.grants(ys, q)), net.gapp(RN.AaNetRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RN.AaNetRule.grants(ys, q)), RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q), P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), net.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), RN.AaNetRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q)), inc.decide(opts, flags, req, RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RN.AaNetRule.grants(RN.AaNetRule.append(xs, ys), q), P.AaGrant.append(RN.AaNetRule.grants(xs, q), RN.AaNetRule.grants(ys, q)), net.gapp(xs, ys, q)))))

def net.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RN.AaNetQuery) -> {V.AaEval.network(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.network(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              net.inc(opts, f, RN.AaNetQuery.req(), n0, n1, q)

def Laws.include_idempotent_network(opts, p, r, q):
  net.law(opts, p, r, q)

# signal rules

def sig.mgo(+hit: Bool, +r: RS.AaSignalRule, +a: List<&2, RS.AaSignalRule>, +b: List<&2, RS.AaSignalRule>) -> {RS.AaSignalRule.matching.go(hit, r, RS.AaSignalRule.append(a, b)) == RS.AaSignalRule.append(RS.AaSignalRule.matching.go(hit, r, a), b) : List<&2, RS.AaSignalRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def sig.match_app(+xs: List<&2, RS.AaSignalRule>, +ys: List<&2, RS.AaSignalRule>, +q: RS.AaSignalQuery) -> {RS.AaSignalRule.matching(RS.AaSignalRule.append(xs, ys), q) == RS.AaSignalRule.append(RS.AaSignalRule.matching(xs, q), RS.AaSignalRule.matching(ys, q)) : List<&2, RS.AaSignalRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RS.AaSignalRule>, RS.AaSignalRule.matching.go(RS.AaSignalRule.matches(r, q), r, RS.AaSignalRule.matching(RS.AaSignalRule.append(t, ys), q)), RS.AaSignalRule.matching.go(RS.AaSignalRule.matches(r, q), r, RS.AaSignalRule.append(RS.AaSignalRule.matching(t, q), RS.AaSignalRule.matching(ys, q))), RS.AaSignalRule.append(RS.AaSignalRule.matching.go(RS.AaSignalRule.matches(r, q), r, RS.AaSignalRule.matching(t, q)), RS.AaSignalRule.matching(ys, q)), Equal.cong(List<&2, RS.AaSignalRule>, List<&2, RS.AaSignalRule>, x => RS.AaSignalRule.matching.go(RS.AaSignalRule.matches(r, q), r, x), RS.AaSignalRule.matching(RS.AaSignalRule.append(t, ys), q), RS.AaSignalRule.append(RS.AaSignalRule.matching(t, q), RS.AaSignalRule.matching(ys, q)), sig.match_app(t, ys, q)), sig.mgo(RS.AaSignalRule.matches(r, q), r, RS.AaSignalRule.matching(t, q), RS.AaSignalRule.matching(ys, q)))

def sig.gof_app(+xs: List<&2, RS.AaSignalRule>, +ys: List<&2, RS.AaSignalRule>) -> {RS.AaSignalRule.grants.of(RS.AaSignalRule.append(xs, ys)) == P.AaGrant.append(RS.AaSignalRule.grants.of(xs), RS.AaSignalRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RS.AaSignalRule{qu, p, s, pe}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, p), x}, RS.AaSignalRule.grants.of(RS.AaSignalRule.append(t, ys)), P.AaGrant.append(RS.AaSignalRule.grants.of(t), RS.AaSignalRule.grants.of(ys)), sig.gof_app(t, ys))

def sig.gapp(+xs: List<&2, RS.AaSignalRule>, +ys: List<&2, RS.AaSignalRule>, +q: RS.AaSignalQuery) -> {RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q) == P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RS.AaSignalRule.grants.of(RS.AaSignalRule.matching(RS.AaSignalRule.append(xs, ys), q)), RS.AaSignalRule.grants.of(RS.AaSignalRule.append(RS.AaSignalRule.matching(xs, q), RS.AaSignalRule.matching(ys, q))), P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), Equal.cong(List<&2, RS.AaSignalRule>, List<&2, P.AaGrant>, x => RS.AaSignalRule.grants.of(x), RS.AaSignalRule.matching(RS.AaSignalRule.append(xs, ys), q), RS.AaSignalRule.append(RS.AaSignalRule.matching(xs, q), RS.AaSignalRule.matching(ys, q)), sig.match_app(xs, ys, q)), sig.gof_app(RS.AaSignalRule.matching(xs, q), RS.AaSignalRule.matching(ys, q)))

def sig.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RS.AaSignalRule>, +ys: List<&2, RS.AaSignalRule>, +q: RS.AaSignalQuery) -> {V.AaEval.decide(opts, flags, req, RS.AaSignalRule.grants(RS.AaSignalRule.append(RS.AaSignalRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RS.AaSignalRule.grants(RS.AaSignalRule.append(RS.AaSignalRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), RS.AaSignalRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RS.AaSignalRule.grants(RS.AaSignalRule.append(RS.AaSignalRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), RS.AaSignalRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RS.AaSignalRule.grants(RS.AaSignalRule.append(RS.AaSignalRule.append(xs, ys), ys), q), P.AaGrant.append(RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q), RS.AaSignalRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), RS.AaSignalRule.grants(ys, q)), sig.gapp(RS.AaSignalRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RS.AaSignalRule.grants(ys, q)), RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q), P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), sig.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), RS.AaSignalRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q)), inc.decide(opts, flags, req, RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RS.AaSignalRule.grants(RS.AaSignalRule.append(xs, ys), q), P.AaGrant.append(RS.AaSignalRule.grants(xs, q), RS.AaSignalRule.grants(ys, q)), sig.gapp(xs, ys, q)))))

def sig.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RS.AaSignalQuery) -> {V.AaEval.signal(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.signal(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              sig.inc(opts, f, RS.AaSignalQuery.req(q), s0, s1, q)

def Laws.include_idempotent_signal(opts, p, r, q):
  sig.law(opts, p, r, q)

# ptrace rules

def ptr.mgo(+hit: Bool, +r: RP.AaPtraceRule, +a: List<&2, RP.AaPtraceRule>, +b: List<&2, RP.AaPtraceRule>) -> {RP.AaPtraceRule.matching.go(hit, r, RP.AaPtraceRule.append(a, b)) == RP.AaPtraceRule.append(RP.AaPtraceRule.matching.go(hit, r, a), b) : List<&2, RP.AaPtraceRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ptr.match_app(+xs: List<&2, RP.AaPtraceRule>, +ys: List<&2, RP.AaPtraceRule>, +q: RP.AaPtraceQuery) -> {RP.AaPtraceRule.matching(RP.AaPtraceRule.append(xs, ys), q) == RP.AaPtraceRule.append(RP.AaPtraceRule.matching(xs, q), RP.AaPtraceRule.matching(ys, q)) : List<&2, RP.AaPtraceRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RP.AaPtraceRule>, RP.AaPtraceRule.matching.go(RP.AaPtraceRule.matches(r, q), r, RP.AaPtraceRule.matching(RP.AaPtraceRule.append(t, ys), q)), RP.AaPtraceRule.matching.go(RP.AaPtraceRule.matches(r, q), r, RP.AaPtraceRule.append(RP.AaPtraceRule.matching(t, q), RP.AaPtraceRule.matching(ys, q))), RP.AaPtraceRule.append(RP.AaPtraceRule.matching.go(RP.AaPtraceRule.matches(r, q), r, RP.AaPtraceRule.matching(t, q)), RP.AaPtraceRule.matching(ys, q)), Equal.cong(List<&2, RP.AaPtraceRule>, List<&2, RP.AaPtraceRule>, x => RP.AaPtraceRule.matching.go(RP.AaPtraceRule.matches(r, q), r, x), RP.AaPtraceRule.matching(RP.AaPtraceRule.append(t, ys), q), RP.AaPtraceRule.append(RP.AaPtraceRule.matching(t, q), RP.AaPtraceRule.matching(ys, q)), ptr.match_app(t, ys, q)), ptr.mgo(RP.AaPtraceRule.matches(r, q), r, RP.AaPtraceRule.matching(t, q), RP.AaPtraceRule.matching(ys, q)))

def ptr.gof_app(+xs: List<&2, RP.AaPtraceRule>, +ys: List<&2, RP.AaPtraceRule>) -> {RP.AaPtraceRule.grants.of(RP.AaPtraceRule.append(xs, ys)) == P.AaGrant.append(RP.AaPtraceRule.grants.of(xs), RP.AaPtraceRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RP.AaPtraceRule{qu, p, pe}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, p), x}, RP.AaPtraceRule.grants.of(RP.AaPtraceRule.append(t, ys)), P.AaGrant.append(RP.AaPtraceRule.grants.of(t), RP.AaPtraceRule.grants.of(ys)), ptr.gof_app(t, ys))

def ptr.gapp(+xs: List<&2, RP.AaPtraceRule>, +ys: List<&2, RP.AaPtraceRule>, +q: RP.AaPtraceQuery) -> {RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q) == P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RP.AaPtraceRule.grants.of(RP.AaPtraceRule.matching(RP.AaPtraceRule.append(xs, ys), q)), RP.AaPtraceRule.grants.of(RP.AaPtraceRule.append(RP.AaPtraceRule.matching(xs, q), RP.AaPtraceRule.matching(ys, q))), P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), Equal.cong(List<&2, RP.AaPtraceRule>, List<&2, P.AaGrant>, x => RP.AaPtraceRule.grants.of(x), RP.AaPtraceRule.matching(RP.AaPtraceRule.append(xs, ys), q), RP.AaPtraceRule.append(RP.AaPtraceRule.matching(xs, q), RP.AaPtraceRule.matching(ys, q)), ptr.match_app(xs, ys, q)), ptr.gof_app(RP.AaPtraceRule.matching(xs, q), RP.AaPtraceRule.matching(ys, q)))

def ptr.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RP.AaPtraceRule>, +ys: List<&2, RP.AaPtraceRule>, +q: RP.AaPtraceQuery) -> {V.AaEval.decide(opts, flags, req, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(RP.AaPtraceRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(RP.AaPtraceRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), RP.AaPtraceRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RP.AaPtraceRule.grants(RP.AaPtraceRule.append(RP.AaPtraceRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), RP.AaPtraceRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(RP.AaPtraceRule.append(xs, ys), ys), q), P.AaGrant.append(RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q), RP.AaPtraceRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), RP.AaPtraceRule.grants(ys, q)), ptr.gapp(RP.AaPtraceRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RP.AaPtraceRule.grants(ys, q)), RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q), P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), ptr.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), RP.AaPtraceRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q)), inc.decide(opts, flags, req, RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RP.AaPtraceRule.grants(RP.AaPtraceRule.append(xs, ys), q), P.AaGrant.append(RP.AaPtraceRule.grants(xs, q), RP.AaPtraceRule.grants(ys, q)), ptr.gapp(xs, ys, q)))))

def ptr.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RP.AaPtraceQuery) -> {V.AaEval.ptrace(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.ptrace(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              ptr.inc(opts, f, RP.AaPtraceQuery.req(q), p0, p1, q)

def Laws.include_idempotent_ptrace(opts, p, r, q):
  ptr.law(opts, p, r, q)

# mount rules

def mnt.mgo(+hit: Bool, +r: RM.AaMountRule, +a: List<&2, RM.AaMountRule>, +b: List<&2, RM.AaMountRule>) -> {RM.AaMountRule.matching.go(hit, r, RM.AaMountRule.append(a, b)) == RM.AaMountRule.append(RM.AaMountRule.matching.go(hit, r, a), b) : List<&2, RM.AaMountRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def mnt.match_app(+xs: List<&2, RM.AaMountRule>, +ys: List<&2, RM.AaMountRule>, +q: RM.AaMountQuery) -> {RM.AaMountRule.matching(RM.AaMountRule.append(xs, ys), q) == RM.AaMountRule.append(RM.AaMountRule.matching(xs, q), RM.AaMountRule.matching(ys, q)) : List<&2, RM.AaMountRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RM.AaMountRule>, RM.AaMountRule.matching.go(RM.AaMountRule.matches(r, q), r, RM.AaMountRule.matching(RM.AaMountRule.append(t, ys), q)), RM.AaMountRule.matching.go(RM.AaMountRule.matches(r, q), r, RM.AaMountRule.append(RM.AaMountRule.matching(t, q), RM.AaMountRule.matching(ys, q))), RM.AaMountRule.append(RM.AaMountRule.matching.go(RM.AaMountRule.matches(r, q), r, RM.AaMountRule.matching(t, q)), RM.AaMountRule.matching(ys, q)), Equal.cong(List<&2, RM.AaMountRule>, List<&2, RM.AaMountRule>, x => RM.AaMountRule.matching.go(RM.AaMountRule.matches(r, q), r, x), RM.AaMountRule.matching(RM.AaMountRule.append(t, ys), q), RM.AaMountRule.append(RM.AaMountRule.matching(t, q), RM.AaMountRule.matching(ys, q)), mnt.match_app(t, ys, q)), mnt.mgo(RM.AaMountRule.matches(r, q), r, RM.AaMountRule.matching(t, q), RM.AaMountRule.matching(ys, q)))

def mnt.gof_app(+xs: List<&2, RM.AaMountRule>, +ys: List<&2, RM.AaMountRule>) -> {RM.AaMountRule.grants.of(RM.AaMountRule.append(xs, ys)) == P.AaGrant.append(RM.AaMountRule.grants.of(xs), RM.AaMountRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RM.AaMountRule{qu, op, fs, os, so, tg}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), x}, RM.AaMountRule.grants.of(RM.AaMountRule.append(t, ys)), P.AaGrant.append(RM.AaMountRule.grants.of(t), RM.AaMountRule.grants.of(ys)), mnt.gof_app(t, ys))

def mnt.gapp(+xs: List<&2, RM.AaMountRule>, +ys: List<&2, RM.AaMountRule>, +q: RM.AaMountQuery) -> {RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q) == P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RM.AaMountRule.grants.of(RM.AaMountRule.matching(RM.AaMountRule.append(xs, ys), q)), RM.AaMountRule.grants.of(RM.AaMountRule.append(RM.AaMountRule.matching(xs, q), RM.AaMountRule.matching(ys, q))), P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), Equal.cong(List<&2, RM.AaMountRule>, List<&2, P.AaGrant>, x => RM.AaMountRule.grants.of(x), RM.AaMountRule.matching(RM.AaMountRule.append(xs, ys), q), RM.AaMountRule.append(RM.AaMountRule.matching(xs, q), RM.AaMountRule.matching(ys, q)), mnt.match_app(xs, ys, q)), mnt.gof_app(RM.AaMountRule.matching(xs, q), RM.AaMountRule.matching(ys, q)))

def mnt.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RM.AaMountRule>, +ys: List<&2, RM.AaMountRule>, +q: RM.AaMountQuery) -> {V.AaEval.decide(opts, flags, req, RM.AaMountRule.grants(RM.AaMountRule.append(RM.AaMountRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RM.AaMountRule.grants(RM.AaMountRule.append(RM.AaMountRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), RM.AaMountRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RM.AaMountRule.grants(RM.AaMountRule.append(RM.AaMountRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), RM.AaMountRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RM.AaMountRule.grants(RM.AaMountRule.append(RM.AaMountRule.append(xs, ys), ys), q), P.AaGrant.append(RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q), RM.AaMountRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), RM.AaMountRule.grants(ys, q)), mnt.gapp(RM.AaMountRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RM.AaMountRule.grants(ys, q)), RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q), P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), mnt.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), RM.AaMountRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q)), inc.decide(opts, flags, req, RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RM.AaMountRule.grants(RM.AaMountRule.append(xs, ys), q), P.AaGrant.append(RM.AaMountRule.grants(xs, q), RM.AaMountRule.grants(ys, q)), mnt.gapp(xs, ys, q)))))

def mnt.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RM.AaMountQuery) -> {V.AaEval.mount(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.mount(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              mnt.inc(opts, f, RM.AaMountQuery.req(), m0, m1, q)

def Laws.include_idempotent_mount(opts, p, r, q):
  mnt.law(opts, p, r, q)

# dbus rules

def dbs.mgo(+hit: Bool, +r: RD.AaDbusRule, +a: List<&2, RD.AaDbusRule>, +b: List<&2, RD.AaDbusRule>) -> {RD.AaDbusRule.matching.go(hit, r, RD.AaDbusRule.append(a, b)) == RD.AaDbusRule.append(RD.AaDbusRule.matching.go(hit, r, a), b) : List<&2, RD.AaDbusRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def dbs.match_app(+xs: List<&2, RD.AaDbusRule>, +ys: List<&2, RD.AaDbusRule>, +q: RD.AaDbusQuery) -> {RD.AaDbusRule.matching(RD.AaDbusRule.append(xs, ys), q) == RD.AaDbusRule.append(RD.AaDbusRule.matching(xs, q), RD.AaDbusRule.matching(ys, q)) : List<&2, RD.AaDbusRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RD.AaDbusRule>, RD.AaDbusRule.matching.go(RD.AaDbusRule.matches(r, q), r, RD.AaDbusRule.matching(RD.AaDbusRule.append(t, ys), q)), RD.AaDbusRule.matching.go(RD.AaDbusRule.matches(r, q), r, RD.AaDbusRule.append(RD.AaDbusRule.matching(t, q), RD.AaDbusRule.matching(ys, q))), RD.AaDbusRule.append(RD.AaDbusRule.matching.go(RD.AaDbusRule.matches(r, q), r, RD.AaDbusRule.matching(t, q)), RD.AaDbusRule.matching(ys, q)), Equal.cong(List<&2, RD.AaDbusRule>, List<&2, RD.AaDbusRule>, x => RD.AaDbusRule.matching.go(RD.AaDbusRule.matches(r, q), r, x), RD.AaDbusRule.matching(RD.AaDbusRule.append(t, ys), q), RD.AaDbusRule.append(RD.AaDbusRule.matching(t, q), RD.AaDbusRule.matching(ys, q)), dbs.match_app(t, ys, q)), dbs.mgo(RD.AaDbusRule.matches(r, q), r, RD.AaDbusRule.matching(t, q), RD.AaDbusRule.matching(ys, q)))

def dbs.gof_app(+xs: List<&2, RD.AaDbusRule>, +ys: List<&2, RD.AaDbusRule>) -> {RD.AaDbusRule.grants.of(RD.AaDbusRule.append(xs, ys)) == P.AaGrant.append(RD.AaDbusRule.grants.of(xs), RD.AaDbusRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RD.AaDbusRule{qu, p, bus, path, iface, member, name, pn, pl}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, p), x}, RD.AaDbusRule.grants.of(RD.AaDbusRule.append(t, ys)), P.AaGrant.append(RD.AaDbusRule.grants.of(t), RD.AaDbusRule.grants.of(ys)), dbs.gof_app(t, ys))

def dbs.gapp(+xs: List<&2, RD.AaDbusRule>, +ys: List<&2, RD.AaDbusRule>, +q: RD.AaDbusQuery) -> {RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q) == P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RD.AaDbusRule.grants.of(RD.AaDbusRule.matching(RD.AaDbusRule.append(xs, ys), q)), RD.AaDbusRule.grants.of(RD.AaDbusRule.append(RD.AaDbusRule.matching(xs, q), RD.AaDbusRule.matching(ys, q))), P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), Equal.cong(List<&2, RD.AaDbusRule>, List<&2, P.AaGrant>, x => RD.AaDbusRule.grants.of(x), RD.AaDbusRule.matching(RD.AaDbusRule.append(xs, ys), q), RD.AaDbusRule.append(RD.AaDbusRule.matching(xs, q), RD.AaDbusRule.matching(ys, q)), dbs.match_app(xs, ys, q)), dbs.gof_app(RD.AaDbusRule.matching(xs, q), RD.AaDbusRule.matching(ys, q)))

def dbs.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RD.AaDbusRule>, +ys: List<&2, RD.AaDbusRule>, +q: RD.AaDbusQuery) -> {V.AaEval.decide(opts, flags, req, RD.AaDbusRule.grants(RD.AaDbusRule.append(RD.AaDbusRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RD.AaDbusRule.grants(RD.AaDbusRule.append(RD.AaDbusRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), RD.AaDbusRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RD.AaDbusRule.grants(RD.AaDbusRule.append(RD.AaDbusRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), RD.AaDbusRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RD.AaDbusRule.grants(RD.AaDbusRule.append(RD.AaDbusRule.append(xs, ys), ys), q), P.AaGrant.append(RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q), RD.AaDbusRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), RD.AaDbusRule.grants(ys, q)), dbs.gapp(RD.AaDbusRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RD.AaDbusRule.grants(ys, q)), RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q), P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), dbs.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), RD.AaDbusRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q)), inc.decide(opts, flags, req, RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RD.AaDbusRule.grants(RD.AaDbusRule.append(xs, ys), q), P.AaGrant.append(RD.AaDbusRule.grants(xs, q), RD.AaDbusRule.grants(ys, q)), dbs.gapp(xs, ys, q)))))

def dbs.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RD.AaDbusQuery) -> {V.AaEval.dbus(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.dbus(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              dbs.inc(opts, f, RD.AaDbusQuery.req(q), d0, d1, q)

def Laws.include_idempotent_dbus(opts, p, r, q):
  dbs.law(opts, p, r, q)

# change_profile rules

def chg.mgo(+hit: Bool, +r: RX.AaChangeRule, +a: List<&2, RX.AaChangeRule>, +b: List<&2, RX.AaChangeRule>) -> {RX.AaChangeRule.matching.go(hit, r, RX.AaChangeRule.append(a, b)) == RX.AaChangeRule.append(RX.AaChangeRule.matching.go(hit, r, a), b) : List<&2, RX.AaChangeRule>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def chg.match_app(+xs: List<&2, RX.AaChangeRule>, +ys: List<&2, RX.AaChangeRule>, +q: RX.AaChangeQuery) -> {RX.AaChangeRule.matching(RX.AaChangeRule.append(xs, ys), q) == RX.AaChangeRule.append(RX.AaChangeRule.matching(xs, q), RX.AaChangeRule.matching(ys, q)) : List<&2, RX.AaChangeRule>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.trans(List<&2, RX.AaChangeRule>, RX.AaChangeRule.matching.go(RX.AaChangeRule.matches(r, q), r, RX.AaChangeRule.matching(RX.AaChangeRule.append(t, ys), q)), RX.AaChangeRule.matching.go(RX.AaChangeRule.matches(r, q), r, RX.AaChangeRule.append(RX.AaChangeRule.matching(t, q), RX.AaChangeRule.matching(ys, q))), RX.AaChangeRule.append(RX.AaChangeRule.matching.go(RX.AaChangeRule.matches(r, q), r, RX.AaChangeRule.matching(t, q)), RX.AaChangeRule.matching(ys, q)), Equal.cong(List<&2, RX.AaChangeRule>, List<&2, RX.AaChangeRule>, x => RX.AaChangeRule.matching.go(RX.AaChangeRule.matches(r, q), r, x), RX.AaChangeRule.matching(RX.AaChangeRule.append(t, ys), q), RX.AaChangeRule.append(RX.AaChangeRule.matching(t, q), RX.AaChangeRule.matching(ys, q)), chg.match_app(t, ys, q)), chg.mgo(RX.AaChangeRule.matches(r, q), r, RX.AaChangeRule.matching(t, q), RX.AaChangeRule.matching(ys, q)))

def chg.gof_app(+xs: List<&2, RX.AaChangeRule>, +ys: List<&2, RX.AaChangeRule>) -> {RX.AaChangeRule.grants.of(RX.AaChangeRule.append(xs, ys)) == P.AaGrant.append(RX.AaChangeRule.grants.of(xs), RX.AaChangeRule.grants.of(ys)) : List<&2, P.AaGrant>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case RX.AaChangeRule{qu, e, s, tg}:
          Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), x}, RX.AaChangeRule.grants.of(RX.AaChangeRule.append(t, ys)), P.AaGrant.append(RX.AaChangeRule.grants.of(t), RX.AaChangeRule.grants.of(ys)), chg.gof_app(t, ys))

def chg.gapp(+xs: List<&2, RX.AaChangeRule>, +ys: List<&2, RX.AaChangeRule>, +q: RX.AaChangeQuery) -> {RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q) == P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)) : List<&2, P.AaGrant>}:
  Equal.trans(List<&2, P.AaGrant>, RX.AaChangeRule.grants.of(RX.AaChangeRule.matching(RX.AaChangeRule.append(xs, ys), q)), RX.AaChangeRule.grants.of(RX.AaChangeRule.append(RX.AaChangeRule.matching(xs, q), RX.AaChangeRule.matching(ys, q))), P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), Equal.cong(List<&2, RX.AaChangeRule>, List<&2, P.AaGrant>, x => RX.AaChangeRule.grants.of(x), RX.AaChangeRule.matching(RX.AaChangeRule.append(xs, ys), q), RX.AaChangeRule.append(RX.AaChangeRule.matching(xs, q), RX.AaChangeRule.matching(ys, q)), chg.match_app(xs, ys, q)), chg.gof_app(RX.AaChangeRule.matching(xs, q), RX.AaChangeRule.matching(ys, q)))

def chg.inc(+opts: O.AaOptions, +flags: PR.AaFlags, +req: P.AaPerms, +xs: List<&2, RX.AaChangeRule>, +ys: List<&2, RX.AaChangeRule>, +q: RX.AaChangeQuery) -> {V.AaEval.decide(opts, flags, req, RX.AaChangeRule.grants(RX.AaChangeRule.append(RX.AaChangeRule.append(xs, ys), ys), q)) == V.AaEval.decide(opts, flags, req, RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q)) : V.AaDecision}:
  Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, RX.AaChangeRule.grants(RX.AaChangeRule.append(RX.AaChangeRule.append(xs, ys), ys), q)), V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), RX.AaChangeRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), RX.AaChangeRule.grants(RX.AaChangeRule.append(RX.AaChangeRule.append(xs, ys), ys), q), P.AaGrant.append(P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), RX.AaChangeRule.grants(ys, q)), Equal.trans(List<&2, P.AaGrant>, RX.AaChangeRule.grants(RX.AaChangeRule.append(RX.AaChangeRule.append(xs, ys), ys), q), P.AaGrant.append(RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q), RX.AaChangeRule.grants(ys, q)), P.AaGrant.append(P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), RX.AaChangeRule.grants(ys, q)), chg.gapp(RX.AaChangeRule.append(xs, ys), ys, q), Equal.cong(List<&2, P.AaGrant>, List<&2, P.AaGrant>, x => P.AaGrant.append(x, RX.AaChangeRule.grants(ys, q)), RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q), P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), chg.gapp(xs, ys, q)))), Equal.trans(V.AaDecision, V.AaEval.decide(opts, flags, req, P.AaGrant.append(P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), RX.AaChangeRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q))), V.AaEval.decide(opts, flags, req, RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q)), inc.decide(opts, flags, req, RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), Equal.cong(List<&2, P.AaGrant>, V.AaDecision, x => V.AaEval.decide(opts, flags, req, x), P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q), Equal.sym(List<&2, P.AaGrant>, RX.AaChangeRule.grants(RX.AaChangeRule.append(xs, ys), q), P.AaGrant.append(RX.AaChangeRule.grants(xs, q), RX.AaChangeRule.grants(ys, q)), chg.gapp(xs, ys, q)))))

def chg.law(+opts: O.AaOptions, +p: PR.AaProfile, +r: PR.AaRules, +q: RX.AaChangeQuery) -> {V.AaEval.change_profile(opts, PR.AaProfile.include(PR.AaProfile.include(p, r), r), q) == V.AaEval.change_profile(opts, PR.AaProfile.include(p, r), q) : V.AaDecision}:
  match p:
    case PR.AaProfile{n, a, f, r0, c, h}:
      match r0:
        case PR.AaRules{f0, c0, n0, s0, p0, m0, d0, x0}:
          match r:
            case PR.AaRules{f1, c1, n1, s1, p1, m1, d1, x1}:
              chg.inc(opts, f, RX.AaChangeQuery.req(), x0, x1, q)

def Laws.include_idempotent_change_profile(opts, p, r, q):
  chg.law(opts, p, r, q)

# Exec

def ex.law(+opts: O.AaOptions, +pol: PR.AaPolicy, +name: List<&2, U32>, +owner: Bool, +path: List<&2, U32>, +p: PR.AaProfile, +h1: {PR.AaPolicy.lookup(pol, name) == Some{p} : Maybe<&2, PR.AaProfile>}, +h2: {TR.AaTrans.is_unconfined(PR.AaFlags.mode(PR.AaProfile.flags(p))) == False{} : Bool}, +h3: {V.AaDecision.allowed(V.AaEval.file(opts, p, F.AaFileQuery{path, owner, P.AaPerms.bit(6n)})) == False{} : Bool}) -> {TR.AaExecResult.ok(TR.AaTrans.exec(opts, pol, name, owner, path)) == False{} : Bool}:
  %Equal.sym(Maybe<&2, PR.AaProfile>, PR.AaPolicy.lookup(pol, name), Some{p}, h1) : {TR.AaExecResult.ok(TR.AaTrans.exec.of(_, opts, pol, name, owner, path)) == False{} : Bool}
  %Equal.sym(Bool, TR.AaTrans.is_unconfined(PR.AaFlags.mode(PR.AaProfile.flags(p))), False{}, h2) : {TR.AaExecResult.ok(TR.AaTrans.exec.mode(_, opts, pol, p, name, owner, path)) == False{} : Bool}
  %Equal.sym(Bool, V.AaDecision.allowed(V.AaEval.file(opts, p, F.AaFileQuery{path, owner, P.AaPerms.bit(6n)})), False{}, h3) : {TR.AaExecResult.ok(TR.AaTrans.exec.granted(_, F.AaFileQuery{path, owner, P.AaPerms.bit(6n)}, pol, p, name, path, V.AaEval.file(opts, p, F.AaFileQuery{path, owner, P.AaPerms.bit(6n)}))) == False{} : Bool}
  {==}

def Laws.exec_needs_x(opts, pol, name, owner, path, p, h1, h2, h3):
  ex.law(opts, pol, name, owner, path, p, h1, h2, h3)

# Witnesses and vectors, by computation

def Laws.deny_wins_sat():
  {==}

def Laws.deny_wins_example():
  {==}

def Laws.allow_example():
  {==}

def Laws.audit_example():
  {==}

def Laws.unmatched_sat():
  {==}

def Laws.file_unmatched_sat():
  {==}

def Laws.unmatched_example():
  {==}

def Laws.complain_sat():
  {==}

def Laws.complain_example_unmatched():
  {==}

def Laws.complain_example_deny_rule():
  {==}

def Laws.complain_example_no_deny():
  {==}

def Laws.kill_example():
  {==}

def Laws.exec_needs_x_sat():
  {==}

def Laws.exec_needs_x_sat2():
  {==}

def Laws.glob_star_not_empty_segment():
  {==}

def Laws.glob_star_file():
  {==}

def Laws.glob_star_no_slash():
  {==}

def Laws.glob_star2_not_dir_itself():
  {==}

def Laws.glob_star2_deep():
  {==}

def Laws.glob_star_inside_segment():
  {==}

def Laws.glob_star_in_braces():
  {==}

def Laws.glob_negated_class_slash():
  {==}

def Laws.glob_slashes_collapse():
  {==}

def Laws.glob_class_range():
  {==}

def Laws.glob_nested_braces():
  {==}

def Laws.glob_question():
  {==}

def Laws.glob_one_alternative_rejected():
  {==}

def Laws.glob_trailing_dash_rejected():
  {==}

def Laws.glob_empty_class_rejected():
  {==}

def Laws.policy_file_vectors():
  {==}

def Laws.policy_exec_vectors():
  {==}
