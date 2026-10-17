import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./uuid.bend as U
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# Converting a list to Octets and back masks each element: bytes' interface
# law octets_to_of, so nothing here depends on how Octets stores its bytes.
def octets_list(xs: List<&2, U32>) -> {B.mask(xs) == B.Octets.to_list(B.Octets.of_list(xs)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs))

# The text round trips. show writes two hex digits per octet; parse reads them
# back two at a time. A nibble's digit reads back as the nibble (16 cases), so
# an octet's two digits read back as the octet, and so, by induction, does a
# list of octets. The dashes are concrete in show's output, so the rest is
# computation.

def nib(n: Word(4n)) -> {Some{n} == U.Uuid.hexval(U.Uuid.hexdigit(n)) : Maybe<&2, Word(4n)>}:
  match n:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}

def nib_upper(n: Word(4n)) -> {Some{n} == U.Uuid.hexval(Char.to_upper(U.Uuid.hexdigit(n))) : Maybe<&2, Word(4n)>}:
  match n:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}

# the upper-case digits of a list of octets
def udigits(bs: List<&2, Word(8n)>) -> List<&2, Char>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      Con{Char.to_upper(U.Uuid.hexdigit(U.Uuid.nibble.hi(b))), Con{Char.to_upper(U.Uuid.hexdigit(U.Uuid.nibble.lo(b))), udigits(t)}}

def rd(b: Word(8n)) -> {Some{b} == U.Uuid.rdbyte(U.Uuid.hexdigit(U.Uuid.nibble.hi(b)), U.Uuid.hexdigit(U.Uuid.nibble.lo(b))) : Maybe<&2, Word(8n)>}:
  match b:
    case WCon{+x0, WCon{+x1, WCon{+x2, WCon{+x3, WCon{+x4, WCon{+x5, WCon{+x6, WCon{+x7, WNil{}}}}}}}}}:
      %nib(WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}) : {Some{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}}}}} == U.Uuid.hexval.join(_, U.Uuid.hexval(U.Uuid.hexdigit(WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}))) : Maybe<&2, Word(8n)>}
      %nib(WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}) : {Some{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}}}}} == U.Uuid.hexval.join(Some{WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}, _) : Maybe<&2, Word(8n)>}
      {==}

def rd_upper(b: Word(8n)) -> {Some{b} == U.Uuid.rdbyte(Char.to_upper(U.Uuid.hexdigit(U.Uuid.nibble.hi(b))), Char.to_upper(U.Uuid.hexdigit(U.Uuid.nibble.lo(b)))) : Maybe<&2, Word(8n)>}:
  match b:
    case WCon{+x0, WCon{+x1, WCon{+x2, WCon{+x3, WCon{+x4, WCon{+x5, WCon{+x6, WCon{+x7, WNil{}}}}}}}}}:
      %nib_upper(WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}) : {Some{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}}}}} == U.Uuid.hexval.join(_, U.Uuid.hexval(Char.to_upper(U.Uuid.hexdigit(WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}})))) : Maybe<&2, Word(8n)>}
      %nib_upper(WCon{x0, WCon{x1, WCon{x2, WCon{x3, WNil{}}}}}) : {Some{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}}}}} == U.Uuid.hexval.join(Some{WCon{x4, WCon{x5, WCon{x6, WCon{x7, WNil{}}}}}}, _) : Maybe<&2, Word(8n)>}
      {==}

def hexlist_digits(bs: List<&2, Word(8n)>) -> {Some{bs} == U.Uuid.hexlist(U.Uuid.digits(bs)) : Maybe<&2, List<&2, Word(8n)>>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %rd(b) : {Some{Con{b, t}} == U.Uuid.cons_m(_, U.Uuid.hexlist(U.Uuid.digits(t))) : Maybe<&2, List<&2, Word(8n)>>}
      %hexlist_digits(t) : {Some{Con{b, t}} == U.Uuid.cons_m(Some{b}, _) : Maybe<&2, List<&2, Word(8n)>>}
      {==}

def hexlist_udigits(bs: List<&2, Word(8n)>) -> {Some{bs} == U.Uuid.hexlist(udigits(bs)) : Maybe<&2, List<&2, Word(8n)>>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %rd_upper(b) : {Some{Con{b, t}} == U.Uuid.cons_m(_, U.Uuid.hexlist(udigits(t))) : Maybe<&2, List<&2, Word(8n)>>}
      %hexlist_udigits(t) : {Some{Con{b, t}} == U.Uuid.cons_m(Some{b}, _) : Maybe<&2, List<&2, Word(8n)>>}
      {==}

def Laws.bytes_round_trip(u):
  match u:
    case U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}}:
      %octets_list(U.Uuid.to_list(U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}})) : {U.Uuid.length_ok(U.Uuid.of_list(_)) == Done{U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.guid_round_trip(u):
  match u:
    case U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}}:
      %octets_list(U.Uuid.guid_list(U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}})) : {U.Uuid.length_ok(U.Uuid.of_guid_list(_)) == Done{U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.guid_list_round_trip(u):
  match u:
    case U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}}:
      {==}

def Laws.make_bytes(u):
  match u:
    case U.Uuid{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WNil{}}}}}}}}}, WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WNil{}}}}}}}}}, WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WNil{}}}}}}}}}, WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WNil{}}}}}}}}}, WCon{xe_0, WCon{xe_1, WCon{xe_2, WCon{xe_3, WCon{xe_4, WCon{xe_5, WCon{xe_6, WCon{xe_7, WNil{}}}}}}}}}, WCon{xf_0, WCon{xf_1, WCon{xf_2, WCon{xf_3, WCon{xf_4, WCon{xf_5, WCon{xf_6, WCon{xf_7, WNil{}}}}}}}}}, WCon{xg_0, WCon{xg_1, WCon{xg_2, WCon{xg_3, WCon{xg_4, WCon{xg_5, WCon{xg_6, WCon{xg_7, WNil{}}}}}}}}}, WCon{xh_0, WCon{xh_1, WCon{xh_2, WCon{xh_3, WCon{xh_4, WCon{xh_5, WCon{xh_6, WCon{xh_7, WNil{}}}}}}}}}, WCon{xi_0, WCon{xi_1, WCon{xi_2, WCon{xi_3, WCon{xi_4, WCon{xi_5, WCon{xi_6, WCon{xi_7, WNil{}}}}}}}}}, WCon{xj_0, WCon{xj_1, WCon{xj_2, WCon{xj_3, WCon{xj_4, WCon{xj_5, WCon{xj_6, WCon{xj_7, WNil{}}}}}}}}}, WCon{xk_0, WCon{xk_1, WCon{xk_2, WCon{xk_3, WCon{xk_4, WCon{xk_5, WCon{xk_6, WCon{xk_7, WNil{}}}}}}}}}, WCon{xl_0, WCon{xl_1, WCon{xl_2, WCon{xl_3, WCon{xl_4, WCon{xl_5, WCon{xl_6, WCon{xl_7, WNil{}}}}}}}}}, WCon{xm_0, WCon{xm_1, WCon{xm_2, WCon{xm_3, WCon{xm_4, WCon{xm_5, WCon{xm_6, WCon{xm_7, WNil{}}}}}}}}}, WCon{xn_0, WCon{xn_1, WCon{xn_2, WCon{xn_3, WCon{xn_4, WCon{xn_5, WCon{xn_6, WCon{xn_7, WNil{}}}}}}}}}, WCon{xo_0, WCon{xo_1, WCon{xo_2, WCon{xo_3, WCon{xo_4, WCon{xo_5, WCon{xo_6, WCon{xo_7, WNil{}}}}}}}}}, WCon{xp_0, WCon{xp_1, WCon{xp_2, WCon{xp_3, WCon{xp_4, WCon{xp_5, WCon{xp_6, WCon{xp_7, WNil{}}}}}}}}}}:
      {==}

def Laws.guid_layout(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15):
  %octets_list([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) : {U.Uuid.length_ok(U.Uuid.of_guid_list(_)) == U.Uuid.length_ok(U.Uuid.of_list(B.Octets.to_list(B.Octets.of_list([a3, a2, a1, a0, a5, a4, a7, a6, a8, a9, a10, a11, a12, a13, a14, a15])))) : Result<&2, &2, U.UuidError, U.Uuid>}
  %octets_list([a3, a2, a1, a0, a5, a4, a7, a6, a8, a9, a10, a11, a12, a13, a14, a15]) : {U.Uuid.length_ok(U.Uuid.of_guid_list(B.mask([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]))) == U.Uuid.length_ok(U.Uuid.of_list(_)) : Result<&2, &2, U.UuidError, U.Uuid>}
  {==}

def Laws.text_round_trip(u):
  match u:
    case U.Uuid{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14, +b15}:
      %hexlist_digits([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) : {U.Uuid.of_digits(_) == Done{U.Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.text_upper_round_trip(u):
  match u:
    case U.Uuid{+b0, +b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8, +b9, +b10, +b11, +b12, +b13, +b14, +b15}:
      %hexlist_udigits([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) : {U.Uuid.of_digits(_) == Done{U.Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.text_length(u):
  match u:
    case U.Uuid{b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15}:
      {==}

def Laws.rfc_v1_text():
  {==}

def Laws.rfc_v3_text():
  {==}

def Laws.rfc_v6_text():
  {==}

def Laws.rfc_v7_text():
  {==}

def Laws.rfc_v1_version():
  {==}

def Laws.rfc_v3_version():
  {==}

def Laws.rfc_v4_version():
  {==}

def Laws.rfc_v5_version():
  {==}

def Laws.rfc_v6_version():
  {==}

def Laws.rfc_v7_version():
  {==}

def Laws.rfc_v8_time_version():
  {==}

def Laws.rfc_v8_name_version():
  {==}

def Laws.rfc_v4_variant():
  {==}

def Laws.rfc_v7_variant():
  {==}

def Laws.rfc_v8_name_variant():
  {==}

def Laws.microsoft_variant():
  {==}

def Laws.nil_text():
  {==}

def Laws.max_text():
  {==}

def Laws.nil_variant():
  {==}

def Laws.max_variant():
  {==}

def Laws.max_parse():
  {==}

def Laws.rfc_v4_bytes():
  {==}

def Laws.rfc_v1_guid():
  {==}

def Laws.esp_guid():
  {==}

def Laws.short_text():
  {==}

def Laws.bad_digit():
  {==}

def Laws.missing_dash():
  {==}

def Laws.short_bytes():
  {==}
