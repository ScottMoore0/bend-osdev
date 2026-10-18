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
    case U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %octets_list(U.Uuid.to_list(U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})) : {U.Uuid.length_ok(U.Uuid.of_list(_)) == Done{U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.guid_round_trip(u):
  match u:
    case U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %octets_list(U.Uuid.guid_list(U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})) : {U.Uuid.length_ok(U.Uuid.of_guid_list(_)) == Done{U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.guid_list_round_trip(u):
  match u:
    case U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.make_bytes(u):
  match u:
    case U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.guid_layout(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15):
  %octets_list([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) : {U.Uuid.length_ok(U.Uuid.of_guid_list(_)) == U.Uuid.length_ok(U.Uuid.of_list(B.Octets.to_list(B.Octets.of_list([a3, a2, a1, a0, a5, a4, a7, a6, a8, a9, a10, a11, a12, a13, a14, a15])))) : Result<&2, &2, U.UuidError, U.Uuid>}
  %octets_list([a3, a2, a1, a0, a5, a4, a7, a6, a8, a9, a10, a11, a12, a13, a14, a15]) : {U.Uuid.length_ok(U.Uuid.of_guid_list(B.mask([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]))) == U.Uuid.length_ok(U.Uuid.of_list(_)) : Result<&2, &2, U.UuidError, U.Uuid>}
  {==}

def Laws.text_round_trip(u):
  match u:
    case U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %hexlist_digits(U.Uuid.octets(U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})) : {U.Uuid.of_digits(_) == Done{U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.text_upper_round_trip(u):
  match u:
    case U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %hexlist_udigits(U.Uuid.octets(U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}})) : {U.Uuid.of_digits(_) == Done{U.Uuid{U32{WCon{xa_0, WCon{xa_1, WCon{xa_2, WCon{xa_3, WCon{xa_4, WCon{xa_5, WCon{xa_6, WCon{xa_7, WCon{xa_8, WCon{xa_9, WCon{xa_10, WCon{xa_11, WCon{xa_12, WCon{xa_13, WCon{xa_14, WCon{xa_15, WCon{xa_16, WCon{xa_17, WCon{xa_18, WCon{xa_19, WCon{xa_20, WCon{xa_21, WCon{xa_22, WCon{xa_23, WCon{xa_24, WCon{xa_25, WCon{xa_26, WCon{xa_27, WCon{xa_28, WCon{xa_29, WCon{xa_30, WCon{xa_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xb_0, WCon{xb_1, WCon{xb_2, WCon{xb_3, WCon{xb_4, WCon{xb_5, WCon{xb_6, WCon{xb_7, WCon{xb_8, WCon{xb_9, WCon{xb_10, WCon{xb_11, WCon{xb_12, WCon{xb_13, WCon{xb_14, WCon{xb_15, WCon{xb_16, WCon{xb_17, WCon{xb_18, WCon{xb_19, WCon{xb_20, WCon{xb_21, WCon{xb_22, WCon{xb_23, WCon{xb_24, WCon{xb_25, WCon{xb_26, WCon{xb_27, WCon{xb_28, WCon{xb_29, WCon{xb_30, WCon{xb_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xc_0, WCon{xc_1, WCon{xc_2, WCon{xc_3, WCon{xc_4, WCon{xc_5, WCon{xc_6, WCon{xc_7, WCon{xc_8, WCon{xc_9, WCon{xc_10, WCon{xc_11, WCon{xc_12, WCon{xc_13, WCon{xc_14, WCon{xc_15, WCon{xc_16, WCon{xc_17, WCon{xc_18, WCon{xc_19, WCon{xc_20, WCon{xc_21, WCon{xc_22, WCon{xc_23, WCon{xc_24, WCon{xc_25, WCon{xc_26, WCon{xc_27, WCon{xc_28, WCon{xc_29, WCon{xc_30, WCon{xc_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{xd_0, WCon{xd_1, WCon{xd_2, WCon{xd_3, WCon{xd_4, WCon{xd_5, WCon{xd_6, WCon{xd_7, WCon{xd_8, WCon{xd_9, WCon{xd_10, WCon{xd_11, WCon{xd_12, WCon{xd_13, WCon{xd_14, WCon{xd_15, WCon{xd_16, WCon{xd_17, WCon{xd_18, WCon{xd_19, WCon{xd_20, WCon{xd_21, WCon{xd_22, WCon{xd_23, WCon{xd_24, WCon{xd_25, WCon{xd_26, WCon{xd_27, WCon{xd_28, WCon{xd_29, WCon{xd_30, WCon{xd_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : Result<&2, &2, U.UuidError, U.Uuid>}
      {==}

def Laws.text_length(u):
  match u:
    case U.Uuid{w0, w1, w2, w3}:
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
