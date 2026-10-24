# Proof helpers for bend-osdev-crc: bitwise identities on Base's U32, for
# every input, by induction over the bits of Base's Word(n). The table-driven
# fast path (proof_fast.bend) rests on them: XOR is a commutative group, AND
# distributes over it, and the shifts move it bit for bit. Lemmas are
# prefixed cw.
import Base

# Contradictions

def cw.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def cw.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : cw.bt(_)
  Unit{}

def cw.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : cw.bt(_)
  Unit{}

# Bool

def cw.bx_comm(+a: Bool, +b: Bool) -> {Bool.xor(a, b) == Bool.xor(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def cw.bx_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def cw.bx_self(+a: Bool) -> {Bool.xor(a, a) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cw.bx_zero(+a: Bool) -> {Bool.xor(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cw.bx_swap(+a: Bool, +b: Bool, +c: Bool) -> {Bool.xor(Bool.xor(a, b), c) == Bool.xor(Bool.xor(a, c), b) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def cw.bx_cancel(+a: Bool, +b: Bool, +c: Bool) -> {Bool.xor(Bool.xor(a, c), Bool.xor(b, c)) == Bool.xor(a, b) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def cw.ba_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def cw.ba_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cw.ba_zero(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cw.ba_one(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cw.ba_idem(+a: Bool) -> {Bool.and(a, a) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# m and (a xor b) = (m and a) xor (m and b)
def cw.ba_xor(+m: Bool, +a: Bool, +b: Bool) -> {Bool.and(m, Bool.xor(a, b)) == Bool.xor(Bool.and(m, a), Bool.and(m, b)) : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# c xor (w and c) = (not w) and c
def cw.bx_clear(+w: Bool, +c: Bool) -> {Bool.xor(c, Bool.and(w, c)) == Bool.and(Bool.not(w), c) : Bool}:
  match w c:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Congruence of a word's head and tail

def cw.wcon2(-p: Nat, -a: Bool, -b: Bool, -x: Word(p), -y: Word(p), ea: {a == b : Bool}, ex: {x == y : Word(p)}) -> {WCon{a, x} == WCon{b, y} : Word(1n+p)}:
  %ea : {WCon{a, x} == WCon{_, y} : Word(1n+p)}
  %ex : {WCon{a, x} == WCon{a, _} : Word(1n+p)}
  {==}

def cw.u32_cong(-x: Word(32n), -y: Word(32n), e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  %e : {U32{x} == U32{_} : U32}
  {==}

# all ones
def cw.ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, cw.ones(p)}

# XOR on words: a commutative group with identity zero, every word its own
# inverse

def cw.wx_comm(n: Nat, a: Word(n), b: Word(n)) -> {Word.xor(n, a, b) == Word.xor(n, b, a) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          cw.wcon2(p, Bool.xor(ah, bh), Bool.xor(bh, ah), Word.xor(p, at, bt), Word.xor(p, bt, at), cw.bx_comm(ah, bh), cw.wx_comm(p, at, bt))

def cw.wx_assoc(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ah, at} WCon{+bh, bt} WCon{+ch, ct}:
          cw.wcon2(p, Bool.xor(Bool.xor(ah, bh), ch), Bool.xor(ah, Bool.xor(bh, ch)), Word.xor(p, Word.xor(p, at, bt), ct), Word.xor(p, at, Word.xor(p, bt, ct)), cw.bx_assoc(ah, bh, ch), cw.wx_assoc(p, at, bt, ct))

def cw.wx_self(n: Nat, a: Word(n)) -> {Word.xor(n, a, a) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          cw.wcon2(p, Bool.xor(ah, ah), False{}, Word.xor(p, at, at), Word.zero(p), cw.bx_self(ah), cw.wx_self(p, at))

def cw.wx_zero(n: Nat, a: Word(n)) -> {Word.xor(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          cw.wcon2(p, Bool.xor(ah, False{}), ah, Word.xor(p, at, Word.zero(p)), at, cw.bx_zero(ah), cw.wx_zero(p, at))

def cw.wx_swap(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, Word.xor(n, a, c), b) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ah, at} WCon{+bh, bt} WCon{+ch, ct}:
          cw.wcon2(p, Bool.xor(Bool.xor(ah, bh), ch), Bool.xor(Bool.xor(ah, ch), bh), Word.xor(p, Word.xor(p, at, bt), ct), Word.xor(p, Word.xor(p, at, ct), bt), cw.bx_swap(ah, bh, ch), cw.wx_swap(p, at, bt, ct))

def cw.wx_cancel(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.xor(n, Word.xor(n, a, c), Word.xor(n, b, c)) == Word.xor(n, a, b) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ah, at} WCon{+bh, bt} WCon{+ch, ct}:
          cw.wcon2(p, Bool.xor(Bool.xor(ah, ch), Bool.xor(bh, ch)), Bool.xor(ah, bh), Word.xor(p, Word.xor(p, at, ct), Word.xor(p, bt, ct)), Word.xor(p, at, bt), cw.bx_cancel(ah, bh, ch), cw.wx_cancel(p, at, bt, ct))

# AND on words

def cw.wa_comm(n: Nat, a: Word(n), b: Word(n)) -> {Word.and(n, a, b) == Word.and(n, b, a) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          cw.wcon2(p, Bool.and(ah, bh), Bool.and(bh, ah), Word.and(p, at, bt), Word.and(p, bt, at), cw.ba_comm(ah, bh), cw.wa_comm(p, at, bt))

def cw.wa_assoc(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.and(n, Word.and(n, a, b), c) == Word.and(n, a, Word.and(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ah, at} WCon{+bh, bt} WCon{+ch, ct}:
          cw.wcon2(p, Bool.and(Bool.and(ah, bh), ch), Bool.and(ah, Bool.and(bh, ch)), Word.and(p, Word.and(p, at, bt), ct), Word.and(p, at, Word.and(p, bt, ct)), cw.ba_assoc(ah, bh, ch), cw.wa_assoc(p, at, bt, ct))

def cw.wa_idem(n: Nat, a: Word(n)) -> {Word.and(n, a, a) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          cw.wcon2(p, Bool.and(ah, ah), ah, Word.and(p, at, at), at, cw.ba_idem(ah), cw.wa_idem(p, at))

def cw.wa_zero_r(n: Nat, a: Word(n)) -> {Word.and(n, a, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          cw.wcon2(p, Bool.and(ah, False{}), False{}, Word.and(p, at, Word.zero(p)), Word.zero(p), cw.ba_zero(ah), cw.wa_zero_r(p, at))

def cw.wa_zero_l(n: Nat, a: Word(n)) -> {Word.and(n, Word.zero(n), a) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ah, at}:
          %Equal.sym(Word(p), Word.and(p, Word.zero(p), at), Word.zero(p), cw.wa_zero_l(p, at)) : {WCon{False{}, _} == Word.zero(1n+p) : Word(1n+p)}
          {==}

def cw.wa_ones_l(n: Nat, a: Word(n)) -> {Word.and(n, cw.ones(n), a) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{ah, +at}:
          %Equal.sym(Word(p), Word.and(p, cw.ones(p), at), at, cw.wa_ones_l(p, at)) : {WCon{ah, _} == WCon{ah, at} : Word(1n+p)}
          {==}

def cw.wa_xor(n: Nat, m: Word(n), a: Word(n), b: Word(n)) -> {Word.and(n, m, Word.xor(n, a, b)) == Word.xor(n, Word.and(n, m, a), Word.and(n, m, b)) : Word(n)}:
  match n:
    case 0n:
      match m a b:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match m a b:
        case WCon{+mh, mt} WCon{+ah, at} WCon{+bh, bt}:
          cw.wcon2(p, Bool.and(mh, Bool.xor(ah, bh)), Bool.xor(Bool.and(mh, ah), Bool.and(mh, bh)), Word.and(p, mt, Word.xor(p, at, bt)), Word.xor(p, Word.and(p, mt, at), Word.and(p, mt, bt)), cw.ba_xor(mh, ah, bh), cw.wa_xor(p, mt, at, bt))

def cw.wx_clear(n: Nat, w: Word(n), c: Word(n)) -> {Word.xor(n, c, Word.and(n, w, c)) == Word.and(n, Word.not(n, w), c) : Word(n)}:
  match n:
    case 0n:
      match w c:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match w c:
        case WCon{+wh, wt} WCon{+ch, +ct}:
          cw.wcon2(p, Bool.xor(ch, Bool.and(wh, ch)), Bool.and(Bool.not(wh), ch), Word.xor(p, ct, Word.and(p, wt, ct)), Word.and(p, Word.not(p, wt), ct), cw.bx_clear(wh, ch), cw.wx_clear(p, wt, ct))

# The shifts move XOR bit for bit

def cw.pad_xor(p: Nat, a: Word(p), b: Word(p)) -> {Word.shr.pad(p, Word.xor(p, a, b)) == Word.xor(1n+p, Word.shr.pad(p, a), Word.shr.pad(p, b)) : Word(1n+p)}:
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          %Equal.sym(Word(1n+q), Word.shr.pad(q, Word.xor(q, at, bt)), Word.xor(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt)), cw.pad_xor(q, at, bt)) : {WCon{Bool.xor(ah, bh), _} == WCon{Bool.xor(ah, bh), Word.xor(1n+q, Word.shr.pad(q, at), Word.shr.pad(q, bt))} : Word(2n+q)}
          {==}

def cw.put_xor(p: Nat, +c: Bool, +d: Bool, a: Word(p), b: Word(p)) -> {Word.shl.put(p, Bool.xor(c, d), Word.xor(p, a, b)) == Word.xor(p, Word.shl.put(p, c, a), Word.shl.put(p, d, b)) : Word(p)}:
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          %Equal.sym(Word(q), Word.shl.put(q, Bool.xor(ah, bh), Word.xor(q, at, bt)), Word.xor(q, Word.shl.put(q, ah, at), Word.shl.put(q, bh, bt)), cw.put_xor(q, ah, bh, at, bt)) : {WCon{Bool.xor(c, d), _} == WCon{Bool.xor(c, d), Word.xor(q, Word.shl.put(q, ah, at), Word.shl.put(q, bh, bt))} : Word(1n+q)}
          {==}

# U32

def cw.ux_comm(a: U32, b: U32) -> {U32.xor(a, b) == U32.xor(b, a) : U32}:
  match a b:
    case U32{x} U32{y}:
      cw.u32_cong(Word.xor(32n, x, y), Word.xor(32n, y, x), cw.wx_comm(32n, x, y))

def cw.ux_assoc(a: U32, b: U32, c: U32) -> {U32.xor(U32.xor(a, b), c) == U32.xor(a, U32.xor(b, c)) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      cw.u32_cong(Word.xor(32n, Word.xor(32n, x, y), z), Word.xor(32n, x, Word.xor(32n, y, z)), cw.wx_assoc(32n, x, y, z))

def cw.ux_self(a: U32) -> {U32.xor(a, a) == 0 : U32}:
  match a:
    case U32{+x}:
      cw.u32_cong(Word.xor(32n, x, x), Word.zero(32n), cw.wx_self(32n, x))

def cw.ux_zero(a: U32) -> {U32.xor(a, 0) == a : U32}:
  match a:
    case U32{+x}:
      cw.u32_cong(Word.xor(32n, x, Word.zero(32n)), x, cw.wx_zero(32n, x))

def cw.ux_zero_l(+a: U32) -> {U32.xor(0, a) == a : U32}:
  %cw.ux_comm(a, 0) : {_ == a : U32}
  cw.ux_zero(a)

def cw.x_swap(a: U32, b: U32, c: U32) -> {U32.xor(U32.xor(a, b), c) == U32.xor(U32.xor(a, c), b) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      cw.u32_cong(Word.xor(32n, Word.xor(32n, x, y), z), Word.xor(32n, Word.xor(32n, x, z), y), cw.wx_swap(32n, x, y, z))

def cw.x_cancel(a: U32, b: U32, c: U32) -> {U32.xor(U32.xor(a, c), U32.xor(b, c)) == U32.xor(a, b) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      cw.u32_cong(Word.xor(32n, Word.xor(32n, x, z), Word.xor(32n, y, z)), Word.xor(32n, x, y), cw.wx_cancel(32n, x, y, z))

def cw.ua_comm(a: U32, b: U32) -> {U32.and(a, b) == U32.and(b, a) : U32}:
  match a b:
    case U32{x} U32{y}:
      cw.u32_cong(Word.and(32n, x, y), Word.and(32n, y, x), cw.wa_comm(32n, x, y))

def cw.ua_assoc(a: U32, b: U32, c: U32) -> {U32.and(U32.and(a, b), c) == U32.and(a, U32.and(b, c)) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      cw.u32_cong(Word.and(32n, Word.and(32n, x, y), z), Word.and(32n, x, Word.and(32n, y, z)), cw.wa_assoc(32n, x, y, z))

def cw.ua_idem(a: U32) -> {U32.and(a, a) == a : U32}:
  match a:
    case U32{+x}:
      cw.u32_cong(Word.and(32n, x, x), x, cw.wa_idem(32n, x))

def cw.ua_zero_l(a: U32) -> {U32.and(0, a) == 0 : U32}:
  match a:
    case U32{+x}:
      cw.u32_cong(Word.and(32n, Word.zero(32n), x), Word.zero(32n), cw.wa_zero_l(32n, x))

def cw.ua_ones_l(a: U32) -> {U32.and(4294967295, a) == a : U32}:
  match a:
    case U32{+x}:
      cw.u32_cong(Word.and(32n, cw.ones(32n), x), x, cw.wa_ones_l(32n, x))

def cw.ua_xor(m: U32, a: U32, b: U32) -> {U32.and(m, U32.xor(a, b)) == U32.xor(U32.and(m, a), U32.and(m, b)) : U32}:
  match m a b:
    case U32{w} U32{x} U32{y}:
      cw.u32_cong(Word.and(32n, w, Word.xor(32n, x, y)), Word.xor(32n, Word.and(32n, w, x), Word.and(32n, w, y)), cw.wa_xor(32n, w, x, y))

def cw.ux_clear(w: U32, c: U32) -> {U32.xor(c, U32.and(w, c)) == U32.and(U32.not(w), c) : U32}:
  match w c:
    case U32{x} U32{+y}:
      cw.u32_cong(Word.xor(32n, y, Word.and(32n, x, y)), Word.and(32n, Word.not(32n, x), y), cw.wx_clear(32n, x, y))

def cw.shr_xor(a: U32, b: U32) -> {U32.shr(U32.xor(a, b)) == U32.xor(U32.shr(a), U32.shr(b)) : U32}:
  match a b:
    case U32{WCon{ah, at}} U32{WCon{bh, bt}}:
      cw.u32_cong(Word.shr.pad(31n, Word.xor(31n, at, bt)), Word.xor(32n, Word.shr.pad(31n, at), Word.shr.pad(31n, bt)), cw.pad_xor(31n, at, bt))

def cw.shl_xor(a: U32, b: U32) -> {U32.shl(U32.xor(a, b)) == U32.xor(U32.shl(a), U32.shl(b)) : U32}:
  match a b:
    case U32{WCon{+ah, at}} U32{WCon{+bh, bt}}:
      %Equal.sym(Word(31n), Word.shl.put(31n, Bool.xor(ah, bh), Word.xor(31n, at, bt)), Word.xor(31n, Word.shl.put(31n, ah, at), Word.shl.put(31n, bh, bt)), cw.put_xor(31n, ah, bh, at, bt)) : {U32{WCon{False{}, _}} == U32.xor(U32.shl(U32{WCon{ah, at}}), U32.shl(U32{WCon{bh, bt}})) : U32}
      {==}

def cw.shrn_xor(+n: Nat, +a: U32, +b: U32) -> {U32.shrn(U32.xor(a, b), n) == U32.xor(U32.shrn(a, n), U32.shrn(b, n)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.shrn(U32.xor(a, b), p), U32.xor(U32.shrn(a, p), U32.shrn(b, p)), cw.shrn_xor(p, a, b)) : {U32.shr(_) == U32.xor(U32.shr(U32.shrn(a, p)), U32.shr(U32.shrn(b, p))) : U32}
      cw.shr_xor(U32.shrn(a, p), U32.shrn(b, p))

def cw.shln_xor(+n: Nat, +a: U32, +b: U32) -> {U32.shln(U32.xor(a, b), n) == U32.xor(U32.shln(a, n), U32.shln(b, n)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.shln(U32.xor(a, b), p), U32.xor(U32.shln(a, p), U32.shln(b, p)), cw.shln_xor(p, a, b)) : {U32.shl(_) == U32.xor(U32.shl(U32.shln(a, p)), U32.shl(U32.shln(b, p))) : U32}
      cw.shl_xor(U32.shln(a, p), U32.shln(b, p))

# The lowest bit, and bit k

def cw.odd(x: U32) -> Bool:
  match x:
    case U32{WCon{b, t}}:
      b

def cw.odd_xor(a: U32, b: U32) -> {cw.odd(U32.xor(a, b)) == Bool.xor(cw.odd(a), cw.odd(b)) : Bool}:
  match a b:
    case U32{WCon{ah, at}} U32{WCon{bh, bt}}:
      {==}

# the engines' test of the lowest bit
def cw.odd_test(x: U32) -> {U32.is_eq(U32.and(x, 1), 1) == cw.odd(x) : Bool}:
  match x:
    case U32{WCon{True{}, +t}}:
      %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)), Word.zero(31n), cw.wa_zero_r(31n, t)) : {U32.is_eq(U32{WCon{True{}, _}}, 1) == True{} : Bool}
      {==}
    case U32{WCon{False{}, +t}}:
      %Equal.sym(Word(31n), Word.and(31n, t, Word.zero(31n)), Word.zero(31n), cw.wa_zero_r(31n, t)) : {U32.is_eq(U32{WCon{False{}, _}}, 1) == False{} : Bool}
      {==}

def cw.bitk(k: Nat, x: U32) -> Bool:
  cw.odd(U32.shrn(x, k))

def cw.bitk_xor(+k: Nat, +a: U32, +b: U32) -> {cw.bitk(k, U32.xor(a, b)) == Bool.xor(cw.bitk(k, a), cw.bitk(k, b)) : Bool}:
  %Equal.sym(U32, U32.shrn(U32.xor(a, b), k), U32.xor(U32.shrn(a, k), U32.shrn(b, k)), cw.shrn_xor(k, a, b)) : {cw.odd(_) == Bool.xor(cw.bitk(k, a), cw.bitk(k, b)) : Bool}
  cw.odd_xor(U32.shrn(a, k), U32.shrn(b, k))

# U32 increment: adding 1 is Base's U32.inc

def cw.incif(n: Nat, c: Bool, w: Word(n)) -> Word(n):
  match c:
    case True{}:
      Word.inc(n, w)
    case False{}:
      w

# adding zero with carry c increments by c
def cw.adc_zero(n: Nat, w: Word(n), c: Bool) -> {Word.adc(n, w, Word.zero(n), False{}, c) == cw.incif(n, c, w) : Word(n)}:
  match n:
    case 0n:
      match w c:
        case WNil{} True{}:
          {==}
        case WNil{} False{}:
          {==}
    case 1n+p:
      match w c:
        case WCon{False{}, +t} False{}:
          cw.wcon2(p, False{}, False{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, cw.adc_zero(p, t, False{}))
        case WCon{False{}, +t} True{}:
          cw.wcon2(p, True{}, True{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, cw.adc_zero(p, t, False{}))
        case WCon{True{}, +t} False{}:
          cw.wcon2(p, True{}, True{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, cw.adc_zero(p, t, False{}))
        case WCon{True{}, +t} True{}:
          cw.wcon2(p, False{}, False{}, Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), {==}, cw.adc_zero(p, t, True{}))

def cw.add_one(x: U32) -> {U32.add(x, 1) == U32.inc(x) : U32}:
  match x:
    case U32{WCon{False{}, +t}}:
      cw.u32_cong(WCon{True{}, Word.adc(31n, t, Word.zero(31n), False{}, False{})}, WCon{True{}, t}, cw.wcon2(31n, True{}, True{}, Word.adc(31n, t, Word.zero(31n), False{}, False{}), t, {==}, cw.adc_zero(31n, t, False{})))
    case U32{WCon{True{}, +t}}:
      cw.u32_cong(WCon{False{}, Word.adc(31n, t, Word.zero(31n), False{}, True{})}, WCon{False{}, Word.inc(31n, t)}, cw.wcon2(31n, False{}, False{}, Word.adc(31n, t, Word.zero(31n), False{}, True{}), Word.inc(31n, t), {==}, cw.adc_zero(31n, t, True{})))

# 32 shifts clear a word
def cw.shl32(w: U32) -> {U32.shln(w, 32n) == 0 : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def cw.shr32(w: U32) -> {U32.shrn(w, 32n) == 0 : U32}:
  match w:
    case U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}
